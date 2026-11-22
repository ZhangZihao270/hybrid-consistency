// What stock progress and held-value validity force on an actual fair
// R1/R2 stock run, and what a concrete ordinary rebuild can then do in
// the paper's two hybrid executions. The resolver may inspect every sender.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Process};
use crate::facade_contract::has_sample;
use crate::facade_history::{answer,serving_work};
use crate::facade_linear::CommandSemantics;
use crate::facade_progress::{Run,front_fair,live_from,project,scheduled};
use crate::facade_quorum::participants;
use crate::fallback_program::{self as program,apply_event};
use crate::genesis_service as genesis;
use crate::live_quorum::root_reports;
use crate::metadata_pair::{self as rpc,BeforeSample};
use crate::ordered_round::{self as base,engine,Store,Work};
use crate::ordered_store::majority;
use crate::quorum_rpc::Resolver;
use crate::stock_facade::*;

verus! {

// Two read clauses of A on stock executions only. Count the actual
// reader's RPC participants, along with service by the backend.
pub open spec fn stock_read_rules(f:CommandSemantics,rho:Resolver) -> bool {
    let p=engine(f);
    (forall|e:Run<Store,Work>,k:nat,id:nat| #[trigger] program::execution_using(p,rho,e) &&
        base::fair(project(e)) && front_fair(p,e) && (#[trigger] (e.state)(k)).calls.contains_key(id) &&
        (e.state)(k).calls[id].method==Method::Read && #[trigger] live_from(p,project(e),k,id)
        ==> exists|j:nat| j>=k && (#[trigger] answer((e.state)(j),id)).is_some()) &&
    (forall|t:Seq<State<Store>>,a:Seq<Event<Work>>,id:nat,q:Set<Replica>,i:nat,k:nat|
        #[trigger] program::path_using(p,rho,t,a) && t[0]==initial(p) && i<k<=a.len() &&
        #[trigger] a[i as int]==Event::Invoke(id,Method::Read) && #[trigger] majority(q) && (#[trigger] answer(t[k as int],id)).is_some() &&
        (forall|j:int| i<=j<k ==> #[trigger] participants(base::used(),id,t[j],a[j]).subset_of(q))
        ==> has_sample(p,t,q,id,i,k))
}
pub proof fn provided_by_stock(f:CommandSemantics,rho:Resolver)
    requires program::stock_contract(engine(f),rho,f,|e|base::fair(e),base::used()),
    ensures stock_read_rules(f,rho),
{
    hide(program::path_using);hide(program::execution_using);hide(front_fair);hide(has_sample);let p=engine(f);
    assert forall|t:Seq<State<Store>>,a:Seq<Event<Work>>,id:nat,q:Set<Replica>,i:nat,k:nat|
        #[trigger] program::path_using(p,rho,t,a) && t[0]==initial(p) && i<k<=a.len() &&
        #[trigger] a[i as int]==Event::Invoke(id,Method::Read) && #[trigger] majority(q) && (#[trigger] answer(t[k as int],id)).is_some() &&
        (forall|j:int| i<=j<k ==> #[trigger] participants(base::used(),id,t[j],a[j]).subset_of(q))
        implies has_sample(p,t,q,id,i,k) by {
        assert forall|j:int| i<=j<k implies #[trigger] serving_work(base::used(),id,t[j],a[j]).subset_of(q)
            by {assert(participants(base::used(),id,t[j],a[j]).subset_of(q));}
    }
}
spec fn at_site(site:Replica,k:nat) -> Leg {
    let d:nat=if site==Replica::R1 {0} else {1};let root=(base::start().disk)(site);
    if site==Replica::R3 || k<=2+d {Leg::Unsent} else if k<=4+d {Leg::Request}
    else if k<=6+d {Leg::AtServer} else if k<=8+d {Leg::InFlight(root)} else {Leg::Received(root)}
}
spec fn state(f:CommandSemantics,rho:Resolver,k:nat) -> State<Store> {
    let s=initial(engine(f));let base=if k==0 {s.base} else {Store{live:live_pair(),..s.base}};
    let c=Call{legs:|r|at_site(r,k),answer:if k>=11 {rho(root_reports())} else {None},..fresh(Method::Read)};
    State{base,calls:if k>=2 {s.calls.insert(2,c)} else {s.calls},..s}
}
spec fn event(rho:Resolver,k:nat) -> Event<Work> {
    if k==0 {Event::Work(Work::Crash(Replica::R3))} else if k==1 {Event::Invoke(2,Method::Read)}
    else if k<=9 {
        Event::Rpc(2,if k%2==0 {Replica::R1} else {Replica::R2},
            if k<4 {Stage::Offer} else if k<6 {Stage::DeliverRequest} else if k<8 {Stage::EmitReply} else {Stage::DeliverReply})
    } else if k==10 {Event::Poll(2)} else if k%3==0 {Event::Work(Work::Tick(Replica::R1))}
    else if k%3==1 {Event::Work(Work::Tick(Replica::R2))}
    else if rho(root_reports()).is_none() {Event::Poll(2)} else {Event::Idle}
}
spec fn run(f:CommandSemantics,rho:Resolver) -> Run<Store,Work> {
    crate::stock_availability::Stream{state:|i|state(f,rho,i),event:|i|event(rho,i)}
}
proof fn schedule_at(f:CommandSemantics,e:Run<Store,Work>,a:Event<Work>,i:nat,j:nat)
    requires j>=i,(e.event)(j)==a || !enabled(engine(f),(e.state)(j),a),
    ensures scheduled(engine(f),e,a,i),
{assert((e.event)(j)==a || !enabled(engine(f),(e.state)(j),a));}
proof fn fair_root_run(f:CommandSemantics,rho:Resolver)
    ensures ({
        let e=run(f,rho);let p=engine(f);let z=project(e);
        program::execution_using(p,rho,e) && front_fair(p,e) && base::fair(z) && live_from(p,z,2,2)
    }),
{
    let p=engine(f);let e=run(f,rho);let z=project(e);
    assert forall|i:nat| {let a=#[trigger] (e.event)(i);let s=(e.state)(i);
        enabled(p,s,a) && (e.state)(i+1)==apply_event(rho,p,s,a)} by {
        if i<11 {prefix_index(i as int);}
        let s=(e.state)(i);let u=(e.state)(i+1);let a=(e.event)(i);let v=apply_event(rho,p,s,a);
        if i>=10 {assert(rows(s.calls[2]) =~= root_reports());}
        assert(v.base.live =~= u.base.live);assert(v.closed =~= u.closed);
        if i>=1 {assert(v.calls[2].legs =~= u.calls[2].legs);}
        assert(v.calls =~= u.calls);
    }
    assert forall|i:nat,id:nat,r:Replica,st:Stage| #[trigger] scheduled(p,e,Event::Rpc(id,r,st),i) by {
        let j=i+11;assert(rows((e.state)(j).calls[2]) =~= root_reports());
        schedule_at(f,e,Event::Rpc(id,r,st),i,j);
    }
    assert forall|i:nat,id:nat| #[trigger] scheduled(p,e,Event::Poll(id),i) by {
        let j=3*(i+11)+2;assert(j%3==2);
        schedule_at(f,e,Event::Poll(id),i,j);
    }
    assert forall|i:nat,id:nat,q:Set<Replica>| #[trigger] base::scheduled(z,i,Work::Serve(id,q)) by {
        assert(base::served_or_disabled(z,i+11,Work::Serve(id,q)));
    }
    assert forall|i:nat,r:Replica| #[trigger] base::scheduled(z,i,Work::Tick(r)) by {
        let d:nat=if r==Replica::R1 {0} else {1};let j=3*(i+11)+d;
        assert(j%3==d);assert(base::served_or_disabled(z,j,Work::Tick(r)));
    }
}
pub proof fn a_forces_root_pair(f:CommandSemantics,rho:Resolver)
    requires stock_read_rules(f,rho),
    ensures rho(root_reports())==Some(1),
{
    let p=engine(f);let e=run(f,rho);fair_root_run(f,rho);
    assert((e.state)(2).calls.contains_key(2) && (e.state)(2).calls[2].method==Method::Read);
    assert(program::execution_using(p,rho,e) && live_from(p,project(e),2,2));
    assert(exists|j:nat| j>=2 && (#[trigger] answer((e.state)(j),2)).is_some());
    let j=choose|j:nat| j>=2 && (#[trigger] answer((e.state)(j),2)).is_some();
    assert(j>=11 && rho(root_reports()).is_some());
    let t=Seq::new(12,|i:int|(e.state)(i as nat));let a=Seq::new(11,|i:int|(e.event)(i as nat));let q=live_pair();
    assert forall|i:int| 0<=i<11 implies enabled(p,t[i],#[trigger] a[i]) && t[i+1]==apply_event(rho,p,t[i],a[i])
        by {assert(enabled(p,(e.state)(i as nat),(e.event)(i as nat)));}
    assert(program::path_using(p,rho,t,a));
    assert forall|i:int| 1<=i<11 implies #[trigger] participants(base::used(),2,t[i],a[i]).subset_of(q) by {};
    assert(t[0]==initial(p) && majority(q) && a[1]==Event::Invoke(2,Method::Read) && answer(t[11],2).is_some());
    assert(has_sample(p,t,q,2,1,11));
    let (h,r)=choose|h:int,r:Replica| 1<=h<=11 && q.contains(r) && #[trigger] (p.cell)(t[h].base,r)==answer(t[11],2).unwrap();
}

pub open spec fn with_rebuild(f:CommandSemantics,rho:Resolver,s:State<Store>,e:Event<Work>,job:Option<Replica>,u:State<Store>) -> bool {
    match job {
        None=>enabled(engine(f),s,e) && u==apply_event(rho,engine(f),s,e),
        Some(r)=>e==Event::Idle && genesis::can_rebuild(s,r) && u==genesis::rebuild(s,r),
    }
}
spec fn root_while_open(s:State<Store>) -> bool {
    forall|r:Replica| !#[trigger] s.closed.contains(r) ==> (s.base.disk)(r).value==1
}
proof fn ordinary_step(f:CommandSemantics,rho:Resolver,s:State<Store>,ev:Event<Work>,job:Option<Replica>,u:State<Store>)
    requires root_while_open(s),with_rebuild(f,rho,s,ev,job,u),
    ensures job.is_none(),enabled(engine(f),s,ev),u==apply_event(rho,engine(f),s,ev),root_while_open(u),
{
    if let Some(r)=job {assert(!s.closed.contains(r));}
    assert forall|r:Replica| !#[trigger] u.closed.contains(r) implies (u.base.disk)(r).value==1 by {
        assert(!s.closed.contains(r));
        if (u.base.disk)(r).value!=(s.base.disk)(r).value {
            assert(all_replicas().contains(r));
            assert(all_replicas().filter(|site:Replica| (u.base.disk)(site).value!=(s.base.disk)(site).value).contains(r));
        }
    }
}
pub open spec fn rebuilt_path(f:CommandSemantics,rho:Resolver,t:Seq<State<Store>>,a:Seq<Event<Work>>,jobs:Seq<Option<Replica>>) -> bool {
    t.len()==a.len()+1 && jobs.len()==a.len() && forall|i:int| 0<=i<a.len() ==>
        with_rebuild(f,rho,t[i],#[trigger] a[i],jobs[i],t[i+1])
}
proof fn stock_state_at(f:CommandSemantics,rho:Resolver,t:Seq<State<Store>>,a:Seq<Event<Work>>,jobs:Seq<Option<Replica>>,k:nat)
    requires t[0]==initial(engine(f)),rebuilt_path(f,rho,t,a,jobs),k<=a.len(),
    ensures root_while_open(t[k as int]),k<a.len() ==> jobs[k as int].is_none() &&
        enabled(engine(f),t[k as int],a[k as int]) && t[k as int+1]==apply_event(rho,engine(f),t[k as int],a[k as int]),
    decreases k,
{
    if k>0 {let j=(k-1) as nat;stock_state_at(f,rho,t,a,jobs,j);ordinary_step(f,rho,t[j as int],a[j as int],jobs[j as int],t[k as int]);}
    if k<a.len() {ordinary_step(f,rho,t[k as int],a[k as int],jobs[k as int],t[k as int+1]);}
}
// No assumption on rho, even on stock reports. The optional local job is
// disabled in every reachable stock state of the augmented implementation.
pub proof fn same_stock_paths(f:CommandSemantics,rho:Resolver,t:Seq<State<Store>>,a:Seq<Event<Work>>,jobs:Seq<Option<Replica>>)
    requires t.len()>0,t[0]==initial(engine(f)),jobs.len()==a.len(),
    ensures rebuilt_path(f,rho,t,a,jobs)==(program::path_using(engine(f),rho,t,a) &&
        forall|i:int| 0<=i<jobs.len() ==> (#[trigger] jobs[i]).is_none()),
{
    if rebuilt_path(f,rho,t,a,jobs) {
        assert forall|i:int| 0<=i<a.len() implies jobs[i].is_none() && enabled(engine(f),t[i],#[trigger] a[i]) &&
            t[i+1]==apply_event(rho,engine(f),t[i],a[i]) by {stock_state_at(f,rho,t,a,jobs,i as nat);}
        assert forall|i:int| 0<=i<jobs.len() implies (#[trigger] jobs[i]).is_none() by {stock_state_at(f,rho,t,a,jobs,i as nat);}
        assert(program::path_using(engine(f),rho,t,a));
    } else if program::path_using(engine(f),rho,t,a) && forall|i:int| 0<=i<jobs.len() ==> (#[trigger] jobs[i]).is_none() {
        assert forall|i:int| 0<=i<a.len() implies with_rebuild(f,rho,t[i],#[trigger] a[i],jobs[i],t[i+1]) by {
            assert(jobs[i].is_none());assert(enabled(engine(f),t[i],a[i]));
        }
    }
}
pub proof fn same_stock_runs(f:CommandSemantics,rho:Resolver,e:Run<Store,Work>,jobs:spec_fn(nat)->Option<Replica>)
    requires (e.state)(0)==initial(engine(f)),
    ensures (forall|k:nat| with_rebuild(f,rho,(e.state)(k),#[trigger] (e.event)(k),jobs(k),(e.state)(k+1))) ==
        (program::execution_using(engine(f),rho,e) && forall|k:nat| (#[trigger] jobs(k)).is_none()),
{
    if forall|i:nat| with_rebuild(f,rho,(e.state)(i),#[trigger] (e.event)(i),jobs(i),(e.state)(i+1)) {
        assert forall|k:nat| {let a=#[trigger] (e.event)(k);let u=(e.state)(k);
            jobs(k).is_none() && enabled(engine(f),u,a) && (e.state)(k+1)==apply_event(rho,engine(f),u,a)} by {
            let t=Seq::new(k+2,|i:int|(e.state)(i as nat));let a=Seq::new(k+1,|i:int|(e.event)(i as nat));
            let js=Seq::new(k+1,|i:int|jobs(i as nat));
            assert forall|i:int| 0<=i<a.len() implies with_rebuild(f,rho,t[i],#[trigger] a[i],js[i],t[i+1])
                by {assert(with_rebuild(f,rho,(e.state)(i as nat),(e.event)(i as nat),jobs(i as nat),(e.state)((i+1) as nat)));}
            stock_state_at(f,rho,t,a,js,k);
        }
        assert forall|k:nat| (#[trigger] jobs(k)).is_none() by {
            assert(enabled(engine(f),(e.state)(k),(e.event)(k)) && jobs(k).is_none());
        }
        assert(program::execution_using(engine(f),rho,e));
    } else if program::execution_using(engine(f),rho,e) && forall|k:nat| (#[trigger] jobs(k)).is_none() {
        assert forall|k:nat| with_rebuild(f,rho,(e.state)(k),#[trigger] (e.event)(k),jobs(k),(e.state)(k+1)) by {
            assert(jobs(k).is_none());assert(enabled(engine(f),(e.state)(k),(e.event)(k)));
        }
    }
}
pub open spec fn repair_step(f:CommandSemantics,rho:Resolver,b:Fork,k:nat) -> bool {
    let work=BeforeSample::RestoreImages;let n=rpc::read_net(b,work,k);let a=rpc::read_actions(b,work)[k as int];
    let s=genesis::at_read(b,k);let u=genesis::at_read(b,k+1);let ev=crate::facade_hybrid::inner(n,a);
    let job=match a {Action::Local(r,_)=>Some(r),_=>None};
    delivery::enabled(n,a) && crate::facade_transport::valid(n,crate::facade_transport::service(n,a,Process::SecondClient),s.calls[2],Process::SecondClient)
        && rpc::read_net(b,work,k+1)==delivery::advance(|x,w|cell(x,w),n,a) && with_rebuild(f,rho,s,ev,job,u)
        && (match a {Action::Local(_,w)=>w==Wire::Copy(1),_=>true})
}
proof fn execute_rebuild(f:CommandSemantics,rho:Resolver,b:Fork,k:nat)
    requires k<11,rho(root_reports())==Some(1),
    ensures repair_step(f,rho,b,k),
{
    let work=BeforeSample::RestoreImages;let n=rpc::read_net(b,work,k);let a=rpc::read_actions(b,work)[k as int];
    let s=genesis::at_read(b,k);let ev=crate::facade_hybrid::inner(n,a);
    genesis::same_reader_with_repair(f,b,k);prefix_index(k as int);
    let net=delivery::advance(|x,w|cell(x,w),n,a);let u=rpc::read_net(b,work,k+1);
    assert(net.locals =~= u.locals);assert(net.pending =~= u.pending);
    if let Event::Poll(id)=ev {
        assert(id==2);assert(rows(s.calls[2]) =~= root_reports());
        assert(apply_event(rho,engine(f),s,ev).calls =~= genesis::at_read(b,k+1).calls);
    }
}
pub open spec fn repaired(f:CommandSemantics,rho:Resolver,b:Fork) -> bool {
    let q=genesis::at_read(b,11);let n=rpc::read_net(b,BeforeSample::RestoreImages,11);
    crate::sender_forks::prefix_taken(f,rho,b) && genesis::at_read(b,0)==program::original(b,17).core
        && rpc::read_net(b,BeforeSample::RestoreImages,0)==program::original(b,17).net
        && (forall|k:nat| k<11 ==> #[trigger] repair_step(f,rho,b,k))
        && n.pending==program::original(b,17).net.pending && n.pending.get(2)==Some(packet_for(b,2)) && delivery::enabled(n,Action::Deliver(2))
        && q.calls[1].answer==Some(first_value(b)) && q.calls[2].answer==Some(1) && !crate::read_recovery::compatible(b,1)
}
// The only hybrid service used beyond the real SR1 prefixes is the local
// ordinary genesis rebuild already implemented at both open survivors.
pub proof fn original_forks_with_rebuild(f:CommandSemantics,rho:Resolver,n:Notice)
    requires stock_read_rules(f,rho),crate::sender_forks::firsts(rho,n),
    ensures repaired(f,rho,alpha(n)),repaired(f,rho,beta(n)),
{
    hide(repaired);hide(stock_read_rules);
    a_forces_root_pair(f,rho);original_rebuild(f,rho,alpha(n));original_rebuild(f,rho,beta(n));
}
proof fn original_rebuild(f:CommandSemantics,rho:Resolver,b:Fork)
    requires rho(root_reports())==Some(1),crate::sender_forks::firsts(rho,b.notice),
    ensures repaired(f,rho,b),
{
    hide(crate::sender_forks::prefix_taken);hide(repair_step);hide(crate::protocol::memory);
    crate::metadata_reader::actual_first_decision(b,rho,Set::empty());crate::sender_forks::original_prefix(f,rho,b);
    genesis::repair_checkpoint(b);crate::facade_transport::actual_first_rpc(b,17);
    assert forall|k:nat| k<11 implies #[trigger] repair_step(f,rho,b,k) by {execute_rebuild(f,rho,b,k);}
    crate::read_recovery::history_accepts_exactly_observed_value(b,1);
    let start=rpc::read_net(b,BeforeSample::RestoreImages,0);let checkpoint_net=program::original(b,17).net;
    assert(start.locals =~= checkpoint_net.locals);assert(start.pending =~= checkpoint_net.pending);
    assert(rpc::read_net(b,BeforeSample::RestoreImages,11).pending =~= checkpoint_net.pending);
}

// A concrete instance with sender-sensitive readiness. Its stock contract
// ranges over every reachable stock run of the ordered-quorum abstraction.
pub proof fn reference_original_service(f:CommandSemantics,n:Notice)
    ensures ({
        let rho=crate::mixed_service_transfer::reference_sample();
        program::stock_contract(engine(f),rho,f,|e|base::fair(e),base::used()) && stock_read_rules(f,rho)
            && repaired(f,rho,alpha(n)) && repaired(f,rho,beta(n))
    }),
{
    hide(program::stock_contract);hide(stock_read_rules);hide(repaired);hide(crate::sender_forks::prefix_taken);
    hide(crate::sender_forks::actual_sr2);hide(crate::sender_forks::release_after_origin_crash);
    let rho=crate::mixed_service_transfer::reference_sample();
    crate::sender_forks::reference_reader(f,alpha(n));provided_by_stock(f,rho);
    crate::mixed_service_transfer::ordinary_reference_escape(alpha(n));
    rpc::real_first_with(rho,rho,alpha(n),Set::empty());rpc::real_first_with(rho,rho,beta(n),Set::empty());
    original_forks_with_rebuild(f,rho,n);
}

}
