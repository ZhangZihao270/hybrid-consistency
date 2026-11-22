use vstd::prelude::*;
use crate::{Replica,origin};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Packet,Process,process_step};
use crate::metadata_pair::{self as rpc,Local,BeforeSample,first_rows};
use crate::metadata_reader::single;
use crate::metadata_stock::Rows;
use crate::metadata_provenance::authentic_copy;
use crate::ordered_store::{Stamp,majority};
use crate::quorum_rpc::Resolver;
use crate::ordinary_service::Configuration;
use crate::protocol::{accepted,memory};
use crate::fanout_service::{run_step,done,reached};
use crate::second_copy_schedule as sched;
use crate::promotion_wait::{self as wait,Path};

verus! {

type C=Configuration<Local>;
type A=Action<Wire>;

pub open spec fn row(x:int) -> Stamp {Stamp{value:x,version:0}}
pub open spec fn expected(b:Fork,r:Replica) -> Stamp {
    row(if r==origin(b.branch) {first_value(b)} else {first_value(sched::rival(b))})
}
pub open spec fn reported(x:Option<Stamp>) -> Set<Stamp> {
    match x {Some(v)=>set![v],None=>Set::empty()}
}
pub open spec fn contents(m:Rows) -> Set<Stamp> {
    reported(m.get(Replica::R1)).union(reported(m.get(Replica::R2))).union(reported(m.get(Replica::R3)))
}
pub open spec fn mixed(b:Fork,m:Rows) -> bool {
    m.contains_key(origin(b.branch)) && majority(m.dom())
        && forall|r:Replica| #[trigger] m.contains_key(r) ==> m[r]==expected(b,r)
}
proof fn distinguishable_rows(b:Fork,m:Rows)
    requires mixed(b,m),
    ensures contents(m)==set![row(2),row(5)],
{
    let a=origin(b.branch);
    let d=if a!=Replica::R1 && m.contains_key(Replica::R1) {Replica::R1}
        else if a!=Replica::R2 && m.contains_key(Replica::R2) {Replica::R2} else {Replica::R3};
    assert(m.contains_key(d) && d!=a);
    assert(m.get(d)==Some(expected(b,d)) && m.get(a)==Some(expected(b,a)));
    if m.contains_key(Replica::R3) {assert(m[Replica::R3]==expected(b,Replica::R3));}
    assert(contents(m) =~= set![row(2),row(5)]);
}
pub open spec fn installation(s:C,a:A,u:C) -> bool {
    match a {
        Action::Deliver(id) if s.net.pending.contains_key(id)=>{
            let p=s.net.pending[id];let r=p.to->At_0;
            authentic_copy(p) && (s.net.locals)(r)!=p.input->Copy_0 && (u.net.locals)(r)==p.input->Copy_0
        }, _=>false,
    }
}
pub open spec fn admitted_firsts(rho:Resolver,b:Fork) -> bool {
    rho(first_rows(b,13))==Some(first_value(b)) && rho(first_rows(sched::rival(b),13))==Some(first_value(sched::rival(b)))
}
pub open spec fn at_cut(rho:Resolver,b:Fork) -> C {
    sched::cfg(single(rho,Set::empty()),b,11)
}
// Discharge the three outstanding R3 callback checks for this message
// family, reading the second data packet and both emitted payloads locally.
pub proof fn service_at_cut(rho:Resolver,b:Fork)
    requires admitted_firsts(rho,b),
    ensures ({
        let m=single(rho,Set::empty());let s=at_cut(rho,b);
        reached(m,s) && wait::can_finish(run_step(m),done(m),s)
            && sched::guard(m,b,11) && sched::guard(m,b,12) && sched::guard(m,b,13)
    }),
{
    let no=Set::empty();let m=single(rho,no);let d=sched::rival(b);let r=at(Replica::R3);
    rpc::real_first_with(rho,rho,b,no);rpc::real_first_with(rho,rho,d,no);
    sched::cut_reachable(m,b);sched::prior_r3(m,b,11);rpc::prefix_control(rho,rho,d,no,r,10);
    let es=sched::events(b);let a=(at_cut(rho,b).private)(r);
    assert(es[11].actor==r && es[12].actor==r && es[13].actor==r);
    assert(memory(m,r,es,12)==rpc::step(rho,a,es[11]));
    assert(memory(m,r,es,13)==rpc::step(rho,memory(m,r,es,12),es[12]));
    assert(sched::guard(m,b,11) && sched::guard(m,b,12) && sched::guard(m,b,13));
    sched::first_return_after_second_copy(m,b,|x:Local|x.returned.unwrap());
    let p=sched::segment(m,b,11,first_return_len(m,b)+2);
    assert(wait::first_return(run_step(m),done(m),at_cut(rho,b),p));
}
// In this direct reader the second receipt is optional. The generic
// completion above also admits protocols with additional required work.
pub proof fn can_sample_before_second_receipt(rho:Resolver,b:Fork) -> (p:Path<C,A>)
    requires admitted_firsts(rho,b),
    ensures ({
        let m=single(rho,Set::empty());
        wait::first_return(run_step(m),done(m),at_cut(rho,b),p)
            && (p.states.last().private)(Process::FirstClient).returned==Some(first_value(b))
            && !p.states.last().net.pending.contains_key(9) && p.states.last().net.pending.get(2)==Some(sched::receipt(sched::rival(b)))
            && (forall|i:int| 0<=i<p.actions.len() ==> match #[trigger] p.actions[i] {
                Action::Send(_,pkt)=>first_reply(pkt),_=>true,
            })
    }),
{
    hide(memory);hide(accepted);hide(wait::first_return);
    let no=Set::empty();let m=single(rho,no);let d=sched::rival(b);let r=at(Replica::R3);let q=sched::segment(m,b,11,12);
    service_at_cut(rho,b);rpc::real_first_with(rho,rho,b,no);
    sched::projected_step(m,b,11);
    assert(run_step(m)(q.states[0],q.actions[0],q.states[1]));
    assert(sched::preparation(m,b,q));
    sched::prior_r3(m,b,11);rpc::prefix_control(rho,rho,d,no,r,10);
    let es=sched::events(b);let s=q.states.last();
    assert(memory(m,r,es,12)==rpc::step(rho,memory(m,r,es,11),es[11])) by {reveal(memory);}
    assert(crate::ordinary_service::allowed(m,s,sched::sample(s)));
    let p=sched::completed_from_prepared_sample(m,|x:Local|x.returned.unwrap(),b,q);
    assert(p.states.len()>0 && done(m)(p.states.last())) by {reveal(wait::first_return);}
    assert((p.states.last().private)(Process::FirstClient).returned==Some(first_value(b)));
    assert(s.net.pending.get(2)==Some(sched::receipt(d)) && !s.net.pending.contains_key(9));
    assert forall|i:int| 0<=i<p.actions.len() implies match #[trigger] p.actions[i] {
        Action::Send(_,pkt)=>first_reply(pkt),_=>true,
    } by {assert(0<=i<=3);}
    p
}

pub open spec fn authentic_pending(b:Fork,p:Packet<Wire>) -> bool {
    (p.input is Copy ==> authentic_copy(p)) && (first_reply(p) ==> p.input==Wire::Reply(expected(b,p.from->At_0).value))
}
pub open spec fn site_ok(b:Fork,s:C,r:Replica) -> bool {
    (s.net.locals)(r)==expected(b,r).value && ((s.private)(at(r))).backup.is_none()
}
pub open spec fn before_installation(b:Fork,s:C) -> bool {
    let c=(s.private)(Process::FirstClient);
    c.rows.contains_key(origin(b.branch))
        && (forall|r:Replica| #[trigger] c.rows.contains_key(r) ==> c.rows[r]==expected(b,r))
        && (forall|r:Replica| #[trigger] site_ok(b,s,r))
        && forall|id:nat| #[trigger] s.net.pending.contains_key(id) ==> authentic_pending(b,s.net.pending[id])
}
proof fn initial(rho:Resolver,b:Fork)
    ensures before_installation(b,at_cut(rho,b)),
{
    let no=Set::empty();let m=single(rho,no);let c=Process::FirstClient;
    sched::same_private(m,b,c,11);rpc::prefix_control(rho,rho,b,no,c,12);
    let s=at_cut(rho,b);
    assert(((s.private)(c)).rows==first_rows(b,12));
    assert forall|r:Replica| #[trigger] ((s.private)(c)).rows.contains_key(r) implies ((s.private)(c)).rows[r]==expected(b,r) by {};
    assert forall|r:Replica| #[trigger] site_ok(b,s,r) by {
        if r==Replica::R3 {sched::prior_r3(m,b,11);rpc::prefix_control(rho,rho,sched::rival(b),no,at(r),10);}
        else {sched::same_private(m,b,at(r),11);rpc::prefix_control(rho,rho,b,no,at(r),12);}
    }
    assert forall|id:nat| #[trigger] s.net.pending.contains_key(id) implies authentic_pending(b,s.net.pending[id]) by {};
}
proof fn preserved(rho:Resolver,b:Fork,s:C,a:A,u:C)
    requires before_installation(b,s),run_step(single(rho,Set::empty()))(s,a,u),!installation(s,a,u),
    ensures before_installation(b,u),
{
    let m=single(rho,Set::empty());let ev=process_step(s.net,a);let c=Process::FirstClient;let prev=(s.private)(c);
    assert((m.accept)((s.private)(ev.actor),ev));
    assert forall|r:Replica| #[trigger] site_ok(b,u,r) by {
        assert(site_ok(b,s,r));
        if let Action::Deliver(id)=a {
            let p=s.net.pending[id];assert(authentic_pending(b,p));
            if p.to==at(r) && p.input is Copy && p.input->Copy_0!=(s.net.locals)(r) {assert(installation(s,a,u));}
        }
    }
    assert forall|id:nat| #[trigger] u.net.pending.contains_key(id) implies authentic_pending(b,u.net.pending[id]) by {
        if s.net.pending.contains_key(id) {assert(s.net.pending[id]==u.net.pending[id]);}
        else if let Action::Send(_,p)=a {
            if first_reply(p) {assert(site_ok(b,s,p.from->At_0));}
        }
    }
    if ev.actor==c && ev.incoming.is_some() {
        let p=ev.incoming.unwrap();let id=a->Deliver_0;
        assert(a is Deliver && s.net.pending.contains_key(id) && s.net.pending[id]==p && p.to==c);
        assert(authentic_pending(b,p));
    }
    assert(prev.rows.contains_key(origin(b.branch)));
    assert(((u.private)(c)).rows.contains_key(origin(b.branch)));
    assert forall|r:Replica| #[trigger] ((u.private)(c)).rows.contains_key(r) implies ((u.private)(c)).rows[r]==expected(b,r) by {
        if prev.rows.contains_key(r) {assert(prev.rows[r]==expected(b,r));}
    }
}
proof fn through(rho:Resolver,b:Fork,p:Path<C,A>,k:nat)
    requires wait::first_return(run_step(single(rho,Set::empty())),done(single(rho,Set::empty())),at_cut(rho,b),p),
        !wait::uses(p,|s,a,u|installation(s,a,u)),k<=p.actions.len(),
    ensures before_installation(b,p.states[k as int]),
    decreases k,
{
    if k==0 {initial(rho,b);} else {
        let i=(k-1) as nat;through(rho,b,p,i);
        assert(run_step(single(rho,Set::empty()))(p.states[i as int],p.actions[i as int],p.states[k as int]));
        assert(!installation(p.states[i as int],p.actions[i as int],p.states[k as int]));
        preserved(rho,b,p.states[i as int],p.actions[i as int],p.states[k as int]);
    }
}
// No hypothesis about what distinguishes the senders or which value the
// resolver chooses. Extract the actual reports on a physical returning poll.
pub proof fn no_copy_response_reports(rho:Resolver,b:Fork,p:Path<C,A>) -> (m:Rows)
    requires wait::first_return(run_step(single(rho,Set::empty())),done(single(rho,Set::empty())),at_cut(rho,b),p),
        !wait::uses(p,|s,a,u|installation(s,a,u)),
    ensures mixed(b,m),contents(m)==set![row(2),row(5)],
        rho(m).is_some() && rho(m)==(p.states.last().private)(Process::FirstClient).returned,
        p.actions.len()>0 && p.actions.last()==Action::Strong(Process::FirstClient)
            && m==(p.states[p.actions.len()-1].private)(Process::FirstClient).rows,
{
    let last=p.actions.len();assert(last>0);
    let i=(last-1) as nat;let s=p.states[i as int];let a=p.actions[i as int];let u=p.states.last();
    let machine=single(rho,Set::empty());let c=Process::FirstClient;
    through(rho,b,p,i);
    assert(run_step(machine)(s,a,u));assert(!done(machine)(s));
    assert((u.private)(c).returned.is_some());assert(a==Action::Strong(c));
    let m=(s.private)(c).rows;distinguishable_rows(b,m);m
}
pub proof fn fallback_wait_in_original_message_reader(b:Fork)
    ensures ({
        let rho=crate::genesis_escape::resolver();let m=single(rho,Set::empty());
        wait::needs_class(run_step(m),done(m),at_cut(rho,b),|s,a,u|installation(s,a,u))
    }),
{
    let rho=crate::genesis_escape::resolver();let m=single(rho,Set::empty());
    assert(admitted_firsts(rho,b));service_at_cut(rho,b);
    assert forall|p:Path<C,A>| #[trigger] wait::first_return(run_step(m),done(m),at_cut(rho,b),p)
        implies wait::uses(p,|s,a,u|installation(s,a,u)) by {
        if !wait::uses(p,|s,a,u|installation(s,a,u)) {
            let q=no_copy_response_reports(rho,b,p);let anchor=origin(b.branch);
            assert(q.contains_key(anchor) && q[anchor]==expected(b,anchor));
            assert(!crate::metadata_reader::valid_root(q));
            if q.contains_key(Replica::R3) {assert(q[Replica::R3]!=q[anchor] && q[Replica::R3].value!=1);}
        }
    }
}

pub open spec fn reference_arrival(s:C,a:A) -> bool {
    match a {
        Action::Deliver(id) if s.net.pending.contains_key(id)=>{
            let p=s.net.pending[id];first_reply(p) && p.from==at(Replica::R3)
        },_=>false,
    }
}
proof fn source_of_reference(rho:Resolver,b:Fork,p:Path<C,A>,k:nat)
    requires wait::first_return(run_step(single(rho,Set::empty())),done(single(rho,Set::empty())),at_cut(rho,b),p),
        k<=p.actions.len(),((p.states[k as int].private)(Process::FirstClient)).rows.contains_key(Replica::R3),
    ensures exists|i:int| 0<=i<k && reference_arrival(p.states[i],#[trigger] p.actions[i]),
    decreases k,
{
    let c=Process::FirstClient;let r3=Replica::R3;let m=single(rho,Set::empty());
    if k==0 {sched::same_private(m,b,c,11);rpc::prefix_control(rho,rho,b,Set::empty(),c,12);}
    else {
        let i=(k-1) as nat;let s=p.states[i as int];let a=p.actions[i as int];let u=p.states[k as int];
        if ((s.private)(c)).rows.contains_key(r3) {source_of_reference(rho,b,p,i);}
        else {assert(run_step(m)(s,a,u));assert(reference_arrival(s,a));}
    }
}
// A necessary condition even for completely sender-sensitive readiness.
// On the first alternative both original second reads really complete.
// On the other, every returning, installation-free first-read path needs
// a specific ordinary reply whose sender can later crash.
pub proof fn direct_service_or_reference_reply(n:Notice,rho:Resolver,b:Fork,p:Path<C,A>)
    requires admitted_firsts(rho,alpha(n)),wait::first_return(run_step(single(rho,Set::empty())),done(single(rho,Set::empty())),at_cut(rho,b),p),
        !wait::uses(p,|s,a,u|installation(s,a,u)),
    ensures ({
        let work=BeforeSample::Unchanged;let a=alpha(n);
        crate::service::incompatible_completions(n,single(rho,Set::empty()),|s:Local|s.returned.unwrap(),|s:Local|s.returned,
            rpc::read_actions(a,work),rho(rpc::sample_rows(a,work)).unwrap())
        || (exists|i:int| 0<=i<p.actions.len()-1 && reference_arrival(p.states[i],#[trigger] p.actions[i]))
    }),
{
    let a=alpha(n);let work=BeforeSample::Unchanged;let q=no_copy_response_reports(rho,b,p);
    let s=rpc::sample_rows(a,work);
    crate::mixed_sources::actual_disk_before_sr2(a,17,Replica::R1);crate::mixed_sources::actual_disk_before_sr2(a,17,Replica::R2);
    if rho(s).is_some() {crate::metadata_reader::same_reader_pair(n,rho,Set::empty(),work);}
    else {
        if !q.contains_key(Replica::R3) {assert(q =~= s);}
        let k=(p.actions.len()-1) as nat;source_of_reference(rho,b,p,k);
    }
}

// Ordinary reference sampling. This separate policy lets R3 break a
// disagreement by reporting its present cell. A zero-position stock image
// can still validate a quorum without R3.
pub open spec fn reference_sample() -> Resolver {
    |m:Rows| if majority(m.dom()) && m.contains_key(Replica::R3) {Some(m[Replica::R3].value)}
        else if crate::metadata_reader::valid_root(m) {crate::quorum_rpc::latest(m)} else {None}
}
pub open spec fn all_reports(b:Fork) -> Rows {
    Map::new(all_replicas(),|r:Replica|expected(b,r))
}
// Emit the still-unissued R3 reply from its present cell. Deliver that
// reply AND the other origin's already-issued reply, then poll C1. The
// actual pending weak update and replication receipt stay in the queue.
pub proof fn all_ordinary_replies(rho:Resolver,b:Fork) -> (p:Path<C,A>)
    ensures ({
        let m=single(rho,Set::empty());let start=at_cut(rho,b);let c=Process::FirstClient;
        p.states[0]==start && p.states.len()==5 && p.actions.len()==4
            && wait::valid_edges(run_step(m),p) && wait::pending_before(done(m),p)
            && !wait::uses(p,|s,a,u|installation(s,a,u))
            && (p.states.last().private)(c).rows==all_reports(b)
            && (p.states.last().private)(c).returned==rho(all_reports(b))
            && p.states.last().net.pending==start.net.pending.remove(sched::reply_id(sched::rival(b)))
            && reference_arrival(p.states[1],p.actions[1])
    }),
{
    let no=Set::empty();let m=single(rho,no);let s=at_cut(rho,b);let d=sched::rival(b);
    let r=at(Replica::R3);let c=Process::FirstClient;let a=actions_to_crash(d)[10];let take=Action::Deliver(8);
    let late=Action::Deliver(sched::reply_id(d));let poll=Action::Strong(c);
    sched::prior_r3(m,b,11);rpc::prefix_control(rho,rho,d,no,r,10);
    sched::same_private(m,b,c,11);rpc::prefix_control(rho,rho,b,no,c,12);
    let u=crate::ordinary_service::apply(m,s,a);let v=crate::ordinary_service::apply(m,u,take);
    let all=crate::ordinary_service::apply(m,v,late);let end=crate::ordinary_service::apply(m,all,poll);
    assert(run_step(m)(s,a,u) && run_step(m)(u,take,v) && run_step(m)(v,late,all) && run_step(m)(all,poll,end));
    assert(((all.private)(c)).rows =~= all_reports(b));
    let p=Path{states:seq![s,u,v,all,end],actions:seq![a,take,late,poll]};
    assert forall|i:int| 0<=i<4 implies run_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        && !installation(p.states[i],p.actions[i],p.states[i+1]) by {assert(i==0 || i==1 || i==2 || i==3);}
    assert(wait::pending_before(done(m),p));assert(end.net.pending =~= s.net.pending.remove(sched::reply_id(d)));
    p
}
pub proof fn ordinary_reference_escape(b:Fork)
    ensures ({
        let rho=reference_sample();let m=single(rho,Set::empty());let d=sched::rival(b);
        admitted_firsts(rho,b) && !wait::needs_class(run_step(m),done(m),at_cut(rho,b),|s,a,u|installation(s,a,u))
            && (exists|p:Path<C,A>| #[trigger] wait::first_return(run_step(m),done(m),at_cut(rho,b),p)
                && !wait::uses(p,|s,a,u|installation(s,a,u))
                && (p.states.last().private)(Process::FirstClient).returned==Some(first_value(d)))
            && rho(crate::metadata_stock::unadvanced_rows()).is_none()
            && crate::irrevocable_order::single_read(crate::irrevocable_order::only_first(d),first_value(d))
            && crate::fallback_program::serves_root(rho)
            && crate::genesis_escape::resolver()(all_reports(b)).is_none()
    }),
{
    let rho=reference_sample();let m=single(rho,Set::empty());let p=all_ordinary_replies(rho,b);
    assert(wait::first_return(run_step(m),done(m),at_cut(rho,b),p));
    assert forall|q:Rows| #[trigger] majority(q.dom()) && (forall|r:Replica| #[trigger] q.contains_key(r) ==> q[r]==row(1))
        implies rho(q)==Some(1) by {crate::quorum_rpc::latest_is_a_sample(q);}
    let q=all_reports(b);let r=origin(b.branch);
    assert(q.contains_key(r) && q.contains_key(Replica::R3) && q[r].value!=q[Replica::R3].value);
    assert(!crate::metadata_reader::unanimous(q) && !crate::metadata_reader::valid_root(q));
    crate::irrevocable_order::separate_histories(b);
}

// A structural restriction on readiness after a majority has been sampled.
// Selection still gets the entire sender-labeled map. A missing optional
// sender from pick does not block service; use a real held row in that case.
pub open spec fn read_rule(ready:spec_fn(Set<Stamp>)->bool,pick:spec_fn(Rows)->Replica) -> Resolver {
    |m:Rows| if majority(m.dom()) && ready(contents(m)) {
        let r=pick(m);Some(if m.contains_key(r) {m[r].value} else {m[crate::quorum_rpc::latest_site(m)].value})
    } else {None}
}
pub proof fn no_await_supplies_original_sr2(n:Notice,ready:spec_fn(Set<Stamp>)->bool,pick:spec_fn(Rows)->Replica)
    requires ({
        let rho=read_rule(ready,pick);let b=alpha(n);
        ready(set![row(2)]) && ready(set![row(5)]) && wait::no_await(run_step(single(rho,Set::empty())),done(single(rho,Set::empty())),
            |s|reached(single(rho,Set::empty()),s),|s,a,u|installation(s,a,u))
    }),
    ensures ({
        let rho=read_rule(ready,pick);let a=alpha(n);let work=BeforeSample::Unchanged;
        crate::service::incompatible_completions(n,single(rho,Set::empty()),|s:Local|s.returned.unwrap(),|s:Local|s.returned,
            rpc::read_actions(a,work),rho(rpc::sample_rows(a,work)).unwrap())
    }),
{
    let b=alpha(n);let rho=read_rule(ready,pick);let m=single(rho,Set::empty());let s=at_cut(rho,b);let work=BeforeSample::Unchanged;
    let d=sched::rival(b);
    assert(contents(first_rows(b,13)) =~= set![row(5)]);
    assert(contents(first_rows(d,13)) =~= set![row(2)]);
    crate::quorum_rpc::latest_is_a_sample(first_rows(b,13));crate::quorum_rpc::latest_is_a_sample(first_rows(d,13));
    assert(admitted_firsts(rho,b));service_at_cut(rho,b);
    let w=choose|p:Path<C,A>| #[trigger] wait::first_return(run_step(m),done(m),s,p);
    let p=wait::extract_without_promotion(run_step(m),done(m),|u|reached(m,u),|x,a,y|installation(x,a,y),s,w);
    let q=no_copy_response_reports(rho,b,p);let reports=rpc::sample_rows(b,work);
    crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R1);crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R2);
    assert(reports.get(Replica::R1)==Some(row(2)) && reports.get(Replica::R2)==Some(row(5)));
    assert(contents(reports) =~= contents(q));
    assert(rho(reports).is_some());
    crate::metadata_reader::same_reader_pair(n,rho,Set::empty(),work);
}
}
