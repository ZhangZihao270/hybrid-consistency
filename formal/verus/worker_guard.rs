// A stock-equivalent ordinary engine can lack a service transition even
// after the same read has actually been registered. The guard examines
// the serving quorum's physical ordinary images, never a weak certificate.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::facade_contract::stock_a;
use crate::facade_history::stock_sample_valid;
use crate::facade_linear::{CommandSemantics,Grid,ordered,certifies,base_linearizable};
use crate::facade_progress::{Run,StockRun,stock_execution,live_from,front_fair,scheduled};
use crate::facade_hybrid as hybrid;
use crate::facade_transport::{actual_first_rpc,actual_second_rpc};
use crate::read_dispatch as jobs;
use crate::delivery::{self,Action};
use crate::metadata_fair::{background,network};
use crate::mixed_service_transfer::reference_sample;
use crate::promotion_wait as wait;
use crate::facade_quorum::{base_service,any_backend_majority};
use crate::ordered_round::{self as base,Store,Work};
use crate::ordered_store::{Stamp,majority};
use crate::stock_facade::*;
use crate::worker_transfer as transfer;

verus! {

pub open spec fn ordinary_image(d:Stamp) -> bool {d.version>0 || d.value==1}
pub open spec fn check(s:Store,a:Input<Work>) -> bool {
    match a {
        Input::Work(Work::Serve(id,q)) if s.calls.get(id)==Some(Method::Read)=>
            forall|r:Replica| q.contains(r) ==> ordinary_image(#[trigger] (s.disk)(r)),
        _=>true,
    }
}
pub open spec fn engine(f:CommandSemantics) -> Engine<Store,Work> {
    Engine{ready:|s,a|base::ready(s,a) && check(s,a),..base::engine(f)}
}
spec fn stock_images(s:Store) -> bool {
    forall|r:Replica| ordinary_image(#[trigger] (s.disk)(r))
}
proof fn preserve(f:CommandSemantics,s:Store,a:Input<Work>)
    requires stock_images(s),
    ensures stock_images(base::advance(f,s,a)),check(s,a),
{
    let u=base::advance(f,s,a);
    assert forall|r:Replica| ordinary_image(#[trigger] (u.disk)(r)) by {
        assert(ordinary_image((s.disk)(r)));
    }
}
proof fn image_at(f:CommandSemantics,t:Seq<Store>,a:Seq<Input<Work>>,k:nat)
    requires t.len()==a.len()+1,stock_images(t[0]),k<=a.len(),
        forall|i:int| 0<=i<a.len() ==> t[i+1]==base::advance(f,t[i],#[trigger] a[i]),
    ensures stock_images(t[k as int]),
    decreases k,
{
    if k>0 {let i=(k-1) as nat;image_at(f,t,a,i);preserve(f,t[i as int],a[i as int]);}
}
pub proof fn same_stock_paths(f:CommandSemantics,t:Seq<Store>,a:Seq<Input<Work>>)
    requires t[0]==base::start(),
    ensures backend_path(base::engine(f),t,a)==backend_path(engine(f),t,a),
{
    if backend_path(base::engine(f),t,a) || backend_path(engine(f),t,a) {
        assert forall|i:int| 0<=i<a.len() implies (engine(f).ready)(t[i],#[trigger] a[i]) && base::ready(t[i],a[i])
            && t[i+1]==base::advance(f,t[i],a[i]) by {image_at(f,t,a,i as nat);}
    }
}
proof fn reachable_images(f:CommandSemantics,s:Store)
    ensures backend_reachable(base::engine(f),s)==backend_reachable(engine(f),s),
        backend_reachable(engine(f),s) ==> stock_images(s),
{
    let p=if backend_reachable(base::engine(f),s) {base::engine(f)} else {engine(f)};
    if backend_reachable(p,s) {
        let (t,a)=choose|t:Seq<Store>,a:Seq<Input<Work>>| #[trigger] backend_path(p,t,a) && t[0]==p.initial && t.last()==s;
        same_stock_paths(f,t,a);image_at(f,t,a,a.len());
        assert(backend_path(base::engine(f),t,a) && backend_path(engine(f),t,a));
    }
}
pub proof fn fair_guards_on_stock(f:CommandSemantics,e:StockRun<Store,Work>)
    ensures stock_execution(engine(f),e)==stock_execution(base::engine(f),e),
        stock_execution(engine(f),e) ==> forall|k:nat,a:Input<Work>| (engine(f).ready)(#[trigger] (e.state)(k),a)==#[trigger] base::ready((e.state)(k),a),
{
    if stock_execution(engine(f),e) || stock_execution(base::engine(f),e) {
        assert forall|k:nat| #[trigger] stock_images((e.state)(k)) by {
            let t=Seq::new(k+1,|i:int|(e.state)(i as nat));let a=Seq::new(k,|i:int|(e.event)(i as nat));
            assert forall|i:int| 0<=i<k implies t[i+1]==base::advance(f,t[i],#[trigger] a[i]) by {};
            image_at(f,t,a,k);
        }
        assert forall|k:nat,a:Input<Work>| (engine(f).ready)(#[trigger] (e.state)(k),a)==#[trigger] base::ready((e.state)(k),a)
            by {preserve(f,(e.state)(k),a);}
        assert forall|k:nat| {let a=#[trigger] (e.event)(k);let s=(e.state)(k);
            base::ready(s,a) && (engine(f).ready)(s,a) && (e.state)(k+1)==base::advance(f,s,a)} by {};
    }
}
pub open spec fn served_or_disabled(f:CommandSemantics,e:StockRun<Store,Work>,j:nat,w:Work) -> bool {
    (e.event)(j)==Input::Work(w) || !(engine(f).ready)((e.state)(j),Input::Work(w))
}
pub open spec fn scheduled_work(f:CommandSemantics,e:StockRun<Store,Work>,i:nat,w:Work) -> bool {
    exists|j:nat| j>=i && #[trigger] served_or_disabled(f,e,j,w)
}
pub open spec fn fair(f:CommandSemantics,e:StockRun<Store,Work>) -> bool {
    (forall|i:nat,id:nat,q:Set<Replica>| #[trigger] scheduled_work(f,e,i,Work::Serve(id,q))) &&
        forall|i:nat,r:Replica| #[trigger] scheduled_work(f,e,i,Work::Tick(r))
}
proof fn fair_on_stock(f:CommandSemantics,e:StockRun<Store,Work>)
    requires stock_execution(engine(f),e),
    ensures base::fair(e)==fair(f,e),
{
    fair_guards_on_stock(f,e);
    assert forall|i:nat,w:Work| #[trigger] scheduled_work(f,e,i,w)==#[trigger] base::scheduled(e,i,w) by {
        if scheduled_work(f,e,i,w) {
            let j=choose|j:nat| j>=i && #[trigger] served_or_disabled(f,e,j,w);
            assert(base::served_or_disabled(e,j,w));
        } else if base::scheduled(e,i,w) {
            let j=choose|j:nat| j>=i && #[trigger] base::served_or_disabled(e,j,w);
            assert(served_or_disabled(f,e,j,w));
        }
    }
    if base::fair(e) {
        assert forall|i:nat,id:nat,q:Set<Replica>| #[trigger] scheduled_work(f,e,i,Work::Serve(id,q)) by {assert(base::scheduled(e,i,Work::Serve(id,q)));}
        assert forall|i:nat,r:Replica| #[trigger] scheduled_work(f,e,i,Work::Tick(r)) by {assert(base::scheduled(e,i,Work::Tick(r)));}
    } else if fair(f,e) {
        assert forall|i:nat,id:nat,q:Set<Replica>| #[trigger] base::scheduled(e,i,Work::Serve(id,q)) by {assert(scheduled_work(f,e,i,Work::Serve(id,q)));}
        assert forall|i:nat,r:Replica| #[trigger] base::scheduled(e,i,Work::Tick(r)) by {assert(scheduled_work(f,e,i,Work::Tick(r)));}
    }
}
proof fn all_majorities(f:CommandSemantics)
    ensures any_backend_majority(engine(f),base::used()),
{
    let p=engine(f);let old=base::engine(f);let used=base::used();base::api_and_majorities(f);
    assert forall|x:Store,id:nat,q:Set<Replica>| #[trigger] backend_reachable(p,x) && (#[trigger] (p.submitted)(x,id)).is_none()
        && (p.client)(x,id) && #[trigger] majority(q) && q.subset_of((p.up)(x))
        implies exists|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] base_service(p,used,x,id,q,t,w,v) by {
        reachable_images(f,x);
        assert(backend_reachable(old,x) && (old.submitted)(x,id).is_none() && (old.client)(x,id) && q.subset_of((old.up)(x)));
        assert(exists|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] base_service(old,used,x,id,q,t,w,v));
        let (t,w,v)=choose|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] base_service(old,used,x,id,q,t,w,v);
        preserve(f,x,Input::Submit(id,Method::Read));
        let a=Seq::new(w.len(),|i:int|Input::Work(w[i]));
        assert forall|i:int| 0<=i<a.len() implies t[i+1]==base::advance(f,t[i],#[trigger] a[i]) by {assert(base::ready(t[i],Input::Work(w[i])));}
        assert forall|i:int| 0<=i<w.len() implies {let ev=Input::Work(#[trigger] w[i]);
            (p.ready)(t[i],ev) && t[i+1]==(p.step)(t[i],ev) && used(id,t[i],ev).subset_of(q)} by {
            image_at(f,t,a,i as nat);preserve(f,t[i],a[i]);
        }
        let (j,r)=choose|j:int,r:Replica| 0<=j<t.len() && q.contains(r) && #[trigger] (old.cell)(t[j],r)==v;
        assert((p.cell)(t[j],r)==v);
        assert forall|i:int| 0<=i<t.len() implies (p.client)(#[trigger] t[i],id) && q.subset_of((p.up)(t[i]))
            by {assert((old.client)(t[i],id) && q.subset_of((old.up)(t[i])));}
        assert(base_service(p,used,x,id,q,t,w,v));
    }
}
// Fairness here tests the same worker/tick guards at every reachable stock
// state (above). A covers commands and reads, including nonuniform disks.
pub proof fn full_stock(f:CommandSemantics)
    ensures stock_a(engine(f),|e|fair(f,e),base::used()),base_linearizable(engine(f),f),ports(engine(f)),
        forall|s:Store,a:Input<Work>| #[trigger] backend_reachable(engine(f),s) ==>
            (engine(f).ready)(s,a)==#[trigger] base::ready(s,a),
{
    let p=engine(f);let old=base::engine(f);let used=base::used();
    base::concrete_full_a(f);all_majorities(f);
    assert forall|s:Store| #[trigger] backend_reachable(p,s) implies backend_reachable(old,s) && stock_images(s) by {reachable_images(f,s);}
    assert forall|e:StockRun<Store,Work>,k:nat,id:nat| stock_execution(p,e) && fair(f,e) &&
        (p.submitted)(#[trigger] (e.state)(k),id).is_some() && #[trigger] live_from(p,e,k,id)
        implies exists|j:nat| j>=k && (p.reply)(#[trigger] (e.state)(j),id).is_some() by {
        fair_guards_on_stock(f,e);fair_on_stock(f,e);assert(live_from(old,e,k,id));
    }
    assert forall|t:Seq<Store>,a:Seq<Input<Work>>| #[trigger] backend_path(p,t,a) && t[0]==p.initial implies backend_path(old,t,a)
        by {same_stock_paths(f,t,a);}
    assert forall|t:Seq<Store>,a:Seq<Input<Work>>| #[trigger] backend_path(p,t,a) && t[0]==p.initial implies
        exists|g:Grid| #[trigger] ordered(g,f,a.len()) && certifies(g,a.len(),
            |i:nat,id:nat,m:Method|a[i as int]==Input::Submit(id,m),|i:nat,id:nat|(p.reply)(t[i as int],id)) by {base::strong_safety(f,t,a);}
    assert forall|t:Seq<Store>,a:Seq<Input<Work>>,id:nat,q:Set<Replica>,i:nat,k:nat|
        #[trigger] backend_path(p,t,a) && t[0]==p.initial && i<k<=a.len() && #[trigger] a[i as int]==Input::Submit(id,Method::Read)
        && #[trigger] majority(q) && (#[trigger] (p.reply)(t[k as int],id)).is_some()
        && (forall|j:int| i<=j<k && a[j] is Work ==> #[trigger] used(id,t[j],a[j]).subset_of(q))
        implies exists|j:int,r:Replica| i<=j<=k && q.contains(r) && #[trigger] (p.cell)(t[j],r)==(p.reply)(t[k as int],id).unwrap() by {
        assert(backend_path(old,t,a) && (old.reply)(t[k as int],id).is_some());
        assert(exists|j:int,r:Replica| i<=j<=k && q.contains(r) && #[trigger] (old.cell)(t[j],r)==(old.reply)(t[k as int],id).unwrap());
        let (j,r)=choose|j:int,r:Replica| i<=j<=k && q.contains(r) && #[trigger] (old.cell)(t[j],r)==(old.reply)(t[k as int],id).unwrap();
        assert((p.cell)(t[j],r)==(p.reply)(t[k as int],id).unwrap());
    }
}

pub open spec fn mixed_job(s:Store) -> bool {
    s.live==live_pair() && s.calls==Map::empty().insert(2nat,Method::Read) && s.done.is_empty() &&
        forall|r:Replica| s.live.contains(r) ==> !ordinary_image(#[trigger] (s.disk)(r))
}
pub open spec fn actual(b:Fork) -> Store {crate::facade_hybrid::prefix(b,17).base}
pub open spec fn issued(f:CommandSemantics,b:Fork) -> Store {base::advance(f,actual(b),Input::Submit(2,Method::Read))}
pub proof fn first_failed_worker_instruction(f:CommandSemantics,b:Fork)
    ensures (engine(f).ready)(actual(b),Input::Submit(2,Method::Read)),mixed_job(issued(f,b)),
        transfer::queue(issued(f,b))==transfer::queue(base::advance(f,transfer::shadow(f),Input::Submit(2,Method::Read))),
        (engine(f).ready)(base::advance(f,transfer::shadow(f),Input::Submit(2,Method::Read)),Input::Work(Work::Serve(2,live_pair()))),
        !transfer::ordinary_jobs(engine(f),base::used(),|s|transfer::queue(s)),
        base::ready(issued(f,b),Input::Work(Work::Serve(2,live_pair()))) &&
            !(engine(f).ready)(issued(f,b),Input::Work(Work::Serve(2,live_pair()))),
{
    transfer::stock_queue_at_originals(f,b);let x=transfer::shadow(f);let ask=Input::Submit(2,Method::Read);
    let t=base::advance(f,x,ask);let q=live_pair();let a=Input::Work(Work::Serve(2,q));
    transfer::reachable_step(base::engine(f),x,ask);reachable_images(f,t);
    assert(mixed_job(issued(f,b))) by {assert(actual(b).live =~= live_pair());}
    let y=issued(f,b);
    assert(y.calls.get(2)==Some(Method::Read) && q.contains(Replica::R1));
    assert(!ordinary_image((y.disk)(Replica::R1)));
    assert(!check(y,a));
    assert(transfer::queue(t)==transfer::queue(y));
    assert((engine(f).ready)(t,a) && backend_reachable(engine(f),t));
    if transfer::ordinary_jobs(engine(f),base::used(),|s|transfer::queue(s)) {
        let view=|s:Store|transfer::queue(s);assert((engine(f).ready)(t,a) && view(t)==view(y));
        assert((engine(f).ready)(y,a));
    }
}

proof fn work_preserves(f:CommandSemantics,s:Store,w:Work)
    requires mixed_job(s),(engine(f).ready)(s,Input::Work(w)),
    ensures mixed_job(base::advance(f,s,Input::Work(w))),
{
    if let Work::Serve(id,q)=w {
        assert(id==2 && majority(q) && q.subset_of(live_pair()));
        assert(q.contains(Replica::R1));assert(!ordinary_image((s.disk)(Replica::R1)));
    }
}
// Every internal job is admitted here by its actual guard. No extra
// client submits an application command in this read-only continuation.
pub proof fn no_ordinary_worker_service(f:CommandSemantics,b:Fork,w:Seq<Work>)
    ensures !transfer::service(engine(f),base::used(),actual(b),2,live_pair(),w),
{
    first_failed_worker_instruction(f,b);let p=engine(f);let x=issued(f,b);
    if transfer::service(p,base::used(),actual(b),2,live_pair(),w) {
        all_work(f,x,w,w.len());assert(transfer::run(p,x,w,w.len()).done.is_empty());
    }
}
proof fn all_work(f:CommandSemantics,x:Store,w:Seq<Work>,k:nat)
    requires mixed_job(x),k<=w.len(),forall|i:int| 0<=i<w.len() ==> (engine(f).ready)(transfer::run(engine(f),x,w,i as nat),Input::Work(#[trigger] w[i])),
    ensures mixed_job(transfer::run(engine(f),x,w,k)),
    decreases k,
{
    if k>0 {let i=(k-1) as nat;all_work(f,x,w,i);work_preserves(f,transfer::run(engine(f),x,w,i),w[i as int]);}
}

pub enum Internal { Ordinary(Work), Network(delivery::Network<int,Wire>,Action<Wire>) }
// The network argument is an overapproximation for the invariant. Each
// delivered payload is read from its slot; the fair execution below checks
// the entire sequence of actual queues. Weak data in this workload are 2/5.
pub open spec fn internal(f:CommandSemantics) -> wait::Relation<Store,Internal> {
    |s:Store,e,u| match e {
        Internal::Ordinary(w)=>(engine(f).ready)(s,Input::Work(w)) && u==base::advance(f,s,Input::Work(w)),
        Internal::Network(n,a)=>{
            let facade=State{base:s,calls:Map::empty(),closed:Set::empty()};
            delivery::enabled(n,a) && crate::validator_block::application_copy(n,a) && u==hybrid::weak_part(facade,n,a).base
        },
    }
}
pub(crate) proof fn internal_keeps_job(f:CommandSemantics,s:Store,e:Internal,u:Store)
    requires mixed_job(s),internal(f)(s,e,u),
    ensures mixed_job(u),
{
    match e {
        Internal::Ordinary(w)=>work_preserves(f,s,w),
        Internal::Network(n,a)=>{
            assert forall|r:Replica| u.live.contains(r) implies !ordinary_image(#[trigger] (u.disk)(r)) by {
                assert(!ordinary_image((s.disk)(r)));
                if let Action::Deliver(id)=a {assert(crate::validator_block::application_copy(n,a));}
            }
        },
    }
}
proof fn still_pending(f:CommandSemantics,t:wait::Path<Store,Internal>,k:nat)
    requires t.states.len()==t.actions.len()+1,mixed_job(t.states[0]),wait::valid_edges(internal(f),t),k<=t.actions.len(),
    ensures mixed_job(t.states[k as int]),
    decreases k,
{
    if k>0 {let i=(k-1) as nat;still_pending(f,t,i);
        assert(internal(f)(t.states[i as int],t.actions[i as int],t.states[k as int]));
        internal_keeps_job(f,t.states[i as int],t.actions[i as int],t.states[k as int]);}
}
pub open spec fn finished(id:nat) -> spec_fn(Store)->bool { |s:Store|s.done.contains_key(id) }
pub proof fn even_issued_weak_traffic_cannot_supply_service(f:CommandSemantics,b:Fork)
    ensures !wait::can_finish(internal(f),finished(2),issued(f,b)),
        forall|effect:wait::Relation<Store,Internal>| !#[trigger] wait::needs_class(internal(f),finished(2),issued(f,b),effect),
{
    first_failed_worker_instruction(f,b);let done=finished(2);
    if wait::can_finish(internal(f),done,issued(f,b)) {
        let t=choose|t:wait::Path<Store,Internal>| #[trigger] wait::first_return(internal(f),done,issued(f,b),t);
        still_pending(f,t,t.actions.len());
    }
}

// Direction of the dependency, independently of the particular mixed cut.
// With only ordinary reads outstanding, neither a copy of 2/5 nor learning
// weak status can make an invalid ordinary quorum image valid. A read that
// can complete in this workload therefore has a real no-network service job.
pub open spec fn only_reads(s:Store) -> bool {
    forall|id:nat| #[trigger] s.calls.contains_key(id) ==> s.calls[id]==Method::Read
}
pub open spec fn usable(s:Store,q:Set<Replica>) -> bool {
    majority(q) && q.subset_of(s.live) && forall|r:Replica| q.contains(r) ==> ordinary_image(#[trigger] (s.disk)(r))
}
proof fn quorum_cannot_be_created(f:CommandSemantics,s:Store,e:Internal,u:Store,q:Set<Replica>)
    requires only_reads(s),internal(f)(s,e,u),
    ensures only_reads(u),u.calls==s.calls,usable(u,q) ==> usable(s,q),
{
    match e {
        Internal::Ordinary(w)=>{
            if let Work::Serve(i,_)=w {assert(s.calls.contains_key(i) && s.calls[i]==Method::Read);}
            assert(u.disk==s.disk);
        },
        Internal::Network(n,a)=>{
            if usable(u,q) {
                assert forall|r:Replica| q.contains(r) implies ordinary_image(#[trigger] (s.disk)(r)) by {
                    assert(ordinary_image((u.disk)(r)));
                    if let Action::Deliver(slot)=a {assert(crate::validator_block::application_copy(n,a));}
                }
            }
        },
    }
}
pub(crate) proof fn quorum_before(f:CommandSemantics,t:wait::Path<Store,Internal>,k:nat,q:Set<Replica>)
    requires t.states.len()==t.actions.len()+1,only_reads(t.states[0]),wait::valid_edges(internal(f),t),k<=t.actions.len(),
    ensures only_reads(t.states[k as int]),t.states[k as int].calls==t.states[0].calls,
        usable(t.states[k as int],q) ==> usable(t.states[0],q),
    decreases k,
{
    if k>0 {let i=(k-1) as nat;quorum_before(f,t,i,q);
        assert(internal(f)(t.states[i as int],t.actions[i as int],t.states[k as int]));
        quorum_cannot_be_created(f,t.states[i as int],t.actions[i as int],t.states[k as int],q);}
}
pub open spec fn network_effect() -> wait::Relation<Store,Internal> { |_s,e:Internal,_u|e is Network }
pub proof fn remove_all_weak_work_from_service(f:CommandSemantics,s:Store,id:nat,t:wait::Path<Store,Internal>) -> (w:wait::Path<Store,Internal>)
    requires only_reads(s),s.calls.get(id)==Some(Method::Read),
        wait::first_return(internal(f),finished(id),s,t),
    ensures wait::first_return(internal(f),finished(id),s,w),w.actions.len()==1,
        !wait::uses(w,network_effect()),w.states.last().disk==s.disk,w.states.last().tip==s.tip,
        w.states.last().done.remove(id)==s.done,
        exists|q:Set<Replica>| #[trigger] usable(s,q) && w.actions[0]==Internal::Ordinary(Work::Serve(id,q)),
{
    let k=t.actions.len();assert(k>0);let u=t.states[k-1];let last=t.actions[k-1];
    assert(!u.done.contains_key(id) && internal(f)(u,last,t.states.last()));
    match last {
        Internal::Network(_,_)=>{assert(t.states.last().done==u.done);},
        Internal::Ordinary(Work::Serve(owner,q))=>{assert(owner==id);},
        _=>{assert(t.states.last().done==u.done);},
    }
    let q=last->Ordinary_0->Serve_1;let work=Work::Serve(id,q);
    assert(last==Internal::Ordinary(work));quorum_before(f,t,(k-1) as nat,q);
    assert(usable(u,q));assert((engine(f).ready)(s,Input::Work(work)));
    let v=base::advance(f,s,Input::Work(work));
    assert(v.done.remove(id) =~= s.done);
    let w=wait::Path{states:seq![s,v],actions:seq![Internal::Ordinary(work)]};
    assert(wait::first_return(internal(f),finished(id),s,w));w
}
pub proof fn no_await_for_registered_reads(f:CommandSemantics,id:nat)
    ensures wait::no_await(internal(f),finished(id),
        |s:Store|only_reads(s) && s.calls.get(id)==Some(Method::Read),network_effect()),
{
    let next=internal(f);let done=finished(id);
    let admitted=|s:Store|only_reads(s) && s.calls.get(id)==Some(Method::Read);
    assert forall|s:Store| #[trigger] admitted(s) implies !wait::needs_class(next,done,s,network_effect()) by {
        if wait::can_finish(next,done,s) {
            let t=choose|t:wait::Path<Store,Internal>| #[trigger] wait::first_return(next,done,s,t);
            let w=remove_all_weak_work_from_service(f,s,id,t);
            assert(wait::first_return(next,done,s,w) && !wait::uses(w,network_effect()));
        }
    }
}

// Compare the two actual backends, where even the physical R3 disk
// differs. Old responses under other IDs and the ghost tip can differ.
// A scheduled quorum job obtains its inputs from its own live members.
pub open spec fn visible(x:Store,y:Store,id:nat) -> bool {
    transfer::queue(x)==transfer::queue(y) && x.done.get(id)==y.done.get(id) &&
        forall|r:Replica| x.live.contains(r) ==> #[trigger] (x.disk)(r)==(y.disk)(r)
}
pub open spec fn use_worker(f:CommandSemantics,guarded:bool) -> Engine<Store,Work> {
    if guarded {engine(f)} else {base::engine(f)}
}
proof fn live_step(f:CommandSemantics,guarded:bool,x:Store,y:Store,id:nat,a:Input<Work>)
    requires visible(x,y,id),
    ensures ({
        let p=use_worker(f,guarded);
        (p.ready)(x,a)==(p.ready)(y,a) &&
            ((p.ready)(x,a) ==> visible((p.step)(x,a),(p.step)(y,a),id))
    }),
{
    let u=base::advance(f,x,a);let v=base::advance(f,y,a);
    if base::ready(x,a) {
        if let Input::Work(Work::Serve(owner,q))=a {
            let left=Map::new(q,x.disk);let right=Map::new(q,y.disk);
            assert(left =~= right) by {
                assert forall|r:Replica| #[trigger] q.contains(r) implies left[r]==right[r] by {assert(x.live.contains(r));}
            }
            crate::quorum_rpc::latest_is_a_sample(left);
            assert(base::current(x,q)==base::current(y,q) && x.live.contains(base::current(x,q)));
            if check(x,a)!=check(y,a) {
                assert(x.calls.get(owner)==Some(Method::Read));
                if !check(x,a) {
                    let r=choose|r:Replica| q.contains(r) && !ordinary_image(#[trigger] (x.disk)(r));
                    assert(x.live.contains(r) && ordinary_image((y.disk)(r)));
                } else {
                    let r=choose|r:Replica| q.contains(r) && !ordinary_image(#[trigger] (y.disk)(r));
                    assert(x.live.contains(r) && ordinary_image((x.disk)(r)));
                }
            }
            assert(u.done.dom() =~= v.done.dom());
        }
        assert forall|r:Replica| u.live.contains(r) implies #[trigger] (u.disk)(r)==(v.disk)(r)
            by {assert(x.live.contains(r));}
    }
}
pub open spec fn after_inputs(f:CommandSemantics,x:Store,a:Seq<Input<Work>>,i:nat) -> Store
    decreases i,
{
    if i==0 {x} else {base::advance(f,after_inputs(f,x,a,(i-1) as nat),a[i-1])}
}
pub open spec fn enabled_through(f:CommandSemantics,guarded:bool,x:Store,a:Seq<Input<Work>>,k:nat) -> bool {
    k<=a.len() && forall|i:int| 0<=i<k ==> (use_worker(f,guarded).ready)(after_inputs(f,x,a,i as nat),#[trigger] a[i])
}
proof fn lift_live(f:CommandSemantics,guarded:bool,x:Store,y:Store,id:nat,a:Seq<Input<Work>>,k:nat)
    requires visible(x,y,id),enabled_through(f,guarded,x,a,k),
    ensures enabled_through(f,guarded,y,a,k),visible(after_inputs(f,x,a,k),after_inputs(f,y,a,k),id),
    decreases k,
{
    hide(visible);hide(base::advance);hide(base::ready);hide(check);hide(use_worker);
    if k>0 {
        let i=(k-1) as nat;let p=use_worker(f,guarded);let a0=a[i as int];
        let left=after_inputs(f,x,a,i);let right=after_inputs(f,y,a,i);
        assert(enabled_through(f,guarded,x,a,i));
        lift_live(f,guarded,x,y,id,a,i);live_step(f,guarded,left,right,id,a0);
        assert((p.ready)(left,a0));
        assert(after_inputs(f,x,a,k)==(p.step)(left,a0) && after_inputs(f,y,a,k)==(p.step)(right,a0))
            by {reveal(use_worker);}
        assert(visible(after_inputs(f,x,a,k),after_inputs(f,y,a,k),id));
        assert forall|j:int| 0<=j<k implies (p.ready)(after_inputs(f,y,a,j as nat),#[trigger] a[j])
            by {if j<i {assert((p.ready)(after_inputs(f,y,a,j as nat),a[j]));}}
    }
}
// Includes enabled work which changes application data and applied
// versions. The two-read H calculation applies to the original workload
// with no new application writes and publication of the actual SR2 value.
pub proof fn both_live_workers(f:CommandSemantics,n:Notice,guarded:bool,a:Seq<Input<Work>>,k:nat)
    requires enabled_through(f,guarded,actual(alpha(n)),a,k),
    ensures enabled_through(f,guarded,actual(beta(n)),a,k),
        visible(after_inputs(f,actual(alpha(n)),a,k),after_inputs(f,actual(beta(n)),a,k),2),
        (actual(alpha(n)).disk)(Replica::R3).value==5 && (actual(beta(n)).disk)(Replica::R3).value==2,
{
    let x=actual(alpha(n));let y=actual(beta(n));assert(x.live =~= live_pair());assert(y.live =~= live_pair());
    assert(visible(x,y,2));lift_live(f,guarded,x,y,2,a,k);
}
pub open spec fn queued(b:Fork,k:nat) -> State<Store> {
    let s=hybrid::suffix(b,k);
    if k<9 {s} else {State{base:Store{calls:s.base.calls.insert(2,Method::Read),..s.base},
        calls:s.calls.insert(2,Call{submitted:true,..s.calls[2]}),..s}}
}
pub open spec fn input_at(b:Fork,k:nat) -> Input<Work> {
    let s=queued(b,k);let a=hybrid::inner(network(b,k),background(b,k));
    if jobs::miss(s,a,reference_sample(),crate::dispatch_boundary::on()) {Input::Submit(2,Method::Read)} else {input(s,a)}
}
pub open spec fn actual_run(b:Fork) -> Run<Store,Work> {
    crate::stock_availability::Stream{state:|k|queued(b,k),event:|k|hybrid::inner(network(b,k),background(b,k))}
}
pub open spec fn worker_run(b:Fork) -> StockRun<Store,Work> {
    crate::stock_availability::Stream{state:|k|queued(b,k).base,event:|k|input_at(b,k)}
}
pub open spec fn real_step(f:CommandSemantics,b:Fork,k:nat) -> bool {
    let rho=reference_sample();let g=crate::dispatch_boundary::on();let n=network(b,k);let a=background(b,k);
    let s=queued(b,k);let p=engine(f);let ev=hybrid::inner(n,a);
    let client=delivery::Process::SecondClient;
    let message=crate::facade_transport::service(n,a,client);
    hybrid::invocation(s,n,a)==Event::Idle && delivery::enabled(n,a) && jobs::permitted(p,s,Event::Idle,rho,g) &&
        jobs::advance(p,s,Event::Idle,rho,g)==s && jobs::permitted(p,s,ev,rho,g) &&
        // Packet stages use the actual RPC guard and payload. A retry
        // after submission uses the worker poll guard above.
        (message is Rpc ==> crate::facade_transport::valid(n,message,s.calls[2],client)) &&
        network(b,k+1)==delivery::advance(|x,w|cell(x,w),n,a) &&
        queued(b,k+1)==hybrid::weak_part(jobs::advance(p,s,ev,rho,g),n,a) &&
        queued(b,k).calls[2].answer.is_none() && (k>=9 ==> mixed_job(s.base) && s.calls[2].submitted)
}
proof fn real_turn(f:CommandSemantics,b:Fork,k:nat)
    ensures real_step(f,b,k),
{
    hide(crate::facade_transport::at_time);
    hybrid::real_suffix(f,b,k);actual_first_rpc(b,17);actual_second_rpc(b,k);actual_second_rpc(b,k+1);
    let n=network(b,k);let a=background(b,k);let p=engine(f);let rho=reference_sample();let g=crate::dispatch_boundary::on();
    let s=queued(b,k);let u=queued(b,k+1);let e=hybrid::inner(n,a);let v=hybrid::weak_part(jobs::advance(p,s,e,rho,g),n,a);
    if k<14 {prefix_index(k as int);}
    if k>=8 {assert(rows(s.calls[2]) =~= crate::metadata_stock::unadvanced_rows());}
    if k>=9 {assert(s.base.live =~= live_pair());assert(mixed_job(s.base));}
    let after=delivery::advance(|x,w|cell(x,w),n,a);
    assert(after.locals =~= network(b,k+1).locals);assert(after.pending =~= network(b,k+1).pending);
    assert(v.base.disk =~= u.base.disk);assert(v.closed =~= u.closed);
    assert(v.calls[2].legs =~= u.calls[2].legs);assert(v.calls =~= u.calls);
    assert(jobs::advance(p,s,Event::Idle,rho,g).closed =~= s.closed);
}
proof fn front_scheduled(f:CommandSemantics,e:Run<Store,Work>,i:nat,j:nat,a:Event<Work>)
    requires j>=i, (e.event)(j)==a || !enabled(engine(f),(e.state)(j),a),
    ensures scheduled(engine(f),e,a,i),
{assert((e.event)(j)==a || !enabled(engine(f),(e.state)(j),a));}
proof fn fair_workers(f:CommandSemantics,b:Fork)
    ensures fair(f,worker_run(b)),front_fair(engine(f),actual_run(b)),
{
    let e=worker_run(b);let p=engine(f);let front=actual_run(b);
    assert forall|i:nat,id:nat,q:Set<Replica>| #[trigger] scheduled_work(f,e,i,Work::Serve(id,q)) by {
        let j=i+14;real_turn(f,b,j);let s=queued(b,j).base;let w=Work::Serve(id,q);
        if (p.ready)(s,Input::Work(w)) {assert(id==2 && q.contains(Replica::R1));assert(!ordinary_image((s.disk)(Replica::R1)));}
        assert(served_or_disabled(f,e,j,w));
    }
    assert forall|i:nat,r:Replica| #[trigger] scheduled_work(f,e,i,Work::Tick(r)) by {
        let d:nat=if r==Replica::R1 {0} else {1};let j=3*(i+14)+d;assert(j%3==d);assert(served_or_disabled(f,e,j,Work::Tick(r)));
    }
    assert forall|i:nat,id:nat| #[trigger] scheduled(p,front,Event::Poll(id),i) by {
        let j=3*(i+14)+2;assert(j%3==2);actual_first_rpc(b,17);
        front_scheduled(f,front,i,j,Event::Poll(id));
    }
    assert forall|i:nat,id:nat,r:Replica,st:Stage| #[trigger] scheduled(p,front,Event::Rpc(id,r,st),i) by {
        let j=i+14;actual_first_rpc(b,17);actual_second_rpc(b,j);
        assert(rows(queued(b,j).calls[2]).dom() =~= live_pair());
        front_scheduled(f,front,i,j,Event::Rpc(id,r,st));
    }
}

// The extra check touches only a worker's Serve instruction. It does not
// change the genuine C1 actions, including the poll that returns on SR1.
pub open spec fn guarded_prefix(f:CommandSemantics,b:Fork) -> bool {
    let p=engine(f);let rho=reference_sample();let g=crate::dispatch_boundary::on();
    crate::sender_forks::prefix_taken(f,rho,b) && forall|k:nat| k<17 ==> {
        let s=crate::fallback_program::original(b,k);let a=#[trigger] actions_to_crash(b)[k as int];
        let begin=hybrid::invocation(s.core,s.net,a);let t=jobs::advance(p,s.core,begin,rho,g);let e=hybrid::inner(s.net,a);
        jobs::permitted(p,s.core,begin,rho,g) && jobs::permitted(p,t,e,rho,g) &&
            crate::fallback_program::original(b,k+1).core==hybrid::weak_part(jobs::advance(p,t,e,rho,g),s.net,a)
    }
}
proof fn original_turns(f:CommandSemantics,b:Fork)
    requires jobs::original_prefix(f,b,reference_sample(),crate::dispatch_boundary::on()),
    ensures guarded_prefix(f,b),
{
    hide(crate::sender_forks::prefix_taken);hide(crate::facade_transport::at_time);
    let p=engine(f);let rho=reference_sample();let g=crate::dispatch_boundary::on();
    assert forall|k:nat| k<17 implies {
        let s=crate::fallback_program::original(b,k);let a=#[trigger] actions_to_crash(b)[k as int];
        let begin=hybrid::invocation(s.core,s.net,a);let t=jobs::advance(p,s.core,begin,rho,g);let e=hybrid::inner(s.net,a);
        jobs::permitted(p,s.core,begin,rho,g) && jobs::permitted(p,t,e,rho,g) &&
            crate::fallback_program::original(b,k+1).core==hybrid::weak_part(jobs::advance(p,t,e,rho,g),s.net,a)
    } by {
        prefix_index(k as int);let s=crate::fallback_program::original(b,k);let a=actions_to_crash(b)[k as int];
        let begin=hybrid::invocation(s.core,s.net,a);let t=jobs::advance(base::engine(f),s.core,begin,rho,g);let ev=hybrid::inner(s.net,a);
        assert(jobs::permitted(base::engine(f),s.core,begin,rho,g) && jobs::permitted(base::engine(f),t,ev,rho,g));
    }
}
proof fn reference_inputs(n:Notice)
    ensures crate::sender_forks::firsts(reference_sample(),n),crate::fallback_program::serves_root(reference_sample()),
        reference_sample()(crate::metadata_stock::unadvanced_rows()).is_none(),
{
    hide(crate::promotion_wait::first_return);hide(crate::promotion_wait::needs_class);hide(crate::protocol::memory);
    let rho=reference_sample();let a=alpha(n);let d=beta(n);
    crate::mixed_service_transfer::ordinary_reference_escape(a);crate::mixed_service_transfer::ordinary_reference_escape(d);
    crate::metadata_pair::real_first_with(rho,rho,a,Set::empty());crate::metadata_pair::real_first_with(rho,rho,d,Set::empty());
}
proof fn reference_and_prefix(f:CommandSemantics,b:Fork)
    ensures ({
        let p=engine(f);let rho=reference_sample();let g=crate::dispatch_boundary::on();
        crate::fallback_program::stock_contract(p,rho,f,|e|fair(f,e),base::used()) && jobs::same_stock(p,rho,g) &&
            guarded_prefix(f,b) && jobs::suffix(f,b,rho,g) && jobs::service_states(f,b,rho,g).last().calls[2].answer==Some(2)
    }),
{
    hide(guarded_prefix);hide(jobs::original_prefix);hide(jobs::physical_intake);hide(jobs::suffix);hide(jobs::same_stock);
    hide(crate::fallback_program::stock_contract);hide(crate::sender_forks::prefix_taken);hide(crate::facade_transport::at_time);
    hide(crate::promotion_wait::first_return);hide(crate::promotion_wait::needs_class);hide(crate::facade_contract::stock_a);
    let rho=reference_sample();let g=crate::dispatch_boundary::on();let a=alpha(b.notice);let d=beta(b.notice);
    reference_inputs(b.notice);
    jobs::two_real_reads(f,b.notice,rho,g);
    match b.branch {crate::Branch::Alpha=>{assert(b==a);},crate::Branch::Beta=>{assert(b==d);}}
    original_turns(f,b);
    full_stock(f);crate::fallback_program::all_stock_services(engine(f),rho,f,|e|fair(f,e),base::used());
    jobs::inherits_stock(engine(f),rho,g);
    assert(jobs::service_states(f,b,rho,g).last().calls[2].answer==jobs::result(rho,g)) by {reveal(jobs::suffix);}

}
pub open spec fn local_image_test(c:Call) -> bool {
    let m=rows(c);majority(m.dom()) && forall|r:Replica| #[trigger] m.contains_key(r) ==> ordinary_image(m[r])
}
proof fn actual_submission(f:CommandSemantics,b:Fork)
    ensures queued(b,9).base==issued(f,b),input_at(b,8)==Input::Submit(2,Method::Read),
        rows(queued(b,9).calls[2])==crate::metadata_stock::unadvanced_rows(),!local_image_test(queued(b,9).calls[2]),
        !(engine(f).ready)(queued(b,9).base,Input::Work(Work::Serve(2,live_pair()))),
{
    hide(crate::facade_transport::at_time);first_failed_worker_instruction(f,b);
    actual_second_rpc(b,8);actual_second_rpc(b,9);
    assert(rows(queued(b,8).calls[2]) =~= crate::metadata_stock::unadvanced_rows());
    assert(rows(queued(b,9).calls[2]) =~= crate::metadata_stock::unadvanced_rows());
    assert(queued(b,9).base.disk =~= issued(f,b).disk);assert(queued(b,9).base.live =~= issued(f,b).live);
}
pub proof fn assembled(f:CommandSemantics,b:Fork)
    ensures ({
        let p=engine(f);let rho=reference_sample();let g=crate::dispatch_boundary::on();
        let n=crate::metadata_fair::run(b);
        crate::fallback_program::stock_contract(p,rho,f,|e|fair(f,e),base::used()) && jobs::same_stock(p,rho,g) &&
            wait::no_await(internal(f),finished(2),
                |s:Store|only_reads(s) && s.calls.get(2)==Some(Method::Read),network_effect()) &&
            guarded_prefix(f,b) && queued(b,0)==hybrid::prefix(b,17) && queued(b,0).calls[1].answer==Some(first_value(b)) &&
            (forall|k:nat| #[trigger] real_step(f,b,k)) && fair(f,worker_run(b)) && front_fair(p,actual_run(b)) &&
            crate::progress::delivery_fair(n) && crate::progress::process_fair(n,|s,p|delivery::live(s,p)) &&
            pre_sr1_g(b,weak_assignment(b,true).ops) && truthful_notice(b,weak_assignment(b,true).ops) &&
            (n.action)(13)==Action::Deliver(2) && (n.state)(13).pending.get(2)==Some(packet_for(b,2)) &&
            (forall|id:nat| #[trigger] (n.state)(14).pending.contains_key(id) ==> !delivery::live((n.state)(14),(n.state)(14).pending[id].to)) &&
            queued(b,9).base==issued(f,b) && input_at(b,8)==Input::Submit(2,Method::Read) &&
            !local_image_test(queued(b,9).calls[2]) && !(p.ready)(queued(b,9).base,Input::Work(Work::Serve(2,live_pair()))) &&
            checkpoint_control(b,at(crate::origin(b.branch))).learned.is_none() &&
            delivery::process_step((n.state)(13),(n.action)(13)).incoming==Some(packet_for(b,2)) &&
            !wait::can_finish(internal(f),finished(2),issued(f,b)) &&
            jobs::suffix(f,b,rho,g) && jobs::service_states(f,b,rho,g).last().calls[2].answer==Some(2) &&
            crate::read_recovery::compatible(b,2)==(b.branch==crate::Branch::Beta)
    }),
{
    hide(guarded_prefix);hide(real_step);hide(jobs::original_prefix);hide(jobs::physical_intake);hide(jobs::suffix);
    hide(front_fair);hide(fair);hide(crate::progress::delivery_fair);hide(crate::progress::process_fair);
    hide(crate::fallback_program::stock_contract);hide(crate::facade_transport::at_time);
    hide(jobs::same_stock);hide(crate::confirmation::admissible_service);hide(crate::protocol::memory);
    hide(crate::promotion_wait::no_await);hide(crate::promotion_wait::can_finish);
    reference_and_prefix(f,b);assert forall|k:nat| #[trigger] real_step(f,b,k) by {real_turn(f,b,k);}
    fair_workers(f,b);even_issued_weak_traffic_cannot_supply_service(f,b);no_await_for_registered_reads(f,2);
    actual_submission(f,b);hybrid::join_read_prefix(b);
    crate::metadata_fair::pending_after_all_live_deliveries(b);
    weak_assignment_at_delivery(b,true);copies_and_knowledge_at_checkpoint(b,weak_assignment(b,true).ops);
    crate::read_recovery::history_accepts_exactly_observed_value(b,2);
}
}
