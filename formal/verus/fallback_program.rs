use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::stock_facade::*;
use crate::facade_contract::*;
use crate::facade_linear::{CommandSemantics,base_linearizable,Grid,ordered,certifies};
use crate::facade_progress::{Run,StockRun,execution,project,front_fair,live_from};
use crate::facade_quorum::{Used,outer_service,extend_reach};
use crate::facade_history::{answer,serving_work};
use crate::ordered_store::{Stamp,majority};
use crate::ordered_round as base;
use crate::metadata_stock::Rows;
use crate::quorum_rpc::Resolver;
use crate::genesis_escape::resolver;
use crate::second_copy_schedule as sched;
use crate::facade_transport::{first_leg,valid,service};
use crate::facade_hybrid::{storage,inner,invocation,weak_part};
use crate::first_copy_wait::Cut;
use crate::delivery::{self,Process};

verus! {

// Install the resolver in the actual stock front end. Requests, fences,
// delegation, commands, and the backend's service and guards use the stock code.
pub open spec fn direct(c:Call) -> bool {
    c.answer.is_none() && !c.submitted && early(c) && majority(rows(c).dom())
}
pub open spec fn apply_event<X,E>(rho:Resolver,p:Engine<X,E>,s:State<X>,a:Event<E>) -> State<X> {
    let u=step(p,s,a);
    match a {
        Event::Poll(id) if direct(s.calls[id])=>State{calls:u.calls.insert(id,Call{answer:rho(rows(s.calls[id])),..s.calls[id]}),..u},
        _=>u,
    }
}
pub open spec fn serves_root(rho:Resolver) -> bool {
    forall|m:Rows| #[trigger] majority(m.dom()) && (forall|r:Replica| #[trigger] m.contains_key(r) ==> m[r]==Stamp{version:0,value:1})
        ==> rho(m)==Some(1)
}
pub proof fn fallback_serves_root()
    ensures serves_root(resolver()),
{
    assert forall|m:Rows| #[trigger] majority(m.dom()) && (forall|r:Replica| #[trigger] m.contains_key(r) ==> m[r]==Stamp{version:0,value:1})
        implies resolver()(m)==Some(1) by {crate::quorum_rpc::latest_is_a_sample(m);assert(crate::metadata_reader::valid_root(m));}
}
proof fn same_event<X,E>(p:Engine<X,E>,rho:Resolver,s:State<X>,a:Event<E>)
    requires ports(p),reachable(p,s),serves_root(rho),enabled(p,s,a),
    ensures apply_event(rho,p,s,a)==step(p,s,a),
{
    if let Event::Poll(id)=a {
        let c=s.calls[id];
        if direct(c) {
            reachable_good(p,s);early_stock_answer(c);
            assert forall|r:Replica| #[trigger] rows(c).contains_key(r) implies rows(c)[r]==Stamp{version:0,value:1}
                by {assert((c.legs)(r) is Received);}
            assert(rho(rows(c))==Some(1));
            assert(apply_event(rho,p,s,a).calls =~= step(p,s,a).calls);
        }
    }
}
pub open spec fn path_using<X,E>(p:Engine<X,E>,rho:Resolver,t:Seq<State<X>>,a:Seq<Event<E>>) -> bool {
    t.len()==a.len()+1 && forall|i:int| 0<=i<a.len() ==>
        enabled(p,t[i],#[trigger] a[i]) && t[i+1]==apply_event(rho,p,t[i],a[i])
}
pub open spec fn execution_using<X,E>(p:Engine<X,E>,rho:Resolver,e:Run<X,E>) -> bool {
    (e.state)(0)==initial(p) && forall|i:nat| {
        let a=#[trigger] (e.event)(i);let s=(e.state)(i);
        enabled(p,s,a) && (e.state)(i+1)==apply_event(rho,p,s,a)
    }
}
proof fn reachable_at<X,E>(p:Engine<X,E>,rho:Resolver,t:Seq<State<X>>,a:Seq<Event<E>>,k:nat)
    requires ports(p),serves_root(rho),reachable(p,t[0]),path(p,t,a) || path_using(p,rho,t,a),k<=a.len(),
    ensures reachable(p,t[k as int]),
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat;reachable_at(p,rho,t,a,i);
        assert(enabled(p,t[i as int],a[i as int]));same_event(p,rho,t[i as int],a[i as int]);
        extend_reach(p,t[i as int],seq![t[i as int],t[k as int]],seq![a[i as int]]);
    }
}
pub proof fn same_paths<X,E>(p:Engine<X,E>,rho:Resolver,t:Seq<State<X>>,a:Seq<Event<E>>)
    requires ports(p),serves_root(rho),reachable(p,t[0]),
    ensures path_using(p,rho,t,a)==path(p,t,a),
{
    if path_using(p,rho,t,a) || path(p,t,a) {
        assert forall|i:int| 0<=i<a.len() implies {
            let ev=#[trigger] a[i];enabled(p,t[i],ev) && t[i+1]==apply_event(rho,p,t[i],ev) && t[i+1]==step(p,t[i],ev)
        } by {reachable_at(p,rho,t,a,i as nat);same_event(p,rho,t[i],a[i]);}
    }
}
pub proof fn same_runs<X,E>(p:Engine<X,E>,rho:Resolver,e:Run<X,E>)
    requires ports(p),serves_root(rho),
    ensures execution_using(p,rho,e)==execution(p,e),
{
    let s=initial(p);assert(path(p,seq![s],Seq::empty()));assert(reachable(p,s));
    if execution_using(p,rho,e) || execution(p,e) {
        assert forall|k:nat| {
            let ev=#[trigger] (e.event)(k);let x=(e.state)(k);
            enabled(p,x,ev) && (e.state)(k+1)==apply_event(rho,p,x,ev) && (e.state)(k+1)==step(p,x,ev)
        } by {
            let t=Seq::new(k+1,|i:int|(e.state)(i as nat));let a=Seq::new(k,|i:int|(e.event)(i as nat));
            if execution_using(p,rho,e) {
                assert forall|i:int| 0<=i<k implies enabled(p,t[i],#[trigger] a[i]) && t[i+1]==apply_event(rho,p,t[i],a[i]) by {};
                assert(path_using(p,rho,t,a));
            } else {
                assert forall|i:int| 0<=i<k implies enabled(p,t[i],#[trigger] a[i]) && t[i+1]==step(p,t[i],a[i]) by {};
                assert(path(p,t,a));
            }
            reachable_at(p,rho,t,a,k);same_event(p,rho,(e.state)(k),(e.event)(k));
        }
    }
}
// Same service witnesses (including participants and held values) and
// same legal histories. Fairness uses the same enabled stages and jobs.
pub open spec fn stock_contract<X,E>(p:Engine<X,E>,rho:Resolver,f:CommandSemantics,fair:spec_fn(StockRun<X,E>)->bool,used:Used<X,E>) -> bool {
    (forall|e:Run<X,E>,k:nat,id:nat| #[trigger] execution_using(p,rho,e) && fair(project(e)) && front_fair(p,e)
            && (#[trigger] (e.state)(k)).calls.contains_key(id) && #[trigger] live_from(p,project(e),k,id)
            ==> exists|j:nat| j>=k && (#[trigger] answer((e.state)(j),id)).is_some()) &&
        (forall|x:State<X>,id:nat,q:Set<Replica>| #[trigger] reachable(p,x) && x.calls.contains_key(id)
            && #[trigger] x.calls[id]==fresh(Method::Read) && (p.client)(x.base,id) && #[trigger] majority(q) && q.subset_of((p.up)(x.base))
            ==> exists|t:Seq<State<X>>,a:Seq<Event<E>>,v:int| #[trigger] outer_service(p,used,x,id,q,t,a,v) && path_using(p,rho,t,a)) &&
        (forall|t:Seq<State<X>>,a:Seq<Event<E>>,id:nat,q:Set<Replica>,i:nat,k:nat|
            #[trigger] path_using(p,rho,t,a) && t[0]==initial(p) && i<k<=a.len() && #[trigger] a[i as int]==Event::Invoke(id,Method::Read)
            && #[trigger] majority(q) && (#[trigger] answer(t[k as int],id)).is_some()
            && (forall|j:int| i<=j<k ==> #[trigger] serving_work(used,id,t[j],a[j]).subset_of(q)) ==> has_sample(p,t,q,id,i,k)) &&
        (forall|t:Seq<State<X>>,a:Seq<Event<E>>| #[trigger] path_using(p,rho,t,a) && t[0]==initial(p)
            ==> exists|g:Grid| #[trigger] ordered(g,f,a.len()) && certifies(g,a.len(),
                |i:nat,id:nat,m:Method|a[i as int]==Event::Invoke(id,m),|i:nat,id:nat|answer(t[i as int],id)))
}
pub proof fn all_stock_services<X,E>(p:Engine<X,E>,rho:Resolver,f:CommandSemantics,fair:spec_fn(StockRun<X,E>)->bool,used:Used<X,E>)
    requires ports(p),serves_root(rho),stock_a(p,fair,used),base_linearizable(p,f),
    ensures stock_contract(p,rho,f,fair,used),
{
    hide(path);hide(path_using);hide(outer_service);hide(ordered);hide(front_fair);hide(execution_using);
    construction_preserves_full_a_and_safety(p,f,fair,used);
    assert forall|e:Run<X,E>| #[trigger] execution_using(p,rho,e) implies execution(p,e) by {same_runs(p,rho,e);}
    let s=initial(p);assert(path(p,seq![s],Seq::empty())) by {reveal(path);} assert(reachable(p,s));
    assert forall|t:Seq<State<X>>,a:Seq<Event<E>>| #[trigger] path_using(p,rho,t,a) && t[0]==s implies path(p,t,a) by {same_paths(p,rho,t,a);}
    assert forall|x:State<X>,id:nat,q:Set<Replica>| #[trigger] reachable(p,x) && x.calls.contains_key(id)
        && #[trigger] x.calls[id]==fresh(Method::Read) && (p.client)(x.base,id) && #[trigger] majority(q) && q.subset_of((p.up)(x.base))
        implies exists|t:Seq<State<X>>,a:Seq<Event<E>>,v:int| #[trigger] outer_service(p,used,x,id,q,t,a,v) && path_using(p,rho,t,a) by {
        let (t,a,v)=choose|t:Seq<State<X>>,a:Seq<Event<E>>,v:int| #[trigger] outer_service(p,used,x,id,q,t,a,v);
        reveal(outer_service);same_paths(p,rho,t,a);
    }
}

pub proof fn concrete_fallback_stock(f:CommandSemantics)
    ensures stock_contract(base::engine(f),resolver(),f,|e|base::fair(e),base::used()),
{
    base::concrete_full_a(f);fallback_serves_root();
    all_stock_services(base::engine(f),resolver(),f,|e|base::fair(e),base::used());
}

pub open spec fn call(b:Fork,k:nat) -> Call {
    let t=sched::original_time(k);
    Call {legs:|r| if r==Replica::R3 && 11<=k<=13 {Leg::AtServer} else {
        first_leg(if k<=10 {sched::rival(b)} else {b},r,t)
    },answer:if k>=16 {Some(first_value(b))} else {None},..fresh(Method::Read)}
}
pub open spec fn cut(b:Fork,k:nat) -> Cut {
    let n=sched::net(b,k);
    let calls=if k<3 {Map::empty()} else {Map::empty().insert(1nat,call(b,k))};
    Cut {net:n,core:State{base:storage(n),closed:Set::empty(),calls:if k==19 {calls.insert(2,fresh(Method::Read))} else {calls}}}
}
// The weak and strong port decoders see the same advance as the shared
// network. This relation also checks the invocation and the actual
// first-client RPC guard at its own stage.
pub open spec fn joint(f:CommandSemantics,rho:Resolver,s:Cut,a:delivery::Action<Wire>,u:Cut) -> bool {
    let p=base::engine(f);
    let begin=invocation(s.core,s.net,a);let mid=apply_event(rho,p,s.core,begin);let ev=inner(s.net,a);
    let c=if s.core.calls.contains_key(1) {s.core.calls[1]} else {fresh(Method::Read)};
    delivery::enabled(s.net,a) && enabled(p,s.core,begin) && enabled(p,mid,ev)
        && valid(s.net,service(s.net,a,Process::FirstClient),c,Process::FirstClient)
        && u.core==weak_part(apply_event(rho,p,mid,ev),s.net,a) && u.net==delivery::advance(|x,w|cell(x,w),s.net,a)
}
pub open spec fn genuine_turn(f:CommandSemantics,rho:Resolver,b:Fork,k:nat) -> bool {
    joint(f,rho,cut(b,k),sched::action(b,k),cut(b,k+1))
}
pub open spec fn original(b:Fork,k:nat) -> Cut {
    Cut{core:crate::facade_hybrid::prefix(b,k),net:state_after(b,k)}
}
pub proof fn original_for(f:CommandSemantics,rho:Resolver,b:Fork,k:nat)
    requires k<17,rho(crate::metadata_pair::first_rows(b,13))==Some(first_value(b)),
    ensures joint(f,rho,original(b,k),actions_to_crash(b)[k as int],original(b,k+1)),
{
    hide(crate::facade_transport::at_time);
    crate::facade_hybrid::real_prefix(f,b,k);prefix_transport_is_enabled(b);prefix_index(k as int);
    crate::facade_transport::actual_first_rpc(b,k);
    let s=original(b,k);let wire=actions_to_crash(b)[k as int];let p=base::engine(f);
    let begin=invocation(s.core,s.net,wire);let mid=step(p,s.core,begin);let a=inner(s.net,wire);
    if k==13 {
        assert(rows(s.core.calls[1]) =~= crate::metadata_pair::first_rows(b,13));
        assert(crate::metadata_reader::unanimous(rows(s.core.calls[1])));
        assert(apply_event(rho,p,mid,a).calls =~= step(p,mid,a).calls);
    }
    assert(apply_event(rho,p,s.core,begin)==mid && apply_event(rho,p,mid,a)==step(p,mid,a));
    assert(checkpoint_states(b)[k as int]==s.net && checkpoint_states(b)[k as int+1]==original(b,k+1).net);
}
pub proof fn actual_original(f:CommandSemantics,b:Fork,k:nat)
    requires k<17,
    ensures joint(f,resolver(),original(b,k),actions_to_crash(b)[k as int],original(b,k+1)),
{
    assert(crate::metadata_reader::unanimous(crate::metadata_pair::first_rows(b,13)));
    original_for(f,resolver(),b,k);
}
pub proof fn actual_entry(b:Fork)
    ensures cut(b,0)==original(b,0),crate::facade_hybrid::prefix_entry(crate::weak_round::paper_ops(),b),
{
    crate::facade_hybrid::weak_calls_and_issued_offers(crate::weak_round::paper_ops(),b);
    sched::transport(b);prefix_transport_is_enabled(b);
    assert(original(b,0).net==after_local_rmws());
    assert(cut(b,0).core.calls =~= original(b,0).core.calls);
    assert(cut(b,0).core.base.disk =~= original(b,0).core.base.disk);
    assert(cut(b,0).core.base.live =~= original(b,0).core.base.live);
}
#[verifier::rlimit(35)]
pub proof fn executes_switched_prefix(f:CommandSemantics,b:Fork,k:nat)
    requires k<19,
    ensures genuine_turn(f,resolver(),b,k),
{
    if k<17 {prefix_index(k as int);}
    sched::transport(b);
    let s=cut(b,k);let u=cut(b,k+1);let a=sched::action(b,k);let p=base::engine(f);let rho=resolver();
    assert(sched::states(b)[k as int]==s.net && sched::actions(b)[k as int]==a);
    let mid=apply_event(rho,p,s.core,invocation(s.core,s.net,a));
    let v=weak_part(apply_event(rho,p,mid,inner(s.net,a)),s.net,a);
    assert(mid.closed =~= s.core.closed);assert(v.closed =~= u.core.closed);
    assert(v.base.live =~= u.core.base.live);assert(v.base.disk =~= u.core.base.disk);
    if k==15 {assert(rows(mid.calls[1]) =~= crate::metadata_pair::first_rows(b,13));assert(crate::metadata_reader::unanimous(rows(mid.calls[1])));}
    if k>=2 {assert(v.calls[1].legs =~= u.core.calls[1].legs);}
    assert(v.calls =~= u.core.calls);
}
}
