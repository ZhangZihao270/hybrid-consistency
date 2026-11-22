// The original two reads, using physical first returns and all native
// ordinary continuations from the independent second invocation.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::fair_read as fair;
use crate::first_assembly::{self as asm, Service};
use crate::fork_alternatives as fork;
use crate::fork_information::caller2;
use crate::guarded_comparison as cmp;
use crate::hybrid_majority as maj;
use crate::independent_read::{self as read, State};
use crate::promotion_wait as wait;
use crate::protocol::survivor_actor;
use crate::read_call::{Event,Program};
use crate::read_nonblocking as nb;
use crate::survivors::after_crash;

verus! {

pub open spec fn invocation<S>(m:Program<S>,p:Service<S>) -> State<S> {
    asm::drive(m,p.states.last(),fork::wake())
}

pub open spec fn weak_packets<S>(x:State<S>) -> Map<nat,Packet<Wire>> {
    let q=x.cfg.net.pending;
    q.restrict(q.dom().filter(|i:nat| q[i].path==Path::Weak))
}

pub open spec fn masks_send(mask:Set<nat>,a:Event) -> bool {
    a is Send && mask.contains(a->Send_0)
}

pub open spec fn uses_name(mask:Set<nat>,s:Seq<Event>) -> bool {
    exists|j:int| 0<=j<s.len() && masks_send(mask,#[trigger] s[j])
}

// Only the payload/path of the actual transition identifies postponed
// work. All request, delivery and ordinary-send guards are the native ones.
pub open spec fn step<S>(m:Program<S>,quiet:bool) -> wait::Relation<State<S>,Event> {
    |x:State<S>,a:Event,y:State<S>| read::prefix_step(m)(x,a,y)
        && (!quiet || !cmp::weak_work(process_step(x.cfg.net,a)))
}

pub open spec fn completes<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>,quiet:bool) -> bool
    decreases s.len(),
{
    if s.len()==0 {read::returned(res)(x)} else {
        let a=s[0];let y=read::next(m,x,a);
        !read::returned(res)(x) && step(m,quiet)(x,a,y) && completes(m,res,y,s.drop_first(),quiet)
    }
}

pub open spec fn value<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>) -> Option<int> {
    res(caller2(asm::drive(m,x,s)))
}

pub open spec fn same_reader<S>(x:State<S>,y:State<S>) -> bool {
    caller2(x)==caller2(y) && x.calls==y.calls && x.requested==y.requested && x.first_requested==y.first_requested
}

// The existing issued-majority liveness predicate starts after the fanout.
// Here StartSecondClient is the invocation. Its native prefix_step may
// send requests, use previously queued messages, or complete immediately.
pub open spec fn call_run<S>(m:Program<S>,x:State<S>,e:fair::Run<S>) -> bool {
    (e.state)(0)==x && forall|i:nat| read::prefix_step(m)((e.state)(i),#[trigger] (e.action)(i),(e.state)(i+1))
}

pub open spec fn states<S>(m:Program<S>,x:State<S>,s:Seq<Event>) -> Seq<State<S>> {
    Seq::new(s.len()+1,|i:int| asm::drive(m,x,s.take(i)))
}

pub open spec fn available<S>(x:State<S>) -> bool {
    maj::sole(x.cfg.net,live_pair()) && live(x.cfg.net,Process::SecondClient)
}

proof fn live_through_call<S>(m:Program<S>,x:State<S>,e:fair::Run<S>,k:nat)
    requires after_crash(x.cfg.net),call_run(m,x,e),
    ensures after_crash((e.state)(k).cfg.net),available((e.state)(k)),
    decreases k,
{
    if k>0 {
        live_through_call(m,x,e,(k-1) as nat);
        assert(read::prefix_step(m)((e.state)((k-1) as nat),(e.action)((k-1) as nat),(e.state)(k)));
    }
    assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
}

pub open spec fn invocation_a<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,run:fair::Runnable) -> bool {
    (forall|e:fair::Run<S>| #[trigger] call_run(m,x,e) && fair::fair(e,run)
        && (forall|k:nat| #[trigger] available((e.state)(k)))
        ==> exists|i:nat| #[trigger] read::returned(res)((e.state)(i)))
    && (forall|s:Seq<Event>| #[trigger] completes(m,res,x,s,false)
        && (forall|k:int| 0<=k<=s.len() ==> #[trigger] available(states(m,x,s)[k]))
        ==> maj::held(states(m,x,s),live_pair(),value(m,res,x,s).unwrap()))
}

pub open spec fn weak_step<S>() -> wait::Relation<State<S>,Event> {
    |x:State<S>,a:Event,_y:State<S>| cmp::weak_work(process_step(x.cfg.net,a))
}

pub open spec fn opportunity<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,run:fair::Runnable) -> bool {
    invocation_a(m,res,x,run)
        && (exists|e:fair::Run<S>| #[trigger] call_run(m,x,e) && fair::fair(e,run))
        && !wait::needs_class(read::prefix_step(m),read::returned(res),x,weak_step())
}

proof fn native_actions<S>(m:Program<S>,res:spec_fn(S)->Option<int>,p:Service<S>,k:nat)
    requires wait::first_return(read::prefix_step(m),read::returned(res),p.states[0],p),
        !wait::uses(p,weak_step()),k<=p.actions.len(),
    ensures completes(m,res,p.states[k as int],p.actions.skip(k as int),true),
    decreases p.actions.len()-k,
{
    let s=p.actions.skip(k as int);
    if k<p.actions.len() {
        let a=p.actions[k as int];let x=p.states[k as int];let y=p.states[k as int+1];
        assert(read::prefix_step(m)(x,a,y) && !weak_step()(x,a,y));
        assert(s.drop_first() =~= p.actions.skip(k as int+1));native_actions(m,res,p,k+1);
    }
}

pub proof fn native_return_from_a<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,run:fair::Runnable) -> (s:Seq<Event>)
    requires after_crash(x.cfg.net),maj::sole(x.cfg.net,live_pair()),opportunity(m,res,x,run),
    ensures completes(m,res,x,s,true),
{
    let d=read::returned(res);let st=read::prefix_step(m);
    if d(x) {Seq::empty()} else {
        let e=choose|e:fair::Run<S>| #[trigger] call_run(m,x,e) && fair::fair(e,run);
        assert forall|k:nat| #[trigger] available((e.state)(k)) by {live_through_call(m,x,e,k);}
        let k=choose|i:nat| #[trigger] d((e.state)(i));
        let p=fair::initial_block(e,k);
        assert forall|i:int| 0<=i<p.actions.len() implies st(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
            assert(st((e.state)(i as nat),(e.action)(i as nat),(e.state)((i+1) as nat)));
        }
        nb::from_path(st,d,p,0);assert(nb::possible(st,d,x));nb::first_response_iff(st,d,x);
        let q=choose|q:Service<S>| #[trigger] wait::first_return(st,d,x,q) && !wait::uses(q,weak_step());
        native_actions(m,res,q,0);assert(q.actions.skip(0) =~= q.actions);q.actions
    }
}

pub(crate) proof fn completion_facts<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>)
    requires after_crash(x.cfg.net),completes(m,res,x,s,true),
    ensures completes(m,res,x,s,false),value(m,res,x,s).is_some(),asm::prefix(m,x,s,true),
        forall|k:int| 0<=k<=s.len() ==> #[trigger] available(states(m,x,s)[k]),
        forall|k:int| 0<=k<=s.len() ==> (#[trigger] states(m,x,s)[k]).cfg.net.locals==x.cfg.net.locals,
        forall|k:int| 0<=k<=s.len() ==> #[trigger] weak_packets(states(m,x,s)[k])==weak_packets(x),
        forall|k:int| 0<=k<s.len() && (#[trigger] s[k]) is Send ==>
            !states(m,x,s)[k].cfg.net.pending.contains_key(s[k]->Send_0) && !weak_packets(x).contains_key(s[k]->Send_0),
        forall|k:int| 0<=k<s.len() ==> survivor_actor(#[trigger] process_step(states(m,x,s)[k].cfg.net,s[k]).actor),
    decreases s.len(),
{
    assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
    if s.len()>0 {
        let a=s[0];let y=read::next(m,x,a);let tail=s.drop_first();
        assert(after_crash(y.cfg.net) && a!=Action::StopFirstClient);
        assert(weak_packets(y) =~= weak_packets(x));
        assert(y.cfg.net.locals =~= x.cfg.net.locals) by {
            assert forall|r:Replica| (#[trigger] local_input(x.cfg.net,a,r)).is_none()
                || !(local_input(x.cfg.net,a,r).unwrap() is Copy) by {};
        }
        completion_facts(m,res,y,tail);
        assert forall|k:int| 1<=k<=s.len() implies #[trigger] states(m,x,s)[k]==states(m,y,tail)[k-1] by {
            assert(s.take(k)[0]==a && s.take(k).drop_first() =~= tail.take(k-1));
        }
        assert forall|k:int| 0<=k<s.len() implies survivor_actor(#[trigger] process_step(states(m,x,s)[k].cfg.net,s[k]).actor) by {
            if k>0 {assert(s[k]==tail[k-1]);assert(survivor_actor(process_step(states(m,y,tail)[k-1].cfg.net,tail[k-1]).actor));}
        }
        assert forall|k:int| 0<=k<s.len() && (#[trigger] s[k]) is Send implies
            !states(m,x,s)[k].cfg.net.pending.contains_key(s[k]->Send_0) && !weak_packets(x).contains_key(s[k]->Send_0) by {
            if k>0 {assert(s[k]==tail[k-1]);}
        }
    }
}

pub proof fn sampled_native_return<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>,run:fair::Runnable)
    requires after_crash(x.cfg.net),survivor(x.cfg.net)==(2int,5int),invocation_a(m,res,x,run),completes(m,res,x,s,true),
    ensures maj::held(states(m,x,s),live_pair(),value(m,res,x,s).unwrap()),
        value(m,res,x,s)==Some(2) || value(m,res,x,s)==Some(5),asm::prefix(m,x,s,true),
        forall|k:int| 0<=k<=s.len() ==> #[trigger] weak_packets(states(m,x,s)[k])==weak_packets(x),
        forall|k:int| 0<=k<s.len() ==> survivor_actor(#[trigger] process_step(states(m,x,s)[k].cfg.net,s[k]).actor),
{
    completion_facts(m,res,x,s);let v=value(m,res,x,s).unwrap();
    let (i,r)=choose|i:int,r:Replica| 0<=i<states(m,x,s).len() && live_pair().contains(r)
        && #[trigger] (states(m,x,s)[i].cfg.net.locals)(r)==v;
    assert(states(m,x,s)[i].cfg.net.locals==x.cfg.net.locals);
}

}
