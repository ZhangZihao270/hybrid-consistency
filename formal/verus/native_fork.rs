// The original two reads, using physical first returns and all native
// ordinary continuations from the independent second invocation.
use vstd::prelude::*;
use crate::{Op, Replica, checkpoint::*, delivery::*, precedence};
use crate::coupled_construction as build;
use crate::coupled_reads::legal_returns;
use crate::envelope_names as names;
use crate::fair_read as fair;
use crate::first_assembly::{self as asm, Service};
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_splice as tape;
use crate::fork_alternatives as fork;
use crate::fork_information::{caller2, Residual};
use crate::guarded_comparison as cmp;
use crate::hybrid_majority as maj;
use crate::independent_read::{self as read, State};
use crate::order_extension as history;
use crate::original_application as app;
use crate::promotion_wait as wait;
use crate::protocol::survivor_actor;
use crate::read_call::{Event,Program};
use crate::read_nonblocking as nb;
use crate::survivors::after_crash;

verus! {

pub open spec fn admitted<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:Service<S>) -> bool {
    app::held_first_return(m,first,b,p)
}

pub open spec fn candidate<S>(m:Program<S>,first:spec_fn(S)->int,n:Notice,a:Service<S>,b:Service<S>) -> bool {
    admitted(m,first,alpha(n),a) && admitted(m,first,beta(n),b)
}

pub open spec fn invocation<S>(m:Program<S>,p:Service<S>) -> State<S> {
    asm::drive(m,p.states.last(),fork::wake())
}

pub open spec fn weak_packets<S>(x:State<S>) -> Map<nat,Packet<Wire>> {
    let q=x.cfg.net.pending;
    q.restrict(q.dom().filter(|i:nat| q[i].path==Path::Weak))
}

// A quiet continuation can deliver ordinary packets addressed to a live
// process, including packets already sent by R3. A permanently occupied
// envelope can also affect a Send guard, even when its body is inaccessible.
pub open spec fn record<S>(x:State<S>,mask:Set<nat>) -> Residual<S> {
    let q=x.cfg.net.pending;
    let blocked = q.dom().filter(|i:nat| q[i].path==Path::Weak || q[i].to==Process::FirstClient);
    Residual {
        cells:survivor(x.cfg.net), left:(x.cfg.private)(at(Replica::R1)), right:(x.cfg.private)(at(Replica::R2)),
        owners:x.owners, reserved:x.reserved.union(read::retired_at_failure(x)).union(blocked).union(mask),
        packets: |i:nat| if q.contains_key(i) && q[i].path!=Path::Weak && survivor_actor(q[i].to) {
            Some(q[i])
        } else {None},
    }
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

pub open spec fn writers<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,mask:Set<nat>) -> Set<Op> {
    set![Op::W1,Op::W2].filter(|w:Op| exists|s:Seq<Event>| !uses_name(mask,s)
        && #[trigger] completes(m,res,x,s,true) && value(m,res,x,s)==Some(crate::next(w,1)))
}

pub open spec fn history_failure<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,mask:Set<nat>) -> bool {
    exists|s:Seq<Event>| !uses_name(mask,s) && #[trigger] completes(m,res,x,s,true)
        && !legal_returns(first_value(b),value(m,res,x,s).unwrap())
}

pub(crate) proof fn first_frame<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:Service<S>,k:nat)
    requires admitted(m,first,b,p),k<p.states.len(),
    ensures ({
        let root=build::root(m,app::lanes(),b);let z=p.states[k as int];
        z.cfg.net.locals==root.cfg.net.locals && z.cfg.net.unavailable.is_none()
            && !z.cfg.net.r3_crashed && !z.cfg.net.first_stopped && !z.cfg.net.second_started
            && z.calls==root.calls && z.requested.is_empty() && z.first_requested==z.calls.first
            && caller2(z)==(m.initial)(Process::SecondClient) && pair::c1_protected(z)
            && weak_packets(z)==weak_packets(root)
            && (forall|i:nat| #[trigger] weak_packets(z).contains_key(i) ==> weak_packets(z)[i].to is At)
    }),
    decreases k,
{
    let root=build::root(m,app::lanes(),b);let z=p.states[k as int];
    if k==0 {
        assert forall|i:nat| #[trigger] weak_packets(root).contains_key(i) implies weak_packets(root)[i].to is At by {};
        assert forall|i:nat| #[trigger] root.cfg.net.pending.contains_key(i) implies root.cfg.net.pending[i].to!=Process::FirstClient by {};
        assert(caller2(root)==(m.initial)(Process::SecondClient)) by {
            assert forall|j:int| 0<=j<5 implies (#[trigger] checkpoint_observations(b)[j]).actor!=Process::SecondClient by {prefix_index(j);}
            crate::protocol::memory_during_quiescence(m,checkpoint_observations(b),Process::SecondClient,0,5);
        }
    } else {
        let j=k as int-1;let x=p.states[j];let a=p.actions[j];let q=x.cfg.net.pending;
        first_frame(m,first,b,p,(k-1) as nat);
        assert(mail::active_step(m)(x,a,z) && !mail::posted(m)(x) && !app::weak_replica_step()(x,a,z));
        app::quiet_cells(m,x,a,z);
        assert forall|i:nat| z.cfg.net.pending.contains_key(i) && z.cfg.net.pending[i].to==Process::FirstClient
            implies #[trigger] z.reserved.contains(i) by {
            if z.cfg.net.pending.get(i)==q.get(i) {assert(x.reserved.contains(i));}
        }
        assert(weak_packets(z) =~= weak_packets(x)) by {
            assert forall|i:nat| #[trigger] weak_packets(z).get(i)==weak_packets(x).get(i) by {
                if a==Action::<Wire>::Deliver(i) && weak_packets(x).contains_key(i) {assert(weak_packets(x)[i].to is At);}
            }
        }
    }
}

pub(crate) proof fn silent_callback<S>(m:Program<S>,x:State<S>,a:Event,y:State<S>,mask:Set<nat>)
    requires pair::c1_protected(x),mail::active_step(m)(x,a,y),!mail::posted(m)(x),
        process_step(x.cfg.net,a).actor==Process::FirstClient,
    ensures record(x,mask)==record(y,mask),
{
    let l=record(x,mask);let r=record(y,mask);
    assert(l.reserved =~= r.reserved) by {
        assert forall|i:nat| #[trigger] l.reserved.contains(i)==r.reserved.contains(i) by {
            if a==Action::<Wire>::Deliver(i) {assert(x.reserved.contains(i));}
        }
    }
    assert(l.packets =~= r.packets);
}

// Nothing is normalized or dropped from the SR1 path. Its final callback
// can read an arbitrary accepted input, including a private CPU input.
pub proof fn actual_handoff<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:Service<S>,mask:Set<nat>)
    requires admitted(m,first,b,p),crate::first_schedule::startup(m),
    ensures ({
        let z=p.states.last();let x=invocation(m,p);let root=build::root(m,app::lanes(),b);
        first((z.cfg.private)(Process::FirstClient))==first_value(b)
            && p.actions.len()>0 && record(p.states[p.actions.len() as int-1],mask)==record(z,mask)
            && (forall|j:int| 0<=j<p.actions.len() && (#[trigger] tape::record(p,0)[j]).actor==Process::FirstClient
                ==> record(p.states[j],mask)==record(p.states[j+1],mask))
            && asm::prefix(m,z,fork::wake(),true) && after_crash(x.cfg.net) && maj::sole(x.cfg.net,live_pair())
            && record(z,mask)==record(x,mask) && weak_packets(x)==weak_packets(root)
            && x.cfg.net.pending==z.cfg.net.pending && survivor(x.cfg.net)==(2int,5int)
            && x.calls==root.calls && x.requested.is_empty() && x.first_requested==x.calls.first
            && caller2(x)==crate::read_issue::started(m)
    }),
{
    let z=p.states.last();let x=invocation(m,p);let j=p.actions.len() as int-1;
    first_frame(m,first,b,p,p.actions.len());
    let (k,r)=choose|k:int,r:Replica| 0<=k<p.states.len() && crate::first_quorum(b.branch).contains(r)
        && #[trigger] (p.states[k].cfg.net.locals)(r)==first((z.cfg.private)(Process::FirstClient));
    first_frame(m,first,b,p,k as nat);
    assert(first((z.cfg.private)(Process::FirstClient))==first_value(b));
    assert(p.actions.len()>0);
    assert(mail::active_step(m)(p.states[j],p.actions[j],z) && !mail::posted(m)(p.states[j]));
    assert(process_step(p.states[j].cfg.net,p.actions[j]).actor==Process::FirstClient);
    assert forall|i:int| 0<=i<p.actions.len() && (#[trigger] tape::record(p,0)[i]).actor==Process::FirstClient
        implies record(p.states[i],mask)==record(p.states[i+1],mask) by {
        first_frame(m,first,b,p,i as nat);
        assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));
        silent_callback(m,p.states[i],p.actions[i],p.states[i+1],mask);
    }
    assert(tape::record(p,0)[j].actor==Process::FirstClient);
    reveal_with_fuel(asm::drive,4);reveal_with_fuel(asm::prefix,4);
    assert(record(z,mask).reserved =~= record(x,mask).reserved);
    assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
}

pub open spec fn same_reader<S>(x:State<S>,y:State<S>) -> bool {
    caller2(x)==caller2(y) && x.calls==y.calls && x.requested==y.requested && x.first_requested==y.first_requested
}

// The mask optionally fixes the availability of extra sends in both
// records. The empty mask compares the entire native ordinary interface.
proof fn replay_step<S>(m:Program<S>,x:State<S>,y:State<S>,a:Event,mask:Set<nat>)
    requires after_crash(x.cfg.net),after_crash(y.cfg.net),same_reader(x,y),record(x,mask)==record(y,mask),
        !masks_send(mask,a),step(m,true)(x,a,read::next(m,x,a)),
    ensures ({
        let u=read::next(m,x,a);let v=read::next(m,y,a);
        step(m,true)(y,a,v) && after_crash(u.cfg.net) && after_crash(v.cfg.net)
            && process_step(x.cfg.net,a)==process_step(y.cfg.net,a)
            && same_reader(u,v) && record(u,mask)==record(v,mask)
    }),
{
    let rx=record(x,mask);let ry=record(y,mask);
    let ex=process_step(x.cfg.net,a);let ey=process_step(y.cfg.net,a);
    if a is Deliver {
        let i=a->Deliver_0;assert(live(x.cfg.net,x.cfg.net.pending[i].to));
        assert((rx.packets)(i)==Some(x.cfg.net.pending[i]) && (rx.packets)(i)==(ry.packets)(i));
    } else if a is Send {
        let i=a->Send_0;assert(!rx.reserved.contains(i)) by {
            if x.owners.contains_key(i) {assert(x.owners[i]==a->Send_1.from);}
        }
        assert(!ry.reserved.contains(i) && (ry.packets)(i).is_none());
    }
    assert(survivor_actor(ex.actor) && ex==ey);
    assert((x.cfg.private)(ex.actor)==(y.cfg.private)(ey.actor));
    let u=read::next(m,x,a);let v=read::next(m,y,a);
    assert(step(m,true)(y,a,v));
    assert(record(u,mask).reserved =~= record(v,mask).reserved) by {
        assert forall|i:nat| #[trigger] record(u,mask).reserved.contains(i)==record(v,mask).reserved.contains(i) by {
            assert(rx.reserved.contains(i)==ry.reserved.contains(i));
            if a==Action::<Wire>::Deliver(i) {assert((rx.packets)(i).is_some());}
        }
    }
    assert(record(u,mask).packets =~= record(v,mask).packets) by {
        assert forall|i:nat| #[trigger] (record(u,mask).packets)(i)==(record(v,mask).packets)(i) by {
            assert((rx.packets)(i)==(ry.packets)(i));
        }
    }
}

pub proof fn replay_return<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>,s:Seq<Event>,mask:Set<nat>)
    requires after_crash(x.cfg.net),after_crash(y.cfg.net),same_reader(x,y),record(x,mask)==record(y,mask),
        !uses_name(mask,s),completes(m,res,x,s,true),
    ensures completes(m,res,y,s,true),value(m,res,x,s)==value(m,res,y,s),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0];let tail=s.drop_first();
        assert forall|i:int| 0<=i<tail.len() implies !masks_send(mask,#[trigger] tail[i]) by {assert(tail[i]==s[i+1]);}
        replay_step(m,x,y,a,mask);
        replay_return(m,res,read::next(m,x,a),read::next(m,y,a),tail,mask);
    }
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

proof fn legal_writers<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,s:Seq<Event>,mask:Set<nat>)
    requires after_crash(x.cfg.net),completes(m,res,x,s,true),!uses_name(mask,s),!history_failure(m,res,b,x,mask),
    ensures writers(m,res,x,mask)==set![observed_writer(b)],value(m,res,x,s)==Some(first_value(b)),
{
    completion_facts(m,res,x,s);
    fork::history_completion(b,value(m,res,x,s));
    let sources=writers(m,res,x,mask);let w=observed_writer(b);
    assert(crate::next(w,1)==first_value(b));assert(sources.contains(w));
    assert forall|v:Op| #[trigger] sources.contains(v) implies v==w by {
        let u=choose|u:Seq<Event>| !uses_name(mask,u) && #[trigger] completes(m,res,x,u,true)
            && value(m,res,x,u)==Some(crate::next(v,1));
        fork::history_completion(b,value(m,res,x,u));
    }
    assert(sources =~= set![w]);
}

// This is the *same* functional rule used by retained_order, with writer
// options obtained from native returns instead of the numbered monitor.
pub open spec fn protected<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,y:State<S>,
    mask:Set<nat>,orders:precedence::Possible) -> bool {
    app::preserves_extension_option(b,writers(m,res,x,mask),writers(m,res,y,mask),orders)
}

pub proof fn native_fork_requires_preservation<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    n:Notice,a:Service<S>,b:Service<S>,sa:Seq<Event>,sb:Seq<Event>,mask:Set<nat>,aa:bool,ab:bool)
    requires candidate(m,first,n,a,b),crate::first_schedule::startup(m),n!=Notice::Replication ==> aa && ab,
        completes(m,res,invocation(m,a),sa,true),completes(m,res,invocation(m,b),sb,true),
        !uses_name(mask,sa),!uses_name(mask,sb),
    ensures ({
        let l=alpha(n);let r=beta(n);let x=invocation(m,a);let y=invocation(m,b);let orders=precedence::actual_cuts(n,aa,ab);
        history_failure(m,res,l,x,mask) || history_failure(m,res,r,y,mask) || (
            writers(m,res,x,mask)==set![Op::W2] && writers(m,res,y,mask)==set![Op::W1]
            && value(m,res,x,sa)==Some(5) && value(m,res,y,sb)==Some(2)
            && record(a.states.last(),mask)==record(x,mask) && record(b.states.last(),mask)==record(y,mask)
            && record(x,mask)!=record(y,mask)
            && !protected(m,res,l,x,y,mask,orders) && !protected(m,res,r,y,x,mask,orders))
    }),
{
    let l=alpha(n);let r=beta(n);let x=invocation(m,a);let y=invocation(m,b);
    actual_handoff(m,first,l,a,mask);actual_handoff(m,first,r,b,mask);
    if !history_failure(m,res,l,x,mask) && !history_failure(m,res,r,y,mask) {
        legal_writers(m,res,l,x,sa,mask);legal_writers(m,res,r,y,sb,mask);
        if record(x,mask)==record(y,mask) {same_record_same_writers(m,res,x,y,mask);}
        let wa=writers(m,res,x,mask);let wb=writers(m,res,y,mask);
        history::canonical_orders_exist(l);history::canonical_orders_exist(r);
        history::extension_iff_writer(l,history::at_first(l),Op::W1);history::extension_iff_writer(l,history::at_first(l),Op::W2);
        history::extension_iff_writer(r,history::at_first(r),Op::W1);history::extension_iff_writer(r,history::at_first(r),Op::W2);
        let orders=precedence::actual_cuts(n,aa,ab);
        let ol=weak_assignment(l,aa).ops;let or=weak_assignment(r,ab).ops;
        weak_assignment_at_delivery(l,aa);weak_assignment_at_delivery(r,ab);precedence::equal_independent_views(r);
        assert(wa.contains(Op::W2) && wb.contains(Op::W1));
        assert(app::extension_option(l,wa) && !app::extension_option(l,wb));
        assert(app::extension_option(r,wb) && !app::extension_option(r,wa));
        assert(orders(precedence::independent_view(l),or) && !precedence::has_precedence(or,Op::W2,Op::W1));
        assert(orders(precedence::independent_view(r),ol) && !precedence::has_precedence(ol,Op::W1,Op::W2));
    }
}

pub proof fn same_record_same_writers<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>,mask:Set<nat>)
    requires after_crash(x.cfg.net),after_crash(y.cfg.net),same_reader(x,y),record(x,mask)==record(y,mask),
    ensures writers(m,res,x,mask)==writers(m,res,y,mask),
{
    let left=writers(m,res,x,mask);let right=writers(m,res,y,mask);
    assert forall|w:Op| #[trigger] left.contains(w)==#[trigger] right.contains(w) by {
        if left.contains(w) && !right.contains(w) {
            let s=choose|s:Seq<Event>| !uses_name(mask,s) && #[trigger] completes(m,res,x,s,true) && value(m,res,x,s)==Some(crate::next(w,1));
            replay_return(m,res,x,y,s,mask);
        } else if right.contains(w) && !left.contains(w) {
            let s=choose|s:Seq<Event>| !uses_name(mask,s) && #[trigger] completes(m,res,y,s,true) && value(m,res,y,s)==Some(crate::next(w,1));
            replay_return(m,res,y,x,s,mask);
        }
    }
    assert(left =~= right);
}

pub open spec fn frozen_names<S>(x:State<S>,y:State<S>) -> Set<nat> {
    weak_packets(x).dom().union(weak_packets(y).dom())
}

pub open spec fn observed_copy(b:Fork) -> Packet<Wire> {
    Packet{path:Path::Weak,from:at(crate::origin(b.branch)),to:at(Replica::R3),input:Wire::Copy(first_value(b))}
}

// The weak envelope present only in the other arm is the actual copy
// whose delivery supplied R3's value here. The confirmation is pending
// in both arms and cannot be the envelope used for a successful Send.
pub open spec fn opposing_copy<S>(b:Fork,x:State<S>,y:State<S>) -> bool {
    forall|i:nat| #[trigger] weak_packets(y).contains_key(i) && !weak_packets(x).contains_key(i)
        ==> weak_packets(y)[i]==observed_copy(b)
}

pub(crate) proof fn common_fanout<S>(m:Program<S>,n:Notice)
    ensures ({
        let a=build::root(m,app::lanes(),alpha(n));let b=build::root(m,app::lanes(),beta(n));let mask=frozen_names(a,b);
        record(a,mask)==record(b,mask) && opposing_copy(alpha(n),a,b) && opposing_copy(beta(n),b,a)
    }),
{
    let a=build::root(m,app::lanes(),alpha(n));let b=build::root(m,app::lanes(),beta(n));let mask=frozen_names(a,b);
    crate::coupled_traffic::pair_at_fanout(m,app::lanes(),n,crate::fork_information::identity());
    let left=record(a,mask);let right=record(b,mask);
    assert forall|i:nat| i>2 implies #[trigger] a.cfg.net.pending.get(i)==b.cfg.net.pending.get(i) by {
        assert(b.cfg.net.pending.get(i)==crate::coupled_traffic::packet(crate::fork_information::identity(),a.cfg.net.pending.get(i)));
    }
    assert(left.packets =~= right.packets) by {
        assert forall|i:nat| #[trigger] (left.packets)(i)==(right.packets)(i) by {if i<=2 {assert(i==0 || i==1 || i==2);}}
    }
    assert(left.reserved =~= right.reserved) by {
        assert forall|i:nat| #[trigger] left.reserved.contains(i)==right.reserved.contains(i) by {
            if i<=2 {assert(i==0 || i==1 || i==2);assert(mask.contains(i));}
        }
    }
}

pub open spec fn installed_record<S>(p:Service<S>,mask:Set<nat>,k:int) -> bool {
    let e=tape::record(p,0)[k];
    0<=k<p.actions.len() && e.actor is At && !cmp::weak_work(e)
        && record(p.states[k],mask)!=record(p.states[k+1],mask)
        && record(p.states[k+1],mask)==record(p.states.last(),mask)
}

proof fn last_record_change<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:Service<S>,mask:Set<nat>,k:nat) -> (j:int)
    requires admitted(m,first,b,p),k<p.states.len(),
        record(p.states[k as int],mask)==record(p.states.last(),mask),
        record(p.states[0],mask)!=record(p.states.last(),mask),
    ensures installed_record(p,mask,j),
    decreases k,
{
    assert(k>0);let i=k as int-1;let x=p.states[i];let y=p.states[i+1];let a=p.actions[i];
    if record(x,mask)==record(y,mask) {last_record_change(m,first,b,p,mask,(k-1) as nat)}
    else {
        first_frame(m,first,b,p,i as nat);
        assert(mail::active_step(m)(x,a,y) && !mail::posted(m)(x));
        if process_step(x.cfg.net,a).actor==Process::FirstClient {silent_callback(m,x,a,y,mask);}
        assert(!app::weak_replica_step()(x,a,y));i
    }
}

pub open spec fn has_return<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,mask:Set<nat>) -> bool {
    exists|s:Seq<Event>| !uses_name(mask,s) && #[trigger] completes(m,res,x,s,true)
}

// Every native completion in this arm must successfully send at a name
// occupied by a still-postponed weak packet in the other actual arm.
pub open spec fn requires_other_slot<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>) -> bool {
    (exists|s:Seq<Event>| #[trigger] completes(m,res,x,s,true)) &&
        forall|s:Seq<Event>| #[trigger] completes(m,res,x,s,true) ==> exists|j:int| 0<=j<s.len()
            && (#[trigger] s[j]) is Send && !states(m,x,s)[j].cfg.net.pending.contains_key(s[j]->Send_0)
            && weak_packets(y).contains_key(s[j]->Send_0)
}

pub proof fn necessary_send_iff<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>,witness:Seq<Event>)
    requires after_crash(x.cfg.net),completes(m,res,x,witness,true),
    ensures requires_other_slot(m,res,x,y)==!has_return(m,res,x,frozen_names(x,y)),
{
    let mask=frozen_names(x,y);
    if !has_return(m,res,x,mask) {
        assert forall|s:Seq<Event>| #[trigger] completes(m,res,x,s,true) implies exists|j:int| 0<=j<s.len()
            && (#[trigger] s[j]) is Send && !states(m,x,s)[j].cfg.net.pending.contains_key(s[j]->Send_0)
            && weak_packets(y).contains_key(s[j]->Send_0) by {
            completion_facts(m,res,x,s);
            let j=choose|j:int| 0<=j<s.len() && masks_send(mask,#[trigger] s[j]);
            assert(!weak_packets(x).contains_key(s[j]->Send_0));
        }
    } else if requires_other_slot(m,res,x,y) {
        let s=choose|s:Seq<Event>| !uses_name(mask,s) && #[trigger] completes(m,res,x,s,true);
        let j=choose|j:int| 0<=j<s.len() && (#[trigger] s[j]) is Send
            && !states(m,x,s)[j].cfg.net.pending.contains_key(s[j]->Send_0) && weak_packets(y).contains_key(s[j]->Send_0);
        assert(masks_send(mask,s[j]));
    }
}

pub open spec fn strong_record_changes_options<S>(m:Program<S>,res:spec_fn(S)->Option<int>,n:Notice,
    a:Service<S>,b:Service<S>,orders:precedence::Possible) -> bool {
    let x=invocation(m,a);let y=invocation(m,b);let mask=frozen_names(x,y);
    has_return(m,res,x,mask) && has_return(m,res,y,mask)
        && record(a.states[0],mask)==record(b.states[0],mask) && record(x,mask)!=record(y,mask)
        && record(a.states.last(),mask)==record(x,mask) && record(b.states.last(),mask)==record(y,mask)
        && ((exists|i:int| #[trigger] installed_record(a,mask,i)) || (exists|i:int| #[trigger] installed_record(b,mask,i)))
        && writers(m,res,x,mask)==set![Op::W2] && writers(m,res,y,mask)==set![Op::W1]
        && !protected(m,res,alpha(n),x,y,mask,orders) && !protected(m,res,beta(n),y,x,mask,orders)
}

// Hold exactly the two real sets of delayed weak envelopes fixed for new
// sends. No such restriction applies to original admission or progress.
// Messages already sent at any slot can still be delivered normally.
pub proof fn preserved_by_first_or_transport_dependency<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    n:Notice,a:Service<S>,b:Service<S>,sa:Seq<Event>,sb:Seq<Event>,aa:bool,ab:bool)
    requires candidate(m,first,n,a,b),crate::first_schedule::startup(m),n!=Notice::Replication ==> aa && ab,
        completes(m,res,invocation(m,a),sa,true),completes(m,res,invocation(m,b),sb,true),
        !history_failure(m,res,alpha(n),invocation(m,a),Set::empty()),
        !history_failure(m,res,beta(n),invocation(m,b),Set::empty()),
    ensures ({
        let x=invocation(m,a);let y=invocation(m,b);
        requires_other_slot(m,res,x,y) || requires_other_slot(m,res,y,x)
            || strong_record_changes_options(m,res,n,a,b,precedence::actual_cuts(n,aa,ab))
    }),
{
    let l=alpha(n);let r=beta(n);let x=invocation(m,a);let y=invocation(m,b);let mask=frozen_names(x,y);
    actual_handoff(m,first,l,a,mask);actual_handoff(m,first,r,b,mask);
    necessary_send_iff(m,res,x,y,sa);necessary_send_iff(m,res,y,x,sb);
    assert(frozen_names(y,x) =~= mask);
    if has_return(m,res,x,mask) && has_return(m,res,y,mask) {
        let u=choose|s:Seq<Event>| !uses_name(mask,s) && #[trigger] completes(m,res,x,s,true);
        let v=choose|s:Seq<Event>| !uses_name(mask,s) && #[trigger] completes(m,res,y,s,true);
        native_fork_requires_preservation(m,first,res,n,a,b,u,v,mask,aa,ab);
        assert(!history_failure(m,res,l,x,mask) && !history_failure(m,res,r,y,mask));
        common_fanout(m,n);
        assert(record(a.states[0],mask)==record(b.states[0],mask));
        if record(a.states[0],mask)!=record(a.states.last(),mask) {last_record_change(m,first,l,a,mask,a.actions.len());}
        else {last_record_change(m,first,r,b,mask,b.actions.len());}
    }
}

pub struct ReadPair<S> { pub first:Service<S>, pub second:Seq<Event> }

pub open spec fn completed_history<S>(raw:Program<S>,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    b:Fork,h:ReadPair<S>) -> bool {
    let l=app::lanes();let p=h.first;let z=p.states.last();let x=invocation(m,p);let s=h.second;
    let start=crate::independent_preparations::before_offers(raw,l);
    let actions=crate::independent_preparations::offers()+((asm::boot(Some(b))+p.actions)+(fork::wake()+s));
    admitted(m,first,b,p) && first((z.cfg.private)(Process::FirstClient))==first_value(b)
        && (forall|i:int| 0<=i<p.actions.len() ==> (#[trigger] tape::record(p,0)[i]).actor!=at(crate::sr1_majorities::missing(b)))
        && after_crash(x.cfg.net) && maj::sole(x.cfg.net,live_pair()) && x.cfg.net.pending==z.cfg.net.pending
        && weak_packets(x)==weak_packets(build::root(m,l,b))
        && (forall|i:int| 0<=i<=s.len() ==> #[trigger] weak_packets(states(m,x,s)[i])==weak_packets(x))
        && caller2(x)==crate::read_issue::started(m) && survivor(x.cfg.net)==(2int,5int)
        && completes(m,res,x,s,true) && maj::held(states(m,x,s),live_pair(),value(m,res,x,s).unwrap())
        && (value(m,res,x,s)==Some(2) || value(m,res,x,s)==Some(5))
        && asm::prefix(raw,start,actions,true) && asm::drive(raw,start,actions)==asm::drive(m,x,s)
}

pub open spec fn legal_history<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,h:ReadPair<S>) -> bool {
    legal_returns(first((h.first.states.last().cfg.private)(Process::FirstClient)),
        value(m,res,invocation(m,h.first),h.second).unwrap())
}

proof fn assemble<S>(raw:Program<S>,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,b:Fork,
    h:ReadPair<S>,run:fair::Runnable)
    requires m==crate::independent_preparations::after_offers(raw,app::lanes()),crate::first_schedule::startup(m),
        crate::first_dispatch::initiates(m),crate::first_dispatch::weak_open(m,b),
        ({
            let l=app::lanes();let start=crate::independent_preparations::before_offers(raw,l);let offers=crate::independent_preparations::offers();
            let cut=invocation(m,h.first);
            asm::prefix(raw,start,offers,true) && asm::drive(raw,start,offers)==asm::entry(m,l)
                && admitted(m,first,b,h.first)
                && (forall|i:int| 0<=i<h.first.actions.len() ==> (#[trigger] tape::record(h.first,0)[i]).actor!=at(crate::sr1_majorities::missing(b)))
                && invocation_a(m,res,cut,run) && completes(m,res,cut,h.second,true)
        }),
    ensures completed_history(raw,m,first,res,b,h),
{
    let l=app::lanes();let start=crate::independent_preparations::before_offers(raw,l);let pre=asm::boot(Some(b))+h.first.actions;
    let z=h.first.states.last();let x=invocation(m,h.first);let s=h.second;
    app::accepted_first_prefix(m,first,b,h.first);
    actual_handoff(m,first,b,h.first,Set::empty());sampled_native_return(m,res,x,s,run);
    asm::prefix_concat(m,z,fork::wake(),s,true);
    asm::prefix_concat(m,asm::entry(m,l),pre,fork::wake()+s,true);
    crate::independent_preparations::rebase_preserves_steps(raw,l,asm::entry(m,l),pre+(fork::wake()+s));
    asm::prefix_concat(raw,start,crate::independent_preparations::offers(),pre+(fork::wake()+s),true);
}

// Complete just the C2 invocation reached by this particular C1 service.
pub open spec fn selected_first<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:Service<S>) -> bool {
    admitted(m,first,b,p) && forall|i:int| 0<=i<p.actions.len() ==>
        (#[trigger] tape::record(p,0)[i]).actor!=at(crate::sr1_majorities::missing(b))
}

pub(crate) proof fn complete_selected_first<S>(raw:Program<S>,m:Program<S>,first:spec_fn(S)->int,
    res:spec_fn(S)->Option<int>,b:Fork,p:Service<S>,run:fair::Runnable) -> (h:ReadPair<S>)
    requires m==crate::independent_preparations::after_offers(raw,app::lanes()),
        crate::first_dispatch::initiates(m),crate::first_dispatch::weak_open(m,b),crate::first_schedule::startup(m),
        selected_first(m,first,b,p),opportunity(m,res,invocation(m,p),run),
        ({
            let start=crate::independent_preparations::before_offers(raw,app::lanes());
            let s=crate::independent_preparations::offers();
            asm::prefix(raw,start,s,true) && asm::drive(raw,start,s)==asm::entry(m,app::lanes())
        }),
    ensures h.first==p,completed_history(raw,m,first,res,b,h),
        history_failure(m,res,b,invocation(m,p),Set::empty()) ==> !legal_history(m,first,res,h),
{
    let x=invocation(m,p); let all=Set::<nat>::empty();
    actual_handoff(m,first,b,p,all);
    let s=native_return_from_a(m,res,x,run);
    let u=if history_failure(m,res,b,x,all) {
        choose|t:Seq<Event>| !uses_name(all,t) && #[trigger] completes(m,res,x,t,true)
            && !legal_returns(first_value(b),value(m,res,x,t).unwrap())
    } else {s};
    let h=ReadPair{first:p,second:u};
    assemble(raw,m,first,res,b,h,run);
    h
}

// Feasibility, no-await and independent SR2 service on the original workload.
pub open spec fn original_opportunities<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    n:Notice,run:fair::Runnable) -> bool {
    (forall|b:Fork| b.notice==n ==> #[trigger] crate::first_dispatch::weak_open(m,b)
        && mail::fair_opportunity(m,run,crate::first_schedule::reference(m,b,5))
        && !wait::needs_class(mail::active_step(m),mail::posted(m),crate::first_schedule::reference(m,b,5),app::weak_replica_step()))
    && (forall|b:Fork,p:Service<S>| b.notice==n && #[trigger] admitted(m,first,b,p)
        && (forall|j:int| 0<=j<p.actions.len() ==> (#[trigger] tape::record(p,0)[j]).actor!=at(crate::sr1_majorities::missing(b)))
        ==> opportunity(m,res,invocation(m,p),run))
}

// Shared by the two transport representations of the original construction.
pub open spec fn original_premises<S>(raw:Program<S>,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    n:Notice,run:fair::Runnable,aa:bool,ab:bool) -> bool {
        m==crate::independent_preparations::after_offers(raw,app::lanes()) && ({
            let x=crate::independent_preparations::before_offers(raw,app::lanes());let s=crate::independent_preparations::offers();
            crate::ordinary_service::allowed(raw,x.cfg,s[0]) && crate::ordinary_service::allowed(raw,read::next(raw,x,s[0]).cfg,s[1])
        })
        && crate::first_dispatch::initiates(m) && crate::first_schedule::startup(m) && (n!=Notice::Replication ==> aa && ab)
        && original_opportunities(m,first,res,n,run)
        && (forall|b:Fork| b.notice==n ==> #[trigger] maj::first_reference_a(m,first,res,b,run))
}

// Choose concrete histories. The T conclusions below are implications:
// the invocation and liveness premises contain no cross-history test.
pub proof fn original_hot_application<S>(raw:Program<S>,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    n:Notice,run:fair::Runnable,aa:bool,ab:bool) -> (histories:(ReadPair<S>,ReadPair<S>))
    requires original_premises(raw,m,first,res,n,run,aa,ab),
    ensures ({
        let (a,b)=histories;let l=alpha(n);let r=beta(n);let x=invocation(m,a.first);let y=invocation(m,b.first);
        let all=Set::<nat>::empty();let orders=precedence::actual_cuts(n,aa,ab);
        let weak=crate::guarded_history::weak_end();
        let bad=!legal_history(m,first,res,a) || !legal_history(m,first,res,b);
        weak.answers.get(crate::weak_round::request(Op::W1).id)==Some(1)
            && weak.answers.get(crate::weak_round::request(Op::W2).id)==Some(1)
            && candidate(m,first,n,a.first,b.first)
            && completed_history(raw,m,first,res,l,a) && completed_history(raw,m,first,res,r,b)
            && opposing_copy(l,x,y) && opposing_copy(r,y,x)
            && (requires_other_slot(m,res,x,y)==names::every_return_sends_at_copy(m,res,l,x,y))
            && (requires_other_slot(m,res,y,x)==names::every_return_sends_at_copy(m,res,r,y,x))
            && truthful_notice(l,weak_assignment(l,aa).ops) && truthful_notice(r,weak_assignment(r,ab).ops)
            && ((protected(m,res,l,x,y,all,orders) || protected(m,res,r,y,x,all,orders)) ==> bad)
            && (bad || (
                value(m,res,x,a.second)==Some(5) && value(m,res,y,b.second)==Some(2)
                && writers(m,res,x,all)==set![Op::W2] && writers(m,res,y,all)==set![Op::W1] && record(x,all)!=record(y,all)
                && (requires_other_slot(m,res,x,y) || requires_other_slot(m,res,y,x)
                    || strong_record_changes_options(m,res,n,a.first,b.first,orders))))
    }),
{
    let l=alpha(n);let r=beta(n);let all=Set::<nat>::empty();
    crate::independent_preparations::shared_weak_entry(raw,app::lanes(),l);
    weak_assignment_at_delivery(l,aa);weak_assignment_at_delivery(r,ab);
    assert(crate::first_dispatch::weak_open(m,l) && crate::first_dispatch::weak_open(m,r));
    let a=app::first_from_reference_a(m,first,res,l,run);let b=app::first_from_reference_a(m,first,res,r,run);
    let x=invocation(m,a);let y=invocation(m,b);
    assert(admitted(m,first,l,a) && admitted(m,first,r,b));
    actual_handoff(m,first,l,a,all);actual_handoff(m,first,r,b,all);
    common_fanout(m,n);
    let ha=complete_selected_first(raw,m,first,res,l,a,run);let hb=complete_selected_first(raw,m,first,res,r,b,run);
    let u=ha.second;let v=hb.second;
    names::original_copy_criterion(m,res,l,x,y,u);
    names::original_copy_criterion(m,res,r,y,x,v);
    if legal_history(m,first,res,ha) && legal_history(m,first,res,hb) {
        native_fork_requires_preservation(m,first,res,n,a,b,u,v,all,aa,ab);
        preserved_by_first_or_transport_dependency(m,first,res,n,a,b,u,v,aa,ab);
    }
    (ha,hb)
}

}
