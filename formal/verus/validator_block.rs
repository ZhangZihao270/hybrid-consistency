use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Path};
use crate::stock_facade::*;
use crate::facade_linear::CommandSemantics;
use crate::facade_hybrid::{prefix,weak_part};
use crate::facade_transport::actual_first_rpc;
use crate::ordered_round::{self as base,Store,Work,engine};
use crate::ordered_store::majority;
use crate::metadata_reader::reference_read;

verus! {

pub open spec fn weak_value(v:int) -> bool { v==2 || v==5 }
pub open spec fn possible_leg(r: Replica,l: Leg) -> bool {
    match l {
        Leg::InFlight(x) | Leg::Received(x)=>r!=Replica::R3 && x.version==0 && weak_value(x.value),
        Leg::AtServer=>r!=Replica::R3, _=>true,
    }
}

// This invariant is about the backend, both private calls, the actual
// shared disks and every in-flight SR2 response. Even receiving two equal
// copies of a weak value cannot manufacture the missing ordinary evidence.
pub open spec fn blocked(s: State<Store>) -> bool {
    s.base.live==live_pair() && s.base.calls.dom().is_empty() && s.closed.is_empty()
    && s.calls.dom()==set![1nat,2nat] && s.calls[1].method is Read && s.calls[1].answer.is_some()
    && s.calls[2].method is Read && !s.calls[2].submitted && s.calls[2].answer.is_none()
    && (forall|r:Replica| #[trigger] possible_leg(r,(s.calls[2].legs)(r)))
    && forall|r:Replica| weak_value((#[trigger] (s.base.disk)(r)).value)
}

pub(crate) proof fn invalid_mailbox(c: Call)
    requires c.method is Read, !c.submitted, c.answer.is_none(), forall|r:Replica| #[trigger] possible_leg(r,(c.legs)(r)),
    ensures early(c), !delegate(c), local_poll(c,None)==c,
{
    let m=rows(c);
    assert(early(c)) by {assert forall|r: Replica| #[trigger] m.contains_key(r) implies m[r].version==0 by {assert(possible_leg(r,(c.legs)(r)));}}
    if majority(m.dom()) {
        assert(possible_leg(Replica::R3,(c.legs)(Replica::R3)));
        assert(!m.contains_key(Replica::R3) && m.contains_key(Replica::R1));
        assert(possible_leg(Replica::R1,(c.legs)(Replica::R1)));
        assert(!crate::metadata_reader::valid_root(m));
        assert(reference_read(Replica::R3)(m).is_none());
    }
}

pub proof fn at_the_real_cut(b: Fork)
    ensures blocked(prefix(b,17)),
{
    actual_first_rpc(b,17);
    assert(prefix(b,17).base.live =~= live_pair());
    assert(prefix(b,17).calls.dom() =~= set![1nat,2nat]);
}

// No additional application command or reader is invoked. The backend's
// own guard decides which ordinary work may occur; all enabled Work, RPC,
// duplicate, client, tick and failure events in this workload are admitted.
pub proof fn ordinary_step_cannot_unlock(f: CommandSemantics,s: State<Store>,a: Event<Work>)
    requires blocked(s),!(a is Invoke),enabled(engine(f),s,a),
    ensures blocked(step(engine(f),s,a)),!(input(s,a) is Submit),
{
    let p=engine(f);let u=step(p,s,a);let c=s.calls[2];invalid_mailbox(c);
    if let Event::Poll(id)=a {assert(id==2);assert(!delegate(s.calls[id]));}
    if let Event::Work(w)=a {match w {
        Work::Serve(id,_)=>{assert(!s.base.calls.contains_key(id));},
        Work::Crash(r)=>{match r {_=>{}}}, _=>{},
    }}
    assert(u.base.disk =~= s.base.disk);assert(u.closed =~= s.closed);assert(u.calls.dom() =~= s.calls.dom());
    assert forall|r:Replica| #[trigger] possible_leg(r,(u.calls[2].legs)(r)) by {
        assert(possible_leg(r,(c.legs)(r)));assert(weak_value((s.base.disk)(r).value));
    }
}

pub open spec fn application_copy(n: Network<int,Wire>,a: Action<Wire>) -> bool {
    match a {
        Action::Deliver(id) if n.pending.contains_key(id) && n.pending[id].path==Path::Weak
            && n.pending[id].input is Copy=>weak_value(n.pending[id].input->Copy_0), _=>true,
    }
}
proof fn network_step_cannot_unlock(s: State<Store>,n: Network<int,Wire>,a: Action<Wire>)
    requires blocked(s),application_copy(n,a),
    ensures blocked(weak_part(s,n,a)),
{
    let u=weak_part(s,n,a);
    assert forall|r:Replica| weak_value((#[trigger] (u.base.disk)(r)).value) by { assert(weak_value((s.base.disk)(r).value)); }
}

// Overapproximates schedules, never adds service: we even allow a separate
// enabled ordinary step at every physical action. Each weak installation
// still takes its payload from an issued packet in the real network trace.
pub open spec fn continuation(f: CommandSemantics,t: Seq<State<Store>>,ordinary: Seq<Event<Work>>,
    n: Seq<Network<int,Wire>>,a: Seq<Action<Wire>>) -> bool {
    t.len()==a.len()+1 && ordinary.len()==a.len() && delivery::trace(|v,w|cell(v,w),n,a)
    && forall|i:int| 0<=i<a.len() ==> {
        let ev=#[trigger] ordinary[i]; !(ev is Invoke) && enabled(engine(f),t[i],ev)
            && application_copy(n[i],a[i]) && t[i+1]==weak_part(step(engine(f),t[i],ev),n[i],a[i])
    }
}
pub proof fn no_return_in_read_only_workload(f: CommandSemantics,b: Fork,t: Seq<State<Store>>,ordinary: Seq<Event<Work>>,
    n: Seq<Network<int,Wire>>,a: Seq<Action<Wire>>,k:nat)
    requires t[0]==prefix(b,17),n[0]==checkpoint_end(b),continuation(f,t,ordinary,n,a),k<=a.len(),
    ensures blocked(t[k as int]),t[k as int].calls[2].answer.is_none() && !t[k as int].calls[2].submitted,
    decreases k,
{
    if k==0 {at_the_real_cut(b);} else {
        let j=(k-1) as nat;no_return_in_read_only_workload(f,b,t,ordinary,n,a,j);
        ordinary_step_cannot_unlock(f,t[j as int],ordinary[j as int]);
        network_step_cannot_unlock(step(engine(f),t[j as int],ordinary[j as int]),n[j as int],a[j as int]);
    }
}

// A failed stock coupling is not a distinction between alpha and beta.
// The zero-tag/non-genesis stamp is impossible at even one open stock site.
pub proof fn no_stock_stamp_matches_either_survivor(f: CommandSemantics,b: Fork,s: State<Store>,r:Replica)
    requires reachable(engine(f),s),live_pair().contains(r),
    ensures stamp(engine(f),s,r)!=stamp(engine(f),prefix(b,17),r),
{
    base::api_and_majorities(f);reachable_good(engine(f),s);at_the_real_cut(b);
    assert(weak_value((prefix(b,17).base.disk)(r).value));
}

}
