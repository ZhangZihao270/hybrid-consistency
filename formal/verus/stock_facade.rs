use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::all_replicas;
use crate::metadata_stock::Rows;
use crate::metadata_reader::reference_read;
use crate::ordered_store::{Stamp, majority};

verus! {

// A wrapper of an existing strong service. Only a non-mutating read can
// bypass the service. Commands are arbitrary application operation codes.
// Submit is the underlying local invocation; Work retains its actual steps.
pub enum Method { Read, Command(nat) }
pub enum Input<E> { Idle, Submit(nat, Method), Work(E) }
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(E)]
pub struct Engine<X,E> {
    pub initial: X,
    pub ready: spec_fn(X,Input<E>) -> bool,
    pub step: spec_fn(X,Input<E>) -> X,
    pub up: spec_fn(X) -> Set<Replica>,
    pub client: spec_fn(X,nat) -> bool,
    pub cell: spec_fn(X,Replica) -> int,
    pub submitted: spec_fn(X,nat) -> Option<Method>,
    pub reply: spec_fn(X,nat) -> Option<int>,
}

// Physical read samples and write-fence acknowledgments are immutable in
// flight. Each (invocation, replica) has a distinct request/reply slot.
pub enum Leg { Unsent, Request, AtServer, InFlight(Stamp), Received(Stamp) }
pub struct Call {
    pub method: Method,
    pub legs: spec_fn(Replica) -> Leg,
    pub submitted: bool,
    pub answer: Option<int>,
}
pub struct State<X> {
    pub base: X,
    pub closed: Set<Replica>,
    pub calls: Map<nat,Call>,
}
pub enum Stage { Offer, DeliverRequest, EmitReply, DeliverReply }
pub enum Event<E> { Idle, Invoke(nat,Method), Rpc(nat,Replica,Stage), Poll(nat), Work(E), Duplicate(nat,Replica) }

pub open spec fn initial<X,E>(p: Engine<X,E>) -> State<X> {
    State { base: p.initial, closed: Set::empty(), calls: Map::empty() }
}
pub open spec fn fresh(m: Method) -> Call {
    Call { method: m, legs: |_r| Leg::Unsent, submitted: false, answer: None }
}
pub open spec fn rows(c: Call) -> Rows {
    Map::new(all_replicas().filter(|r: Replica| (c.legs)(r) is Received),
        |r| (c.legs)(r)->Received_0)
}
pub open spec fn early(c: Call) -> bool {
    c.method is Read && forall|r: Replica| #[trigger] rows(c).contains_key(r) ==> rows(c)[r].version==0
}
pub open spec fn delegate(c: Call) -> bool {
    !c.submitted && c.answer.is_none() && majority(rows(c).dom()) && !early(c)
}
pub open spec fn input<X,E>(s: State<X>, e: Event<E>) -> Input<E> {
    match e {
        Event::Work(w) => Input::Work(w),
        Event::Poll(id) if s.calls.contains_key(id) && delegate(s.calls[id]) => Input::Submit(id,s.calls[id].method),
        _ => Input::Idle,
    }
}
pub open spec fn rpc_enabled(c: Call,r: Replica,stage: Stage,server_up: bool,client_up: bool) -> bool {
    match stage {
        Stage::Offer => client_up && (c.legs)(r) is Unsent && !majority(rows(c).dom()),
        Stage::DeliverRequest => server_up && (c.legs)(r) is Request,
        Stage::EmitReply => server_up && (c.legs)(r) is AtServer,
        Stage::DeliverReply => client_up && (c.legs)(r) is InFlight,
    }
}

pub open spec fn enabled<X,E>(p: Engine<X,E>, s: State<X>, e: Event<E>) -> bool {
    (p.ready)(s.base,input(s,e)) && match e {
        Event::Invoke(id,_) => !s.calls.contains_key(id) && (p.client)(s.base,id),
        Event::Poll(id) => s.calls.contains_key(id) && s.calls[id].answer.is_none() && (p.client)(s.base,id),
        Event::Rpc(id,r,stage) => s.calls.contains_key(id)
            && rpc_enabled(s.calls[id],r,stage,(p.up)(s.base).contains(r),(p.client)(s.base,id)),
        // Duplicate deliveries use the original slot and are idempotent.
        Event::Duplicate(id,r) => s.calls.contains_key(id) && ((s.calls[id].legs)(r) is AtServer || (s.calls[id].legs)(r) is Received),
        Event::Work(_) | Event::Idle => true,
    }
}
pub open spec fn stamp<X,E>(p: Engine<X,E>, s: State<X>, r: Replica) -> Stamp {
    Stamp { version: if s.closed.contains(r) {1} else {0}, value: (p.cell)(s.base,r) }
}
pub open spec fn local_poll(c: Call, backend_reply: Option<int>) -> Call {
    if c.answer.is_some() { c }
    else if c.submitted { Call { answer: backend_reply, ..c } }
    else if !majority(rows(c).dom()) { c }
    else if early(c) { Call { answer: reference_read(Replica::R3)(rows(c)), ..c } }
    else { Call { submitted: true, ..c } }
}
pub open spec fn poll<X,E>(p: Engine<X,E>, s: State<X>, id: nat) -> Call {
    local_poll(s.calls[id],(p.reply)(s.base,id))
}
pub open spec fn advance_rpc(c: Call,r: Replica,stage: Stage,sampled: Stamp) -> Call {
    let leg=match stage {
        Stage::Offer => Leg::Request, Stage::DeliverRequest => Leg::AtServer,
        Stage::EmitReply => Leg::InFlight(sampled), Stage::DeliverReply => Leg::Received((c.legs)(r)->InFlight_0),
    };
    Call { legs: |site| if site==r {leg} else {(c.legs)(site)}, ..c }
}
pub open spec fn step<X,E>(p: Engine<X,E>, s: State<X>, e: Event<E>) -> State<X> {
    let base=(p.step)(s.base,input(s,e));
    // The ordinary store closes its own flag on a local application write.
    // No process observes another site's base memory to maintain this flag.
    // Each bit lives at its own replica. A local ordinary data change or
    // delivery of a command fence there closes its direct-read generation.
    let closed=s.closed.union(all_replicas().filter(|r| (p.cell)(base,r)!=(p.cell)(s.base,r)));
    let closed=match e {
        Event::Rpc(id,r,Stage::DeliverRequest) if s.calls[id].method is Command => closed.insert(r),
        _ => closed,
    };
    let calls=match e {
        Event::Invoke(id,m) => s.calls.insert(id,fresh(m)),
        Event::Rpc(id,r,stage) => s.calls.insert(id,advance_rpc(s.calls[id],r,stage,stamp(p,s,r))),
        Event::Poll(id) => s.calls.insert(id,poll(p,s,id)),
        _ => s.calls,
    };
    State { base, closed, calls }
}

}
