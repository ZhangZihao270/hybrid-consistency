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

pub open spec fn backend_path<X,E>(p: Engine<X,E>, t: Seq<X>, a: Seq<Input<E>>) -> bool {
    t.len()==a.len()+1 && forall|i: int| 0<=i<a.len() ==>
        (p.ready)(t[i],#[trigger] a[i]) && t[i+1]==(p.step)(t[i],a[i])
}
pub open spec fn backend_reachable<X,E>(p: Engine<X,E>, x: X) -> bool {
    exists|t: Seq<X>,a: Seq<Input<E>>| #[trigger] backend_path(p,t,a) && t[0]==p.initial && t.last()==x
}
pub open spec fn path<X,E>(p: Engine<X,E>, t: Seq<State<X>>, a: Seq<Event<E>>) -> bool {
    t.len()==a.len()+1 && forall|i: int| 0<=i<a.len() ==>
        enabled(p,t[i],#[trigger] a[i]) && t[i+1]==step(p,t[i],a[i])
}
pub open spec fn reachable<X,E>(p: Engine<X,E>, x: State<X>) -> bool {
    exists|t: Seq<State<X>>,a: Seq<Event<E>>| #[trigger] path(p,t,a) && t[0]==initial(p) && t.last()==x
}

// Interface laws for the supplied SMR. These describe normal invocation
// and response bookkeeping, crash-stop and genesis. They say nothing about
// hybrid progress, freshness of read samples or the availability of repair.
pub open spec fn ports<X,E>(p: Engine<X,E>) -> bool {
    (forall|r: Replica| #[trigger] (p.cell)(p.initial,r)==1)
    && (forall|id: nat| #[trigger] (p.submitted)(p.initial,id).is_none())
    && (forall|x: X| #[trigger] backend_reachable(p,x) ==> (p.ready)(x,Input::Idle) && (p.step)(x,Input::Idle)==x)
    && (forall|x: X,id: nat,m: Method| backend_reachable(p,x) && (p.submitted)(x,id).is_none()
        && (p.client)(x,id) ==> #[trigger] (p.ready)(x,Input::Submit(id,m)))
    && (forall|x: X,a: Input<E>| backend_reachable(p,x) && #[trigger] (p.ready)(x,a) ==> {
        let y=(p.step)(x,a);
        (p.up)(y).subset_of((p.up)(x))
        && (a is Submit ==> (p.up)(y)==(p.up)(x) && forall|id: nat| #[trigger] (p.client)(y,id)==(p.client)(x,id))
        && forall|id: nat| #[trigger] (p.submitted)(y,id) == match a {
            Input::Submit(i,m) if i==id => Some(m), _ => (p.submitted)(x,id),
        } && ((p.reply)(x,id).is_some() ==> (p.reply)(y,id)==(p.reply)(x,id))
    })
}

pub open spec fn inspectable(c: Call) -> bool {
    forall|r: Replica| match #[trigger] (c.legs)(r) {
        Leg::InFlight(s) | Leg::Received(s) => s.version!=0 || s.value==1, _=>true,
    }
}
pub open spec fn good<X,E>(p: Engine<X,E>, s: State<X>) -> bool {
    (forall|r: Replica| !s.closed.contains(r) ==> #[trigger] (p.cell)(s.base,r)==1)
    && (forall|id: nat| #[trigger] s.calls.contains_key(id) ==> {
        let c=s.calls[id];
        inspectable(c) && (c.method is Command ==> forall|r: Replica|
            ((#[trigger] (c.legs)(r) is AtServer) || (c.legs)(r) is InFlight || (c.legs)(r) is Received) ==> s.closed.contains(r))
    })
    && (forall|id: nat| #[trigger] (p.submitted)(s.base,id) == if s.calls.contains_key(id) && s.calls[id].submitted {
        Some(s.calls[id].method)
    } else {None})
}
pub proof fn project_prefix<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,k: nat)
    requires path(p,t,a), t[0]==initial(p), k<=a.len(),
    ensures backend_reachable(p,t[k as int].base),
{
    let xs=Seq::new(k+1,|i: int|t[i].base); let bs=Seq::new(k,|i: int|input(t[i],a[i]));
    assert forall|i: int| 0<=i<k implies (p.ready)(xs[i],#[trigger] bs[i]) && xs[i+1]==(p.step)(xs[i],bs[i]) by {
        assert(enabled(p,t[i],a[i]) && t[i+1]==step(p,t[i],a[i]));
    }
    assert(backend_path(p,xs,bs));
}

pub proof fn keep_good<X,E>(p: Engine<X,E>,s: State<X>,e: Event<E>)
    requires ports(p), backend_reachable(p,s.base), good(p,s), enabled(p,s,e),
    ensures good(p,step(p,s,e)), s.closed.subset_of(step(p,s,e).closed),
{
    let u=step(p,s,e);
    assert forall|id: nat| #[trigger] u.calls.contains_key(id) implies {
        let c=u.calls[id];
        inspectable(c) && (c.method is Command ==> forall|r: Replica| ((#[trigger] (c.legs)(r) is AtServer) || (c.legs)(r) is InFlight || (c.legs)(r) is Received) ==> u.closed.contains(r))
    } by {
        if s.calls.contains_key(id) { assert(inspectable(s.calls[id])); }
        assert forall|r: Replica| match #[trigger] (u.calls[id].legs)(r) {
            Leg::InFlight(x) | Leg::Received(x) => x.version!=0 || x.value==1, _=>true,
        } by {
            match e {
                Event::Rpc(i,site,Stage::EmitReply) if i==id && site==r => {
                    if !s.closed.contains(r) { assert((p.cell)(s.base,r)==1); }
                }, _=>{},
            }
        }
    }
    assert((p.ready)(s.base,input(s,e)));
}
pub proof fn good_at<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,k: nat)
    requires ports(p), path(p,t,a), t[0]==initial(p), k<=a.len(),
    ensures good(p,t[k as int]), backend_reachable(p,t[k as int].base),
    decreases k,
{
    project_prefix(p,t,a,k);
    if k>0 {
        let j=(k-1) as nat; good_at(p,t,a,j); keep_good(p,t[j as int],a[j as int]);
    }
}
pub proof fn reachable_good<X,E>(p: Engine<X,E>,s: State<X>)
    requires ports(p), reachable(p,s),
    ensures good(p,s), backend_reachable(p,s.base),
{
    let (t,a)=choose|t: Seq<State<X>>,a: Seq<Event<E>>| #[trigger] path(p,t,a) && t[0]==initial(p) && t.last()==s;
    good_at(p,t,a,a.len());
}
pub proof fn early_stock_answer(c: Call)
    requires inspectable(c), early(c), majority(rows(c).dom()),
    ensures reference_read(Replica::R3)(rows(c))==Some(1),
{
    let m=rows(c);
    assert forall|r: Replica| #[trigger] m.contains_key(r) implies m[r].value==1 by {
        assert((c.legs)(r) is Received && m[r].version==0);
    }
    crate::quorum_rpc::latest_is_a_sample(m);
    assert(crate::metadata_reader::valid_root(m));
}

}
