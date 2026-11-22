// Packet occurrences and the native envelope numbers at the original SR2 cut.
use vstd::prelude::*;
use crate::checkpoint::{Fork, Wire};
use crate::delivery::{Action, Packet, process_step};
use crate::first_splice::{slot, Observation};
use crate::independent_read::{self as read, State};
use crate::native_fork as native;
use crate::protocol::LocalProtocol;
use crate::read_call::{Event, Program};

verus! {

// Test one field of the existing callback. This is a local distinguishability
// test for the interface, with no liveness claim about the modified guard.
pub proof fn native_guard_can_test_the_number<S>(m: Program<S>, x: State<S>, a: Event, i: nat)
    requires slot(a).is_some(),
    ensures ({
        let p = LocalProtocol {
            accept: |s: S, e: Observation| (m.accept)(s, e)
                && (slot(e.action).is_none() || slot(e.action) == Some(i)),
            ..m
        };
        slot(process_step(x.cfg.net, a).action) == slot(a)
            && read::next(p, x, a) == read::next(m, x, a)
            && (native::step(p, true)(x, a, read::next(p, x, a))
                == (native::step(m, true)(x, a, read::next(m, x, a)) && slot(a) == Some(i)))
    }),
{
    match a { Action::Send(..) | Action::Deliver(_) => {}, _ => {} }
}

// A pending packet at entry has birth None. Each later send gets its
// own step index. The original slot is the number delivered to handlers.
pub struct Handle { pub slot: nat, pub birth: Option<nat> }
pub struct Directory { pub clock: nat, pub births: Map<nat, nat> }
pub enum QueueEvent { Send(Handle, Packet<Wire>), Deliver(Handle), Other(Event) }

pub open spec fn entry() -> Directory { Directory { clock: 0, births: Map::empty() } }

pub open spec fn queued<S>(x: State<S>, d: Directory, h: Handle) -> Option<Packet<Wire>> {
    if h.birth == d.births.get(h.slot) { x.cfg.net.pending.get(h.slot) } else { None }
}

pub open spec fn consistent<S>(x: State<S>, d: Directory) -> bool {
    forall|i: nat| #[trigger] d.births.contains_key(i) ==>
        d.births[i] < d.clock && x.cfg.net.pending.contains_key(i)
}

pub open spec fn attach(d: Directory, a: Event) -> QueueEvent {
    match a {
        Action::Send(i, p) => QueueEvent::Send(Handle { slot: i, birth: Some(d.clock) }, p),
        Action::Deliver(i) => QueueEvent::Deliver(Handle { slot: i, birth: d.births.get(i) }),
        _ => QueueEvent::Other(a),
    }
}

pub open spec fn visible(e: QueueEvent) -> Event {
    match e {
        QueueEvent::Send(h, p) => Action::Send(h.slot, p),
        QueueEvent::Deliver(h) => Action::Deliver(h.slot),
        QueueEvent::Other(a) => a,
    }
}

pub open spec fn advance(d: Directory, a: Event) -> Directory {
    Directory { clock: d.clock + 1, births: match a {
        Action::Send(i, _) => d.births.insert(i, d.clock),
        Action::Deliver(i) => d.births.remove(i),
        _ => d.births,
    } }
}

// The same native guards check the visible event. Delivery additionally
// resolves the physical occurrence, so a stale handle cannot receive a reuse.
pub open spec fn edge<S>(m: Program<S>, x: State<S>, d: Directory, e: QueueEvent, quiet: bool) -> bool {
    let a = visible(e);
    native::step(m, quiet)(x, a, read::next(m, x, a)) && match e {
        QueueEvent::Send(h, _) => h.birth == Some(d.clock),
        QueueEvent::Deliver(h) => queued(x, d, h).is_some(),
        QueueEvent::Other(a) => slot(a).is_none(),
    }
}

// Every accepted event modifies exactly the named physical occurrence.
pub proof fn queue_step<S>(m: Program<S>, x: State<S>, d: Directory, e: QueueEvent, quiet: bool)
    requires consistent(x, d),
    ensures ({
        let a = visible(e); let y = read::next(m, x, a); let u = advance(d, a);
        (edge(m, x, d, e, quiet) == (native::step(m, quiet)(x, a, y) && e == attach(d, a)))
        && (edge(m, x, d, e, quiet) ==> consistent(y, u)
            && (forall|h: Handle| #[trigger] queued(y, u, h) == match e {
                QueueEvent::Send(sent, p) if h == sent => Some(p),
                QueueEvent::Deliver(taken) if h == taken => None,
                _ => queued(x, d, h),
            })
            && (e is Deliver ==> process_step(x.cfg.net, a).incoming == queued(x, d, e->Deliver_0)))
    }),
{
    let a = visible(e); let y = read::next(m, x, a); let u = advance(d, a);
    if edge(m, x, d, e, quiet) {
        assert forall|i: nat| #[trigger] u.births.contains_key(i) implies
            u.births[i] < u.clock && y.cfg.net.pending.contains_key(i) by {
            if !(a is Send && a->Send_0 == i) { assert(d.births.contains_key(i)); }
        }
        assert forall|h: Handle| #[trigger] queued(y, u, h) == match e {
            QueueEvent::Send(sent, p) if h == sent => Some(p),
            QueueEvent::Deliver(taken) if h == taken => None,
            _ => queued(x, d, h),
        } by {
            match e {
                QueueEvent::Send(sent, _) => { assert(!x.cfg.net.pending.contains_key(sent.slot)); },
                QueueEvent::Deliver(taken) => { assert(taken.birth == d.births.get(taken.slot)); },
                QueueEvent::Other(_) => {},
            }
        }
    }
}

pub open spec fn lift(d: Directory, s: Seq<Event>) -> Seq<QueueEvent>
    decreases s.len(),
{
    if s.len() == 0 { seq![] } else {
        seq![attach(d, s[0])] + lift(advance(d, s[0]), s.drop_first())
    }
}

pub open spec fn project(t: Seq<QueueEvent>) -> Seq<Event> {
    t.map(|_j: int, e: QueueEvent| visible(e))
}

pub open spec fn handle_return<S>(m: Program<S>, res: spec_fn(S) -> Option<int>, x: State<S>,
    d: Directory, t: Seq<QueueEvent>, quiet: bool) -> bool
    decreases t.len(),
{
    if t.len() == 0 { read::returned(res)(x) } else {
        let e = t[0]; let a = visible(e);
        !read::returned(res)(x) && edge(m, x, d, e, quiet)
            && handle_return(m, res, read::next(m, x, a), advance(d, a), t.drop_first(), quiet)
    }
}

pub proof fn fresh_sends(d: Directory, s: Seq<Event>)
    ensures project(lift(d, s)) == s,
        forall|j: int| 0 <= j < s.len() && (#[trigger] s[j]) is Send ==> ({
            let e = lift(d, s)[j]; e is Send && e->Send_0.slot == s[j]->Send_0
                && e->Send_0.birth == Some((d.clock + j) as nat)
        }),
    decreases s.len(),
{
    if s.len() > 0 {
        let tail = s.drop_first(); let u = advance(d, s[0]);
        fresh_sends(u, tail);
        assert forall|j: int| 0 <= j < s.len() implies (#[trigger] project(lift(d, s))[j]) == s[j] by {
            if j == 0 {
                assert(lift(d, s)[0] == attach(d, s[0]));
                match s[0] { Action::Send(..) | Action::Deliver(_) => {}, _ => {} }
            } else {
                assert(lift(d, s)[j] == lift(u, tail)[j-1]);
                assert(visible(lift(u, tail)[j-1]) == project(lift(u, tail))[j-1]);
                assert(tail[j-1] == s[j]);
            }
        }
        assert forall|j: int| 0 <= j < s.len() && (#[trigger] s[j]) is Send implies ({
            let e = lift(d, s)[j]; e is Send && e->Send_0.slot == s[j]->Send_0
                && e->Send_0.birth == Some((d.clock + j) as nat)
        }) by {
            if j > 0 { assert(tail[j-1] == s[j]); assert(lift(d, s)[j] == lift(u, tail)[j-1]); }
        }
    }
    assert(project(lift(d, s)) =~= s);
}

// Bijection on guarded paths up to the actual first return, including an
// immediate return. Both sides run the same private and network transitions.
pub proof fn exact_returns<S>(m: Program<S>, res: spec_fn(S) -> Option<int>, x: State<S>,
    d: Directory, t: Seq<QueueEvent>, quiet: bool)
    requires consistent(x, d),
    ensures handle_return(m, res, x, d, t, quiet) == (native::completes(m, res, x, project(t), quiet)
        && t == lift(d, project(t))),
    decreases t.len(),
{
    let s = project(t);
    if t.len() > 0 {
        let e = t[0]; let a = visible(e); let y = read::next(m, x, a);
        assert(project(t.drop_first()) =~= s.drop_first());
        queue_step(m, x, d, e, quiet);
        if edge(m, x, d, e, quiet) {
            exact_returns(m, res, y, advance(d, a), t.drop_first(), quiet);
            assert(t =~= seq![e] + t.drop_first());
            assert(lift(d, s).drop_first() =~= lift(advance(d, a), s.drop_first()));
        }
    } else { assert(t =~= lift(d, s)); }
}

// Test the original visible-slot guard with an actually fresh handle.
pub proof fn occupied_slot_blocks_fresh_send<S>(m: Program<S>, x: State<S>, d: Directory,
    i: nat, p: Packet<Wire>, quiet: bool)
    requires consistent(x, d), x.cfg.net.pending.contains_key(i),
    ensures ({
        let fresh = Handle { slot: i, birth: Some(d.clock) };
        let pending = Handle { slot: i, birth: d.births.get(i) };
        fresh != pending && queued(x, d, fresh).is_none()
            && queued(x, d, pending) == Some(x.cfg.net.pending[i])
            && !edge(m, x, d, QueueEvent::Send(fresh, p), quiet)
    }),
{}

// Identify the entry packet by its actual path, endpoints and payload.
// A send in the current trace has its own fresh occurrence at index j.
pub open spec fn sends_at_copy<S>(b: Fork, other: State<S>, t: Seq<QueueEvent>) -> bool {
    exists|j: int| 0 <= j < t.len() && (#[trigger] t[j]) is Send
        && t[j]->Send_0.birth == Some(j as nat)
        && queued(other, entry(), Handle { slot: t[j]->Send_0.slot, birth: None }) == Some(native::observed_copy(b))
}

proof fn copy_on_path<S>(m: Program<S>, res: spec_fn(S) -> Option<int>, b: Fork,
    x: State<S>, other: State<S>, s: Seq<Event>)
    requires crate::survivors::after_crash(x.cfg.net), native::opposing_copy(b, x, other),
        native::completes(m, res, x, s, true),
    ensures native::uses_name(native::frozen_names(x, other), s) == sends_at_copy(b, other, lift(entry(), s)),
{
    let mask = native::frozen_names(x, other); let t = lift(entry(), s);
    fresh_sends(entry(), s);
    native::completion_facts(m, res, x, s);
    if native::uses_name(mask, s) {
        let j = choose|j: int| 0 <= j < s.len() && native::masks_send(mask, #[trigger] s[j]);
        let i = s[j]->Send_0;
        assert(!native::weak_packets(x).contains_key(i));
        assert(native::weak_packets(other).contains_key(i));
        assert(t[j] is Send && t[j]->Send_0.slot == i && t[j]->Send_0.birth == Some(j as nat));
    } else if sends_at_copy(b, other, t) {
        let j = choose|j: int| 0 <= j < t.len() && (#[trigger] t[j]) is Send
            && t[j]->Send_0.birth == Some(j as nat)
            && queued(other, entry(), Handle { slot: t[j]->Send_0.slot, birth: None }) == Some(native::observed_copy(b));
        assert(s[j] == visible(t[j]));
        assert(native::weak_packets(other).contains_key(t[j]->Send_0.slot));
        assert(native::masks_send(mask, s[j]));
    }
}

pub open spec fn every_return_sends_at_copy<S>(m: Program<S>, res: spec_fn(S) -> Option<int>, b: Fork,
    x: State<S>, other: State<S>) -> bool {
    forall|t: Seq<QueueEvent>| #[trigger] handle_return(m, res, x, entry(), t, true) ==> sends_at_copy(b, other, t)
}

// Both cuts and the unmasked witness are supplied by original_hot_application.
// The universal ranges over all guarded returns on this arm, in fresh handles.
pub proof fn original_copy_criterion<S>(m: Program<S>, res: spec_fn(S) -> Option<int>, b: Fork,
    x: State<S>, other: State<S>, witness: Seq<Event>)
    requires crate::survivors::after_crash(x.cfg.net), native::opposing_copy(b, x, other),
        native::completes(m, res, x, witness, true),
    ensures handle_return(m, res, x, entry(), lift(entry(), witness), true),
        native::requires_other_slot(m, res, x, other) == !native::has_return(m, res, x, native::frozen_names(x, other)),
        native::requires_other_slot(m, res, x, other) == every_return_sends_at_copy(m, res, b, x, other),
{
    let mask = native::frozen_names(x, other);
    fresh_sends(entry(), witness);
    exact_returns(m, res, x, entry(), lift(entry(), witness), true);
    native::necessary_send_iff(m, res, x, other, witness);
    if !native::has_return(m, res, x, mask) {
        assert forall|t: Seq<QueueEvent>| #[trigger] handle_return(m, res, x, entry(), t, true)
            implies sends_at_copy(b, other, t) by {
            exact_returns(m, res, x, entry(), t, true);
            copy_on_path(m, res, b, x, other, project(t));
        }
    } else {
        let s = choose|s: Seq<Event>| !native::uses_name(mask, s) && #[trigger] native::completes(m, res, x, s, true);
        fresh_sends(entry(), s);
        exact_returns(m, res, x, entry(), lift(entry(), s), true);
        copy_on_path(m, res, b, x, other, s);
        assert(handle_return(m, res, x, entry(), lift(entry(), s), true) && !sends_at_copy(b, other, lift(entry(), s)));
    }
}

}
