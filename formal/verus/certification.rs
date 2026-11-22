use vstd::prelude::*;
use crate::Replica;

verus! {

pub struct WeakStatus {
    pub origin: Replica,
    pub copies: Set<Replica>,
    pub acknowledged: bool,
    pub order_holders: Set<Replica>,
}

pub enum WeakEvent {
    CopyAt(Replica),
    ConfirmAtOrigin(Replica),
    CertifyAtOrigin,
    CertifyAtR3,
}

pub open spec fn initial_status(origin: Replica) -> WeakStatus {
    WeakStatus {
        origin, copies: Set::empty().insert(origin),
        acknowledged: false, order_holders: Set::empty(),
    }
}

// An installed witness stands for independently justified weak-path
// ordering. Copy count is a separate component of G.
pub open spec fn weak_g(s: WeakStatus) -> bool {
    s.copies.len() >= 2 && s.order_holders.len() > 0
}

pub open spec fn weak_event(s: WeakStatus, e: WeakEvent, r3_authority: bool) -> Option<WeakStatus> {
    match e {
        WeakEvent::CopyAt(r) => Some(WeakStatus { copies: s.copies.insert(r), ..s }),
        WeakEvent::ConfirmAtOrigin(r) if r != s.origin && s.copies.contains(r) =>
            Some(WeakStatus { acknowledged: true, ..s }),
        WeakEvent::CertifyAtOrigin if s.acknowledged =>
            Some(WeakStatus { order_holders: s.order_holders.insert(s.origin), ..s }),
        WeakEvent::CertifyAtR3 if r3_authority && s.origin != Replica::R3
            && s.copies.contains(s.origin) && s.copies.contains(Replica::R3) =>
            Some(WeakStatus { order_holders: s.order_holders.insert(Replica::R3), ..s }),
        _ => None,
    }
}

pub open spec fn weak_trace(
    states: Seq<WeakStatus>, events: Seq<WeakEvent>, r3_authority: bool,
) -> bool {
    states.len() == events.len() + 1 && forall|i: int| 0 <= i < events.len() ==>
        weak_event(states[i], #[trigger] events[i], r3_authority) == Some(states[i + 1])
}

pub open spec fn is_confirmation(e: WeakEvent) -> bool {
    match e { WeakEvent::ConfirmAtOrigin(_) => true, _ => false }
}

// Conditional on who may establish order. This is not implied by O.
pub proof fn origin_certificate_needs_a_confirmation(
    origin: Replica, states: Seq<WeakStatus>, events: Seq<WeakEvent>, k: int,
)
    requires
        weak_trace(states, events, false), states[0] == initial_status(origin),
        0 <= k <= events.len(),
        forall|i: int| 0 <= i < k ==> !is_confirmation(#[trigger] events[i]),
    ensures !states[k].acknowledged, states[k].order_holders.len() == 0, !weak_g(states[k]),
    decreases k,
{
    if k > 0 {
        let i = k - 1;
        origin_certificate_needs_a_confirmation(origin, states, events, i);
        assert(!is_confirmation(events[i]));
        assert(weak_event(states[i], events[i], false) == Some(states[k]));
    }
}

pub open spec fn two_copies(origin: Replica) -> WeakStatus {
    WeakStatus { copies: Set::empty().insert(origin).insert(Replica::R3), ..initial_status(origin) }
}

pub open spec fn r3_certified(origin: Replica) -> WeakStatus {
    WeakStatus { order_holders: Set::empty().insert(Replica::R3), ..two_copies(origin) }
}

pub proof fn two_copies_and_no_confirmation_do_not_determine_g(origin: Replica)
    requires origin != Replica::R3,
    ensures
        two_copies(origin).copies.len() == 2,
        !two_copies(origin).acknowledged && !r3_certified(origin).acknowledged,
        !weak_g(two_copies(origin)), weak_g(r3_certified(origin)),
        weak_event(initial_status(origin), WeakEvent::CopyAt(Replica::R3), true)
            == Some(two_copies(origin)),
        weak_event(two_copies(origin), WeakEvent::CertifyAtR3, true) == Some(r3_certified(origin)),
        weak_event(two_copies(origin), WeakEvent::CertifyAtR3, false) == None,
{
    assert(!Set::empty().insert(origin).contains(Replica::R3));
}

// An in-flight witness is counted separately from the live holders.
pub open spec fn recoverable_witness(
    s: WeakStatus, in_flight_to_live_survivor: bool,
) -> bool {
    s.order_holders.contains(Replica::R1) || s.order_holders.contains(Replica::R2)
        || in_flight_to_live_survivor
}

pub proof fn r3_certificate_recovery_depends_on_surviving_evidence(origin: Replica)
    requires origin != Replica::R3,
    ensures
        weak_g(r3_certified(origin)),
        !recoverable_witness(r3_certified(origin), false),
        recoverable_witness(r3_certified(origin), true),
{
    two_copies_and_no_confirmation_do_not_determine_g(origin);
}

pub open spec fn read_surviving_record<Q>(
    records: spec_fn(Replica) -> Option<Q>,
) -> Option<Q> {
    if records(Replica::R1).is_some() { records(Replica::R1) }
    else { records(Replica::R2) }
}

// Sufficient durability mechanism, distinct from replicating only data.
// The agreement premise applies to decoded current certificates, not to
// stale records a real decoder would have to validate or discard.
pub proof fn replicated_order_record_survives_r3<Q>(
    before: spec_fn(Replica) -> Option<Q>, after: spec_fn(Replica) -> Option<Q>,
    order: Q, first: Replica, second: Replica,
)
    requires
        first != second,
        before(first) == Some(order), before(second) == Some(order),
        forall|r: Replica| r != Replica::R3 && #[trigger] before(r) == Some(order)
            ==> after(r) == Some(order),
        forall|r: Replica| r != Replica::R3 && (#[trigger] after(r)).is_some()
            ==> after(r) == Some(order),
    ensures read_surviving_record(after) == Some(order),
{
    let survivor = if first == Replica::R3 { second } else { first };
    assert(survivor == Replica::R1 || survivor == Replica::R2);
    assert(before(survivor) == Some(order));
    assert(after(survivor) == Some(order));
    assert(after(Replica::R1).is_some() || after(Replica::R2).is_some());
}

}
