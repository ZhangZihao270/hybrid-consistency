use vstd::prelude::*;
use crate::{Branch, Replica, origin};
use crate::delivery::*;

verus! {

pub open spec fn untouched_slot<I>(a: Action<I>, id: nat) -> bool {
    match a {
        Action::Send(slot, _) | Action::Deliver(slot) => slot != id,
        _ => true,
    }
}

pub open spec fn hold_delivery<L, I>(
    s: Network<L, I>, id: nat, packet: Packet<I>, to: Replica, old: L,
) -> Network<L, I> {
    Network {
        pending: s.pending.insert(id, packet),
        locals: |r: Replica| if r == to { old } else { (s.locals)(r) },
        ..s
    }
}

pub open spec fn independent_of_delivery<L, I>(
    s: Network<L, I>, a: Action<I>, id: nat, to: Replica, old: L,
) -> bool {
    untouched_slot(a, id)
    && (process_step(s, a).actor != Process::At(to)
        || ((s.locals)(to) == old && local_input(s, a, to).is_none()))
}

proof fn hold_commutes<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, a: Action<I>,
    id: nat, packet: Packet<I>, to: Replica, old: L,
)
    requires
        enabled(s, a), !s.pending.contains_key(id),
        independent_of_delivery(s, a, id, to, old),
    ensures ({
        let held = hold_delivery(s, id, packet, to, old);
        enabled(held, a)
        && process_step(s, a) == process_step(held, a)
        && !advance(update, s, a).pending.contains_key(id)
        && advance(update, held, a) == hold_delivery(advance(update, s, a), id, packet, to, old)
    }),
{
    let held = hold_delivery(s, id, packet, to, old);
    let before = advance(update, held, a);
    let after = hold_delivery(advance(update, s, a), id, packet, to, old);
    match a {
        Action::Deliver(slot) => {
            assert(held.pending[slot] == s.pending[slot]);
            assert(held.pending.remove(slot) =~= s.pending.remove(slot).insert(id, packet));
            assert(!s.pending.remove(slot).contains_key(id));
        },
        Action::Send(slot, p) => {
            assert(held.pending.contains_key(slot) == s.pending.contains_key(slot));
            assert(held.pending.insert(slot, p) =~= s.pending.insert(slot, p).insert(id, packet));
            assert(!s.pending.insert(slot, p).contains_key(id));
        },
        _ => {},
    }
    assert(local_input(s, a, to).is_none());
    assert forall|r: Replica| #[trigger] (before.locals)(r) == (after.locals)(r) by {
        assert(local_input(held, a, r) == local_input(s, a, r));
    }
    assert(before.locals =~= after.locals);
}

pub open spec fn held_trace<L, I>(
    states: Seq<Network<L, I>>, id: nat, p: Packet<I>, to: Replica, old: L,
) -> Seq<Network<L, I>> {
    states.map(|i: int, s| hold_delivery(s, id, p, to, old))
}

proof fn untouched_absent_slot<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>,
    actions: Seq<Action<I>>, id: nat, end: int,
)
    requires
        trace(update, states, actions), 0 <= end <= actions.len(),
        !states[0].pending.contains_key(id),
        forall|i: int| 0 <= i < end ==> untouched_slot(#[trigger] actions[i], id),
    ensures !states[end].pending.contains_key(id),
    decreases end,
{
    if end > 0 {
        let i = end - 1;
        untouched_absent_slot(update, states, actions, id, i);
        let a = actions[i];
        assert(untouched_slot(a, id));
        assert(states[end] == advance(update, states[i], a));
        match a {
            Action::Send(slot, p) => assert(!states[i].pending.insert(slot, p).contains_key(id)),
            Action::Deliver(slot) => assert(!states[i].pending.remove(slot).contains_key(id)),
            _ => {},
        }
    }
}

// Begin with a real completed suffix after delivery of an issued packet.
// Replay that suffix from the pre-delivery state, keeping the packet queued.
// The finish observer must track completion of the suffix, such as replies.
pub proof fn defer_one_weak_delivery<L, I>(
    update: spec_fn(L, I) -> L,
    guard: spec_fn(Network<L, I>, Action<I>) -> bool,
    completed: spec_fn(Seq<Network<L, I>>, Seq<Action<I>>) -> bool,
    pre: Network<L, I>, id: nat, to: Replica,
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
)
    requires
        enabled(pre, Action::Deliver(id)),
        pre.pending[id].path == Path::Weak,
        pre.pending[id].to == Process::At(to),
        states[0] == advance(update, pre, Action::Deliver(id)),
        protocol_trace(update, guard, states, actions),
        completed(states, actions),
        crash_blind_guard(guard), crash_blind_completion(completed),
        forall|i: int| 0 <= i < actions.len() ==>
            independent_of_delivery(states[i], #[trigger] actions[i], id, to, (pre.locals)(to)),
    ensures ({
        let held = held_trace(states, id, pre.pending[id], to, (pre.locals)(to));
        let end = actions.len() as int;
        held[0] == pre
            && protocol_trace(update, guard, held, actions)
            && completed(held, actions)
            && observations(held, actions) == observations(states, actions)
            && held[end].pending.contains_key(id)
            && held[end].pending[id] == pre.pending[id]
    }),
{
    let p = pre.pending[id];
    let old = (pre.locals)(to);
    let held = held_trace(states, id, p, to, old);
    assert(states[0].pending.remove(id).insert(id, p) =~= pre.pending);
    assert(pre.pending.remove(id).insert(id, p) =~= pre.pending);
    assert forall|r: Replica| #[trigger] (held[0].locals)(r) == (pre.locals)(r) by {
        assert(r == to || local_input(pre, Action::Deliver(id), r).is_none());
    }
    assert(held[0].locals =~= pre.locals);
    assert(held[0] == pre);
    assert(!states[0].pending.contains_key(id));
    assert forall|i: int| 0 <= i < actions.len() implies untouched_slot(#[trigger] actions[i], id)
    by {
        assert(independent_of_delivery(states[i], actions[i], id, to, old));
    }
    assert forall|i: int| 0 <= i <= actions.len() implies !#[trigger] states[i].pending.contains_key(id)
    by {
        untouched_absent_slot(update, states, actions, id, i);
    }
    assert forall|i: int| 0 <= i < actions.len() implies {
        let a = #[trigger] actions[i];
        enabled(held[i], a) && guard(held[i], a)
            && held[i + 1] == advance(update, held[i], a)
    } by {
        let a = actions[i];
        assert(enabled(states[i], a) && guard(states[i], a));
        hold_commutes(update, states[i], a, id, p, to, old);
        assert(process_step(held[i], a) == process_step(states[i], a));
    }
    assert forall|i: int| 0 <= i < actions.len() implies
        #[trigger] observations(held, actions)[i] == observations(states, actions)[i] by {
        let a = actions[i];
        assert(enabled(states[i], a));
        hold_commutes(update, states[i], a, id, p, to, old);
    }
    assert(observations(held, actions) =~= observations(states, actions));
    assert(completed(held, actions));
    assert(held[actions.len() as int].pending.contains_key(id));
}

pub open spec fn delivery_actions<I>(ids: Seq<nat>) -> Seq<Action<I>> {
    ids.map(|i: int, id| Action::Deliver(id))
}

pub open spec fn live_packets_listed<L, I>(
    s: Network<L, I>, ids: Seq<nat>,
) -> bool {
    forall|id: nat| #[trigger] s.pending.contains_key(id) ==>
        ids.contains(id) == live(s, s.pending[id].to)
}

// Closed finite backlog. The listed slots must be exactly the pending
// live-recipient slots; no new sends are required by this transport suffix.
pub proof fn drain_live_backlog<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, ids: Seq<nat>,
)
    requires
        ids.no_duplicates(),
        live_packets_listed(s, ids),
        forall|i: int| 0 <= i < ids.len() ==> #[trigger] s.pending.contains_key(ids[i]),
    ensures ({
        let actions = delivery_actions(ids);
        let states = replay(update, s, actions);
        let end = states[ids.len() as int];
        trace(update, states, actions)
        && (forall|id: nat| #[trigger] end.pending.contains_key(id) ==>
            !live(end, end.pending[id].to))
        && end.r3_crashed == s.r3_crashed && end.unavailable == s.unavailable
        && end.first_stopped == s.first_stopped && end.second_started == s.second_started
    }),
    decreases ids.len(),
{
    let actions = delivery_actions(ids);
    let states = replay(update, s, actions);
    if ids.len() > 0 {
        let id = ids[0];
        assert(s.pending.contains_key(id));
        assert(ids.contains(id));
        assert(enabled(s, Action::Deliver(id)));
        let after = advance(update, s, Action::Deliver(id));
        let rest = ids.drop_first();
        assert(!rest.contains(id)) by {
            if rest.contains(id) {
                let k = choose|k: int| 0 <= k < rest.len() && rest[k] == id;
                assert(ids[k + 1] == ids[0]);
            }
        }
        assert(rest.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < j < rest.len() implies
                #[trigger] rest[i] != #[trigger] rest[j] by {
                assert(ids[i + 1] != ids[j + 1]);
            }
        }
        assert forall|i: int| 0 <= i < rest.len() implies
            #[trigger] after.pending.contains_key(rest[i]) by {
            assert(s.pending.contains_key(ids[i + 1]));
        }
        assert forall|other: nat| #[trigger] after.pending.contains_key(other) implies
            rest.contains(other) == live(after, after.pending[other].to) by {
            assert(other != id && s.pending.contains_key(other));
            assert(s.pending[other] == after.pending[other]);
            if ids.contains(other) {
                let i = choose|i: int| 0 <= i < ids.len() && ids[i] == other;
                assert(rest[i - 1] == other);
            }
            if rest.contains(other) {
                let i = choose|i: int| 0 <= i < rest.len() && rest[i] == other;
                assert(ids[i + 1] == other);
            }
        }
        drain_live_backlog(update, after, rest);
        assert(actions.drop_first() =~= delivery_actions(rest));
    } else {
        assert forall|id: nat| #[trigger] s.pending.contains_key(id) implies
            !live(s, s.pending[id].to) by {
            assert(!ids.contains(id));
        }
    }
    assert(states.len() == actions.len() + 1);
    replay_is_trace_if_complete(update, s, actions);
}

pub open spec fn with_weak_confirmation(b: Branch, value: int) -> Network<int, int> {
    let s = reply_fixture(b, value);
    let ack = Packet { path: Path::Weak, from: Process::At(Replica::R3),
        to: Process::At(origin(b)), input: 0int };
    Network { pending: s.pending.insert(12nat, ack), ..s }
}

pub proof fn replies_can_complete_before_a_queued_confirmation(b: Branch, value: int)
    ensures ({
        let pre = with_weak_confirmation(b, value);
        let held = held_trace(fixture_states(b, value), 12,
            pre.pending[12nat], origin(b), value);
        let end = held[2];
        held[0] == pre
            && has_quorum_replies(held, fixture_actions(), b, value)
            && enabled(end, Action::Deliver(12))
    }),
{
    let pre = with_weak_confirmation(b, value);
    let states = fixture_states(b, value);
    let actions = fixture_actions();
    let update = |x, i| unchanged_int(x, i);
    let guard = |s, a| reply_guard(s, a);
    let observer = |s, a| has_quorum_replies(s, a, b, value);
    reveal_with_fuel(replay, 4);
    two_actual_replies_complete_and_replay(b, value);
    reply_protocol_is_crash_blind::<int, int>(b, value);
    let after = advance(update, pre, Action::Deliver(12));
    let initial = reply_fixture(b, value);
    assert(after.pending =~= initial.pending);
    assert(after.locals =~= initial.locals);
    assert(after == initial);
    assert forall|i: int| 0 <= i < actions.len() implies
        independent_of_delivery(states[i], #[trigger] actions[i], 12, origin(b), value)
    by {
        assert(i == 0 || i == 1);
    }
    defer_one_weak_delivery(update, guard, observer, pre, 12, origin(b), states, actions);
}

}
