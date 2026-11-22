use vstd::prelude::*;
use crate::{Branch, Replica, origin};
use crate::delivery::*;
use crate::scheduling::*;
use crate::protocol::*;

verus! {

pub open spec fn project<L, V, I>(
    view: spec_fn(L) -> V, s: Network<L, I>,
) -> Network<V, I> {
    Network {
        locals: |r: Replica| view((s.locals)(r)),
        pending: s.pending, first_stopped: s.first_stopped,
        r3_crashed: s.r3_crashed, second_started: s.second_started, unavailable: s.unavailable,
    }
}

// A protocol interface, independent of the read result. A local field
// may be omitted only when visible updates factor through this view.
pub open spec fn respects_view<L, V, I>(
    view: spec_fn(L) -> V, update: spec_fn(L, I) -> L, visible_update: spec_fn(V, I) -> V,
) -> bool {
    forall|l: L, input: I| #[trigger] view(update(l, input)) == visible_update(view(l), input)
}

proof fn projection_commutes_with_step<L, V, I>(
    view: spec_fn(L) -> V, update: spec_fn(L, I) -> L, visible_update: spec_fn(V, I) -> V,
    s: Network<L, I>, a: Action<I>,
)
    requires respects_view(view, update, visible_update),
    ensures
        enabled(s, a) == enabled(project(view, s), a),
        project(view, advance(update, s, a)) == advance(visible_update, project(view, s), a),
{
    let after = project(view, advance(update, s, a));
    let visible = advance(visible_update, project(view, s), a);
    assert forall|r: Replica| #[trigger] (after.locals)(r) == (visible.locals)(r) by {
        if let Some(input) = local_input(s, a, r) {
            assert(view(update((s.locals)(r), input)) == visible_update(view((s.locals)(r)), input));
        }
    }
    assert(after.locals =~= visible.locals);
}

pub proof fn lift_visible_schedule<L, V, I>(
    view: spec_fn(L) -> V, update: spec_fn(L, I) -> L, visible_update: spec_fn(V, I) -> V,
    initial: Network<L, I>, states: Seq<Network<V, I>>, actions: Seq<Action<I>>,
)
    requires
        respects_view(view, update, visible_update),
        trace(visible_update, states, actions), states[0] == project(view, initial),
    ensures ({
        let concrete = replay(update, initial, actions);
        trace(update, concrete, actions)
        && concrete.map(|i: int, s| project(view, s)) == states
    }),
    decreases actions.len(),
{
    let concrete = replay(update, initial, actions);
    if actions.len() > 0 {
        let first = actions[0];
        let tail = actions.drop_first();
        let suffix = states.drop_first();
        let next = advance(update, initial, first);
        assert(enabled(states[0], first));
        assert(states[1] == advance(visible_update, states[0], first));
        projection_commutes_with_step(view, update, visible_update, initial, first);
        assert forall|i: int| 0 <= i < tail.len() implies {
            let a = #[trigger] tail[i];
            enabled(suffix[i], a) && suffix[i + 1] == advance(visible_update, suffix[i], a)
        } by {
            assert(actions[i + 1] == tail[i]);
            assert(enabled(states[i + 1], actions[i + 1]));
        }
        lift_visible_schedule(view, update, visible_update, next, suffix, tail);
        let rest = replay(update, next, tail);
        assert(concrete == seq![initial] + rest);
        assert forall|i: int| 0 <= i < concrete.len() implies
            #[trigger] project(view, concrete[i]) == states[i] by {
            if i > 0 {
                assert(rest[i - 1] == concrete[i]);
                assert(suffix[i - 1] == states[i]);
                assert(rest.map(|j: int, s| project(view, s))[i - 1] == suffix[i - 1]);
            }
        }
    }
    assert(concrete.map(|i: int, s| project(view, s)) =~= states);
    replay_is_trace_if_complete(update, initial, actions);
}

pub open spec fn keep_pending<L, I>(
    s: Network<L, I>, id: nat, packet: Packet<I>,
) -> Network<L, I> {
    Network { pending: s.pending.insert(id, packet), ..s }
}

pub(crate) proof fn keep_pending_commutes<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, a: Action<I>, id: nat, packet: Packet<I>,
)
    requires enabled(s, a), untouched_slot(a, id),
    ensures
        enabled(keep_pending(s, id, packet), a),
        process_step(s, a) == process_step(keep_pending(s, id, packet), a),
        advance(update, keep_pending(s, id, packet), a) ==
            keep_pending(advance(update, s, a), id, packet),
{
    let held = keep_pending(s, id, packet);
    let before = advance(update, held, a);
    let after = keep_pending(advance(update, s, a), id, packet);
    match a {
        Action::Deliver(slot) => {
            assert(held.pending[slot] == s.pending[slot]);
            assert(before.pending =~= after.pending);
        },
        Action::Send(slot, p) => {
            assert(held.pending.contains_key(slot) == s.pending.contains_key(slot));
            assert(before.pending =~= after.pending);
        },
        _ => {},
    }
    assert forall|r: Replica| #[trigger] (before.locals)(r) == (after.locals)(r) by {
        assert(local_input(held, a, r) == local_input(s, a, r));
    }
    assert(before.locals =~= after.locals);
}

// A finite response suffix in the read's view lifts to an actual
// concrete execution that still has the unconsumed acknowledgment.
// The guarded protocol interface reads the projected history and events.
pub proof fn defer_ack_with_private_bookkeeping<L, V, I>(
    view: spec_fn(L) -> V, update: spec_fn(L, I) -> L, visible_update: spec_fn(V, I) -> V,
    guard: spec_fn(Network<V, I>, Action<I>) -> bool,
    completed: spec_fn(Seq<Network<V, I>>, Seq<Action<I>>) -> bool,
    pre: Network<L, I>, ack: nat, receiver: Replica,
    states: Seq<Network<V, I>>, actions: Seq<Action<I>>,
)
    requires
        respects_view(view, update, visible_update),
        enabled(pre, Action::Deliver(ack)),
        pre.pending[ack].path == Path::Weak,
        pre.pending[ack].to == Process::At(receiver),
        states[0] == advance(visible_update, project(view, pre), Action::Deliver(ack)),
        visible_update(view((pre.locals)(receiver)), pre.pending[ack].input)
            == view((pre.locals)(receiver)),
        protocol_trace(visible_update, guard, states, actions), completed(states, actions),
        crash_blind_guard(guard), crash_blind_completion(completed),
        forall|i: int| 0 <= i < actions.len() ==> untouched_slot(#[trigger] actions[i], ack),
    ensures ({
        let concrete = replay(update, pre, actions);
        let projected = concrete.map(|i: int, s| project(view, s));
        trace(update, concrete, actions) && protocol_trace(visible_update, guard, projected, actions)
        && completed(projected, actions)
        && observations(projected, actions) == observations(states, actions)
        && concrete[actions.len() as int].pending.contains_key(ack)
        && concrete[actions.len() as int].pending[ack] == pre.pending[ack]
    }),
{
    let p = project(view, pre);
    let packet = pre.pending[ack];
    let held = states.map(|i: int, s| keep_pending(s, ack, packet));
    assert(held[0].pending =~= p.pending);
    assert forall|r: Replica| #[trigger] (held[0].locals)(r) == (p.locals)(r) by {
        if r == receiver {
            assert(visible_update((p.locals)(r), packet.input) == (p.locals)(r));
        }
    }
    assert(held[0].locals =~= p.locals);
    assert(held[0] == p);
    assert forall|i: int| 0 <= i < actions.len() implies {
        let a = #[trigger] actions[i];
        enabled(held[i], a) && guard(held[i], a)
            && held[i + 1] == advance(visible_update, held[i], a)
    } by {
        let a = actions[i];
        assert(enabled(states[i], a) && guard(states[i], a));
        keep_pending_commutes(visible_update, states[i], a, ack, packet);
        assert(process_step(held[i], a) == process_step(states[i], a));
    }
    assert forall|i: int| 0 <= i < actions.len() implies
        #[trigger] observations(held, actions)[i] == observations(states, actions)[i] by {
        let a = actions[i];
        assert(enabled(states[i], a));
        keep_pending_commutes(visible_update, states[i], a, ack, packet);
    }
    assert(observations(held, actions) =~= observations(states, actions));
    assert(completed(held, actions));
    lift_visible_schedule(view, update, visible_update, pre, held, actions);
    assert(held[actions.len() as int].pending.contains_key(ack));
}

pub open spec fn counted_fixture(b: Branch, value: int) -> Network<(int, nat), int> {
    let s = with_weak_confirmation(b, value);
    Network {
        locals: |r: Replica| ((s.locals)(r), 0nat),
        pending: s.pending, first_stopped: s.first_stopped, r3_crashed: s.r3_crashed,
        second_started: s.second_started, unavailable: s.unavailable,
    }
}

pub open spec fn counted_step(s: (int, nat), input: int) -> (int, nat) {
    (s.0, s.1 + 1)
}

pub open spec fn read_cell(s: (int, nat)) -> int { s.0 }

pub open spec fn counted_actions(b: Branch) -> Seq<Action<int>> {
    seq![Action::Local(origin(b), 1), Action::Deliver(10), Action::Deliver(11)]
}

pub proof fn quiet_ack_does_not_block_receiver_steps(b: Branch, value: int)
    ensures ({
        let actions = counted_actions(b);
        let concrete = replay(|s, i| counted_step(s, i), counted_fixture(b, value), actions);
        trace(|s, i| counted_step(s, i), concrete, actions)
            && has_quorum_replies(concrete.map(|i: int, s| project(|l| read_cell(l), s)),
                actions, b, value)
            && concrete[3].pending.contains_key(12)
            && (concrete[3].locals)(origin(b)).1 == 1
    }),
{
    let pre = counted_fixture(b, value);
    let view = |s| read_cell(s);
    let update = |s, input| counted_step(s, input);
    let visible = |x, input| unchanged_int(x, input);
    let guard = |s, a| reply_guard(s, a);
    let completed = |s, a| has_quorum_replies(s, a, b, value);
    let actions = counted_actions(b);
    let start = advance(visible, project(view, pre), Action::Deliver(12));
    let reference = replay(visible, start, actions);
    reveal_with_fuel(replay, 5);
    assert(reference.len() == actions.len() + 1);
    replay_is_trace_if_complete(visible, start, actions);
    assert(sees_reply(reference[1], actions[1], origin(b), value));
    assert(sees_reply(reference[2], actions[2], Replica::R3, value));
    assert forall|i: int| 0 <= i < actions.len() implies guard(reference[i], #[trigger] actions[i]) by {
        assert(i == 0 || i == 1 || i == 2);
    }
    assert forall|i: int| 0 <= i < actions.len() implies untouched_slot(#[trigger] actions[i], 12) by {
        assert(i == 0 || i == 1 || i == 2);
    }
    reply_protocol_is_crash_blind::<int, int>(b, value);
    defer_ack_with_private_bookkeeping(view, update, visible, guard, completed,
        pre, 12, origin(b), reference, actions);
}

// The reference history includes the acknowledgment, so the private
// protocol state cannot be silently reset at the response suffix.
pub proof fn defer_ack_preserves_deterministic_reader<L, V, I, S>(
    view: spec_fn(L) -> V, update: spec_fn(L, I) -> L, visible_update: spec_fn(V, I) -> V,
    m: LocalProtocol<S, V, I>, pre: Network<L, I>, ack: nat, receiver: Replica,
    states: Seq<Network<V, I>>, actions: Seq<Action<I>>,
)
    requires
        respects_view(view, update, visible_update),
        enabled(pre, Action::Deliver(ack)),
        pre.pending[ack].path == Path::Weak,
        pre.pending[ack].to == Process::At(receiver),
        states[0] == advance(visible_update, project(view, pre), Action::Deliver(ack)),
        visible_update(view((pre.locals)(receiver)), pre.pending[ack].input)
            == view((pre.locals)(receiver)),
        trace(visible_update, states, actions),
        forall|i: int| 0 <= i < actions.len() ==> untouched_slot(#[trigger] actions[i], ack),
        ({
            let first = process_step(project(view, pre), Action::Deliver(ack));
            let suffix = observations(states, actions);
            accepted(m, seq![first] + suffix) && completes(m, seq![first] + suffix)
                && head_quiet_for(m, Process::FirstClient, first)
                && (forall|i: int| 0 <= i < suffix.len() ==>
                    head_quiet_for(m, (#[trigger] suffix[i]).actor, first))
        }),
    ensures ({
        let concrete = replay(update, pre, actions);
        let projected = concrete.map(|i: int, s| project(view, s));
        trace(update, concrete, actions)
        && accepted(m, observations(projected, actions))
        && completes(m, observations(projected, actions))
        && concrete[actions.len() as int].pending[ack] == pre.pending[ack]
        && concrete[actions.len() as int].pending.contains_key(ack)
    }),
{
    let first = process_step(project(view, pre), Action::Deliver(ack));
    let suffix = observations(states, actions);
    stateful_suffix_drops_quiet_head(m, first, suffix);
    defer_ack_with_private_bookkeeping(view, update, visible_update, |s, a| true, |s, a| true,
        pre, ack, receiver, states, actions);
}

pub open spec fn private_ack_gate() -> LocalProtocol<bool, int, int> {
    LocalProtocol {
        initial: |p: Process| false,
        accept: |ready: bool, event: ProcessStep<int, int>|
            event.action != Action::Strong(Process::At(Replica::R1)) || ready,
        update: |ready: bool, event: ProcessStep<int, int>| ready
            || (event.incoming.is_some() && event.incoming.unwrap().path == Path::Weak),
        done: |ready: bool| ready,
    }
}

pub proof fn relevant_ack_history_cannot_be_discarded()
    ensures ({
        let pre = with_weak_confirmation(Branch::Beta, 2);
        let ack = process_step(pre, Action::Deliver(12));
        let next = process_step(pre, Action::Strong(Process::At(Replica::R1)));
        let m = private_ack_gate();
        accepted(m, seq![ack, next]) && !accepted(m, seq![next])
            && !head_quiet_for(m, Process::At(Replica::R1), ack)
    }),
{
    let pre = with_weak_confirmation(Branch::Beta, 2);
    let ack = process_step(pre, Action::Deliver(12));
    let next = process_step(pre, Action::Strong(Process::At(Replica::R1)));
    let m = private_ack_gate();
    let history = seq![ack, next];
    reveal_with_fuel(memory, 3);
    assert forall|i: int| 0 <= i < history.len() implies {
        let e = #[trigger] history[i];
        (m.accept)(memory(m, e.actor, history, i as nat), e)
    } by {
        assert(i == 0 || i == 1);
    }
    let short = seq![next];
    assert(short[0] == next);
    assert(!(m.accept)(memory(m, next.actor, short, 0), next));
}

pub proof fn counted_reader_defers_ack_without_resetting_memory(b: Branch, value: int)
    ensures ({
        let pre = counted_fixture(b, value);
        let actions = counted_actions(b);
        let concrete = replay(|s, i| counted_step(s, i), pre, actions);
        let obs = observations(concrete.map(|i: int, s| project(|l| read_cell(l), s)), actions);
        accepted(counts_replies(), obs) && completes(counts_replies(), obs)
            && concrete[3].pending.contains_key(12)
    }),
{
    let pre = counted_fixture(b, value);
    let view = |s| read_cell(s);
    let update = |s, input| counted_step(s, input);
    let visible = |x, input| unchanged_int(x, input);
    let actions = counted_actions(b);
    let start = advance(visible, project(view, pre), Action::Deliver(12));
    let reference = replay(visible, start, actions);
    let head = process_step(project(view, pre), Action::Deliver(12));
    let suffix = observations(reference, actions);
    let obs = seq![head] + suffix;
    let m = counts_replies();
    reveal_with_fuel(replay, 5);
    reveal_with_fuel(memory, 5);
    assert(reference.len() == actions.len() + 1);
    replay_is_trace_if_complete(visible, start, actions);
    assert(head.actor == Process::At(origin(b)));
    assert(head.incoming.unwrap().path == Path::Weak);
    assert(suffix[0].actor == Process::At(origin(b)));
    assert(suffix[1].actor == Process::FirstClient && suffix[2].actor == Process::FirstClient);
    assert(suffix[1].incoming.unwrap().path == Path::FirstReadReply);
    assert(suffix[2].incoming.unwrap().path == Path::FirstReadReply);
    assert forall|i: int| 0 <= i < obs.len() implies {
        let event = #[trigger] obs[i];
        (m.accept)(memory(m, event.actor, obs, i as nat), event)
    } by {
        assert(i == 0 || i == 1 || i == 2 || i == 3);
    }
    assert(completes(m, obs));
    assert forall|i: int| 0 <= i < suffix.len() implies
        head_quiet_for(m, (#[trigger] suffix[i]).actor, head) by {};
    assert forall|i: int| 0 <= i < actions.len() implies untouched_slot(#[trigger] actions[i], 12) by {
        assert(i == 0 || i == 1 || i == 2);
    }
    defer_ack_preserves_deterministic_reader(view, update, visible, m,
        pre, 12, origin(b), reference, actions);
}

// Separate write authority for the inbox handlers. Weak data writes
// and local inputs still enter the read-facing transition if not ACKs.
pub open spec fn read_inbox<V, I>(
    read: spec_fn(V, I) -> V, is_ack: spec_fn(I) -> bool, state: V, input: I,
) -> V {
    if is_ack(input) { state } else { read(state, input) }
}

pub open spec fn owned_inbox<V, B, I>(
    read: spec_fn(V, I) -> V, book: spec_fn(V, B, I) -> B, is_ack: spec_fn(I) -> bool,
    state: (V, B), input: I,
) -> (V, B) {
    (read_inbox(read, is_ack, state.0, input), book(state.0, state.1, input))
}

pub open spec fn weak_ack_event<V, I>(
    event: ProcessStep<V, I>, is_ack: spec_fn(I) -> bool,
) -> bool {
    match event.incoming {
        Some(p) => p.path == Path::Weak && is_ack(p.input),
        None => false,
    }
}

// The control handler never receives the weak-ACK inbox notice. This is
// a routing/ownership policy, not a predicate on the final read result.
pub open spec fn control_inbox<S, V, I>(
    m: LocalProtocol<S, V, I>, is_ack: spec_fn(I) -> bool,
) -> LocalProtocol<S, V, I> {
    LocalProtocol {
        update: |state: S, event: ProcessStep<V, I>| if weak_ack_event(event, is_ack) {
            state
        } else {
            (m.update)(state, event)
        },
        ..m
    }
}

pub proof fn separate_ack_handler_derives_read_independence<S, V, B, I>(
    m: LocalProtocol<S, V, I>, is_ack: spec_fn(I) -> bool,
    read: spec_fn(V, I) -> V, book: spec_fn(V, B, I) -> B,
    pre: Network<(V, B), I>, id: nat, receiver: Replica,
)
    requires
        enabled(pre, Action::Deliver(id)),
        pre.pending[id].path == Path::Weak,
        pre.pending[id].to == Process::At(receiver),
        is_ack(pre.pending[id].input),
    ensures ({
        let view = |state: (V, B)| state.0;
        let concrete = |state, input| owned_inbox(read, book, is_ack, state, input);
        let visible = |state, input| read_inbox(read, is_ack, state, input);
        let first = process_step(project(view, pre), Action::Deliver(id));
        respects_view(view, concrete, visible)
            && visible(view((pre.locals)(receiver)), pre.pending[id].input) == view((pre.locals)(receiver))
            && forall|actor: Process| #[trigger] head_quiet_for(control_inbox(m, is_ack), actor, first)
    }),
{}

pub proof fn separate_inboxes_defer_ack<S, V, B, I>(
    m: LocalProtocol<S, V, I>, is_ack: spec_fn(I) -> bool,
    read: spec_fn(V, I) -> V, book: spec_fn(V, B, I) -> B,
    pre: Network<(V, B), I>, id: nat, receiver: Replica,
    states: Seq<Network<V, I>>, actions: Seq<Action<I>>,
)
    requires
        enabled(pre, Action::Deliver(id)),
        pre.pending[id].path == Path::Weak,
        pre.pending[id].to == Process::At(receiver),
        is_ack(pre.pending[id].input),
        trace(|v, input| read_inbox(read, is_ack, v, input), states, actions),
        states[0] == advance(|v, input| read_inbox(read, is_ack, v, input),
            project(|state: (V, B)| state.0, pre), Action::Deliver(id)),
        forall|i: int| 0 <= i < actions.len() ==> untouched_slot(#[trigger] actions[i], id),
        ({
            let first = process_step(project(|state: (V, B)| state.0, pre), Action::Deliver(id));
            let actual = seq![first] + observations(states, actions);
            accepted(control_inbox(m, is_ack), actual) && completes(control_inbox(m, is_ack), actual)
        }),
    ensures ({
        let concrete = replay(|state, input| owned_inbox(read, book, is_ack, state, input),
            pre, actions);
        let obs = observations(concrete.map(|i: int, s| project(|state: (V, B)| state.0, s)),
            actions);
        trace(|state, input| owned_inbox(read, book, is_ack, state, input), concrete, actions)
            && accepted(control_inbox(m, is_ack), obs) && completes(control_inbox(m, is_ack), obs)
            && concrete[actions.len() as int].pending.contains_key(id)
    }),
{
    separate_ack_handler_derives_read_independence(m, is_ack, read, book, pre, id, receiver);
    let first = process_step(project(|state: (V, B)| state.0, pre), Action::Deliver(id));
    let suffix = observations(states, actions);
    assert forall|i: int| 0 <= i < suffix.len() implies
        head_quiet_for(control_inbox(m, is_ack), (#[trigger] suffix[i]).actor, first) by {};
    defer_ack_preserves_deterministic_reader(|state: (V, B)| state.0,
        |state, input| owned_inbox(read, book, is_ack, state, input),
        |v, input| read_inbox(read, is_ack, v, input), control_inbox(m, is_ack),
        pre, id, receiver, states, actions);
}

}
