use vstd::prelude::*;
use crate::{Branch, Event, LocalPrefix, Op, ReadRun, Replica, delivery, realizes, first_quorum, first_stores,
    legal, legal_history_keeps_first_read, load, sample_window};
use crate::delivery::*;
use crate::protocol::*;
use crate::scheduling::untouched_slot;

verus! {

pub open spec fn outside_delays<L, I>(
    a: Network<L, I>, b: Network<L, I>, held: Set<nat>,
) -> bool {
    a.r3_crashed && b.r3_crashed && a.first_stopped && b.first_stopped
    && a.second_started && b.second_started
    && a.unavailable.is_none() && b.unavailable.is_none()
    && survivor(a) == survivor(b)
    && forall|id: nat| !held.contains(id) ==> packet_at(a, id) == #[trigger] packet_at(b, id)
}

pub open spec fn keeps_delayed_slots<I>(action: Action<I>, held: Set<nat>) -> bool {
    forall|id: nat| #[trigger] held.contains(id) ==> untouched_slot(action, id)
}

// This interface exposes every queue slot outside the delayed set.
// Projecting the pending map is sound only for actual steps that do not
// access the delayed slots, including sends that might reuse a slot.
proof fn a_step_cannot_read_delayed_slots<L, I>(
    update: spec_fn(L, I) -> L, a: Network<L, I>, b: Network<L, I>,
    action: Action<I>, held: Set<nat>,
)
    requires outside_delays(a, b, held), enabled(a, action), keeps_delayed_slots(action, held),
    ensures
        enabled(b, action),
        process_step(a, action) == process_step(b, action),
        outside_delays(advance(update, a, action), advance(update, b, action), held),
{
    match action {
        Action::Send(slot, _) | Action::Deliver(slot) => {
            assert(!held.contains(slot));
            assert(packet_at(a, slot) == packet_at(b, slot));
            assert(a.pending.contains_key(slot) == b.pending.contains_key(slot));
            if a.pending.contains_key(slot) {
                assert(a.pending[slot] == b.pending[slot]);
            }
        },
        _ => {},
    }
    let actor = process_step(a, action).actor;
    assert(actor == Process::At(Replica::R1) || actor == Process::At(Replica::R2)
        || actor == Process::SecondClient);
    let ax = advance(update, a, action);
    let bx = advance(update, b, action);
    assert forall|id: nat| !held.contains(id) implies
        #[trigger] packet_at(bx, id) == packet_at(ax, id) by {
        assert(packet_at(a, id) == packet_at(b, id));
        match action {
            Action::Send(slot, packet) => {
                if slot == id {
                    assert(a.pending.insert(slot, packet).contains_key(id));
                    assert(b.pending.insert(slot, packet).contains_key(id));
                } else {
                    assert(ax.pending.contains_key(id) == a.pending.contains_key(id));
                    assert(bx.pending.contains_key(id) == b.pending.contains_key(id));
                    assert(ax.pending[id] == a.pending[id] && bx.pending[id] == b.pending[id]);
                }
            },
            Action::Deliver(slot) => {
                if slot == id {
                    assert(!ax.pending.contains_key(id) && !bx.pending.contains_key(id));
                } else {
                    assert(ax.pending.contains_key(id) == a.pending.contains_key(id));
                    assert(bx.pending.contains_key(id) == b.pending.contains_key(id));
                    assert(ax.pending[id] == a.pending[id] && bx.pending[id] == b.pending[id]);
                }
            },
            _ => {},
        }
    }
}

pub proof fn replay_sr2_without_touching_delayed_slots<L, I>(
    update: spec_fn(L, I) -> L, a: Seq<Network<L, I>>, b: Network<L, I>,
    actions: Seq<Action<I>>, held: Set<nat>,
)
    requires
        trace(update, a, actions),
        outside_delays(a[0], b, held),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], held),
    ensures ({
        let replayed = replay(update, b, actions);
        trace(update, replayed, actions)
            && observations(a, actions) == observations(replayed, actions)
            && outside_delays(a[actions.len() as int], replayed[actions.len() as int], held)
    }),
    decreases actions.len(),
{
    let replayed = replay(update, b, actions);
    if actions.len() > 0 {
        let first = actions[0];
        let tail = actions.drop_first();
        let a_rest = a.drop_first();
        let next = advance(update, b, first);
        assert(enabled(a[0], first));
        assert(keeps_delayed_slots(first, held));
        assert(a[1] == advance(update, a[0], first));
        a_step_cannot_read_delayed_slots(update, a[0], b, first, held);
        assert forall|i: int| 0 <= i < tail.len() implies {
            let action = #[trigger] tail[i];
            enabled(a_rest[i], action) && a_rest[i + 1] == advance(update, a_rest[i], action)
                && keeps_delayed_slots(action, held)
        } by {
            assert(tail[i] == actions[i + 1]);
            assert(enabled(a[i + 1], actions[i + 1]));
        }
        replay_sr2_without_touching_delayed_slots(update, a_rest, next, tail, held);
        let b_rest = replay(update, next, tail);
        assert(replayed == seq![b] + b_rest);
        assert forall|i: int| 0 <= i < actions.len() implies
            #[trigger] observations(a, actions)[i] == observations(replayed, actions)[i] by {
            if i > 0 {
                assert(a_rest[i - 1] == a[i] && b_rest[i - 1] == replayed[i]);
                assert(tail[i - 1] == actions[i]);
                assert(observations(a_rest, tail)[i - 1] == observations(b_rest, tail)[i - 1]);
            }
        }
    }
    assert(observations(a, actions) =~= observations(replayed, actions));
    assert(replayed.len() == actions.len() + 1);
    replay_is_trace_if_complete(update, b, actions);
}

pub open spec fn sr2_result<S, L, I>(
    m: LocalProtocol<S, L, I>, result: spec_fn(S) -> Option<int>, events: Seq<ProcessStep<L, I>>,
) -> Option<int> {
    result(memory(m, Process::SecondClient, events, events.len()))
}

// Equality follows from an alpha schedule and the unconsumed-slot
// invariant. No beta completion or matched selector observation is needed.
pub proof fn deterministic_sr2_replays_with_same_result<S, L, I>(
    update: spec_fn(L, I) -> L, m: LocalProtocol<S, L, I>,
    result: spec_fn(S) -> Option<int>,
    a: Seq<Network<L, I>>, b: Network<L, I>, actions: Seq<Action<I>>, held: Set<nat>, v: int,
)
    requires
        trace(update, a, actions), outside_delays(a[0], b, held),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], held),
        accepted(m, observations(a, actions)),
        sr2_result(m, result, observations(a, actions)) == Some(v),
    ensures ({
        let replayed = replay(update, b, actions);
        trace(update, replayed, actions) && accepted(m, observations(replayed, actions))
            && sr2_result(m, result, observations(replayed, actions)) == Some(v)
    }),
{
    replay_sr2_without_touching_delayed_slots(update, a, b, actions, held);
}

// The two beta variants are the same actual beta prefix through the
// crash, followed by the derived SR2 schedule. The caller supplies the
// prefix's concrete continuation checkpoints and truthful read samples.
pub proof fn conditional_hot_from_one_completed_sr2<S, L, I>(
    update: spec_fn(L, I) -> L, m: LocalProtocol<S, L, I>,
    result: spec_fn(S) -> Option<int>,
    alpha: LocalPrefix<L, I>, beta: LocalPrefix<L, I>,
    initial: Network<L, I>,
    milestone: spec_fn(Network<L, I>, Event, Network<L, I>) -> bool,
    first_response: spec_fn(Network<L, I>) -> Option<int>,
    alpha_milestones: Seq<Network<L, I>>, beta_milestones: Seq<Network<L, I>>,
    a: Seq<Network<L, I>>, actions: Seq<Action<I>>, held: Set<nat>,
    first_alpha: int, first_beta: int, second_alpha: int,
    alpha_order: Seq<Op>, alpha_register: Seq<int>,
    beta_order: Seq<Op>, beta_register: Seq<int>,
)
    requires
        realizes(initial, milestone, first_response, Branch::Alpha, alpha_milestones,
            ReadRun { start_sr2: a[0], first: first_alpha, second: second_alpha,
                order: alpha_order, states: alpha_register }),
        realizes(initial, milestone, first_response, Branch::Beta, beta_milestones,
            ReadRun { start_sr2: beta.states[beta.actions.len() as int], first: first_beta,
                second: 5, order: beta_order, states: beta_register }),
        trace(update, alpha.states, alpha.actions),
        trace(update, beta.states, beta.actions),
        a[0] == alpha.states[alpha.actions.len() as int],
        trace(update, a, actions),
        outside_delays(a[0], beta.states[beta.actions.len() as int], held),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], held),
        sample_window(alpha.samples, Branch::Alpha, first_alpha),
        sample_window(beta.samples, Branch::Beta, first_beta),
        accepted(m, observations(a, actions)),
        sr2_result(m, result, observations(a, actions)) == Some(second_alpha),
        legal(alpha_order, alpha_register, first_alpha, second_alpha),
    ensures ({
        let replayed = replay(update, beta.states[beta.actions.len() as int], actions);
        trace(update, replayed, actions)
            && accepted(m, observations(replayed, actions))
            && sr2_result(m, result, observations(replayed, actions)) == Some(5)
            && !legal(beta_order, beta_register, first_beta, 5)
    }),
{
    delivery::stable_quorum_sample(alpha.samples, first_quorum(Branch::Alpha),
        first_alpha, load(first_stores(Branch::Alpha), Replica::R3));
    delivery::stable_quorum_sample(beta.samples, first_quorum(Branch::Beta),
        first_beta, load(first_stores(Branch::Beta), Replica::R3));
    assert(first_alpha == 5 && first_beta == 2);
    legal_history_keeps_first_read(alpha_order, alpha_register, first_alpha, second_alpha);
    deterministic_sr2_replays_with_same_result(update, m, result, a,
        beta.states[beta.actions.len() as int], actions, held, second_alpha);
    if legal(beta_order, beta_register, first_beta, 5) {
        legal_history_keeps_first_read(beta_order, beta_register, first_beta, 5);
    }
}

pub open spec fn replay_fixture(beta: bool) -> Network<int, int> {
    let initial = Network {
        locals: |r: Replica| if r == Replica::R1 { 2int } else if r == Replica::R2 { 5int }
            else if beta { 2int } else { 5int },
        pending: Map::empty(), first_stopped: false, r3_crashed: false,
        second_started: false, unavailable: None,
    };
    let v = if beta { 2int } else { 5int };
    let update = |x, i| unchanged_int(x, i);
    let a = advance(update, initial, Action::Send(0, Packet {
        path: Path::Weak, from: Process::At(Replica::R3), to: Process::At(Replica::R1), input: v,
    }));
    let b = advance(update, a, Action::Send(1, Packet {
        path: Path::FirstReadReply, from: if beta { Process::At(Replica::R2) } else { Process::At(Replica::R1) },
        to: Process::FirstClient, input: if beta { 5 } else { 2 },
    }));
    advance(update, advance(update, advance(update, b, Action::StopFirstClient),
        Action::CrashR3), Action::StartSecondClient)
}

pub open spec fn sr2_inbox_reader() -> LocalProtocol<Option<int>, int, int> {
    LocalProtocol {
        initial: |p: Process| None,
        accept: |s: Option<int>, event: ProcessStep<int, int>| true,
        update: |s: Option<int>, event: ProcessStep<int, int>| match event.incoming {
            Some(p) => Some(p.input),
            None => s,
        },
        done: |s: Option<int>| s.is_some(),
    }
}

pub open spec fn common_sr2_exchange() -> Seq<Action<int>> {
    seq![
        Action::Send(3, Packet {
            path: Path::Strong, from: Process::SecondClient,
            to: Process::At(Replica::R2), input: 0,
        }),
        Action::Deliver(3),
        Action::Send(2, Packet {
            path: Path::Strong, from: Process::At(Replica::R2),
            to: Process::SecondClient, input: 5,
        }),
        Action::Deliver(2),
    ]
}

pub proof fn sr2_can_replay_with_two_different_held_packets()
    ensures ({
        let actions = common_sr2_exchange();
        let a = replay(|x, i| unchanged_int(x, i), replay_fixture(false), actions);
        let b = replay(|x, i| unchanged_int(x, i), replay_fixture(true), actions);
        let held = Set::empty().insert(0nat).insert(1nat);
        trace(|x, i| unchanged_int(x, i), b, actions)
            && observations(a, actions) == observations(b, actions)
            && sr2_result(sr2_inbox_reader(), |s| s, observations(b, actions)) == Some(5)
            && packet_at(a[4], 0) != packet_at(b[4], 0)
            && packet_at(a[4], 1) != packet_at(b[4], 1)
            && outside_delays(a[4], b[4], held)
    }),
{
    let update = |x, i| unchanged_int(x, i);
    let actions = common_sr2_exchange();
    let alpha = replay_fixture(false);
    let beta = replay_fixture(true);
    let held = Set::empty().insert(0nat).insert(1nat);
    let a = replay(update, alpha, actions);
    let b = replay(update, beta, actions);
    assert forall|id: nat| !held.contains(id) implies #[trigger] packet_at(beta, id) ==
        packet_at(alpha, id) by {};
    assert(outside_delays(alpha, beta, held));
    reveal_with_fuel(replay, 6);
    reveal_with_fuel(memory, 6);
    assert(a.len() == 5);
    replay_is_trace_if_complete(update, alpha, actions);
    assert forall|i: int| 0 <= i < actions.len() implies
        keeps_delayed_slots(#[trigger] actions[i], held) by { assert(i == 0 || i == 1 || i == 2 || i == 3); }
    assert forall|i: int| 0 <= i < observations(a, actions).len() implies {
        let event = #[trigger] observations(a, actions)[i];
        (sr2_inbox_reader().accept)(memory(sr2_inbox_reader(), event.actor,
            observations(a, actions), i as nat), event)
    } by {};
    assert(sr2_result(sr2_inbox_reader(), |s| s, observations(a, actions)) == Some(5));
    deterministic_sr2_replays_with_same_result(update, sr2_inbox_reader(), |s| s,
        a, beta, actions, held, 5);
    replay_sr2_without_touching_delayed_slots(update, a, beta, actions, held);
    assert(packet_at(a[4], 0) != packet_at(b[4], 0));
    assert(packet_at(a[4], 1) != packet_at(b[4], 1));
}

pub proof fn required_delivery_can_expose_distinct_certification()
    ensures ({
        let a = replay_fixture(false);
        let b = replay_fixture(true);
        let delivered = Action::Deliver(0);
        let held = Set::empty().insert(0nat).insert(1nat);
        survivor(a) == survivor(b)
            && enabled(a, delivered) && enabled(b, delivered)
            && process_step(a, delivered).incoming != process_step(b, delivered).incoming
            && !keeps_delayed_slots(delivered, held)
            && !outside_delays(a, b, Set::empty().insert(1nat))
    }),
{
    let held = Set::empty().insert(0nat).insert(1nat);
    assert(held.contains(0nat));
    let others = Set::empty().insert(1nat);
    assert(!others.contains(0nat));
    if outside_delays(replay_fixture(false), replay_fixture(true), others) {
        assert(packet_at(replay_fixture(false), 0) == packet_at(replay_fixture(true), 0));
    }
}

pub open spec fn after_crash<L, I>(s: Network<L, I>) -> bool {
    s.r3_crashed && s.first_stopped && s.second_started && s.unavailable.is_none()
}

pub proof fn postcrash_schedule_has_only_live_actors<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>, k: nat,
)
    requires trace(update, states, actions), k <= actions.len(), after_crash(states[0]),
    ensures
        after_crash(states[k as int]),
        forall|i: int| 0 <= i < k ==> survivor_actor(
            process_step(states[i], #[trigger] actions[i]).actor),
    decreases k,
{
    if k > 0 {
        let i = k - 1;
        postcrash_schedule_has_only_live_actors(update, states, actions, i as nat);
        let action = actions[i];
        assert(enabled(states[i], action));
        assert(states[k as int] == advance(update, states[i], action));
        assert(survivor_actor(process_step(states[i], action).actor));
    }
}

pub proof fn replay_with_actual_private_checkpoints<S, L, I>(
    update: spec_fn(L, I) -> L, m: LocalProtocol<S, L, I>,
    earlier_alpha: Seq<ProcessStep<L, I>>, earlier_beta: Seq<ProcessStep<L, I>>,
    a: Seq<Network<L, I>>, b: Network<L, I>, actions: Seq<Action<I>>, held: Set<nat>,
    result: spec_fn(S) -> Option<int>, v: int,
)
    requires
        trace(update, a, actions), outside_delays(a[0], b, held),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], held),
        forall|p: Process| #[trigger] survivor_actor(p) ==>
            memory(m, p, earlier_alpha, earlier_alpha.len())
                == memory(m, p, earlier_beta, earlier_beta.len()),
        accepted(resume_at(m, earlier_alpha), observations(a, actions)),
        sr2_result(resume_at(m, earlier_alpha), result, observations(a, actions)) == Some(v),
    ensures ({
        let replayed = replay(update, b, actions);
        trace(update, replayed, actions)
            && accepted(resume_at(m, earlier_beta), observations(replayed, actions))
            && sr2_result(resume_at(m, earlier_beta), result, observations(replayed, actions)) == Some(v)
    }),
{
    replay_sr2_without_touching_delayed_slots(update, a, b, actions, held);
    postcrash_schedule_has_only_live_actors(update, a, actions, actions.len());
    let later = observations(a, actions);
    assert forall|i: int| 0 <= i < later.len() implies
        survivor_actor((#[trigger] later[i]).actor) by {
        assert(later[i] == process_step(a[i], actions[i]));
        assert(survivor_actor(process_step(a[i], actions[i]).actor));
    }
    dead_private_history_cannot_change_live_continuation(m, earlier_alpha, earlier_beta, later);
}

}
