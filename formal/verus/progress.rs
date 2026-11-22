use vstd::prelude::*;
use crate::{Branch, Replica, origin};
use crate::delivery::*;
use crate::scheduling::*;
use crate::observation::{project, respects_view, defer_ack_with_private_bookkeeping};
use crate::transparency::{StrongEffect, permitted};

verus! {

#[verifier::reject_recursive_types(L)]
#[verifier::reject_recursive_types(I)]
pub struct Execution<L, I> {
    pub state: spec_fn(nat) -> Network<L, I>,
    pub action: spec_fn(nat) -> Action<I>,
}

pub open spec fn states_through<L, I>(e: Execution<L, I>, n: nat) -> Seq<Network<L, I>> {
    Seq::new(n + 1, |i: int| (e.state)(i as nat))
}

pub open spec fn actions_before<L, I>(e: Execution<L, I>, n: nat) -> Seq<Action<I>> {
    Seq::new(n, |i: int| (e.action)(i as nat))
}

pub open spec fn follows<L, I>(
    e: Execution<L, I>, update: spec_fn(L, I) -> L,
    guard: spec_fn(Network<L, I>, Action<I>) -> bool,
) -> bool {
    forall|i: nat| {
        let a = #[trigger] (e.action)(i);
        enabled((e.state)(i), a) && guard((e.state)(i), a)
            && (e.state)(i + 1) == advance(update, (e.state)(i), a)
    }
}

// An issued packet cannot be postponed forever while its recipient
// remains live. This is tested on the reference execution only.
pub open spec fn delivery_fair<L, I>(e: Execution<L, I>) -> bool {
    forall|i: nat, id: nat| #[trigger] (e.state)(i).pending.contains_key(id)
        ==> exists|j: nat| j >= i && (#[trigger] (e.action)(j) == Action::Deliver(id)
            || !live((e.state)(j), (e.state)(i).pending[id].to))
}

pub open spec fn continuously_runnable<L, I>(
    e: Execution<L, I>, runnable: spec_fn(Network<L, I>, Process) -> bool,
    from: nat, p: Process,
) -> bool {
    forall|i: nat| i >= from ==> #[trigger] runnable((e.state)(i), p)
}

pub open spec fn runs_at<L, I>(e: Execution<L, I>, j: nat, p: Process) -> bool {
    process_step((e.state)(j), (e.action)(j)).actor == p
}

pub open spec fn process_fair<L, I>(
    e: Execution<L, I>, runnable: spec_fn(Network<L, I>, Process) -> bool,
) -> bool {
    forall|from: nat, p: Process| #[trigger] continuously_runnable(e, runnable, from, p)
        ==> exists|j: nat| j >= from && #[trigger] runs_at(e, j, p)
}

pub open spec fn majority_up<L, I>(s: Network<L, I>) -> bool {
    let a = live(s, Process::At(Replica::R1));
    let b = live(s, Process::At(Replica::R2));
    let c = live(s, Process::At(Replica::R3));
    (a && b) || (a && c) || (b && c)
}

// Hybrid formulation of A's progress part. The request is pending at
// entry. The protocol must separately justify this contract for hybrid
// reads and supply an admissible fair execution of that protocol.
pub open spec fn eventually_responds<L, I>(
    e: Execution<L, I>, runnable: spec_fn(Network<L, I>, Process) -> bool,
    completed: spec_fn(Seq<Network<L, I>>, Seq<Action<I>>) -> bool,
) -> bool {
    delivery_fair(e) && process_fair(e, runnable)
        && (forall|i: nat| majority_up(#[trigger] (e.state)(i)))
        ==> exists|n: nat| #[trigger] completed(states_through(e, n), actions_before(e, n))
}

pub(crate) proof fn finite_prefix_is_protocol_trace<L, I>(
    e: Execution<L, I>, update: spec_fn(L, I) -> L,
    guard: spec_fn(Network<L, I>, Action<I>) -> bool, n: nat,
)
    requires follows(e, update, guard),
    ensures protocol_trace(update, guard, states_through(e, n), actions_before(e, n)),
{
    let states = states_through(e, n);
    let actions = actions_before(e, n);
    assert forall|i: int| 0 <= i < n implies {
        let a = #[trigger] actions[i];
        enabled(states[i], a) && guard(states[i], a)
            && states[i + 1] == advance(update, states[i], a)
    } by {
        assert(actions[i] == (e.action)(i as nat));
    }
}

pub open spec fn response_by<L, I>(
    e: Execution<L, I>, completed: spec_fn(Seq<Network<L, I>>, Seq<Action<I>>) -> bool, n: nat,
) -> bool {
    completed(states_through(e, n), actions_before(e, n))
}

proof fn first_response_at_or_before<L, I>(
    e: Execution<L, I>, completed: spec_fn(Seq<Network<L, I>>, Seq<Action<I>>) -> bool, limit: nat,
)
    requires exists|i: nat| i <= limit && #[trigger] response_by(e, completed, i)
    ensures exists|n: nat| n <= limit && #[trigger] response_by(e, completed, n)
        && forall|j: nat| j < n ==> !#[trigger] response_by(e, completed, j)
    decreases limit,
{
    if exists|i: nat| i < limit && #[trigger] response_by(e, completed, i) {
        let i = choose|i: nat| i < limit && #[trigger] response_by(e, completed, i);
        first_response_at_or_before(e, completed, i);
    } else {
        let i = choose|i: nat| i <= limit && #[trigger] response_by(e, completed, i);
        assert(i == limit);
    }
}

// Apply fair progress after receipt, then move the receipt past the finite
// response using an independent commutation rule. No unfair run is used
// as a premise of A.
pub proof fn fair_progress_yields_held_confirmation_prefix<L, I>(
    e: Execution<L, I>, update: spec_fn(L, I) -> L,
    guard: spec_fn(Network<L, I>, Action<I>) -> bool,
    runnable: spec_fn(Network<L, I>, Process) -> bool,
    completed: spec_fn(Seq<Network<L, I>>, Seq<Action<I>>) -> bool,
    pre: Network<L, I>, ack: nat, receiver: Replica, is_ack: spec_fn(I) -> bool, b: Branch,
)
    requires
        enabled(pre, Action::Deliver(ack)),
        pre.pending[ack].path == Path::Weak, is_ack(pre.pending[ack].input),
        pre.pending[ack].from == Process::At(Replica::R3),
        pre.pending[ack].to == Process::At(receiver),
        (e.state)(0) == advance(update, pre, Action::Deliver(ack)),
        pre.unavailable == Some(match b {
            Branch::Alpha => Replica::R1, Branch::Beta => Replica::R2,
        }),
        forall|i: nat| !#[trigger] (e.state)(i).r3_crashed,
        follows(e, update, guard),
        delivery_fair(e), process_fair(e, runnable),
        forall|i: nat| majority_up(#[trigger] (e.state)(i)),
        eventually_responds(e, runnable, completed),
        crash_blind_guard(guard), crash_blind_completion(completed),
        forall|i: nat| (forall|j: nat| j <= i ==> !#[trigger] response_by(e, completed, j))
            ==> independent_of_delivery((e.state)(i), #[trigger] (e.action)(i),
                ack, receiver, (pre.locals)(receiver)),
    ensures exists|n: nat| {
        let actions = actions_before(e, n);
        let held = held_trace(states_through(e, n), ack, pre.pending[ack], receiver,
            (pre.locals)(receiver));
        held[0] == pre && protocol_trace(update, guard, held, actions)
            && completed(held, actions) && #[trigger] response_by(e, completed, n)
            && held[n as int].pending.contains_key(ack)
            && protocol_trace(update, guard, slow_prefix(held), actions)
            && completed(slow_prefix(held), actions)
            && enabled(slow_prefix(held)[n as int], Action::CrashR3)
    },
{
    let limit = choose|n: nat| #[trigger] completed(states_through(e, n), actions_before(e, n));
    assert(response_by(e, completed, limit));
    first_response_at_or_before(e, completed, limit);
    let n = choose|n: nat| n <= limit && #[trigger] response_by(e, completed, n)
        && forall|j: nat| j < n ==> !#[trigger] response_by(e, completed, j);
    let states = states_through(e, n);
    let actions = actions_before(e, n);
    finite_prefix_is_protocol_trace(e, update, guard, n);
    assert forall|i: int| 0 <= i < n implies
        independent_of_delivery(states[i], #[trigger] actions[i], ack, receiver, (pre.locals)(receiver))
    by {
        assert(actions[i] == (e.action)(i as nat));
        assert forall|j: nat| j <= i implies !#[trigger] response_by(e, completed, j) by {};
    }
    defer_one_weak_delivery(update, guard, completed, pre, ack, receiver, states, actions);
    let held = held_trace(states, ack, pre.pending[ack], receiver, (pre.locals)(receiver));
    assert((e.state)(n).r3_crashed == held[n as int].r3_crashed);
    crash_completion_replays_before_r3_crash(update, guard, held, actions, completed, b);
}

pub open spec fn quorum_reference(b: Branch, value: int) -> Execution<int, int> {
    let finite = fixture_states(b, value);
    let replies = fixture_actions();
    Execution {
        state: |i: nat| if i < 2 { finite[i as int] } else { finite[2] },
        action: |i: nat| if i < 2 { replies[i as int] } else { Action::Strong(Process::FirstClient) },
    }
}

pub open spec fn quorum_observer(b: Branch, value: int)
    -> spec_fn(Seq<Network<int, int>>, Seq<Action<int>>) -> bool
{
    |s, a| has_quorum_replies(s, a, b, value)
}

pub proof fn fair_quorum_reference_yields_held_confirmation(b: Branch, value: int)
    ensures exists|n: nat| {
        let e = quorum_reference(b, value);
        let actions = actions_before(e, n);
        let pre = with_weak_confirmation(b, value);
        let held = held_trace(states_through(e, n), 12, pre.pending[12nat], origin(b), value);
        #[trigger] response_by(quorum_reference(b, value), quorum_observer(b, value), n)
            && has_quorum_replies(slow_prefix(held), actions, b, value)
            && held[n as int].pending.contains_key(12)
    },
{
    let e = quorum_reference(b, value);
    let update = |x, i| unchanged_int(x, i);
    let guard = |s, a| reply_guard(s, a);
    let completed = quorum_observer(b, value);
    let runnable = |s: Network<int, int>, p| p == Process::FirstClient;
    let pre = with_weak_confirmation(b, value);
    let finite = fixture_states(b, value);
    reveal_with_fuel(replay, 4);
    two_actual_replies_complete_and_replay(b, value);
    reply_protocol_is_crash_blind::<int, int>(b, value);
    assert(states_through(e, 2) =~= finite);
    assert(actions_before(e, 2) =~= fixture_actions());
    assert(response_by(e, completed, 2));

    let after = advance(update, pre, Action::Deliver(12));
    let initial = (e.state)(0);
    assert(after.pending =~= initial.pending);
    assert(after.locals =~= initial.locals);
    assert(after == initial);

    let end = (e.state)(2);
    let idle = advance(update, end, Action::Strong(Process::FirstClient));
    assert(idle.locals =~= end.locals);
    assert(idle == end);
    assert forall|i: nat| {
        let a = #[trigger] (e.action)(i);
        enabled((e.state)(i), a) && guard((e.state)(i), a)
            && (e.state)(i + 1) == advance(update, (e.state)(i), a)
    } by {};
    assert forall|i: nat| majority_up(#[trigger] (e.state)(i)) by {};
    assert forall|i: nat| !#[trigger] (e.state)(i).r3_crashed by {};

    assert forall|i: nat, id: nat| #[trigger] (e.state)(i).pending.contains_key(id) implies
        exists|j: nat| j >= i && (#[trigger] (e.action)(j) == Action::Deliver(id)
            || !live((e.state)(j), (e.state)(i).pending[id].to)) by {
        if i == 0 && id == 10 {
            assert((e.action)(0) == Action::Deliver(id));
        } else {
            assert(i <= 1 && id == 11);
            assert((e.action)(1) == Action::Deliver(id));
        }
    }
    assert forall|from: nat, p: Process| #[trigger] continuously_runnable(e, runnable, from, p)
        implies exists|j: nat| j >= from && #[trigger] runs_at(e, j, p) by {
        assert(runnable((e.state)(from), p));
        assert(p == Process::FirstClient);
        let j = if from < 2 { 2nat } else { from };
        assert(runs_at(e, j, p));
    }
    assert forall|i: nat| (forall|j: nat| j <= i ==> !#[trigger] response_by(e, completed, j))
        implies independent_of_delivery((e.state)(i), #[trigger] (e.action)(i),
            12, origin(b), (pre.locals)(origin(b))) by {
        assert(i < 2);
    }
    fair_progress_yields_held_confirmation_prefix(e, update, guard, runnable, completed,
        pre, 12, origin(b), |input: int| input == 0, b);
}

// A control check can be crash-blind and perform no explicit promotion,
// yet use the local state changed by a weak input when forming a reply.
pub proof fn a_weak_write_can_change_a_required_reply_observation()
    ensures ({
        let initial = survivor_initial();
        let weak = notice(7);
        let update = |x, i| weak_cell(x, i);
        let pre = advance(update, initial, Action::Send(30, weak));
        let after = advance(update, pre, Action::Deliver(30));
        let step = Action::Strong(Process::At(Replica::R1));
        enabled(after, step) && enabled(pre, step)
            && process_step(after, step).own_local == Some(7int)
            && process_step(pre, step).own_local == Some(2int)
            && !independent_of_delivery(after, step, 30, Replica::R1, 2)
    }),
{}

// Even an acknowledgment that changes only an unused bookkeeping field
// can fail exact observation equality. The proof's criterion must then
// use an independently justified projection of the read's local state.
pub proof fn ack_bookkeeping_can_fail_exact_commutation()
    ensures ({
        let initial = Network {
            locals: |r: Replica| (2int, 0nat),
            pending: Map::empty(),
            first_stopped: false, r3_crashed: false, second_started: false, unavailable: None,
        };
        let ack = Packet { path: Path::Weak, from: Process::At(Replica::R3),
            to: Process::At(Replica::R1), input: 0int };
        let update = |s: (int, nat), input: int| (s.0, s.1 + 1);
        let pre = advance(update, initial, Action::Send(31, ack));
        let after = advance(update, pre, Action::Deliver(31));
        let step = Action::Strong(Process::At(Replica::R1));
        let read = |s: Network<(int, nat), int>| (s.locals)(Replica::R1).0;
        enabled(after, step) && enabled(pre, step) && read(after) == read(pre)
            && !independent_of_delivery(after, step, 31, Replica::R1, (2int, 0nat))
    }),
{}

// For a protocol with an explicit delivery gate, classify a wait by
// the provenance and purpose of the actual blocking packet.
pub open spec fn gate_awaits_promotion<L, I, W>(
    s: Network<L, I>, required: Set<nat>, purpose: spec_fn(I) -> Option<W>, w: W,
) -> bool {
    exists|id: nat| #[trigger] required.contains(id) && s.pending.contains_key(id)
        && s.pending[id].path == Path::Weak && purpose(s.pending[id].input) == Some(w)
}

pub open spec fn gate_effects<L, I, W>(
    s: Network<L, I>, required: Set<nat>, purpose: spec_fn(I) -> Option<W>,
    effect: StrongEffect<W>,
) -> bool {
    match effect {
        StrongEffect::AwaitWeak(w) => gate_awaits_promotion(s, required, purpose, w),
        StrongEffect::StrongOnly => true,
        _ => false,
    }
}

pub proof fn t_distinguishes_required_reply_from_promotion_ack(b: Branch)
    ensures ({
        let s = with_weak_confirmation(b, 5);
        let purpose = |input: int| if input == 0 { Some(5int) } else { None };
        let replies = Set::empty().insert(10nat).insert(11nat);
        let ack = Set::empty().insert(12nat);
        let wait = StrongEffect::AwaitWeak(5int);
        !gate_open(s, replies) && !gate_open(s, ack)
            && !gate_effects(s, replies, purpose, wait)
            && gate_effects(s, ack, purpose, wait) && !permitted(wait)
    }),
{
    let s = with_weak_confirmation(b, 5);
    let purpose = |input: int| if input == 0 { Some(5int) } else { None };
    let replies = Set::empty().insert(10nat).insert(11nat);
    let ack = Set::empty().insert(12nat);
    assert(replies.contains(10nat) && ack.contains(12nat));
    assert(s.pending.contains_key(10nat) && s.pending.contains_key(12nat));
    assert(gate_awaits_promotion(s, ack, purpose, 5));
    if gate_awaits_promotion(s, replies, purpose, 5) {
        let id = choose|id: nat| #[trigger] replies.contains(id) && s.pending.contains_key(id)
            && s.pending[id].path == Path::Weak && purpose(s.pending[id].input) == Some(5);
        assert(id == 10 || id == 11);
    }
}

pub open spec fn projected_replay<L, V, I>(
    view: spec_fn(L) -> V, update: spec_fn(L, I) -> L, pre: Network<L, I>,
    actions: Seq<Action<I>>,
) -> Seq<Network<V, I>> {
    replay(update, pre, actions).map(|i: int, s| project(view, s))
}

// A and fairness are used on the reference model. The concrete replay
// can retain arbitrary bookkeeping omitted by the independently closed
// read view. Kept steps can still run at the acknowledgment recipient.
pub proof fn fair_projected_read_defers_ack<L, V, I>(
    view: spec_fn(L) -> V, update: spec_fn(L, I) -> L, visible_update: spec_fn(V, I) -> V,
    e: Execution<V, I>, guard: spec_fn(Network<V, I>, Action<I>) -> bool,
    runnable: spec_fn(Network<V, I>, Process) -> bool,
    completed: spec_fn(Seq<Network<V, I>>, Seq<Action<I>>) -> bool,
    pre: Network<L, I>, ack: nat, receiver: Replica, is_ack: spec_fn(I) -> bool,
)
    requires
        respects_view(view, update, visible_update),
        enabled(pre, Action::Deliver(ack)),
        pre.pending[ack].path == Path::Weak, is_ack(pre.pending[ack].input),
        pre.pending[ack].to == Process::At(receiver),
        (e.state)(0) == advance(visible_update, project(view, pre), Action::Deliver(ack)),
        visible_update(view((pre.locals)(receiver)), pre.pending[ack].input)
            == view((pre.locals)(receiver)),
        follows(e, visible_update, guard),
        delivery_fair(e), process_fair(e, runnable),
        forall|i: nat| majority_up(#[trigger] (e.state)(i)),
        eventually_responds(e, runnable, completed),
        crash_blind_guard(guard), crash_blind_completion(completed),
        forall|i: nat| (forall|j: nat| j <= i ==> !#[trigger] response_by(e, completed, j))
            ==> untouched_slot(#[trigger] (e.action)(i), ack),
    ensures exists|n: nat| {
        let actions = actions_before(e, n);
        let projected = projected_replay(view, update, pre, actions);
        #[trigger] response_by(e, completed, n)
            && trace(update, replay(update, pre, actions), actions)
            && protocol_trace(visible_update, guard, projected, actions)
            && completed(projected, actions)
            && projected[n as int].pending.contains_key(ack)
            && projected[n as int].pending[ack] == pre.pending[ack]
    },
{
    let limit = choose|n: nat| #[trigger] completed(states_through(e, n), actions_before(e, n));
    assert(response_by(e, completed, limit));
    first_response_at_or_before(e, completed, limit);
    let n = choose|n: nat| n <= limit && #[trigger] response_by(e, completed, n)
        && forall|j: nat| j < n ==> !#[trigger] response_by(e, completed, j);
    let states = states_through(e, n);
    let actions = actions_before(e, n);
    finite_prefix_is_protocol_trace(e, visible_update, guard, n);
    assert forall|i: int| 0 <= i < n implies untouched_slot(#[trigger] actions[i], ack) by {
        assert(actions[i] == (e.action)(i as nat));
        assert forall|j: nat| j <= i implies !#[trigger] response_by(e, completed, j) by {};
    }
    defer_ack_with_private_bookkeeping(view, update, visible_update, guard,
        completed, pre, ack, receiver, states, actions);
}

}
