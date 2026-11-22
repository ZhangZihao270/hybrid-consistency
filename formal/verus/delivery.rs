use vstd::prelude::*;
use crate::{Replica, Branch, Op, Stores, load, next, origin};

verus! {

pub enum Process {
    At(Replica),
    FirstClient,
    SecondClient,
}

pub enum Path { Weak, FirstReadReply, Strong }

pub struct Packet<I> {
    pub path: Path,
    pub from: Process,
    pub to: Process,
    pub input: I,
}

pub enum Action<I> {
    Local(Replica, I),
    Send(nat, Packet<I>),
    Deliver(nat),
    Strong(Process),
    ClientInput(Process, I),
    StopFirstClient,
    CrashR3,
    StartSecondClient,
}

pub struct Network<L, I> {
    pub locals: spec_fn(Replica) -> L,
    pub pending: Map<nat, Packet<I>>,
    pub first_stopped: bool,
    pub r3_crashed: bool,
    pub second_started: bool,
    pub unavailable: Option<Replica>,
}

pub open spec fn live<L, I>(s: Network<L, I>, p: Process) -> bool {
    match p {
        Process::At(r) => s.unavailable != Some(r) && (r != Replica::R3 || !s.r3_crashed),
        Process::FirstClient => !s.first_stopped,
        Process::SecondClient => s.second_started,
    }
}

pub open spec fn outside_replica(p: Process) -> bool {
    p == Process::FirstClient || p == Process::SecondClient
}

pub open spec fn enabled<L, I>(s: Network<L, I>, a: Action<I>) -> bool {
    match a {
        Action::Send(id, packet) => !s.pending.contains_key(id) && live(s, packet.from)
            && (packet.path != Path::FirstReadReply || packet.to == Process::FirstClient),
        Action::Deliver(id) => s.pending.contains_key(id) && live(s, s.pending[id].to),
        Action::Local(r, _) => live(s, Process::At(r)),
        Action::Strong(p) => live(s, p),
        Action::ClientInput(p, _) => outside_replica(p) && live(s, p),
        Action::StopFirstClient => !s.first_stopped,
        Action::CrashR3 => live(s, Process::At(Replica::R3)),
        Action::StartSecondClient => s.first_stopped && s.r3_crashed && !s.second_started,
    }
}

pub open spec fn local_input<L, I>(s: Network<L, I>, a: Action<I>, r: Replica) -> Option<I> {
    match a {
        Action::Local(at, input) if at == r => Some(input),
        Action::Deliver(id) if s.pending.contains_key(id) && s.pending[id].to == Process::At(r)
            && s.pending[id].path == Path::Weak =>
            Some(s.pending[id].input),
        _ => None,
    }
}

pub open spec fn advance<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, a: Action<I>,
) -> Network<L, I> {
    let pending = match a {
        Action::Send(id, packet) => s.pending.insert(id, packet),
        Action::Deliver(id) => s.pending.remove(id),
        _ => s.pending,
    };
    Network {
        pending,
        first_stopped: s.first_stopped || a == Action::StopFirstClient,
        r3_crashed: s.r3_crashed || a == Action::CrashR3,
        second_started: s.second_started || a == Action::StartSecondClient,
        unavailable: s.unavailable,
        locals: |r: Replica| match local_input(s, a, r) {
            Some(input) => update((s.locals)(r), input),
            None => (s.locals)(r),
        },
    }
}

pub open spec fn trace<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
) -> bool {
    states.len() == actions.len() + 1
    && forall|k: int| 0 <= k < actions.len() ==> {
        let a = #[trigger] actions[k];
        enabled(states[k], a) && states[k + 1] == advance(update, states[k], a)
    }
}

// Transport provenance: a packet still pending was either already
// offered at entry or queued by an enabled send from its live source.
pub proof fn pending_packet_has_live_origin<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
    k: int, id: nat,
)
    requires
        trace(update, states, actions), 0 <= k <= actions.len(),
        states[k].pending.contains_key(id),
    ensures
        (states[0].pending.contains_key(id)
            && states[0].pending[id] == states[k].pending[id])
        || (exists|j: int| 0 <= j < k
            && #[trigger] actions[j] == Action::Send(id, states[k].pending[id])
            && live(states[j], states[k].pending[id].from)),
    decreases k,
{
    if k > 0 {
        let j = k - 1;
        let action = actions[j];
        assert(enabled(states[j], action));
        assert(states[k] == advance(update, states[j], action));
        match action {
            Action::Send(sent_id, packet) if sent_id == id => {
                assert(states[k].pending[id] == packet);
                assert(live(states[j], packet.from));
            },
            _ => {
                match action {
                    Action::Send(other, packet) => {
                        assert(other != id);
                        assert(states[j].pending.insert(other, packet).contains_key(id));
                        assert(states[j].pending.insert(other, packet)[id] == states[j].pending[id]);
                    },
                    Action::Deliver(other) => {
                        assert(other != id);
                        assert(states[j].pending.remove(other).contains_key(id));
                        assert(states[j].pending.remove(other)[id] == states[j].pending[id]);
                    },
                    _ => {},
                }
                assert(states[j].pending.contains_key(id));
                assert(states[j].pending[id] == states[k].pending[id]);
                pending_packet_has_live_origin(update, states, actions, j, id);
            },
        }
    }
}

pub open spec fn survivor<L, I>(s: Network<L, I>) -> (L, L) {
    ((s.locals)(Replica::R1), (s.locals)(Replica::R2))
}

pub open spec fn outside_survivors(p: Process) -> bool {
    p != Process::At(Replica::R1) && p != Process::At(Replica::R2)
}

pub open spec fn can_run_alone<L, I>(s: Network<L, I>, a: Action<I>) -> bool {
    match a {
        Action::Local(r, _) => r == Replica::R3,
        Action::Deliver(id) => s.pending.contains_key(id)
            && (outside_survivors(s.pending[id].to) || s.pending[id].path != Path::Weak),
        _ => true,
    }
}

pub open spec fn common_action<L, I>(
    a: Network<L, I>, ae: Action<I>, b: Network<L, I>, be: Action<I>,
) -> bool {
    match (ae, be) {
        (Action::Local(r, input), Action::Local(other, value)) => r == other && input == value,
        (Action::Deliver(i), Action::Deliver(j)) =>
            a.pending.contains_key(i) && b.pending.contains_key(j)
                && a.pending[i].to == b.pending[j].to
                && a.pending[i].path == b.pending[j].path
                && (a.pending[i].path != Path::Weak || a.pending[i].input == b.pending[j].input),
        _ => false,
    }
}

pub enum Move { AlphaOnly, BetaOnly, Common }

// An interleaving of two actual traces. High-level moves can only pair
// replica-local actions or already issued packets, never suppress a step
// required by either protocol run.
pub open spec fn valid_schedule<L, I>(
    a: Seq<Network<L, I>>, ae: Seq<Action<I>>, i: int,
    b: Seq<Network<L, I>>, be: Seq<Action<I>>, j: int,
    plan: Seq<Move>,
) -> bool
    decreases plan.len(),
{
    if plan.len() == 0 {
        i == ae.len() && j == be.len()
    } else {
        let rest = plan.drop_first();
        match plan[0] {
            Move::AlphaOnly => i < ae.len() && can_run_alone(a[i], ae[i])
                && valid_schedule(a, ae, i + 1, b, be, j, rest),
            Move::BetaOnly => j < be.len() && can_run_alone(b[j], be[j])
                && valid_schedule(a, ae, i, b, be, j + 1, rest),
            Move::Common => i < ae.len() && j < be.len() && common_action(a[i], ae[i], b[j], be[j])
                && valid_schedule(a, ae, i + 1, b, be, j + 1, rest),
        }
    }
}

pub proof fn survivor_context_from_schedule<L, I>(
    update: spec_fn(L, I) -> L,
    a: Seq<Network<L, I>>, ae: Seq<Action<I>>, i: int,
    b: Seq<Network<L, I>>, be: Seq<Action<I>>, j: int,
    plan: Seq<Move>,
)
    requires
        trace(update, a, ae), trace(update, b, be),
        0 <= i <= ae.len(), 0 <= j <= be.len(),
        survivor(a[i]) == survivor(b[j]),
        valid_schedule(a, ae, i, b, be, j, plan),
    ensures survivor(a[ae.len() as int]) == survivor(b[be.len() as int]),
    decreases plan.len(),
{
    reveal(valid_schedule);
    if plan.len() > 0 {
        let rest = plan.drop_first();
        match plan[0] {
            Move::AlphaOnly => {
                assert(a[i + 1] == advance(update, a[i], ae[i]));
                assert(survivor(a[i + 1]) == survivor(a[i]));
                survivor_context_from_schedule(update, a, ae, i + 1, b, be, j, rest);
            },
            Move::BetaOnly => {
                assert(b[j + 1] == advance(update, b[j], be[j]));
                assert(survivor(b[j + 1]) == survivor(b[j]));
                survivor_context_from_schedule(update, a, ae, i, b, be, j + 1, rest);
            },
            Move::Common => {
                assert(a[i + 1] == advance(update, a[i], ae[i]));
                assert(b[j + 1] == advance(update, b[j], be[j]));
                assert(survivor(a[i + 1]) == survivor(b[j + 1]));
                survivor_context_from_schedule(update, a, ae, i + 1, b, be, j + 1, rest);
            },
        }
    }
}

// Stopping the producer does not cancel a packet it already sent.
pub proof fn stopped_sources_can_leave_live_packets<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, id: nat,
)
    requires
        s.pending.contains_key(id),
        s.pending[id].from == Process::At(Replica::R3)
            || s.pending[id].from == Process::FirstClient,
        s.pending[id].to == Process::At(Replica::R1),
        live(s, Process::At(Replica::R1)),
    ensures ({
        let stopped = advance(update, advance(update, s, Action::StopFirstClient), Action::CrashR3);
        enabled(stopped, Action::Deliver(id))
            && !live(stopped, s.pending[id].from)

    }),
{}

pub enum WeakInput {
    Rmw(Op),
    Apply(int),
}

pub open spec fn weak_cell(x: int, input: WeakInput) -> int {
    match input {
        WeakInput::Rmw(op) => next(op, x),
        WeakInput::Apply(v) => v,
    }
}

pub open spec fn weak_local(r: Replica, op: Op) -> Action<WeakInput> {
    Action::Local(r, WeakInput::Rmw(op))
}

pub open spec fn rmw_return(s: Network<int, WeakInput>, r: Replica) -> int {
    (s.locals)(r)
}

// O supplies each completion without incoming cross-replica deliveries.
// This product model gives it its own cell and the RMW returns its prestate.
pub proof fn isolated_completions_compose(s: Network<int, WeakInput>)
    requires
        (s.locals)(Replica::R1) == 1,
        (s.locals)(Replica::R2) == 1,
    ensures ({
        let w1 = weak_local(Replica::R1, Op::W1);
        let w2 = weak_local(Replica::R2, Op::W2);
        let a = advance(|x, input| weak_cell(x, input), s, w1);
        let b = advance(|x, input| weak_cell(x, input), s, w2);
        let ab = advance(|x, input| weak_cell(x, input), a, w2);
        let ba = advance(|x, input| weak_cell(x, input), b, w1);
        rmw_return(s, Replica::R1) == 1 && rmw_return(a, Replica::R2) == 1
            && rmw_return(s, Replica::R2) == 1 && rmw_return(b, Replica::R1) == 1
            && survivor(ab) == (2int, 5int) && survivor(ba) == survivor(ab)
            && ab.pending == s.pending && ba.pending == s.pending
    }),
{}

pub open spec fn offered<L, I>(s: Network<L, I>, id: nat, from: Replica, to: Replica) -> bool {
    s.pending.contains_key(id) && s.pending[id].from == Process::At(from)
        && s.pending[id].to == Process::At(to) && s.pending[id].path == Path::Weak
}

// An existential finite choice among already-issued packets. This does
// not require a link from every replica to every other replica.
pub proof fn offered_update_can_be_delivered<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, id: nat, b: Branch,
)
    requires offered(s, id, origin(b), Replica::R3), live(s, Process::At(Replica::R3)),
    ensures
        enabled(s, Action::Deliver(id)),
        !advance(update, s, Action::Deliver(id)).pending.contains_key(id),
        survivor(advance(update, s, Action::Deliver(id))) == survivor(s),
{
    assert(!s.pending.remove(id).contains_key(id));
}

// The scheduler selects between these two finite extensions of one
// network state. Each branch delivers just its issued R3 update.
pub proof fn split_offered_updates(s: Network<int, WeakInput>, w1: nat, w2: nat)
    requires
        survivor(s) == (2int, 5int), live(s, Process::At(Replica::R3)),
        offered(s, w1, Replica::R1, Replica::R3),
        offered(s, w2, Replica::R2, Replica::R3),
        s.pending[w1].input == WeakInput::Apply(2),
        s.pending[w2].input == WeakInput::Apply(5),
    ensures ({
        let update = |x, input| weak_cell(x, input);
        let alpha = advance(update, s, Action::Deliver(w2));
        let beta = advance(update, s, Action::Deliver(w1));
        trace(update, seq![s, alpha], seq![Action::Deliver(w2)])
            && trace(update, seq![s, beta], seq![Action::Deliver(w1)])
            && survivor(alpha) == survivor(beta)
            && (alpha.locals)(Replica::R3) == 5 && (beta.locals)(Replica::R3) == 2
            && alpha.pending.contains_key(w1) && beta.pending.contains_key(w2)
    }),
{
    let update = |x, input| weak_cell(x, input);
    offered_update_can_be_delivered(update, s, w2, Branch::Alpha);
    offered_update_can_be_delivered(update, s, w1, Branch::Beta);
    assert(w1 != w2);
    assert(s.pending.remove(w2).contains_key(w1));
    assert(s.pending.remove(w1).contains_key(w2));
    one_delivery_trace(update, s, w2);
    one_delivery_trace(update, s, w1);
}

proof fn one_delivery_trace<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, id: nat,
)
    requires enabled(s, Action::Deliver(id)),
    ensures trace(update, seq![s, advance(update, s, Action::Deliver(id))],
        seq![Action::Deliver(id)]),
{
    let actions = seq![Action::Deliver(id)];
    let states = seq![s, advance(update, s, Action::Deliver(id))];
    assert forall|i: int| 0 <= i < actions.len() implies {
        let a = #[trigger] actions[i];
        enabled(states[i], a) && states[i + 1] == advance(update, states[i], a)
    } by {
        assert(i == 0);
    }
}

pub open spec fn preserves_cell<L, I>(
    update: spec_fn(L, I) -> L, cell: spec_fn(L) -> int,
    s: Network<L, I>, action: Action<I>, at: Replica,
) -> bool {
    match local_input(s, action, at) {
        Some(input) => cell(update((s.locals)(at), input)) == cell((s.locals)(at)),
        None => true,
    }
}

pub proof fn addressed_steps_preserve_quorum_cell<L, I>(
    update: spec_fn(L, I) -> L, cell: spec_fn(L) -> int,
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
    at: Replica, begin: int, end: int,
)
    requires
        trace(update, states, actions), 0 <= begin <= end <= actions.len(),
        forall|i: int| begin <= i < end ==>
            preserves_cell(update, cell, states[i], #[trigger] actions[i], at),
    ensures cell((states[end].locals)(at)) == cell((states[begin].locals)(at)),
    decreases end - begin,
{
    if end > begin {
        let i = end - 1;
        addressed_steps_preserve_quorum_cell(update, cell, states, actions, at, begin, i);
        assert(states[end] == advance(update, states[i], actions[i]));
        assert(preserves_cell(update, cell, states[i], actions[i], at));
    }
}

// A read may sample at any position in its interval. Only the possible
// source cells, not the other state or even the other cells, must agree.
pub open spec fn sampled(
    snapshots: Seq<Stores>, q: Set<Replica>, result: int,
) -> bool {
    exists|i: int, r: Replica| 0 <= i < snapshots.len()
        && #[trigger] q.contains(r) && #[trigger] load(snapshots[i], r) == result
}

pub proof fn stable_quorum_sample(
    snapshots: Seq<Stores>, q: Set<Replica>, result: int, value: int,
)
    requires
        sampled(snapshots, q, result),
        forall|i: int, r: Replica| 0 <= i < snapshots.len() && q.contains(r)
            ==> #[trigger] load(snapshots[i], r) == value,
    ensures result == value,
{
    let (i, r) = choose|i: int, r: Replica| 0 <= i < snapshots.len()
        && #[trigger] q.contains(r) && #[trigger] load(snapshots[i], r) == result;
    assert(load(snapshots[i], r) == value);
}

// Completion gates describe deliveries required by a protocol, distinct
// from enabled deliveries that the scheduler is free to postpone.
pub open spec fn gate_open<L, I>(s: Network<L, I>, required: Set<nat>) -> bool {
    forall|id: nat| #[trigger] required.contains(id) ==> !s.pending.contains_key(id)
}

pub proof fn withheld_packet_stays_pending<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
    id: nat, k: int,
)
    requires
        trace(update, states, actions),
        states[0].pending.contains_key(id),
        0 <= k <= actions.len(),
        forall|i: int| 0 <= i < k ==> #[trigger] actions[i] != Action::Deliver(id),
    ensures states[k].pending.contains_key(id), states[k].pending[id] == states[0].pending[id],
    decreases k,
{
    if k > 0 {
        let i = k - 1;
        withheld_packet_stays_pending(update, states, actions, id, i);
        let action = actions[i];
        assert(action != Action::Deliver(id));
        assert(states[k] == advance(update, states[i], action));
        match action {
            Action::Deliver(other) => {
                assert(other != id);
                assert(states[i].pending.remove(other).contains_key(id));
            },
            Action::Send(other, packet) => {
                assert(enabled(states[i], action));
                assert(other != id);
                assert(states[i].pending.insert(other, packet).contains_key(id));
            },
            _ => {},
        }
    }
}

pub proof fn required_withheld_packet_blocks_completion<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
    required: Set<nat>, id: nat,
)
    requires
        trace(update, states, actions),
        states[0].pending.contains_key(id), required.contains(id),
        forall|i: int| 0 <= i < actions.len() ==> #[trigger] actions[i] != Action::Deliver(id),
    ensures !gate_open(states[actions.len() as int], required),
{
    withheld_packet_stays_pending(update, states, actions, id, actions.len() as int);
}

// Check only the route of unmatched deliveries and the owners of unmatched
// local steps. A protocol may complete its strong work in either suffix.
pub open spec fn quiet_suffix<L, I>(
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>, begin: int,
) -> bool {
    forall|i: int| begin <= i < actions.len() ==>
        can_run_alone(states[i], #[trigger] actions[i])
}

pub proof fn quiet_suffix_keeps_survivor<L, I>(
    update: spec_fn(L, I) -> L,
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>, begin: int, end: int,
)
    requires
        trace(update, states, actions), quiet_suffix(states, actions, begin),
        0 <= begin <= end <= actions.len(),
    ensures survivor(states[begin]) == survivor(states[end]),
    decreases end - begin,
{
    if begin < end {
        let i = end - 1;
        quiet_suffix_keeps_survivor(update, states, actions, begin, i);
        assert(can_run_alone(states[i], actions[i]));
        assert(states[end] == advance(update, states[i], actions[i]));
    }
}

pub open spec fn shared_prefix_then_quiet<L, I>(
    a: Seq<Network<L, I>>, ae: Seq<Action<I>>,
    b: Seq<Network<L, I>>, be: Seq<Action<I>>, fork: int,
) -> bool {
    a[0] == b[0]
        && 0 <= fork <= ae.len() && fork <= be.len()
        && (forall|i: int| 0 <= i < fork ==> #[trigger] ae[i] == be[i])
        && quiet_suffix(a, ae, fork) && quiet_suffix(b, be, fork)
}

proof fn common_prefix_state<L, I>(
    update: spec_fn(L, I) -> L,
    a: Seq<Network<L, I>>, ae: Seq<Action<I>>,
    b: Seq<Network<L, I>>, be: Seq<Action<I>>, fork: int, k: int,
)
    requires
        trace(update, a, ae), trace(update, b, be),
        shared_prefix_then_quiet(a, ae, b, be, fork), 0 <= k <= fork,
    ensures a[k] == b[k],
    decreases k,
{
    if k > 0 {
        let i = k - 1;
        common_prefix_state(update, a, ae, b, be, fork, i);
        assert(ae[i] == be[i]);
        assert(a[k] == advance(update, a[i], ae[i]));
        assert(b[k] == advance(update, b[i], be[i]));
    }
}

pub proof fn survivor_context_after_quiet_fork<L, I>(
    update: spec_fn(L, I) -> L,
    a: Seq<Network<L, I>>, ae: Seq<Action<I>>,
    b: Seq<Network<L, I>>, be: Seq<Action<I>>, fork: int,
)
    requires trace(update, a, ae), trace(update, b, be), shared_prefix_then_quiet(a, ae, b, be, fork),
    ensures survivor(a[ae.len() as int]) == survivor(b[be.len() as int]),
{
    common_prefix_state(update, a, ae, b, be, fork, fork);
    quiet_suffix_keeps_survivor(update, a, ae, fork, ae.len() as int);
    quiet_suffix_keeps_survivor(update, b, be, fork, be.len() as int);
}

pub open spec fn survivor_initial() -> Network<int, WeakInput> {
    Network {
        locals: |r: Replica| match r { Replica::R1 => 2, Replica::R2 => 5, Replica::R3 => 1 },
        pending: Map::empty(), first_stopped: false, r3_crashed: false, second_started: false,
        unavailable: None,
    }
}

pub open spec fn notice(value: int) -> Packet<WeakInput> {
    Packet { path: Path::Weak, from: Process::At(Replica::R3), to: Process::At(Replica::R1),
        input: WeakInput::Apply(value) }
}

// An SR1 gate might require receiving an already issued branch-dependent
// notice. This fragment tests locality + completion, without claiming T.
pub proof fn a_required_notice_can_break_survivor_agreement()
    ensures ({
        let update = |x, input| weak_cell(x, input);
        let s = survivor_initial();
        let a = advance(update, s, Action::Send(0, notice(5)));
        let b = advance(update, s, Action::Send(0, notice(2)));
        let required = Set::empty().insert(0nat);
        let ax = advance(update, a, Action::Deliver(0));
        let bx = advance(update, b, Action::Deliver(0));
        survivor(a) == survivor(b)
            && !gate_open(a, required) && !gate_open(b, required)
            && trace(update, seq![a, ax], seq![Action::Deliver(0)])
            && trace(update, seq![b, bx], seq![Action::Deliver(0)])
            && gate_open(ax, required) && gate_open(bx, required)
            && !common_action(a, Action::Deliver(0), b, Action::Deliver(0))
            && !can_run_alone(a, Action::Deliver(0))
            && survivor(ax) != survivor(bx)
    }),
{
    let update = |x, input| weak_cell(x, input);
    let s = survivor_initial();
    let a = advance(update, s, Action::Send(0, notice(5)));
    let b = advance(update, s, Action::Send(0, notice(2)));
    let ax = advance(update, a, Action::Deliver(0));
    let bx = advance(update, b, Action::Deliver(0));
    let required = Set::empty().insert(0nat);
    assert(required.contains(0nat));
    assert(a.pending.contains_key(0nat) && b.pending.contains_key(0nat));
    assert(!gate_open(a, required) && !gate_open(b, required));
    assert(ax.pending =~= Map::empty());
    assert(bx.pending =~= Map::empty());
    one_delivery_trace(update, a, 0);
    one_delivery_trace(update, b, 0);
}

// Replays only enabled events. This is a finite prefix builder, not
// a fairness or progress model.
pub open spec fn replay<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, actions: Seq<Action<I>>,
) -> Seq<Network<L, I>>
    decreases actions.len(),
{
    if actions.len() == 0 || !enabled(s, actions[0]) {
        seq![s]
    } else {
        seq![s] + replay(update, advance(update, s, actions[0]), actions.drop_first())
    }
}

pub proof fn replay_is_trace_if_complete<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, actions: Seq<Action<I>>,
)
    ensures
        replay(update, s, actions)[0] == s,
        replay(update, s, actions).len() == actions.len() + 1 ==>
            trace(update, replay(update, s, actions), actions),
    decreases actions.len(),
{
    let states = replay(update, s, actions);
    if actions.len() > 0 && enabled(s, actions[0]) && states.len() == actions.len() + 1 {
        let rest = actions.drop_first();
        let next = advance(update, s, actions[0]);
        let tail = replay(update, next, rest);
        replay_is_trace_if_complete(update, next, rest);
        assert forall|i: int| 0 <= i < actions.len() implies
            enabled(states[i], #[trigger] actions[i])
                && states[i + 1] == advance(update, states[i], actions[i]) by {
            if i > 0 {
                assert(rest[i - 1] == actions[i]);
                assert(tail[i - 1] == states[i]);
                assert(tail[i] == states[i + 1]);
                assert(enabled(tail[i - 1], rest[i - 1]));
            }
        }
    }
}

pub open spec fn offered_fork() -> Network<int, WeakInput> {
    let w1 = Packet { path: Path::Weak, from: Process::At(Replica::R1), to: Process::At(Replica::R3),
        input: WeakInput::Apply(2) };
    let w2 = Packet { path: Path::Weak, from: Process::At(Replica::R2), to: Process::At(Replica::R3),
        input: WeakInput::Apply(5) };
    Network { pending: Map::empty().insert(0, w1).insert(1, w2), ..survivor_initial() }
}

pub open spec fn end_of_branch(b: Branch) -> Seq<Action<WeakInput>> {
    match b {
        Branch::Alpha => seq![Action::Deliver(1), Action::Strong(Process::At(Replica::R3)),
            Action::StopFirstClient, Action::CrashR3, Action::StartSecondClient],
        Branch::Beta => seq![Action::Deliver(0), Action::StopFirstClient, Action::CrashR3,
            Action::StartSecondClient],
    }
}

pub proof fn unequal_branch_suffixes_preserve_survivors()
    ensures ({
        let update = |x, input| weak_cell(x, input);
        let ae = end_of_branch(Branch::Alpha);
        let be = end_of_branch(Branch::Beta);
        let a = replay(update, offered_fork(), ae);
        let b = replay(update, offered_fork(), be);
        trace(update, a, ae) && trace(update, b, be)
        && ae.len() != be.len()
        && survivor(a[5]) == survivor(b[4])
        && a[5].second_started && b[4].second_started
        && (a[5].locals)(Replica::R3) == 5 && (b[4].locals)(Replica::R3) == 2
    }),
{
    let update = |x, input| weak_cell(x, input);
    let ae = end_of_branch(Branch::Alpha);
    let be = end_of_branch(Branch::Beta);
    let a = replay(update, offered_fork(), ae);
    let b = replay(update, offered_fork(), be);
    reveal_with_fuel(replay, 7);
    assert(a.len() == ae.len() + 1 && b.len() == be.len() + 1);
    replay_is_trace_if_complete(update, offered_fork(), ae);
    replay_is_trace_if_complete(update, offered_fork(), be);
    assert forall|i: int| 0 <= i < ae.len() implies
        can_run_alone(a[i], #[trigger] ae[i]) by {
        assert(i == 0 || i == 1 || i == 2 || i == 3 || i == 4);
    }
    assert forall|i: int| 0 <= i < be.len() implies
        can_run_alone(b[i], #[trigger] be[i]) by {
        assert(i == 0 || i == 1 || i == 2 || i == 3);
    }
    survivor_context_after_quiet_fork(update, a, ae, b, be, 0);
}

pub open spec fn without_initial_crash<L, I>(s: Network<L, I>) -> Network<L, I> {
    Network { unavailable: None, ..s }
}

proof fn removal_of_crash_enables_same_step<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, action: Action<I>,
)
    requires enabled(s, action),
    ensures
        enabled(without_initial_crash(s), action),
        advance(update, without_initial_crash(s), action)
            == without_initial_crash(advance(update, s, action)),
{
    let a = advance(update, without_initial_crash(s), action);
    let b = without_initial_crash(advance(update, s, action));
    assert forall|r: Replica| #[trigger] (a.locals)(r) == (b.locals)(r) by {
        assert(local_input(without_initial_crash(s), action, r) == local_input(s, action, r));
    }
    assert(a.locals =~= b.locals);
}

// A finite transport execution with a failed R1/R2 can run with that
// process merely unscheduled. Sends to it and its pending packets remain.
pub proof fn replay_crash_prefix_with_slow_replica<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
)
    requires trace(update, states, actions),
    ensures ({
        let replayed = states.map(|i: int, s| without_initial_crash(s));
        trace(update, replayed, actions)
        && replayed[actions.len() as int].pending == states[actions.len() as int].pending
        && replayed[actions.len() as int].locals == states[actions.len() as int].locals
        && replayed[actions.len() as int].unavailable == None
    }),
{
    let replayed = states.map(|i: int, s| without_initial_crash(s));
    assert forall|i: int| 0 <= i < actions.len() implies {
        let a = #[trigger] actions[i];
        enabled(replayed[i], a) && replayed[i + 1] == advance(update, replayed[i], a)
    } by {
        let a = actions[i];
        assert(enabled(states[i], a));
        removal_of_crash_enables_same_step(update, states[i], a);
    }
}

// A protocol may expose a crash oracle even though the transport does
// not. Its enabledness then need not be monotone under removing failure.
pub proof fn a_crash_oracle_blocks_replay<L, I>(s: Network<L, I>, r: Replica)
    requires s.unavailable == Some(r), r != Replica::R3,
    ensures
        !live(s, Process::At(r)),
        live(without_initial_crash(s), Process::At(r)),
{}

pub open spec fn deliver_slot<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, id: nat,
) -> Network<L, I> {
    advance(update, s, Action::Deliver(id))
}

// The scheduler chooses only a slot. Each machine receives its own
// packet; mere agreement on a slot says nothing about payload equality.
pub proof fn common_slot_can_deliver_different_strong_messages<L, I>(
    update: spec_fn(L, I) -> L, a: Network<L, I>, b: Network<L, I>, id: nat,
)
    requires
        enabled(a, Action::Deliver(id)), enabled(b, Action::Deliver(id)),
        a.pending[id].path == Path::Strong, b.pending[id].path == Path::Strong,
        survivor(a) == survivor(b),
    ensures
        survivor(deliver_slot(update, a, id)) == survivor(deliver_slot(update, b, id)),
        !deliver_slot(update, a, id).pending.contains_key(id),
        !deliver_slot(update, b, id).pending.contains_key(id),
{
    assert(!a.pending.remove(id).contains_key(id));
    assert(!b.pending.remove(id).contains_key(id));
}

pub open spec fn weak_at<L, I>(s: Network<L, I>, id: nat) -> Option<Packet<I>> {
    if s.pending.contains_key(id) && s.pending[id].path == Path::Weak {
        Some(s.pending[id])
    } else {
        None
    }
}

pub open spec fn strong_at<L, I>(s: Network<L, I>, id: nat) -> Option<Packet<I>> {
    if s.pending.contains_key(id) && s.pending[id].path != Path::Weak {
        Some(s.pending[id])
    } else {
        None
    }
}

// No packet accessible at a selected SR2 slot is erased by this split.
pub proof fn pending_partition_is_lossless<L, I>(s: Network<L, I>, id: nat)
    ensures
        s.pending.contains_key(id) == (weak_at(s, id).is_some() || strong_at(s, id).is_some()),
        !(weak_at(s, id).is_some() && strong_at(s, id).is_some()),
        weak_at(s, id).is_some() ==> weak_at(s, id) == Some(s.pending[id]),
        strong_at(s, id).is_some() ==> strong_at(s, id) == Some(s.pending[id]),
{}

pub open spec fn leaves_weak_slot<L, I>(s: Network<L, I>, action: Action<I>, id: nat) -> bool {
    match action {
        Action::Send(slot, packet) => slot != id || packet.path != Path::Weak,
        Action::Deliver(slot) => slot != id || weak_at(s, id).is_none(),
        _ => true,
    }
}

// Local sufficient condition at a slot actually observable by SR2.
// It leaves all other slots and strong effects unconstrained.
pub proof fn unchanged_visible_weak_slot<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
    id: nat, begin: int, end: int,
)
    requires
        trace(update, states, actions), 0 <= begin <= end <= actions.len(),
        forall|i: int| begin <= i < end ==>
            leaves_weak_slot(states[i], #[trigger] actions[i], id),
    ensures weak_at(states[begin], id) == weak_at(states[end], id),
    decreases end - begin,
{
    if end > begin {
        let i = end - 1;
        unchanged_visible_weak_slot(update, states, actions, id, begin, i);
        let action = actions[i];
        assert(enabled(states[i], action));
        assert(leaves_weak_slot(states[i], action, id));
        assert(states[end] == advance(update, states[i], action));
        match action {
            Action::Send(slot, packet) => {
                if slot == id {
                    assert(!states[i].pending.contains_key(id));
                } else {
                    assert(states[end].pending.contains_key(id) == states[i].pending.contains_key(id));
                    assert(states[end].pending[id] == states[i].pending[id]);
                }
            },
            Action::Deliver(slot) => {
                if slot != id {
                    assert(states[end].pending.contains_key(id) == states[i].pending.contains_key(id));
                    assert(states[end].pending[id] == states[i].pending[id]);
                } else {
                    assert(!states[end].pending.contains_key(id));
                }
            },
            _ => {},
        }
    }
}

pub proof fn mandatory_strong_notices_can_differ_without_changing_weak_context()
    ensures ({
        let update = |x, input| weak_cell(x, input);
        let s = survivor_initial();
        let pa = Packet { path: Path::Strong, ..notice(5) };
        let pb = Packet { path: Path::Strong, ..notice(2) };
        let a = advance(update, s, Action::Send(0, pa));
        let b = advance(update, s, Action::Send(0, pb));
        let ax = deliver_slot(update, a, 0);
        let bx = deliver_slot(update, b, 0);
        let required = Set::empty().insert(0nat);
        strong_at(a, 0) != strong_at(b, 0)
            && !gate_open(a, required) && !gate_open(b, required)
            && gate_open(ax, required) && gate_open(bx, required)
            && can_run_alone(a, Action::Deliver(0)) && can_run_alone(b, Action::Deliver(0))
            && survivor(ax) == survivor(bx)
    }),
{
    let update = |x, input| weak_cell(x, input);
    let s = survivor_initial();
    let a = advance(update, s, Action::Send(0, Packet { path: Path::Strong, ..notice(5) }));
    let b = advance(update, s, Action::Send(0, Packet { path: Path::Strong, ..notice(2) }));
    let required = Set::empty().insert(0nat);
    assert(required.contains(0nat));
    assert(a.pending.contains_key(0nat) && b.pending.contains_key(0nat));
    common_slot_can_deliver_different_strong_messages(update, a, b, 0);
    assert(deliver_slot(update, a, 0).pending =~= Map::empty());
    assert(deliver_slot(update, b, 0).pending =~= Map::empty());
}

// Requires only the selected last-hop packet in each actual branch. The
// sender may be a relay, which must preserve the survivor view upstream.
pub proof fn branch_specific_last_hops(
    a: Network<int, WeakInput>, b: Network<int, WeakInput>, ai: nat, bi: nat,
)
    requires
        survivor(a) == (2int, 5int), survivor(b) == (2int, 5int),
        enabled(a, Action::Deliver(ai)), enabled(b, Action::Deliver(bi)),
        a.pending[ai].to == Process::At(Replica::R3),
        b.pending[bi].to == Process::At(Replica::R3),
        a.pending[ai].path == Path::Weak, b.pending[bi].path == Path::Weak,
        a.pending[ai].input == WeakInput::Apply(5),
        b.pending[bi].input == WeakInput::Apply(2),
    ensures ({
        let update = |x, input| weak_cell(x, input);
        let ax = deliver_slot(update, a, ai);
        let bx = deliver_slot(update, b, bi);
        survivor(ax) == survivor(bx)
            && (ax.locals)(Replica::R3) == 5 && (bx.locals)(Replica::R3) == 2
    }),
{}

pub open spec fn packet_at<L, I>(s: Network<L, I>, id: nat) -> Option<Packet<I>> {
    if s.pending.contains_key(id) { Some(s.pending[id]) } else { None }
}

pub proof fn survivor_and_slot_provenance_after_quiet_fork<L, I>(
    update: spec_fn(L, I) -> L,
    a: Seq<Network<L, I>>, ae: Seq<Action<I>>,
    b: Seq<Network<L, I>>, be: Seq<Action<I>>, fork: int, id: nat,
)
    requires
        trace(update, a, ae), trace(update, b, be),
        shared_prefix_then_quiet(a, ae, b, be, fork),
        forall|i: int| fork <= i < ae.len() ==> leaves_weak_slot(a[i], #[trigger] ae[i], id),
        forall|i: int| fork <= i < be.len() ==> leaves_weak_slot(b[i], #[trigger] be[i], id),
    ensures ({
        let ax = a[ae.len() as int];
        let bx = b[be.len() as int];
        survivor(ax) == survivor(bx)
            && weak_at(ax, id) == weak_at(bx, id)
            && (packet_at(ax, id) != packet_at(bx, id) ==> strong_at(ax, id) != strong_at(bx, id))
    }),
{
    survivor_context_after_quiet_fork(update, a, ae, b, be, fork);
    common_prefix_state(update, a, ae, b, be, fork, fork);
    unchanged_visible_weak_slot(update, a, ae, id, fork, ae.len() as int);
    unchanged_visible_weak_slot(update, b, be, id, fork, be.len() as int);
    pending_partition_is_lossless(a[ae.len() as int], id);
    pending_partition_is_lossless(b[be.len() as int], id);
}

pub open spec fn slow_prefix<L, I>(states: Seq<Network<L, I>>) -> Seq<Network<L, I>> {
    states.map(|i: int, s| without_initial_crash(s))
}

// What the active process sees at one step. A network delivery exposes
// the actual packet, including source and payload, rather than a crash bit.
pub struct ProcessStep<L, I> {
    pub actor: Process,
    pub action: Action<I>,
    pub own_local: Option<L>,
    pub incoming: Option<Packet<I>>,
}

pub open spec fn process_step<L, I>(s: Network<L, I>, a: Action<I>) -> ProcessStep<L, I> {
    let incoming = match a {
        Action::Deliver(id) => packet_at(s, id),
        _ => None,
    };
    let actor = match a {
        Action::Local(r, _) => Process::At(r),
        Action::Send(_, p) => p.from,
        Action::Deliver(_) => match incoming {
            Some(p) => p.to,
            None => Process::FirstClient,
        },
        Action::Strong(p) | Action::ClientInput(p, _) => p,
        Action::StopFirstClient => Process::FirstClient,
        Action::CrashR3 => Process::At(Replica::R3),
        Action::StartSecondClient => Process::SecondClient,
    };
    ProcessStep { actor, action: a, incoming, own_local: match actor {
        Process::At(r) => Some((s.locals)(r)),
        _ => None,
    } }
}

pub open spec fn observations<L, I>(
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
) -> Seq<ProcessStep<L, I>> {
    Seq::new(actions.len(), |i: int| process_step(states[i], actions[i]))
}

pub open spec fn crash_blind_guard<L, I>(
    guard: spec_fn(Network<L, I>, Action<I>) -> bool,
) -> bool {
    forall|s: Network<L, I>, t: Network<L, I>, a: Action<I>|
        #![trigger guard(s, a), guard(t, a)]
        process_step(s, a) == process_step(t, a) ==> guard(s, a) == guard(t, a)
}

pub open spec fn protocol_trace<L, I>(
    update: spec_fn(L, I) -> L, guard: spec_fn(Network<L, I>, Action<I>) -> bool,
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
) -> bool {
    trace(update, states, actions) && forall|i: int| 0 <= i < actions.len() ==>
        guard(states[i], #[trigger] actions[i])
}

pub open spec fn crash_blind_completion<L, I>(
    completed: spec_fn(Seq<Network<L, I>>, Seq<Action<I>>) -> bool,
) -> bool {
    forall|s: Seq<Network<L, I>>, t: Seq<Network<L, I>>, a: Seq<Action<I>>|
        #![trigger completed(s, a), completed(t, a)]
        s.len() == a.len() + 1 && t.len() == a.len() + 1
        && observations(s, a) == observations(t, a) ==> completed(s, a) == completed(t, a)
}

pub proof fn replay_preserves_process_observations<L, I>(
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
)
    requires states.len() == actions.len() + 1,
    ensures observations(states, actions) == observations(slow_prefix(states), actions),
{
    let slow = slow_prefix(states);
    let original = observations(states, actions);
    let replayed = observations(slow, actions);
    assert forall|i: int| 0 <= i < actions.len() implies
        #[trigger] original[i] == replayed[i] by {
        assert(slow[i] == without_initial_crash(states[i]));
        assert(process_step(states[i], actions[i]) == process_step(slow[i], actions[i]));
    }
    assert(original =~= replayed);
}

// A finite actual crash execution and its completed read are premises.
// The guard and observer separately respect local observations.
pub proof fn crash_completion_replays_before_r3_crash<L, I>(
    update: spec_fn(L, I) -> L,
    guard: spec_fn(Network<L, I>, Action<I>) -> bool,
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
    completed: spec_fn(Seq<Network<L, I>>, Seq<Action<I>>) -> bool,
    b: Branch,
)
    requires
        protocol_trace(update, guard, states, actions),
        states[0].unavailable == Some(match b {
            Branch::Alpha => Replica::R1, Branch::Beta => Replica::R2,
        }),
        !states[actions.len() as int].r3_crashed,
        completed(states, actions),
        crash_blind_guard(guard),
        crash_blind_completion(completed),
    ensures
        protocol_trace(update, guard, slow_prefix(states), actions),
        completed(slow_prefix(states), actions),
        enabled(slow_prefix(states)[actions.len() as int], Action::CrashR3),
        ({
            let stopped = advance(update, slow_prefix(states)[actions.len() as int], Action::CrashR3);
            stopped.r3_crashed && stopped.unavailable == None
        }),
{
    let slow = slow_prefix(states);
    replay_crash_prefix_with_slow_replica(update, states, actions);
    replay_preserves_process_observations(states, actions);
    assert forall|i: int| 0 <= i < actions.len() implies
        guard(slow[i], #[trigger] actions[i]) by {
        let a = actions[i];
        assert(guard(states[i], a));
        assert(process_step(states[i], a) == process_step(slow[i], a));
    }
    assert(completed(slow, actions));
}

pub open spec fn sees_reply<L, I>(
    s: Network<L, I>, action: Action<I>, from: Replica, input: I,
) -> bool {
    match action {
        Action::Deliver(id) => s.pending.contains_key(id) && s.pending[id] == Packet {
            path: Path::FirstReadReply, from: Process::At(from), to: Process::FirstClient, input,
        },
        _ => false,
    }
}

pub open spec fn has_reply<L, I>(
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>, from: Replica, input: I,
) -> bool {
    exists|i: int| 0 <= i < actions.len() && #[trigger] sees_reply(states[i], actions[i], from, input)
}

pub open spec fn has_quorum_replies<L, I>(
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>, b: Branch, input: I,
) -> bool {
    has_reply(states, actions, origin(b), input) && has_reply(states, actions, Replica::R3, input)
}

// This guard checks the actual delivered packet. It permits other steps,
// but completion in the example still requires both specific replies.
pub open spec fn reply_guard<L, I>(s: Network<L, I>, a: Action<I>) -> bool {
    match process_step(s, a).incoming {
        Some(p) => p.path != Path::FirstReadReply || p.to == Process::FirstClient,
        None => true,
    }
}

proof fn reply_occurrence_respects_observations<L, I>(
    s: Seq<Network<L, I>>, t: Seq<Network<L, I>>, a: Seq<Action<I>>, from: Replica, input: I,
)
    requires
        s.len() == a.len() + 1, t.len() == a.len() + 1,
        observations(s, a) == observations(t, a), has_reply(s, a, from, input),
    ensures has_reply(t, a, from, input),
{
    let i = choose|i: int| 0 <= i < a.len() && #[trigger] sees_reply(s[i], a[i], from, input);
    assert(observations(s, a)[i] == process_step(s[i], a[i]));
    assert(observations(t, a)[i] == process_step(t[i], a[i]));
    assert(process_step(s[i], a[i]).incoming == process_step(t[i], a[i]).incoming);
    assert(sees_reply(t[i], a[i], from, input));
}

pub proof fn reply_protocol_is_crash_blind<L, I>(b: Branch, input: I)
    ensures
        crash_blind_guard(|s: Network<L, I>, a| reply_guard(s, a)),
        crash_blind_completion(|s: Seq<Network<L, I>>, a| has_quorum_replies(s, a, b, input)),
{
    let observer = |s: Seq<Network<L, I>>, a| has_quorum_replies(s, a, b, input);
    assert forall|s: Seq<Network<L, I>>, t: Seq<Network<L, I>>, a: Seq<Action<I>>|
        #![trigger observer(s, a), observer(t, a)]
        s.len() == a.len() + 1 && t.len() == a.len() + 1
        && observations(s, a) == observations(t, a) implies observer(s, a) == observer(t, a) by {
        if observer(s, a) {
            reply_occurrence_respects_observations(s, t, a, origin(b), input);
            reply_occurrence_respects_observations(s, t, a, Replica::R3, input);
        }
        if observer(t, a) {
            reply_occurrence_respects_observations(t, s, a, origin(b), input);
            reply_occurrence_respects_observations(t, s, a, Replica::R3, input);
        }
    }
}

pub open spec fn reply_fixture(b: Branch, value: int) -> Network<int, int> {
    let packet = Packet {
        path: Path::FirstReadReply, from: Process::At(origin(b)),
        to: Process::FirstClient, input: value,
    };
    Network {
        locals: |r: Replica| if r == Replica::R3 || r == origin(b) { value } else { 1int },
        pending: Map::empty().insert(10, packet)
            .insert(11, Packet { from: Process::At(Replica::R3), ..packet }),
        unavailable: Some(match b { Branch::Alpha => Replica::R1, Branch::Beta => Replica::R2 }),
        first_stopped: false, second_started: false, r3_crashed: false,
    }
}

pub open spec fn fixture_actions() -> Seq<Action<int>> {
    seq![Action::Deliver(10), Action::Deliver(11)]
}

pub open spec fn unchanged_int(x: int, input: int) -> int { x }

pub open spec fn fixture_states(b: Branch, value: int) -> Seq<Network<int, int>> {
    replay(|x, input| unchanged_int(x, input), reply_fixture(b, value), fixture_actions())
}

pub proof fn two_actual_replies_complete_and_replay(b: Branch, value: int)
    ensures
        protocol_trace(|x, i| unchanged_int(x, i), |s, a| reply_guard(s, a),
            fixture_states(b, value), fixture_actions()),
        has_quorum_replies(fixture_states(b, value), fixture_actions(), b, value),
        has_quorum_replies(slow_prefix(fixture_states(b, value)), fixture_actions(), b, value),
{
    let update = |x, i| unchanged_int(x, i);
    let states = fixture_states(b, value);
    let actions = fixture_actions();
    let guard = |s, a| reply_guard(s, a);
    let observer = |s, a| has_quorum_replies(s, a, b, value);
    reveal_with_fuel(replay, 4);
    assert(states.len() == actions.len() + 1);
    replay_is_trace_if_complete(update, reply_fixture(b, value), actions);
    assert(sees_reply(states[0], actions[0], origin(b), value));
    assert(sees_reply(states[1], actions[1], Replica::R3, value));
    assert forall|i: int| 0 <= i < actions.len() implies guard(states[i], #[trigger] actions[i]) by {
        assert(i == 0 || i == 1);
    }
    reply_protocol_is_crash_blind::<int, int>(b, value);
    crash_completion_replays_before_r3_crash(update, guard, states, actions, observer, b);
}

pub open spec fn oracle_completion(
    states: Seq<Network<int, int>>, actions: Seq<Action<int>>, b: Branch, value: int,
) -> bool {
    has_quorum_replies(states, actions, b, value) && states[0].unavailable.is_some()
}

pub proof fn same_delivered_replies_do_not_replay_an_oracle_observer(b: Branch, value: int)
    ensures ({
        let states = fixture_states(b, value);
        let actions = fixture_actions();
        oracle_completion(states, actions, b, value)
            && !oracle_completion(slow_prefix(states), actions, b, value)
            && !crash_blind_completion(|s, a| oracle_completion(s, a, b, value))
    }),
{
    let states = fixture_states(b, value);
    let actions = fixture_actions();
    let slow = slow_prefix(states);
    let observer = |s, a| oracle_completion(s, a, b, value);
    two_actual_replies_complete_and_replay(b, value);
    assert(protocol_trace(|x, i| unchanged_int(x, i), |s, a| reply_guard(s, a), states, actions));
    replay_preserves_process_observations(states, actions);
    reveal_with_fuel(replay, 4);
    assert(observer(states, actions));
    assert(!observer(slow, actions));
    if crash_blind_completion(observer) {
        assert(observer(states, actions) == observer(slow, actions));
    }
}

pub open spec fn oracle_guard(s: Network<int, int>, a: Action<int>) -> bool {
    reply_guard(s, a) && (a != Action::Deliver(11) || s.unavailable.is_some())
}

pub proof fn crash_oracle_can_block_a_required_protocol_step(b: Branch, value: int)
    ensures ({
        let s = fixture_states(b, value)[1];
        let slow = without_initial_crash(s);
        let action = Action::Deliver(11);
        enabled(s, action) && enabled(slow, action)
            && oracle_guard(s, action) && !oracle_guard(slow, action)
            && !crash_blind_guard(|state, a| oracle_guard(state, a))
    }),
{
    let s = fixture_states(b, value)[1];
    let slow = without_initial_crash(s);
    let action = Action::Deliver(11);
    let guard = |state, a| oracle_guard(state, a);
    reveal_with_fuel(replay, 4);
    assert(process_step(s, action) == process_step(slow, action));
    assert(guard(s, action) && !guard(slow, action));
    if crash_blind_guard(guard) {
        assert(guard(s, action) == guard(slow, action));
    }
}

}
