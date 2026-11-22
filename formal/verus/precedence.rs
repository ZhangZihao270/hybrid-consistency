use vstd::prelude::*;
use crate::{Op, Replica, origin};
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::sr2::*;

verus! {

pub enum Side { Left, Right }

pub open spec fn at_side<V>(versions: (V, V), side: Side) -> V {
    match side { Side::Left => versions.0, Side::Right => versions.1 }
}

// An independent order currently places preferred after the rival, or
// includes preferred while omitting the rival. A particular order need
// not impose any preference between these two versions.
pub open spec fn has_precedence<V>(order: Seq<V>, preferred: V, rival: V) -> bool {
    preferred != rival && exists|i: int| 0 <= i < order.len() && #[trigger] order[i] == preferred
        && (forall|j: int| i < j < order.len() ==> #[trigger] order[j] != rival)
}

// A necessary soundness test for credits issued from independently
// available information. Adding admissible histories can only invalidate
// credits. No whole-order reconstruction, history substitution or
// knowledge test in the running strong reader is involved.
pub open spec fn sound_credit<E, V>(
    credit: spec_fn(E, V, V) -> bool, possible: spec_fn(E, Seq<V>) -> bool,
) -> bool {
    forall|e: E, order: Seq<V>, v: V, rival: V|
        #[trigger] possible(e, order) && #[trigger] credit(e, v, rival) ==> has_precedence(order, v, rival)
}

// Proposed extra clause, evaluated on one read-derived update of retained
// state. before/after are the resolver's source priorities for the same
// current contest and fresh inputs. Some(w) means the causative read
// observed weak version w. None denotes an ordinary strong version.
pub open spec fn supported_read_update<E, V>(
    observed: Option<V>, versions: (V, V), before: Side, after: Side,
    available: E, credit: spec_fn(E, V, V) -> bool,
) -> bool {
    let old = at_side(versions, before);
    let new = at_side(versions, after);
    old != new && observed == Some(new) ==> credit(available, new, old)
}

// Sufficient implementation discipline. A read can write logs, routing
// state and clocks freely. If the version order is represented by scores,
// increasing the observed weak version's *relative score* needs authority.
// This local write rule never evaluates a read, compares two histories or
// even asks which candidate currently wins.
pub struct Scores<M> { pub left: int, pub right: int, pub other: M }

pub open spec fn elect<M>(s: Scores<M>, tie: Side) -> Side {
    if s.left > s.right { Side::Left } else if s.right > s.left { Side::Right } else { tie }
}

pub open spec fn authorized_score_write<E, V, M>(
    observed: Option<V>, v: (V, V), old: Scores<M>, new: Scores<M>, e: E,
    credit: spec_fn(E, V, V) -> bool,
) -> bool {
    let old_gap = old.left - old.right;
    let new_gap = new.left - new.right;
    v.0 != v.1 ==> ((observed == Some(v.0) && new_gap > old_gap ==> credit(e, v.0, v.1))
        && (observed == Some(v.1) && new_gap < old_gap ==> credit(e, v.1, v.0)))
}

pub proof fn score_write_discipline_implies_supported_update<E, V, M>(
    observed: Option<V>, v: (V, V), old: Scores<M>, new: Scores<M>, e: E,
    credit: spec_fn(E, V, V) -> bool, tie: Side,
)
    requires authorized_score_write(observed, v, old, new, e, credit),
    ensures supported_read_update(observed, v, elect(old, tie), elect(new, tie), e, credit),
{}

// This includes arbitrary ordinary metadata and even a common clock
// increment on both scores. No version-order certificate is needed.
pub proof fn ordinary_updates_are_allowed<E, V, M>(
    old: Scores<M>, other: M, clock: int, e: E, credit: spec_fn(E, V, V) -> bool,
    observed: Option<V>, v: (V, V), tie: Side, completely_new: Scores<M>,
)
    ensures ({
        let new = Scores { left: old.left + clock, right: old.right + clock, other };
        authorized_score_write(observed, v, old, new, e, credit)
            && supported_read_update(observed, v, elect(old, tie), elect(new, tie), e, credit)
            && supported_read_update(None, v, elect(old, tie), elect(completely_new, tie), e, credit)
    }),
{}

// A generic inductive form, allowing any number of changes to ordinary
// state. The comparison is useful for consumers that elect a source
// before loading a value. The choice of candidates and fresh inputs is
// fixed for this interval, not the whole protocol or execution.
pub proof fn first_gain_requires_evidence<E, V, S>(
    states: Seq<S>, priority: spec_fn(S) -> Side, versions: (V, V), observed: V,
    available: E, credit: spec_fn(E, V, V) -> bool, k: nat,
)
    requires
        k < states.len(), at_side(versions, priority(states[0])) != observed,
        at_side(versions, priority(states[k as int])) == observed,
        forall|j: int| 0 <= j < k ==> supported_read_update(Some(observed), versions,
            priority(#[trigger] states[j]), priority(states[j + 1]), available, credit),
    ensures exists|i: int| 0 <= i < k && at_side(versions, priority(#[trigger] states[i])) != observed
        && at_side(versions, priority(states[i + 1])) == observed
        && credit(available, observed, at_side(versions, priority(states[i]))),
    decreases k,
{
    assert(k > 0);
    let prev = (k - 1) as nat;
    if at_side(versions, priority(states[prev as int])) == observed {
        first_gain_requires_evidence(states, priority, versions, observed, available, credit, prev);
        let i = choose|i: int| 0 <= i < prev && at_side(versions, priority(#[trigger] states[i])) != observed
            && at_side(versions, priority(states[i + 1])) == observed
            && credit(available, observed, at_side(versions, priority(states[i])));
        assert(i < k);
    } else {
        assert(supported_read_update(Some(observed), versions, priority(states[prev as int]),
            priority(states[k as int]), available, credit));
    }
}

// Paired consequence for two finite sequences of real metadata states,
// possibly of different lengths. Every state change here descends from
// the one prior read of that branch. Its actual ancestry is a refinement
// obligation when applying this interface to another protocol.
pub proof fn opposed_priorities_need_a_gain<E, V, S>(
    a: Seq<S>, b: Seq<S>, priority: spec_fn(S) -> Side, v: (V, V), e: E, credit: spec_fn(E, V, V) -> bool,
)
    requires
        a.len() > 0, b.len() > 0, v.0 != v.1, priority(a[0]) == priority(b[0]),
        priority(a.last()) == Side::Right, priority(b.last()) == Side::Left,
        !credit(e, v.0, v.1), !credit(e, v.1, v.0),
    ensures
        (exists|j: int| 0 <= j < a.len() - 1 && !supported_read_update(Some(v.1), v,
            priority(#[trigger] a[j]), priority(a[j + 1]), e, credit))
        || (exists|j: int| 0 <= j < b.len() - 1 && !supported_read_update(Some(v.0), v,
            priority(#[trigger] b[j]), priority(b[j + 1]), e, credit)),
{
    let (path, observed) = if priority(a[0]) == Side::Left { (a, v.1) } else { (b, v.0) };
    let k = (path.len() - 1) as nat;
    if forall|j: int| 0 <= j < k ==> supported_read_update(Some(observed), v,
        priority(#[trigger] path[j]), priority(path[j + 1]), e, credit) {
        first_gain_requires_evidence(path, priority, v, observed, e, credit, k);
        let i = choose|i: int| 0 <= i < k && at_side(v, priority(#[trigger] path[i])) != observed
            && at_side(v, priority(path[i + 1])) == observed && credit(e, observed, at_side(v, priority(path[i])));
        assert(false);
    }
}

pub open spec fn source_versions() -> (Op, Op) { (Op::W1, Op::W2) }

pub open spec fn control_at(b: Fork, r: Replica, k: nat) -> Control {
    memory(checkpoint_machine(), at(r), checkpoint_observations(b), k)
}

pub struct IndependentView {
    pub cells: (int, int),
    pub left: Control,
    pub right: Control,
}

pub open spec fn independent_view(b: Fork) -> IndependentView {
    IndependentView {
        cells: survivor(checkpoint_end(b)),
        left: checkpoint_control(b, at(Replica::R1)),
        right: checkpoint_control(b, at(Replica::R2)),
    }
}

pub type Credit = spec_fn(IndependentView, Op, Op) -> bool;
pub type Possible = spec_fn(IndependentView, Seq<Op>) -> bool;

pub open spec fn cut_is_possible(b: Fork, assigned: bool, possible: Possible) -> bool {
    possible(independent_view(b), weak_assignment(b, assigned).ops)
}

pub open spec fn actual_cuts(n: Notice, aa: bool, ab: bool) -> Possible {
    |e: IndependentView, order: Seq<Op>|
        (e == independent_view(alpha(n)) && order == weak_assignment(alpha(n), aa).ops)
        || (e == independent_view(beta(n)) && order == weak_assignment(beta(n), ab).ops)
}

// Most permissive sound credit on reachable inputs of 'possible'. Any
// real extra histories with this same input can only withdraw a credit.
pub open spec fn established<E, V>(possible: spec_fn(E, Seq<V>) -> bool) -> spec_fn(E, V, V) -> bool {
    |e: E, v: V, rival: V| (exists|order: Seq<V>| #[trigger] possible(e, order))
        && (forall|order: Seq<V>| #[trigger] possible(e, order) ==> has_precedence(order, v, rival))
}

pub proof fn maximal_sound_credit<E, V>(
    possible: spec_fn(E, Seq<V>) -> bool, credit: spec_fn(E, V, V) -> bool, e: E, history: Seq<V>,
)
    requires possible(e, history),
    ensures
        sound_credit(established(possible), possible),
        sound_credit(credit, possible) ==> (forall|v: V, rival: V| #[trigger] credit(e, v, rival)
            ==> established(possible)(e, v, rival)),
{
    assert forall|v: V, rival: V| sound_credit(credit, possible) && #[trigger] credit(e, v, rival)
        implies established(possible)(e, v, rival) by {
        assert forall|other: Seq<V>| #[trigger] possible(e, other) implies has_precedence(other, v, rival) by {};
    }
}

pub proof fn equal_independent_views(b: Fork)
    ensures
        independent_view(b) == independent_view(alpha(b.notice)),
        independent_view(b).cells == (2int, 5int),
        checkpoint_control(b, Process::SecondClient) == initial_control(),
        packet_at(checkpoint_end(b), 2) == Some(packet_for(b, 2)),
        forall|k: nat, id: nat| k <= 9 && id <= 10 ==> #[trigger] packet_at(exchange_net(b, k), id)
            == packet_at(checkpoint_end(b), id),
{
    let a = alpha(b.notice);
    let k = actions_to_crash(b).len();
    let j = actions_to_crash(a).len();
    prefix_memory_tracks_actual_messages(b, at(Replica::R1), k);
    prefix_memory_tracks_actual_messages(b, at(Replica::R2), k);
    prefix_memory_tracks_actual_messages(b, Process::SecondClient, k);
    prefix_memory_tracks_actual_messages(a, at(Replica::R1), j);
    prefix_memory_tracks_actual_messages(a, at(Replica::R2), j);
}

// Uses two actual, correctly attributed weak prefix orders. Even granting
// an arbitrary sound decoder, neither conflicting order preference can
// come from the common independent input at this cut.
pub proof fn two_real_cuts_exclude_both_credits(
    n: Notice, aa: bool, ab: bool, possible: Possible, credit: Credit,
)
    requires sound_credit(credit, possible),
        cut_is_possible(alpha(n), aa, possible), cut_is_possible(beta(n), ab, possible),
    ensures !credit(independent_view(alpha(n)), Op::W2, Op::W1),
        !credit(independent_view(beta(n)), Op::W1, Op::W2),
{
    let a = alpha(n);
    let b = beta(n);
    let av = independent_view(a);
    let bv = independent_view(b);
    equal_independent_views(b);
    weak_assignment_at_delivery(a, aa);
    weak_assignment_at_delivery(b, ab);
    let ao = weak_assignment(a, aa).ops;
    let bo = weak_assignment(b, ab).ops;
    assert(!ao.contains(Op::W1) && !bo.contains(Op::W2));
    if credit(av, Op::W2, Op::W1) {
        assert(has_precedence(bo, Op::W2, Op::W1));
        let i = choose|i: int| 0 <= i < bo.len() && #[trigger] bo[i] == Op::W2
            && (forall|j: int| i < j < bo.len() ==> #[trigger] bo[j] != Op::W1);
        assert(bo.contains(Op::W2));
    }
    if credit(bv, Op::W1, Op::W2) {
        assert(has_precedence(ao, Op::W1, Op::W2));
        let i = choose|i: int| 0 <= i < ao.len() && #[trigger] ao[i] == Op::W1
            && (forall|j: int| i < j < ao.len() ==> #[trigger] ao[j] != Op::W2);
        assert(ao.contains(Op::W1));
    }
}

// Evidence is fixed across this comparison window. An adapter supplies the
// actual retained states and the weak sample, if any, causing each update.
pub open spec fn source_of_gain<S>(
    path: Seq<S>, causes: Seq<Option<Op>>, priority: spec_fn(S) -> Side,
    observed: Op, view: IndependentView, credit: Credit,
) -> bool {
    exists|i: int| 0 <= i < path.len() - 1 && {
        let old = priority(#[trigger] path[i]); let new = priority(path[i+1]);
        at_side(source_versions(), old) != observed && at_side(source_versions(), new) == observed
            && (causes[i] != Some(observed)
                || !supported_read_update(causes[i], source_versions(), old, new, view, credit))
    }
}

pub proof fn h_identifies_a_preference_gain_requiring_attribution<S>(
    n: Notice, aa: bool, ab: bool, credit: Credit, paths_a: Seq<S>, paths_b: Seq<S>,
    causes_a: Seq<Option<Op>>, causes_b: Seq<Option<Op>>, priority: spec_fn(S) -> Side,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>,
)
    requires
        n != Notice::Replication ==> aa && ab, sound_credit(credit, actual_cuts(n, aa, ab)),
        paths_a.len() == causes_a.len() + 1, paths_b.len() == causes_b.len() + 1,
        priority(paths_a[0]) == priority(paths_b[0]),
        crate::legal(ao, ax, checkpoint_control(alpha(n), Process::FirstClient).reply.unwrap(),
            at_side(independent_view(alpha(n)).cells, priority(paths_a.last()))),
        crate::legal(bo, bx, checkpoint_control(beta(n), Process::FirstClient).reply.unwrap(),
            at_side(independent_view(beta(n)).cells, priority(paths_b.last()))),
    ensures
        source_of_gain(paths_a, causes_a, priority, observed_writer(alpha(n)), independent_view(alpha(n)), credit)
        || source_of_gain(paths_b, causes_b, priority, observed_writer(beta(n)), independent_view(beta(n)), credit),
{
    hide(crate::legal);
    let a = alpha(n); let b = beta(n); let e = independent_view(a); let v = source_versions();
    fanout_and_reply_deliveries(a); fanout_and_reply_deliveries(b);
    equal_independent_views(a); equal_independent_views(b);
    two_real_cuts_exclude_both_credits(n, aa, ab, actual_cuts(n, aa, ab), credit);
    crate::legal_history_keeps_first_read(ao, ax, 5, at_side(e.cells, priority(paths_a.last())));
    crate::legal_history_keeps_first_read(bo, bx, 2, at_side(e.cells, priority(paths_b.last())));
    assert(priority(paths_a.last()) == Side::Right && priority(paths_b.last()) == Side::Left);
    opposed_priorities_need_a_gain(paths_a, paths_b, priority, v, e, credit);
    let (path, causes, w) = if exists|i: int| 0 <= i < paths_a.len()-1 &&
        !supported_read_update(Some(Op::W2), v, priority(#[trigger] paths_a[i]), priority(paths_a[i+1]), e, credit) {
        (paths_a, causes_a, Op::W2)
    } else { (paths_b, causes_b, Op::W1) };
    let i = choose|i: int| 0 <= i < path.len()-1 && !supported_read_update(Some(w), v,
        priority(#[trigger] path[i]), priority(path[i+1]), e, credit);
    assert(source_of_gain(path, causes, priority, w, e, credit));
}

// The local strong response exposes the replica's own sample. The RMWs
// and the constant source cell in these prefixes identify its writer.
// This decoder is specific to the two distinct values in this workload.
pub open spec fn sampled_writer(e: ProcessStep<int, Wire>) -> Option<Op> {
    match e.action {
        Action::Send(_, p) if first_reply(p) && p.from == e.actor => match p.from {
            Process::At(Replica::R1) if p.input == Wire::Reply(2) && e.own_local == Some(2) => Some(Op::W1),
            Process::At(Replica::R2) if p.input == Wire::Reply(5) && e.own_local == Some(5) => Some(Op::W2),
            _ => None,
        },
        _ => None,
    }
}

pub open spec fn installed_at_sample(b: Fork) -> IndependentView {
    IndependentView {
        cells: survivor(checkpoint_states(b)[9]),
        left: control_at(b, Replica::R1, 9), right: control_at(b, Replica::R2, 9),
    }
}

// Two possible retained-state updates on a genuine R2 strong send.
// A later resolver uses the scores to elect its source. Both handlers
// record the same measurement in the ordinary log.
pub open spec fn on_sample(old: Scores<int>, e: ProcessStep<int, Wire>, prefer_sample: bool) -> Scores<int> {
    let logged = Scores { other: e.own_local.unwrap(), ..old };
    if prefer_sample && sampled_writer(e) == Some(Op::W2) {
        Scores { right: if old.left >= old.right { old.left + 1 } else { old.right }, ..logged }
    } else { logged }
}

pub open spec fn orders_at_sample() -> Possible {
    |e: IndependentView, o: Seq<Op>|
        (e == installed_at_sample(alpha(Notice::G)) && o == weak_assignment(alpha(Notice::G), true).ops)
        || (e == installed_at_sample(beta(Notice::G)) && o == weak_assignment(beta(Notice::G), true).ops)
}

pub proof fn using_a_reply_as_order_evidence_differs_from_logging_it(credit: Credit)
    requires sound_credit(credit, orders_at_sample()),
    ensures ({
        let a = alpha(Notice::G); let b = beta(Notice::G);
        let e = checkpoint_observations(a)[9]; let view = installed_at_sample(a);
        let old = Scores { left: 1int, right: 0int, other: 0int };
        let log = on_sample(old, e, false); let rank = on_sample(old, e, true);
        e == checkpoint_observations(b)[9] && sampled_writer(e) == Some(Op::W2)
            && first_round(a) && first_round(b) && view == installed_at_sample(b)
            && pre_sr1_g(a, weak_assignment(a, true).ops) && pre_sr1_g(b, weak_assignment(b, true).ops)
            && log.other == 5 && rank.other == 5
            && at_side(view.cells, elect(log, Side::Left)) == 2
            && at_side(view.cells, elect(rank, Side::Left)) == 5
            && authorized_score_write(sampled_writer(e), source_versions(), old, log, view, credit)
            && supported_read_update(sampled_writer(e), source_versions(), elect(old, Side::Left),
                elect(log, Side::Left), view, credit)
            && !supported_read_update(sampled_writer(e), source_versions(), elect(old, Side::Left),
                elect(rank, Side::Left), view, credit)
    }),
{
    hide(first_round);
    let a = alpha(Notice::G); let b = beta(Notice::G);
    fanout_and_reply_deliveries(a); fanout_and_reply_deliveries(b);
    crate::isolated_rmws();
    arbitrary_survivor_memory_agrees(Notice::G, checkpoint_machine(), at(Replica::R1), 9);
    arbitrary_survivor_memory_agrees(Notice::G, checkpoint_machine(), at(Replica::R2), 9);
    assert(installed_at_sample(a) == installed_at_sample(b));
    weak_assignment_at_delivery(a, true); weak_assignment_at_delivery(b, true);
    let order = weak_assignment(b, true).ops;
    assert(order == seq![Op::W1]);
    assert(!has_precedence(order, Op::W2, Op::W1));
    assert(orders_at_sample()(installed_at_sample(b), order));
    assert(!credit(installed_at_sample(b), Op::W2, Op::W1));
}

// Alternate delivery window. R3's already-issued status arrives at its origin
// after the crash and before C2 invokes the read.
pub open spec fn after_background_delivery(b: Fork) -> IndependentView {
    let net = checkpoint_states(b)[16];
    let event = process_step(net, Action::Deliver(2));
    let left = control_at(b, Replica::R1, 16);
    let right = control_at(b, Replica::R2, 16);
    IndependentView {
        cells: survivor(advance(|x, w| cell(x, w), net, Action::Deliver(2))),
        left: if event.actor == at(Replica::R1) { change_control(left, event) } else { left },
        right: if event.actor == at(Replica::R2) { change_control(right, event) } else { right },
    }
}

pub open spec fn notice_windows() -> Possible {
    |e: IndependentView, order: Seq<Op>| actual_cuts(Notice::G, true, true)(e, order)
        || (e == after_background_delivery(alpha(Notice::G))
            && order == weak_assignment(alpha(Notice::G), true).ops)
        || (e == after_background_delivery(beta(Notice::G))
            && order == weak_assignment(beta(Notice::G), true).ops)
}

pub open spec fn installed_credit(e: IndependentView, w: Op, rival: Op) -> bool {
    (w == Op::W1 && rival == Op::W2 && e.left.learned == Some(Notice::G))
    || (w == Op::W2 && rival == Op::W1 && e.right.learned == Some(Notice::G))
}

// Total current-data choice, for use even if neither status has arrived.
pub open spec fn read_installed(e: IndependentView) -> int {
    if e.left.learned == Some(Notice::G) { e.cells.0 } else { e.cells.1 }
}

proof fn notice_arrives_before_invocation(b: Fork)
    requires b.notice == Notice::G,
    ensures ({
        let net = checkpoint_states(b)[16];
        let receipt = Action::Deliver(2);
        let up = |x, w| cell(x, w);
        let post = advance(up, net, receipt);
        let later = advance(up, post, Action::StartSecondClient);
        let old = independent_view(b); let seen = after_background_delivery(b);
        trace(up, seq![net, post, later], seq![receipt, Action::StartSecondClient])
            && net.first_stopped && net.r3_crashed && !net.second_started && later.second_started
            && packet_at(net, 2) == Some(packet_for(b, 2)) && !post.pending.contains_key(2)
            && old.cells == seen.cells && seen.cells == (2int, 5int)
            && old.left.learned.is_none() && old.right.learned.is_none()
            && seen.left.learned == (if origin(b.branch) == Replica::R1 { Some(Notice::G) } else { None })
            && seen.right.learned == (if origin(b.branch) == Replica::R2 { Some(Notice::G) } else { None })
    }),
{
    hide(memory);
    let cut = actions_to_crash(b).len();
    prefix_memory_tracks_actual_messages(b, at(Replica::R1), 16);
    prefix_memory_tracks_actual_messages(b, at(Replica::R2), 16);
    prefix_memory_tracks_actual_messages(b, at(Replica::R1), cut);
    prefix_memory_tracks_actual_messages(b, at(Replica::R2), cut);
    let net = checkpoint_states(b)[16];
    let up = |x, w| cell(x, w);
    let post = advance(up, net, Action::Deliver(2));
    let acts = seq![Action::Deliver(2), Action::StartSecondClient];
    let ns = seq![net, post, advance(up, post, Action::StartSecondClient)];
    assert forall|i: int| 0 <= i < 2 implies {
        let a = #[trigger] acts[i]; enabled(ns[i], a) && ns[i + 1] == advance(up, ns[i], a)
    } by { assert(i == 0 || i == 1); }
}

pub proof fn available_weak_evidence_allows_normal_read_and_supported_priority(old: Side)
    ensures ({
        let a = alpha(Notice::G); let b = beta(Notice::G); let c = |e, w, r| installed_credit(e, w, r);
        let av = after_background_delivery(a); let bv = after_background_delivery(b);
        sound_credit(c, notice_windows())
            && read_installed(independent_view(a)) == 5 && read_installed(independent_view(b)) == 5
            && read_installed(av) == 5 && read_installed(bv) == 2
            && supported_read_update(Some(Op::W2), source_versions(), old, Side::Right, av, c)
            && supported_read_update(Some(Op::W1), source_versions(), old, Side::Left, bv, c)
    }),
{
    let a = alpha(Notice::G); let b = beta(Notice::G);
    notice_arrives_before_invocation(a); notice_arrives_before_invocation(b);
    weak_assignment_at_delivery(a, true); weak_assignment_at_delivery(b, true);
    let ao = weak_assignment(a, true).ops; let bo = weak_assignment(b, true).ops;
    assert(ao[0] == Op::W2 && ao.len() == 1 && bo[0] == Op::W1 && bo.len() == 1);
    assert(has_precedence(ao, Op::W2, Op::W1) && has_precedence(bo, Op::W1, Op::W2));
}

}
