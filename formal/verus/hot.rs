use vstd::prelude::*;
pub mod delivery;
pub mod scheduling;
pub mod observation;
pub mod progress;
pub mod certification;
pub mod guarantee;
pub mod survivors;
pub mod checkpoint;
pub mod participation;
pub mod sr2;
pub mod confirmation;
pub mod service;
pub mod unsent;
pub mod attribution;
pub mod stock;
pub mod stock_first;
pub mod quorum_progress;
pub mod stock_quorum;
pub mod ordered_store;
pub mod stock_availability;
pub mod stock_facade;
pub mod facade_progress;
pub mod facade_quorum;
pub mod facade_history;
pub mod facade_linear;
pub mod facade_transport;
pub mod facade_contract;
pub mod ordered_round;
pub mod stock_fair_extension;
pub mod facade_hybrid;
pub mod fanout_replay;
pub mod promotion_wait;
pub mod first_copy_wait;
pub mod fanout_service;
pub mod genesis_escape;
pub mod second_copy_schedule;
pub mod fallback_program;
pub mod fallback_wait;
pub mod fallback_repair;
pub mod irrevocable_order;
pub mod mixed_service_transfer;
pub mod live_quorum;
pub mod sender_forks;
pub mod weak_merge_fork;
pub mod isolated_sender;
pub mod stock_root_service;
pub mod read_dispatch;
pub mod worker_transfer;
pub mod worker_guard;
pub mod guarded_history;
pub mod ordinary_fairness;
pub mod ordinary_duties;
pub mod read_nonblocking;
pub mod read_bookkeeping;
pub mod read_service_rank;
pub mod quorum_service_audit;
pub mod read_call;
pub mod read_issue;
pub mod independent_read;
pub mod fair_read;
pub mod early_crash;
pub mod sr1_majorities;
pub mod first_mailbox;
pub mod first_schedule;
pub mod first_dispatch;
pub mod first_splice;
pub mod first_assembly;
pub mod first_pair;
pub mod first_causality;
pub mod first_service_loss;
pub mod hybrid_majority;
pub mod hybrid_fork;
pub mod hybrid_transparency;
pub mod sr1_contract;
pub mod sr1_ordinary;
pub mod sr1_permission;
pub mod coupled_traffic;
pub mod coupled_reads;
pub mod coupled_construction;
pub mod coupled_sources;
pub mod information_flow;
pub mod r3_value;
pub mod order_extension;
pub mod retained_order;
pub mod r3_comparison;
pub mod independent_preparations;
pub mod guarded_comparison;
pub mod fork_information;
pub mod fork_alternatives;
pub mod mailbox_preparation;
pub mod quorum_schedules;
pub mod quorum_projection;
pub mod reference_resume;
pub mod quorum_contact;
pub mod quorum_ballot;
pub mod schedule_observations;
pub mod fork_dependencies;
pub mod fork_delivery;
pub mod fork_influence;
pub mod first_schedule_checks;
pub mod read_service_contract;
pub mod read_service_checks;
pub mod ordinary_stutter;
pub mod service_obstruction;
pub mod worker_refusal;
pub mod dispatch_boundary;
pub mod mixed_origin_wait;
pub mod validator_block;
pub mod ordinary_install;
pub mod locally_rebuilt;
pub mod genesis_service;
pub mod read_recovery;
pub mod open_read_repair;
pub mod weak_round;
pub mod ordinary_service;
pub mod finite_service;
pub mod stock_reports;
pub mod quorum_rpc;
pub mod rpc_majority;
pub mod mixed_read;
pub mod mixed_hybrid;
pub mod mixed_sources;
pub mod metadata_stock;
pub mod metadata_pair;
pub mod metadata_repair;
pub mod metadata_provenance;
pub mod metadata_reader;
pub mod metadata_fair;
pub mod first_read;
pub mod publisher;
pub mod correspondence;
pub mod stamped;
pub mod precedence;
pub mod protocol;
pub mod transparency;

verus! {

pub enum Op { W1, W2, SR1, SR2 }

pub open spec fn next(op: Op, x: int) -> int {
    match op {
        Op::W1 => x + 1,
        Op::W2 => 5 * x,
        _ => x,
    }
}

// A legal sequential execution of the selected subset, including the
// recorded return values of any selected weak RMWs.
pub open spec fn legal(ops: Seq<Op>, xs: Seq<int>, first: int, second: int) -> bool {
    xs.len() == ops.len() + 1 && xs[0] == 1 && ops.no_duplicates()
    && exists|i: int, j: int| 0 <= i < j < ops.len()
        && #[trigger] ops[i] == Op::SR1 && #[trigger] ops[j] == Op::SR2
    && forall|k: int| 0 <= k < ops.len() ==> {
        let op = #[trigger] ops[k];
        xs[k + 1] == next(op, xs[k])
        && xs[k] == match op {
            Op::W1 | Op::W2 => 1,
            Op::SR1 => first,
            Op::SR2 => second,
        }
    }
}

proof fn state_range(ops: Seq<Op>, xs: Seq<int>, a: int, b: int)
    requires
        xs.len() == ops.len() + 1,
        0 <= a <= b <= ops.len(),
        forall|k: int| a <= k < b ==> {
            let op = #[trigger] ops[k];
            xs[k + 1] == next(op, xs[k])
        },
        1 <= xs[a],
    ensures xs[a] <= xs[b],
    decreases b - a,
{
    if a < b {
        state_range(ops, xs, a, b - 1);
        assert(xs[b] == next(ops[b - 1], xs[b - 1]));
    }
}

pub proof fn legal_history_keeps_first_read(
    ops: Seq<Op>, xs: Seq<int>, first: int, second: int,
)
    requires legal(ops, xs, first, second), first != 1,
    ensures first == second,
{
    let (i, j) = choose|i: int, j: int| 0 <= i < j < ops.len()
        && #[trigger] ops[i] == Op::SR1 && #[trigger] ops[j] == Op::SR2;
    assert(xs[i] == first);
    assert(xs[j] == second);
    state_range(ops, xs, 0, i);
    state_range(ops, xs, i, j);
    assert forall|k: int| i <= k < j implies xs[k + 1] == #[trigger] xs[k] by {
        state_range(ops, xs, i, k);
        assert(xs[k + 1] == next(ops[k], xs[k]));
        match ops[k] {
            Op::W1 | Op::W2 => { assert(xs[k] == 1); }
            _ => {}
        }
    }
    unchanged(xs, i, j);
}

proof fn unchanged(xs: Seq<int>, i: int, j: int)
    requires
        0 <= i <= j < xs.len(),
        forall|k: int| i <= k < j ==> xs[k + 1] == #[trigger] xs[k],
    ensures xs[i] == xs[j],
    decreases j - i,
{
    if i < j {
        unchanged(xs, i, j - 1);
        assert(xs[j] == xs[j - 1]);
    }
}

pub proof fn conflicting_rmws_cannot_both_appear(
    ops: Seq<Op>, xs: Seq<int>, first: int, second: int, i: int, j: int,
)
    requires
        legal(ops, xs, first, second), 0 <= i < j < ops.len(),
        (ops[i] == Op::W1 || ops[i] == Op::W2),
        (ops[j] == Op::W1 || ops[j] == Op::W2),
    ensures false,
{
    assert(xs[i] == 1 && xs[j] == 1);
    assert(xs[i + 1] == next(ops[i], xs[i]));
    state_range(ops, xs, i + 1, j);
}

// Any noninitial value in a legal history comes from an included RMW.
proof fn prior_writer(
    ops: Seq<Op>, xs: Seq<int>, first: int, second: int, k: int,
)
    requires legal(ops, xs, first, second), 0 <= k <= ops.len(), xs[k] != 1,
    ensures exists|p: int| 0 <= p < k && (
        (#[trigger] ops[p] == Op::W1 && xs[k] == 2)
        || (ops[p] == Op::W2 && xs[k] == 5)
    ),
    decreases k,
{
    assert(k > 0);
    let p = k - 1;
    assert(xs[k] == next(ops[p], xs[p]));
    match ops[p] {
        Op::W1 | Op::W2 => { assert(xs[p] == 1); }
        _ => { prior_writer(ops, xs, first, second, p); }
    }
}

pub proof fn first_read_includes_its_writer(
    ops: Seq<Op>, xs: Seq<int>, first: int, second: int,
)
    requires legal(ops, xs, first, second), first != 1,
    ensures exists|p: int, i: int| 0 <= p < i < ops.len()
        && #[trigger] ops[i] == Op::SR1
        && ((#[trigger] ops[p] == Op::W1 && first == 2)
            || (ops[p] == Op::W2 && first == 5)),
{
    let (i, j) = choose|i: int, j: int| 0 <= i < j < ops.len()
        && #[trigger] ops[i] == Op::SR1 && #[trigger] ops[j] == Op::SR2;
    assert(xs[i] == first);
    prior_writer(ops, xs, first, second, i);
    let p = choose|p: int| 0 <= p < i && (
        (#[trigger] ops[p] == Op::W1 && first == 2)
        || (ops[p] == Op::W2 && first == 5)
    );
    assert(0 <= p < i < ops.len() && ops[i] == Op::SR1);
}

pub proof fn conditional_history_contradiction(
    alpha: Seq<Op>, ax: Seq<int>, beta: Seq<Op>, bx: Seq<int>, u: int,
)
    requires legal(alpha, ax, 5, u), legal(beta, bx, 2, u),
    ensures false,
{
    legal_history_keeps_first_read(alpha, ax, 5, u);
    legal_history_keeps_first_read(beta, bx, 2, u);
}


pub enum Replica { R1, R2, R3 }
pub enum Branch { Alpha, Beta }

pub struct Stores {
    pub r1: int,
    pub r2: int,
    pub r3: int,
}

pub open spec fn initial() -> Stores {
    Stores { r1: 1, r2: 1, r3: 1 }
}

// Both requests are already invoked. Each local step returns its input
// and writes its RMW result. Delivery of network messages is a separate step.
pub open spec fn local_w1(s: Stores) -> (Stores, int) {
    (Stores { r1: next(Op::W1, s.r1), ..s }, s.r1)
}

pub open spec fn local_w2(s: Stores) -> (Stores, int) {
    (Stores { r2: next(Op::W2, s.r2), ..s }, s.r2)
}

pub open spec fn isolated() -> Stores {
    local_w2(local_w1(initial()).0).0
}

pub proof fn isolated_rmws()
    ensures
        local_w1(initial()).1 == 1,
        local_w2(local_w1(initial()).0).1 == 1,
        isolated() == (Stores { r1: 2, r2: 5, r3: 1 }),
        local_w1(local_w2(initial()).0).0 == isolated(),
        local_w2(initial()).1 == 1,
        local_w1(local_w2(initial()).0).1 == 1,
{}

pub open spec fn origin(b: Branch) -> Replica {
    match b {
        Branch::Alpha => Replica::R2,
        Branch::Beta => Replica::R1,
    }
}

pub open spec fn load(s: Stores, r: Replica) -> int {
    match r {
        Replica::R1 => s.r1,
        Replica::R2 => s.r2,
        Replica::R3 => s.r3,
    }
}

pub open spec fn deliver_to_r3(s: Stores, b: Branch) -> Stores {
    Stores { r3: load(s, origin(b)), ..s }
}

pub open spec fn first_stores(b: Branch) -> Stores {
    deliver_to_r3(isolated(), b)
}

pub open spec fn first_quorum(b: Branch) -> Set<Replica> {
    // Requests go to all three. Withhold the reply from the third member.
    Set::empty().insert(origin(b)).insert(Replica::R3)
}

pub open spec fn survivor_quorum() -> Set<Replica> {
    Set::empty().insert(Replica::R1).insert(Replica::R2)
}

// Conditional use of A on the hybrid shared store. The responders' cells
// stay fixed through the sampling interval. Selection and metadata are arbitrary.
pub open spec fn quorum_value(s: Stores, q: Set<Replica>, result: int) -> bool {
    exists|r: Replica| q.contains(r) && #[trigger] load(s, r) == result
}

pub proof fn first_read_values(alpha: int, beta: int)
    requires
        quorum_value(first_stores(Branch::Alpha), first_quorum(Branch::Alpha), alpha),
        quorum_value(first_stores(Branch::Beta), first_quorum(Branch::Beta), beta),
    ensures alpha == 5, beta == 2,
{
    isolated_rmws();
    let a = choose|r: Replica| first_quorum(Branch::Alpha).contains(r)
        && #[trigger] load(first_stores(Branch::Alpha), r) == alpha;
    let b = choose|r: Replica| first_quorum(Branch::Beta).contains(r)
        && #[trigger] load(first_stores(Branch::Beta), r) == beta;
    assert(a == Replica::R2 || a == Replica::R3);
    assert(b == Replica::R1 || b == Replica::R3);
}

// Finite routing abstraction. A direct send of the completed update permits
// its one-hop delivery before any relay or confirmation is delivered.
pub open spec fn can_deliver_first(
    links: spec_fn(Replica, Replica) -> bool, b: Branch,
) -> bool {
    links(origin(b), Replica::R3)
}

pub enum Event {
    InvokeWeak(Replica),
    CompleteWeak(Replica),
    DeliverWeak(Replica, Replica),
    SendRead1(Replica),
    DeliverReply1(Replica),
    FinishRead1,
    Crash(Replica),
    InvokeRead2,
}

// The first client is quiescent after FinishRead1. No weak confirmations
// or extra propagation are delivered. SR2 is invoked by a fresh client.
pub open spec fn prefix(b: Branch) -> Seq<Event> {
    seq![
        Event::InvokeWeak(Replica::R1), Event::InvokeWeak(Replica::R2),
        Event::CompleteWeak(Replica::R1), Event::CompleteWeak(Replica::R2),
        Event::DeliverWeak(origin(b), Replica::R3),
        Event::SendRead1(Replica::R1), Event::SendRead1(Replica::R2),
        Event::SendRead1(Replica::R3),
        Event::DeliverReply1(origin(b)), Event::DeliverReply1(Replica::R3),
        Event::FinishRead1, Event::Crash(Replica::R3), Event::InvokeRead2,
    ]
}

// The projection consists of the continuing clients' and replicas' relevant
// state and pending messages. These cells are its application-state component.
pub open spec fn survivor_cells(s: Stores) -> (int, int) { (s.r1, s.r2) }

pub proof fn both_branches_have_same_survivor_cells()
    ensures
        survivor_cells(first_stores(Branch::Alpha))
        == survivor_cells(first_stores(Branch::Beta)),
{}

// Routing counterexample for the one-delivery premise. Both updates can
// reach R3 in two hops when the other origin acts as a relay.
pub open spec fn relay_only(from: Replica, to: Replica) -> bool {
    (from == Replica::R1 && (to == Replica::R2 || to == Replica::R3))
        || (from == Replica::R2 && to == Replica::R1)
}

pub proof fn eventual_routes_do_not_give_both_one_delivery_prefixes()
    ensures
        relay_only(Replica::R1, Replica::R3),
        relay_only(Replica::R2, Replica::R1) && relay_only(Replica::R1, Replica::R3),
        !can_deliver_first(|from, to| relay_only(from, to), Branch::Alpha),
        can_deliver_first(|from, to| relay_only(from, to), Branch::Beta),
{}

// Arbitrary deterministic continuation, including any number of strong
// messages or rounds. A projection can forget state only if it simulates
// every scheduled step and determines the return value.
pub open spec fn run<S, I>(step: spec_fn(S, I) -> S, s: S, inputs: Seq<I>) -> S
    decreases inputs.len(),
{
    if inputs.len() == 0 { s }
    else { run(step, step(s, inputs[0]), inputs.drop_first()) }
}

pub open spec fn continuation_refines<S, V, I>(
    step: spec_fn(S, I) -> S, view: spec_fn(S) -> V,
    visible_step: spec_fn(V, I) -> V,
) -> bool {
    forall|s: S, input: I| #[trigger] view(step(s, input)) == visible_step(view(s), input)
}

pub proof fn projection_commutes_with_run<S, V, I>(
    step: spec_fn(S, I) -> S, view: spec_fn(S) -> V, visible_step: spec_fn(V, I) -> V,
    s: S, inputs: Seq<I>,
)
    requires continuation_refines(step, view, visible_step),
    ensures view(run(step, s, inputs)) == run(visible_step, view(s), inputs),
    decreases inputs.len(),
{
    reveal(run);
    if inputs.len() != 0 {
        assert(view(step(s, inputs[0])) == visible_step(view(s), inputs[0]));
        projection_commutes_with_run(step, view, visible_step, step(s, inputs[0]),
            inputs.drop_first());
    }
}

// Explicit conditional interface with an arbitrary protocol. The adapters
// establish actual prefix feasibility, hybrid quorum validity/completion,
// and an SR2 projection from the protocol's own transition system.
pub struct ReadRun<S> {
    pub start_sr2: S,
    pub first: int,
    pub second: int,
    pub order: Seq<Op>,
    pub states: Seq<int>,
}

// Each event must be enabled by the protocol transition relation. The
// observation connects the completed first response to this same trace.
pub open spec fn trace_follows<S>(
    transition: spec_fn(S, Event, S) -> bool, events: Seq<Event>, states: Seq<S>,
) -> bool {
    states.len() == events.len() + 1
    && forall|k: int| 0 <= k < events.len() ==>
        transition(states[k], #[trigger] events[k], states[k + 1])
}

pub open spec fn realizes<S>(
    initial_state: S, transition: spec_fn(S, Event, S) -> bool,
    first_response: spec_fn(S) -> Option<int>,
    b: Branch, states: Seq<S>, r: ReadRun<S>,
) -> bool {
    let events = prefix(b);
    trace_follows(transition, events, states)
    && states[0] == initial_state
    && states[events.len() as int] == r.start_sr2
    && first_response(states[11]) == Some(r.first) // Immediately after FinishRead1.
}

pub proof fn conditional_three_replica_hot<S, V, I>(
    initial_state: S, transition: spec_fn(S, Event, S) -> bool,
    first_response: spec_fn(S) -> Option<int>, alpha_trace: Seq<S>, beta_trace: Seq<S>,
    alpha: ReadRun<S>, beta: ReadRun<S>,
    step: spec_fn(S, I) -> S, view: spec_fn(S) -> V, visible_step: spec_fn(V, I) -> V,
    returned: spec_fn(V) -> Option<int>, inputs: Seq<I>,
)
    requires
        realizes(initial_state, transition, first_response, Branch::Alpha, alpha_trace, alpha),
        realizes(initial_state, transition, first_response, Branch::Beta, beta_trace, beta),
        quorum_value(first_stores(Branch::Alpha), first_quorum(Branch::Alpha), alpha.first),
        quorum_value(first_stores(Branch::Beta), first_quorum(Branch::Beta), beta.first),
        continuation_refines(step, view, visible_step),
        view(alpha.start_sr2) == view(beta.start_sr2),
        returned(view(run(step, alpha.start_sr2, inputs))) == Some(alpha.second),
        returned(view(run(step, beta.start_sr2, inputs))) == Some(beta.second),
    ensures
        !legal(alpha.order, alpha.states, alpha.first, alpha.second)
        || !legal(beta.order, beta.states, beta.first, beta.second),
{
    first_read_values(alpha.first, beta.first);
    projection_commutes_with_run(step, view, visible_step, alpha.start_sr2, inputs);
    projection_commutes_with_run(step, view, visible_step, beta.start_sr2, inputs);
    assert(alpha.second == beta.second);
    if legal(alpha.order, alpha.states, alpha.first, alpha.second)
        && legal(beta.order, beta.states, beta.first, beta.second) {
        conditional_history_contradiction(alpha.order, alpha.states, beta.order, beta.states,
            alpha.second);
    }
}


// In the routing abstraction, an unlisted link cannot deliver an update.
// This rules out every alpha milestone trace for every such transition relation.
pub proof fn relay_blocks_alpha_trace<S>(
    transition: spec_fn(S, Event, S) -> bool, states: Seq<S>,
)
    requires
        forall|before: S, after: S, from: Replica, to: Replica|
            #[trigger] transition(before, Event::DeliverWeak(from, to), after)
                ==> relay_only(from, to),
    ensures !trace_follows(transition, prefix(Branch::Alpha), states),
{
    let events = prefix(Branch::Alpha);
    if trace_follows(transition, events, states) {
        assert(4 < events.len());
        assert(events[4] == Event::DeliverWeak(Replica::R2, Replica::R3));
        assert(transition(states[4], events[4], states[5]));
    }
}

// Checked separation: even read-only transitions on the application cells
// and a fixed quorum do not make those cells a sufficient projection.
pub struct ReadFootprint {
    pub stores: Stores,
    pub prefer_r1: bool,
}

pub open spec fn after_reply(b: Branch) -> ReadFootprint {
    ReadFootprint {
        stores: first_stores(b),
        prefer_r1: origin(b) == Replica::R1,
    }
}

pub open spec fn read_with_footprint(s: ReadFootprint) -> int {
    if s.prefer_r1 { s.stores.r1 } else { s.stores.r2 }
}

pub proof fn unchanged_cells_do_not_determine_sr2()
    ensures
        survivor_cells(after_reply(Branch::Alpha).stores)
            == survivor_cells(after_reply(Branch::Beta).stores),
        quorum_value(after_reply(Branch::Alpha).stores, survivor_quorum(),
            read_with_footprint(after_reply(Branch::Alpha))),
        quorum_value(after_reply(Branch::Beta).stores, survivor_quorum(),
            read_with_footprint(after_reply(Branch::Beta))),
        read_with_footprint(after_reply(Branch::Alpha))
            != read_with_footprint(after_reply(Branch::Beta)),
{
    let a = after_reply(Branch::Alpha);
    let b = after_reply(Branch::Beta);
    assert(survivor_quorum().contains(Replica::R2) &&
        load(a.stores, Replica::R2) == read_with_footprint(a));
    assert(survivor_quorum().contains(Replica::R1) &&
        load(b.stores, Replica::R1) == read_with_footprint(b));
}

pub proof fn each_branch_has_a_legal_sequential_history()
    ensures
        legal(seq![Op::W2, Op::SR1, Op::SR2], seq![1int, 5, 5, 5], 5, 5),
        legal(seq![Op::W1, Op::SR1, Op::SR2], seq![1int, 2, 2, 2], 2, 2),
{
    branch_history(Op::W2, 5);
    branch_history(Op::W1, 2);
}

proof fn branch_history(w: Op, value: int)
    requires (w == Op::W1 || w == Op::W2), next(w, 1) == value,
    ensures legal(seq![w, Op::SR1, Op::SR2], seq![1int, value, value, value], value, value),
{
    let ops = seq![w, Op::SR1, Op::SR2];
    let xs = seq![1int, value, value, value];
    assert(ops[1] == Op::SR1 && ops[2] == Op::SR2);
    assert(ops.no_duplicates());
    assert forall|k: int| 0 <= k < ops.len() implies {
        let op = #[trigger] ops[k];
        xs[k + 1] == next(op, xs[k])
        && xs[k] == match op {
            Op::W1 | Op::W2 => 1,
            Op::SR1 | Op::SR2 => value,
        }
    } by {
        assert(k == 0 || k == 1 || k == 2);
    }
}

// Restricted schedule witness. This model exposes a ready direct update
// after local completion, and a read can return from any two replies.
pub struct MilestoneState {
    pub cells: Stores,
    pub pending: Set<Replica>,
    pub completed: Set<Replica>,
    pub sent: Set<Replica>,
    pub replies: Set<Replica>,
    pub first: Option<int>,
    pub r3_crashed: bool,
    pub sr2_invoked: bool,
}

pub open spec fn milestone_initial() -> MilestoneState {
    MilestoneState {
        cells: initial(), pending: Set::empty(), completed: Set::empty(),
        sent: Set::empty(), replies: Set::empty(), first: None,
        r3_crashed: false, sr2_invoked: false,
    }
}

pub open spec fn milestone_step(
    links: spec_fn(Replica, Replica) -> bool, s: MilestoneState, event: Event,
) -> Option<MilestoneState> {
    match event {
        Event::InvokeWeak(r) if r != Replica::R3 =>
            Some(MilestoneState { pending: s.pending.insert(r), ..s }),
        Event::CompleteWeak(r) if s.pending.contains(r) && r != Replica::R3 => {
            let cells = if r == Replica::R1 { local_w1(s.cells).0 }
                else { local_w2(s.cells).0 };
            Some(MilestoneState {
                cells, pending: s.pending.remove(r), completed: s.completed.insert(r), ..s
            })
        },
        Event::DeliverWeak(from, to) if to == Replica::R3
            && s.completed.contains(from) && links(from, to) =>
            Some(MilestoneState { cells: Stores { r3: load(s.cells, from), ..s.cells }, ..s }),
        Event::SendRead1(r) =>
            Some(MilestoneState { sent: s.sent.insert(r), ..s }),
        Event::DeliverReply1(r) if s.sent.contains(r) =>
            Some(MilestoneState { replies: s.replies.insert(r), ..s }),
        Event::FinishRead1 if s.replies.contains(Replica::R3)
            && (s.replies.contains(Replica::R1) || s.replies.contains(Replica::R2)) =>
            Some(MilestoneState { first: Some(s.cells.r3), ..s }),
        Event::Crash(r) if r == Replica::R3 =>
            Some(MilestoneState { r3_crashed: true, ..s }),
        Event::InvokeRead2 if s.r3_crashed && s.first.is_some() =>
            Some(MilestoneState { sr2_invoked: true, ..s }),
        _ => None,
    }
}

pub open spec fn milestone_run(
    links: spec_fn(Replica, Replica) -> bool, s: MilestoneState, events: Seq<Event>,
) -> Seq<MilestoneState>
    decreases events.len(),
{
    if events.len() == 0 {
        seq![s]
    } else {
        match milestone_step(links, s, events[0]) {
            Some(after) => seq![s] + milestone_run(links, after, events.drop_first()),
            None => seq![s],
        }
    }
}

proof fn milestone_run_follows(
    links: spec_fn(Replica, Replica) -> bool, s: MilestoneState, events: Seq<Event>,
)
    ensures
        milestone_run(links, s, events)[0] == s,
        milestone_run(links, s, events).len() == events.len() + 1 ==>
            trace_follows(|before, event, after|
                milestone_step(links, before, event) == Some(after),
                events, milestone_run(links, s, events)),
    decreases events.len(),
{
    if events.len() > 0 {
        if let Some(after) = milestone_step(links, s, events[0]) {
            let rest = events.drop_first();
            milestone_run_follows(links, after, rest);
            let tail = milestone_run(links, after, rest);
            let states = milestone_run(links, s, events);
            if states.len() == events.len() + 1 {
                assert forall|k: int| 0 <= k < events.len() implies
                    milestone_step(links, states[k], #[trigger] events[k])
                        == Some(states[k + 1]) by {
                    if k > 0 {
                        assert(rest[k - 1] == events[k]);
                        assert(tail[k - 1] == states[k]);
                        assert(tail[k] == states[k + 1]);
                        assert(milestone_step(links, tail[k - 1], rest[k - 1])
                            == Some(tail[(k - 1) + 1]));
                    }
                }
            }
        }
    }
}

pub proof fn restricted_prefix_is_feasible(
    links: spec_fn(Replica, Replica) -> bool, b: Branch,
)
    requires can_deliver_first(links, b),
    ensures exists|states: Seq<MilestoneState>|
        trace_follows(|before, event, after|
            milestone_step(links, before, event) == Some(after), prefix(b), states)
        && #[trigger] states[0] == milestone_initial()
        && states[11].replies == first_quorum(b)
        && states[11].cells == first_stores(b)
        && states[11].first == Some(load(first_stores(b), Replica::R3))
        && states[13].r3_crashed && states[13].sr2_invoked
        && survivor_cells(states[13].cells) == survivor_cells(isolated()),
{
    let events = prefix(b);
    let states = milestone_run(links, milestone_initial(), events);
    reveal_with_fuel(milestone_run, 15);
    match b { Branch::Alpha => {}, Branch::Beta => {} }
    assert(states.len() == events.len() + 1);
    milestone_run_follows(links, milestone_initial(), events);
    assert(states[11].replies == first_quorum(b));
    assert(states[11].cells == first_stores(b));
    assert(states[11].first == Some(load(first_stores(b), Replica::R3)));
    assert(states[13].r3_crashed && states[13].sr2_invoked);
    assert(survivor_cells(states[13].cells) == survivor_cells(isolated()));
}

// The intervention keeps the survivor context and scheduled inputs fixed.
// "Observed" labels the weak write from SR1 in the actual history. Swapping
// storage does not change that label. A missing response also fails to
// carry the observed write forward.
pub open spec fn uses_retained_state_to_maintain_order<B, F>(
    resume: spec_fn(B, F) -> Option<int>, context: B, kept: F, replacement: F,
    observed: int,
) -> bool {
    resume(context, kept) == Some(observed)
        && resume(context, replacement) != Some(observed)
}

// A conditional, behavioral reading of T for this workload. Replacements
// are the footprints from the paired real executions. This prohibits a
// particular use of retained strong state, even if its encoding is opaque.
pub open spec fn transparent_on_pair<B, F>(
    resume: spec_fn(B, F) -> Option<int>, context: B,
    alpha: F, beta: F, observed_alpha: int, observed_beta: int,
) -> bool {
    !uses_retained_state_to_maintain_order(resume, context, alpha, beta, observed_alpha)
    && !uses_retained_state_to_maintain_order(resume, context, beta, alpha, observed_beta)
}

pub open spec fn scheduled_response<B, F, I>(
    step: spec_fn((B, F), I) -> (B, F),
    returned: spec_fn((B, F)) -> Option<int>, inputs: Seq<I>,
    context: B, footprint: F,
) -> Option<int> {
    returned(run(step, (context, footprint), inputs))
}

// The continuation can examine and update both components without any
// commuting projection. The caller justifies that B contains all other
// SR2-accessible state and F contains only prior strong-path information.
pub proof fn h_requires_retained_ordering<B, F, I>(
    alpha: ReadRun<(B, F)>, beta: ReadRun<(B, F)>,
    step: spec_fn((B, F), I) -> (B, F),
    returned: spec_fn((B, F)) -> Option<int>, inputs: Seq<I>,
)
    requires
        alpha.start_sr2.0 == beta.start_sr2.0,
        quorum_value(first_stores(Branch::Alpha), first_quorum(Branch::Alpha), alpha.first),
        quorum_value(first_stores(Branch::Beta), first_quorum(Branch::Beta), beta.first),
        returned(run(step, alpha.start_sr2, inputs)) == Some(alpha.second),
        returned(run(step, beta.start_sr2, inputs)) == Some(beta.second),
        legal(alpha.order, alpha.states, alpha.first, alpha.second),
        legal(beta.order, beta.states, beta.first, beta.second),
    ensures ({
        let resume = |context: B, footprint: F|
            scheduled_response(step, returned, inputs, context, footprint);
        let (context, a) = alpha.start_sr2;
        let b = beta.start_sr2.1;
        a != b
            && uses_retained_state_to_maintain_order(resume, context, a, b, alpha.first)
            && uses_retained_state_to_maintain_order(resume, context, b, a, beta.first)
    }),
{
    first_read_values(alpha.first, beta.first);
    legal_history_keeps_first_read(alpha.order, alpha.states, alpha.first, alpha.second);
    legal_history_keeps_first_read(beta.order, beta.states, beta.first, beta.second);
    assert((alpha.start_sr2.0, alpha.start_sr2.1) == alpha.start_sr2);
    assert((alpha.start_sr2.0, beta.start_sr2.1) == beta.start_sr2);
}

// The adapter exposes the local network execution and the actual read
// sampling interval of a protocol trace. Its footprint may also contain
// strong messages. Auditing their provenance is a separate obligation.
pub struct LocalPrefix<L, I> {
    pub states: Seq<delivery::Network<L, I>>,
    pub actions: Seq<delivery::Action<I>>,
    pub samples: Seq<Stores>,
}

pub open spec fn post_crash_entry<L, I>(prefix: LocalPrefix<L, I>) -> bool {
    let end = prefix.states[prefix.actions.len() as int];
    end.first_stopped && end.r3_crashed && end.second_started && end.unavailable.is_none()
}

pub open spec fn sample_window(window: Seq<Stores>, b: Branch, result: int) -> bool {
    let q = first_quorum(b);
    delivery::sampled(window, q, result)
        && forall|i: int, r: Replica| 0 <= i < window.len() && q.contains(r)
            ==> #[trigger] load(window[i], r) == load(first_stores(b), Replica::R3)
}

pub open spec fn carries_writer(decision: Option<int>, written: int) -> bool {
    decision == Some(written)
}

pub proof fn effect_policy_derives_pair_test<B, F>(
    resume: spec_fn(B, F) -> Option<int>,
    effects: spec_fn(B, F) -> Set<transparency::StrongEffect<int>>,
    eligible: spec_fn(B, F, F, int) -> bool,
    context: B, a: F, b: F, wa: int, wb: int,
)
    requires
        transparency::reports_retained_order(
            resume, effects, |decision, written| carries_writer(decision, written), eligible),
        eligible(context, a, b, wa), eligible(context, b, a, wb),
        transparency::effects_transparent(effects(context, a)),
        transparency::effects_transparent(effects(context, b)),
    ensures transparent_on_pair(resume, context, a, b, wa, wb),
{
    if resume(context, a) == Some(wa) {
        transparency::transparent_effects_exclude_retained_order(
            resume, effects, |decision, written| carries_writer(decision, written), eligible,
            context, a, b, wa);
    }
    if resume(context, b) == Some(wb) {
        transparency::transparent_effects_exclude_retained_order(
            resume, effects, |decision, written| carries_writer(decision, written), eligible,
            context, b, a, wb);
    }
}

pub open spec fn order_semantics_for_read<B, F, I>(
    step: spec_fn((B, F), I) -> (B, F),
    returned: spec_fn((B, F)) -> Option<int>, inputs: Seq<I>,
    eligible: spec_fn(B, F, F, int) -> bool,
    before_sr1: spec_fn(B, int) -> transparency::OrderOrigin,
) -> transparency::OrderSemantics<B, F, Option<int>, int> {
    transparency::OrderSemantics {
        resume: |context, footprint| scheduled_response(step, returned, inputs, context, footprint),
        maintains: |decision, written| carries_writer(decision, written),
        eligible,
        before_sr1,
    }
}

// A recovered order preserves the recorded input of every included
// weak RMW. No response from SR1 or SR2 is required of this reconstruction.
pub struct RecoveredOrder {
    pub ops: Seq<Op>,
    pub states: Seq<int>,
}

pub open spec fn legal_recovery(r: RecoveredOrder) -> bool {
    r.states.len() == r.ops.len() + 1 && r.states[0] == 1
    && forall|i: int| 0 <= i < r.ops.len() ==> {
        let op = #[trigger] r.ops[i];
        r.states[i + 1] == next(op, r.states[i])
        && (op == Op::W1 || op == Op::W2 ==> r.states[i] == 1)
    }
}

pub proof fn recovered_order_cannot_keep_both_rmws(r: RecoveredOrder)
    requires legal_recovery(r), r.ops.contains(Op::W1), r.ops.contains(Op::W2),
    ensures false,
{
    let a = choose|i: int| 0 <= i < r.ops.len() && #[trigger] r.ops[i] == Op::W1;
    let b = choose|i: int| 0 <= i < r.ops.len() && #[trigger] r.ops[i] == Op::W2;
    let (i, j) = if a < b { (a, b) } else { (b, a) };
    assert(r.states[i] == 1 && r.states[j] == 1);
    assert(r.states[i + 1] == next(r.ops[i], r.states[i]));
    state_range(r.ops, r.states, i + 1, j);
}

// Both stable writes are guaranteed to be recoverable from the actual
// weak survivor view. The recovery function includes any pending weak
// evidence available to it through that view and its fixed inputs.
pub open spec fn stable_recovery_pair<B>(
    recover: spec_fn(B) -> RecoveredOrder, a: B, b: B,
) -> bool {
    legal_recovery(recover(a))
        && recover(a).ops.contains(Op::W2)
        && recover(b).ops.contains(Op::W1)
}

pub proof fn both_g_requires_distinguishable_weak_recovery<B>(
    recover: spec_fn(B) -> RecoveredOrder, a: B, b: B,
)
    requires stable_recovery_pair(recover, a, b),
    ensures a != b,
{
    if a == b {
        recovered_order_cannot_keep_both_rmws(recover(a));
    }
}

// This interface is about actual SR2 selection observations and the
// protocol's deterministic read rule, irrespective of unused metadata.
pub open spec fn matching_read_observations<B, V, I>(
    step: spec_fn(B, I) -> B, returned: spec_fn(B) -> Option<int>, inputs: Seq<I>,
    observe: spec_fn(B) -> V, select: spec_fn(V) -> int, a: ReadRun<B>, b: ReadRun<B>,
) -> bool {
    observe(a.start_sr2) == observe(b.start_sr2)
        && returned(run(step, a.start_sr2, inputs)) == Some(select(observe(a.start_sr2)))
        && returned(run(step, b.start_sr2, inputs)) == Some(select(observe(b.start_sr2)))
        && returned(run(step, a.start_sr2, inputs)) == Some(a.second)
        && returned(run(step, b.start_sr2, inputs)) == Some(b.second)
}

// Conditional on a local-network adapter and semantic transparency. The
// original milestone traces certify actual completion; the local traces
// account for traffic rather than assuming a protocol-wide frame.
pub proof fn conditional_hot_with_local_delivery<L, P, F, I, V>(
    initial_state: ((L, L), F),
    transition: spec_fn(((L, L), F), Event, ((L, L), F)) -> bool,
    first_response: spec_fn(((L, L), F)) -> Option<int>,
    alpha_trace: Seq<((L, L), F)>, beta_trace: Seq<((L, L), F)>,
    public_alpha: LocalPrefix<L, P>, public_beta: LocalPrefix<L, P>,
    plan: Seq<delivery::Move>, fork: int,
    update: spec_fn(L, P) -> L,
    alpha: ReadRun<((L, L), F)>, beta: ReadRun<((L, L), F)>,
    step: spec_fn(((L, L), F), I) -> ((L, L), F),
    returned: spec_fn(((L, L), F)) -> Option<int>, inputs: Seq<I>,
    direction: Branch,
    histories: Set<((L, L), F, int)>,
    direct: Set<transparency::StrongEffect<int>>,
    eligible: spec_fn((L, L), F, F, int) -> bool,
    before_sr1: spec_fn((L, L), int) -> transparency::OrderOrigin,
    recover: spec_fn((L, L)) -> RecoveredOrder,
    observe_ordered_read: spec_fn(((L, L), F)) -> V,
    select_ordered_read: spec_fn(V) -> int,
)
    requires
        realizes(initial_state, transition, first_response, Branch::Alpha, alpha_trace, alpha),
        realizes(initial_state, transition, first_response, Branch::Beta, beta_trace, beta),
        delivery::trace(update, public_alpha.states, public_alpha.actions),
        delivery::trace(update, public_beta.states, public_beta.actions),
        post_crash_entry(public_alpha), post_crash_entry(public_beta),
        delivery::survivor(public_alpha.states[0]) == delivery::survivor(public_beta.states[0]),
        alpha.start_sr2.0 == delivery::survivor(
            public_alpha.states[public_alpha.actions.len() as int]),
        beta.start_sr2.0 == delivery::survivor(
            public_beta.states[public_beta.actions.len() as int]),
        delivery::valid_schedule(public_alpha.states, public_alpha.actions, 0,
            public_beta.states, public_beta.actions, 0, plan)
        || delivery::shared_prefix_then_quiet(public_alpha.states, public_alpha.actions,
            public_beta.states, public_beta.actions, fork)
        || matching_read_observations(step, returned, inputs,
            observe_ordered_read, select_ordered_read, alpha, beta),
        sample_window(public_alpha.samples, Branch::Alpha, alpha.first),
        sample_window(public_beta.samples, Branch::Beta, beta.first),
        matching_read_observations(step, returned, inputs,
            observe_ordered_read, select_ordered_read, alpha, beta)
        || (before_sr1(alpha.start_sr2.0, alpha.first) == transparency::OrderOrigin::WeakG
            && before_sr1(beta.start_sr2.0, beta.first) == transparency::OrderOrigin::WeakG
            && stable_recovery_pair(recover, alpha.start_sr2.0, beta.start_sr2.0))
        || ({
            let actual = match direction { Branch::Alpha => alpha, Branch::Beta => beta };
            let other = match direction { Branch::Alpha => beta, Branch::Beta => alpha };
            let (context, footprint) = actual.start_sr2;
            before_sr1(context, actual.first) != transparency::OrderOrigin::WeakG
            && returned(run(step, alpha.start_sr2, inputs)) == Some(alpha.second)
            && returned(run(step, beta.start_sr2, inputs)) == Some(beta.second)
            && transparency::semantic_transparent(transparency::semantic_effects(
                order_semantics_for_read(step, returned, inputs, eligible, before_sr1), direct,
                context, footprint))
            && (eligible(context, footprint, other.start_sr2.1, actual.first)
                || (eligible == (|c, f, g, w| transparency::real_trace_alternative(histories, c, f, g, w))
                    && histories.contains((context, footprint, actual.first))
                    && histories.contains((other.start_sr2.0, other.start_sr2.1, other.first))))
        }),
    ensures
        !legal(alpha.order, alpha.states, alpha.first, alpha.second)
        || !legal(beta.order, beta.states, beta.first, beta.second),
{
    if legal(alpha.order, alpha.states, alpha.first, alpha.second)
        && legal(beta.order, beta.states, beta.first, beta.second) {
        delivery::stable_quorum_sample(public_alpha.samples, first_quorum(Branch::Alpha),
            alpha.first, load(first_stores(Branch::Alpha), Replica::R3));
        delivery::stable_quorum_sample(public_beta.samples, first_quorum(Branch::Beta),
            beta.first, load(first_stores(Branch::Beta), Replica::R3));
        assert(alpha.first == 5 && beta.first == 2);
        if matching_read_observations(step, returned, inputs,
            observe_ordered_read, select_ordered_read, alpha, beta) {
            assert(alpha.second == beta.second);
            conditional_history_contradiction(alpha.order, alpha.states,
                beta.order, beta.states, alpha.second);
            return;
        }
        if delivery::valid_schedule(public_alpha.states, public_alpha.actions, 0,
            public_beta.states, public_beta.actions, 0, plan) {
            delivery::survivor_context_from_schedule(update,
                public_alpha.states, public_alpha.actions, 0,
                public_beta.states, public_beta.actions, 0, plan);
        } else {
            delivery::survivor_context_after_quiet_fork(update,
                public_alpha.states, public_alpha.actions,
                public_beta.states, public_beta.actions, fork);
        }
        if before_sr1(alpha.start_sr2.0, alpha.first) == transparency::OrderOrigin::WeakG
            && before_sr1(beta.start_sr2.0, beta.first) == transparency::OrderOrigin::WeakG {
            both_g_requires_distinguishable_weak_recovery(recover,
                alpha.start_sr2.0, beta.start_sr2.0);
            return;
        }
        legal_history_keeps_first_read(alpha.order, alpha.states, alpha.first, alpha.second);
        legal_history_keeps_first_read(beta.order, beta.states, beta.first, beta.second);
        let actual = match direction { Branch::Alpha => alpha, Branch::Beta => beta };
        let other = match direction { Branch::Alpha => beta, Branch::Beta => alpha };
        let (context, footprint) = actual.start_sr2;
        assert((context, other.start_sr2.1) == other.start_sr2);
        if !eligible(context, footprint, other.start_sr2.1, actual.first) {
            transparency::real_trace_alternative_from_actual_runs(
                histories, context, footprint, other.start_sr2.1, actual.first, other.first);
        }
        transparency::semantic_policy_guards_order(
            order_semantics_for_read(step, returned, inputs, eligible, before_sr1), direct,
            context, footprint, other.start_sr2.1, actual.first,
        );
    }
}

// Abstract selector test with a supplied source preference. A reversed
// choice distinguishes the branches and violates H in both.
pub open spec fn reversed_selector(context: (int, int), prefer_r1: bool) -> Option<int> {
    Some(if prefer_r1 { context.1 } else { context.0 })
}

pub proof fn different_results_can_pass_the_ordering_use_test()
    ensures
        reversed_selector((2, 5), false) == Some(2),
        reversed_selector((2, 5), true) == Some(5),
        transparent_on_pair(|cells, flag| reversed_selector(cells, flag),
            (2int, 5int), false, true, 5, 2),
{}

pub proof fn using_a_version_hint_for_correct_order_fails_the_pair_test()
    ensures
        !transparent_on_pair(
            |cells: (int, int), flag: bool| Some(if flag { cells.0 } else { cells.1 }),
            (2int, 5int), false, true, 5, 2,
        ),
{}

pub proof fn reversed_results_violate_h(
    alpha: Seq<Op>, ax: Seq<int>, beta: Seq<Op>, bx: Seq<int>,
)
    ensures
        !legal(alpha, ax, 5, 2),
        !legal(beta, bx, 2, 5),
{
    if legal(alpha, ax, 5, 2) {
        legal_history_keeps_first_read(alpha, ax, 5, 2);
    }
    if legal(beta, bx, 2, 5) {
        legal_history_keeps_first_read(beta, bx, 2, 5);
    }
}

}

pub mod original_application;
pub mod native_fork;
pub mod envelope_names;
pub mod async_messages;
pub mod async_fork;
pub mod semantic_promotion;
pub mod operation_history;
pub mod register_history;
pub mod weak_construction;
pub mod weak_visibility;

pub mod prepared_service;
pub mod prepared_hot;
pub mod background_replication;
pub mod weak_cut_service;

pub mod async_weak;
