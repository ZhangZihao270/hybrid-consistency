use vstd::prelude::*;
use crate::delivery::*;
use crate::transparency::*;
use crate::{Op, Replica, RecoveredOrder, legal, legal_recovery,
    both_g_requires_distinguishable_weak_recovery, stable_recovery_pair};

verus! {

pub struct GHistory {
    pub order: Seq<Op>,
    pub states: Seq<int>,
    pub first: int,
    pub second: int,
    pub replicas: spec_fn(Op) -> Set<Replica>,
}

// G records membership in the total order and replication of the
// operation. It does not say which replica encodes the order position.
pub open spec fn ordered_on_majority(order: Seq<Op>, copies: Set<Replica>, w: Op) -> bool {
    order.contains(w) && copies.len() >= 2
}

pub open spec fn at_g(h: GHistory, w: Op) -> bool {
    ordered_on_majority(h.order, (h.replicas)(w), w)
}

pub open spec fn h_with_g(h: GHistory, w: Op) -> bool {
    legal(h.order, h.states, h.first, h.second) && at_g(h, w)
}

pub proof fn a_copy_of_a_g_operation_survives_r3(h: GHistory, w: Op)
    requires at_g(h, w),
    ensures (h.replicas)(w).contains(Replica::R1) || (h.replicas)(w).contains(Replica::R2),
{
    let copies = (h.replicas)(w);
    if !copies.contains(Replica::R1) && !copies.contains(Replica::R2) {
        if copies.contains(Replica::R3) {
            assert(copies =~= Set::empty().insert(Replica::R3));
        } else {
            assert(copies =~= Set::empty());
        }
    }
}

pub open spec fn written(b: bool) -> Op {
    if b { Op::W1 } else { Op::W2 }
}

pub open spec fn value(b: bool) -> int {
    if b { 2 } else { 5 }
}

pub open spec fn g_fixture(b: bool) -> GHistory {
    GHistory {
        order: seq![written(b), Op::SR1, Op::SR2],
        states: seq![1int, value(b), value(b), value(b)],
        first: value(b), second: value(b),
        replicas: |w: Op| if w == written(b) {
            Set::empty().insert(Replica::R3).insert(if b { Replica::R1 } else { Replica::R2 })
        } else { Set::empty() },
    }
}

// An algebraic recovery fixture supplies an independent order hint as
// input. It specifies no transport or client-to-replica dissemination.
// The checkpoint proof separately derives what is actually observable.
pub struct RecoveryView {
    pub weak_cells: (int, int),
    pub weak_pending: Seq<Op>,
    pub order_hint: bool,
}

pub open spec fn fixture_view(beta: bool) -> RecoveryView {
    RecoveryView { weak_cells: (2, 5), weak_pending: Seq::empty(), order_hint: beta }
}

pub open spec fn reconstruct(v: RecoveryView) -> RecoveredOrder {
    let h = g_fixture(v.order_hint);
    RecoveredOrder { ops: h.order, states: h.states }
}

pub proof fn full_view_recovery_does_not_imply_weak_view_recovery()
    ensures
        h_with_g(g_fixture(false), Op::W2),
        h_with_g(g_fixture(true), Op::W1),
        stable_recovery_pair(|v| reconstruct(v), fixture_view(false), fixture_view(true)),
        fixture_view(false).weak_cells == fixture_view(true).weak_cells,
        fixture_view(false).weak_pending == fixture_view(true).weak_pending,
        forall|recover: spec_fn(((int, int), Seq<Op>)) -> RecoveredOrder|
            !#[trigger] stable_recovery_pair(recover,
                (fixture_view(false).weak_cells, fixture_view(false).weak_pending),
                (fixture_view(true).weak_cells, fixture_view(true).weak_pending)),
{
    crate::each_branch_has_a_legal_sequential_history();
    assert(g_fixture(false).order.contains(Op::W2));
    assert(g_fixture(true).order.contains(Op::W1));
    assert(g_fixture(false).order[0] == Op::W2 && g_fixture(true).order[0] == Op::W1);
    assert((g_fixture(false).replicas)(Op::W2).len() == 2);
    assert((g_fixture(true).replicas)(Op::W1).len() == 2);
    assert(legal_recovery(reconstruct(fixture_view(false))));
    let common = (fixture_view(false).weak_cells, fixture_view(false).weak_pending);
    assert forall|recover: spec_fn(((int, int), Seq<Op>)) -> RecoveredOrder|
        !#[trigger] stable_recovery_pair(recover,
            (fixture_view(false).weak_cells, fixture_view(false).weak_pending),
            (fixture_view(true).weak_cells, fixture_view(true).weak_pending)) by {
        if stable_recovery_pair(recover, common, common) {
            both_g_requires_distinguishable_weak_recovery(recover, common, common);
        }
    }
}

pub open spec fn stable_record_reader(actual_beta: bool) -> OrderSemantics<(int, int), bool, int, int> {
    OrderSemantics {
        resume: |cells: (int, int), beta: bool| if beta { cells.0 } else { cells.1 },
        maintains: |output: int, writer: int| output == writer,
        eligible: |cells: (int, int), actual: bool, alternate: bool, writer: int| true,
        before_sr1: |cells: (int, int), writer: int|
            if writer == value(actual_beta) { OrderOrigin::WeakG }
            else { OrderOrigin::Unordered },
    }
}

// The tag in this semantic test represents already-established order
// in each actual branch. It is not a claim about which writes can both
// be ordered in a single execution, or about a promotion protocol.
pub proof fn already_stable_read_can_use_distinguishing_order_observation(beta: bool)
    ensures
        (stable_record_reader(beta).resume)((2int, 5int), beta) == value(beta),
        semantic_transparent(semantic_effects(stable_record_reader(beta),
            Set::empty().insert(StrongEffect::StrongOnly), (2int, 5int), beta)),
{
    let m = stable_record_reader(beta);
    let effects = semantic_effects(m, Set::empty().insert(StrongEffect::StrongOnly),
        (2int, 5int), beta);
    assert forall|e: StrongEffect<int>| #[trigger] effects(e) implies permitted(e) by {
        match e {
            StrongEffect::MaintainWeak(w) => {
                if w == value(beta) {
                    assert((m.before_sr1)((2int, 5int), w) == OrderOrigin::WeakG);
                }
            },
            _ => {},
        }
    }
}

pub open spec fn with_order_packet(w: Op) -> Network<(int, int), Op> {
    Network {
        locals: |r: Replica| (2int, 5int),
        pending: Map::empty().insert(0nat, Packet {
            path: Path::Weak, from: Process::At(Replica::R3), to: Process::At(Replica::R1), input: w,
        }),
        first_stopped: true, r3_crashed: false, second_started: false, unavailable: None,
    }
}

// A delivery outside the finite window can restore order evidence but
// does not establish that evidence was observable inside the window.
pub proof fn queued_order_evidence_survives_the_sender_crash()
    ensures ({
        let unchanged = |s: (int, int), packet: Op| s;
        let a = advance(unchanged, with_order_packet(Op::W2), Action::CrashR3);
        let b = advance(unchanged, with_order_packet(Op::W1), Action::CrashR3);
        a.r3_crashed && b.r3_crashed && survivor(a) == survivor(b)
            && enabled(a, Action::Deliver(0)) && enabled(b, Action::Deliver(0))
            && weak_at(a, 0) != weak_at(b, 0)
    }),
{}

pub open spec fn order_evidence_in_flight(w: Op) -> Network<(int, Option<Op>), Op> {
    let queue = with_order_packet(w);
    Network {
        locals: |r: Replica| (if r == Replica::R1 { 2int } else { 5int }, None),
        pending: queue.pending, first_stopped: queue.first_stopped, r3_crashed: queue.r3_crashed,
        second_started: queue.second_started, unavailable: queue.unavailable,
    }
}

pub open spec fn install_order_notice(s: (int, Option<Op>), w: Op) -> (int, Option<Op>) {
    (s.0, Some(w))
}

// An issued weak-path notice makes the prior order recoverable through
// delivery to a live survivor, even if the finite read window excludes it.
// Only the already-selected operation is decoded here.
pub proof fn eventual_single_order_can_be_recovered_after_finite_delay()
    ensures ({
        let update = |state, w| install_order_notice(state, w);
        let a = advance(update, order_evidence_in_flight(Op::W2), Action::CrashR3);
        let b = advance(update, order_evidence_in_flight(Op::W1), Action::CrashR3);
        let delivered = Action::Deliver(0);
        let ax = advance(update, a, delivered);
        let bx = advance(update, b, delivered);
        survivor(a) == survivor(b)
            && enabled(a, delivered) && enabled(b, delivered)
            && (ax.locals)(Replica::R1) == (2int, Some(Op::W2))
            && (bx.locals)(Replica::R1) == (2int, Some(Op::W1))
            && ax.r3_crashed && bx.r3_crashed
    }),
{}

}
