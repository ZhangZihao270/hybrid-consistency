use vstd::prelude::*;
include!("network.rs");
include!("read_service.rs");
include!("strong_model.rs");
include!("history.rs");
include!("weak_replication.rs");
include!("fork_proof.rs");

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

pub open spec fn first_quorum(b: Branch) -> Set<Replica> {
    // Requests go to all three. Withhold the reply from the third member.
    Set::empty().insert(origin(b)).insert(Replica::R3)
}

// Conditional use of A on the hybrid shared store. The responders' cells
// stay fixed through the sampling interval. Selection and metadata are arbitrary.
pub open spec fn quorum_value(s: Stores, q: Set<Replica>, result: int) -> bool {
    exists|r: Replica| q.contains(r) && #[trigger] load(s, r) == result
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

}



pub mod async_weak;
