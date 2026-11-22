// The order justified at SR1 and the additional read-from obligation at SR2.
use vstd::prelude::*;
use crate::{Op, RecoveredOrder, legal, legal_recovery, next};
use crate::checkpoint::{Fork, first_value, observed_writer};
use crate::information_flow as flow;

verus! {

pub open spec fn weak(op: Op) -> bool { op == Op::W1 || op == Op::W2 }

pub open spec fn before(order: Seq<Op>, a: Op, b: Op) -> bool {
    exists|i: int, j: int| 0 <= i < j < order.len() && #[trigger] order[i] == a && #[trigger] order[j] == b
}

// Read-from in the sequential register means the last preceding writer.
pub open spec fn reads_from(order: Seq<Op>, read: Op, writer: Op) -> bool {
    weak(writer) && exists|i: int, j: int| 0 <= i < j < order.len()
        && #[trigger] order[i] == writer && #[trigger] order[j] == read
        && forall|k: int| i < k < j ==> !weak(#[trigger] order[k])
}

// This definition can be evaluated when C1 has returned and C2 has never
// run. Other completed weak calls may be included if their responses fit.
pub open spec fn legal_first(h: RecoveredOrder, value: int) -> bool {
    legal_recovery(h) && h.ops.no_duplicates() && h.ops.contains(Op::SR1) && !h.ops.contains(Op::SR2)
        && forall|i: int| 0 <= i < h.ops.len() && #[trigger] h.ops[i] == Op::SR1 ==> h.states[i] == value
}

pub open spec fn at_first(b: Fork) -> RecoveredOrder {
    let v = first_value(b);
    RecoveredOrder { ops: seq![observed_writer(b), Op::SR1], states: seq![1int, v, v] }
}

pub open spec fn at_second(b: Fork) -> RecoveredOrder {
    let h = at_first(b);
    RecoveredOrder { ops: h.ops.push(Op::SR2), states: h.states.push(first_value(b)) }
}

pub proof fn canonical_orders_exist(b: Fork)
    ensures legal_first(at_first(b), first_value(b)),
        legal(at_second(b).ops, at_second(b).states, first_value(b), first_value(b)),
{
    let h = at_first(b); let g = at_second(b); let v = first_value(b);
    assert(h.ops.contains(Op::SR1) && g.ops[1] == Op::SR1 && g.ops[2] == Op::SR2);
    assert forall|k: int| 0 <= k < 3 implies {
        let op = #[trigger] g.ops[k];
        g.states[k + 1] == next(op, g.states[k]) && g.states[k] == (if weak(op) { 1 } else { v })
    } by { assert(k == 0 || k == 1 || k == 2); }
}

pub proof fn exact_completed_order(b: Fork, h: RecoveredOrder, value: int)
    requires legal(h.ops, h.states, first_value(b), value),
    ensures h == at_second(b), value == first_value(b),
{
    let ops = h.ops; let w = observed_writer(b);
    flow::h_fixes_writer_and_value(b, ops, h.states, value);
    let (p,i,j) = choose|p: int, i: int, j: int| 0 <= p < i < j < ops.len()
        && #[trigger] ops[p] == w && #[trigger] ops[i] == Op::SR1 && #[trigger] ops[j] == Op::SR2;
    assert forall|k: int| 0 <= k < ops.len() implies match #[trigger] ops[k] {
        Op::SR1 => k == i, Op::SR2 => k == j, _ => k == p,
    } by {
        if ops[k] == flow::rival(w) { assert(ops.contains(flow::rival(w))); }
    }
    assert(ops[0] == w && p == 0);
    assert(ops[1] == Op::SR1 && i == 1);
    assert(ops[2] == Op::SR2 && j == 2);
    if ops.len() > 3 { assert(ops[3] != w && ops[3] != Op::SR1 && ops[3] != Op::SR2); }
    assert(ops =~= at_second(b).ops);
    assert(h.states[1] == next(w, h.states[0]));
    assert(h.states[2] == next(Op::SR1, h.states[1]));
    assert(h.states[3] == next(Op::SR2, h.states[2]));
    assert(h.states =~= at_second(b).states);
}

// Append a mathematical identity read to characterize the SR1 prefix.
// This is an algebraic argument about the register, with no physical SR2
// completion or future compatibility requirement on the prefix.
pub proof fn exact_first_order(b: Fork, h: RecoveredOrder)
    requires legal_first(h, first_value(b)),
    ensures h == at_first(b),
{
    let n = h.ops.len(); let v = h.states.last();
    let g = RecoveredOrder { ops: h.ops.push(Op::SR2), states: h.states.push(v) };
    let i = choose|i: int| 0 <= i < n && h.ops[i] == Op::SR1;
    assert(g.ops[i] == Op::SR1 && g.ops[n as int] == Op::SR2);
    assert(g.ops.no_duplicates()) by {
        assert forall|a: int, d: int| 0 <= a < d < g.ops.len() implies #[trigger] g.ops[a] != #[trigger] g.ops[d] by {
            if d == n && h.ops[a] == Op::SR2 { assert(h.ops.contains(Op::SR2)); }
        }
    }
    assert forall|k: int| 0 <= k < g.ops.len() implies {
        let op = #[trigger] g.ops[k];
        g.states[k + 1] == next(op, g.states[k])
            && g.states[k] == match op { Op::W1 | Op::W2 => 1, Op::SR1 => first_value(b), Op::SR2 => v }
    } by {
        if k < n {
            assert(h.states[k + 1] == next(h.ops[k], h.states[k]));
            if h.ops[k] == Op::SR2 { assert(h.ops.contains(Op::SR2)); }
        }
    }
    exact_completed_order(b, g, v);
    assert(h.ops =~= at_first(b).ops && h.states =~= at_first(b).states);
}

// Keep membership and every previously observed order edge. Allow other
// operations anywhere in the new order if their recorded RMWs are legal.
pub open spec fn restricts_to(old: Seq<Op>, full: Seq<Op>) -> bool {
    (forall|op: Op| #[trigger] old.contains(op) ==> full.contains(op))
    && (forall|a: Op, b: Op| #[trigger] before(old, a, b) ==> before(full, a, b))
}

pub open spec fn extension(old: Seq<Op>, writer: Op, source2: Op, full: RecoveredOrder) -> bool {
    legal_recovery(full) && full.ops.no_duplicates() && restricts_to(old, full.ops)
        && reads_from(old, Op::SR1, writer) && reads_from(full.ops, Op::SR1, writer)
        && before(full.ops, Op::SR1, Op::SR2) && reads_from(full.ops, Op::SR2, source2)
}

// History compatibility consumes only operation identities and the weak
// commands' recorded preconditions. It has no argument for either strong
// return value, a preferred member, an effect label or another execution.
pub open spec fn can_keep(old: Seq<Op>, writer: Op, source2: Op) -> bool {
    exists|full: RecoveredOrder| #[trigger] extension(old, writer, source2, full)
}

proof fn reader_includes_writer(order: Seq<Op>, r: Op, w: Op)
    requires reads_from(order, r, w),
    ensures order.contains(w), before(order, w, r),
{
    let (i, j) = choose|i: int, j: int| 0 <= i < j < order.len()
        && #[trigger] order[i] == w && #[trigger] order[j] == r
        && forall|k: int| i < k < j ==> !weak(#[trigger] order[k]);
}

pub open spec fn same_weak_order(a: Seq<Op>, d: Seq<Op>) -> bool {
    (forall|w: Op| weak(w) ==> (#[trigger] a.contains(w) == d.contains(w)))
        && (forall|u: Op, v: Op| weak(u) && weak(v) ==> (#[trigger] before(a,u,v) == before(d,u,v)))
}

pub proof fn canonical_extension(b: Fork)
    ensures ({
        let w = observed_writer(b); let p = at_first(b).ops; let g = at_second(b);
        extension(p,w,w,g) && same_weak_order(p,g.ops)
    }),
{
    let w = observed_writer(b); let p = at_first(b).ops; let g = at_second(b);
    canonical_orders_exist(b);
    assert forall|op: Op| #[trigger] p.contains(op) implies g.ops.contains(op) by {
        if op == w {assert(g.ops[0] == op);} else {assert(g.ops[1] == op);}
    }
    assert forall|a: Op, d: Op| #[trigger] before(p, a, d) implies before(g.ops, a, d) by {
        let (i,j) = choose|i: int, j: int| 0 <= i < j < p.len() && #[trigger] p[i] == a && #[trigger] p[j] == d;
        assert(g.ops[i] == a && g.ops[j] == d);
    }
    assert(p[0] == w && p[1] == Op::SR1 && g.ops[0] == w && g.ops[1] == Op::SR1 && g.ops[2] == Op::SR2);
    assert(reads_from(p, Op::SR1, w) && reads_from(g.ops, Op::SR1, w) && reads_from(g.ops, Op::SR2, w));
    assert(extension(p, w, w, g));
    assert forall|u: Op, v: Op| weak(u) && weak(v) implies !#[trigger] before(g.ops,u,v) by {
        if before(g.ops,u,v) {
            let (i,j) = choose|i: int, j: int| 0 <= i < j < g.ops.len() && #[trigger] g.ops[i] == u && #[trigger] g.ops[j] == v;
            assert(j == 1 || j == 2);
        }
    }
}

pub proof fn extension_iff_writer(b: Fork, prefix: RecoveredOrder, source2: Op)
    requires legal_first(prefix, first_value(b)), weak(source2),
    ensures can_keep(prefix.ops, observed_writer(b), source2) == (source2 == observed_writer(b)),
{
    exact_first_order(b, prefix);
    let w = observed_writer(b); let g = at_second(b); let p = prefix.ops;
    if source2 == w {
        canonical_extension(b);
    } else if can_keep(p, w, source2) {
        let full = choose|h: RecoveredOrder| #[trigger] extension(p, w, source2, h);
        reader_includes_writer(full.ops, Op::SR1, w); reader_includes_writer(full.ops, Op::SR2, source2);
        crate::recovered_order_cannot_keep_both_rmws(full);
    }
}

}
