// Backwards from the two histories to the independent caller's actual inputs.
use vstd::prelude::*;
use crate::{Op, checkpoint::*};

verus! {

pub open spec fn rival(w: Op) -> Op { if w == Op::W1 { Op::W2 } else { Op::W1 } }

pub open spec fn writer_before_reads(ops: Seq<Op>, w: Op) -> bool {
    !ops.contains(rival(w)) && exists|p: int, i: int, j: int| 0 <= p < i < j < ops.len()
        && #[trigger] ops[p] == w && #[trigger] ops[i] == Op::SR1 && #[trigger] ops[j] == Op::SR2
}

pub proof fn h_fixes_writer_and_value(b: Fork, ops: Seq<Op>, xs: Seq<int>, v: int)
    requires crate::legal(ops, xs, first_value(b), v),
    ensures v == first_value(b), writer_before_reads(ops, observed_writer(b)),
{
    let f = first_value(b);
    let w = observed_writer(b);
    crate::legal_history_keeps_first_read(ops, xs, f, v);
    crate::first_read_includes_its_writer(ops, xs, f, v);
    let (p, i) = choose|p: int, i: int| 0 <= p < i < ops.len() && #[trigger] ops[i] == Op::SR1
        && ((#[trigger] ops[p] == Op::W1 && f == 2) || (ops[p] == Op::W2 && f == 5));
    let (h, j) = choose|h: int, j: int| 0 <= h < j < ops.len()
        && #[trigger] ops[h] == Op::SR1 && #[trigger] ops[j] == Op::SR2;
    assert(i == h);
    if ops.contains(rival(w)) {
        let r = choose|r: int| 0 <= r < ops.len() && ops[r] == rival(w);
        if r < p { crate::conflicting_rmws_cannot_both_appear(ops, xs, f, v, r, p); }
        else { crate::conflicting_rmws_cannot_both_appear(ops, xs, f, v, p, r); }
    }
}

}
