// The order justified at SR1 and the additional read-from obligation at SR2.
use vstd::prelude::*;
use crate::{Op, RecoveredOrder, legal, legal_recovery, next};
use crate::checkpoint::{Fork, first_value, observed_writer};
use crate::information_flow as flow;
use crate::precedence::{self, Side, at_side};
use crate::read_call::Log;

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

// With actual authenticated sources, testing extension adds no demand
// beyond the necessary sequential clause of H, even on a failed probe.
pub proof fn history_test_is_exact(b: Fork, prefix: RecoveredOrder, source2: Op)
    requires legal_first(prefix,first_value(b)), weak(source2),
    ensures can_keep(prefix.ops,observed_writer(b),source2) == (exists|g: RecoveredOrder|
        #[trigger] legal(g.ops,g.states,first_value(b),next(source2,1))),
{
    extension_iff_writer(b,prefix,source2);
    let w = observed_writer(b); let v = first_value(b);
    if source2 == w {
        canonical_orders_exist(b);
        assert(legal(at_second(b).ops,at_second(b).states,v,next(source2,1)));
    } else if exists|g: RecoveredOrder| #[trigger] legal(g.ops,g.states,v,next(source2,1)) {
        let g = choose|g: RecoveredOrder| #[trigger] legal(g.ops,g.states,v,next(source2,1));
        exact_completed_order(b,g,next(source2,1));
    }
}

// In particular, adding the transitive edge from the first writer to SR2
// never needs the cache. The direct read-from obligation provides the test.
pub proof fn transitive_edge(old: Seq<Op>, full: Seq<Op>, w: Op)
    requires before(old, w, Op::SR1), restricts_to(old, full),
        full.no_duplicates(), before(full, Op::SR1, Op::SR2),
    ensures before(full, w, Op::SR2),
{
    assert(before(full, w, Op::SR1));
    let (p,i) = choose|p: int, i: int| 0 <= p < i < full.len() && #[trigger] full[p] == w && #[trigger] full[i] == Op::SR1;
    let (j,k) = choose|j: int, k: int| 0 <= j < k < full.len() && #[trigger] full[j] == Op::SR1 && #[trigger] full[k] == Op::SR2;
    assert(i == j);
}

// A functional reading of the paper's preservation clause: at an eligible
// causal comparison, a record derived from w may newly enable extension of
// w's independently fixed history only with independent order support.
// Eligibility concerns the two physical executions, not their legality or
// the success of the intervention.
pub open spec fn history_clause<E,I>(
    prefix: Seq<Op>, steps: Seq<E>, origin: spec_fn(E) -> Option<Op>, probes: Seq<Log>,
    eligible: spec_fn(E, Log, Log) -> bool, read_from: spec_fn(Log) -> Op,
    evidence: I, credit: spec_fn(I, Op, Op) -> bool,
) -> bool {
    probes.len() == steps.len() + 1 && forall|j: int| 0 <= j < steps.len() ==> {
        let e = #[trigger] steps[j]; let old = probes[j]; let new = probes[j+1];
        let w = origin(e);
        eligible(e, old, new) && w.is_some() && can_keep(prefix, w.unwrap(), read_from(new))
            && !can_keep(prefix, w.unwrap(), read_from(old)) ==> credit(evidence, w.unwrap(), read_from(old))
    }
}

// Adapter for the repository's effect-based interpretation of T. The
// semantic observer is existence of a legal order extension. Completeness
// of the effect report is an explicit interpretation, never evidence that
// a physical handler annotated itself with MaintainWeak.
pub open spec fn unsupported_pair<E,I>(
    origin: spec_fn(E) -> Option<Op>, eligible: spec_fn(E,Log,Log) -> bool,
    read_from: spec_fn(Log) -> Op, evidence: I, credit: spec_fn(I,Op,Op) -> bool,
) -> spec_fn(E,Log,Log,Op) -> bool {
    |e: E, new: Log, old: Log, w: Op| origin(e) == Some(w) && eligible(e,old,new)
        && !credit(evidence,w,read_from(old))
}

pub proof fn audited_t_respects_history<E,I>(
    prefix: Seq<Op>, steps: Seq<E>, origin: spec_fn(E) -> Option<Op>, probes: Seq<Log>,
    eligible: spec_fn(E,Log,Log) -> bool, read_from: spec_fn(Log) -> Op,
    evidence: I, credit: spec_fn(I,Op,Op) -> bool,
    labels: spec_fn(E,Log) -> Set<crate::transparency::StrongEffect<Op>>,
)
    requires
        probes.len() == steps.len() + 1,
        crate::transparency::reports_retained_order(
            |_e: E, l: Log| read_from(l), labels, |source: Op, w: Op| can_keep(prefix,w,source),
            unsupported_pair(origin,eligible,read_from,evidence,credit)),
        forall|j: int| 0 <= j < steps.len() ==>
            crate::transparency::effects_transparent(labels(#[trigger] steps[j],probes[j+1])),
    ensures history_clause(prefix,steps,origin,probes,eligible,read_from,evidence,credit),
{
    let pairs = unsupported_pair(origin,eligible,read_from,evidence,credit);
    let resume = |_e: E, l: Log| read_from(l);
    let keeps = |s: Op, w: Op| can_keep(prefix,w,s);
    assert forall|j: int| 0 <= j < steps.len() implies {
        let e = #[trigger] steps[j]; let old = probes[j]; let new = probes[j+1]; let src = origin(e);
        eligible(e,old,new) && src.is_some() && can_keep(prefix,src.unwrap(),read_from(new))
            && !can_keep(prefix,src.unwrap(),read_from(old)) ==> credit(evidence,src.unwrap(),read_from(old))
    } by {
        let e = steps[j]; let w = origin(e).unwrap(); let old = probes[j]; let new = probes[j+1];
        if pairs(e,new,old,w) && keeps(read_from(new),w) {
            crate::transparency::transparent_effects_exclude_retained_order(resume,labels,keeps,pairs,e,new,old,w);
        }
    }
}

pub proof fn history_clause_iff_supported_retention<E,S,I>(
    b: Fork, prefix: RecoveredOrder, steps: Seq<E>, cuts: Seq<S>, origin: spec_fn(E) -> Option<Op>,
    probes: Seq<Log>, eligible: spec_fn(E, Log, Log) -> bool, read_from: spec_fn(Log) -> Op,
    elect: spec_fn(S) -> Side, evidence: I, credit: spec_fn(I, Op, Op) -> bool,
)
    requires
        legal_first(prefix, first_value(b)), cuts.len() == steps.len() + 1, probes.len() == cuts.len(),
        forall|j: int| 0 <= j < steps.len() ==> {
            let e = #[trigger] steps[j]; eligible(e, probes[j], probes[j+1])
                && (origin(e).is_none() || origin(e) == Some(observed_writer(b)))
        },
        forall|j: int| 0 <= j < cuts.len() ==> #[trigger] read_from(probes[j]) == at_side(precedence::source_versions(), elect(cuts[j])),
    ensures history_clause(prefix.ops, steps, origin, probes, eligible, read_from, evidence, credit)
        == flow::supported_retention(steps, cuts, origin, precedence::source_versions(), elect, evidence, credit),
{
    let w = observed_writer(b); let versions = precedence::source_versions();
    assert forall|j: int| 0 <= j < cuts.len() implies
        can_keep(prefix.ops, w, #[trigger] read_from(probes[j])) == (read_from(probes[j]) == w) by {
        assert(read_from(probes[j]) == at_side(versions, elect(cuts[j])));
        extension_iff_writer(b, prefix, read_from(probes[j]));
    }
    if history_clause(prefix.ops, steps, origin, probes, eligible, read_from, evidence, credit) {
        assert forall|j: int| 0 <= j < steps.len() implies precedence::supported_read_update(
            origin(#[trigger] steps[j]), versions, elect(cuts[j]), elect(cuts[j+1]), evidence, credit) by {
            assert(read_from(probes[j]) == at_side(versions, elect(cuts[j])));
            assert(read_from(probes[j+1]) == at_side(versions, elect(cuts[j+1])));
        }
    } else if flow::supported_retention(steps, cuts, origin, versions, elect, evidence, credit) {
        assert forall|j: int| 0 <= j < steps.len() implies {
            let e = #[trigger] steps[j]; let old = probes[j]; let new = probes[j+1]; let src = origin(e);
            eligible(e, old, new) && src.is_some() && can_keep(prefix.ops, src.unwrap(), read_from(new))
                && !can_keep(prefix.ops, src.unwrap(), read_from(old)) ==> credit(evidence, src.unwrap(), read_from(old))
        } by {
            assert(precedence::supported_read_update(origin(steps[j]), versions, elect(cuts[j]), elect(cuts[j+1]), evidence, credit));
        }
    }
}

// Boundary for a SAME-SR1 probe interpretation. The semantic source of a
// quorum value is authenticated by its register value on this workload.
// If every eligible completed probe has H for its own, fixed SR1, the
// independent compatibility test is already true on both probes. A
// compulsory message can therefore defeat a retiming argument without
// giving a physically admissible same-prefix intervention.
pub proof fn fixed_prefix_h_precludes_probe_gain<S,E,I>(m:crate::read_call::Program<S>,res:spec_fn(S)->Option<int>,
    b:Fork,prefix:RecoveredOrder,steps:Seq<E>,probes:Seq<Log>,first_at:spec_fn(Log)->int,
    origin:spec_fn(E)->Option<Op>,eligible:spec_fn(E,Log,Log)->bool,read_from:spec_fn(Log)->Op,
    evidence:I,credit:spec_fn(I,Op,Op)->bool)
    requires legal_first(prefix,first_value(b)),probes.len()==steps.len()+1,
        forall|j:int| 0<=j<steps.len() ==> origin(#[trigger] steps[j]).is_none() || origin(steps[j])==Some(observed_writer(b)),
        forall|j:int| 0<=j<probes.len() ==> {
            let p=#[trigger] probes[j]; first_at(p)==first_value(b) && weak(read_from(p))
                && flow::result(m,res,p)==Some(next(read_from(p),1))
                && exists|o:Seq<Op>,xs:Seq<int>| #[trigger] flow::legal_result(m,res,p,first_at(p),o,xs)
        },
    ensures history_clause(prefix.ops,steps,origin,probes,eligible,read_from,evidence,credit),
        forall|j:int| 0<=j<probes.len() ==> can_keep(prefix.ops,observed_writer(b),read_from(#[trigger] probes[j])),
{
    assert forall|j:int| 0<=j<probes.len() implies can_keep(prefix.ops,observed_writer(b),read_from(#[trigger] probes[j])) by {
        let p=probes[j];let (o,xs)=choose|o:Seq<Op>,xs:Seq<int>| #[trigger] flow::legal_result(m,res,p,first_at(p),o,xs);
        history_test_is_exact(b,prefix,read_from(p));let g=RecoveredOrder{ops:o,states:xs};
        assert(legal(g.ops,g.states,first_value(b),next(read_from(p),1)));
        assert(exists|g:RecoveredOrder| #[trigger] legal(g.ops,g.states,first_value(b),next(read_from(p),1)));
    }
}

}
