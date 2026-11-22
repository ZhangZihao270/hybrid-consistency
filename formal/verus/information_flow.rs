// Backwards from the two histories to the independent caller's actual inputs.
use vstd::prelude::*;
use crate::{Op, checkpoint::*, delivery::*, protocol::*};
use crate::first_splice::{pick, Tape};
use crate::read_call::{Log, Program, Event, obs};
use crate::precedence::{Side, supported_read_update};

verus! {

pub open spec fn c2_log(l: Log) -> Tape {
    pick(obs(l), Process::SecondClient, true)
}

// This includes local inputs, timers/CPU steps, sends (including any chosen
// body), and the order and slot of every delivery. Only the delivered packet
// itself comes from the queue, independently of this schedule.
pub open spec fn c2_schedule(l: Log) -> Seq<Event> {
    c2_log(l).map_values(|e: ProcessStep<int, Wire>| e.action)
}

proof fn projected_memory<S>(m: Program<S>, p: Process, es: Tape, k: nat)
    requires k <= es.len(),
    ensures ({
        let local = pick(es.take(k as int), p, true);
        memory(m, p, es, k) == memory(m, p, local, local.len())
    }),
    decreases k,
{
    if k == 0 {
        assert(es.take(0) =~= Seq::empty());
    } else {
        let j = (k - 1) as nat;
        let head = es.take(j as int);
        let e = es[j as int];
        let old = pick(head, p, true);
        let new = pick(es.take(k as int), p, true);
        projected_memory(m, p, es, j);
        assert(es.take(k as int) =~= head + seq![e]);
        crate::first_causality::pick_concat(head, seq![e], p, true);
        assert(seq![e].drop_first() =~= Seq::empty());
        reveal_with_fuel(pick, 2);
        assert(pick(seq![e], p, true) == if e.actor == p { seq![e] } else { Seq::empty() });
        if e.actor == p {
            assert(new =~= old.push(e));
            memory_on_common_prefix(m, p, old, new, old.len());
        } else { assert(new == old); }
    }
}

// Recover the occurrence, including its local ordinal if identical packets
// have been delivered more than once.
proof fn occurrence(es: Tape, p: Process, k: nat) -> (i: nat)
    requires k < pick(es, p, true).len(),
    ensures i < es.len(), es[i as int] == pick(es, p, true)[k as int], es[i as int].actor == p,
        pick(es.take(i as int), p, true).len() == k,
    decreases es.len(),
{
    let u = es.drop_first();
    if es[0].actor == p && k == 0 { assert(es.take(0) =~= Seq::empty()); 0 }
    else {
        let j = occurrence(u, p, if es[0].actor == p { (k - 1) as nat } else { k });
        let prefix = es.take(j as int + 1);
        assert(prefix.drop_first() =~= u.take(j as int));
        j + 1
    }
}

pub open spec fn untouched(l: Log, lo: int, hi: int, id: nat) -> bool {
    forall|j: int| lo <= j < hi ==> crate::scheduling::untouched_slot(#[trigger] l.actions[j], id)
}

pub open spec fn issued(l: Log, i: int, id: nat, q: Packet<Wire>) -> bool {
    (l.nets[0].pending.get(id) == Some(q) && untouched(l, 0, i, id))
    || exists|j: int| 0 <= j < i && #[trigger] l.actions[j] == Action::Send(id, q)
        && live(l.nets[j], q.from) && untouched(l, j + 1, i, id)
}

proof fn current_issue(l: Log, i: nat, id: nat, q: Packet<Wire>)
    requires trace(|x, w| cell(x, w), l.nets, l.actions), i <= l.actions.len(),
        l.nets[i as int].pending.get(id) == Some(q),
    ensures issued(l, i as int, id, q),
    decreases i,
{
    if i > 0 {
        let j = i as int - 1;
        let a = l.actions[j];
        assert(enabled(l.nets[j], a) && l.nets[i as int] == advance(|x, w| cell(x, w), l.nets[j], a));
        if a == Action::Send(id, q) { assert(untouched(l, j + 1, i as int, id)); }
        else {
            assert(crate::scheduling::untouched_slot(a, id));
            current_issue(l, j as nat, id, q);
            if !untouched(l, 0, j, id) || l.nets[0].pending.get(id) != Some(q) {
                let h = choose|h: int| 0 <= h < j && #[trigger] l.actions[h] == Action::Send(id, q)
                    && live(l.nets[h], q.from) && untouched(l, h + 1, j, id);
                assert(untouched(l, h + 1, i as int, id));
            }
        }
    }
}

pub open spec fn receipt(l: Log, i: int, id: nat, q: Packet<Wire>) -> bool {
    0 <= i < l.actions.len() && l.actions[i] == Action::<Wire>::Deliver(id)
        && q.to == Process::SecondClient && l.nets[i].pending.get(id) == Some(q)
        && obs(l)[i].incoming == Some(q) && issued(l, i, id, q)
}

proof fn trace_receipt(l: Log, i: int, id: nat)
    requires trace(|x, w| cell(x, w), l.nets, l.actions), 0 <= i < l.actions.len(),
        l.actions[i] == Action::<Wire>::Deliver(id), obs(l)[i].actor == Process::SecondClient,
    ensures receipt(l, i, id, l.nets[i].pending[id]),
{
    assert(enabled(l.nets[i], l.actions[i]));
    current_issue(l, i as nat, id, l.nets[i].pending[id]);
}

pub open spec fn differing_receipts(a: Log, b: Log, k: int, i: int, j: int, id: nat) -> bool {
    0 <= k < c2_log(a).len() && 0 <= k < c2_log(b).len()
        && c2_log(a)[k] == obs(a)[i] && c2_log(b)[k] == obs(b)[j]
        && pick(obs(a).take(i), Process::SecondClient, true).len() == k
        && pick(obs(b).take(j), Process::SecondClient, true).len() == k
        && receipt(a, i, id, a.nets[i].pending[id]) && receipt(b, j, id, b.nets[j].pending[id])
        && a.nets[i].pending[id] != b.nets[j].pending[id]
}

// Locate a receipt that actually separates the deterministic caller states.
// Choose the last equal prefix, so the states stay distinct through return.
pub open spec fn splits<S>(ma: Program<S>, mb: Program<S>, a: Tape, b: Tape, k: int, end: nat) -> bool {
    let c = Process::SecondClient;
    0 <= k < end <= a.len() && end <= b.len()
        && memory(ma, c, a, k as nat) == memory(mb, c, b, k as nat)
        && a[k] != b[k] && (forall|h: nat| k < h <= end ==>
            #[trigger] memory(ma, c, a, h) != #[trigger] memory(mb, c, b, h))
}

proof fn last_common_state<S>(ma: Program<S>, mb: Program<S>, a: Tape, b: Tape, end: nat) -> (k: nat)
    requires end <= a.len(), end <= b.len(), ma.update == mb.update,
        (ma.initial)(Process::SecondClient) == (mb.initial)(Process::SecondClient),
        memory(ma, Process::SecondClient, a, end) != memory(mb, Process::SecondClient, b, end),
    ensures splits(ma, mb, a, b, k as int, end),
    decreases end,
{
    let c = Process::SecondClient;
    assert(end > 0);
    let j = (end - 1) as nat;
    if memory(ma, c, a, j) == memory(mb, c, b, j) { j }
    else { last_common_state(ma, mb, a, b, j) }
}

proof fn packet_or_schedule<S>(ma: Program<S>, mb: Program<S>, a: Log, b: Log)
    requires trace(|x, w| cell(x, w), a.nets, a.actions),
        trace(|x, w| cell(x, w), b.nets, b.actions), ma.update == mb.update,
        (ma.initial)(Process::SecondClient) == (mb.initial)(Process::SecondClient),
        memory(ma, Process::SecondClient, c2_log(a), c2_log(a).len())
            != memory(mb, Process::SecondClient, c2_log(b), c2_log(b).len()),
    ensures c2_schedule(a) != c2_schedule(b) || exists|k: int, i: int, j: int, id: nat|
        #[trigger] differing_receipts(a, b, k, i, j, id)
            && splits(ma, mb, c2_log(a), c2_log(b), k, c2_log(a).len()),
{
    let c = Process::SecondClient;
    let left = c2_log(a);
    let right = c2_log(b);
    if c2_schedule(a) == c2_schedule(b) {
        assert(c2_schedule(a).len() == left.len());
        assert(c2_schedule(b).len() == right.len());
        let k = last_common_state(ma, mb, left, right, left.len()) as int;
        let i = occurrence(obs(a), c, k as nat) as int;
        let j = occurrence(obs(b), c, k as nat) as int;
        assert(c2_schedule(a)[k] == c2_schedule(b)[k]);
        assert(left[k].own_local == None && right[k].own_local == None);
        assert(left[k].incoming != right[k].incoming);
        assert(a.actions[i] is Deliver);
        let id = a.actions[i]->Deliver_0;
        trace_receipt(a, i, id);
        trace_receipt(b, j, id);
        assert(a.nets[i].pending[id] != b.nets[j].pending[id]);
        assert(differing_receipts(a, b, k, i, j, id));
    }
}

pub open spec fn result<S>(m: Program<S>, read: spec_fn(S) -> Option<int>, l: Log) -> Option<int> {
    read(memory(m, Process::SecondClient, obs(l), l.actions.len()))
}

pub open spec fn legal_result<S>(m: Program<S>, read: spec_fn(S) -> Option<int>,
    l: Log, first: int, ops: Seq<Op>, xs: Seq<int>) -> bool {
    let v = result(m, read, l);
    v.is_some() && crate::legal(ops, xs, first, v.unwrap())
}

// No chosen interleaving, fanout or metadata format is required. The logs may
// start at different checkpoints with the same initial C2 private state.
// If a schedule differs, it is not sound to infer a different packet body.
pub proof fn h_requires_distinguishing_input<S>(
    ma: Program<S>, mb: Program<S>, read: spec_fn(S) -> Option<int>, a: Log, b: Log,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>,
)
    requires
        ma.update == mb.update, (ma.initial)(Process::SecondClient) == (mb.initial)(Process::SecondClient),
        trace(|x, w| cell(x, w), a.nets, a.actions), accepted(ma, obs(a)),
        trace(|x, w| cell(x, w), b.nets, b.actions), accepted(mb, obs(b)),
        legal_result(ma, read, a, 5, ao, ax), legal_result(mb, read, b, 2, bo, bx),
    ensures
        result(ma, read, a) == Some(5), result(mb, read, b) == Some(2),
        c2_log(a) != c2_log(b),
        c2_schedule(a) != c2_schedule(b) || exists|k: int, i: int, j: int, id: nat|
            #[trigger] differing_receipts(a, b, k, i, j, id)
            && splits(ma, mb, c2_log(a), c2_log(b), k, c2_log(a).len()),
{
    let c = Process::SecondClient;
    crate::legal_history_keeps_first_read(ao, ax, 5, result(ma, read, a).unwrap());
    crate::legal_history_keeps_first_read(bo, bx, 2, result(mb, read, b).unwrap());
    let left = c2_log(a);
    let right = c2_log(b);
    projected_memory(ma, c, obs(a), a.actions.len());
    projected_memory(mb, c, obs(b), b.actions.len());
    assert(obs(a).take(a.actions.len() as int) =~= obs(a));
    assert(obs(b).take(b.actions.len() as int) =~= obs(b));
    if left == right {
        memory_from_same_local_state(ma, mb, c, left, left.len());
        assert(false);
    }
    packet_or_schedule(ma, mb, a, b);
}

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

// Unobserved interleaving may change length or order elsewhere in a run.
// This sufficient alignment rule is used only to audit the concrete schedule.
pub proof fn aligned_actions(a: Tape, b: Tape, p: Process)
    requires a.len() == b.len(), forall|i: int| 0 <= i < a.len() ==> {
        let x = #[trigger] a[i]; let y = #[trigger] b[i];
        (x.actor == p) == (y.actor == p) && (x.actor == p ==> x.action == y.action)
    },
    ensures pick(a, p, true).map_values(|e: ProcessStep<int, Wire>| e.action)
        == pick(b, p, true).map_values(|e: ProcessStep<int, Wire>| e.action),
    decreases a.len(),
{
    if a.len() > 0 {
        let u = a.drop_first();
        let v = b.drop_first();
        assert forall|i: int| 0 <= i < u.len() implies {
            let x = #[trigger] u[i]; let y = #[trigger] v[i];
            (x.actor == p) == (y.actor == p) && (x.actor == p ==> x.action == y.action)
        } by { assert(u[i] == a[i + 1] && v[i] == b[i + 1]); }
        aligned_actions(u, v, p);
        let f = |e: ProcessStep<int, Wire>| e.action;
        if a[0].actor == p {
            assert(pick(a, p, true).map_values(f) =~= seq![a[0].action] + pick(u, p, true).map_values(f));
            assert(pick(b, p, true).map_values(f) =~= seq![b[0].action] + pick(v, p, true).map_values(f));
        }
    }
}

// Audit a sequence of actual retention updates. The adapter must identify
// the causal source of each update and the later resolver's effective source
// choice at fixed independent inputs. An order credit is independent of the
// retained information. No return value, history legality or second run
// occurs in the test. An opaque encoding or unused log is allowed.
pub open spec fn supported_retention<E, S, V, I>(
    events: Seq<E>, cuts: Seq<S>, from_sample: spec_fn(E) -> Option<V>,
    sources: (V, V), elect: spec_fn(S) -> Side, independent: I,
    credit: spec_fn(I, V, V) -> bool,
) -> bool {
    cuts.len() == events.len() + 1 && forall|i: int| 0 <= i < events.len() ==>
        supported_read_update(from_sample(#[trigger] events[i]), sources,
            elect(cuts[i]), elect(cuts[i + 1]), independent, credit)
}

}
