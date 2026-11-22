// Which previously observed writer can a returning SR2 still read from?
use vstd::prelude::*;
use crate::{Op, checkpoint::*, order_extension as history, precedence};
use crate::coupled_construction::{prepared, root};
use crate::coupled_reads::legal_returns;
use crate::first_assembly::Lanes;
use crate::fork_alternatives::{self as fork, Tapes};
use crate::fork_information::{self as info, Residual, caller2, live_view};
use crate::guarded_comparison as cmp;
use crate::independent_read::{self as read, State};
use crate::read_call::{Event, Program};

verus! {

// External SR2 inputs are held to the same domain for both records.
// ISet::full() tests every finite ordinary continuation. There is no
// restriction on the native SR1 tapes. The register versions are unique
// on this workload; the handler need not identify a writer or a source.
pub open spec fn possible_writers<S>(
    m: Program<S>, res: spec_fn(S) -> Option<int>, reader: S,
    record: Residual<S>, inputs: ISet<Seq<Event>>,
) -> Set<Op> {
    set![Op::W1, Op::W2].filter(|w: Op| exists|s: Seq<Event>| inputs.contains(s)
        && #[trigger] fork::selects(true, m, res, reader, s, record) == Some(crate::next(w, 1)))
}

// The actual choice extends the writer's read-from position. From another
// reached record the reader can still finish, but loses EVERY way of
// extending that same position within the input domain. The independent
// weak evidence admits an order that does not justify this preference.
// The other execution is always run with its own prefix and its own guards.
pub open spec fn record_enables_observed_order<S>(
    m: Program<S>, res: spec_fn(S) -> Option<int>, b: Fork, reader: S,
    record: Residual<S>, other: Residual<S>, inputs: ISet<Seq<Event>>, actual: Seq<Event>,
    weak_orders: precedence::Possible,
) -> bool {
    let w = observed_writer(b);
    let prefix = history::at_first(b).ops;
    let selected = fork::writer(fork::selects(true, m, res, reader, actual, record));
    let alternatives = possible_writers(m, res, reader, other, inputs);
    inputs.contains(actual) && selected.is_some() && history::can_keep(prefix, w, selected.unwrap())
        && (forall|v: Op| #[trigger] alternatives.contains(v) ==> !history::can_keep(prefix, w, v))
        && (exists|v: Op, order: Seq<Op>| #[trigger] alternatives.contains(v)
            && #[trigger] weak_orders(precedence::independent_view(b), order)
            && !precedence::has_precedence(order, w, v))
}

pub open spec fn history_failure<S>(
    m: Program<S>, res: spec_fn(S) -> Option<int>, b: Fork, x: State<S>, inputs: ISet<Seq<Event>>,
) -> bool {
    exists|s: Seq<Event>| inputs.contains(s) && #[trigger] cmp::second_return(true, m, res, b, x, s)
        && !legal_returns(first_value(b), fork::outcome(true, m, res, x, s).unwrap())
}

// Each abstract selection used here is a concrete first return from x.
// Thus safety on actual completions characterizes the entire set of
// versions available at the retained input, including unchosen futures.
pub proof fn writers_at_returning_cut<S>(
    m: Program<S>, res: spec_fn(S) -> Option<int>, b: Fork, x: State<S>,
    inputs: ISet<Seq<Event>>, actual: Seq<Event>,
)
    requires cmp::issued(x, b), !read::returned(res)(x), inputs.contains(actual),
        cmp::second_return(true, m, res, b, x, actual), !history_failure(m, res, b, x, inputs),
    ensures possible_writers(m, res, caller2(x), live_view(x), inputs) == set![observed_writer(b)],
        fork::outcome(true, m, res, x, actual) == Some(first_value(b)),
{
    let record = live_view(x);
    let w = observed_writer(b);
    let sources = possible_writers(m, res, caller2(x), record, inputs);
    let value = fork::outcome(true, m, res, x, actual);
    fork::real_selection(true, m, res, x, actual);
    fork::history_completion(b, value);
    assert(crate::next(w, 1) == first_value(b));
    assert(sources.contains(w));
    assert forall|v: Op| #[trigger] sources.contains(v) implies v == w by {
        let s = choose|s: Seq<Event>| inputs.contains(s)
            && #[trigger] fork::selects(true, m, res, caller2(x), s, record) == Some(crate::next(v, 1));
        fork::real_selection(true, m, res, x, s);
        cmp::returned_run(true, m, res, b, x, s);
        fork::history_completion(b, fork::outcome(true, m, res, x, s));
    }
    assert(sources =~= set![w]);
}

// A is used upstream for returning operations. This implication starts
// with the two independently admitted executions in the paper. A failure
// is witnessed by a native completion from one of these very same cuts.
pub proof fn original_fork_requires_preservation<S>(
    m: Program<S>, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>,
    lanes: Lanes, n: Notice, a: Tapes, b: Tapes, inputs: ISet<Seq<Event>>,
    sa: Seq<Event>, sb: Seq<Event>, assigned_a: bool, assigned_b: bool,
)
    requires
        fork::candidate(m, first, res, lanes, n, a, b),
        inputs.contains(sa), inputs.contains(sb),
        cmp::second_return(true, m, res, alpha(n), fork::cut(m, lanes, alpha(n), a), sa),
        cmp::second_return(true, m, res, beta(n), fork::cut(m, lanes, beta(n), b), sb),
        n != Notice::Replication ==> assigned_a && assigned_b,
    ensures ({
        let left = alpha(n); let right = beta(n);
        let x = fork::cut(m, lanes, left, a); let y = fork::cut(m, lanes, right, b);
        let ra = info::retained(prepared(m, lanes, left, a.replicas));
        let rb = info::retained(prepared(m, lanes, right, b.replicas));
        let c = caller2(x); let orders = precedence::actual_cuts(n, assigned_a, assigned_b);
        info::retained(root(m, lanes, left)) == info::retained(root(m, lanes, right))
            && ra == live_view(x) && rb == live_view(y) && caller2(y) == c
            && ra.cells == (2int, 5int) && rb.cells == ra.cells
            && precedence::independent_view(left) == precedence::independent_view(right)
            && truthful_notice(left, weak_assignment(left, assigned_a).ops)
            && truthful_notice(right, weak_assignment(right, assigned_b).ops)
            && (history_failure(m, res, left, x, inputs) || history_failure(m, res, right, y, inputs)
                || (ra != rb
                    && fork::outcome(true, m, res, x, sa) == Some(5)
                    && fork::outcome(true, m, res, y, sb) == Some(2)
                    && possible_writers(m, res, c, ra, inputs) == set![Op::W2]
                    && possible_writers(m, res, c, rb, inputs) == set![Op::W1]
                    && (sa == sb ==> exists|j: int| #[trigger] info::used_receipt(true, m, res, x, y, sa, j))
                    && record_enables_observed_order(m, res, left, c, ra, rb, inputs, sa, orders)
                    && record_enables_observed_order(m, res, right, c, rb, ra, inputs, sb, orders)))
    }),
{
    let left = alpha(n); let right = beta(n);
    let x = fork::cut(m, lanes, left, a); let y = fork::cut(m, lanes, right, b);
    let c = caller2(x); let ra = live_view(x); let rb = live_view(y);
    crate::coupled_traffic::pair_at_fanout(m, lanes, n, info::identity());
    info::paired_retention(root(m, lanes, left), root(m, lanes, right), n);
    info::private_first_return_cannot_signal(m, first, res, lanes, left, a.replicas, a.caller);
    info::private_first_return_cannot_signal(m, first, res, lanes, right, b.replicas, b.caller);
    precedence::equal_independent_views(right);
    weak_assignment_at_delivery(left, assigned_a); weak_assignment_at_delivery(right, assigned_b);
    if !history_failure(m, res, left, x, inputs) && !history_failure(m, res, right, y, inputs) {
        writers_at_returning_cut(m, res, left, x, inputs, sa);
        writers_at_returning_cut(m, res, right, y, inputs, sb);
        if sa == sb {
            info::distinguishing_delivery(true, m, res, n, x, y, sa);
        }
        fork::real_selection(true, m, res, x, sa);
        fork::real_selection(true, m, res, y, sb);
        assert(caller2(y) == c);
        let wa = possible_writers(m, res, c, ra, inputs);
        let wb = possible_writers(m, res, c, rb, inputs);
        assert(wa.contains(Op::W2) && wb.contains(Op::W1));
        history::canonical_orders_exist(left); history::canonical_orders_exist(right);
        history::extension_iff_writer(left, history::at_first(left), Op::W1);
        history::extension_iff_writer(left, history::at_first(left), Op::W2);
        history::extension_iff_writer(right, history::at_first(right), Op::W1);
        history::extension_iff_writer(right, history::at_first(right), Op::W2);

        // Each opposing weak prefix is an actual possibility at the same
        // independently available weak view, even if the copy assigned G.
        let orders = precedence::actual_cuts(n, assigned_a, assigned_b);
        let oa = weak_assignment(left, assigned_a).ops;
        let ob = weak_assignment(right, assigned_b).ops;
        assert(orders(precedence::independent_view(left), ob)
            && !precedence::has_precedence(ob, Op::W2, Op::W1));
        assert(orders(precedence::independent_view(right), oa)
            && !precedence::has_precedence(oa, Op::W1, Op::W2));
        assert(exists|v: Op, o: Seq<Op>| #[trigger] wb.contains(v)
            && #[trigger] orders(precedence::independent_view(left), o)
            && !precedence::has_precedence(o, Op::W2, v)) by {
            assert(wb.contains(Op::W1) && orders(precedence::independent_view(left), ob));
        }
        assert(exists|v: Op, o: Seq<Op>| #[trigger] wa.contains(v)
            && #[trigger] orders(precedence::independent_view(right), o)
            && !precedence::has_precedence(o, Op::W1, v)) by {
            assert(wa.contains(Op::W2) && orders(precedence::independent_view(right), oa));
        }
        assert(record_enables_observed_order(m, res, left, c, ra, rb, inputs, sa, orders));
        assert(record_enables_observed_order(m, res, right, c, rb, ra, inputs, sb, orders));
    }
}

}
