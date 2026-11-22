// Functional reading of the prohibition on preserving an observed weak position.
use vstd::prelude::*;
use crate::{Op, Replica, delivery::*, order_extension as history, precedence};
use crate::async_messages::{self as net, Headers};
use crate::fork_information::caller2;
use crate::independent_read::{Calls, State};

verus! {

// An observation of a reached execution. I includes the later request and
// independent weak evidence. D is what the later operation actually does.
// The object specification supplies the meaning of extending a position H.
#[verifier::reject_recursive_types(R)]
pub struct Episode<W, H, R, I> {
    pub writer: W,
    pub position: H,
    pub weak_order: Seq<W>,
    pub input: I,
    pub entry: R,
    pub exit: R,
    pub inherited: R,
    pub ordinary_edges: ISet<(R, R)>,
}

pub open spec fn installed<W,H,R,I>(a: Episode<W,H,R,I>) -> bool {
    exists|old: R| old != a.exit && #[trigger] a.ordinary_edges.contains((old, a.exit))
}

// Test the later decisions against BOTH prior positions. A decision that
// extends both positions conveys no such choice. Empty service cannot certify it.
pub open spec fn resolves<W,H,D>(decisions: ISet<D>, own: (H,W), rival: (H,W),
    extends: spec_fn(H,W,D) -> bool) -> bool {
    (exists|d: D| decisions.contains(d))
        && forall|d: D| #[trigger] decisions.contains(d) ==> extends(own.0, own.1, d)
            && !extends(rival.0, rival.1, d)
}

pub open spec fn retained_difference<W,H,R,I>(a: Episode<W,H,R,I>, b: Episode<W,H,R,I>) -> bool {
    a.input == b.input && a.entry == b.entry
        && a.exit == a.inherited && b.exit == b.inherited && a.inherited != b.inherited
        && (installed(a) || installed(b))
}

pub open spec fn unsupported_outcomes<W,H,R,I,D>(a: Episode<W,H,R,I>, b: Episode<W,H,R,I>,
    actual: ISet<D>, other: ISet<D>, extends: spec_fn(H,W,D) -> bool) -> bool {
    a.writer != b.writer && retained_difference(a,b)
        && (!precedence::has_precedence(a.weak_order, a.writer, b.writer)
            || !precedence::has_precedence(b.weak_order, a.writer, b.writer))
        && (exists|d: D| #[trigger] actual.contains(d) && extends(a.position,a.writer,d)
            && !extends(b.position,b.writer,d))
        && resolves(other, (b.position,b.writer), (a.position,a.writer), extends)
}
pub type Input<S> = (precedence::IndependentView, S, Calls, Set<Replica>, Set<Replica>);

pub open spec fn keeps_value() -> spec_fn(Seq<Op>,Op,int) -> bool {
    |prefix: Seq<Op>, w: Op, d: int| exists|v: Op| history::weak(v) && d == crate::next(v,1)
        && #[trigger] history::can_keep(prefix,w,v)
}

pub open spec fn input<S>(e: precedence::IndependentView, x: State<S>) -> Input<S> {
    (e,caller2(x),x.calls,x.requested,x.first_requested)
}

pub open spec fn ordinary_edges<X,A,R>(record: spec_fn(X)->R, installer: spec_fn(X,A)->bool,
    path: crate::promotion_wait::Path<X,A>) -> ISet<(R,R)> {
    ISet::new(|edge: (R,R)| exists|i: int| 0 <= i < path.actions.len()
        && edge == (record(#[trigger] path.states[i]),record(path.states[i+1]))
        && installer(path.states[i],path.actions[i]))
}

pub open spec fn ordinary_replica<S>(k: Headers) -> spec_fn(State<S>,crate::read_call::Event)->bool {
    |x: State<S>,a: crate::read_call::Event| { let e=net::callback(k,process_step(x.cfg.net,a));
        e.actor is At && !crate::guarded_comparison::weak_work(e) }
}

}
