use vstd::prelude::*;
use crate::Replica;
use crate::ordered_store::majority;

verus! {

// The interface concerns one distinguished strong read of the original
// protocol. States include private memory, transport, operation identity
// and whatever other commands the SMR admits. The observation functions
// come from the implementation. No particular request topology is imposed.
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(E)]
pub struct ReadSystem<X, E> {
    pub initial: spec_fn(X) -> bool,
    pub next: spec_fn(X, E, X) -> bool,
    pub invoked: spec_fn(X) -> bool, // cut at this read's invocation
    pub client_live: spec_fn(X) -> bool,
    pub up: spec_fn(X) -> Set<Replica>,
    pub value: spec_fn(X, Replica) -> int,
    pub response: spec_fn(X) -> Option<int>,
    // Identifies the majority actually serving an operation. Sending a
    // probe to an unavailable/nonresponding site need not involve it.
    pub served_by: spec_fn(Seq<X>, Seq<E>, Set<Replica>) -> bool,
}

pub struct Stream<X, E> { pub state: spec_fn(nat) -> X, pub event: spec_fn(nat) -> E }

pub open spec fn path<X, E>(p: ReadSystem<X, E>, t: Seq<X>, a: Seq<E>) -> bool {
    t.len() == a.len()+1
        && forall|i: int| 0 <= i < a.len() ==> (p.next)(t[i], #[trigger] a[i], t[i+1])
}

pub open spec fn reaches<X, E>(p: ReadSystem<X, E>, x: X) -> bool {
    exists|t: Seq<X>, a: Seq<E>| #[trigger] path(p, t, a) && (p.initial)(t[0]) && t.last() == x
}

pub open spec fn follows_stock<X, E>(p: ReadSystem<X, E>, e: Stream<X, E>) -> bool {
    forall|i: nat| (p.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i+1))
}

pub open spec fn first_answer<X, E>(p: ReadSystem<X, E>, t: Seq<X>, a: Seq<E>, v: int) -> bool {
    path(p, t, a) && (p.response)(t.last()) == Some(v)
        && forall|i: int| 0 <= i < a.len() ==> (p.response)(#[trigger] t[i]).is_none()
}

pub open spec fn member_during<X, E>(p: ReadSystem<X, E>, t: Seq<X>, q: Set<Replica>, v: int) -> bool {
    exists|r: Replica, i: int| q.contains(r) && 0 <= i < t.len() && #[trigger] (p.value)(t[i], r) == v
}

// The fair progress clause, the existential "can use any available majority"
// clause, and the interval validity of an actual read are distinct. Fair is
// the stock scheduler/network semantics, independent of the returned value.
pub open spec fn eventual<X, E>(p: ReadSystem<X, E>, fair: spec_fn(Stream<X, E>) -> bool) -> bool {
    forall|e: Stream<X, E>| #[trigger] follows_stock(p, e) && fair(e) && reaches(p, (e.state)(0))
        && (p.invoked)((e.state)(0)) && (p.response)((e.state)(0)).is_none()
        && (forall|i: nat| (p.client_live)(#[trigger] (e.state)(i)) && majority((p.up)((e.state)(i))))
         ==> exists|k: nat| (p.response)(#[trigger] (e.state)(k)).is_some()
}

pub open spec fn quorum_witness<X, E>(p: ReadSystem<X, E>, x: X, q: Set<Replica>, t: Seq<X>, a: Seq<E>, v: int) -> bool {
    first_answer(p, t, a, v) && t[0] == x && (p.served_by)(t, a, q) && member_during(p, t, q, v)
        && forall|i: int| 0 <= i < t.len() ==> (p.client_live)(#[trigger] t[i]) && q.subset_of((p.up)(t[i]))
}

pub open spec fn available_majorities<X, E>(p: ReadSystem<X, E>) -> bool {
    forall|x: X, q: Set<Replica>| #[trigger] reaches(p, x) && #[trigger] majority(q) && q.subset_of((p.up)(x))
        && (p.client_live)(x) && (p.invoked)(x) && (p.response)(x).is_none()
         ==> exists|t: Seq<X>, a: Seq<E>, v: int| #[trigger] quorum_witness(p, x, q, t, a, v)
}

pub open spec fn valid_samples<X, E>(p: ReadSystem<X, E>) -> bool {
    forall|t: Seq<X>, a: Seq<E>, q: Set<Replica>, v: int| #[trigger] first_answer(p, t, a, v)
        && reaches(p, t[0]) && (p.invoked)(t[0]) && majority(q) && #[trigger] (p.served_by)(t, a, q)
         ==> member_during(p, t, q, v)
}

pub open spec fn read_a<X, E>(p: ReadSystem<X, E>, fair: spec_fn(Stream<X, E>) -> bool) -> bool {
    eventual(p, fair) && available_majorities(p) && valid_samples(p)
}

pub open spec fn guarded<X, E>(p: ReadSystem<X, E>, guard: spec_fn(X, E, X) -> bool) -> ReadSystem<X, E> {
    ReadSystem { next: |s, e, t| (p.next)(s, e, t) && guard(s, e, t), ..p }
}

pub open spec fn inductive<X, E>(p: ReadSystem<X, E>, inv: spec_fn(X) -> bool) -> bool {
    (forall|x: X| #[trigger] (p.initial)(x) ==> inv(x))
        && forall|s: X, e: E, t: X| inv(s) && #[trigger] (p.next)(s, e, t) ==> inv(t)
}

pub(crate) proof fn invariant_on_path<X, E>(p: ReadSystem<X, E>, inv: spec_fn(X) -> bool, t: Seq<X>, a: Seq<E>, k: nat)
    requires inductive(p, inv), path(p, t, a), inv(t[0]), k <= a.len(),
    ensures inv(t[k as int]),
    decreases k,
{
    if k > 0 {
        invariant_on_path(p, inv, t, a, (k-1) as nat);
        assert((p.next)(t[k-1], a[k-1], t[k as int]));
    }
}

pub proof fn reachable_invariant<X, E>(p: ReadSystem<X, E>, inv: spec_fn(X) -> bool, x: X)
    requires inductive(p, inv), reaches(p, x),
    ensures inv(x),
{
    let (t, a) = choose|t: Seq<X>, a: Seq<E>| #[trigger] path(p, t, a) && (p.initial)(t[0]) && t.last() == x;
    invariant_on_path(p, inv, t, a, a.len());
}

pub open spec fn harmless_on_invariant<X, E>(p: ReadSystem<X, E>, inv: spec_fn(X) -> bool, g: spec_fn(X, E, X) -> bool) -> bool {
    forall|s: X, e: E, t: X| inv(s) && #[trigger] (p.next)(s, e, t) ==> g(s, e, t)
}

proof fn guard_on_path<X, E>(p: ReadSystem<X, E>, inv: spec_fn(X) -> bool, g: spec_fn(X, E, X) -> bool, t: Seq<X>, a: Seq<E>)
    requires inductive(p, inv), harmless_on_invariant(p, inv, g), t.len()>0, inv(t[0]),
    ensures path(p, t, a) == path(guarded(p, g), t, a),
{
    let m = guarded(p, g);
    if path(p, t, a) {
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] (m.next)(t[i], a[i], t[i+1]) by {
            invariant_on_path(p, inv, t, a, i as nat);
            assert((p.next)(t[i], a[i], t[i+1]));
        }
    }
    if path(m, t, a) {
        assert forall|i: int| 0 <= i<a.len() implies (p.next)(t[i], #[trigger] a[i], t[i+1]) by {
            assert((m.next)(t[i], a[i], t[i+1]));
        }
    }
}

pub proof fn guarded_reachability<X, E>(p: ReadSystem<X, E>, inv: spec_fn(X) -> bool, g: spec_fn(X, E, X) -> bool, x: X)
    requires inductive(p, inv), harmless_on_invariant(p, inv, g),
    ensures reaches(p, x) == reaches(guarded(p, g), x),
{
    let m = guarded(p, g);
    if reaches(p, x) {
        let (t, a) = choose|t: Seq<X>, a: Seq<E>| #[trigger] path(p, t, a) && (p.initial)(t[0]) && t.last() == x;
        guard_on_path(p, inv, g, t, a);
    }
    if reaches(m, x) {
        let (t, a) = choose|t: Seq<X>, a: Seq<E>| #[trigger] path(m, t, a) && (m.initial)(t[0]) && t.last() == x;
        guard_on_path(p, inv, g, t, a);
    }
}

pub open spec fn finite_stock_run<X, E>(p: ReadSystem<X, E>, t: Seq<X>, a: Seq<E>) -> bool {
    path(p, t, a) && reaches(p, t[0])
}

pub open spec fn infinite_stock_run<X, E>(p: ReadSystem<X, E>, e: Stream<X, E>) -> bool {
    follows_stock(p, e) && reaches(p, (e.state)(0))
}

proof fn invariant_in_stream<X, E>(p: ReadSystem<X, E>, e: Stream<X, E>, inv: spec_fn(X) -> bool, k: nat)
    requires infinite_stock_run(p, e), inductive(p, inv),
    ensures inv((e.state)(k)),
    decreases k,
{
    if k == 0 { reachable_invariant(p, inv, (e.state)(0)); } else {
        let h = (k-1) as nat; invariant_in_stream(p, e, inv, h);
        assert((p.next)((e.state)(h), (e.event)(h), (e.state)(k)));
    }
}

// Quantifies over the original full states and events. Other strong
// operations, their replies and histories need not be interpreted by the
// read observer. Equality of the stock executions preserves trace-based
// safety and liveness properties over those events.
pub proof fn reachable_language_preserved<X, E>(
    p: ReadSystem<X, E>, inv: spec_fn(X) -> bool, g: spec_fn(X, E, X) -> bool,
)
    requires inductive(p, inv), harmless_on_invariant(p, inv, g),
    ensures ({
        let m = guarded(p, g);
        (forall|t: Seq<X>, a: Seq<E>| #[trigger] finite_stock_run(p, t, a) == finite_stock_run(m, t, a))
            && (forall|e: Stream<X, E>| #[trigger] infinite_stock_run(p, e) == infinite_stock_run(m, e))
    }),
{
    let m = guarded(p, g);
    assert forall|t: Seq<X>, a: Seq<E>| #[trigger] finite_stock_run(p, t, a) == finite_stock_run(m, t, a) by {
        if t.len()>0 {
            guarded_reachability(p, inv, g, t[0]);
            if reaches(p, t[0]) { reachable_invariant(p, inv, t[0]); guard_on_path(p, inv, g, t, a); }
        }
    }
    assert forall|e: Stream<X, E>| #[trigger] infinite_stock_run(p, e) == infinite_stock_run(m, e) by {
        guarded_reachability(p, inv, g, (e.state)(0));
        if infinite_stock_run(p, e) {
            assert forall|i: nat| (m.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i+1)) by {
                invariant_in_stream(p, e, inv, i); assert((p.next)((e.state)(i), (e.event)(i), (e.state)(i+1)));
            }
        }
        if follows_stock(m, e) {
            assert forall|i: nat| (p.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i+1)) by {
                assert((m.next)((e.state)(i), (e.event)(i), (e.state)(i+1)));
            }
        }
    }
}

// Any stock quorum, any reachable data, all admitted routing, all required
// repair and metadata steps. The wrapped program has the very same possible
// transitions on reachable states. A therefore cannot constrain how the
// guard treats a new combination introduced only by local weak writes.
pub proof fn live_guard_preserves_read_a<X, E>(
    p: ReadSystem<X, E>, fair: spec_fn(Stream<X, E>) -> bool, inv: spec_fn(X) -> bool, g: spec_fn(X, E, X) -> bool,
)
    requires read_a(p, fair), inductive(p, inv), harmless_on_invariant(p, inv, g),
    ensures read_a(guarded(p, g), fair),
{
    let m = guarded(p, g);
    assert forall|e: Stream<X, E>| #[trigger] follows_stock(m, e) && fair(e) && reaches(m, (e.state)(0))
        && (m.invoked)((e.state)(0)) && (m.response)((e.state)(0)).is_none()
        && (forall|i: nat| (m.client_live)(#[trigger] (e.state)(i)) && majority((m.up)((e.state)(i))))
        implies exists|k: nat| (m.response)(#[trigger] (e.state)(k)).is_some() by {
        guarded_reachability(p, inv, g, (e.state)(0));
        assert forall|i: nat| (p.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i+1)) by {
            assert((m.next)((e.state)(i), (e.event)(i), (e.state)(i+1)));
        }
        assert(follows_stock(p, e));
    }
    assert forall|x: X, q: Set<Replica>| #[trigger] reaches(m, x) && #[trigger] majority(q) && q.subset_of((m.up)(x))
        && (m.client_live)(x) && (m.invoked)(x) && (m.response)(x).is_none()
        implies exists|t: Seq<X>, a: Seq<E>, v: int| #[trigger] quorum_witness(m, x, q, t, a, v) by {
        guarded_reachability(p, inv, g, x); reachable_invariant(p, inv, x);
        let (t, a, v) = choose|t: Seq<X>, a: Seq<E>, v: int| #[trigger] quorum_witness(p, x, q, t, a, v);
        guard_on_path(p, inv, g, t, a);
        let (r, i) = choose|r: Replica, i: int| q.contains(r) && 0 <= i<t.len() && #[trigger] (p.value)(t[i], r) == v;
        assert((m.value)(t[i], r) == v);
        assert(quorum_witness(m, x, q, t, a, v));
    }
    assert forall|t: Seq<X>, a: Seq<E>, q: Set<Replica>, v: int| #[trigger] first_answer(m, t, a, v)
        && reaches(m, t[0]) && (m.invoked)(t[0]) && majority(q) && #[trigger] (m.served_by)(t, a, q)
        implies member_during(m, t, q, v) by {
        guarded_reachability(p, inv, g, t[0]); reachable_invariant(p, inv, t[0]); guard_on_path(p, inv, g, t, a);
        assert(first_answer(p, t, a, v) && (p.served_by)(t, a, q));
        assert(member_during(p, t, q, v));
        let (r, i) = choose|r: Replica, i: int| q.contains(r) && 0 <= i<t.len() && #[trigger] (p.value)(t[i], r) == v;
        assert((m.value)(t[i], r) == v);
    }
}

}
