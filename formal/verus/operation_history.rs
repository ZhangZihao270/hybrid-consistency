// The preservation clause at the boundary between a guarded execution and
// a sequential object's methods. K identifies a call, including its arguments.
use vstd::prelude::*;
use crate::promotion_wait::{Path, Relation, valid_edges};
use crate::semantic_promotion as retention;

verus! {

// Observe one object component. Accesses can depend on the sequential
// pre-state. A multi-component method can be tested on each component.
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(V)]
pub struct Object<K,V,D> {
    pub initial: V,
    pub apply: spec_fn(K,V) -> (V,D),
    pub reads: spec_fn(K,V) -> bool,
    pub writes: spec_fn(K,V) -> bool,
    pub weak: spec_fn(K) -> bool,
}

pub struct Calls<K,D> { pub issued: Set<K>, pub replies: Map<K,D> }
pub struct Word<K,V> { pub ops: Seq<K>, pub states: Seq<V> }

// Keep completed strong calls in scope. Each included recorded response
// must agree with its method. No property requires the run to have a word.
pub open spec fn legal<K,V,D>(o: Object<K,V,D>, c: Calls<K,D>, h: Word<K,V>) -> bool {
    h.states.len() == h.ops.len() + 1 && h.states[0] == o.initial && h.ops.no_duplicates()
        && c.replies.dom().subset_of(c.issued)
        && (forall|k: K| #[trigger] c.replies.contains_key(k) && !(o.weak)(k) ==> h.ops.contains(k))
        && (forall|i: int| 0 <= i < h.ops.len() ==> {
            let k = #[trigger] h.ops[i]; let (post,d) = (o.apply)(k,h.states[i]);
            c.issued.contains(k) && h.states[i+1] == post && (c.replies.contains_key(k) ==> c.replies[k] == d)
        })
}

pub open spec fn observes<K,V,D>(o: Object<K,V,D>, h: Word<K,V>, call: K, w: K) -> bool {
    (o.weak)(w) && exists|i: int,j: int| 0 <= i < j < h.ops.len()
        && #[trigger] h.ops[i] == w && #[trigger] h.ops[j] == call
        && (o.writes)(w,h.states[i]) && (o.reads)(call,h.states[j])
        && forall|n: int| i < n < j ==> !(o.writes)(#[trigger] h.ops[n],h.states[n])
}

// An ambiguous earlier publication cannot be freely labelled with a writer.
pub open spec fn identified<K,V,D>(o: Object<K,V,D>, c: Calls<K,D>, producer: K, w: K) -> bool {
    c.replies.contains_key(producer) && c.issued.contains(w) && (o.weak)(w)
        && (exists|h: Word<K,V>| #[trigger] legal(o,c,h) && h.ops.contains(producer))
        && forall|h: Word<K,V>| #[trigger] legal(o,c,h) && h.ops.contains(producer) ==> observes(o,h,producer,w)
}

pub struct Question<K,D> { pub producer: K, pub consumer: K, pub background: Calls<K,D> }

// Hold fixed the surrounding invocations and recorded responses. Erase the
// producer's answer so the two tests differ only in the earlier read-from edge.
// Test the consumer's proposed decision by running its actual sequential method.
pub open spec fn question<K,D>(c: Calls<K,D>, producer: K, consumer: K) -> Question<K,D> {
    Question { producer, consumer, background: Calls { issued: c.issued, replies: c.replies.remove(producer).remove(consumer) } }
}

pub open spec fn supports<K,V,D>(o: Object<K,V,D>, q: Question<K,D>, w: K, d: D) -> bool {
    exists|h: Word<K,V>, i: int, j: int| #[trigger] legal(o,q.background,h) && observes(o,h,q.producer,w)
        && 0 <= i < j < h.ops.len() && #[trigger] h.ops[i] == q.producer && #[trigger] h.ops[j] == q.consumer
        && (o.apply)(q.consumer,h.states[j]).1 == d
}

// The operational interface fixes the reachable entries with their weak
// snapshot, guarded transitions, operation ledger and ordinary inputs. All
// possible decisions are computed from these transitions and publications.
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(A)]
#[verifier::reject_recursive_types(K)]
#[verifier::reject_recursive_types(R)]
#[verifier::reject_recursive_types(I)]
#[verifier::reject_recursive_types(E)]
#[verifier::reject_recursive_types(D)]
pub struct System<X,A,K,D,R,I,E> {
    pub entry: spec_fn(X,E,Seq<K>) -> bool,
    pub step: Relation<X,A>,
    pub quiet: spec_fn(X,A) -> bool,
    pub installer: spec_fn(X,A) -> bool,
    pub calls: spec_fn(X) -> Calls<K,D>,
    pub record: spec_fn(X) -> R,
    pub input: spec_fn(X,K,E) -> I,
    pub service_cut: spec_fn(X,K) -> bool,
    pub ordinary_input: spec_fn(X,K,A) -> bool,
}

pub struct Window<X,A,K,E> {
    pub service: Path<X,A>, pub handoff: Path<X,A>,
    pub producer: K, pub consumer: K, pub writer: K, pub evidence: E, pub weak_order: Seq<K>,
}

pub open spec fn segment<X,A>(step: Relation<X,A>, quiet: spec_fn(X,A) -> bool, p: Path<X,A>) -> bool {
    p.states.len() == p.actions.len()+1 && valid_edges(step,p)
        && forall|i: int| 0 <= i < p.actions.len() ==> quiet(p.states[i],#[trigger] p.actions[i])
}

// First publication for a fixed external workload, including publication
// at invocation. Each proposed successor must satisfy the real transition.
pub open spec fn finishes<X,A,K,D,R,I,E>(s: System<X,A,K,D,R,I,E>, x: X, k: K, t: Seq<(A,X)>, d: D) -> bool
    decreases t.len(),
{
    let calls=(s.calls)(x);
    calls.issued.contains(k) && if t.len()==0 { calls.replies.get(k)==Some(d) } else {
        let (a,y)=t[0];
        !calls.replies.contains_key(k) && (s.step)(x,a,y) && (s.ordinary_input)(x,k,a) && (s.quiet)(x,a)
            && (s.calls)(y).issued==calls.issued && finishes(s,y,k,t.drop_first(),d)
    }
}

pub open spec fn outcomes<X,A,K,D,R,I,E>(s: System<X,A,K,D,R,I,E>, x: X, k: K) -> ISet<D> {
    ISet::new(|d:D| exists|t:Seq<(A,X)>| #[trigger] finishes(s,x,k,t,d))
}

pub open spec fn genuine<X,A,K,V,D,R,I,E>(s: System<X,A,K,D,R,I,E>, o: Object<K,V,D>, t: Window<X,A,K,E>) -> bool {
    let p = t.service; let z = p.states.last(); let cut = t.handoff.states.last();
    let a = t.producer; let b = t.consumer; let before = (s.calls)(z); let after = (s.calls)(cut);
    (s.entry)(p.states[0],t.evidence,t.weak_order) && segment(s.step,s.quiet,p) && segment(s.step,s.quiet,t.handoff)
        && t.handoff.states[0] == z && a != b && !(o.weak)(a) && !(o.weak)(b)
        && (s.calls)(p.states[0]).issued.contains(a) && !(s.calls)(p.states[0]).replies.contains_key(a) && before.issued.contains(a)
        && t.weak_order.no_duplicates() && (forall|i: int| 0 <= i < t.weak_order.len() ==> {
            let k = #[trigger] t.weak_order[i]; (o.weak)(k) && (s.calls)(p.states[0]).issued.contains(k)
        })
        && (forall|i: int| 0 <= i < p.actions.len() ==> {
            let c=(s.calls)(#[trigger] p.states[i]); c.issued.contains(a) && !c.replies.contains_key(a) && !c.issued.contains(b)
        })
        && !before.issued.contains(b) && after.issued.contains(b)
        && (forall|i: int| 0 <= i < t.handoff.actions.len() ==> !(s.calls)(#[trigger] t.handoff.states[i]).issued.contains(b))
        && before.issued.subset_of(after.issued) && before.replies.remove(a).submap_of(after.replies)
        && identified(o,before,a,t.writer)
        && (s.service_cut)(cut,b)
}

pub open spec fn observation<X,A,K,D,R,I,E>(s: System<X,A,K,D,R,I,E>, t: Window<X,A,K,E>)
    -> retention::Episode<K,Question<K,D>,R,I> {
    let p = t.service; let cut = t.handoff.states.last();
    retention::Episode { writer: t.writer, position: question((s.calls)(cut),t.producer,t.consumer),
        weak_order: t.weak_order, input: (s.input)(cut,t.consumer,t.evidence),
        entry: (s.record)(p.states[0]), exit: (s.record)(p.states.last()), inherited: (s.record)(cut),
        ordinary_edges: retention::ordinary_edges(s.record,s.installer,p) }
}

// A projection suffices only if it determines the full ordinary service
// across all cuts in its operational domain, including other schedules.
pub open spec fn determined_by_record<X,A,K,D,R,I,E>(s: System<X,A,K,D,R,I,E>, k: K) -> bool {
    forall|x: X,y: X,e: E,f: E| (s.service_cut)(x,k) && (s.service_cut)(y,k) && (s.record)(x)==(s.record)(y)
        && #[trigger] (s.input)(x,k,e)==#[trigger] (s.input)(y,k,f) ==> outcomes(s,x,k)==outcomes(s,y,k)
}

// The same operation question and other receipts, with independently
// computed returning traces. No external predicate chooses their outcomes.
pub open spec fn operation_t<X,A,K,V,D,R,I,E>(s: System<X,A,K,D,R,I,E>, o: Object<K,V,D>) -> bool {
    forall|a: Window<X,A,K,E>, b: Window<X,A,K,E>| #[trigger] genuine(s,o,a) && #[trigger] genuine(s,o,b) ==> {
        let x = observation(s,a); let y = observation(s,b);
        a.evidence == b.evidence && x.position == y.position && determined_by_record(s,a.consumer) ==> !retention::unsupported_outcomes(x,y,
            outcomes(s,a.handoff.states.last(),a.consumer),outcomes(s,b.handoff.states.last(),b.consumer),
            |q: Question<K,D>,w: K,d: D| supports(o,q,w,d))
    }
}


// A record-independent selector satisfies the law even if both genuine
// windows have weak sources, records change, and ordinary service returns.
pub proof fn independent_service_satisfies_t<X,A,K,V,D,R,I,E>(s: System<X,A,K,D,R,I,E>, o: Object<K,V,D>)
    requires forall|k: K,x: X,y: X,e: E,f: E| (s.service_cut)(x,k) && (s.service_cut)(y,k)
        && #[trigger] (s.input)(x,k,e)==#[trigger] (s.input)(y,k,f) ==> outcomes(s,x,k)==outcomes(s,y,k),
    ensures operation_t(s,o),
{
    assert forall|a: Window<X,A,K,E>, b: Window<X,A,K,E>| #[trigger] genuine(s,o,a) && #[trigger] genuine(s,o,b) implies {
        let x = observation(s,a); let y = observation(s,b);
        a.evidence == b.evidence && x.position == y.position && determined_by_record(s,a.consumer) ==> !retention::unsupported_outcomes(x,y,
            outcomes(s,a.handoff.states.last(),a.consumer),outcomes(s,b.handoff.states.last(),b.consumer),
            |q: Question<K,D>,w: K,d: D| supports(o,q,w,d))
    } by {
        let x=observation(s,a); let y=observation(s,b);
        if x.position==y.position && x.input==y.input {
            assert(a.consumer==b.consumer);
            assert(outcomes(s,a.handoff.states.last(),a.consumer)==outcomes(s,b.handoff.states.last(),b.consumer));
        }
    }
}

// With no weak operations in the object's vocabulary every strong service
// is allowed, including protocols that retain and consult earlier replies.
pub proof fn strong_only_object_satisfies_t<X,A,K,V,D,R,I,E>(s: System<X,A,K,D,R,I,E>, o: Object<K,V,D>)
    ensures operation_t(s,Object { weak: |_k:K| false, ..o }),
{
    let strong=Object { weak: |_k:K| false, ..o };
    assert forall|a: Window<X,A,K,E>| !#[trigger] genuine(s,strong,a) by {
        assert(!(strong.weak)(a.writer));
    }
}

}
