// BEGIN MODULE: coupled_reads
pub mod coupled_reads {
    use vstd::prelude::*;
    use crate::Op;

    verus! {

    pub open spec fn legal_returns(v:int,w:int) -> bool {
        exists|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,v,w)
    }
    }
}
// END MODULE: coupled_reads

// BEGIN MODULE: information_flow
pub mod information_flow {
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
}
// END MODULE: information_flow

// BEGIN MODULE: order_extension
pub mod order_extension {
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
}
// END MODULE: order_extension

// BEGIN MODULE: precedence
pub mod precedence {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::checkpoint::*;
    use crate::delivery::*;

    verus! {

    // An independent order currently places preferred after the rival, or
    // includes preferred while omitting the rival. A particular order need
    // not impose any preference between these two versions.
    pub open spec fn has_precedence<V>(order: Seq<V>, preferred: V, rival: V) -> bool {
        preferred != rival && exists|i: int| 0 <= i < order.len() && #[trigger] order[i] == preferred
            && (forall|j: int| i < j < order.len() ==> #[trigger] order[j] != rival)
    }

    pub struct IndependentView {
        pub cells: (int, int),
        pub left: Control,
        pub right: Control,
    }

    pub open spec fn independent_view(b: Fork) -> IndependentView {
        IndependentView {
            cells: survivor(checkpoint_end(b)),
            left: checkpoint_control(b, at(Replica::R1)),
            right: checkpoint_control(b, at(Replica::R2)),
        }
    }

    }
}
// END MODULE: precedence

// BEGIN MODULE: semantic_promotion
pub mod semantic_promotion {
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
}
// END MODULE: semantic_promotion

// BEGIN MODULE: operation_history
pub mod operation_history {
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
}
// END MODULE: operation_history

// BEGIN MODULE: register_history
pub mod register_history {
    // Instantiate the operation/history rule at the existing register boundary.
    use vstd::prelude::*;
    use crate::{Op, RecoveredOrder, checkpoint::*, delivery::*};
    use crate::async_fork as af;
    use crate::async_messages::{self as net, Headers};
    use crate::first_assembly as asm;
    use crate::first_mailbox as mail;
    use crate::independent_preparations as prep;
    use crate::independent_read::{self as read, State};
    use crate::native_fork as fork;
    use crate::operation_history::{self as op, Calls, Object, Question, System, Word};
    use crate::order_extension as order;
    use crate::original_application as app;
    use crate::precedence::IndependentView;
    use crate::promotion_wait::Path;
    use crate::read_call::{Event,Program};
    use crate::semantic_promotion as old;

    verus! {

    pub open spec fn register() -> Object<Op,int,int> {
        Object { initial: 1, apply: |k: Op,v: int| (crate::next(k,v),v),
            reads: |_k: Op,_v: int| true, writes: |k: Op,_v: int| order::weak(k), weak: |k: Op| order::weak(k) }
    }

    pub open spec fn weak_calls() -> Set<Op> { set![Op::W1,Op::W2] }
    pub open spec fn weak_replies() -> Map<Op,int> {
        let end = crate::guarded_history::weak_end();
        Map::new(weak_calls(), |k: Op| end.answers[crate::weak_round::request(k).id])
    }

    pub open spec fn ledger<S>(m: Program<S>, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>, x: State<S>) -> Calls<Op,int> {
        let c1 = !x.first_requested.is_empty(); let c2 = x.cfg.net.second_started;
        let issued = if c1 { weak_calls().insert(Op::SR1) } else { weak_calls() };
        let replies = if c1 && mail::posted(m)(x) {
            weak_replies().insert(Op::SR1,first((x.cfg.private)(Process::FirstClient)))
        } else { weak_replies() };
        let d = res(crate::fork_information::caller2(x));
        Calls { issued: if c2 { issued.insert(Op::SR2) } else { issued },
            replies: if c2 && d.is_some() { replies.insert(Op::SR2,d.unwrap()) } else { replies } }
    }

    pub open spec fn background() -> Calls<Op,int> {
        Calls { issued: weak_calls().insert(Op::SR1).insert(Op::SR2), replies: weak_replies() }
    }
    pub open spec fn contest() -> Question<Op,int> {
        Question { producer: Op::SR1, consumer: Op::SR2, background: background() }
    }
    pub open spec fn publication(b: Fork) -> Calls<Op,int> {
        Calls { issued: weak_calls().insert(Op::SR1), replies: weak_replies().insert(Op::SR1,first_value(b)) }
    }
    spec fn word(h: RecoveredOrder) -> Word<Op,int> { Word { ops: h.ops, states: h.states } }
    spec fn recovery(h: Word<Op,int>) -> RecoveredOrder { RecoveredOrder { ops: h.ops, states: h.states } }

    proof fn actual_weak_answers(b: Fork)
        ensures weak_replies() == map![Op::W1 => 1int, Op::W2 => 1int],
    {
        crate::weak_round::actual_overlap(b);
        assert(weak_replies() =~= map![Op::W1 => 1int, Op::W2 => 1int]);
    }

    proof fn source_agrees(h: Word<Op,int>, reader: Op, w: Op)
        ensures op::observes(register(),h,reader,w) == order::reads_from(h.ops,reader,w),
    {}

    pub(crate) proof fn earlier_source(b: Fork)
        ensures op::identified(register(),publication(b),Op::SR1,observed_writer(b)),
    {
        let obj = register(); let c = publication(b); let w = observed_writer(b);
        let h = word(order::at_first(b));
        actual_weak_answers(b); order::canonical_orders_exist(b); order::canonical_extension(b);
        assert(op::legal(obj,c,h)) by {
            assert forall|i: int| 0 <= i < h.ops.len() implies {
                let k = #[trigger] h.ops[i]; c.issued.contains(k) && h.states[i+1] == crate::next(k,h.states[i])
                    && (c.replies.contains_key(k) ==> c.replies[k] == h.states[i])
            } by { assert(i == 0 || i == 1); }
        }
        assert forall|g: Word<Op,int>| #[trigger] op::legal(obj,c,g) && g.ops.contains(Op::SR1)
            implies op::observes(obj,g,Op::SR1,w) by {
            if g.ops.contains(Op::SR2) { let i = choose|i: int| 0 <= i < g.ops.len() && g.ops[i] == Op::SR2;
                assert(c.issued.contains(g.ops[i])); }
            assert(order::legal_first(recovery(g),first_value(b)));
            order::exact_first_order(b,recovery(g)); source_agrees(g,Op::SR1,w);
        }
    }

    // Only one recorded RMW fits. After its unique occurrence all remaining
    // operations are reads and the register keeps that RMW's post-state.
    proof fn state_after_source(h: Word<Op,int>, w: Op, i: int, j: int)
        requires op::legal(register(),background(),h), 0 <= i < j < h.ops.len(), h.ops[i] == w, order::weak(w),
            crate::legal_recovery(recovery(h)), !h.ops.contains(crate::information_flow::rival(w)),
        ensures h.states[j] == crate::next(w,1),
        decreases j-i,
    {
        if i+1 < j {
            state_after_source(h,w,i,j-1);
            assert(h.ops[j-1] != w);
            if h.ops[j-1] == crate::information_flow::rival(w) { assert(h.ops.contains(h.ops[j-1])); }
            assert(!order::weak(h.ops[j-1]));
            assert(h.states[j] == crate::next(h.ops[j-1],h.states[j-1]));
        } else {
            assert(h.states[i] == 1 && h.states[i+1] == crate::next(w,h.states[i]));
        }
    }

    // Equality for every proposed outcome, including values no replica holds.
    // Neither actual SR2 return nor H occurs among the premises.
    pub proof fn register_question_is_exact(b: Fork, d: int)
        ensures op::supports(register(),contest(),observed_writer(b),d)
            == old::keeps_value()(order::at_first(b).ops,observed_writer(b),d),
    {
        let obj = register(); let q = contest(); let w = observed_writer(b); let p = order::at_first(b);
        actual_weak_answers(b); order::canonical_orders_exist(b); order::canonical_extension(b);
        order::extension_iff_writer(b,p,w);
        if old::keeps_value()(p.ops,w,d) {
            let v = choose|v: Op| order::weak(v) && d == crate::next(v,1) && #[trigger] order::can_keep(p.ops,w,v);
            order::extension_iff_writer(b,p,v);
            let h = word(order::at_second(b));
            source_agrees(h,Op::SR1,w);
            assert(op::legal(obj,q.background,h)) by {
                assert forall|i: int| 0 <= i < h.ops.len() implies {
                    let k = #[trigger] h.ops[i]; q.background.issued.contains(k) && h.states[i+1] == crate::next(k,h.states[i])
                        && (q.background.replies.contains_key(k) ==> q.background.replies[k] == h.states[i])
                } by { assert(i == 0 || i == 1 || i == 2); }
            }
            assert(h.ops[1] == Op::SR1 && h.ops[2] == Op::SR2 && h.states[2] == d);
        } else if op::supports(obj,q,w,d) {
            let (h,i,j) = choose|h: Word<Op,int>,i: int,j: int| #[trigger] op::legal(obj,q.background,h)
                && op::observes(obj,h,q.producer,w) && 0 <= i < j < h.ops.len()
                && #[trigger] h.ops[i] == q.producer && #[trigger] h.ops[j] == q.consumer
                && (obj.apply)(q.consumer,h.states[j]).1 == d;
            source_agrees(h,Op::SR1,w);
            let (u,v) = choose|u: int,v: int| 0 <= u < v < h.ops.len() && #[trigger] h.ops[u] == w
                && #[trigger] h.ops[v] == Op::SR1 && forall|n: int| u < n < v ==> !order::weak(#[trigger] h.ops[n]);
            assert(v == i && h.ops.contains(w));
            assert(crate::legal_recovery(recovery(h)));
            if h.ops.contains(crate::information_flow::rival(w)) { crate::recovered_order_cannot_keep_both_rmws(recovery(h)); }
            state_after_source(h,w,u,j);
            assert(old::keeps_value()(p.ops,w,d));
        }
    }

    pub type Runtime<S> = System<State<S>,Event,Op,int,af::View<S>,old::Input<S>,IndependentView>;

    // Entries may follow any guarded, weak-free preparation after the original
    // weak prefix. The only constraints on the two later intervals are the
    // generic operation-window tests and the native transition guards.
    pub open spec fn weak_entry<S>(p: Program<S>, k: Headers, b: Fork, assigned: bool, x: State<S>, tail: Path<State<S>,Event>) -> bool {
        let raw = net::implementation(k,p); let m = af::after_offers(p,k);
        let start = prep::before_offers(raw,app::lanes()); let lead = prep::offers()+asm::boot(Some(b));
        asm::prefix(raw,start,lead,true) && truthful_notice(b,weak_assignment(b,assigned).ops)
            && tail.states[0] == asm::drive(raw,start,lead) && tail.states.last() == x
            && op::segment(native_step(m),quiet(),tail)
    }
    pub open spec fn native_step<S>(m: Program<S>) -> crate::promotion_wait::Relation<State<S>,Event> {
        |x: State<S>,a: Event,y: State<S>| asm::prefix(m,x,seq![a],true) && y == read::next(m,x,a)
    }
    pub open spec fn quiet<S>() -> spec_fn(State<S>,Event) -> bool {
        |x: State<S>,a: Event| !app::weak_replica_step()(x,a,x)
    }

    pub open spec fn system<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>) -> Runtime<S> {
        let m = af::after_offers(p,k);
        System {
            entry: |x: State<S>, e: IndependentView, o: Seq<Op>| exists|b: Fork,f: bool,tail: Path<State<S>,Event>|
                #[trigger] weak_entry(p,k,b,f,x,tail) && e == crate::precedence::independent_view(b) && o == weak_assignment(b,f).ops,
            step: native_step(m), quiet: quiet(),
            installer: old::ordinary_replica(k),
            calls: |x: State<S>| ledger(m,first,res,x), record: |x: State<S>| af::view(k,x),
            input: |x: State<S>,_b: Op,e: IndependentView| old::input(e,x),
            service_cut: |x: State<S>,b: Op| b==Op::SR2 && crate::survivors::after_crash(x.cfg.net),
            ordinary_input: |x: State<S>,b: Op,a: Event| b==Op::SR2 && crate::survivors::after_crash(x.cfg.net)
                && !crate::guarded_comparison::weak_work(process_step(x.cfg.net,a)),
        }
    }

    pub(crate) proof fn native_to_window_return<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
        x:State<S>,s:Seq<Event>,d:int) -> (t:Seq<(Event,State<S>)>)
        requires crate::survivors::after_crash(x.cfg.net), fork::completes(net::implementation(k,p),res,x,s,true),
            fork::value(net::implementation(k,p),res,x,s)==Some(d),
        ensures op::finishes(system(p,k,first,res),x,Op::SR2,t,d),
        decreases s.len(),
    {
        let raw=net::implementation(k,p); let sys=system(p,k,first,res);
        if s.len()==0 { seq![] } else {
            let a=s[0]; let y=read::next(raw,x,a);
            assert(a!=Action::StopFirstClient && crate::survivors::after_crash(y.cfg.net) && y.first_requested==x.first_requested);
            assert((sys.step)(x,a,y)) by { reveal_with_fuel(asm::prefix,2); }
            let tail=native_to_window_return(p,k,first,res,y,s.drop_first(),d);
            let t=seq![(a,y)]+tail; assert(t.drop_first() =~= tail); t
        }
    }

    pub(crate) proof fn window_to_native_return<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
        x:State<S>,t:Seq<(Event,State<S>)>,d:int) -> (s:Seq<Event>)
        requires crate::survivors::after_crash(x.cfg.net), op::finishes(system(p,k,first,res),x,Op::SR2,t,d),
        ensures fork::completes(net::implementation(k,p),res,x,s,true), fork::value(net::implementation(k,p),res,x,s)==Some(d),
        decreases t.len(),
    {
        if t.len()==0 { seq![] } else {
            let (a,y)=t[0]; let m=af::after_offers(p,k);
            assert(asm::prefix(m,x,seq![a],true));
            assert(a!=Action::StopFirstClient && read::prefix_step(m)(x,a,y)) by { reveal(asm::prefix); }
            assert(crate::survivors::after_crash(y.cfg.net));
            let tail=window_to_native_return(p,k,first,res,y,t.drop_first(),d);
            let s=seq![a]+tail; assert(s.drop_first() =~= tail); s
        }
    }

    pub(crate) proof fn wake_segment<S>(m: Program<S>, z: State<S>)
        requires asm::prefix(m,z,crate::fork_alternatives::wake(),true),
        ensures ({
            let a=crate::fork_alternatives::wake(); let h=Path {states: fork::states(m,z,a), actions: a};
            op::segment(native_step(m),quiet(),h) && h.states[0] == z && h.states.last() == asm::drive(m,z,a)
        }),
    {
        let a=crate::fork_alternatives::wake(); let states=fork::states(m,z,a);
        assert(a.take(0) =~= seq![] && a.take(a.len() as int) =~= a);
        assert forall|i: int| 0 <= i < a.len() implies native_step(m)(states[i],#[trigger] a[i],states[i+1])
            && quiet()(states[i],a[i]) by {
            assert(i==0 || i==1 || i==2);
            let head=a.take(i); let one=seq![a[i]]; let tail=a.skip(i+1);
            assert(head+one+tail =~= a && head+one =~= a.take(i+1));
            asm::prefix_concat(m,z,head+one,tail,true); asm::prefix_concat(m,z,head,one,true);
            assert(asm::drive(m,states[i],one)==read::next(m,states[i],a[i])) by { reveal_with_fuel(asm::drive,2); }
        }
    }

    }
}
// END MODULE: register_history
