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
