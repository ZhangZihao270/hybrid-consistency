// Instantiate the operation/history rule at the existing register boundary.
use vstd::prelude::*;
use crate::{Branch, Op, RecoveredOrder, Replica, checkpoint::*, delivery::*};
use crate::async_fork as af;
use crate::async_messages::{self as net, Headers};
use crate::first_assembly as asm;
use crate::first_mailbox as mail;
use crate::first_splice as tape;
use crate::independent_preparations as prep;
use crate::independent_read::{self as read, State};
use crate::native_fork::{self as fork, ReadPair};
use crate::operation_history::{self as op, Calls, Object, Question, System, Window, Word};
use crate::order_extension as order;
use crate::original_application as app;
use crate::precedence::IndependentView;
use crate::promotion_wait::Path;
use crate::read_call::{Event,Program};
use crate::semantic_promotion::{self as old, Trial};

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
pub type NativeWindow<S> = Window<State<S>,Event,Op,IndependentView>;

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

pub proof fn actual_window_outcomes<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    x:State<S>,e:IndependentView)
    requires crate::survivors::after_crash(x.cfg.net),
    ensures op::outcomes(system(p,k,first,res),x,Op::SR2)==old::readout(p,k,res)(old::input(e,x),af::view(k,x)),
{
    let sys=system(p,k,first,res); let r=old::readout(p,k,res)(old::input(e,x),af::view(k,x)); let a=op::outcomes(sys,x,Op::SR2);
    old::readout_is_exact(p,k,res,x,e);
    assert forall|d:int| #[trigger] a.contains(d)==#[trigger] r.contains(d) by {
        if r.contains(d) && !a.contains(d) {
            let s=old::realize_decision(p,k,res,x,d);
            let t=native_to_window_return(p,k,first,res,x,s,d);
            assert(op::finishes(sys,x,Op::SR2,t,d));
        } else if a.contains(d) && !r.contains(d) {
            let t=choose|t:Seq<(Event,State<S>)>| #[trigger] op::finishes(sys,x,Op::SR2,t,d);
            let s=window_to_native_return(p,k,first,res,x,t,d);
            assert(fork::completes(net::implementation(k,p),res,x,s,true));
        }
    }
    assert(a =~= r);
}

pub proof fn record_determines_service<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    ensures op::determined_by_record(system(p,k,first,res),Op::SR2),
{
    let sys=system(p,k,first,res); let b=Op::SR2;
    assert forall|x: State<S>,y: State<S>,e: IndependentView,f: IndependentView|
        (sys.service_cut)(x,b) && (sys.service_cut)(y,b) && (sys.record)(x)==(sys.record)(y)
        && #[trigger] (sys.input)(x,b,e)==#[trigger] (sys.input)(y,b,f) implies op::outcomes(sys,x,b)==op::outcomes(sys,y,b) by {
        actual_window_outcomes(p,k,first,res,x,e); actual_window_outcomes(p,k,first,res,y,f);
    }
}

pub open spec fn window<S>(m: Program<S>, t: Trial<S>) -> NativeWindow<S> {
    let p = t.path.first; let z = p.states.last(); let wake = crate::fork_alternatives::wake();
    Window { service: p, handoff: Path { states: fork::states(m,z,wake), actions: wake },
        producer: Op::SR1, consumer: Op::SR2, writer: observed_writer(t.arm),
        evidence: crate::precedence::independent_view(t.arm), weak_order: weak_assignment(t.arm,t.assigned).ops }
}

// Recover both physical boundaries from the completed trace itself. The
// computation of the boot endpoint needs no hypothetical client guard.
proof fn boundaries<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>, t: Trial<S>)
    requires old::reached(p,k,first,res,t),
    ensures ({
        let m=af::after_offers(p,k); let s=t.path.first; let x=s.states[0]; let z=s.states.last();
        weak_entry(p,k,t.arm,t.assigned,x,Path { states: seq![x], actions: seq![] })
            && asm::prefix(m,z,crate::fork_alternatives::wake(),true)
    }),
{
    let raw=net::implementation(k,p); let m=af::after_offers(p,k); let l=app::lanes();
    let start=prep::before_offers(raw,l); let offers=prep::offers(); let s=t.path.first; let b=t.arm;
    let boot=asm::boot(Some(b)); let wake=crate::fork_alternatives::wake();
    let pre=boot+s.actions; let rest=wake+t.path.second;
    asm::prefix_concat(raw,start,offers,pre+rest,true);
    assert(crate::ordinary_service::allowed(raw,start.cfg,offers[0])
        && crate::ordinary_service::allowed(raw,read::next(raw,start,offers[0]).cfg,offers[1])) by {
        reveal_with_fuel(asm::prefix,3);
    }
    prep::shared_weak_entry(raw,l,b);
    let entry=asm::entry(m,l);
    prep::rebase_preserves_steps(raw,l,entry,pre+rest);
    asm::prefix_concat(m,entry,pre,rest,true); asm::prefix_concat(m,entry,boot,s.actions,true);
    asm::boot_state(m,l,b); let root=s.states[0];
    tape::recorded(m,s,0); asm::native_prefix(m,root,tape::record(s,0),true);
    assert(asm::actions(tape::record(s,0)) =~= s.actions);
    assert(asm::drive(m,entry,pre) == s.states.last());
    asm::prefix_concat(m,s.states.last(),wake,t.path.second,true);
    prep::rebase_preserves_steps(raw,l,entry,boot); asm::prefix_concat(raw,start,offers,boot,true);
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

// Only the position's vocabulary changes from the old concrete test.
spec fn with_question<S>(a: old::Observation<S>) -> old::Episode<Op,Question<Op,int>,af::View<S>,old::Input<S>> {
    old::Episode { writer:a.writer,position:contest(),weak_order:a.weak_order,input:a.input,
        entry:a.entry,exit:a.exit,inherited:a.inherited,ordinary_edges:a.ordinary_edges }
}

pub proof fn trial_is_genuine<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>,
    t: Trial<S>)
    requires old::reached(p,k,first,res,t),
    ensures ({
        let w=window(af::after_offers(p,k),t); let sys=system(p,k,first,res);
        op::genuine(sys,register(),w) && op::observation(sys,w).position==contest()
    }),
{
    let m=af::after_offers(p,k); let sys=system(p,k,first,res); let w=window(m,t);
    let s=t.path.first; let entry=s.states[0]; let z=s.states.last(); let x=fork::invocation(m,s);
    boundaries(p,k,first,res,t); wake_segment(m,z);
    assert((sys.entry)(entry,w.evidence,w.weak_order)) by {
        let empty=Path {states:seq![entry],actions:Seq::<Event>::empty()};
        assert(weak_entry(p,k,t.arm,t.assigned,entry,empty));
    }
    assert forall|j: int| 0<=j<s.actions.len() implies native_step(m)(s.states[j],#[trigger] s.actions[j],s.states[j+1])
        && quiet()(s.states[j],s.actions[j]) by {
        let a=s.actions[j]; let v=s.states[j];
        assert(mail::active_step(m)(v,a,s.states[j+1]) && !mail::posted(m)(v));
        assert(!app::weak_replica_step()(v,a,s.states[j+1]));
        assert(a!=Action::StopFirstClient && read::initial_send(v,a));
        assert(asm::prefix(m,v,seq![a],true)) by { reveal_with_fuel(asm::prefix,2); }
    }
    fork::first_frame(m,first,t.arm,s,0); fork::first_frame(m,first,t.arm,s,s.actions.len());
    assert forall|j:int| 0<=j<s.actions.len() implies {
        let c=ledger(m,first,res,#[trigger] s.states[j]);
        c.issued.contains(Op::SR1) && !c.replies.contains_key(Op::SR1) && !c.issued.contains(Op::SR2)
    } by {
        fork::first_frame(m,first,t.arm,s,j as nat);
        assert(!mail::posted(m)(s.states[j]));
    }
    assert(s.states[s.actions.len() as int]==z && !z.cfg.net.second_started);
    assert(ledger(m,first,res,z)==publication(t.arm));
    assert(w.handoff.states.last()==x && !x.first_requested.is_empty()) by {
        let a=crate::fork_alternatives::wake();
        reveal_with_fuel(asm::drive,4);
    }
    assert forall|j:int| 0<=j<w.handoff.actions.len() implies
        !ledger(m,first,res,#[trigger] w.handoff.states[j]).issued.contains(Op::SR2) by {
        assert(j==0 || j==1 || j==2); reveal_with_fuel(asm::drive,3);
    }
    assert(op::question(ledger(m,first,res,x),Op::SR1,Op::SR2)==contest()) by {
        let q=op::question(ledger(m,first,res,x),Op::SR1,Op::SR2);
        assert(q.background.replies =~= weak_replies());
    }
    earlier_source(t.arm); weak_assignment_at_delivery(t.arm,t.assigned);
}

proof fn same_carrier<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>, t: Trial<S>)
    requires old::reached(p,k,first,res,t),
    ensures op::observation(system(p,k,first,res),window(af::after_offers(p,k),t))==with_question(old::observe(p,k,t)),
{
    hide(old::ordinary_edges); hide(af::view); hide(op::genuine);
    let m=af::after_offers(p,k); let w=window(m,t);
    trial_is_genuine(p,k,first,res,t);
    assert(w.handoff.states.last()==fork::invocation(m,t.path.first)) by { let h=crate::fork_alternatives::wake(); assert(h.take(h.len() as int) =~= h); }
}

proof fn transfer_test<S>(a: old::Observation<S>, b: old::Observation<S>,
    later: spec_fn(old::Input<S>,af::View<S>)->ISet<int>, l: Fork, r: Fork)
    requires a.writer==observed_writer(l), b.writer==observed_writer(r),
        a.position==order::at_first(l).ops, b.position==order::at_first(r).ops,
    ensures old::unsupported_choice(a,b,later,old::keeps_value()) ==> old::unsupported_choice(with_question(a),with_question(b),
        later,|q:Question<Op,int>,w:Op,d:int| op::supports(register(),q,w,d)),
{
    hide(op::supports); hide(old::keeps_value);
    if old::unsupported_choice(a,b,later,old::keeps_value()) {
        let choice=old::keeps_value();
        let d=choose|v:int| #[trigger] later(a.input,a.inherited).contains(v)
            && choice(a.position,a.writer,v) && !choice(b.position,b.writer,v);
        register_question_is_exact(l,d); register_question_is_exact(r,d);
        let x=with_question(a); let y=with_question(b);
        let test=|q: Question<Op,int>,w: Op,d: int| op::supports(register(),q,w,d);
        if old::installed(a) {
            let prev=choose|r:af::View<S>| r!=a.exit && #[trigger] a.ordinary_edges.contains((r,a.exit));
            assert(prev!=x.exit && x.ordinary_edges.contains((prev,x.exit)));
            assert(old::installed(x));
        } else {
            assert(old::installed(b));
            let prev=choose|r:af::View<S>| r!=b.exit && #[trigger] b.ordinary_edges.contains((r,b.exit));
            assert(prev!=y.exit && y.ordinary_edges.contains((prev,y.exit)));
            assert(old::installed(y));
        }
        assert(old::retained_difference(x,y));
        assert(test(x.position,x.writer,d) && !test(y.position,y.writer,d));
        assert(exists|v:int| #[trigger] later(x.input,x.inherited).contains(v) && test(x.position,x.writer,v) && !test(y.position,y.writer,v));
        assert forall|v:int| #[trigger] later(a.input,b.inherited).contains(v) implies
            op::supports(register(),contest(),b.writer,v) && !op::supports(register(),contest(),a.writer,v) by {
            register_question_is_exact(l,v); register_question_is_exact(r,v);
        }
        assert(old::resolves(later(x.input,y.inherited),(y.position,y.writer),(x.position,x.writer),test));
        assert(old::unsupported_choice(x,y,later,test));
    }
}

pub proof fn operation_t_implies_register_t<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>)
    requires op::operation_t(system(p,k,first,res),register()),
    ensures old::register_t(p,k,first,res),
{
    hide(old::reached); hide(op::genuine); hide(op::supports); hide(old::unsupported_choice);
    let sys=system(p,k,first,res); let m=af::after_offers(p,k); let later=old::readout(p,k,res);
    let obs=|t:Trial<S>|old::observe(p,k,t);
    record_determines_service(p,k,first,res);
    assert forall|a:Trial<S>,b:Trial<S>| old::reached(p,k,first,res,a) && old::reached(p,k,first,res,b)
        implies !#[trigger] old::unsupported_choice(obs(a),obs(b),later,old::keeps_value()) by {
        let x=window(m,a); let y=window(m,b);
        trial_is_genuine(p,k,first,res,a); trial_is_genuine(p,k,first,res,b);
        same_carrier(p,k,first,res,a); same_carrier(p,k,first,res,b);
        let u=x.handoff.states.last(); let v=y.handoff.states.last();
        assert(crate::survivors::after_crash(u.cfg.net) && crate::survivors::after_crash(v.cfg.net)) by { reveal(op::genuine); }
        actual_window_outcomes(p,k,first,res,u,x.evidence); actual_window_outcomes(p,k,first,res,v,y.evidence);
        transfer_test(obs(a),obs(b),later,a.arm,b.arm);
        if old::unsupported_choice(obs(a),obs(b),later,old::keeps_value()) {
            assert(obs(a).input==obs(b).input) by { reveal(old::unsupported_choice); }
            assert(x.evidence==y.evidence);
            assert(!old::unsupported_outcomes(op::observation(sys,x),op::observation(sys,y),
                op::outcomes(sys,u,Op::SR2),op::outcomes(sys,v,Op::SR2),
                |q:Question<Op,int>,w:Op,d:int| op::supports(register(),q,w,d)));
            assert(old::unsupported_outcomes(with_question(obs(a)),with_question(obs(b)),
                op::outcomes(sys,u,Op::SR2),op::outcomes(sys,v,Op::SR2),
                |q:Question<Op,int>,w:Op,d:int| op::supports(register(),q,w,d))) by { reveal(old::unsupported_choice); }
        }
    }
}

// The transport enables both distinct-origin weak offers. What remains
// for a guarded implementation is exactly the two origin callbacks.
pub open spec fn origin_send_guards<S>(raw: Program<S>) -> bool {
    let x=prep::before_offers(raw,app::lanes()); let s=prep::offers();
    (raw.accept)((raw.initial)(at(Replica::R1)),process_step(x.cfg.net,s[0]))
        && (raw.accept)((raw.initial)(at(Replica::R2)),process_step(x.cfg.net,s[1]))
}

pub proof fn offers_need_only_origin_guards<S>(raw: Program<S>)
    ensures origin_send_guards(raw) == ({
        let x=prep::before_offers(raw,app::lanes()); let s=prep::offers();
        crate::ordinary_service::allowed(raw,x.cfg,s[0])
            && crate::ordinary_service::allowed(raw,read::next(raw,x,s[0]).cfg,s[1])
    }),
{
    origin_updates_are_actually_offered(); reveal(crate::protocol::memory);
}

// The client interface supplies enabled requests while pending. Whether
// any of them can publish is settled by invocation-time quorum sampling.
pub open spec fn construction_inputs<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, n: Notice, run: crate::fair_read::Runnable, aa: bool, ab: bool) -> bool {
    let raw=net::implementation(k,p); let m=af::after_offers(p,k);
    origin_send_guards(raw) && crate::first_dispatch::pending_fanout(m) && crate::first_schedule::startup(m)
        && (n!=Notice::Replication ==> aa && ab) && fork::original_opportunities(m,first,res,n,run)
        && forall|b: Fork| b.notice==n ==> #[trigger] crate::hybrid_majority::first_invocation_sampling(
            m,first,crate::first_schedule::reference(m,b,0))
            && mail::first_availability(m,run,crate::first_schedule::reached_in(m,b))
}

pub proof fn construction_gives_original_premises<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, n: Notice, run: crate::fair_read::Runnable, aa: bool, ab: bool)
    requires construction_inputs(p,k,first,res,n,run,aa,ab),
    ensures fork::original_premises(net::implementation(k,p),af::after_offers(p,k),first,res,n,run,aa,ab),
{
    let m=af::after_offers(p,k);
    offers_need_only_origin_guards(net::implementation(k,p));
    crate::hybrid_majority::invocation_a_keeps_fanout_pending(m,first,n);
    assert forall|b: Fork| b.notice==n implies
        #[trigger] crate::hybrid_majority::first_reference_a(m,first,res,b,run) by {
        crate::hybrid_majority::invocation_includes_submitted_sampling(m,first,res,crate::first_schedule::reference(m,b,0));
    }
}

pub open spec fn exercised<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>, t: Trial<S>) -> bool {
    let m=af::after_offers(p,k); let sys=system(p,k,first,res); let w=window(m,t); let x=w.handoff.states.last();
    old::reached(p,k,first,res,t) && op::genuine(sys,register(),w)
        && op::outcomes(sys,x,w.consumer).contains(fork::value(m,res,x,t.path.second).unwrap())
}

proof fn completed_trial_is_exercised<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>, t: Trial<S>)
    requires ({
        let m=af::after_offers(p,k); crate::first_schedule::startup(m)
            && fork::completed_history(net::implementation(k,p),m,first,res,t.arm,t.path)
            && af::public_history(p,k,t.arm,t.path) && truthful_notice(t.arm,weak_assignment(t.arm,t.assigned).ops)
    }),
    ensures exercised(p,k,first,res,t),
{
    let raw=net::implementation(k,p); let m=af::after_offers(p,k); let s=t.path.second; let w=window(m,t);
    let x=fork::invocation(m,t.path.first); let d=fork::value(m,res,x,s).unwrap();
    old::actual_origin(m,k,first,t); trial_is_genuine(p,k,first,res,t);
    assert(w.handoff.states.last()==x) by { let h=crate::fork_alternatives::wake(); assert(h.take(h.len() as int) =~= h); }
    af::same_started_machine(raw,m,res,x,s);
    let ret=native_to_window_return(p,k,first,res,x,s,d);
    assert(op::finishes(system(p,k,first,res),x,Op::SR2,ret,d));
}

// No T or history-safety law is needed to inhabit both windows with actual
// weak sources and nonempty ordinary service.
pub proof fn original_windows_are_exercised<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, n: Notice, run: crate::fair_read::Runnable, aa: bool, ab: bool) -> (trials: (Trial<S>,Trial<S>))
    requires construction_inputs(p,k,first,res,n,run,aa,ab),
    ensures trials.0.arm==alpha(n) && trials.1.arm==beta(n)
        && exercised(p,k,first,res,trials.0) && exercised(p,k,first,res,trials.1),
{
    construction_gives_original_premises(p,k,first,res,n,run,aa,ab);
    let (a,b)=af::original_async_application(p,k,first,res,n,run,aa,ab);
    let t=Trial {arm:alpha(n),assigned:aa,path:a}; let u=Trial {arm:beta(n),assigned:ab,path:b};
    completed_trial_is_exercised(p,k,first,res,t); completed_trial_is_exercised(p,k,first,res,u);
    (t,u)
}

pub proof fn original_hot_under_operation_t<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, n: Notice, run: crate::fair_read::Runnable, aa: bool, ab: bool) -> (histories: (ReadPair<S>,ReadPair<S>))
    requires construction_inputs(p,k,first,res,n,run,aa,ab), op::operation_t(system(p,k,first,res),register()),
    ensures ({
        let (a,b)=histories; let raw=net::implementation(k,p); let m=af::after_offers(p,k);
        fork::completed_history(raw,m,first,res,alpha(n),a) && af::public_history(p,k,alpha(n),a)
            && fork::completed_history(raw,m,first,res,beta(n),b) && af::public_history(p,k,beta(n),b)
            && (!fork::legal_history(m,first,res,a) || !fork::legal_history(m,first,res,b))
    }),
{
    construction_gives_original_premises(p,k,first,res,n,run,aa,ab);
    operation_t_implies_register_t(p,k,first,res);
    old::original_hot_under_functional_t(p,k,first,res,n,run,aa,ab)
}

}
