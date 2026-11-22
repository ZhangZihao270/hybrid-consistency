// Functional reading of the prohibition on preserving an observed weak position.
use vstd::prelude::*;
use crate::{Op, Replica, checkpoint::*, delivery::*, order_extension as history, precedence};
use crate::async_fork::{self as af, View};
use crate::async_messages::{self as net, Headers};
use crate::first_assembly as asm;
use crate::first_splice as tape;
use crate::fork_information::caller2;
use crate::independent_read::{Calls, State};
use crate::native_fork::{self as fork, ReadPair};
use crate::original_application as app;
use crate::read_call::Program;

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

pub open spec fn unsupported_choice<W,H,R,I,D>(a: Episode<W,H,R,I>, b: Episode<W,H,R,I>,
    later: spec_fn(I,R) -> ISet<D>, extends: spec_fn(H,W,D) -> bool) -> bool {
    unsupported_outcomes(a,b,later(a.input,a.inherited),later(a.input,b.inherited),extends)
}

// A necessary subclause of the functional interpretation. Fix one system's
// genuine episodes, current weak orders and legal object extensions. Vary the
// earlier strong operation histories and all later ordinary returning traces.
pub open spec fn functional_t<C,W,H,R,I,D>(reached: spec_fn(C) -> bool,
    observe: spec_fn(C) -> Episode<W,H,R,I>, later: spec_fn(I,R) -> ISet<D>, extends: spec_fn(H,W,D) -> bool) -> bool {
    forall|a: C, b: C| reached(a) && reached(b)
        ==> !#[trigger] unsupported_choice(observe(a), observe(b), later, extends)
}

// Restricting a system-wide law to any reached workload needs only the
// inclusion of its episodes, with the same observations and object semantics.
pub proof fn restrict_to_workload<C,W,H,R,I,D>(all: spec_fn(C) -> bool, workload: spec_fn(C) -> bool,
    observe: spec_fn(C) -> Episode<W,H,R,I>, later: spec_fn(I,R) -> ISet<D>, extends: spec_fn(H,W,D) -> bool)
    requires functional_t(all, observe, later, extends), forall|c: C| #[trigger] workload(c) ==> all(c),
    ensures functional_t(workload, observe, later, extends),
{}

// Concrete observations for the register. The record includes ordinary
// packets in flight. An application tag for the weak writer is unnecessary.
#[verifier::reject_recursive_types(S)]
pub struct Trial<S> { pub arm: Fork, pub assigned: bool, pub path: ReadPair<S> }
pub type Input<S> = (precedence::IndependentView, S, Calls, Set<Replica>, Set<Replica>);
pub type Observation<S> = Episode<Op,Seq<Op>,View<S>,Input<S>>;

pub open spec fn decisions<S>(p: Program<S>, res: spec_fn(S) -> Option<int>, x: net::Channel<S>) -> ISet<int> {
    ISet::new(|d: int| exists|ts: Seq<net::Turn>| #[trigger] net::quiet_return(p,res,x,ts)
        && res(caller2(net::end(p,x,ts).local)) == Some(d))
}

pub open spec fn keeps_value() -> spec_fn(Seq<Op>,Op,int) -> bool {
    |prefix: Seq<Op>, w: Op, d: int| exists|v: Op| history::weak(v) && d == crate::next(v,1)
        && #[trigger] history::can_keep(prefix,w,v)
}

pub open spec fn input<S>(e: precedence::IndependentView, x: State<S>) -> Input<S> {
    (e,caller2(x),x.calls,x.requested,x.first_requested)
}

// The resolver has no argument for the prior writer, history, or schedule.
// The union over representatives is exact on EACH post-crash cut by replay.
pub open spec fn readout<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>)
    -> spec_fn(Input<S>,View<S>) -> ISet<int> {
    |i: Input<S>, r: View<S>| ISet::new(|d: int| exists|x: State<S>, s: Seq<crate::read_call::Event>|
        crate::survivors::after_crash(x.cfg.net) && input(i.0,x) == i && af::view(k,x) == r
        && #[trigger] fork::completes(net::implementation(k,p),res,x,s,true)
        && fork::value(net::implementation(k,p),res,x,s) == Some(d))
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

pub open spec fn observe<S>(p: Program<S>, k: Headers, t: Trial<S>) -> Observation<S> {
    let s = t.path.first; let x = fork::invocation(af::after_offers(p,k), s);
    Episode {
        writer: observed_writer(t.arm), position: history::at_first(t.arm).ops,
        weak_order: weak_assignment(t.arm,t.assigned).ops,
        input: input(precedence::independent_view(t.arm),x),
        entry: af::view(k,s.states[0]), exit: af::view(k,s.states.last()), inherited: af::view(k,x),
        ordinary_edges: ordinary_edges(|x:State<S>| af::view(k,x),ordinary_replica(k),s),
    }
}

// Authenticate the earlier strong observation against the actual weak receipt
// before fanout, the earlier client's publication, and the recorded weak RMWs.
pub open spec fn observed_position<S>(m: Program<S>, k: Headers, first: spec_fn(S) -> int, t: Trial<S>) -> bool {
    let b = t.arm; let w = observed_writer(b); let h = history::at_first(b);
    let v = first((t.path.first.states.last().cfg.private)(Process::FirstClient));
    let x = asm::entry(m,app::lanes()); let a = asm::boot(Some(b))[0];
    let e = net::callback(k,process_step(x.cfg.net,a));
    let owner = if w == Op::W1 { Replica::R1 } else { Replica::R2 };
    e.actor == at(Replica::R3) && e.action is Deliver
        && e.incoming == Some(Packet { path: Path::Weak, from: at(owner), to: at(Replica::R3), input: Wire::Copy(v) })
        && (t.path.first.states[0].cfg.net.locals)(Replica::R3) == v
        && history::weak(w) && v == crate::next(w,1)
        && (forall|u: Op| history::weak(u) && #[trigger] crate::next(u,1) == v ==> u == w)
        && history::legal_first(h,v) && history::reads_from(h.ops,Op::SR1,w)
}

pub open spec fn reached<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>,
    t: Trial<S>) -> bool {
    let m = af::after_offers(p,k);
    fork::completed_history(net::implementation(k,p),m,first,res,t.arm,t.path)
        && af::public_history(p,k,t.arm,t.path) && truthful_notice(t.arm,weak_assignment(t.arm,t.assigned).ops)
        && observed_position(m,k,first,t)
}

pub open spec fn register_t<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>) -> bool {
    functional_t(|t: Trial<S>| reached(p,k,first,res,t), |t: Trial<S>| observe(p,k,t), readout(p,k,res), keeps_value())
}

pub(crate) proof fn actual_origin<S>(m: Program<S>, k: Headers, first: spec_fn(S) -> int, t: Trial<S>)
    requires fork::admitted(m,first,t.arm,t.path.first), crate::first_schedule::startup(m),
    ensures observed_position(m,k,first,t), ({
        let x = fork::invocation(m,t.path.first);
        crate::survivors::after_crash(x.cfg.net) && survivor(x.cfg.net) == (2int,5int)
    }),
{
    let b = t.arm; let s = t.path.first;
    fork::actual_handoff(m,first,b,s,Set::empty());
    fork::first_frame(m,first,b,s,0);
    history::canonical_orders_exist(b);
    history::canonical_extension(b);
    let a = asm::boot(Some(b))[0]; let x = asm::entry(m,app::lanes());
    assert(a == Action::Deliver(if b.branch == crate::Branch::Alpha {1nat} else {0nat}));
    assert((x.cfg.net.locals)(Replica::R3) == 1);
    assert(s.states[0] == crate::coupled_construction::root(m,app::lanes(),b));
    assert((s.states[0].cfg.net.locals)(Replica::R3) == first_value(b));
}

pub(crate) proof fn realize_decision<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>, x: State<S>, d: int)
    -> (s: Seq<crate::read_call::Event>)
    requires decisions(p,res,net::snapshot(k,x)).contains(d),
    ensures fork::completes(net::implementation(k,p),res,x,s,true),
        fork::value(net::implementation(k,p),res,x,s) == Some(d),
{
    let public = net::snapshot(k,x);
    let ts = choose|ts: Seq<net::Turn>| #[trigger] net::quiet_return(p,res,public,ts)
        && res(caller2(net::end(p,public,ts).local)) == Some(d);
    let keys = Map::new(public.packets.dom(), |h: nat| h);
    assert forall|h: nat| #[trigger] public.packets.contains_key(h) implies
        exists|i: nat| #[trigger] keys.get(i) == Some(h) by { assert(keys.get(h) == Some(h)); }
    assert(net::represents(public.packets,keys,public.packets));
    net::return_is_trace(p,res,public,ts);
    net::lift_prefix(p,k,x,public,keys,ts,false,res).0
}

pub proof fn readout_is_exact<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>, x: State<S>,
    e: precedence::IndependentView)
    requires crate::survivors::after_crash(x.cfg.net),
    ensures readout(p,k,res)(input(e,x),af::view(k,x)) == decisions(p,res,net::snapshot(k,x)),
{
    let raw = net::implementation(k,p); let i = input(e,x); let r = af::view(k,x);
    let physical = decisions(p,res,net::snapshot(k,x)); let possible = readout(p,k,res)(i,r);
    assert forall|d: int| #[trigger] physical.contains(d) == #[trigger] possible.contains(d) by {
        if physical.contains(d) && !possible.contains(d) {
            let s = realize_decision(p,k,res,x,d);
            assert(fork::completes(raw,res,x,s,true));
        } else if possible.contains(d) && !physical.contains(d) {
            let (y,s) = choose|y: State<S>, s: Seq<crate::read_call::Event>| crate::survivors::after_crash(y.cfg.net)
                && input(i.0,y) == i && af::view(k,y) == r
                && #[trigger] fork::completes(raw,res,y,s,true) && fork::value(raw,res,y,s) == Some(d);
            let t = af::replay_return(p,k,res,y,x,s,Set::empty());
            fork::completion_facts(raw,res,x,t); net::project_prefix(p,k,x,t,true,res);
            assert(net::quiet_return(p,res,net::snapshot(k,x),net::turns(k,t)));
            assert(res(caller2(net::end(p,net::snapshot(k,x),net::turns(k,t)).local)) == Some(d));
        }
    }
    assert(physical =~= possible);
}

pub open spec fn sourced(ds: ISet<int>, ws: Set<Op>) -> bool {
    (forall|d: int| #[trigger] ds.contains(d) ==> exists|w: Op| #[trigger] ws.contains(w) && d == crate::next(w,1))
        && (forall|w: Op| #[trigger] ws.contains(w) ==> history::weak(w) && ds.contains(crate::next(w,1)))
}

// All public returning schedules count, including those the two constructed
// histories did not choose. Hybrid A authenticates the decision on each one.
proof fn public_decisions<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>, x: State<S>,
    run: crate::fair_read::Runnable)
    requires crate::survivors::after_crash(x.cfg.net), survivor(x.cfg.net) == (2int,5int),
        fork::invocation_a(af::after_offers(p,k),res,x,run),
    ensures sourced(decisions(p,res,net::snapshot(k,x)),af::options(p,res,net::snapshot(k,x))),
{
    let public = net::snapshot(k,x); let raw = net::implementation(k,p); let m = af::after_offers(p,k);
    let ds = decisions(p,res,public); let ws = af::options(p,res,public);
    assert forall|d: int| #[trigger] ds.contains(d) implies exists|w: Op| #[trigger] ws.contains(w) && d == crate::next(w,1) by {
        let ts = choose|ts: Seq<net::Turn>| #[trigger] net::quiet_return(p,res,public,ts)
            && res(caller2(net::end(p,public,ts).local)) == Some(d);
        let s = realize_decision(p,k,res,x,d);
        af::same_started_machine(raw,m,res,x,s);
        fork::sampled_native_return(m,res,x,s,run);
        assert(fork::value(raw,res,x,s) == Some(d));
        let w = if d == 5 { Op::W2 } else { Op::W1 };
        assert(d == crate::next(w,1));
        assert(ws.contains(w));
    }
    assert forall|w: Op| #[trigger] ws.contains(w) implies ds.contains(crate::next(w,1)) by {
        let ts = choose|ts: Seq<net::Turn>| #[trigger] net::quiet_return(p,res,public,ts)
            && res(caller2(net::end(p,public,ts).local)) == Some(crate::next(w,1));
    }
}

// These two links use the register's algebra, independently of the legality
// of any completed pair of strong calls.
proof fn register_extension(b: Fork, v: Op)
    requires history::weak(v),
    ensures keeps_value()(history::at_first(b).ops,observed_writer(b),crate::next(v,1)) == (v == observed_writer(b)),
{
    let h = history::at_first(b); let w = observed_writer(b);
    history::canonical_orders_exist(b);
    history::extension_iff_writer(b,h,v);
    if keeps_value()(h.ops,w,crate::next(v,1)) {
        let u = choose|u: Op| history::weak(u) && crate::next(v,1) == crate::next(u,1)
            && #[trigger] history::can_keep(h.ops,w,u);
        assert(u == v);
    }
}

proof fn option_is_observed_writer(b: Fork, ws: Set<Op>)
    requires forall|v: Op| #[trigger] ws.contains(v) ==> history::weak(v),
    ensures app::extension_option(b,ws) == ws.contains(observed_writer(b)),
{
    let h = history::at_first(b); let w = observed_writer(b);
    history::canonical_orders_exist(b);
    history::extension_iff_writer(b,h,w);
    if app::extension_option(b,ws) {
        let v = choose|v: Op| #[trigger] ws.contains(v) && history::can_keep(h.ops,w,v);
        history::extension_iff_writer(b,h,v);
    }
}

proof fn decisions_test(b: Fork, c: Fork, left: ISet<int>, right: ISet<int>, wa: Set<Op>, wb: Set<Op>)
    requires b.branch != c.branch, sourced(left,wa), sourced(right,wb),
        wa.contains(observed_writer(b)), wb.contains(observed_writer(c)), !wb.contains(observed_writer(b)),
    ensures ({
        let w = observed_writer(b); let v = observed_writer(c); let d = crate::next(w,1);
        let h = history::at_first(b).ops; let g = history::at_first(c).ops; let keeps = keeps_value();
        left.contains(d) && keeps(h,w,d) && !keeps(g,v,d) && resolves(right,(g,v),(h,w),keeps)
    }),
{
    hide(keeps_value); hide(history::at_first);
    let w = observed_writer(b); let v = observed_writer(c);
    let h = history::at_first(b).ops; let g = history::at_first(c).ops; let keeps = keeps_value();
    register_extension(b,w); register_extension(b,v); register_extension(c,w); register_extension(c,v);
    assert(right.contains(crate::next(v,1)));
    assert forall|d: int| #[trigger] right.contains(d) implies keeps(g,v,d) && !keeps(h,w,d) by {
        let z = choose|z: Op| #[trigger] wb.contains(z) && d == crate::next(z,1);
        assert(history::weak(z) && z == v);
    }
}

proof fn install_is_edge<S>(p: Program<S>, k: Headers, t: Trial<S>, j: int)
    requires af::installed(k,t.path.first,j),
    ensures installed(observe(p,k,t)),
{
    let s = t.path.first; let o = observe(p,k,t);
    let old = af::view(k,s.states[j]);
    assert(tape::record(s,0)[j] == process_step(s.states[j].cfg.net,s.actions[j]));
    assert(o.ordinary_edges.contains((old,o.exit)));
}

// The comparison is directional. Either original history can supply the
// observed position. The services can have different lengths and callbacks.
pub open spec fn preserves<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>, t: Trial<S>, u: Trial<S>) -> bool {
    let m = af::after_offers(p,k); let n = t.arm.notice;
    let x = fork::invocation(m,t.path.first); let y = fork::invocation(m,u.path.first);
    let (aa,ab) = if t.arm == alpha(n) { (t.assigned,u.assigned) } else { (u.assigned,t.assigned) };
    app::preserves_extension_option(t.arm,af::options(p,res,net::snapshot(k,x)),af::options(p,res,net::snapshot(k,y)),
        precedence::actual_cuts(n,aa,ab))
}

proof fn option_difference_needs_record<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, t: Trial<S>, u: Trial<S>)
    requires t.arm.notice == u.arm.notice, t.arm.branch != u.arm.branch, ({
        let m = af::after_offers(p,k); let w = observed_writer(t.arm);
        crate::first_schedule::startup(m)
            && fork::admitted(m,first,t.arm,t.path.first) && fork::admitted(m,first,u.arm,u.path.first)
            && af::options(p,res,net::snapshot(k,fork::invocation(m,t.path.first))).contains(w)
            && !af::options(p,res,net::snapshot(k,fork::invocation(m,u.path.first))).contains(w)
    }),
    ensures retained_difference(observe(p,k,t),observe(p,k,u)),
{
    hide(af::view); hide(fork::admitted);
    let m = af::after_offers(p,k); let n = t.arm.notice; let w = observed_writer(t.arm);
    let (a,b) = if t.arm == alpha(n) { (t,u) } else { (u,t) };
    let x = fork::invocation(m,t.path.first); let y = fork::invocation(m,u.path.first);
    let all = Set::empty(); let handler = Program { initial: m.initial, ..p };
    assert(m == net::implementation(k,handler));
    fork::actual_handoff(m,first,t.arm,t.path.first,all); fork::actual_handoff(m,first,u.arm,u.path.first,all);
    af::started_options(p,k,res,x); af::started_options(p,k,res,y);
    assert(fork::writers(m,res,x,all).contains(w));
    let s = choose|s: Seq<crate::read_call::Event>| !fork::uses_name(all,s) && #[trigger] fork::completes(m,res,x,s,true)
        && fork::value(m,res,x,s) == Some(crate::next(w,1));
    af::attribute_pair(handler,k,first,res,n,a.path.first,b.path.first,t.arm,s);
    if exists|j: int| #[trigger] af::installed(k,t.path.first,j) {
        let j = choose|j: int| #[trigger] af::installed(k,t.path.first,j);
        install_is_edge(p,k,t,j);
    } else {
        assert(exists|j: int| #[trigger] af::installed(k,u.path.first,j));
        let j = choose|j: int| #[trigger] af::installed(k,u.path.first,j);
        install_is_edge(p,k,u,j);
    }
    precedence::equal_independent_views(t.arm); precedence::equal_independent_views(u.arm);
}

proof fn later_distinguishes_positions<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>, t: Trial<S>, u: Trial<S>,
    run: crate::fair_read::Runnable)
    requires t.arm.branch != u.arm.branch, ({
        let m = af::after_offers(p,k); let x = fork::invocation(m,t.path.first); let y = fork::invocation(m,u.path.first);
        let w = observed_writer(t.arm); let v = observed_writer(u.arm); let wb = af::options(p,res,net::snapshot(k,y));
        crate::survivors::after_crash(x.cfg.net) && survivor(x.cfg.net) == (2int,5int) && fork::invocation_a(m,res,x,run)
            && crate::survivors::after_crash(y.cfg.net) && survivor(y.cfg.net) == (2int,5int) && fork::invocation_a(m,res,y,run)
            && af::options(p,res,net::snapshot(k,x)).contains(w) && wb.contains(v) && !wb.contains(w)
    }),
    ensures ({
        let a = observe(p,k,t); let b = observe(p,k,u); let later = readout(p,k,res); let keeps = keeps_value();
        let d = crate::next(a.writer,1);
        later(a.input,a.inherited).contains(d) && keeps(a.position,a.writer,d) && !keeps(b.position,b.writer,d)
            && resolves(later(b.input,b.inherited),(b.position,b.writer),(a.position,a.writer),keeps)
    }),
{
    hide(readout); hide(af::view); hide(fork::invocation_a); hide(decisions); hide(af::options);
    hide(keeps_value); hide(history::at_first); hide(sourced); hide(resolves);
    let m = af::after_offers(p,k); let x = fork::invocation(m,t.path.first); let y = fork::invocation(m,u.path.first);
    let wa = af::options(p,res,net::snapshot(k,x)); let wb = af::options(p,res,net::snapshot(k,y));
    public_decisions(p,k,res,x,run); public_decisions(p,k,res,y,run);
    readout_is_exact(p,k,res,x,precedence::independent_view(t.arm));
    readout_is_exact(p,k,res,y,precedence::independent_view(u.arm));
    decisions_test(t.arm,u.arm,decisions(p,res,net::snapshot(k,x)),decisions(p,res,net::snapshot(k,y)),wa,wb);
}

proof fn losing_version(b: Fork, c: Fork, assigned: bool, other_assigned: bool, wa: Set<Op>, wb: Set<Op>)
    requires c.notice == b.notice, b.branch != c.branch,
        forall|v: Op| #[trigger] wa.contains(v) ==> history::weak(v),
        forall|v: Op| #[trigger] wb.contains(v) ==> history::weak(v),
        ({
            let (aa,ab) = if b == alpha(b.notice) { (assigned,other_assigned) } else { (other_assigned,assigned) };
            !app::preserves_extension_option(b,wa,wb,precedence::actual_cuts(b.notice,aa,ab))
        }),
    ensures ({
        let w = observed_writer(b); let v = observed_writer(c);
        wa.contains(w) && !wb.contains(w) && wb.contains(v)
            && (!precedence::has_precedence(weak_assignment(b,assigned).ops,w,v)
                || !precedence::has_precedence(weak_assignment(c,other_assigned).ops,w,v))
    }),
{
    hide(weak_assignment); hide(precedence::has_precedence); hide(precedence::independent_view);
    option_is_observed_writer(b,wa); option_is_observed_writer(b,wb);
    let w = observed_writer(b); let v = observed_writer(c);
    let (aa,ab) = if b == alpha(b.notice) { (assigned,other_assigned) } else { (other_assigned,assigned) };
    let orders = precedence::actual_cuts(b.notice,aa,ab);
    let (z,o) = choose|z: Op,o: Seq<Op>| #[trigger] wb.contains(z) && #[trigger] orders(precedence::independent_view(b),o)
        && !precedence::has_precedence(o,w,z);
    assert(z == v);
    assert(o == weak_assignment(b,assigned).ops || o == weak_assignment(c,other_assigned).ops);
}

// No T or H premise. Losing an extending option yields a grounded witness
// of information use in the semantic test, including the ordinary install.
pub proof fn lost_option_supplies_order<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, t: Trial<S>, u: Trial<S>, run: crate::fair_read::Runnable)
    requires t.arm.notice == u.arm.notice, t.arm.branch != u.arm.branch, ({
        let m = af::after_offers(p,k);
        crate::first_schedule::startup(m)
            && fork::admitted(m,first,t.arm,t.path.first) && fork::admitted(m,first,u.arm,u.path.first)
            && fork::invocation_a(m,res,fork::invocation(m,t.path.first),run)
            && fork::invocation_a(m,res,fork::invocation(m,u.path.first),run)
    }),
    ensures observed_position(af::after_offers(p,k),k,first,t) && observed_position(af::after_offers(p,k),k,first,u),
        !preserves(p,k,res,t,u) ==> unsupported_choice(observe(p,k,t),observe(p,k,u),readout(p,k,res),keeps_value()),
{
    hide(readout); hide(af::view); hide(fork::admitted); hide(fork::invocation_a);
    hide(keeps_value); hide(resolves); hide(fork::record); hide(af::options); hide(retained_difference);
    hide(precedence::actual_cuts); hide(app::preserves_extension_option); hide(precedence::has_precedence);
    hide(weak_assignment); hide(history::at_first); hide(observed_position);
    hide(af::after_offers); hide(fork::invocation); hide(net::snapshot);
    hide(crate::first_schedule::startup); hide(crate::survivors::after_crash); hide(survivor);
    let m = af::after_offers(p,k);
    let x = fork::invocation(m,t.path.first); let y = fork::invocation(m,u.path.first);
    let w = observed_writer(t.arm); let v = observed_writer(u.arm);
    let wa = af::options(p,res,net::snapshot(k,x)); let wb = af::options(p,res,net::snapshot(k,y));
    let oa = observe(p,k,t); let ob = observe(p,k,u);
    actual_origin(m,k,first,t); actual_origin(m,k,first,u);
    if !preserves(p,k,res,t,u) {
        assert forall|v: Op| #[trigger] wa.contains(v) implies history::weak(v) by { reveal(af::options); }
        assert forall|v: Op| #[trigger] wb.contains(v) implies history::weak(v) by { reveal(af::options); }
        losing_version(t.arm,u.arm,t.assigned,u.assigned,wa,wb);
        option_difference_needs_record(p,k,first,res,t,u);
        later_distinguishes_positions(p,k,res,t,u,run);
        assert(oa.input == ob.input) by { reveal(retained_difference); }
        let later = readout(p,k,res); let keeps = keeps_value(); let d = crate::next(w,1);
        assert(later(oa.input,oa.inherited).contains(d) && keeps(oa.position,w,d) && !keeps(ob.position,v,d));
        assert(exists|z: int| #[trigger] later(oa.input,oa.inherited).contains(z)
            && keeps(oa.position,w,z) && !keeps(ob.position,v,z));
        assert(resolves(later(oa.input,ob.inherited),(ob.position,v),(oa.position,w),keeps));
        assert(unsupported_choice(oa,ob,later,keeps));
    }
}

// Apply the functional interpretation in both directions to reached histories.
// Every physical premise of the order test is discharged before invoking T.
pub proof fn functional_t_preserves_original_options<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, t: Trial<S>, u: Trial<S>, run: crate::fair_read::Runnable)
    requires register_t(p,k,first,res), t.arm.notice == u.arm.notice, t.arm.branch != u.arm.branch,
        ({
            let raw = net::implementation(k,p); let m = af::after_offers(p,k);
            crate::first_schedule::startup(m) && (t.arm.notice != Notice::Replication ==> t.assigned && u.assigned)
                && fork::invocation_a(m,res,fork::invocation(m,t.path.first),run)
                && fork::invocation_a(m,res,fork::invocation(m,u.path.first),run)
                && fork::completed_history(raw,m,first,res,t.arm,t.path) && fork::completed_history(raw,m,first,res,u.arm,u.path)
        }),
    ensures preserves(p,k,res,t,u) && preserves(p,k,res,u,t),
{
    let m = af::after_offers(p,k);
    assert(fork::admitted(m,first,t.arm,t.path.first) && fork::admitted(m,first,u.arm,u.path.first));
    lost_option_supplies_order(p,k,first,res,t,u,run); lost_option_supplies_order(p,k,first,res,u,t,run);
    weak_assignment_at_delivery(t.arm,t.assigned); weak_assignment_at_delivery(u.arm,u.assigned);
    af::publish_history(p,k,first,res,t.arm,t.path); af::publish_history(p,k,first,res,u.arm,u.path);
    assert(reached(p,k,first,res,t) && reached(p,k,first,res,u));
    let obs = |t: Trial<S>| observe(p,k,t);
    assert(!unsupported_choice(obs(t),obs(u),readout(p,k,res),keeps_value())
        && !unsupported_choice(obs(u),obs(t),readout(p,k,res),keeps_value()));
}

pub proof fn original_hot_under_functional_t<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, n: Notice, run: crate::fair_read::Runnable, aa: bool, ab: bool)
    -> (histories: (ReadPair<S>,ReadPair<S>))
    requires fork::original_premises(net::implementation(k,p),af::after_offers(p,k),first,res,n,run,aa,ab),
        register_t(p,k,first,res),
    ensures ({
        let (a,b) = histories; let raw = net::implementation(k,p); let m = af::after_offers(p,k);
        fork::completed_history(raw,m,first,res,alpha(n),a) && af::public_history(p,k,alpha(n),a)
            && fork::completed_history(raw,m,first,res,beta(n),b) && af::public_history(p,k,beta(n),b)
            && (!fork::legal_history(m,first,res,a) || !fork::legal_history(m,first,res,b))
    }),
{
    let (a,b) = af::original_async_application(p,k,first,res,n,run,aa,ab);
    let t = Trial { arm: alpha(n), assigned: aa, path: a }; let u = Trial { arm: beta(n), assigned: ab, path: b };
    let m = af::after_offers(p,k);
    assert(fork::opportunity(m,res,fork::invocation(m,a.first),run));
    assert(fork::opportunity(m,res,fork::invocation(m,b.first),run));
    functional_t_preserves_original_options(p,k,first,res,t,u,run);
    (a,b)
}

}
