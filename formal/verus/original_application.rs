// Apply the retained-order result to the paper's two original invocations.
use vstd::prelude::*;
use crate::{Op, Replica, checkpoint::*, delivery::*, precedence};
use crate::coupled_construction as build;
use crate::coupled_reads as reads;
use crate::fair_read as fair;
use crate::first_assembly::{self as asm, Lanes, Service};
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::reference;
use crate::first_splice as tape;
use crate::fork_alternatives::{self as fork, Tapes};
use crate::fork_information::{caller2, live_view, Residual};
use crate::guarded_comparison as cmp;
use crate::hybrid_majority as maj;
use crate::independent_preparations as prep;
use crate::independent_read::{self as read, State};
use crate::mailbox_preparation as mb;
use crate::order_extension as history;
use crate::promotion_wait as wait;
use crate::read_call::{Event, Net, Program};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::retained_order as order;
use crate::sr1_majorities as refs;

verus! {

// Only the existing R3 confirmation has a statically owned envelope.
pub open spec fn lanes() -> Lanes { map![2nat => Replica::R3, 3nat => Replica::R1, 4nat => Replica::R2] }

pub open spec fn weak_replica_step<S>() -> wait::Relation<State<S>, Event> {
    |x: State<S>, a: Event, _y: State<S>| {
        let e = process_step(x.cfg.net, a);
        e.actor is At && cmp::weak_work(e)
    }
}

// Positive service on an original, all-live prefix. The value condition is
// membership in the selected majority during this service. No reply format,
// expected read value, metadata or future SR2 appears here.
pub open spec fn held_first_return<S>(m: Program<S>, first: spec_fn(S) -> int, b: Fork, p: Service<S>) -> bool {
    wait::first_return(mail::active_step(m), mail::posted(m), build::root(m, lanes(), b), p)
        && !wait::uses(p, weak_replica_step())
        && maj::held(p.states, crate::first_quorum(b.branch), first((p.states.last().cfg.private)(Process::FirstClient)))
}

pub(crate) proof fn quiet_cells<S>(m: Program<S>, x: State<S>, a: Event, y: State<S>)
    requires read::service_step(m)(x,a,y), !weak_replica_step()(x,a,y),
    ensures y.cfg.net.locals == x.cfg.net.locals,
{
    assert forall|r: Replica| (#[trigger] local_input(x.cfg.net,a,r)).is_none()
        || !(local_input(x.cfg.net,a,r).unwrap() is Copy) by {};
    assert(y.cfg.net.locals =~= x.cfg.net.locals);
}

// Remove only the service mask. The omitted replica takes no action in the
// copied interval. In particular no queued packet is deleted or renamed.
pub open spec fn all_available<S>(x: State<S>) -> State<S> {
    State { cfg: crate::ordinary_service::Configuration { net: Net { unavailable: None, ..x.cfg.net }, ..x.cfg }, ..x }
}

proof fn original_at_fanout<S>(m: Program<S>, b: Fork)
    ensures all_available(reference(m,b,5)) == build::root(m,lanes(),b),
{
    let refcut = reference(m,b,5); let root = build::root(m,lanes(),b);
    refs::majority_transport(b);
    assert forall|i:int| 0<=i<5 implies #[trigger] refs::obs(b)[i] == #[trigger] checkpoint_observations(b)[i]
        by { assert(refs::kept_index(b,i as nat)==i); }
    assert(refcut.cfg.private =~= root.cfg.private) by {
        assert forall|p:Process| #[trigger] (refcut.cfg.private)(p) == (root.cfg.private)(p) by {
            crate::protocol::memory_on_common_prefix(m,p,refs::obs(b),checkpoint_observations(b),5);
        }
    }
    assert(refcut.cfg.net.pending =~= root.cfg.net.pending);
    assert(refcut.owners =~= root.owners);
}

pub(crate) proof fn original_step<S>(m: Program<S>, x: State<S>, a: Event, y: State<S>)
    requires mail::active_step(m)(x,a,y),
    ensures mail::active_step(m)(all_available(x),a,all_available(y)),
        process_step(all_available(x).cfg.net,a) == process_step(x.cfg.net,a),
{
    let u = all_available(x); let v = read::next(m,u,a);
    assert(process_step(u.cfg.net,a) == process_step(x.cfg.net,a));
    assert(v.cfg.net.locals =~= y.cfg.net.locals);
    assert(v.cfg.private =~= y.cfg.private);
    assert(v == all_available(y));
}

// Each accepted service starts at the original SR1 fanout. Its recorded
// callbacks give a physical prefix ending at C1's publication.
pub proof fn accepted_first_prefix<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:Service<S>)
    requires held_first_return(m,first,b,p),dispatch::initiates(m),dispatch::weak_open(m,b),
    ensures asm::prefix(m,asm::entry(m,lanes()),asm::boot(Some(b))+p.actions,true),
        asm::drive(m,asm::entry(m,lanes()),asm::boot(Some(b))+p.actions)==p.states.last(),
{
    let root=build::root(m,lanes(),b);let t=tape::record(p,0);
    tape::recorded(m,p,0);asm::native_prefix(m,root,t,true);
    assert(asm::actions(t) =~= p.actions);
    asm::launch(m,lanes(),Some(b));
    asm::prefix_concat(m,asm::entry(m,lanes()),asm::boot(Some(b)),p.actions,true);
}

// A from the actual invocation on the designated majority, a fair
// opportunity and the no-await test yield an SR1 value in the all-live
// original even when the protocol returns via an opaque or aggregated reply.
pub(crate) proof fn first_from_reference_a<S>(
    m: Program<S>, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>, b: Fork, run: fair::Runnable,
) -> (original: Service<S>)
    requires dispatch::initiates(m), dispatch::weak_open(m,b),
        maj::first_reference_a(m,first,res,b,run), mail::fair_opportunity(m,run,reference(m,b,5)),
        !wait::needs_class(mail::active_step(m),mail::posted(m),reference(m,b,5),weak_replica_step()),
    ensures held_first_return(m,first,b,original),
        first((original.states.last().cfg.private)(Process::FirstClient)) == first_value(b),
        asm::prefix(m,asm::entry(m,lanes()),asm::boot(Some(b))+original.actions,true),
        asm::drive(m,asm::entry(m,lanes()),asm::boot(Some(b))+original.actions)==original.states.last(),
        forall|i:int| 0<=i<original.actions.len() ==> (#[trigger] tape::record(original,0)[i]).actor != at(refs::missing(b)),
{
    let x = reference(m,b,5); let step = mail::active_step(m); let posted = mail::posted(m);
    crate::first_service_loss::finite_service(m,b,run);
    let witness = choose|p:Service<S>| #[trigger] cause::returning(m,b,p);
    assert(wait::can_finish(step,posted,x));
    let p = choose|p:Service<S>| #[trigger] wait::first_return(step,posted,x,p) && !wait::uses(p,weak_replica_step());
    maj::first_quorum_from_submitted(m,first,res,b);
    assert forall|i:int| 0<=i<p.actions.len() implies !cause::changes_sample(b,#[trigger] p.states[i],p.states[i+1]) by {
        assert(step(p.states[i],p.actions[i],p.states[i+1]));
        quiet_cells(m,p.states[i],p.actions[i],p.states[i+1]);
    }
    cause::forced_sample(m,first,p,b);
    let original = wait::Path { states:p.states.map_values(|z| all_available(z)), actions:p.actions };
    original_at_fanout(m,b);
    assert forall|i:int| 0<=i<p.actions.len() implies {
        let a = #[trigger] p.actions[i]; let u=original.states[i]; let v=original.states[i+1];
        step(u,a,v) && !posted(u) && !weak_replica_step()(u,a,v)
            && process_step(u.cfg.net,a).actor != at(refs::missing(b))
    } by {
        let a=p.actions[i];let z=p.states[i];assert(step(z,a,p.states[i+1]));
        cause::prefix_mask(m,p,i as nat);
        original_step(m,z,a,p.states[i+1]);
        assert(tape::moves(a) && live(z.cfg.net,process_step(z.cfg.net,a).actor));
    }
    assert(maj::held(original.states,crate::first_quorum(b.branch),first_value(b))) by {
        assert(crate::first_quorum(b.branch).contains(Replica::R3));
        assert((original.states[0].cfg.net.locals)(Replica::R3) == first_value(b));
    }
    accepted_first_prefix(m,first,b,original);
    original
}

// The older callers provide A for both clients on the reference. Keep
// that entry point while the native mainline needs only C1 service there.
pub proof fn available_original_first<S>(
    m: Program<S>, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>, b: Fork, run: fair::Runnable,
) -> (original: Service<S>)
    requires dispatch::initiates(m), dispatch::weak_open(m,b),
        maj::read_a(m,first,res,reference(m,b,0),run), mail::fair_opportunity(m,run,reference(m,b,5)),
        !wait::needs_class(mail::active_step(m),mail::posted(m),reference(m,b,5),weak_replica_step()),
    ensures held_first_return(m,first,b,original),
        first((original.states.last().cfg.private)(Process::FirstClient)) == first_value(b),
        asm::prefix(m,asm::entry(m,lanes()),asm::boot(Some(b))+original.actions,true),
        asm::drive(m,asm::entry(m,lanes()),asm::boot(Some(b))+original.actions)==original.states.last(),
        forall|i:int| 0<=i<original.actions.len() ==> (#[trigger] tape::record(original,0)[i]).actor != at(refs::missing(b)),
{
    maj::availability_at_both_clients(m,res,reference(m,b,0),run);
    first_from_reference_a(m,first,res,b,run)
}

// Evaluate the certificate's wire test with a constant result observer.
// This removes exactly its numeric return conjunct and keeps every
// original guard on the senders, envelopes and replica callbacks.
pub open spec fn selected_inputs<S>(b:Fork,p:Service<S>) -> bool {
    mb::selected_service(|_s:S| first_value(b),b,p)
}

// This is a wire observation on *some* first return of each original.
// The outputs of the two reads and their histories are not prescribed.
pub open spec fn has_selected_inputs<S>(m: Program<S>, first: spec_fn(S) -> int, b: Fork) -> bool {
    exists|p:Service<S>| #[trigger] held_first_return(m,first,b,p) && selected_inputs(b,p)
}

pub(crate) proof fn cells_at<S>(m:Program<S>,p:Service<S>,k:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::active_step(m),p),
        !wait::uses(p,weak_replica_step()), k<p.states.len(),
    ensures p.states[k as int].cfg.net.locals==p.states[0].cfg.net.locals,
    decreases k,
{
    if k>0 {
        let i=k as int-1; cells_at(m,p,(k-1) as nat);
        assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));
        quiet_cells(m,p.states[i],p.actions[i],p.states[i+1]);
    }
}

pub proof fn first_inputs_iff_admitted_arm<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,b:Fork)
    requires mb::setup(m,res,lanes(),b),
    ensures has_selected_inputs(m,first,b) == (exists|t:Tapes| #[trigger] fork::admitted(m,first,res,lanes(),b,t)),
{
    let l=lanes();let x=build::root(m,l,b);
    if has_selected_inputs(m,first,b) {
        let p=choose|p:Service<S>| #[trigger] held_first_return(m,first,b,p) && selected_inputs(b,p);
        let value=first((p.states.last().cfg.private)(Process::FirstClient));
        let (i,r)=choose|i:int,r:Replica| 0<=i<p.states.len() && crate::first_quorum(b.branch).contains(r)
            && #[trigger] (p.states[i].cfg.net.locals)(r)==value;
        cells_at(m,p,i as nat);
        assert(value==first_value(b));
        assert(crate::first_pair::c1_protected(x)) by {
            assert forall|id:nat| #[trigger] x.cfg.net.pending.contains_key(id) implies x.cfg.net.pending[id].to!=Process::FirstClient by {};
        }
        mb::normalize_selected_return(m,first,b,x,p);
        let t=Tapes{replicas:crate::coupled_sources::replicas(p),caller:reads::caller(p)};
        mb::release(m,first,res,l,b,t.replicas,t.caller);
        assert(fork::admitted(m,first,res,l,b,t));
    } else if exists|t:Tapes| #[trigger] fork::admitted(m,first,res,l,b,t) {
        let t=choose|t:Tapes| #[trigger] fork::admitted(m,first,res,l,b,t);
        let p=typed_arm_is_native(m,first,res,b,t);
        assert(held_first_return(m,first,b,p) && selected_inputs(b,p));
    }
}

// Embed the old arm with its exact observations, return state, and C2 invocation.
pub proof fn typed_arm_is_native<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,b:Fork,t:Tapes) -> (p:Service<S>)
    requires fork::admitted(m,first,res,lanes(),b,t),
    ensures crate::native_fork::admitted(m,first,b,p),selected_inputs(b,p),
        tape::record(p,0)==t.replicas+t.caller, p.states.last()==build::first_end(m,lanes(),b,t.replicas,t.caller),
        crate::native_fork::invocation(m,p)==fork::invocation(m,lanes(),b,t),
{
    let l=lanes();let x=build::root(m,l,b);
    mb::arm_has_mailbox(m,first,res,l,b,t);
    let p=mb::release_to_service(m,first,b,x,t.replicas,t.caller);
    assert forall|i:int| 0<=i<p.actions.len() implies !weak_replica_step()(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
        let e=tape::record(p,0)[i];
        if e.actor!=Process::FirstClient { assert(crate::independent_preparations::ordinary_input(e)); }
    }
    assert(maj::held(p.states,crate::first_quorum(b.branch),first_value(b))) by {
        assert(crate::first_quorum(b.branch).contains(Replica::R3));
        assert((p.states[0].cfg.net.locals)(Replica::R3)==first_value(b));
    }
    assert(held_first_return(m,first,b,p));
    p
}

pub open spec fn quiet_second<S>(m:Program<S>,b:Fork) -> wait::Relation<State<S>,Event> {
    nb::ordinary(read::service_step(m),cmp::postponed(b,true))
}

// The monitor reserves the three seed names even when a seed envelope
// has gone. Test just whether a new send at such a name is indispensable
// on this call; an ordinary send at a free name need not be weak work.
pub open spec fn seed_send<S>() -> wait::Relation<State<S>,Event> {
    |_x:State<S>,a:Event,_y:State<S>| a is Send && a->Send_0<=2
}

pub open spec fn names_available<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>) -> bool {
    !wait::needs_class(quiet_second(m,b),read::returned(res),x,seed_send())
}

pub open spec fn second_progress<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    b:Fork,t:Tapes,run:fair::Runnable) -> bool {
    let x=fork::cut(m,lanes(),b,t);
    maj::read_a(m,first,res,fork::invocation(m,lanes(),b,t),run)
        && (exists|e:fair::Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run))
        && !wait::needs_class(read::service_step(m),read::returned(res),x,cmp::postponed(b,true))
}

// Independently reached C2 invocation, before either query. Extract a
// weak-free physical return from A and no-await. Exactly one local
// envelope condition relates it to the existing mainline monitor.
pub proof fn second_at_original_invocation<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    b:Fork,t:Tapes,run:fair::Runnable)
    requires fork::admitted(m,first,res,lanes(),b,t),second_progress(m,first,res,b,t,run),
    ensures ({
        let x=fork::cut(m,lanes(),b,t);
        wait::can_finish(quiet_second(m,b),read::returned(res),x)
            && (names_available(m,res,b,x) == (exists|s:Seq<Event>| #[trigger] cmp::second_return(true,m,res,b,x,s)))
            && (reads::distinct_weak_names(m) ==> names_available(m,res,b,x))
    }),
{
    let l=lanes();let start=build::prefix_actions(b,t.replicas,t.caller);
    let z=build::first_end(m,l,b,t.replicas,t.caller);
    let i=fork::invocation(m,l,b,t);let h=maj::second_head(m,i);let x=fork::cut(m,l,b,t);
    assert(crate::first_pair::close(true) =~= fork::wake()+h.actions);
    asm::prefix_concat(m,asm::entry(m,l),start,crate::first_pair::close(true),true);
    asm::prefix_concat(m,z,fork::wake(),h.actions,true);
    reveal_with_fuel(asm::drive,4);reveal_with_fuel(asm::prefix,3);
    assert(h.states.last()==x);
    let y=read::next(m,i,issue::send_first());
    let prefix=read::prefix_step(m);let at_x=read::at_state(x);
    assert(prefix(i,issue::send_first(),y) && prefix(y,issue::send_second(),x));
    assert(nb::within(prefix,at_x,x,0));assert(nb::within(prefix,at_x,y,1));assert(nb::within(prefix,at_x,i,2));
    cmp::opportunity_from_hybrid_a(true,m,res,run,i,b,x);
    let p=cmp::finish_one(true,m,res,run,b,x);
    let st=read::service_step(m);let d=read::returned(res);let quiet=quiet_second(m,b);
    assert forall|j:int| 0<=j<p.actions.len() implies quiet(p.states[j],#[trigger] p.actions[j],p.states[j+1]) by {
        assert(st(p.states[j],p.actions[j],p.states[j+1]));
    }
    assert(wait::first_return(quiet,d,x,p));
    assert(wait::can_finish(quiet,d,x));
    if names_available(m,res,b,x) || reads::distinct_weak_names(m) {
        let q=if names_available(m,res,b,x) {
            choose|q:Service<S>| #[trigger] wait::first_return(quiet,d,x,q) && !wait::uses(q,seed_send())
        } else {p};
        assert forall|j:int| 0<=j<q.actions.len() implies st(q.states[j],#[trigger] q.actions[j],q.states[j+1])
            && !cmp::postponed(b,true)(q.states[j],q.actions[j],q.states[j+1]) by {
            assert(quiet(q.states[j],q.actions[j],q.states[j+1]));
        }
        assert(wait::first_return(st,d,x,q));
        cmp::native_script(true,m,res,b,q,0);
        assert(q.actions.skip(0) =~= q.actions);cmp::returned_run(true,m,res,b,x,q.actions);
        assert(exists|s:Seq<Event>| #[trigger] cmp::second_return(true,m,res,b,x,s));
    }
    if exists|s:Seq<Event>| #[trigger] cmp::second_return(true,m,res,b,x,s) {
        let s=choose|s:Seq<Event>| #[trigger] cmp::second_return(true,m,res,b,x,s);
        let g=cmp::second(true,res);let tape=cmp::fired(m,g,x,s);let q=cmp::path(m,x,tape);
        cmp::firing_is_native(m,g,x,s);cmp::physical_steps(m,g,x,tape);
        assert forall|j:int| 0<=j<q.actions.len() implies quiet(q.states[j],#[trigger] q.actions[j],q.states[j+1])
            && !seed_send()(q.states[j],q.actions[j],q.states[j+1]) by {
            assert(st(q.states[j],q.actions[j],q.states[j+1]) && g(q.states[j],q.actions[j]));
        }
        assert(wait::first_return(quiet,d,x,q) && !wait::uses(q,seed_send()));
    }
}

// Functional interpretation of the preservation sentence. A record may
// supply the only remaining way to extend the observed writer's position
// only if the independent weak evidence justifies it against every rival
// still selectable from the alternative. This is a rule on available
// choices, with no strong return values, event labels or H in the rule.
pub open spec fn extension_option(b: Fork, versions: Set<Op>) -> bool {
    exists|v: Op| #[trigger] versions.contains(v) && history::can_keep(history::at_first(b).ops, observed_writer(b), v)
}

pub open spec fn preserves_extension_option(b: Fork, actual: Set<Op>, other: Set<Op>, orders: precedence::Possible) -> bool {
    extension_option(b, actual) && !extension_option(b, other) ==> forall|v: Op, o: Seq<Op>|
        #[trigger] other.contains(v) && #[trigger] orders(precedence::independent_view(b), o)
            ==> precedence::has_precedence(o, observed_writer(b), v)
}

pub proof fn preservation_iff_no_enabling_use<S>(
    m: Program<S>, res: spec_fn(S)->Option<int>, b: Fork, reader: S, actual: Residual<S>, other: Residual<S>,
    inputs: ISet<Seq<Event>>, orders: precedence::Possible,
)
    ensures preserves_extension_option(b, order::possible_writers(m,res,reader,actual,inputs),
        order::possible_writers(m,res,reader,other,inputs), orders)
        == (forall|s:Seq<Event>| !#[trigger] order::record_enables_observed_order(m,res,b,reader,actual,other,inputs,s,orders)),
{
    let own = order::possible_writers(m,res,reader,actual,inputs);
    let alternatives = order::possible_writers(m,res,reader,other,inputs);
    let w = observed_writer(b); let prefix = history::at_first(b).ops;
    if preserves_extension_option(b,own,alternatives,orders) {
        assert forall|s: Seq<Event>| !#[trigger] order::record_enables_observed_order(m,res,b,reader,actual,other,inputs,s,orders) by {
            if order::record_enables_observed_order(m,res,b,reader,actual,other,inputs,s,orders) {
                let value = fork::selects(true,m,res,reader,s,actual);
                let v = fork::writer(value).unwrap();
                assert(value == Some(crate::next(v,1)) && own.contains(v));
                assert(extension_option(b,own) && !extension_option(b,alternatives));
                let (u,o) = choose|u: Op,o: Seq<Op>| #[trigger] alternatives.contains(u)
                    && #[trigger] orders(precedence::independent_view(b),o) && !precedence::has_precedence(o,w,u);
            }
        }
    } else {
        let v = choose|v: Op| #[trigger] own.contains(v) && history::can_keep(prefix,w,v);
        let s = choose|s: Seq<Event>| inputs.contains(s)
            && #[trigger] fork::selects(true,m,res,reader,s,actual)==Some(crate::next(v,1));
        assert(fork::writer(Some(crate::next(v,1))) == Some(v));
        assert(order::record_enables_observed_order(m,res,b,reader,actual,other,inputs,s,orders));
    }
}

// Only this specialization of the functional reading of T is used.
// Both native cuts are reached, the reader is held fixed, and every
// finite ordinary SR2 input is allowed on each arm.
pub open spec fn protects_observed_position<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,
    x:State<S>,y:State<S>,orders:precedence::Possible) -> bool {
    let inputs=ISet::<Seq<Event>>::full();let c=caller2(x);
    preserves_extension_option(b,order::possible_writers(m,res,c,live_view(x),inputs),
        order::possible_writers(m,res,c,live_view(y),inputs),orders)
}

pub open spec fn completed_violation<S>(m:Program<S>,res:spec_fn(S)->Option<int>,n:Notice,
    a:Tapes,b:Tapes,sa:Seq<Event>,sb:Seq<Event>) -> bool {
    let l=lanes();let left=alpha(n);let right=beta(n);
    fork::sampled(true,m,res,l,left,a,sa) && fork::sampled(true,m,res,l,right,b,sb)
        && (!reads::legal_returns(5,fork::outcome(true,m,res,fork::cut(m,l,left,a),sa).unwrap())
            || !reads::legal_returns(2,fork::outcome(true,m,res,fork::cut(m,l,right,b),sb).unwrap()))
}

pub open spec fn reached_first_return<S>(raw:Program<S>,b:Fork,p:Service<S>) -> bool {
    let start=prep::before_offers(raw,lanes());let tail=asm::boot(Some(b))+p.actions;
    asm::prefix(raw,start,prep::offers()+tail,true) && asm::drive(raw,start,prep::offers()+tail)==p.states.last()
}

// No candidate, prescribed first result or returning second script is
// supplied. Separate the positive service that A gives on the original
// workload from exactly what the existing certificate can represent.
pub proof fn typed_certificate_application<S>(raw:Program<S>,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    n:Notice,run:fair::Runnable,assigned_a:bool,assigned_b:bool)
    requires
        m==prep::after_offers(raw,lanes()), ({
            let x=prep::before_offers(raw,lanes());let s=prep::offers();let y=read::next(raw,x,s[0]);
            crate::ordinary_service::allowed(raw,x.cfg,s[0]) && crate::ordinary_service::allowed(raw,y.cfg,s[1])
        }),
        n!=Notice::Replication ==> assigned_a && assigned_b,
        forall|b:Fork| b.notice==n ==> #[trigger] mb::setup(m,res,lanes(),b)
            && maj::read_a(m,first,res,reference(m,b,0),run) && mail::fair_opportunity(m,run,reference(m,b,5))
            && !wait::needs_class(mail::active_step(m),mail::posted(m),reference(m,b,5),weak_replica_step()),
        forall|b:Fork,t:Tapes| b.notice==n && #[trigger] fork::admitted(m,first,res,lanes(),b,t)
            ==> second_progress(m,first,res,b,t,run),
        forall|a:Tapes,b:Tapes| #[trigger] fork::candidate(m,first,res,lanes(),n,a,b) ==> {
            let x=fork::cut(m,lanes(),alpha(n),a);let y=fork::cut(m,lanes(),beta(n),b);
            let orders=precedence::actual_cuts(n,assigned_a,assigned_b);
            protects_observed_position(m,res,alpha(n),x,y,orders) || protects_observed_position(m,res,beta(n),y,x,orders)
        },
    ensures ({
        let l=lanes();let left=alpha(n);let right=beta(n);let entry=prep::before_offers(raw,l);
        let weak=crate::guarded_history::weak_end();
        asm::prefix(raw,entry,prep::offers(),true) && asm::drive(raw,entry,prep::offers())==asm::entry(m,l)
            && weak.answers.get(crate::weak_round::request(crate::Op::W1).id)==Some(1)
            && weak.answers.get(crate::weak_round::request(crate::Op::W2).id)==Some(1)
            && (forall|arm:Fork| arm.notice==n ==> exists|p:Service<S>| #[trigger] held_first_return(m,first,arm,p)
                && first((p.states.last().cfg.private)(Process::FirstClient))==first_value(arm) && reached_first_return(raw,arm,p))
            && ((has_selected_inputs(m,first,left) && has_selected_inputs(m,first,right))
                == (exists|a:Tapes,b:Tapes| #[trigger] fork::candidate(m,first,res,l,n,a,b)))
            && (forall|a:Tapes,b:Tapes| #[trigger] fork::candidate(m,first,res,l,n,a,b) ==> {
                let x=fork::cut(m,l,left,a);let y=fork::cut(m,l,right,b);
                let names=names_available(m,res,left,x) && names_available(m,res,right,y);
                let violates=exists|sa:Seq<Event>,sb:Seq<Event>| #[trigger] completed_violation(m,res,n,a,b,sa,sb);
                (names == violates) && (reads::distinct_weak_names(m) ==> violates)
            })
    }),
{
    let l=lanes();let left=alpha(n);let right=beta(n);let inputs=ISet::<Seq<Event>>::full();
    assert(mb::setup(m,res,l,left) && mb::setup(m,res,l,right));
    prep::shared_weak_entry(raw,l,left);
    assert forall|arm:Fork| arm.notice==n implies exists|p:Service<S>| #[trigger] held_first_return(m,first,arm,p)
        && first((p.states.last().cfg.private)(Process::FirstClient))==first_value(arm) && reached_first_return(raw,arm,p) by {
        assert(mb::setup(m,res,l,arm));let p=available_original_first(m,first,res,arm,run);
        let tail=asm::boot(Some(arm))+p.actions;
        prep::rebase_preserves_steps(raw,l,asm::entry(m,l),tail);
        asm::prefix_concat(raw,prep::before_offers(raw,l),prep::offers(),tail,true);
        assert(reached_first_return(raw,arm,p));
    }
    first_inputs_iff_admitted_arm(m,first,res,left);first_inputs_iff_admitted_arm(m,first,res,right);
    if has_selected_inputs(m,first,left) && has_selected_inputs(m,first,right) {
        let a=choose|t:Tapes| #[trigger] fork::admitted(m,first,res,l,left,t);
        let b=choose|t:Tapes| #[trigger] fork::admitted(m,first,res,l,right,t);
        assert(fork::candidate(m,first,res,l,n,a,b));
    } else {
        assert forall|a:Tapes,b:Tapes| !#[trigger] fork::candidate(m,first,res,l,n,a,b) by {
            if fork::candidate(m,first,res,l,n,a,b) {
                assert(fork::admitted(m,first,res,l,left,a) && fork::admitted(m,first,res,l,right,b));
            }
        }
    }
    assert forall|a:Tapes,b:Tapes| #[trigger] fork::candidate(m,first,res,l,n,a,b) implies {
        let x=fork::cut(m,l,left,a);let y=fork::cut(m,l,right,b);
        let names=names_available(m,res,left,x) && names_available(m,res,right,y);
        let violates=exists|sa:Seq<Event>,sb:Seq<Event>| #[trigger] completed_violation(m,res,n,a,b,sa,sb);
        (names == violates) && (reads::distinct_weak_names(m) ==> violates)
    } by {
        let x=fork::cut(m,l,left,a);let y=fork::cut(m,l,right,b);
        second_at_original_invocation(m,first,res,left,a,run);second_at_original_invocation(m,first,res,right,b,run);
        if names_available(m,res,left,x) && names_available(m,res,right,y) {
            let sa=choose|s:Seq<Event>| #[trigger] cmp::second_return(true,m,res,left,x,s);
            let sb=choose|s:Seq<Event>| #[trigger] cmp::second_return(true,m,res,right,y,s);
            order::original_fork_requires_preservation(m,first,res,l,n,a,b,inputs,sa,sb,assigned_a,assigned_b);
            let orders=precedence::actual_cuts(n,assigned_a,assigned_b);
            preservation_iff_no_enabling_use(m,res,left,caller2(x),live_view(x),live_view(y),inputs,orders);
            preservation_iff_no_enabling_use(m,res,right,caller2(y),live_view(y),live_view(x),inputs,orders);
            assert(order::history_failure(m,res,left,x,inputs) || order::history_failure(m,res,right,y,inputs));
            let u=if order::history_failure(m,res,left,x,inputs) {
                choose|s:Seq<Event>| inputs.contains(s) && #[trigger] cmp::second_return(true,m,res,left,x,s)
                    && !reads::legal_returns(first_value(left),fork::outcome(true,m,res,x,s).unwrap())
            } else {sa};
            let v=if order::history_failure(m,res,right,y,inputs) {
                choose|s:Seq<Event>| inputs.contains(s) && #[trigger] cmp::second_return(true,m,res,right,y,s)
                    && !reads::legal_returns(first_value(right),fork::outcome(true,m,res,y,s).unwrap())
            } else {sb};
            fork::quorum_value(true,m,first,res,l,left,a,u);fork::quorum_value(true,m,first,res,l,right,b,v);
            assert(completed_violation(m,res,n,a,b,u,v));
        } else if exists|sa:Seq<Event>,sb:Seq<Event>| #[trigger] completed_violation(m,res,n,a,b,sa,sb) {
            let (u,v)=choose|u:Seq<Event>,v:Seq<Event>| #[trigger] completed_violation(m,res,n,a,b,u,v);
            assert(cmp::second_return(true,m,res,left,x,u) && cmp::second_return(true,m,res,right,y,v));
        }
    }
}

}

// Public mainline entry point. The typed certificate remains available above.
pub use crate::native_fork::original_hot_application;
