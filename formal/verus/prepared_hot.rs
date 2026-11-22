// Apply the functional preservation rule to the two real service windows
// reached from selective weak visibility.
use vstd::prelude::*;
use crate::{Op,Replica,checkpoint::*,delivery::*};
use crate::async_fork as af;
use crate::async_messages::{self as net,Headers};
use crate::first_assembly::{self as asm,Service};
use crate::first_mailbox as mail;
use crate::first_splice::{self as tape,Observation};
use crate::independent_read::{self as read,State};
use crate::native_fork as fork;
use crate::operation_history as op;
use crate::order_extension as order;
use crate::original_application as app;
use crate::prepared_service::{self as svc,Exposure};
use crate::read_call::{Event,Program};
use crate::register_history as reg;
use crate::semantic_promotion as retain;
use crate::weak_construction as wc;
use crate::weak_visibility as vis;

verus! {

// Independent evidence is taken before SR1. It includes the complete private
// memories of R1/R2, their cells, and ordinary messages available to the
// surviving actors. Weak positions are computed separately on the full trace.
pub type Evidence<S> = af::View<S>;
pub open spec fn evidence<S>(p:Program<S>,k:Headers,e:Exposure) -> Evidence<S> {
    af::view(k,svc::endpoint(p,k,e))
}

// A fixed interpretation of independently assigned weak positions on the
// public weak history. It sees no strong operation, return or future cut.
pub type WeakOrder = spec_fn(Seq<Observation>)->Seq<Op>;
pub open spec fn positions(k:Headers,o:WeakOrder,e:Exposure) -> Seq<Op> { o(vis::callbacks(k,local_rmw_cells(),svc::weak_trace(e))) }
pub open spec fn weak_word(s:Seq<Op>) -> bool {
    s.no_duplicates() && forall|i:int| 0<=i<s.len() ==> order::weak(#[trigger] s[i])
}

pub struct Phase<S> { pub weak:Exposure, pub sends:Seq<Event>, pub service:Service<S> }
pub open spec fn root<S>(p:Program<S>,k:Headers,e:Exposure,s:Seq<Event>) -> State<S> {
    asm::drive(net::implementation(k,p),svc::endpoint(p,k,e),s)
}
pub open spec fn at_entry<S>(p:Program<S>,k:Headers,e:Exposure,s:Seq<Event>,x:State<S>) -> bool {
    let m=net::implementation(k,p);
    svc::service_entry(p,k,e) && svc::fan(m,svc::endpoint(p,k,e),s) && x==root(p,k,e,s)
        && x.first_requested==all_replicas() && !mail::posted(m)(x)
}
pub open spec fn phase<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,h:Phase<S>) -> bool {
    let m=net::implementation(k,p);let z=h.service.states[0];
    at_entry(p,k,h.weak,h.sends,z) && svc::first_path(m,first,h.weak,z,h.service)
}

pub type Input<S> = (Evidence<S>,S,read::Calls,Set<Replica>,Set<Replica>);
pub type Runtime<S> = op::System<State<S>,Event,Op,int,af::View<S>,Input<S>,Evidence<S>>;
pub type Window<S> = op::Window<State<S>,Event,Op,Evidence<S>>;

pub open spec fn entry_witness<S>(p:Program<S>,k:Headers,o:WeakOrder,w:(Exposure,Seq<Event>),
    x:State<S>,ev:Evidence<S>,weak:Seq<Op>) -> bool {
    at_entry(p,k,w.0,w.1,x) && ev==evidence(p,k,w.0) && weak==positions(k,o,w.0)
}
pub type Admission = spec_fn(Exposure)->bool;
// Restrict the functional-T domain to the actual weak interface. Replica
// guards, operation records and all possible ordinary returns stay native.
pub open spec fn system_for<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission) -> Runtime<S> {
    let raw=net::implementation(k,p);
    op::System {
        entry:|x:State<S>,ev:Evidence<S>,weak:Seq<Op>| exists|w:(Exposure,Seq<Event>)| #[trigger] entry_witness(p,k,o,w,x,ev,weak) && allows_entry(w.0),
        step:reg::native_step(raw), quiet:reg::quiet(), installer:retain::ordinary_replica(k),
        calls:|x:State<S>|reg::ledger(raw,first,res,x), record:|x:State<S>|af::view(k,x),
        input:|x:State<S>,_op:Op,ev:Evidence<S>|(ev,crate::fork_information::caller2(x),x.calls,x.requested,x.first_requested),
        service_cut: |x:State<S>,b:Op| b==Op::SR2 && crate::survivors::after_crash(x.cfg.net),
        ordinary_input: |x:State<S>,b:Op,a:Event| b==Op::SR2 && crate::survivors::after_crash(x.cfg.net)
            && !crate::guarded_comparison::weak_work(process_step(x.cfg.net,a)),
    }
}
pub open spec fn window<S>(p:Program<S>,k:Headers,o:WeakOrder,h:Phase<S>) -> Window<S> {
    let wake=crate::fork_alternatives::wake();
    op::Window { service:h.service,handoff:svc::path(net::implementation(k,p),h.service.states.last(),wake),
        producer:Op::SR1,consumer:Op::SR2,writer:observed_writer(h.weak.arm),
        evidence:evidence(p,k,h.weak),weak_order:positions(k,o,h.weak) }
}

// Changing the admitted producer entries and their evidence has no effect
// on the underlying guarded consumer executions.
proof fn same_finish<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
    x:State<S>,t:Seq<(Event,State<S>)>,d:int)
    ensures op::finishes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2,t,d)==op::finishes(reg::system(p,k,first,res),x,Op::SR2,t,d),
    decreases t.len(),
{
    if t.len()>0 {
        let (a,y)=t[0];let raw=net::implementation(k,p);let old=af::after_offers(p,k);
        assert(read::next(raw,x,a)==read::next(old,x,a));
        assert(asm::prefix(raw,x,seq![a],true)==asm::prefix(old,x,seq![a],true)) by {reveal_with_fuel(asm::prefix,2);}
        same_finish(p,k,first,res,o,allows_entry,y,t.drop_first(),d);
    }
}
proof fn transfer_outcome<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
    x:State<S>,y:State<S>,d:int)
    requires crate::survivors::after_crash(x.cfg.net),crate::survivors::after_crash(y.cfg.net),fork::same_reader(x,y),
        af::view(k,x)==af::view(k,y),op::outcomes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2).contains(d),
    ensures op::outcomes(system_for(p,k,first,res,o,allows_entry),y,Op::SR2).contains(d),
{
    let s=actual_option(p,k,first,res,o,allows_entry,x,d);
    let t=af::replay_return(p,k,res,x,y,s,Set::empty());
    option_for(p,k,first,res,o,allows_entry,y,t);
}
proof fn determines<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission)
    ensures op::determined_by_record(system_for(p,k,first,res,o,allows_entry),Op::SR2),
{
    let sys=system_for(p,k,first,res,o,allows_entry);let b=Op::SR2;
    assert forall|x:State<S>,y:State<S>,e:Evidence<S>,f:Evidence<S>| (sys.service_cut)(x,b) && (sys.service_cut)(y,b)
        && (sys.record)(x)==(sys.record)(y) && #[trigger] (sys.input)(x,b,e)==#[trigger] (sys.input)(y,b,f)
        implies op::outcomes(sys,x,b)==op::outcomes(sys,y,b) by {
        let u=op::outcomes(sys,x,b);let v=op::outcomes(sys,y,b);
        assert forall|d:int| #[trigger] u.contains(d)==#[trigger] v.contains(d) by {
            if u.contains(d) {transfer_outcome(p,k,first,res,o,allows_entry,x,y,d);}
            if v.contains(d) {transfer_outcome(p,k,first,res,o,allows_entry,y,x,d);}
        }
        assert(u =~= v);
    }
}

pub(crate) proof fn view_from_queue<S>(k:Headers,x:State<S>,y:State<S>)
    requires svc::ordinary(x)==svc::ordinary(y),survivor(x.cfg.net)==survivor(y.cfg.net),
        (x.cfg.private)(at(Replica::R1))==(y.cfg.private)(at(Replica::R1)),(x.cfg.private)(at(Replica::R2))==(y.cfg.private)(at(Replica::R2)),
    ensures af::view(k,x)==af::view(k,y),
{
    assert forall|msg:net::Message| (#[trigger] (af::view(k,x).copies)(msg))==(af::view(k,y).copies)(msg) by {
        if msg.body.path!=Path::Weak && crate::protocol::survivor_actor(msg.body.to) {
            assert(af::occurrences(k,x.cfg.net,msg) =~= af::occurrences(k,y.cfg.net,msg)) by {
                assert forall|j:nat| #[trigger] af::occurrences(k,x.cfg.net,msg).contains(j)==#[trigger] af::occurrences(k,y.cfg.net,msg).contains(j)
                    by {assert(svc::ordinary(x).get(j)==svc::ordinary(y).get(j));}
            }
        }
    }
    assert(af::view(k,x).copies =~= af::view(k,y).copies);
}
// Fanout adds the same public requests to possibly differently named queues.
// Counts retain the payload ID, body, sender, recipient and multiplicity.
proof fn fan_view<S>(p:Program<S>,k:Headers,x:State<S>,y:State<S>,s:Seq<Event>)
    requires af::view(k,x)==af::view(k,y),svc::fan(net::implementation(k,p),x,s),svc::fan(net::implementation(k,p),y,s),
    ensures af::view(k,asm::drive(net::implementation(k,p),x,s))==af::view(k,asm::drive(net::implementation(k,p),y,s)),
    decreases s.len(),
{
    if s.len()>0 {
        let m=net::implementation(k,p);
        let a=s[0];let u=read::next(m,x,a);let v=read::next(m,y,a);assert(svc::request(a));
        assert(process_step(x.cfg.net,a)==process_step(y.cfg.net,a));
        assert forall|msg:net::Message| (#[trigger] (af::view(k,u).copies)(msg))==(af::view(k,v).copies)(msg) by {
            if msg.body.path!=Path::Weak && crate::protocol::survivor_actor(msg.body.to) {
                assert((af::view(k,x).copies)(msg)==(af::view(k,y).copies)(msg));
                af::visible_count(k,x,msg);af::visible_count(k,y,msg);
                af::visible_count(k,u,msg);af::visible_count(k,v,msg);
                af::count_step(p,k,x,a,msg);af::count_step(p,k,y,a,msg);
            }
        }
        assert(af::view(k,u).copies =~= af::view(k,v).copies);
        fan_view(p,k,u,v,s.drop_first());
    }
}
proof fn same_entry<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,a:Phase<S>,b:Phase<S>)
    requires phase(p,k,first,a),phase(p,k,first,b),a.sends==b.sends,evidence(p,k,a.weak)==evidence(p,k,b.weak),
    ensures af::view(k,a.service.states[0])==af::view(k,b.service.states[0]),
{
    let x=svc::endpoint(p,k,a.weak);let y=svc::endpoint(p,k,b.weak);let s=a.sends;
    fan_view(p,k,x,y,s);
}

pub open spec fn lead<S>(h:Phase<S>) -> Seq<Event> {
    ((svc::weak_trace(h.weak)+h.sends)+h.service.actions)+crate::fork_alternatives::wake()
}
pub open spec fn invoked<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,h:Phase<S>,x:State<S>) -> bool {
    phase(p,k,first,h) && x==fork::invocation(net::implementation(k,p),h.service)
        && asm::prefix(net::implementation(k,p),wc::start(net::implementation(k,p)),lead(h),true)
}
#[verifier::rlimit(20)]
pub(crate) proof fn handoff_for<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,h:Phase<S>)
    requires allows_entry(h.weak),phase(p,k,first,h),crate::first_schedule::startup(net::implementation(k,p)),weak_word(positions(k,o,h.weak)),
    ensures ({
        let m=net::implementation(k,p);let sys=system_for(p,k,first,res,o,allows_entry);let w=window(p,k,o,h);let z=h.service.states.last();
        let x=fork::invocation(m,h.service);let base=wc::start(m);let weak=svc::endpoint(p,k,h.weak);
        invoked(p,k,first,h,x) && asm::drive(m,base,lead(h))==x && fork::available(x) && crate::survivors::after_crash(x.cfg.net)
            && net::trace(p,net::snapshot(k,base),net::turns(k,lead(h)),true)
            && op::genuine(sys,reg::register(),w) && op::observation(sys,w).position==reg::contest()
            && w.handoff.states.last()==x && x.cfg.net.pending==z.cfg.net.pending && af::view(k,z)==af::view(k,x)
            && fork::weak_packets(x)==fork::weak_packets(weak) && survivor(x.cfg.net)==(2int,5int)
            && x.calls==weak.calls && x.first_requested==all_replicas() && x.requested.is_empty()
            && crate::fork_information::caller2(x)==(m.update)((m.initial)(Process::SecondClient),crate::read_issue::local_event(Action::StartSecondClient))
    }),
{
    let m=net::implementation(k,p);let base=wc::start(m);let weak=svc::endpoint(p,k,h.weak);let s=h.service;let z=s.states.last();
    let sys=system_for(p,k,first,res,o,allows_entry);let w=window(p,k,o,h);let wake=crate::fork_alternatives::wake();let x=fork::invocation(m,s);
    let root=s.states[0];
    svc::weak_endpoint(p,k,h.weak);svc::fan_at(m,weak,h.sends,h.sends.len());svc::endpoints(m,weak,h.sends);
    svc::lift_fan(m,weak,h.sends);assert(app::all_available(weak)==weak);
    svc::service_frame(m,s,s.actions.len());
    assert((sys.entry)(root,w.evidence,w.weak_order)) by {assert(entry_witness(p,k,o,(h.weak,h.sends),root,w.evidence,w.weak_order));}
    assert forall|j:int| 0<=j<s.actions.len() implies reg::native_step(m)(s.states[j],#[trigger] s.actions[j],s.states[j+1])
        && reg::quiet()(s.states[j],s.actions[j]) by {
        assert(mail::active_step(m)(s.states[j],s.actions[j],s.states[j+1]) && !mail::posted(m)(s.states[j]));
        assert(read::initial_send(s.states[j],s.actions[j]));
        assert(asm::prefix(m,s.states[j],seq![s.actions[j]],true)) by {reveal_with_fuel(asm::prefix,2);}
    }
    assert forall|j:int| 0<=j<s.actions.len() implies {
        let c=reg::ledger(m,first,res,#[trigger] s.states[j]);
        c.issued.contains(Op::SR1) && !c.replies.contains_key(Op::SR1) && !c.issued.contains(Op::SR2)
    } by {svc::service_frame(m,s,j as nat);assert(!mail::posted(m)(s.states[j]));}
    assert(reg::ledger(m,first,res,z)==reg::publication(h.weak.arm));reg::earlier_source(h.weak.arm);
    tape::recorded(m,s,0);asm::native_prefix(m,root,tape::record(s,0),true);assert(asm::actions(tape::record(s,0)) =~= s.actions);
    assert(asm::prefix(m,z,wake,true)) by {reveal_with_fuel(asm::prefix,4);}
    reg::wake_segment(m,z);svc::endpoints(m,z,wake);
    assert forall|j:int| 0<=j<wake.len() implies !reg::ledger(m,first,res,#[trigger] w.handoff.states[j]).issued.contains(Op::SR2)
        by {assert(j==0 || j==1 || j==2);reveal_with_fuel(asm::drive,3);}
    assert(x.cfg.net.pending==z.cfg.net.pending && svc::ordinary(x)==svc::ordinary(z)
        && x.first_requested==z.first_requested && x.requested==z.requested && x.calls==z.calls
        && crate::survivors::after_crash(x.cfg.net) && survivor(x.cfg.net)==survivor(z.cfg.net)
        && (x.cfg.private)(at(Replica::R1))==(z.cfg.private)(at(Replica::R1))
        && (x.cfg.private)(at(Replica::R2))==(z.cfg.private)(at(Replica::R2))
        && crate::fork_information::caller2(x)==(m.update)((m.initial)(Process::SecondClient),crate::read_issue::local_event(Action::StartSecondClient)))
        by {reveal_with_fuel(asm::drive,4);}
    assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
    view_from_queue(k,z,x);
    assert(op::question(reg::ledger(m,first,res,x),Op::SR1,Op::SR2)==reg::contest()) by {
        assert(op::question(reg::ledger(m,first,res,x),Op::SR1,Op::SR2).background.replies =~= reg::weak_replies());
    }
    asm::prefix_concat(m,base,svc::weak_trace(h.weak),h.sends,true);
    asm::prefix_concat(m,base,svc::weak_trace(h.weak)+h.sends,s.actions,true);
    asm::prefix_concat(m,base,(svc::weak_trace(h.weak)+h.sends)+s.actions,wake,true);
    net::project_prefix(p,k,base,lead(h),true,res);
}

// A pending C1 has no sends during service. Consuming a packet addressed
// to C1 cannot change the ordinary packets that a survivor could consume.
proof fn client_frame<S>(p:Program<S>,k:Headers,x:State<S>,a:Event,y:State<S>)
    requires mail::active_step(net::implementation(k,p))(x,a,y),!mail::posted(net::implementation(k,p))(x),
        !x.cfg.net.second_started,!(process_step(x.cfg.net,a).actor is At),
    ensures af::view(k,x)==af::view(k,y),
{
    let e=process_step(x.cfg.net,a);assert(e.actor==Process::FirstClient && !(a is Send));
    assert(y.cfg.net.locals =~= x.cfg.net.locals);
    assert forall|msg:net::Message| (#[trigger] (af::view(k,x).copies)(msg))==(af::view(k,y).copies)(msg) by {
        if msg.body.path!=Path::Weak && crate::protocol::survivor_actor(msg.body.to) {
            assert(af::occurrences(k,x.cfg.net,msg) =~= af::occurrences(k,y.cfg.net,msg));
        }
    }
    assert(af::view(k,x).copies =~= af::view(k,y).copies);
}

proof fn last_change<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,h:Phase<S>,i:nat) -> (j:int)
    requires phase(p,k,first,h),i<h.service.states.len(),
        !h.service.states[0].cfg.net.second_started,svc::replica_weak(h.service.states[0]),
        af::view(k,h.service.states[0])!=af::view(k,h.service.states.last()),
        af::view(k,h.service.states[i as int])==af::view(k,h.service.states.last()),
    ensures ({
        let s=h.service;
        0<=j<s.actions.len() && retain::ordinary_replica(k)(s.states[j],s.actions[j])
            && af::view(k,s.states[j])!=af::view(k,s.states.last())
            && af::view(k,s.states[j+1])==af::view(k,s.states.last())
    }),
    decreases i,
{
    let m=net::implementation(k,p);let s=h.service;
    assert(i>0);let j=i as int-1;let x=s.states[j];let y=s.states[i as int];let a=s.actions[j];
    if af::view(k,x)==af::view(k,y) {last_change(p,k,first,h,(i-1) as nat)} else {
        svc::service_frame(m,s,j as nat);
        assert(mail::active_step(m)(x,a,y) && !mail::posted(m)(x) && !app::weak_replica_step()(x,a,y));
        if !(process_step(x.cfg.net,a).actor is At) {client_frame(p,k,x,a,y);}
        j
    }
}

proof fn installed_exit<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,h:Phase<S>)
    requires phase(p,k,first,h), af::view(k,h.service.states[0])!=af::view(k,h.service.states.last()),
    ensures retain::installed(op::observation(system_for(p,k,first,res,o,allows_entry),window(p,k,o,h))),
{
    let sys=system_for(p,k,first,res,o,allows_entry);let w=window(p,k,o,h);let s=h.service;let m=net::implementation(k,p);
    let weak=svc::endpoint(p,k,h.weak);svc::weak_endpoint(p,k,h.weak);
    svc::fan_at(m,weak,h.sends,h.sends.len());svc::endpoints(m,weak,h.sends);
    let j=last_change(p,k,first,h,s.actions.len());
    let z=op::observation(sys,w);let prev=af::view(k,s.states[j]);
    assert(z.ordinary_edges.contains((prev,z.exit)));
}

proof fn supports_value(b:Fork,d:int)
    ensures op::supports(reg::register(),reg::contest(),observed_writer(b),d)==(d==first_value(b)),
{
    reg::register_question_is_exact(b,d);let w=observed_writer(b);let h=order::at_first(b);
    order::canonical_orders_exist(b);order::extension_iff_writer(b,h,w);
    if retain::keeps_value()(h.ops,w,d) {
        let v=choose|v:Op| order::weak(v) && d==crate::next(v,1) && #[trigger] order::can_keep(h.ops,w,v);
        order::extension_iff_writer(b,h,v);
    } else if d==first_value(b) {assert(d==crate::next(w,1) && order::can_keep(h.ops,w,w));}
}

proof fn asymmetric(o:Seq<Op>,a:Op,b:Op)
    ensures !crate::precedence::has_precedence(o,a,b) || !crate::precedence::has_precedence(o,b,a),
{
    if crate::precedence::has_precedence(o,a,b) && crate::precedence::has_precedence(o,b,a) {
        let i=choose|i:int| 0<=i<o.len() && #[trigger] o[i]==a && forall|j:int| i<j<o.len() ==> #[trigger] o[j]!=b;
        let j=choose|j:int| 0<=j<o.len() && #[trigger] o[j]==b && forall|i:int| j<i<o.len() ==> #[trigger] o[i]!=a;
        assert(i!=j);
    }
}

pub type Episode<S> = retain::Episode<Op,op::Question<Op,int>,af::View<S>,Input<S>>;
proof fn direction<S>(a:Episode<S>,b:Episode<S>,l:Fork,r:Fork,ds:ISet<int>,other:ISet<int>)
    requires l.branch!=r.branch,a.writer==observed_writer(l),b.writer==observed_writer(r),
        a.position==reg::contest(),b.position==reg::contest(),retain::retained_difference(a,b),
        !crate::precedence::has_precedence(a.weak_order,a.writer,b.writer) || !crate::precedence::has_precedence(b.weak_order,a.writer,b.writer),
        ds.contains(first_value(l)),other.contains(first_value(r)),
        forall|d:int| #[trigger] other.contains(d) ==> d==first_value(r),
    ensures retain::unsupported_outcomes(a,b,ds,other,|q:op::Question<Op,int>,w:Op,d:int|op::supports(reg::register(),q,w,d)),
{
    hide(op::supports);
    let test=|q:op::Question<Op,int>,w:Op,d:int|op::supports(reg::register(),q,w,d);
    supports_value(l,first_value(l));supports_value(r,first_value(l));supports_value(l,first_value(r));supports_value(r,first_value(r));
    assert(test(a.position,a.writer,first_value(l)) && !test(b.position,b.writer,first_value(l)));
    assert(retain::resolves(other,(b.position,b.writer),(a.position,a.writer),test));
}

proof fn rules_out_both<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
    l:Phase<S>,r:Phase<S>)
    requires allows_entry(l.weak),allows_entry(r.weak),phase(p,k,first,l),phase(p,k,first,r),l.weak.arm.branch!=r.weak.arm.branch,
        l.sends==r.sends,evidence(p,k,l.weak)==evidence(p,k,r.weak),
        crate::first_schedule::startup(net::implementation(k,p)), weak_word(positions(k,o,l.weak)),weak_word(positions(k,o,r.weak)),
        op::operation_t(system_for(p,k,first,res,o,allows_entry),reg::register()), ({
            let sys=system_for(p,k,first,res,o,allows_entry);let m=net::implementation(k,p);
            let u=op::outcomes(sys,fork::invocation(m,l.service),Op::SR2);
            let v=op::outcomes(sys,fork::invocation(m,r.service),Op::SR2);
            u.contains(first_value(l.weak.arm)) && v.contains(first_value(r.weak.arm))
                && (forall|d:int| #[trigger] u.contains(d) ==> d==first_value(l.weak.arm))
                && (forall|d:int| #[trigger] v.contains(d) ==> d==first_value(r.weak.arm))
        }),
    ensures false,
{
    hide(op::genuine);hide(op::supports);hide(op::finishes);hide(phase);hide(svc::service_entry);
    let sys=system_for(p,k,first,res,o,allows_entry);let m=net::implementation(k,p);let wa=window(p,k,o,l);let wb=window(p,k,o,r);
    let a=op::observation(sys,wa);let b=op::observation(sys,wb);let x=fork::invocation(m,l.service);let y=fork::invocation(m,r.service);
    let u=op::outcomes(sys,x,Op::SR2);let v=op::outcomes(sys,y,Op::SR2);
    handoff_for(p,k,first,res,o,allows_entry,l);handoff_for(p,k,first,res,o,allows_entry,r);same_entry(p,k,first,l,r);determines(p,k,first,res,o,allows_entry);
    assert((sys.input)(x,Op::SR2,wa.evidence)==(sys.input)(y,Op::SR2,wb.evidence)) by {
        reveal(phase);reveal(svc::service_entry);svc::weak_endpoint(p,k,l.weak);svc::weak_endpoint(p,k,r.weak);
    }
    assert(a.input==b.input && a.entry==b.entry && a.exit==a.inherited && b.exit==b.inherited);
    assert(u!=v);
    assert((sys.service_cut)(x,Op::SR2) && (sys.service_cut)(y,Op::SR2));
    assert(a.inherited!=b.inherited);
    if a.entry!=a.exit {installed_exit(p,k,first,res,o,allows_entry,l);} else {installed_exit(p,k,first,res,o,allows_entry,r);}
    assert(retain::retained_difference(a,b) && retain::retained_difference(b,a));
    asymmetric(a.weak_order,a.writer,b.writer);
    let test=|q:op::Question<Op,int>,w:Op,d:int|op::supports(reg::register(),q,w,d);
    if !crate::precedence::has_precedence(a.weak_order,a.writer,b.writer) {
        direction(a,b,l.weak.arm,r.weak.arm,u,v);
        assert(!retain::unsupported_outcomes(a,b,u,v,test));
    } else {
        direction(b,a,r.weak.arm,l.weak.arm,v,u);
        assert(!retain::unsupported_outcomes(b,a,v,u,test));
    }
}

pub struct Execution<S> { pub first:Phase<S>, pub second:Seq<Event> }
pub open spec fn result<S>(m:Program<S>,res:spec_fn(S)->Option<int>,h:Execution<S>) -> int {
    fork::value(m,res,fork::invocation(m,h.first.service),h.second).unwrap()
}
pub open spec fn completed<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,h:Execution<S>) -> bool {
    let m=net::implementation(k,p);let f=h.first;let x=fork::invocation(m,f.service);let base=wc::start(m);
    let all=lead(f)+h.second;let z=asm::drive(m,base,all);let d=result(m,res,h);
    let w=crate::guarded_history::weak_end();
    w.answers.get(crate::weak_round::request(Op::W1).id)==Some(1)
        && w.answers.get(crate::weak_round::request(Op::W2).id)==Some(1) && crate::weak_round::origin_only(w)
        && (forall|r:Replica| (#[trigger] (base.cfg.net.locals)(r))==(w.front.base.disk)(r).value)
        && invoked(p,k,first,f,x) && fork::completes(m,res,x,h.second,true) && fork::available(x)
        && asm::prefix(m,base,all,true) && net::trace(p,net::snapshot(k,base),net::turns(k,all),true)
        && net::end(p,net::snapshot(k,base),net::turns(k,all))==net::snapshot(k,z)
        && first((f.service.states.last().cfg.private)(Process::FirstClient))==first_value(f.weak.arm)
        && res(crate::fork_information::caller2(z))==Some(d) && (d==2 || d==5)
        && x.cfg.net.pending==f.service.states.last().cfg.net.pending
        && fork::weak_packets(z)==fork::weak_packets(svc::endpoint(p,k,f.weak))
        && (forall|i:int| 0<=i<f.service.states.len() ==> #[trigger] fork::weak_packets(f.service.states[i])==fork::weak_packets(x))
        && (forall|i:int| 0<=i<=h.second.len() ==> #[trigger] fork::weak_packets(fork::states(m,x,h.second)[i])==fork::weak_packets(x))
        && forall|i:int| 0<=i<h.second.len() ==> crate::protocol::survivor_actor(
            #[trigger] process_step(fork::states(m,x,h.second)[i].cfg.net,h.second[i]).actor)
}

proof fn publish<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,h:Execution<S>,
    run:crate::fair_read::Runnable)
    requires allows_entry(h.first.weak),phase(p,k,first,h.first),weak_word(positions(k,o,h.first.weak)),crate::first_schedule::startup(net::implementation(k,p)), ({
        let m=net::implementation(k,p);let x=fork::invocation(m,h.first.service);
        fork::completes(m,res,x,h.second,true) && fork::invocation_a(m,res,x,run)
    }),
    ensures completed(p,k,first,res,h),
{
    let m=net::implementation(k,p);let f=h.first;let x=fork::invocation(m,f.service);let base=wc::start(m);
    crate::weak_round::actual_overlap(f.weak.arm);
    crate::isolated_rmws();
    assert forall|r:Replica| (#[trigger] (base.cfg.net.locals)(r))==(crate::guarded_history::weak_end().front.base.disk)(r).value by {
        assert((crate::guarded_history::weak_end().front.base.disk)(r).value==(state_after(f.weak.arm,0).locals)(r));
    }
    handoff_for(p,k,first,res,o,allows_entry,f);fork::sampled_native_return(m,res,x,h.second,run);
    let weak=svc::endpoint(p,k,f.weak);svc::weak_endpoint(p,k,f.weak);
    svc::fan_at(m,weak,f.sends,f.sends.len());svc::endpoints(m,weak,f.sends);
    assert forall|i:int| 0<=i<f.service.states.len() implies #[trigger] fork::weak_packets(f.service.states[i])==fork::weak_packets(x)
        by {svc::service_frame(m,f.service,i as nat);}
    svc::endpoints(m,x,h.second);asm::prefix_concat(m,base,lead(f),h.second,true);
    net::project_prefix(p,k,base,lead(f)+h.second,true,res);
}

proof fn option_for<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,x:State<S>,s:Seq<Event>)
    requires crate::survivors::after_crash(x.cfg.net),fork::completes(net::implementation(k,p),res,x,s,true),
    ensures op::outcomes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2).contains(fork::value(net::implementation(k,p),res,x,s).unwrap()),
{
    let m=net::implementation(k,p);let d=fork::value(m,res,x,s).unwrap();fork::completion_facts(m,res,x,s);
    let t=reg::native_to_window_return(p,k,first,res,x,s,d);same_finish(p,k,first,res,o,allows_entry,x,t,d);
    assert(op::finishes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2,t,d));
}
proof fn actual_option<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,x:State<S>,d:int)
    -> (s:Seq<Event>)
    requires crate::survivors::after_crash(x.cfg.net),op::outcomes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2).contains(d),
    ensures fork::completes(net::implementation(k,p),res,x,s,true),fork::value(net::implementation(k,p),res,x,s)==Some(d),
{
    let sys=system_for(p,k,first,res,o,allows_entry);
    let t=choose|t:Seq<(Event,State<S>)>| #[trigger] op::finishes(sys,x,Op::SR2,t,d);
    same_finish(p,k,first,res,o,allows_entry,x,t,d);reg::window_to_native_return(p,k,first,res,x,t,d)
}

pub open spec fn bad<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,h:Execution<S>) -> bool {
    !crate::coupled_reads::legal_returns(first((h.first.service.states.last().cfg.private)(Process::FirstClient)),result(m,res,h))
}

proof fn incompatible(b:Fork,d:int)
    requires d!=first_value(b),
    ensures !crate::coupled_reads::legal_returns(first_value(b),d),
{
    if crate::coupled_reads::legal_returns(first_value(b),d) {
        let (ops,states)=choose|ops:Seq<Op>,states:Seq<int>| #[trigger] crate::legal(ops,states,first_value(b),d);
        order::exact_completed_order(b,crate::RecoveredOrder{ops,states},d);
    }
}

// Only two reached SR2 invocations need service. All possible ordinary
// returns there are real guarded continuations of these same weak prefixes.
#[verifier::rlimit(18)]
proof fn finish_admitted_phases<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
    l:Phase<S>,r:Phase<S>,run:crate::fair_read::Runnable) -> (pair:(Execution<S>,Execution<S>))
    requires allows_entry(l.weak),allows_entry(r.weak),phase(p,k,first,l),phase(p,k,first,r),l.weak.arm.branch!=r.weak.arm.branch,l.sends==r.sends,
        evidence(p,k,l.weak)==evidence(p,k,r.weak),weak_word(positions(k,o,l.weak)),weak_word(positions(k,o,r.weak)),
        crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system_for(p,k,first,res,o,allows_entry),reg::register()), ({
            let m=net::implementation(k,p);
            fork::opportunity(m,res,fork::invocation(m,l.service),run) && fork::opportunity(m,res,fork::invocation(m,r.service),run)
        }),
    ensures pair.0.first==l,pair.1.first==r,completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
        bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
{
    hide(op::genuine);hide(op::supports);hide(op::operation_t);
    let m=net::implementation(k,p);let x=fork::invocation(m,l.service);let y=fork::invocation(m,r.service);
    let a=l.weak.arm;let b=r.weak.arm;let sys=system_for(p,k,first,res,o,allows_entry);
    handoff_for(p,k,first,res,o,allows_entry,l);handoff_for(p,k,first,res,o,allows_entry,r);
    let u=op::outcomes(sys,x,Op::SR2);let v=op::outcomes(sys,y,Op::SR2);
    let s=fork::native_return_from_a(m,res,x,run);let t=fork::native_return_from_a(m,res,y,run);
    option_for(p,k,first,res,o,allows_entry,x,s);option_for(p,k,first,res,o,allows_entry,y,t);
    let (left,right)=if exists|d:int| #[trigger] u.contains(d) && d!=first_value(a) {
        let d=choose|d:int| #[trigger] u.contains(d) && d!=first_value(a);
        incompatible(a,d);(actual_option(p,k,first,res,o,allows_entry,x,d),t)
    } else if exists|d:int| #[trigger] v.contains(d) && d!=first_value(b) {
        let d=choose|d:int| #[trigger] v.contains(d) && d!=first_value(b);
        incompatible(b,d);(s,actual_option(p,k,first,res,o,allows_entry,y,d))
    } else {
        assert(u.contains(first_value(a)) && v.contains(first_value(b)));
        rules_out_both(p,k,first,res,o,allows_entry,l,r);(s,t)
    };
    let h=Execution {first:l,second:left};let g=Execution {first:r,second:right};
    publish(p,k,first,res,o,allows_entry,h,run);publish(p,k,first,res,o,allows_entry,g,run);(h,g)
}

pub open spec fn fresh_caller<S>(p:Program<S>,plan:svc::Requests) -> bool {
    !(p.done)((p.initial)(Process::FirstClient)) && svc::recipients(plan).no_duplicates()
        && svc::recipients(plan).to_set()==all_replicas() && svc::supported(p,(p.initial)(Process::FirstClient),plan)
}

pub open spec fn second_opportunities<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    run:crate::fair_read::Runnable,l:Exposure,r:Exposure) -> bool {
    forall|h:Phase<S>| (h.weak==l || h.weak==r) && #[trigger] invoked(p,k,first,h,fork::invocation(net::implementation(k,p),h.service))
        ==> fork::opportunity(net::implementation(k,p),res,fork::invocation(net::implementation(k,p),h.service),run)
}

// Optional R3 work after installation, including any real confirmation
// actually sent, is part of each supplied exposure and its public trace.
pub proof fn original_hot_at_admitted_exposures<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    o:WeakOrder,allows_entry:Admission,l:Exposure,r:Exposure,plan:svc::Requests,run:crate::fair_read::Runnable) -> (pair:(Execution<S>,Execution<S>))
    requires allows_entry(l),allows_entry(r),svc::service_entry(p,k,l),svc::service_entry(p,k,r),l.arm.branch!=r.arm.branch,evidence(p,k,l)==evidence(p,k,r),
        weak_word(positions(k,o,l)),weak_word(positions(k,o,r)),fresh_caller(p,plan),
        crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system_for(p,k,first,res,o,allows_entry),reg::register()),
        svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,l),l.arm),run),
        svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,r),r.arm),run),
        second_opportunities(p,k,first,res,run,l,r),
    ensures pair.0.first.weak==l,pair.1.first.weak==r,pair.0.first.sends==pair.1.first.sends,svc::contents(k,pair.0.first.sends)==plan,
        completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
        bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
{
    let m=net::implementation(k,p);let s=svc::paired_fanout(p,k,first,l,r,plan);
    let a=svc::first_service(p,k,first,res,l,s,run);let b=svc::first_service(p,k,first,res,r,s,run);
    let h=Phase{weak:l,sends:s,service:a};let g=Phase{weak:r,sends:s,service:b};
    assert(phase(p,k,first,h) && phase(p,k,first,g)) by {
        svc::weak_endpoint(p,k,l);svc::weak_endpoint(p,k,r);
        svc::lift_fan(m,svc::reference(svc::endpoint(p,k,l),l.arm),s);
        svc::lift_fan(m,svc::reference(svc::endpoint(p,k,r),r.arm),s);
    }
    handoff_for(p,k,first,res,o,allows_entry,h);handoff_for(p,k,first,res,o,allows_entry,g);finish_admitted_phases(p,k,first,res,o,allows_entry,h,g,run)
}

pub(crate) proof fn laws_at_exposures<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,
    run:crate::fair_read::Runnable,l:Exposure,r:Exposure)
    requires svc::service_entry(p,k,l),svc::service_entry(p,k,r),
        svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        crate::first_schedule::startup(net::implementation(k,p)),
        weak_word(positions(k,o,l)),weak_word(positions(k,o,r)),
    ensures svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,l),l.arm),run),
        svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,r),r.arm),run),
        second_opportunities(p,k,first,res,run,l,r),
{
    let m=net::implementation(k,p);let base=wc::start(m);
    svc::reference_laws(p,k,l,first,res,run);svc::reference_laws(p,k,r,first,res,run);
    assert forall|h:Phase<S>| (h.weak==l || h.weak==r) && #[trigger] invoked(p,k,first,h,fork::invocation(m,h.service))
        implies fork::opportunity(m,res,fork::invocation(m,h.service),run) by {
            let x=fork::invocation(m,h.service);handoff_for(p,k,first,res,o,|_entry:Exposure|true,h);
            assert(svc::reaches(m,base,(lead(h),None,seq![]),x));assert(svc::reachable(m,base,x));
        }
}

}
