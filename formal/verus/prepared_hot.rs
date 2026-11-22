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
pub open spec fn log<S>(p:Program<S>,k:Headers,x:State<S>,s:Seq<Event>) -> Seq<Observation>
    decreases s.len(),
{
    if s.len()==0 {seq![]} else {
        let e=net::callback(k,process_step(x.cfg.net,s[0]));
        let t=log(p,k,read::next(net::implementation(k,p),x,s[0]),s.drop_first());
        if e.actor==at(Replica::R1) || e.actor==at(Replica::R2) {seq![e]+t} else {t}
    }
}
pub open spec fn evidence<S>(p:Program<S>,k:Headers,e:Exposure) -> Evidence<S> {
    af::view(k,svc::endpoint(p,k,e))
}
proof fn log_join<S>(p:Program<S>,k:Headers,x:State<S>,a:Seq<Event>,b:Seq<Event>)
    ensures log(p,k,x,a+b)==log(p,k,x,a)+log(p,k,asm::drive(net::implementation(k,p),x,a),b),
    decreases a.len(),
{
    if a.len()==0 {assert(a+b =~= b);} else {
        let y=read::next(net::implementation(k,p),x,a[0]);
        assert((a+b).drop_first() =~= a.drop_first()+b);log_join(p,k,y,a.drop_first(),b);
        assert(log(p,k,x,a+b) =~= log(p,k,x,a)+log(p,k,asm::drive(net::implementation(k,p),x,a),b));
    }
}
proof fn third_log<S>(p:Program<S>,k:Headers,x:State<S>,t:Seq<Event>)
    requires vis::background_prefix(net::implementation(k,p),x,t),vis::at_site(t,Replica::R3),
    ensures log(p,k,x,t).len()==0,
    decreases t.len(),
{
    if t.len()>0 {
        let a=t[0];let tail=t.drop_first();
        assert(wc::background(a) && vis::local_input(a).actor==at(Replica::R3));
        assert forall|i:int| 0<=i<tail.len() implies #[trigger] wc::background(tail[i])
            && vis::local_input(tail[i]).actor==at(Replica::R3) by {assert(tail[i]==t[i+1]);}
        third_log(p,k,read::next(net::implementation(k,p),x,a),tail);
    }
}
proof fn installed_log<S>(p:Program<S>,k:Headers,b:Fork,c:vis::Cut,t:Seq<Event>)
    requires vis::installation(p,k,b,c,t),
    ensures ({
        let x=wc::start(net::implementation(k,p));
        log(p,k,x,svc::weak_trace(svc::selected(c,t,b)))==log(p,k,x,c.pre)
    }),
{
    let m=net::implementation(k,p);let x=wc::start(m);let z=asm::drive(m,x,c.pre);
    let pre=c.pre+t;let e=svc::selected(c,t,b);let q=asm::drive(m,x,pre);let d=seq![Action::Deliver(svc::selected_handle(c,b))];
    asm::prefix_concat(m,x,c.pre,t,true);
    assert forall|i:int| 0<=i<t.len() implies #[trigger] wc::background(t[i]) by {assert(t[i]==pre[c.pre.len()+i]);}
    third_log(p,k,z,t);log_join(p,k,x,c.pre,t);log_join(p,k,x,pre,d);
    assert(process_step(q.cfg.net,d[0]).actor==at(Replica::R3));
    assert(log(p,k,q,d)==Seq::<Observation>::empty()) by {reveal_with_fuel(log,2);}
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
pub open spec fn system<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder) -> Runtime<S> {
    system_for(p,k,first,res,o,|e:Exposure| svc::exposed(p,k,e))
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

// Receipt-only callers retain their original functional-T entry domain.
pub proof fn handoff<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,h:Phase<S>)
    requires phase(p,k,first,h),svc::exposed(p,k,h.weak),crate::first_schedule::startup(net::implementation(k,p)),weak_word(positions(k,o,h.weak)),
    ensures ({
        let m=net::implementation(k,p);let sys=system(p,k,first,res,o);let w=window(p,k,o,h);let z=h.service.states.last();
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
    handoff_for(p,k,first,res,o,|e:Exposure|svc::exposed(p,k,e),h);
}

pub proof fn finish_phases<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,
    l:Phase<S>,r:Phase<S>,run:crate::fair_read::Runnable) -> (pair:(Execution<S>,Execution<S>))
    requires phase(p,k,first,l),phase(p,k,first,r),svc::exposed(p,k,l.weak),svc::exposed(p,k,r.weak),l.weak.arm.branch!=r.weak.arm.branch,l.sends==r.sends,
        evidence(p,k,l.weak)==evidence(p,k,r.weak),weak_word(positions(k,o,l.weak)),weak_word(positions(k,o,r.weak)),
        crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system(p,k,first,res,o),reg::register()), ({
            let m=net::implementation(k,p);
            fork::opportunity(m,res,fork::invocation(m,l.service),run) && fork::opportunity(m,res,fork::invocation(m,r.service),run)
        }),
    ensures pair.0.first==l,pair.1.first==r,completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
        bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
{
    finish_admitted_phases(p,k,first,res,o,|e:Exposure|svc::exposed(p,k,e),l,r,run)
}

pub proof fn original_hot_at_exposures<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    o:WeakOrder,l:Exposure,r:Exposure,plan:svc::Requests,run:crate::fair_read::Runnable) -> (pair:(Execution<S>,Execution<S>))
    requires svc::exposed(p,k,l),svc::exposed(p,k,r),l.arm.branch!=r.arm.branch,evidence(p,k,l)==evidence(p,k,r),
        weak_word(positions(k,o,l)),weak_word(positions(k,o,r)),fresh_caller(p,plan),
        crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system(p,k,first,res,o),reg::register()),
        svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,l),l.arm),run),
        svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,r),r.arm),run),
        second_opportunities(p,k,first,res,run,l,r),
    ensures pair.0.first.weak==l,pair.1.first.weak==r,pair.0.first.sends==pair.1.first.sends,svc::contents(k,pair.0.first.sends)==plan,
        completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
        bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
{
    original_hot_at_admitted_exposures(p,k,first,res,o,|e:Exposure|svc::exposed(p,k,e),l,r,plan,run)
}

pub open spec fn original_pair<S>(p:Program<S>,k:Headers,n:Notice,f:(vis::Cut,Seq<Event>,Seq<Event>),l:Exposure,r:Exposure) -> bool {
    vis::paired_installation(p,k,n,f) && l==svc::selected(f.0,f.1,alpha(n)) && r==svc::selected(f.0,f.2,beta(n))
}
pub open spec fn at_prepared_entries<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    o:WeakOrder,n:Notice,run:crate::fair_read::Runnable,f:(vis::Cut,Seq<Event>,Seq<Event>)) -> bool {
    let m=net::implementation(k,p);let l=svc::selected(f.0,f.1,alpha(n));let r=svc::selected(f.0,f.2,beta(n));
    weak_word(positions(k,o,l)) && weak_word(positions(k,o,r))
        && svc::service_laws(m,first,svc::reference(svc::endpoint(p,k,l),l.arm),run)
        && svc::service_laws(m,first,svc::reference(svc::endpoint(p,k,r),r.arm),run)
        && second_opportunities(p,k,first,res,run,l,r)
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

pub proof fn laws_at_pair<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,n:Notice,
    run:crate::fair_read::Runnable,f:(vis::Cut,Seq<Event>,Seq<Event>))
    requires vis::paired_installation(p,k,n,f),
        svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        crate::first_schedule::startup(net::implementation(k,p)),
        weak_word(positions(k,o,svc::selected(f.0,f.1,alpha(n)))),weak_word(positions(k,o,svc::selected(f.0,f.2,beta(n)))),
    ensures at_prepared_entries(p,k,first,res,o,n,run,f),
{
    let l=svc::selected(f.0,f.1,alpha(n));let r=svc::selected(f.0,f.2,beta(n));
    svc::from_installation(p,k,l.arm,f.0,f.1);svc::from_installation(p,k,r.arm,f.0,f.2);
    laws_at_exposures(p,k,first,res,o,run,l,r);
}

// This predicate refers only to the two post-RMW preparations. Scheduler
// handles, R3's memory and weak packets still awaiting delivery are private
// to each execution. No read continuation or result occurs in the test.
pub open spec fn matching_preparations<S>(p:Program<S>,k:Headers,l:Exposure,r:Exposure) -> bool {
    l.arm.branch==crate::Branch::Alpha && r.arm.branch==crate::Branch::Beta
        && svc::exposed(p,k,l) && svc::exposed(p,k,r) && evidence(p,k,l)==evidence(p,k,r)
}

// Supply this lemma independently in each arm. All matching data and weak
// order inputs can be checked directly on the application's channel traces.
pub proof fn exposure_from_channel<S>(p:Program<S>,k:Headers,b:Fork,ts:Seq<net::Turn>) -> (result:(Exposure,Map<nat,nat>))
    requires ({
        let x=net::snapshot(k,wc::start(net::implementation(k,p)));let z=net::end(p,x,ts);
        net::trace(p,x,ts,true) && vis::replica_word(vis::channel_callbacks(p,x,ts))
            && survivor(z.local.cfg.net)==(2int,5int) && (z.local.cfg.net.locals)(Replica::R3)==first_value(b)
    }),
    ensures ({
        let (e,keys)=result;let m=net::implementation(k,p);let x=wc::start(m);let public=net::snapshot(k,x);
        let z=net::end(p,public,ts);let q=svc::endpoint(p,k,e);
        e.arm==b && svc::exposed(p,k,e) && evidence(p,k,e)==af::channel_view(z)
            && net::same_callbacks(p,k,x,e.events,public,ts) && vis::callbacks(k,x.cfg.net,e.events)==vis::channel_callbacks(p,public,ts)
            && z.local==net::control(q) && net::represents(z.packets,keys,net::queue(k,q.cfg.net))
    }),
{
    let m=net::implementation(k,p);let x=wc::start(m);let public=net::snapshot(k,x);
    assert(public.packets =~= Map::empty());
    let (s,keys)=net::lift_prefix(p,k,x,public,Map::empty(),ts,true,|_s:S|None);
    vis::lift_replica_callbacks(p,k,x,s,public,ts);
    af::represented_view(k,asm::drive(m,x,s),net::end(p,public,ts),keys);
    (Exposure{arm:b,events:s},keys)
}

// Locate the installing receipt in the supplied trace and its actual send.
// This is an ingress/visibility fact; the register history identifies the
// abstract weak writer when the subsequent strong read returns this value.
pub open spec fn sourced_application<S>(p:Program<S>,k:Headers,e:Exposure,i:int) -> bool {
    let m=net::implementation(k,p);let x=wc::start(m);let s=svc::weak_trace(e);
    let q=asm::drive(m,x,s.take(i));let a=s[i];let h=a->Deliver_0;
    let incoming=q.cfg.net.pending[h];let input=net::input(k,q.cfg.net,net::Command::Deliver(h));
    let y=read::next(m,q,a);
    vis::applies_at(m,x,s,first_value(e.arm),i)
        && input.incoming==Some(incoming) && input.actor==at(Replica::R3)
        && (y.cfg.private)(at(Replica::R3))==(p.update)((q.cfg.private)(at(Replica::R3)),input)
        && net::queue(k,y.cfg.net)==net::queue(k,q.cfg.net).remove(h)
        && exists|j:int| 0<=j<i && #[trigger] s[j]==Action::Send(h,incoming)
}

pub proof fn preparation_application<S>(p:Program<S>,k:Headers,e:Exposure) -> (i:int)
    requires svc::exposed(p,k,e),
    ensures sourced_application(p,k,e,i),
{
    let m=net::implementation(k,p);let x=wc::start(m);let s=svc::weak_trace(e);
    crate::isolated_rmws();svc::weak_endpoint(p,k,e);
    let i=vis::find_application(m,x,s,first_value(e.arm));
    let pre=s.take(i);let a=s[i];let h=a->Deliver_0;let q=asm::drive(m,x,pre);
    assert(pre+s.skip(i) =~= s);
    asm::prefix_concat(m,x,pre,s.skip(i),true);
    wc::prefix_packet_source(m,x,pre,h,q.cfg.net.pending[h]);
    let j=choose|j:int| 0<=j<pre.len() && #[trigger] pre[j]==Action::Send(h,q.cfg.net.pending[h]);
    assert(s[j]==pre[j]);
    net::project_step(p,k,q,a,false);
    i
}

pub proof fn original_hot_from_matched_preparations<S>(
    p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,
    l:Exposure,r:Exposure,plan:svc::Requests,run:crate::fair_read::Runnable,
) -> (pair:(Execution<S>,Execution<S>))
    requires matching_preparations(p,k,l,r), fresh_caller(p,plan),
        crate::first_schedule::startup(net::implementation(k,p)),
        svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        weak_word(positions(k,o,l)),weak_word(positions(k,o,r)),
        op::operation_t(system(p,k,first,res,o),reg::register()),
    ensures pair.0.first.weak==l,pair.1.first.weak==r,
        (exists|i:int| #[trigger] sourced_application(p,k,l,i)),(exists|i:int| #[trigger] sourced_application(p,k,r,i)),
        pair.0.first.sends==pair.1.first.sends,svc::contents(k,pair.0.first.sends)==plan,
        completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
        bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
{
    preparation_application(p,k,l);preparation_application(p,k,r);
    laws_at_exposures(p,k,first,res,o,run,l,r);
    original_hot_at_exposures(p,k,first,res,o,l,r,plan,run)
}

pub proof fn matching_from_installation<S>(p:Program<S>,k:Headers,n:Notice,f:(vis::Cut,Seq<Event>,Seq<Event>))
    requires vis::paired_installation(p,k,n,f),
    ensures ({
        let l=svc::selected(f.0,f.1,alpha(n));let r=svc::selected(f.0,f.2,beta(n));
        let x=wc::start(net::implementation(k,p));
        matching_preparations(p,k,l,r) && log(p,k,x,l.events)==log(p,k,x,r.events)
    }),
{
    let l=svc::selected(f.0,f.1,alpha(n));let r=svc::selected(f.0,f.2,beta(n));
    svc::from_installation(p,k,l.arm,f.0,f.1);svc::from_installation(p,k,r.arm,f.0,f.2);
    let x=svc::endpoint(p,k,l);let y=svc::endpoint(p,k,r);
    assert(svc::ordinary(x) =~= svc::ordinary(y));
    view_from_queue(k,x,y);
    installed_log(p,k,l.arm,f.0,f.1);installed_log(p,k,r.arm,f.0,f.2);
}

// A single chosen installation pair suffices. In particular schedule_offers
// supplies f=(cut,[],[]) for a literal common prefix up to the receipt.
pub proof fn original_hot_at_installation<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    o:WeakOrder,n:Notice,plan:svc::Requests,run:crate::fair_read::Runnable,f:(vis::Cut,Seq<Event>,Seq<Event>)) -> (pair:(Execution<S>,Execution<S>))
    requires vis::paired_installation(p,k,n,f),at_prepared_entries(p,k,first,res,o,n,run,f),fresh_caller(p,plan),
        crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system(p,k,first,res,o),reg::register()),
    ensures original_pair(p,k,n,f,pair.0.first.weak,pair.1.first.weak),pair.0.first.sends==pair.1.first.sends,
        evidence(p,k,pair.0.first.weak)==evidence(p,k,pair.1.first.weak),
        ({let x=wc::start(net::implementation(k,p));log(p,k,x,pair.0.first.weak.events)==log(p,k,x,pair.1.first.weak.events)}),
        svc::contents(k,pair.0.first.sends)==plan,completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
        bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
{
    let l=svc::selected(f.0,f.1,alpha(n));let r=svc::selected(f.0,f.2,beta(n));
    matching_from_installation(p,k,n,f);
    original_hot_at_exposures(p,k,first,res,o,l,r,plan,run)
}

pub proof fn original_hot_from_selective_visibility<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    o:WeakOrder,n:Notice,plan:svc::Requests,run:crate::fair_read::Runnable) -> (pair:(Execution<S>,Execution<S>))
    requires vis::selective_input(p,alpha(n)),vis::selective_input(p,beta(n)),fresh_caller(p,plan),
        crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system(p,k,first,res,o),reg::register()),
        svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        forall|f:(vis::Cut,Seq<Event>,Seq<Event>)| #[trigger] vis::paired_installation(p,k,n,f) ==>
            weak_word(positions(k,o,svc::selected(f.0,f.1,alpha(n)))) && weak_word(positions(k,o,svc::selected(f.0,f.2,beta(n)))),
    ensures completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),pair.0.first.sends==pair.1.first.sends,svc::contents(k,pair.0.first.sends)==plan,
        evidence(p,k,pair.0.first.weak)==evidence(p,k,pair.1.first.weak),
        ({let x=wc::start(net::implementation(k,p));log(p,k,x,pair.0.first.weak.events)==log(p,k,x,pair.1.first.weak.events)}),
        (exists|f:(vis::Cut,Seq<Event>,Seq<Event>)| #[trigger] original_pair(p,k,n,f,pair.0.first.weak,pair.1.first.weak)),
        bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
{
    vis::selective_visibility_exact(p,k,n);
    let f=choose|f:(vis::Cut,Seq<Event>,Seq<Event>)| #[trigger] vis::paired_installation(p,k,n,f);
    let l=svc::selected(f.0,f.1,alpha(n));let r=svc::selected(f.0,f.2,beta(n));
    matching_from_installation(p,k,n,f);
    let pair=original_hot_from_matched_preparations(p,k,first,res,o,l,r,plan,run);
    assert(original_pair(p,k,n,f,pair.0.first.weak,pair.1.first.weak));pair
}

// Both alternatives start on the same complete machine, including any
// weak deliveries already accepted by the survivors. Only R3 takes the
// final receipt. Its actual callback and the rival occurrence are retained.
pub proof fn shared_cut_receipt<S>(p: Program<S>, k: Headers, c: vis::Cut, b: Fork) -> (e: Exposure)
    requires vis::shared_cut(p, k, b.notice, c),
    ensures e == svc::selected(c, seq![], b), svc::exposed(p,k,e), ({
        let m = net::implementation(k,p);
        let x = wc::start(m);
        let q = asm::drive(m, x, c.pre);
        let y = svc::endpoint(p,k,e);
        let h = svc::selected_handle(c,b);
        let a = Action::Deliver(h);
        let rival = if b.branch == crate::Branch::Alpha { c.two } else { c.five };
        let other = if b.branch == crate::Branch::Alpha { beta(b.notice) } else { alpha(b.notice) };
        svc::weak_trace(e) == c.pre + seq![a] && y == read::next(m, q, a)
            && net::trace(p, net::snapshot(k,x), net::turns(k,svc::weak_trace(e)), true)
            && net::end(p, net::snapshot(k,x), net::turns(k,svc::weak_trace(e))) == net::snapshot(k,y)
            && (exists|i: int| 0 <= i < c.pre.len() && #[trigger] c.pre[i] == Action::Send(h,vis::copy(b)))
            && y.cfg.net.pending == q.cfg.net.pending.remove(h)
            && net::queue(k,y.cfg.net) == net::queue(k,q.cfg.net).remove(h)
            && y.cfg.net.pending.get(rival) == Some(vis::copy(other))
            && (q.cfg.net.locals)(Replica::R3) != 2 && (q.cfg.net.locals)(Replica::R3) != 5
            && (y.cfg.net.locals)(Replica::R3) == first_value(b)
            && (y.cfg.private)(at(Replica::R3)) == (p.update)((q.cfg.private)(at(Replica::R3)),
                net::input(k,q.cfg.net,net::Command::Deliver(h)))
            && evidence(p,k,e) == af::view(k,q) && log(p,k,x,e.events)==log(p,k,x,c.pre)
    }),
{
    let m = net::implementation(k,p);
    let x = wc::start(m);
    let q = asm::drive(m, x, c.pre);
    let e = svc::selected(c, seq![], b);
    let h = svc::selected_handle(c,b);
    let a = Action::Deliver(h);
    assert(svc::weak_trace(e) =~= c.pre + seq![a]);
    assert(c.five != c.two);
    svc::from_ready_copy(p,k,b,c.pre,h);
    svc::weak_endpoint(p,k,e);
    asm::prefix_concat(m, x, c.pre, seq![a], true);
    assert(read::prefix_step(m)(q,a,read::next(m,q,a))) by { reveal_with_fuel(asm::prefix,2); }
    net::project_step(p,k,q,a,false);
    vis::weak_receipt(p,k,q,h);
    let y = svc::endpoint(p,k,e);
    assert(svc::ordinary(y) =~= svc::ordinary(q));
    view_from_queue(k,y,q);
    wc::prefix_packet_source(m,x,c.pre,h,vis::copy(b));
    net::project_prefix(p,k,x,svc::weak_trace(e),true,|_s:S|None);
    log_join(p,k,x,c.pre,seq![a]);
    assert(log(p,k,q,seq![a]) =~= Seq::<Observation>::empty()) by { reveal_with_fuel(log,2); }
    e
}

pub proof fn original_hot_from_shared_cut<S>(
    p: Program<S>, k: Headers, first: spec_fn(S)->int, res: spec_fn(S)->Option<int>,
    o: WeakOrder, n: Notice, c: vis::Cut, plan: svc::Requests, run: crate::fair_read::Runnable,
) -> (pair: (Execution<S>,Execution<S>))
    requires vis::shared_cut(p,k,n,c), fresh_caller(p,plan),
        crate::first_schedule::startup(net::implementation(k,p)),
        svc::invocation_laws(net::implementation(k,p), wc::start(net::implementation(k,p)), first,res,run),
        weak_word(positions(k,o,svc::selected(c,seq![],alpha(n)))),
        weak_word(positions(k,o,svc::selected(c,seq![],beta(n)))),
        op::operation_t(system(p,k,first,res,o),reg::register()),
    ensures pair.0.first.weak == svc::selected(c,seq![],alpha(n)), pair.1.first.weak == svc::selected(c,seq![],beta(n)),
        evidence(p,k,pair.0.first.weak) == evidence(p,k,pair.1.first.weak),
        ({let x=wc::start(net::implementation(k,p));log(p,k,x,pair.0.first.weak.events)==log(p,k,x,pair.1.first.weak.events)}),
        pair.0.first.sends == pair.1.first.sends, svc::contents(k,pair.0.first.sends) == plan,
        completed(p,k,first,res,pair.0), completed(p,k,first,res,pair.1), ({
            let m = net::implementation(k,p);
            let left = asm::drive(m, wc::start(m), lead(pair.0.first) + pair.0.second);
            let right = asm::drive(m, wc::start(m), lead(pair.1.first) + pair.1.second);
            left.cfg.net.pending.get(c.two) == Some(vis::copy(beta(n)))
                && right.cfg.net.pending.get(c.five) == Some(vis::copy(alpha(n)))
                && (bad(m,first,res,pair.0) || bad(m,first,res,pair.1))
        }),
{
    let l = shared_cut_receipt(p,k,c,alpha(n));
    let r = shared_cut_receipt(p,k,c,beta(n));
    let pair = original_hot_from_matched_preparations(p,k,first,res,o,l,r,plan,run);
    assert(fork::weak_packets(svc::endpoint(p,k,l)).get(c.two) == Some(vis::copy(beta(n))));
    assert(fork::weak_packets(svc::endpoint(p,k,r)).get(c.five) == Some(vis::copy(alpha(n))));
    let m = net::implementation(k,p);
    let left = asm::drive(m, wc::start(m), lead(pair.0.first) + pair.0.second);
    let right = asm::drive(m, wc::start(m), lead(pair.1.first) + pair.1.second);
    assert(fork::weak_packets(left).get(c.two) == Some(vis::copy(beta(n))));
    assert(fork::weak_packets(right).get(c.five) == Some(vis::copy(alpha(n))));
    pair
}

// A cut before SR1 can already expose the arm's value, or the scheduler
// can select a particular enabled receipt there. The occurrence belongs to
// this execution. Its actual sender, application ID and guard are retained.
pub open spec fn r3_value_available<S>(p: Program<S>, k: Headers, pre: Exposure, receipt: Option<nat>) -> bool {
    let m = net::implementation(k,p);
    let q = svc::endpoint(p,k,pre);
    let v = first_value(pre.arm);
    vis::replica_prefix(m,wc::start(m),pre.events) && survivor(q.cfg.net) == (2int,5int)
        && match receipt {
            None => (q.cfg.net.locals)(Replica::R3) == v,
            Some(h) => {
                let packet = q.cfg.net.pending[h];
                net::ready(p,k,q,net::Command::Deliver(h),false)
                    && packet.from is At && packet.to == at(Replica::R3)
                    && packet.path == Path::Weak && packet.input == Wire::Copy(v)
            },
        }
}

pub open spec fn after_r3_receipt(pre: Exposure, receipt: Option<nat>) -> Exposure {
    match receipt {
        None => pre,
        Some(h) => Exposure { arm: pre.arm, events: pre.events + seq![Action::Deliver(h)] },
    }
}

pub(crate) proof fn available_value_preserves_view<S>(p: Program<S>, k: Headers, pre: Exposure, receipt: Option<nat>)
    requires r3_value_available(p,k,pre,receipt),
    ensures svc::exposed(p,k,after_r3_receipt(pre,receipt)),
        evidence(p,k,after_r3_receipt(pre,receipt)) == evidence(p,k,pre),
{
    if let Some(h) = receipt {
        let m = net::implementation(k,p);
        let x = wc::start(m);
        let q = svc::endpoint(p,k,pre);
        let d = seq![Action::Deliver(h)];
        vis::weak_receipt(p,k,q,h);
        assert(vis::replica_prefix(m,q,d)) by {
            reveal_with_fuel(vis::replica_prefix,2);
            reveal_with_fuel(asm::prefix,2);
        }
        vis::join_replica_prefix(m,x,pre.events,d);
        asm::prefix_concat(m,x,pre.events,d,true);
        let y = svc::endpoint(p,k,after_r3_receipt(pre,receipt));
        assert(svc::ordinary(y) =~= svc::ordinary(q));
        view_from_queue(k,y,q);
    }
}

// Use only the legal-history consequence of all-execution H. If each weak
// possibility is reachable, the distinction must already be present at the
// survivors before the selected R3 receipts. Neither reachability claim
// is inferred from H or from fair delivery.
pub proof fn all_h_separates_r3_opportunities<S>(
    p: Program<S>, k: Headers, first: spec_fn(S)->int, res: spec_fn(S)->Option<int>, o: WeakOrder,
    l: Exposure, r: Exposure, five: Option<nat>, two: Option<nat>, plan: svc::Requests,
    run: crate::fair_read::Runnable,
)
    requires l.arm.branch == crate::Branch::Alpha, r.arm.branch == crate::Branch::Beta,
        r3_value_available(p,k,l,five), r3_value_available(p,k,r,two),
        fresh_caller(p,plan), crate::first_schedule::startup(net::implementation(k,p)),
        svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        weak_word(positions(k,o,after_r3_receipt(l,five))), weak_word(positions(k,o,after_r3_receipt(r,two))),
        op::operation_t(system(p,k,first,res,o),reg::register()),
        forall|h: Execution<S>| #[trigger] completed(p,k,first,res,h) ==> crate::coupled_reads::legal_returns(
            first((h.first.service.states.last().cfg.private)(Process::FirstClient)), result(net::implementation(k,p),res,h)),
    ensures ({
        let x = svc::endpoint(p,k,l);
        let y = svc::endpoint(p,k,r);
        (x.cfg.private)(at(Replica::R1)) != (y.cfg.private)(at(Replica::R1))
            || (x.cfg.private)(at(Replica::R2)) != (y.cfg.private)(at(Replica::R2))
            || exists|msg: net::Message| msg.body.path != Path::Weak && crate::protocol::survivor_actor(msg.body.to)
                && (#[trigger] af::occurrences(k,x.cfg.net,msg)).len() != af::occurrences(k,y.cfg.net,msg).len()
    }),
{
    available_value_preserves_view(p,k,l,five);
    available_value_preserves_view(p,k,r,two);
    let x = svc::endpoint(p,k,l);
    let y = svc::endpoint(p,k,r);
    assert(af::view(k,x) != af::view(k,y)) by {
        if af::view(k,x) == af::view(k,y) {
            let a = after_r3_receipt(l,five);
            let b = after_r3_receipt(r,two);
            let pair = original_hot_from_matched_preparations(p,k,first,res,o,a,b,plan,run);
            assert(completed(p,k,first,res,pair.0) && completed(p,k,first,res,pair.1));
        }
    }
    if (x.cfg.private)(at(Replica::R1)) == (y.cfg.private)(at(Replica::R1))
        && (x.cfg.private)(at(Replica::R2)) == (y.cfg.private)(at(Replica::R2)) {
        assert(!(af::view(k,x).copies =~= af::view(k,y).copies));
        let msg = choose|msg: net::Message| #[trigger] (af::view(k,x).copies)(msg) != (af::view(k,y).copies)(msg);
        af::visible_count(k,x,msg);
        af::visible_count(k,y,msg);
    }
}

}
