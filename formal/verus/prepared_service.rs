// Strong service at real weak-prefix endpoints. The sole-majority reference
// changes only availability. Its whole queue and all handler memories survive.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*};
use crate::async_messages::{self as net,Headers,Command,Message};
use crate::first_assembly::{self as asm,Service};
use crate::first_mailbox as mail;
use crate::hybrid_majority as maj;
use crate::independent_read::{self as read,State};
use crate::native_fork as fork;
use crate::original_application as app;
use crate::promotion_wait as wait;
use crate::read_call::{Program,Event};
use crate::read_nonblocking as nb;
use crate::fair_read as fair;
use crate::weak_construction as wc;
use crate::weak_visibility as vis;

verus! {

pub struct Exposure { pub arm:Fork, pub events:Seq<Event> }

pub open spec fn weak_trace(e:Exposure) -> Seq<Event> {
    e.events
}

pub open spec fn exposed<S>(p:Program<S>,k:Headers,e:Exposure) -> bool {
    let m=net::implementation(k,p);
    let z=endpoint(p,k,e);
    vis::replica_prefix(m,wc::start(m),weak_trace(e)) && survivor(z.cfg.net)==(2int,5int)
        && (z.cfg.net.locals)(Replica::R3)==first_value(e.arm)
}

pub open spec fn endpoint<S>(p:Program<S>,k:Headers,e:Exposure) -> State<S> {
    let m=net::implementation(k,p); asm::drive(m,wc::start(m),weak_trace(e))
}

pub open spec fn ordinary<S>(x:State<S>) -> Map<nat,Packet<Wire>> {
    let q=x.cfg.net.pending; q.restrict(q.dom().filter(|i:nat| q[i].path!=Path::Weak))
}

pub open spec fn replica_weak<S>(x:State<S>) -> bool {
    let w=fork::weak_packets(x);
    forall|h:nat| w.contains_key(h) ==> (#[trigger] w[h]).to is At
}

pub open spec fn idle<S>(m:Program<S>,x:State<S>) -> bool {
    x.calls.first==all_replicas() && x.calls.second==live_pair()
        && x.first_requested.is_empty() && x.requested.is_empty()
        && !x.cfg.net.first_stopped && !x.cfg.net.second_started && !x.cfg.net.r3_crashed && x.cfg.net.unavailable.is_none()
        && (x.cfg.private)(Process::FirstClient)==(m.initial)(Process::FirstClient)
        && (x.cfg.private)(Process::SecondClient)==(m.initial)(Process::SecondClient)
}

pub(crate) proof fn replica_frame<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    requires vis::replica_prefix(m,x,s),idle(m,x),replica_weak(x),
    ensures asm::prefix(m,x,s,true),idle(m,asm::drive(m,x,s)),replica_weak(asm::drive(m,x,s)),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0];
        let y=read::next(m,x,a);
        assert(vis::replica_input(process_step(x.cfg.net,a)));
        assert(process_step(x.cfg.net,a).actor is At);
        assert forall|h:nat| fork::weak_packets(y).contains_key(h) implies (#[trigger] fork::weak_packets(y)[h]).to is At by {
            if !(a is Send && a->Send_0==h) {assert(fork::weak_packets(x).get(h)==Some(fork::weak_packets(y)[h]));}
        }
        replica_frame(m,y,s.drop_first());
    }
}

// Strong service can also start after a guarded application of a buffered
// weak receipt. The older receipt-only exposure keeps its original meaning.
pub open spec fn service_entry<S>(p:Program<S>,k:Headers,e:Exposure) -> bool {
    exposed(p,k,e) || exists|c:crate::async_weak::Install<S>| #[trigger] crate::async_weak::installation(p,k,e,c)
}

pub proof fn weak_endpoint<S>(p:Program<S>,k:Headers,e:Exposure)
    requires service_entry(p,k,e),
    ensures ({
        let m=net::implementation(k,p); let x=wc::start(m); let z=endpoint(p,k,e);
        asm::prefix(m,x,weak_trace(e),true) && idle(m,z) && replica_weak(z)
            && survivor(z.cfg.net)==(2int,5int) && (z.cfg.net.locals)(Replica::R3)==first_value(e.arm)
    }),
{
    let m=net::implementation(k,p);
    if exposed(p,k,e) {
        replica_frame(m,wc::start(m),weak_trace(e));
    } else {
        let c=choose|c:crate::async_weak::Install<S>| #[trigger] crate::async_weak::installation(p,k,e,c);
        crate::async_weak::installation_frame(p,k,e,c);
    }
}

// The reference models one failure of the omitted replica after this
// weak prefix, before invocation. No pending occurrence is retracted.
pub open spec fn lost<S>(x:State<S>,r:Replica) -> State<S> {
    State {cfg:crate::ordinary_service::Configuration {net:crate::read_call::Net {
        unavailable:Some(r),..x.cfg.net},..x.cfg},..x}
}
pub open spec fn reference<S>(x:State<S>,b:Fork) -> State<S> { lost(x,crate::sr1_majorities::missing(b)) }

// The native alphabet has CrashR3. For references the environment can
// instead stop R1 or R2 once, at a reached cut. Only its availability bit
// changes. Native CrashR3 is disabled with this bit set.
pub type Route = (Seq<Event>,Option<Replica>,Seq<Event>);
pub open spec fn reaches<S>(m:Program<S>,base:State<S>,route:Route,x:State<S>) -> bool {
    let y=asm::drive(m,base,route.0);
    let z=if route.1.is_some() {lost(y,route.1.unwrap())} else {y};
    asm::prefix(m,base,route.0,true)
        && (route.1.is_some() ==> route.1.unwrap()!=Replica::R3 && y.cfg.net.unavailable.is_none() && !y.cfg.net.r3_crashed)
        && asm::prefix(m,z,route.2,true) && asm::drive(m,z,route.2)==x
}
pub open spec fn reachable<S>(m:Program<S>,base:State<S>,x:State<S>) -> bool {
    exists|t:Route| #[trigger] reaches(m,base,t,x)
}

pub type Requests = Seq<(Replica,nat)>;
pub open spec fn packet(r:Replica) -> Packet<Wire> {
    Packet {from:Process::FirstClient,to:at(r),path:Path::Strong,input:Wire::Request}
}
pub open spec fn request(a:Event) -> bool {
    a is Send && a->Send_1.to is At && a->Send_1==packet(a->Send_1.to->At_0)
}
pub open spec fn input(r:Replica,id:nat) -> crate::first_splice::Observation {
    process_step(local_rmw_cells(),Action::Send(id,packet(r)))
}
pub open spec fn supported<S>(p:Program<S>,z:S,plan:Requests) -> bool
    decreases plan.len(),
{
    if plan.len()==0 || (p.done)(z) {true} else {
        let e=input(plan[0].0,plan[0].1);
        (p.accept)(z,e) && supported(p,(p.update)(z,e),plan.drop_first())
    }
}
pub open spec fn recipients(t:Requests) -> Seq<Replica> { t.map_values(|v:(Replica,nat)|v.0) }

pub open spec fn fan<S>(m:Program<S>,x:State<S>,s:Seq<Event>) -> bool
    decreases s.len(),
{
    if s.len()==0 {true} else {
        let a=s[0]; let y=read::next(m,x,a);
        !mail::posted(m)(x) && request(a) && read::prefix_step(m)(x,a,y) && fan(m,y,s.drop_first())
    }
}

pub open spec fn contents(k:Headers,s:Seq<Event>) -> Requests {
    s.map_values(|a:Event| (a->Send_1.to->At_0,net::message(k,a->Send_0,a->Send_1).id))
}

// Select fresh queue handles on both real cuts. Equal application IDs can
// occur in different requests. Stop immediately if C1 publishes.
pub(crate) proof fn emit<S>(p:Program<S>,k:Headers,x:State<S>,y:State<S>,t:Requests) -> (s:Seq<Event>)
    requires x.calls.first==all_replicas(),y.calls.first==all_replicas(),
        !x.cfg.net.first_stopped,!y.cfg.net.first_stopped,x.first_requested==y.first_requested,
        (x.cfg.private)(Process::FirstClient)==(y.cfg.private)(Process::FirstClient),
        supported(p,(x.cfg.private)(Process::FirstClient),t),recipients(t).no_duplicates(),
        x.first_requested.disjoint(recipients(t).to_set()),
    ensures ({
        let m=net::implementation(k,p); let u=asm::drive(m,x,s); let v=asm::drive(m,y,s);
        fan(m,x,s) && fan(m,y,s) && (u.cfg.private)(Process::FirstClient)==(v.cfg.private)(Process::FirstClient)
            && u.first_requested==v.first_requested
            && s.len()<=t.len() && contents(k,s)==t.take(s.len() as int)
            && (!mail::posted(m)(u) ==> contents(k,s)==t && u.first_requested==x.first_requested.union(recipients(t).to_set()))
    }),
    decreases t.len(),
{
    let m=net::implementation(k,p); let c=Process::FirstClient;
    if t.len()==0 || mail::posted(m)(x) {
        if t.len()==0 { assert(recipients(t).to_set() =~= Set::empty()); }
        assert(contents(k,seq![]) =~= t.take(0));
        seq![]
    } else {
        let r=t[0].0; let msg=Message {id:t[0].1,body:packet(r)}; let cmd=Command::Send(msg);
        let tail=t.drop_first(); let rs=recipients(t); let rt=recipients(tail);
        assert(rs[0]==r && rs.contains(r)); assert(rt =~= rs.drop_first());
        assert(rs.to_set() =~= rt.to_set().insert(r)) by {assert(rs =~= seq![r]+rt);}
        assert(!rt.contains(r));
        let avoid=y.cfg.net.pending.dom().union(y.reserved).union(y.owners.dom());
        assert(net::ready(p,k,x,cmd,false) && net::ready(p,k,y,cmd,false));
        let a=net::realize_step(p,k,x,cmd,false,avoid);
        assert(net::allocatable(y,a)); net::project_step(p,k,y,a,false);
        let u=read::next(m,x,a); let v=read::next(m,y,a);
        assert(u.first_requested.disjoint(rt.to_set()));
        let rest=emit(p,k,u,v,tail); let s=seq![a]+rest; assert(s.drop_first() =~= rest);
        assert(contents(k,s) =~= seq![t[0]]+contents(k,rest)) by {
            assert forall|i:int| 0<=i<s.len() implies #[trigger] contents(k,s)[i]==(seq![t[0]]+contents(k,rest))[i] by {
                if i>0 {assert(s[i]==rest[i-1]);}
            }
        }
        assert(seq![t[0]]+tail.take(rest.len() as int) =~= t.take(s.len() as int));
        assert(u.first_requested.union(rt.to_set()) =~= x.first_requested.union(rs.to_set()));
        s
    }
}

pub open spec fn path<S>(m:Program<S>,x:State<S>,s:Seq<Event>) -> Service<S> {
    wait::Path { states:fork::states(m,x,s), actions:s }
}

pub proof fn index_step<S>(m:Program<S>,x:State<S>,s:Seq<Event>,i:int)
    requires 0<=i<s.len(),
    ensures fork::states(m,x,s)[i+1]==read::next(m,fork::states(m,x,s)[i],s[i]),
{
    let head=s.take(i);let a=seq![s[i]];assert(head+a =~= s.take(i+1));asm::prefix_concat(m,x,head,a,true);
    reveal_with_fuel(asm::drive,2);
}

pub proof fn endpoints<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    ensures path(m,x,s).states[0]==x, path(m,x,s).states.last()==asm::drive(m,x,s),
{
    assert(s.take(0) =~= seq![] && s.take(s.len() as int) =~= s);
}

pub(crate) proof fn fan_at<S>(m:Program<S>,x:State<S>,s:Seq<Event>,i:nat)
    requires fan(m,x,s),i<=s.len(),
    ensures ({
        let q=fork::states(m,x,s)[i as int];
        q.cfg.net==crate::read_call::Net{pending:q.cfg.net.pending,..x.cfg.net}
            && q.calls==x.calls && q.requested==x.requested
            && (forall|c:Process| c!=Process::FirstClient ==> (#[trigger] (q.cfg.private)(c))==(x.cfg.private)(c))
            && fork::weak_packets(q)==fork::weak_packets(x)
            && (i<s.len() ==> !mail::posted(m)(q) && request(s[i as int])
                && read::prefix_step(m)(q,s[i as int],fork::states(m,x,s)[i as int+1]))
    }),
    decreases i,
{
    if i==0 {endpoints(m,x,s); if s.len()>0 {index_step(m,x,s,0);}}
    else {
        let y=read::next(m,x,s[0]); let tail=s.drop_first(); let j=(i-1) as nat;
        assert(request(s[0])); assert(y.cfg.net.locals =~= x.cfg.net.locals);
        assert(fork::weak_packets(y) =~= fork::weak_packets(x));
        assert(s.take(i as int) =~= seq![s[0]]+tail.take(j as int));
        asm::prefix_concat(m,x,seq![s[0]],tail.take(j as int),true);
        assert(asm::drive(m,x,seq![s[0]])==y) by {reveal_with_fuel(asm::drive,2);}
        if i<s.len() {index_step(m,x,s,i as int);index_step(m,y,tail,j as int);assert(tail[j as int]==s[i as int]);}
        fan_at(m,y,tail,j);
    }
}
pub(crate) proof fn fan_path<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    requires fan(m,x,s),
    ensures wait::valid_edges(read::prefix_step(m),path(m,x,s)),wait::pending_before(mail::posted(m),path(m,x,s)),
{
    let h=path(m,x,s);
    assert forall|i:int| 0<=i<s.len() implies read::prefix_step(m)(h.states[i],#[trigger] h.actions[i],h.states[i+1])
        by {fan_at(m,x,s,i as nat);}
    assert forall|i:int| 0<=i<s.len() implies !mail::posted(m)(#[trigger] h.states[i]) by {fan_at(m,x,s,i as nat);}
}

proof fn early_value<S>(m:Program<S>,first:spec_fn(S)->int,x:State<S>,b:Fork,s:Seq<Event>)
    requires fan(m,x,s), x.first_requested.is_empty(), !mail::posted(m)(x),mail::posted(m)(asm::drive(m,x,s)),
        maj::sole(x.cfg.net,crate::first_quorum(b.branch)),!x.cfg.net.first_stopped,
        forall|r:Replica| crate::first_quorum(b.branch).contains(r) ==> (#[trigger] (x.cfg.net.locals)(r))==first_value(b),
        maj::first_invocation_sampling(m,first,x),
    ensures first((asm::drive(m,x,s).cfg.private)(Process::FirstClient))==first_value(b),
{
    let h=path(m,x,s); let q=crate::first_quorum(b.branch); endpoints(m,x,s);
    assert(s.len()>0);fan_at(m,x,s,0);fan_at(m,x,s,s.len());
    assert forall|i:int| 0<=i<s.len() implies read::prefix_step(m)(h.states[i],#[trigger] s[i],h.states[i+1])
        && !mail::posted(m)(h.states[i]) by {fan_at(m,x,s,i as nat);}
    fan_path(m,x,s);assert(maj::fresh_invocation(maj::Caller::First,x,s[0]));
    assert(wait::first_return(read::prefix_step(m),mail::posted(m),x,h));
    assert forall|r:Replica| #[trigger] q.contains(r)==live(h.states.last().cfg.net,at(r)) by {
        assert(q.contains(r)==live(x.cfg.net,at(r)));
    }
    assert(maj::first_invocation_interval(m,h,q)); assert(nb::within(read::prefix_step(m),read::at_state(x),x,0));
    let v=first((h.states.last().cfg.private)(Process::FirstClient));
    let (j,r)=choose|j:int,r:Replica| 0<=j<h.states.len() && q.contains(r) && #[trigger] (h.states[j].cfg.net.locals)(r)==v;
    fan_at(m,x,s,j as nat);
}

pub open spec fn service_laws<S>(m:Program<S>,first:spec_fn(S)->int,x:State<S>,run:fair::Runnable) -> bool {
    maj::first_invocation_sampling(m,first,x) && (forall|s:Seq<Event>| #[trigger] fan(m,x,s)
        && mail::submitted(asm::drive(m,x,s)) && !mail::posted(m)(asm::drive(m,x,s)) ==> {
            let y=asm::drive(m,x,s);
            mail::first_availability(m,run,read::at_state(y)) && mail::fair_opportunity(m,run,y)
                && !wait::needs_class(mail::active_step(m),mail::posted(m),y,app::weak_replica_step())
        })
}

// Positive service and held-value sampling are hybrid A. Fair executions
// are the scheduler premise. The two needs_class tests are no-await on
// the actual weak work. None of these clauses selects a read result.
pub open spec fn invocation_laws<S>(m:Program<S>,base:State<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    run:fair::Runnable) -> bool {
    forall|x:State<S>| #[trigger] reachable(m,base,x) ==> (
        (x.first_requested.is_empty() && !x.cfg.net.first_stopped && !x.cfg.net.second_started
            ==> maj::first_invocation_sampling(m,first,x))
        && (mail::submitted(x) && !mail::posted(m)(x) && !x.cfg.net.second_started ==>
            mail::first_availability(m,run,read::at_state(x)) && mail::fair_opportunity(m,run,x)
                && !wait::needs_class(mail::active_step(m),mail::posted(m),x,app::weak_replica_step()))
        && (crate::survivors::after_crash(x.cfg.net) && fork::available(x) && x.requested.is_empty()
            ==> fork::opportunity(m,res,x,run)))
}
pub(crate) proof fn fan_prefix<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    requires fan(m,x,s),
    ensures asm::prefix(m,x,s,true),
    decreases s.len(),
{
    if s.len()>0 {fan_prefix(m,read::next(m,x,s[0]),s.drop_first());}
}

pub proof fn reference_laws<S>(p:Program<S>,k:Headers,e:Exposure,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,run:fair::Runnable)
    requires service_entry(p,k,e),invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
    ensures ({
        let m=net::implementation(k,p);let x=reference(endpoint(p,k,e),e.arm);
        reachable(m,wc::start(m),x) && service_laws(m,first,x,run)
    }),
{
    let m=net::implementation(k,p);let base=wc::start(m);let z=endpoint(p,k,e);let r=crate::sr1_majorities::missing(e.arm);
    let x=reference(z,e.arm);weak_endpoint(p,k,e);
    assert(reaches(m,base,(weak_trace(e),Some(r),seq![]),x));
    assert(reachable(m,base,x));assert(maj::first_invocation_sampling(m,first,x));
    assert forall|s:Seq<Event>| #[trigger] fan(m,x,s) && mail::submitted(asm::drive(m,x,s)) && !mail::posted(m)(asm::drive(m,x,s))
        implies {
            let y=asm::drive(m,x,s);
            mail::first_availability(m,run,read::at_state(y)) && mail::fair_opportunity(m,run,y)
                && !wait::needs_class(mail::active_step(m),mail::posted(m),y,app::weak_replica_step())
        } by {
            let y=asm::drive(m,x,s);fan_prefix(m,x,s);fan_at(m,x,s,s.len());endpoints(m,x,s);
            assert(reaches(m,base,(weak_trace(e),Some(r),s),y));assert(reachable(m,base,y));
        }
}
proof fn ref_cells<S>(p:Program<S>,k:Headers,e:Exposure)
    requires service_entry(p,k,e),
    ensures ({
        let m=net::implementation(k,p); let x=reference(endpoint(p,k,e),e.arm); let q=crate::first_quorum(e.arm.branch);
        app::all_available(x)==endpoint(p,k,e) && maj::sole(x.cfg.net,q) && q.len()==2
            && (forall|r:Replica| q.contains(r) ==> (#[trigger] (x.cfg.net.locals)(r))==first_value(e.arm))
    }),
{
    weak_endpoint(p,k,e); let q=crate::first_quorum(e.arm.branch);
    assert(q =~= set![crate::origin(e.arm.branch),Replica::R3]);assert(crate::origin(e.arm.branch)!=Replica::R3);
    assert(set![crate::origin(e.arm.branch),Replica::R3].len()==2);
}

// The two sole-quorum value sets are disjoint. Since C1 sees only its
// own identical proposals, it cannot publish during this common fanout.
pub proof fn paired_fanout<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,l:Exposure,r:Exposure,t:Requests)
    -> (s:Seq<Event>)
    requires service_entry(p,k,l),service_entry(p,k,r),l.arm.branch!=r.arm.branch,
        recipients(t).no_duplicates(),recipients(t).to_set()==all_replicas(),supported(p,(p.initial)(Process::FirstClient),t),
        !(p.done)((p.initial)(Process::FirstClient)),
        maj::first_invocation_sampling(net::implementation(k,p),first,reference(endpoint(p,k,l),l.arm)),
        maj::first_invocation_sampling(net::implementation(k,p),first,reference(endpoint(p,k,r),r.arm)),
    ensures ({
        let m=net::implementation(k,p); let x=reference(endpoint(p,k,l),l.arm);let y=reference(endpoint(p,k,r),r.arm);
        fan(m,x,s) && fan(m,y,s) && contents(k,s)==t && !mail::posted(m)(asm::drive(m,x,s)) && !mail::posted(m)(asm::drive(m,y,s))
            && asm::drive(m,x,s).first_requested==all_replicas() && asm::drive(m,y,s).first_requested==all_replicas()
    }),
{
    weak_endpoint(p,k,l);weak_endpoint(p,k,r);ref_cells(p,k,l);ref_cells(p,k,r);
    let m=net::implementation(k,p);let x=reference(endpoint(p,k,l),l.arm);let y=reference(endpoint(p,k,r),r.arm);
    let s=emit(p,k,x,y,t);
    if mail::posted(m)(asm::drive(m,x,s)) {early_value(m,first,x,l.arm,s);early_value(m,first,y,r.arm,s);}
    s
}

pub proof fn lift_fan<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    requires fan(m,x,s),
    ensures fan(m,app::all_available(x),s),asm::prefix(m,app::all_available(x),s,true),
        asm::drive(m,app::all_available(x),s)==app::all_available(asm::drive(m,x,s)),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0];let u=app::all_available(x);let v=read::next(m,u,a);let y=read::next(m,x,a);
        assert(request(a));assert(v.cfg.private =~= y.cfg.private);assert(v.cfg.net.locals =~= y.cfg.net.locals);
        assert(v==app::all_available(y));lift_fan(m,y,s.drop_first());
    }
}

pub open spec fn first_path<S>(m:Program<S>,first:spec_fn(S)->int,e:Exposure,root:State<S>,u:Service<S>) -> bool {
    wait::first_return(mail::active_step(m),mail::posted(m),root,u) && !wait::uses(u,app::weak_replica_step())
        && first((u.states.last().cfg.private)(Process::FirstClient))==first_value(e.arm)
        && forall|i:int| 0<=i<u.actions.len() ==> process_step(u.states[i].cfg.net,#[trigger] u.actions[i]).actor
            != at(crate::sr1_majorities::missing(e.arm))
}

pub proof fn first_service<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    e:Exposure,s:Seq<Event>,run:fair::Runnable) -> (u:Service<S>)
    requires service_entry(p,k,e), ({
        let m=net::implementation(k,p);let x=reference(endpoint(p,k,e),e.arm);let y=asm::drive(m,x,s);
        fan(m,x,s) && y.first_requested==all_replicas() && !mail::posted(m)(y) && service_laws(m,first,x,run)
    }),
    ensures ({
        let m=net::implementation(k,p);let z=endpoint(p,k,e);let root=asm::drive(m,z,s);
        fan(m,z,s) && asm::prefix(m,z,s,true) && first_path(m,first,e,root,u)
    }),
{
    let m=net::implementation(k,p);let b=e.arm;let x=reference(endpoint(p,k,e),b);let y=asm::drive(m,x,s);
    let q=crate::first_quorum(b.branch);let h=path(m,x,s);
    weak_endpoint(p,k,e);ref_cells(p,k,e);lift_fan(m,x,s);endpoints(m,x,s);fan_at(m,x,s,0);fan_at(m,x,s,s.len());
    assert(q.contains(crate::origin(b.branch)) && q.contains(Replica::R3));
    assert(live(y.cfg.net,at(crate::origin(b.branch))) && live(y.cfg.net,at(Replica::R3)));
    assert(y.first_requested.contains(crate::origin(b.branch)) && y.first_requested.contains(Replica::R3));
    assert(mail::submitted(y));
    mail::fair_first_service(m,run,read::at_state(y),y);nb::first_response_iff(mail::active_step(m),mail::posted(m),y);
    let t=choose|t:Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),y,t) && !wait::uses(t,app::weak_replica_step());
    assert forall|i:int| 0<=i<s.len() implies read::prefix_step(m)(h.states[i],#[trigger] s[i],h.states[i+1]) && !mail::posted(m)(h.states[i])
        by {fan_at(m,x,s,i as nat);}
    assert(s.len()>0);
    let u=wait::Path {states:t.states.map_values(|z|app::all_available(z)),actions:t.actions};
    assert forall|i:int| 0<=i<t.actions.len() implies {
        let a=#[trigger] t.actions[i];let z=t.states[i];let v=t.states[i+1];
        mail::active_step(m)(u.states[i],a,u.states[i+1]) && !mail::posted(m)(u.states[i])
            && !app::weak_replica_step()(u.states[i],a,u.states[i+1])
            && process_step(u.states[i].cfg.net,a).actor!=at(crate::sr1_majorities::missing(b))
    } by {
        assert(mail::active_step(m)(t.states[i],t.actions[i],t.states[i+1]) && !mail::posted(m)(t.states[i]));
        service_frame(m,t,i as nat);app::original_step(m,t.states[i],t.actions[i],t.states[i+1]);
        assert(live(t.states[i].cfg.net,process_step(t.states[i].cfg.net,t.actions[i]).actor));
    }
    service_frame(m,t,t.actions.len());
    fan_path(m,x,s);assert(maj::fresh_invocation(maj::Caller::First,x,s[0]));
    assert forall|r:Replica| #[trigger] q.contains(r)==live(t.states.last().cfg.net,at(r)) by {
        assert(q.contains(r)==live(x.cfg.net,at(r)));
    }
    assert(maj::served(maj::Caller::First,m,res,h,t,q));assert(nb::within(read::prefix_step(m),read::at_state(x),x,0));
    maj::invocation_includes_submitted_sampling(m,first,res,x);
    let v=first((t.states.last().cfg.private)(Process::FirstClient));
    if maj::held(h.states,q,v) {
        let (i,r)=choose|i:int,r:Replica| 0<=i<h.states.len() && q.contains(r) && #[trigger] (h.states[i].cfg.net.locals)(r)==v;
        fan_at(m,x,s,i as nat);
    } else {
        assert(maj::held(t.states,q,v));
        let (i,r)=choose|i:int,r:Replica| 0<=i<t.states.len() && q.contains(r) && #[trigger] (t.states[i].cfg.net.locals)(r)==v;
        app::cells_at(m,t,i as nat);
    }
    u
}

pub proof fn service_frame<S>(m:Program<S>,t:Service<S>,i:nat)
    requires t.states.len()>0,wait::first_return(mail::active_step(m),mail::posted(m),t.states[0],t),
        !wait::uses(t,app::weak_replica_step()),i<t.states.len(), !t.states[0].cfg.net.second_started,
        // All initially postponed weak traffic in the original prefix is replica-to-replica.
        replica_weak(t.states[0]),
    ensures ({
        let x=t.states[0];let y=t.states[i as int];
        y.cfg.net.locals==x.cfg.net.locals && y.cfg.net.unavailable==x.cfg.net.unavailable
            && y.cfg.net.r3_crashed==x.cfg.net.r3_crashed && y.cfg.net.first_stopped==x.cfg.net.first_stopped
            && y.cfg.net.second_started==x.cfg.net.second_started && y.calls==x.calls && y.requested==x.requested
            && y.first_requested==x.first_requested && crate::fork_information::caller2(y)==crate::fork_information::caller2(x)
            && fork::weak_packets(y)==fork::weak_packets(x)
    }),
    decreases i,
{
    if i>0 {
        let j=i as int-1;service_frame(m,t,(i-1) as nat);let x=t.states[j];let a=t.actions[j];let y=t.states[i as int];
        assert(mail::active_step(m)(x,a,y) && !mail::posted(m)(x) && !app::weak_replica_step()(x,a,y));
        app::quiet_cells(m,x,a,y);
        if let Action::Deliver(h)=a {
            if x.cfg.net.pending[h].path==Path::Weak {
                assert(fork::weak_packets(x).get(h)==Some(x.cfg.net.pending[h]));
                assert(fork::weak_packets(t.states[0])[h].to is At);
                assert(app::weak_replica_step()(x,a,y));
            }
        }
        if a is Send {assert(a->Send_1.from is At && a->Send_1.path!=Path::Weak);}
        assert(fork::weak_packets(y) =~= fork::weak_packets(x));
    }
}

}
