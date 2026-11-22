// Additional schedules testing the same sender-sensitive reader across legal
// weak invocation sites. In the paper forks both origins stay at R1/R2.
use vstd::prelude::*;
use crate::{Op,Replica,RecoveredOrder,origin};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Packet,Path as Route,Process};
use crate::facade_hybrid::{inner,invocation,weak_part};
use crate::fallback_program::{self as program,apply_event};
use crate::first_copy_wait::{Cut,offered};
use crate::live_quorum::{self as rpc,root_reports};
use crate::metadata_stock::Rows;
use crate::ordered_round::engine;
use crate::ordered_store::{majority,Stamp};
use crate::quorum_rpc::Resolver;
use crate::sender_forks::opposite;
use crate::stock_facade::*;
use crate::weak_round::{self as weak,paper_ops};

verus! {

pub open spec fn anchor(b:Fork) -> Replica { origin(opposite(b).branch) }
pub open spec fn local(b:Fork) -> weak::Request {
    weak::Request{site:Replica::R3,..weak::request(observed_writer(b))}
}
pub open spec fn rival(b:Fork) -> weak::Request { weak::request(observed_writer(opposite(b))) }
pub open spec fn calls(b:Fork) -> Seq<weak::Action> {
    use crate::weak_round::Action::*;
    seq![Send(0,local(b)),Send(1,rival(b)),Handle(0),Receive(0),Handle(1),Receive(1)]
}
pub open spec fn ports(b:Fork,k:nat) -> weak::World
    decreases k,
{
    if k==0 {weak::start()} else {weak::step(paper_ops(),ports(b,(k-1) as nat),calls(b)[k-1])}
}
pub open spec fn before(b:Fork,split:bool) -> weak::World { ports(b,if split {6} else {4}) }
pub open spec fn stamp(v:int) -> Stamp {Stamp{version:0,value:v}}
pub open spec fn working(b:Fork,split:bool,r:Replica) -> int {
    if r==Replica::R3 {first_value(b)} else if split && r==anchor(b) {first_value(opposite(b))} else {1}
}
pub open spec fn holders(w:weak::World,id:weak::Id) -> Set<Replica> {
    all_replicas().filter(|r:Replica|(w.journal)(r).contains_key(id))
}
pub open spec fn local_prefix(b:Fork,split:bool) -> bool {
    let w=before(b,split);let q=local(b);let t=rival(b);let n=if split {6nat} else {4};
    (forall|k:nat| k<n ==> weak::enabled(ports(b,k),#[trigger] calls(b)[k as int]))
        && ports(b,2).wire==map![0nat=>weak::Packet::Request(q),1nat=>weak::Packet::Request(t)]
        && q.id!=t.id && q.site!=t.site && q.method==weak::request(observed_writer(b)).method
        && w.answers.get(q.id)==Some(1) && (w.journal)(q.site)[q.id]==weak::evaluate(paper_ops(),q,1)
        && holders(w,q.id)==set![q.site] && holders(w,t.id)==(if split {set![t.site]} else {Set::empty()})
        && (if split {w.wire.is_empty() && w.answers.get(t.id)==Some(1)}
            else {w.wire==map![1nat=>weak::Packet::Request(t)] && !w.answers.contains_key(t.id)})
        && w.front.base.live==all_replicas() && w.front.base.stopped.is_empty() && w.front.calls.is_empty() && w.front.closed.is_empty()
        && forall|r:Replica| (#[trigger] (w.front.base.disk)(r))==stamp(working(b,split,r))
}
proof fn weak_prefix(b:Fork,split:bool)
    ensures local_prefix(b,split),
{
    reveal_with_fuel(ports,7);
    assert forall|k:nat| k<(if split {6nat} else {4}) implies weak::enabled(ports(b,k),#[trigger] calls(b)[k as int])
        by {assert(k==0 || k==1 || k==2 || k==3 || k==4 || k==5);}
    let w=before(b,split);let q=local(b);let t=rival(b);
    assert(holders(w,q.id) =~= set![q.site]);
    assert(holders(w,t.id) =~= (if split {set![t.site]} else {Set::empty()}));
    assert(ports(b,2).wire =~= map![0nat=>weak::Packet::Request(q),1nat=>weak::Packet::Request(t)]);
    if split {assert(w.wire =~= Map::<nat,weak::Packet>::empty());}
    else {assert(w.wire =~= map![1nat=>weak::Packet::Request(t)]);}
}

// The weak client RPC inbox and the background replication network are
// distinct. R3 issues a real background copy while live. It stays in slot 0.
pub open spec fn empty_bus(b:Fork,split:bool) -> Cut {
    let w=before(b,split);
    Cut{core:w.front,net:Network{locals:|r|(w.front.base.disk)(r).value,pending:Map::empty(),
        first_stopped:false,second_started:false,r3_crashed:false,unavailable:None}}
}
pub open spec fn copy(b:Fork) -> Packet<Wire> {
    Packet{path:Route::Weak,from:at(Replica::R3),to:at(origin(b.branch)),input:Wire::Copy(first_value(b))}
}
pub open spec fn rowmap(b:Fork,split:bool) -> Rows {
    Map::empty().insert(anchor(b),stamp(working(b,split,anchor(b)))).insert(Replica::R3,stamp(first_value(b)))
}
pub open spec fn index(r:Replica) -> nat {match r {Replica::R1=>0,Replica::R2=>1,Replica::R3=>2}}
pub open spec fn body(b:Fork,split:bool,id:nat) -> Packet<Wire> {
    let r=if id==3 || id==6 {Replica::R1} else if id==4 || id==7 {Replica::R2} else {Replica::R3};
    if id<=5 {Packet{path:Route::Strong,from:Process::FirstClient,to:at(r),input:Wire::Request}}
    else {Packet{path:Route::FirstReadReply,from:at(r),to:Process::FirstClient,input:Wire::Reply(working(b,split,r))}}
}
pub open spec fn sr1(b:Fork,split:bool) -> Seq<rpc::Ev> {
    seq![Action::Send(3,body(b,split,3)),Action::Send(4,body(b,split,4)),Action::Send(5,body(b,split,5)),
        Action::Deliver(3),Action::Deliver(4),Action::Deliver(5),
        Action::Send(6,body(b,split,6)),Action::Send(7,body(b,split,7)),Action::Send(8,body(b,split,8)),
        Action::Deliver(6+index(anchor(b))),Action::Deliver(8),Action::Strong(Process::FirstClient)]
}
pub open spec fn leg(b:Fork,split:bool,r:Replica,k:nat) -> Leg {
    let i=index(r);let row=stamp(working(b,split,r));
    if k<=i {Leg::Unsent} else if k<=3+i {Leg::Request} else if k<=6+i {Leg::AtServer}
    else if (r==anchor(b) && k>=10) || (r==Replica::R3 && k>=11) {Leg::Received(row)}
    else {Leg::InFlight(row)}
}
pub open spec fn sample(b:Fork,split:bool,rho:Resolver,k:nat) -> Cut {
    let x=empty_bus(b,split);
    let p=Map::new(set![3nat,4,5,6,7,8].filter(|i:nat| (3<=i<=5 && i<=k+2 && k<i+1) ||
        (6<=i<=8 && i<k && !(i==6+index(anchor(b)) && k>=10) && !(i==8 && k>=11))),|i|body(b,split,i));
    let c=Call{legs:|r|leg(b,split,r,k),answer:if k==12 {rho(rowmap(b,split))} else {None},..fresh(Method::Read)};
    Cut{net:Network{pending:p.insert(0,copy(b)),..x.net},
        core:State{calls:if k==0 {Map::empty()} else {Map::empty().insert(1nat,c)},..x.core}}
}
pub open spec fn take(rho:Resolver,s:Cut,a:rpc::Ev) -> Cut {
    let p=engine(paper_ops());let mid=apply_event(rho,p,s.core,invocation(s.core,s.net,a));
    Cut{net:delivery::advance(|x,w|cell(x,w),s.net,a),core:weak_part(apply_event(rho,p,mid,inner(s.net,a)),s.net,a)}
}
pub open spec fn only_initial_requests(n:rpc::Net,a:rpc::Ev) -> bool {
    match a {
        Action::Send(_,p) if delivery::outside_replica(p.from)=>p.from==Process::FirstClient && p.input==Wire::Request,
        Action::Deliver(i) if n.pending[i].to is At=>n.pending.contains_key(i) && n.pending[i].input==Wire::Request,
        _=>true,
    }
}
// Autonomous strong/service events leave the separately addressed weak RPC
// inbox, replies and origin journals intact while advancing the shared front.
pub open spec fn carried(w:weak::World,s:Cut) -> weak::World { weak::World{front:s.core,..w} }
pub open spec fn weak_ports_quiet(w:weak::World,s:Cut,u:Cut) -> bool {
    let x=carried(w,s);let y=carried(w,u);
    weak::ports_step(paper_ops(),x,None,y) && x.wire==y.wire && x.answers==y.answers && x.journal==y.journal
}
pub open spec fn first_trace(b:Fork,split:bool,rho:Resolver) -> bool {
    let f=paper_ops();let x=empty_bus(b,split);let offer=Action::Send(0,copy(b));
    local_prefix(b,split) && offered(x,offer) && program::joint(f,rho,x,offer,sample(b,split,rho,0))
        && weak_ports_quiet(before(b,split),x,sample(b,split,rho,0))
        && (forall|k:nat| k<12 ==> {let ev=#[trigger] sr1(b,split)[k as int];let s=sample(b,split,rho,k);
            let u=sample(b,split,rho,k+1);program::joint(f,rho,s,ev,u) && only_initial_requests(s.net,ev)
            && weak_ports_quiet(before(b,split),s,u) && u.core.base==x.core.base && u.net.pending.get(0)==Some(copy(b))})
        && sample(b,split,rho,12).core.calls[1].answer==rho(rowmap(b,split))
        && rows(sample(b,split,rho,12).core.calls[1])==rowmap(b,split)
}
proof fn issued(b:Fork,split:bool,rho:Resolver)
    requires local_prefix(b,split),
    ensures ({let s=empty_bus(b,split);let a=Action::Send(0,copy(b));
        offered(s,a) && program::joint(paper_ops(),rho,s,a,sample(b,split,rho,0))}),
{
    hide(ports);let s=empty_bus(b,split);let a=Action::Send(0,copy(b));let u=sample(b,split,rho,0);let v=take(rho,s,a);
    assert(v.net.pending =~= u.net.pending);assert(v.net.locals =~= u.net.locals);
    assert(v.core.closed =~= u.core.closed);assert(v.core.calls =~= u.core.calls);
    assert(v==u);assert(offered(s,a));
}
#[verifier::rlimit(14)]
proof fn first_step(b:Fork,split:bool,rho:Resolver,k:nat)
    requires local_prefix(b,split),k<12,
    ensures ({let ev=sr1(b,split)[k as int];let s=sample(b,split,rho,k);let u=sample(b,split,rho,k+1);
        program::joint(paper_ops(),rho,s,ev,u) && only_initial_requests(s.net,ev)
        && u.core.base==before(b,split).front.base && u.net.pending.get(0)==Some(copy(b))}),
{
    hide(ports);let f=paper_ops();let s=sample(b,split,rho,k);let u=sample(b,split,rho,k+1);let ev=sr1(b,split)[k as int];
    let v=take(rho,s,ev);let p=engine(f);
    let start=invocation(s.core,s.net,ev);let mid=apply_event(rho,p,s.core,start);let action=inner(s.net,ev);
    let c=if k==0 {fresh(Method::Read)} else {s.core.calls[1]};
    prefix_index(k as int);
    if k==11 {assert(rows(s.core.calls[1]) =~= rowmap(b,split));}
    assert(delivery::enabled(s.net,ev));assert(enabled(p,s.core,start));assert(enabled(p,mid,action));
    assert(crate::facade_transport::valid(s.net,crate::facade_transport::service(s.net,ev,Process::FirstClient),c,Process::FirstClient));
    assert(v.net.pending =~= u.net.pending);assert(v.net.locals =~= u.net.locals);
    assert(v.core.closed =~= u.core.closed);assert(v.core.calls[1].legs =~= u.core.calls[1].legs);
    assert(v.core.calls =~= u.core.calls);assert(v==u);
}
pub proof fn addressed_first(b:Fork,split:bool,rho:Resolver)
    ensures first_trace(b,split,rho),
{
    hide(ports);hide(program::joint);weak_prefix(b,split);issued(b,split,rho);
    assert forall|k:nat| k<12 implies {let ev=#[trigger] sr1(b,split)[k as int];let s=sample(b,split,rho,k);
        let u=sample(b,split,rho,k+1);program::joint(paper_ops(),rho,s,ev,u) && only_initial_requests(s.net,ev)
        && u.core.base==empty_bus(b,split).core.base && u.net.pending.get(0)==Some(copy(b))} by {first_step(b,split,rho,k);}
    assert(rows(sample(b,split,rho,12).core.calls[1]) =~= rowmap(b,split));
}

// A legal sequential order and the manuscript's additional majority-by-
// response requirement. Majority is on the producing invocation identity.
pub open spec fn durable_read(w:weak::World,h:RecoveredOrder,v:int) -> bool {
    crate::irrevocable_order::single_read(h,v)
        && forall|j:int,i:int| 0<=j<i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 &&
            (#[trigger] h.ops[j]==Op::W1 || h.ops[j]==Op::W2) ==>
            majority(holders(w,weak::request(h.ops[j]).id))
}
proof fn no_noninitial_durable(b:Fork,split:bool,h:RecoveredOrder,v:int)
    requires v!=1,
    ensures !durable_read(before(b,split),h,v),
{
    weak_prefix(b,split);
    if durable_read(before(b,split),h,v) {
        let i=choose|i:int| 0<=i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 && h.states[i]==v;
        crate::irrevocable_order::writer_before(h,i as nat);
        let j=choose|j:int| 0<=j<i && (#[trigger] h.ops[j]==Op::W1 && h.states[i]==2 || h.ops[j]==Op::W2 && h.states[i]==5);
        assert(majority(holders(before(b,split),weak::request(h.ops[j]).id)));
    }
}
pub open spec fn held(b:Fork,split:bool,rho:Resolver,v:int) -> bool {
    exists|r:Replica,k:nat| (r==anchor(b) || r==Replica::R3) && k<=12 &&
        (#[trigger] (sample(b,split,rho,k).core.base.disk)(r)).value==v
}
// In the isolated split cut both distinct commands have already replied 1.
// Any completion either violates held-value validity or lacks a majority
// copy of the invocation required by a legal single-read history.
pub proof fn split_return(b:Fork,rho:Resolver)
    ensures first_trace(b,true,rho),match sample(b,true,rho,12).core.calls[1].answer {
        Some(v)=> !held(b,true,rho,v) || (forall|h:RecoveredOrder| !#[trigger] durable_read(before(b,true),h,v)),
        None=>true,
    },
{
    addressed_first(b,true,rho);
    if let Some(v)=rho(rowmap(b,true)) {
        if v==1 {assert(!held(b,true,rho,v));}
        else {assert forall|h:RecoveredOrder| !#[trigger] durable_read(before(b,true),h,v)
            by {no_noninitial_durable(b,true,h,v);}}
    }
}

pub open spec fn handoff(rho:Resolver,b:Fork,k:nat) -> Cut {
    let s=sample(b,false,rho,12);
    let stopped=take(rho,s,Action::StopFirstClient);let crashed=take(rho,stopped,Action::CrashR3);
    if k==0 {s} else if k==1 {stopped} else if k==2 {crashed} else {take(rho,crashed,Action::StartSecondClient)}
}
pub open spec fn after_c2(b:Fork,rho:Resolver) -> weak::World {
    let s=handoff(rho,b,3);let end=rpc::at_step(rho,s,Replica::R1,Replica::R2,9);
    carried(before(b,false),end)
}
pub open spec fn delayed_finishes(b:Fork,rho:Resolver) -> bool {
    let f=paper_ops();let s=handoff(rho,b,3);let end2=rpc::at_step(rho,s,Replica::R1,Replica::R2,9);
    let delivery=Action::Deliver(0);let received=take(rho,end2,delivery);
    let w=carried(before(b,false),received);let a=weak::Action::Handle(1);let u=weak::step(f,w,a);
    let reply=weak::Action::Receive(1);let end=weak::step(f,u,reply);
    program::joint(f,rho,end2,delivery,received) && weak_ports_quiet(before(b,false),end2,received)
        && received.net.pending==end2.net.pending.remove(0) && received.core.calls==end2.core.calls &&
        w.wire.get(1)==Some(weak::Packet::Request(rival(b))) && weak::enabled(w,a) && weak::enabled(u,reply) &&
        u.wire.get(1)==Some(weak::Packet::Reply(rival(b).id,1)) && end.answers.get(rival(b).id)==Some(1) &&
        end.answers.get(local(b).id)==Some(1) && end.front.calls==w.front.calls &&
        (end.front.base.disk)(anchor(b)).value==first_value(opposite(b))
}
// On this different invocation placement, R3 alone handled the observed
// RMW. Deferring the other, already-issued weak request leaves the entire
// ordinary SR2 majority at genesis. Finish the deferred RMW after SR2.
pub proof fn returning_r3_before_any_copy(b:Fork,rho:Resolver)
    requires rho(rowmap(b,false))==Some(first_value(b)),crate::stock_root_service::stock_read_rules(paper_ops(),rho),
    ensures first_trace(b,false,rho),({
        let es=seq![Action::StopFirstClient,Action::CrashR3,Action::StartSecondClient];
        let s=handoff(rho,b,3);let q=rpc::at_step(rho,s,Replica::R1,Replica::R2,9);
        (forall|k:nat| k<3 ==> program::joint(paper_ops(),rho,handoff(rho,b,k),#[trigger] es[k as int],handoff(rho,b,k+1))
            && weak_ports_quiet(before(b,false),handoff(rho,b,k),handoff(rho,b,k+1)))
            && (forall|k:nat| k<9 ==> weak_ports_quiet(before(b,false),#[trigger] rpc::at_step(rho,s,Replica::R1,Replica::R2,k),
                rpc::at_step(rho,s,Replica::R1,Replica::R2,k+1)))
            && rpc::exchange(paper_ops(),rho,s,Replica::R1,Replica::R2) && q.net.pending==sample(b,false,rho,12).net.pending
            && q.net.pending.get(0)==Some(copy(b)) && delivery::enabled(q.net,Action::Deliver(0))
            && q.core.calls[1].answer==Some(first_value(b)) && q.core.calls[2].answer==Some(1)
            && !crate::read_recovery::compatible(b,1) && delayed_finishes(b,rho)
    }),
{
    crate::stock_root_service::a_forces_root_pair(paper_ops(),rho);addressed_first(b,false,rho);let f=paper_ops();let es=seq![Action::StopFirstClient,Action::CrashR3,Action::StartSecondClient];
    assert forall|k:nat| k<3 implies program::joint(f,rho,handoff(rho,b,k),#[trigger] es[k as int],handoff(rho,b,k+1))
        by {assert(k==0 || k==1 || k==2);}
    let s=handoff(rho,b,3);let l=Replica::R1;let r=Replica::R2;
    assert(rpc::fresh_majority(s,l,r));rpc::addressed_exchange(f,rho,s,l,r);
    assert(rpc::reports(s,l,r) =~= root_reports());
    crate::read_recovery::history_accepts_exactly_observed_value(b,1);
}
#[verifier::rlimit(16)]
pub proof fn reference_at_isolated_origin(b:Fork)
    ensures ({
        let rho=crate::mixed_service_transfer::reference_sample();let f=paper_ops();
        let end=after_c2(b,rho);let s=handoff(rho,b,3);
        first_trace(b,true,rho) && sample(b,true,rho,12).core.calls[1].answer==Some(first_value(b))
            && held(b,true,rho,first_value(b)) && (forall|h:RecoveredOrder| !#[trigger] durable_read(before(b,true),h,first_value(b)))
            && first_trace(b,false,rho) && rpc::exchange(f,rho,s,Replica::R1,Replica::R2)
            && end.front.calls[1].answer==Some(first_value(b)) && end.front.calls[2].answer==Some(1) && delayed_finishes(b,rho)
            && !crate::read_recovery::compatible(b,1)
    }),
{
    hide(ports);hide(program::joint);hide(rpc::exchange);hide(program::stock_contract);
    hide(crate::stock_root_service::stock_read_rules);hide(crate::stock_root_service::repaired);hide(delayed_finishes);
    let rho=crate::mixed_service_transfer::reference_sample();split_return(b,rho);
    assert((sample(b,true,rho,12).core.base.disk)(Replica::R3).value==first_value(b));
    assert(held(b,true,rho,first_value(b)));
    crate::stock_root_service::reference_original_service(paper_ops(),b.notice);
    assert(rho(rowmap(b,false))==Some(first_value(b)));returning_r3_before_any_copy(b,rho);
}
}
