// Safety audit of the actual guarded worker. The alternative one-failure
// continuation tests this implementation; it is not used by the general
// two-execution theorem, whose failed replica in both histories is R3.
use vstd::prelude::*;
use crate::{Replica,origin};
use crate::checkpoint::*;
use crate::delivery::{self,Action};
use crate::facade_hybrid as hybrid;
use crate::facade_linear::CommandSemantics;
use crate::fallback_program as front;
use crate::first_copy_wait::Cut;
use crate::live_quorum as rpc;
use crate::mixed_service_transfer::reference_sample;
use crate::ordered_round::{self as base,Store,Work};
use crate::read_dispatch as jobs;
use crate::read_recovery::compatible;
use crate::sender_forks as forks;
use crate::stock_facade::*;
use crate::worker_guard as guard;
use crate::weak_round as weak;
use crate::facade_progress as fair;
use crate::progress;
use crate::delivery::Process;

verus! {

// Readiness is the only change to the backend. Relate actual inputs;
// a dispatcher poll that submits instead of replying may not be replayed
// as a direct response.
proof fn same_instruction(f:CommandSemantics,s:State<Store>,e:Event<Work>,rho:crate::quorum_rpc::Resolver,g:jobs::Admission)
    requires guard::check(s.base,input(s,e)),!jobs::miss(s,e,rho,g),
    ensures jobs::permitted(guard::engine(f),s,e,rho,g)==enabled(base::engine(f),s,e),
        jobs::advance(guard::engine(f),s,e,rho,g)==front::apply_event(rho,base::engine(f),s,e),
{}

pub open spec fn took(f:CommandSemantics,s:State<Store>,e:Event<Work>,u:State<Store>) -> bool {
    let p=guard::engine(f);let rho=reference_sample();let g=crate::dispatch_boundary::on();
    jobs::permitted(p,s,e,rho,g) && jobs::advance(p,s,e,rho,g)==u
}

pub open spec fn weak_end() -> weak::World {
    let f=weak::paper_ops();let one=weak::step(f,weak::start(),weak::Action::Send(0,weak::request(crate::Op::W1)));
    let both=weak::step(f,one,weak::Action::Send(1,weak::request(crate::Op::W2)));
    let left=weak::step(f,both,weak::Action::Handle(0));let right=weak::step(f,left,weak::Action::Handle(1));
    weak::step(f,weak::step(f,right,weak::Action::Receive(0)),weak::Action::Receive(1))
}
// Both offered copies and the weak RPC results precede the guarded front
// end's first SR1 instruction. A weak Send runs neither Submit nor Serve.
pub open spec fn offers(b:Fork) -> bool {
    let f=weak::paper_ops();let end=weak_end();let s=end.front;let n=local_rmw_cells();
    let a=send(0,delivery::Path::Weak,at(Replica::R1),at(Replica::R3),Wire::Copy((s.base.disk)(Replica::R1).value));
    let h=delivery::advance(|v,w|cell(v,w),n,a);
    let d=send(1,delivery::Path::Weak,at(Replica::R2),at(Replica::R3),Wire::Copy((s.base.disk)(Replica::R2).value));
    end.answers.get(weak::request(crate::Op::W1).id)==Some(1) && end.answers.get(weak::request(crate::Op::W2).id)==Some(1)
        && s==front::original(b,0).core && delivery::enabled(n,a) && delivery::enabled(h,d)
        && delivery::advance(|v,w|cell(v,w),h,d)==front::original(b,0).net
        && hybrid::invocation(s,n,a)==Event::Idle && hybrid::invocation(s,h,d)==Event::Idle
        && hybrid::inner(n,a)==Event::Idle && hybrid::inner(h,d)==Event::Idle && took(f,s,Event::Idle,s)
        && hybrid::weak_part(s,n,a)==s && hybrid::weak_part(s,h,d)==s
}
proof fn offered_after_returns(b:Fork)
    ensures offers(b),
{
    let f=weak::paper_ops();let s=weak_end().front;
    weak::actual_overlap(b);hybrid::weak_calls_and_issued_offers(f,b);
    same_instruction(f,s,Event::Idle,reference_sample(),crate::dispatch_boundary::on());
    assert(front::apply_event(reference_sample(),base::engine(f),s,Event::Idle).closed =~= s.closed);
}

pub open spec fn guarded_release(f:CommandSemantics,b:Fork) -> bool {
    let rho=reference_sample();let old=front::original(b,15);let r=origin(b.branch);let id=forks::late(b);
    let x=forks::crash(f,rho,old,r);let y=forks::receive(f,rho,x,id);let u=forks::alternate(f,rho,b);
    let idle=jobs::advance(guard::engine(f),x.core,Event::Idle,rho,crate::dispatch_boundary::on());
    forks::release_after_origin_crash(f,rho,b) && took(f,old.core,Event::Work(Work::Crash(r)),x.core)
        && hybrid::invocation(x.core,x.net,Action::Deliver(id))==Event::Idle && hybrid::inner(x.net,Action::Deliver(id))==Event::Idle
        && took(f,x.core,Event::Idle,idle) && idle==x.core && y.core==hybrid::weak_part(idle,x.net,Action::Deliver(id))
        && y.net==delivery::advance(|x,w|cell(x,w),x.net,Action::Deliver(id))
        && took(f,y.core,Event::Invoke(2,Method::Read),u.core)
}

proof fn release(f:CommandSemantics,b:Fork)
    requires forks::release_after_origin_crash(f,reference_sample(),b),
    ensures guarded_release(f,b),
{
    let rho=reference_sample();let g=crate::dispatch_boundary::on();
    let s=front::original(b,15);let r=origin(b.branch);
    let x=forks::crash(f,rho,s,r);let y=forks::receive(f,rho,x,forks::late(b));
    same_instruction(f,s.core,Event::Work(Work::Crash(r)),rho,g);
    same_instruction(f,x.core,Event::Idle,rho,g);
    assert(front::apply_event(rho,base::engine(f),x.core,Event::Idle).closed =~= x.core.closed);
    same_instruction(f,y.core,Event::Invoke(2,Method::Read),rho,g);
}

pub open spec fn direct_step(f:CommandSemantics,s:Cut,l:Replica,r:Replica,k:nat) -> bool {
    let rho=reference_sample();let x=rpc::at_step(rho,s,l,r,k);let y=rpc::at_step(rho,s,l,r,k+1);
    let a=rpc::actions(s,l,r)[k as int];let e=hybrid::request(rpc::decode(x.net,a),2);
    rpc::rpc_step(f,rho,x,a,y) && took(f,x.core,e,y.core) && x.core.base==y.core.base
}

proof fn poll_rows(s:Cut,l:Replica,r:Replica,k:nat)
    requires rpc::fresh_majority(s,l,r),k<9,
    ensures ({
        let rho=reference_sample();let x=rpc::at_step(rho,s,l,r,k);
        let a=rpc::actions(s,l,r)[k as int];let e=hybrid::request(rpc::decode(x.net,a),2);
        e is Poll ==> e==Event::<Work>::Poll(2) && rows(x.core.calls[2])==rpc::reports(s,l,r)
    }),
{
    hide(reference_sample);
    prefix_index(k as int);
    if k==8 {assert(rows(rpc::at_step(reference_sample(),s,l,r,k).core.calls[2]) =~= rpc::reports(s,l,r));}
}

proof fn uniform_exchange(f:CommandSemantics,s:Cut,l:Replica,r:Replica)
    requires rpc::fresh_majority(s,l,r),reference_sample()(rpc::reports(s,l,r)).is_some(),
    ensures forall|k:nat| k<9 ==> #[trigger] direct_step(f,s,l,r,k),
{
    hide(guard::engine);hide(jobs::advance);hide(jobs::permitted);hide(reference_sample);
    hide(rpc::rpc_step);hide(rpc::at_step);hide(rpc::decode);hide(rpc::actions);
    let rho=reference_sample();let g=crate::dispatch_boundary::on();
    rpc::addressed_exchange(f,rho,s,l,r);
    assert forall|k:nat| k<9 implies #[trigger] direct_step(f,s,l,r,k) by {
        let x=rpc::at_step(rho,s,l,r,k);let y=rpc::at_step(rho,s,l,r,k+1);
        let a=rpc::actions(s,l,r)[k as int];let e=hybrid::request(rpc::decode(x.net,a),2);
        assert(rpc::rpc_step(f,rho,x,a,y));
        poll_rows(s,l,r,k);
        assert(!jobs::miss(x.core,e,rho,g));
        same_instruction(f,x.core,e,rho,g);
        assert(took(f,x.core,e,y.core)) by {reveal(rpc::rpc_step);}
        assert(x.core.base==y.core.base) by {reveal(rpc::at_step);}
    }
}

pub proof fn guarded_worker_violates_history(b:Fork)
    ensures ({
        let f=crate::weak_round::paper_ops();let rho=reference_sample();
        let d=forks::opposite(b);let other=origin(d.branch);let s=forks::alternate(f,rho,b);
        let end=rpc::at_step(rho,s,other,Replica::R3,9);
        guard::guarded_prefix(f,b) && offers(b) && guarded_release(f,b)
            && (forall|k:nat| k<9 ==> #[trigger] direct_step(f,s,other,Replica::R3,k))
            && end.core.calls[1].answer==Some(first_value(b))
            && end.core.calls[2].answer==Some(first_value(d)) && !compatible(b,first_value(d))
    }),
{
    hide(guard::guarded_prefix); hide(rpc::exchange); hide(forks::prefix_taken);
    let f=crate::weak_round::paper_ops();let rho=reference_sample();let d=forks::opposite(b);
    let other=origin(d.branch);let s=forks::alternate(f,rho,b);
    offered_after_returns(b);
    guard::assembled(f,b);forks::reference_reader(f,b);release(f,b);
    assert(rpc::exchange(f,rho,s,other,Replica::R3));
    let end=rpc::at_step(rho,s,other,Replica::R3,9);
    assert(end.core.calls[2].answer==rho(rpc::reports(s,other,Replica::R3)) && end.core.calls[1]==s.core.calls[1]) by { reveal(rpc::exchange); }
    let old=front::original(b,15);
    assert(old.core.calls[1].answer==Some(first_value(b))) by {reveal(forks::prefix_taken);}
    assert(s.core.calls[1]==old.core.calls[1]);
    uniform_exchange(f,s,other,Replica::R3);
}

pub open spec fn last(b:Fork) -> Cut {
    let f=weak::paper_ops();let rho=reference_sample();let other=origin(forks::opposite(b).branch);
    rpc::at_step(rho,forks::alternate(f,rho,b),other,Replica::R3,9)
}
pub open spec fn turn(b:Fork,k:nat) -> Action<Wire> {
    if k%3==0 {Action::Strong(at(origin(forks::opposite(b).branch)))}
    else if k%3==1 {Action::Strong(at(Replica::R3))}
    else {Action::ClientInput(Process::SecondClient,Wire::Peer(0))}
}
pub open spec fn network_tail(b:Fork) -> progress::Execution<int,Wire> {
    progress::Execution{state:|_i|last(b).net,action:|i|turn(b,i)}
}
pub open spec fn front_tail(b:Fork) -> fair::Run<Store,Work> {
    fair::Run{state:|_i|last(b).core,event:|i|hybrid::inner(last(b).net,turn(b,i))}
}
proof fn terminal_state(b:Fork)
    ensures ({
        let s=last(b);let c=s.core;
        c.calls.dom()==set![1nat,2] && c.calls[1].answer.is_some() && c.calls[2].answer.is_some()
            && c.base.stopped.contains(1) && c.base.calls.is_empty() && c.base.live==all_replicas().remove(origin(b.branch))
            && crate::ordered_store::majority(rows(c.calls[2]).dom())
            && (forall|r:Replica| {let leg=#[trigger] (c.calls[1].legs)(r); leg is Received || leg is InFlight})
            && (forall|r:Replica| {let leg=#[trigger] (c.calls[2].legs)(r); leg is Received || leg is Unsent})
            && s.net.first_stopped && s.net.second_started && !s.net.r3_crashed && s.net.unavailable==Some(origin(b.branch))
            && (forall|id:nat| #[trigger] s.net.pending.contains_key(id) ==> !delivery::live(s.net,s.net.pending[id].to))
    }),
{
    hide(reference_sample);hide(rpc::rpc_step);hide(guard::guarded_prefix);hide(forks::prefix_taken);
    hide(crate::facade_transport::at_time);hide(rpc::exchange);
    let f=weak::paper_ops();let rho=reference_sample();let d=forks::opposite(b);let other=origin(d.branch);
    let x=forks::alternate(f,rho,b);let s=last(b);let old=front::original(b,15);
    crate::facade_transport::actual_first_rpc(b,15);forks::reference_reader(f,b);guarded_worker_violates_history(b);
    assert(s.core.calls[1]==old.core.calls[1]) by {reveal(rpc::exchange);}
    assert(rows(s.core.calls[2]) =~= rpc::reports(x,other,Replica::R3));
    assert(s.core.calls.dom() =~= set![1nat,2]);
    assert(s.core.base.calls =~= Map::<nat,Method>::empty());
    assert forall|id:nat| #[trigger] s.net.pending.contains_key(id) implies !delivery::live(s.net,s.net.pending[id].to) by {
        assert(s.net==x.net) by {reveal(rpc::exchange);}
        assert(x.net.pending==old.net.pending.remove(forks::late(b)));
    }
}
proof fn no_outstanding_job(b:Fork,id:nat,r:Replica,st:Stage)
    ensures ({
        let s=last(b);let p=guard::engine(weak::paper_ops());
        !enabled(p,s.core,Event::Poll(id)) && !enabled(p,s.core,Event::Rpc(id,r,st))
            && s.core.base.calls.is_empty() && s.core.base.live==all_replicas().remove(origin(b.branch))
    }),
{
    hide(last);terminal_state(b);
    let s=last(b).core;
    if id==1 {let l=(s.calls[1].legs)(r);assert(l is InFlight || l is Received);}
    else if id==2 {let l=(s.calls[2].legs)(r);assert(l is Unsent || l is Received);}
    else { assert(!s.calls.contains_key(id)); }
}
proof fn tail_step(b:Fork,i:nat)
    ensures ({
        let x=last(b);let a=turn(b,i);let f=weak::paper_ops();
        delivery::enabled(x.net,a) && delivery::advance(|v,w|cell(v,w),x.net,a)==x.net &&
            hybrid::invocation(x.core,x.net,a)==Event::Idle && took(f,x.core,Event::Idle,x.core)
            && took(f,x.core,hybrid::inner(x.net,a),x.core) && hybrid::weak_part(x.core,x.net,a)==x.core
    }),
{
    let f=weak::paper_ops();let rho=reference_sample();let x=last(b);let a=turn(b,i);let e=hybrid::inner(x.net,a);
    no_outstanding_job(b,2,Replica::R3,Stage::Offer);
    same_instruction(f,x.core,e,rho,crate::dispatch_boundary::on());
    same_instruction(f,x.core,Event::Idle,rho,crate::dispatch_boundary::on());
    assert(front::apply_event(rho,base::engine(f),x.core,e).closed =~= x.core.closed);
    assert(front::apply_event(rho,base::engine(f),x.core,Event::Idle).closed =~= x.core.closed);
    assert(delivery::advance(|v,w|cell(v,w),x.net,a).locals =~= x.net.locals);
}
// All original packets to still-live destinations have already arrived.
// Remaining envelopes stay queued. Runnable replicas and C2 take real
// local turns forever; both completed calls and their answers persist.
pub proof fn fair_tail_after_history_violation(b:Fork)
    ensures ({
        let x=last(b);let f=weak::paper_ops();let n=network_tail(b);let e=front_tail(b);
        x.core.calls[1].answer==Some(first_value(b)) && x.core.calls[2].answer==Some(first_value(forks::opposite(b)))
            && !compatible(b,first_value(forks::opposite(b)))
            && (forall|id:nat| #[trigger] x.net.pending.contains_key(id) ==> !delivery::live(x.net,x.net.pending[id].to))
            && progress::delivery_fair(n) && progress::process_fair(n,|s,p|delivery::live(s,p))
            && fair::front_fair(guard::engine(f),e) && guard::fair(f,fair::project(e))
            && (forall|i:nat| {let a=#[trigger] (n.action)(i);
                delivery::enabled(x.net,a) && delivery::advance(|v,w|cell(v,w),x.net,a)==x.net
                    && took(f,x.core,hybrid::inner(x.net,a),x.core)})
    }),
{
    hide(last);hide(forks::alternate);hide(rpc::at_step);hide(guard::guarded_prefix);hide(forks::release_after_origin_crash);
    hide(direct_step);hide(offers);hide(guarded_release);
    let f=weak::paper_ops();let rho=reference_sample();let x=last(b);let n=network_tail(b);let e=front_tail(b);
    let p=guard::engine(f);let h=fair::project(e);let other=origin(forks::opposite(b).branch);
    terminal_state(b);guarded_worker_violates_history(b);
    assert(x==rpc::at_step(rho,forks::alternate(f,rho,b),other,Replica::R3,9)) by {reveal(last);}
    assert forall|id:nat| #[trigger] x.net.pending.contains_key(id) implies !delivery::live(x.net,x.net.pending[id].to) by {};
    assert forall|i:nat,id:nat| #[trigger] (n.state)(i).pending.contains_key(id) implies
        exists|j:nat| j>=i && (#[trigger] (n.action)(j)==Action::Deliver(id) || !delivery::live((n.state)(j),(n.state)(i).pending[id].to))
        by {assert((n.action)(i)==turn(b,i)); assert(!delivery::live((n.state)(i),(n.state)(i).pending[id].to));}
    let runnable=|s:crate::read_call::Net,p:Process|delivery::live(s,p);
    assert forall|i:nat,q:Process| #[trigger] progress::continuously_runnable(n,runnable,i,q) implies
        exists|j:nat| j>=i && #[trigger] progress::runs_at(n,j,q) by {
        assert(runnable((n.state)(i),q));let d:nat=if q==at(other) {0} else if q==at(Replica::R3) {1} else {2};
        let j=3*i+d;assert(j%3==d);assert(progress::runs_at(n,j,q));
    }
    assert forall|i:nat,id:nat,r:Replica,st:Stage| #[trigger] fair::scheduled(p,e,Event::Rpc(id,r,st),i)
        by {no_outstanding_job(b,id,r,st);assert((e.event)(i)==hybrid::inner(x.net,turn(b,i)));assert(!enabled(p,(e.state)(i),Event::Rpc(id,r,st)));}
    assert forall|i:nat,id:nat| #[trigger] fair::scheduled(p,e,Event::Poll(id),i)
        by {no_outstanding_job(b,id,Replica::R3,Stage::Offer);assert((e.event)(i)==hybrid::inner(x.net,turn(b,i)));assert(!enabled(p,(e.state)(i),Event::Poll(id)));}
    assert forall|i:nat,id:nat,q:Set<Replica>| #[trigger] guard::scheduled_work(f,h,i,Work::Serve(id,q)) by {
        no_outstanding_job(b,id,Replica::R3,Stage::Offer);assert(guard::served_or_disabled(f,h,i,Work::Serve(id,q)));
    }
    assert forall|i:nat,r:Replica| #[trigger] guard::scheduled_work(f,h,i,Work::Tick(r)) by {
        let j=3*i+if r==Replica::R3 {1nat} else {0nat};
        no_outstanding_job(b,2,r,Stage::Offer);
        assert(guard::served_or_disabled(f,h,j,Work::Tick(r)));
    }
    assert forall|i:nat| {let a=#[trigger] (n.action)(i);delivery::enabled(x.net,a) &&
        delivery::advance(|v,w|cell(v,w),x.net,a)==x.net && took(f,x.core,hybrid::inner(x.net,a),x.core)} by {tail_step(b,i);}
}

}
