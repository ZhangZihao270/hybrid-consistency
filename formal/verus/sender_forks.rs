use vstd::prelude::*;
use crate::{Branch,Replica,origin};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Process};
use crate::facade_linear::CommandSemantics;
use crate::facade_transport::actual_first_rpc;
use crate::facade_hybrid::{prefix,weak_part};
use crate::fallback_program::{self as program,apply_event};
use crate::first_copy_wait::Cut;
use crate::live_quorum as rpc;
use crate::metadata_pair::{self,Local,first_rows};
use crate::metadata_reader::single;
use crate::ordered_round::{engine,Work};
use crate::quorum_rpc::Resolver;
use crate::stock_facade::*;
use crate::read_recovery::compatible;

verus! {

pub open spec fn firsts(rho:Resolver,n:Notice) -> bool {
    let m=single(rho,Set::empty());let value=|x:Local|x.returned.unwrap();
    completed_quorum_sample(m,value,alpha(n)) && completed_quorum_sample(m,value,beta(n))
}
pub open spec fn opposite(b:Fork) -> Fork {
    if b.branch==Branch::Alpha {beta(b.notice)} else {alpha(b.notice)}
}
pub open spec fn late(b:Fork) -> nat { crate::second_copy_schedule::copy_id(opposite(b)) }

// Use the existing front-end crash and invocation operations. Enable the
// transport lifecycle for any one failed site. A crash never edits a queue.
pub open spec fn crash(f:CommandSemantics,rho:Resolver,s:Cut,r:Replica) -> Cut {
    let n=s.net;
    Cut{net:Network{r3_crashed:r==Replica::R3,unavailable:if r==Replica::R3 {None} else {Some(r)},..n},
        core:apply_event(rho,engine(f),s.core,Event::Work(Work::Crash(r)))}
}
pub open spec fn one_failure(f:CommandSemantics,s:Cut,r:Replica) -> bool {
    s.net.unavailable.is_none() && !s.net.r3_crashed && delivery::live(s.net,at(r))
        && enabled(engine(f),s.core,Event::Work(Work::Crash(r)))
}
pub open spec fn begin(f:CommandSemantics,rho:Resolver,s:Cut) -> Cut {
    Cut{net:Network{second_started:true,..s.net},core:apply_event(rho,engine(f),s.core,Event::Invoke(2,Method::Read))}
}
pub open spec fn new_client(f:CommandSemantics,s:Cut) -> bool {
    s.net.first_stopped && !s.net.second_started && s.core.calls[1].answer.is_some()
        && enabled(engine(f),s.core,Event::Invoke(2,Method::Read))
}
pub open spec fn receive(f:CommandSemantics,rho:Resolver,s:Cut,id:nat) -> Cut {
    let a=Action::Deliver(id);let idle=apply_event(rho,engine(f),s.core,Event::Idle);
    Cut{net:delivery::advance(|x,w|cell(x,w),s.net,a),core:weak_part(idle,s.net,a)}
}
pub open spec fn alternate(f:CommandSemantics,rho:Resolver,b:Fork) -> Cut {
    let s=crash(f,rho,program::original(b,15),origin(b.branch));
    begin(f,rho,receive(f,rho,s,late(b)))
}
pub open spec fn prefix_taken(f:CommandSemantics,rho:Resolver,b:Fork) -> bool {
    first_round(b) && program::original(b,0).net==after_local_rmws() && crate::facade_hybrid::prefix_entry(f,b)
        && (forall|k:nat| k<17 ==> program::joint(f,rho,program::original(b,k),
            #[trigger] actions_to_crash(b)[k as int],program::original(b,k+1)))
        && program::original(b,15).net.first_stopped && prefix(b,15).calls[1].answer==Some(first_value(b))
}
pub proof fn original_prefix(f:CommandSemantics,rho:Resolver,b:Fork)
    requires rho(first_rows(b,13))==Some(first_value(b)),
    ensures prefix_taken(f,rho,b),
{
    fanout_and_reply_deliveries(b);crate::facade_hybrid::weak_calls_and_issued_offers(f,b);actual_first_rpc(b,15);prefix_transport_is_enabled(b);
    assert forall|k:nat| k<17 implies program::joint(f,rho,program::original(b,k),
        #[trigger] actions_to_crash(b)[k as int],program::original(b,k+1)) by {program::original_for(f,rho,b,k);}
}

pub open spec fn release_after_origin_crash(f:CommandSemantics,rho:Resolver,b:Fork) -> bool {
    let old=program::original(b,15);let dead=origin(b.branch);let id=late(b);
    let x=crash(f,rho,old,dead);let u=receive(f,rho,x,id);let s=alternate(f,rho,b);
    let d=opposite(b);let other=origin(d.branch);let r3=Replica::R3;
    one_failure(f,old,dead) && x.net.pending==old.net.pending && x.net.pending.get(id)==Some(packet_for(b,id))
        && x.net.pending[id].from==at(other) && x.net.pending[id].to==at(r3)
        && x.net.pending[id].input==Wire::Copy(first_value(d)) && delivery::enabled(x.net,Action::Deliver(id))
        && program::joint(f,rho,x,Action::Deliver(id),u) && new_client(f,u)
        && s.net.pending==old.net.pending.remove(id) && s.net.pending.get(2)==Some(packet_for(b,2))
        && s.net.pending.get(crate::second_copy_schedule::reply_id(d))==Some(packet_for(b,crate::second_copy_schedule::reply_id(d)))
        && s.core.base.live==all_replicas().remove(dead)
        && (s.core.base.disk)(dead)==(old.core.base.disk)(dead)
        && (s.core.base.disk)(other)==(old.core.base.disk)(other)
        && (old.core.base.disk)(r3).value==first_value(b) && (s.core.base.disk)(r3).value==first_value(d)
        && s.core.calls[1]==old.core.calls[1]
        && rpc::fresh_majority(s,other,r3) && rpc::reports(s,other,r3)==first_rows(d,13)
}
proof fn live_after_release(f:CommandSemantics,rho:Resolver,b:Fork)
    ensures release_after_origin_crash(f,rho,b),
{
    let s=program::original(b,15);let r=origin(b.branch);let d=opposite(b);let other=origin(d.branch);
    actual_first_rpc(b,15);let x=crash(f,rho,s,r);let y=receive(f,rho,x,late(b));let u=alternate(f,rho,b);
    assert(x.core.base.live =~= all_replicas().remove(r));
    assert(apply_event(rho,engine(f),x.core,Event::Idle).closed =~= x.core.closed);
    assert(apply_event(rho,engine(f),x.core,Event::Idle)==x.core);
    assert(u.core.closed =~= Set::empty());assert(rpc::reports(u,other,Replica::R3) =~= first_rows(d,13));
}
pub open spec fn actual_sr2(f:CommandSemantics,rho:Resolver,b:Fork) -> bool {
    let s=program::original(b,17);let l=Replica::R1;let r=Replica::R2;
    rpc::fresh_majority(s,l,r) && rpc::exchange(f,rho,s,l,r)
        && rpc::reports(s,l,r)==crate::metadata_stock::unadvanced_rows()
        && rpc::at_step(rho,s,l,r,9).core.calls[1].answer==Some(first_value(b))
}
proof fn original_exchange(f:CommandSemantics,rho:Resolver,b:Fork)
    ensures actual_sr2(f,rho,b),
{
    let s=program::original(b,17);let l=Replica::R1;let r=Replica::R2;
    actual_first_rpc(b,17);assert(rpc::fresh_majority(s,l,r));rpc::addressed_exchange(f,rho,s,l,r);
    assert(rpc::reports(s,l,r) =~= crate::metadata_stock::unadvanced_rows());
}

pub open spec fn original_answer(rho:Resolver,b:Fork) -> Option<int> {
    rpc::at_step(rho,program::original(b,17),Replica::R1,Replica::R2,9).core.calls[2].answer
}
// On the paper schedules even sender-sensitive *readiness* agrees at
// this actual poll. If both are pending, the statement ends there.
pub proof fn both_original_polls(f:CommandSemantics,rho:Resolver,n:Notice)
    requires firsts(rho,n),
    ensures ({let a=alpha(n);let b=beta(n);
        prefix_taken(f,rho,a) && prefix_taken(f,rho,b) && actual_sr2(f,rho,a) && actual_sr2(f,rho,b)
            && original_answer(rho,a)==rho(crate::metadata_stock::unadvanced_rows())
            && original_answer(rho,b)==original_answer(rho,a)
            && match original_answer(rho,a) {Some(v)=> !compatible(a,v) || !compatible(b,v),None=>true}}),
{
    hide(prefix_taken);hide(rpc::exchange);
    let a=alpha(n);let b=beta(n);
    crate::metadata_reader::actual_first_decision(a,rho,Set::empty());crate::metadata_reader::actual_first_decision(b,rho,Set::empty());
    original_prefix(f,rho,a);original_prefix(f,rho,b);original_exchange(f,rho,a);original_exchange(f,rho,b);
    if let Some(v)=rho(crate::metadata_stock::unadvanced_rows()) {
        crate::read_recovery::history_accepts_exactly_observed_value(a,v);
        crate::read_recovery::history_accepts_exactly_observed_value(b,v);
    }
}
// The C1 prefixes (including both survivor replies) and both weak commands
// are exactly the paper's. At the branch with a different single failure,
// the pending OTHER writer's delivery to R3 precedes the fresh C2 invocation.
// Use the same two physical sender IDs and stamps as the opposite SR1.
pub proof fn both_schedules(f:CommandSemantics,rho:Resolver,b:Fork)
    requires completed_quorum_sample(single(rho,Set::empty()),|x:Local|x.returned.unwrap(),b),
        completed_quorum_sample(single(rho,Set::empty()),|x:Local|x.returned.unwrap(),opposite(b)),
    ensures prefix_taken(f,rho,b),actual_sr2(f,rho,b),release_after_origin_crash(f,rho,b),
        ({
            let other=origin(opposite(b).branch);let r=Replica::R3;let s=alternate(f,rho,b);
            let end=rpc::at_step(rho,s,other,r,9);
            rpc::exchange(f,rho,s,other,r) && end.core.calls[1].answer==Some(first_value(b))
                && end.core.calls[2].answer==Some(first_value(opposite(b))) && !compatible(b,first_value(opposite(b)))
        }),
{
    let d=opposite(b);let other=origin(d.branch);let r=Replica::R3;let s=alternate(f,rho,b);
    crate::metadata_reader::actual_first_decision(b,rho,Set::empty());
    crate::metadata_reader::actual_first_decision(d,rho,Set::empty());original_prefix(f,rho,b);original_exchange(f,rho,b);
    live_after_release(f,rho,b);rpc::addressed_exchange(f,rho,s,other,r);
    crate::read_recovery::history_accepts_exactly_observed_value(b,first_value(d));
}
pub proof fn reference_reader(f:CommandSemantics,b:Fork)
    ensures ({
        let rho=crate::mixed_service_transfer::reference_sample();let q=program::original(b,17);
        let r=Replica::R3;let d=opposite(b);let other=origin(d.branch);let s=alternate(f,rho,b);
        program::stock_contract(engine(f),rho,f,|e|crate::ordered_round::fair(e),crate::ordered_round::used())
            && prefix_taken(f,rho,b) && actual_sr2(f,rho,b)
            && rpc::at_step(rho,q,Replica::R1,Replica::R2,9).core.calls[2].answer.is_none()
            && release_after_origin_crash(f,rho,b) && rpc::exchange(f,rho,s,other,r)
            && rpc::at_step(rho,s,other,r,9).core.calls[2].answer==Some(first_value(d)) && !compatible(b,first_value(d))
    }),
{
    let rho=crate::mixed_service_transfer::reference_sample();let d=opposite(b);
    crate::mixed_service_transfer::ordinary_reference_escape(b);crate::ordered_round::concrete_full_a(f);
    program::all_stock_services(engine(f),rho,f,|e|crate::ordered_round::fair(e),crate::ordered_round::used());
    metadata_pair::real_first_with(rho,rho,b,Set::empty());metadata_pair::real_first_with(rho,rho,d,Set::empty());
    both_schedules(f,rho,b);
}
}
