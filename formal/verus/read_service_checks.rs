// Exercise the same capability and closed-region tests on existing real
// paths and guard implementations. The stock and hybrid scopes stay separate.
use vstd::prelude::*;
use crate::{origin,Replica};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Process,observations};
use crate::dispatch_boundary as dispatch;
use crate::facade_linear::CommandSemantics;
use crate::first_copy_wait::Cut;
use crate::genesis_service as genesis;
use crate::metadata_pair::{self as rpc,BeforeSample};
use crate::ordered_round::{engine,Store,Work};
use crate::promotion_wait as wait;
use crate::protocol::{memory,pending_before_end};
use crate::read_call as call;
use crate::read_dispatch as jobs;
use crate::read_nonblocking as nb;
use crate::read_service_contract as contract;
use crate::read_service_rank as rank;
use crate::quorum_rpc::Resolver;
use crate::service as svc;
use crate::sr2::{self,Reader,Select};
use crate::stock_facade::{Event,State,rows};
use crate::stock_root_service as repair;
use crate::survivors::sr2_result;
use crate::worker_guard as guard;

verus! {

// Runs actual strong handlers on their own states, even if the resolver
// distinguishes senders or declines the two live reports. The opposite
// implication uses the previously checked overapproximation of *all* steps.
pub open spec fn ordinary_cpu(f:CommandSemantics,rho:Resolver,g:jobs::Admission)
    -> wait::Relation<State<Store>,Event<Work>> {
    |s,e,u| jobs::permitted(engine(f),s,e,rho,g) && u==jobs::advance(engine(f),s,e,rho,g)
}
pub proof fn response_after_intake(f:CommandSemantics,b:Fork,rho:Resolver,g:jobs::Admission)
    requires crate::sender_forks::firsts(rho,b.notice),
    ensures ({
        let h=jobs::collected(b,rho);let reports=rows(h.core.calls[2]);let step=ordinary_cpu(f,rho,g);
        nb::possible(step,dispatch::done(2),h.core)==(rho(reports).is_some() || g(reports))
        && h.net.pending.get(2)==Some(packet_for(b,2)) && h.core.calls[1].answer==Some(first_value(b))
    }),
{
    hide(jobs::collected);hide(jobs::permitted);hide(jobs::advance);hide(jobs::completion_events);hide(jobs::service_states);
    hide(jobs::original_prefix);hide(jobs::physical_intake);hide(engine);hide(nb::within);
    let h=jobs::collected(b,rho);let s=h.core;let step=ordinary_cpu(f,rho,g);let d=dispatch::done(2);
    let large=dispatch::step(engine(f),rho,g,2);let m=rows(s.calls[2]);
    dispatch::exact_after_intake(f,b,rho,g);
    assert(h.net.pending.get(2)==Some(packet_for(b,2)) && s.calls[1].answer==Some(first_value(b)) && s.calls[2].answer.is_none())
        by {reveal(jobs::physical_intake);}
    if rho(m).is_some() || g(m) {
        let t=wait::Path{states:jobs::service_states(f,b,rho,g),actions:jobs::completion_events(rho,g)};
        assert(jobs::path(engine(f),rho,g,t.states,t.actions));
        assert forall|i:int| 0<=i<t.actions.len() implies step(t.states[i],#[trigger] t.actions[i],t.states[i+1]) by {};
        assert(d(t.states.last()));nb::from_path(step,d,t,0);
    } else if nb::possible(step,d,s) {
        let t=nb::to_path(step,d,s,choose|k:nat| #[trigger] nb::within(step,d,s,k));
        assert forall|i:int| 0<=i<t.actions.len() implies large(t.states[i],#[trigger] t.actions[i],t.states[i+1])
            by {assert(step(t.states[i],t.actions[i],t.states[i+1]));}
        assert(wait::first_return(large,d,s,t));
    }
}

pub open spec fn blocked() -> nb::Region<Store> { |s:Store|guard::mixed_job(s) }
pub proof fn lost_guard_is_a_trap(f:CommandSemantics,b:Fork)
    ensures guard::mixed_job(guard::issued(f,b)),
        nb::pending_trap(guard::internal(f),guard::finished(2),blocked()),
        !nb::possible(guard::internal(f),guard::finished(2),guard::issued(f,b)),
        nb::no_unlock(guard::internal(f),guard::finished(2),guard::network_effect(),blocked()),
        forall|k:rank::Rank<Store>| #[trigger] rank::valid(guard::internal(f),guard::finished(2),k)
            ==> !(k.domain)(guard::issued(f,b)),
{
    let r=guard::internal(f);let d=guard::finished(2);let bset=blocked();let effect=guard::network_effect();
    guard::first_failed_worker_instruction(f,b);
    assert forall|s:Store,a:guard::Internal,u:Store| bset(s) && #[trigger] r(s,a,u) implies bset(u)
        by {guard::internal_keeps_job(f,s,a,u);}
    assert(nb::pending_trap(r,d,bset));
    nb::trap_excludes_service(r,d,bset,guard::issued(f,b));
    assert forall|s:Store,a:guard::Internal,u:Store| bset(s) implies !#[trigger] nb::unlocks(r,d,effect,s,a,u) by {
        if nb::unlocks(r,d,effect,s,a,u) {nb::unlocks_require_service(r,d,effect,s,a,u);nb::trap_excludes_service(r,d,bset,s);}
    }
    assert forall|k:rank::Rank<Store>| #[trigger] rank::valid(r,d,k) implies !(k.domain)(guard::issued(f,b)) by {
        if (k.domain)(guard::issued(f,b)) {rank::schedule_exit(r,d,k,guard::issued(f,b));}
    }
}

// Inspect the effects rather than the instruction's name. With just C2's
// read registered, a guarded Serve cannot execute. Other enabled ordinary
// work in this region cannot change either disk, the ordinary tip, or any
// registered call or completed ordinary response. The workload also admits
// client-stop actions; no claim that all of them lie on a fair live-C2 run.
pub proof fn ordinary_actions_at_block(f:CommandSemantics,s:Store,w:Work,u:Store)
    requires guard::mixed_job(s),guard::internal(f)(s,guard::Internal::Ordinary(w),u),
    ensures !(w is Serve),u.disk==s.disk,u.tip==s.tip,u.done==s.done,u.calls==s.calls,u.live==s.live,
{
    guard::internal_keeps_job(f,s,guard::Internal::Ordinary(w),u);
    if let Work::Serve(id,q)=w {
        assert(id==2 && crate::stock_facade::Method::Read==s.calls[id]);
        assert(u.done.contains_key(id));
    }
}

// Local rebuild has to exist at the site. An ordinary protocol wait is
// possible until the enabled rebuild and its two actual reports are served.
pub open spec fn rebuilding(f:CommandSemantics,rho:Resolver) -> wait::Relation<Cut,Action<Wire>> {
    |s:Cut,a,u:Cut| {
        let e=crate::facade_hybrid::inner(s.net,a);
        let job=match a {Action::Local(r,_)=>Some(r),_=>None};
        delivery::enabled(s.net,a) && u.net==delivery::advance(|x,w|cell(x,w),s.net,a) &&
            crate::facade_transport::valid(s.net,crate::facade_transport::service(s.net,a,Process::SecondClient),s.core.calls[2],Process::SecondClient)
            && repair::with_rebuild(f,rho,s.core,e,job,u.core)
            && (match a {Action::Local(_,w)=>w==Wire::Copy(1),_=>true})
    }
}
pub open spec fn repair_cut(b:Fork,k:nat) -> Cut {
    Cut{net:rpc::read_net(b,BeforeSample::RestoreImages,k),core:genesis::at_read(b,k)}
}
pub open spec fn confirmed_at_site() -> wait::Relation<Cut,Action<Wire>> {
    |s:Cut,a,_u:Cut| match a {
        Action::Deliver(id)=> s.net.pending.contains_key(id) && notice_to(s.net.pending[id],s.net.pending[id].to), _=>false,
    }
}
proof fn rebuilt_edge(f:CommandSemantics,rho:Resolver,b:Fork,k:nat)
    requires k<11,repair::repair_step(f,rho,b,k),
    ensures ({
        let a=rpc::read_actions(b,BeforeSample::RestoreImages)[k as int];
        nb::ordinary(rebuilding(f,rho),confirmed_at_site())(repair_cut(b,k),a,repair_cut(b,k+1))
    }),
{
    hide(repair::with_rebuild);hide(crate::facade_transport::valid);hide(crate::facade_transport::service);
    hide(crate::facade_hybrid::inner);hide(genesis::at_read);hide(rpc::read_net);
    let a=rpc::read_actions(b,BeforeSample::RestoreImages)[k as int];let s=repair_cut(b,k);let u=repair_cut(b,k+1);
    assert(rebuilding(f,rho)(s,a,u));
    assert(!confirmed_at_site()(s,a,u)) by {reveal(rpc::read_net);prefix_index(k as int);}
}
pub proof fn actual_repair_remains_an_option(f:CommandSemantics,rho:Resolver,b:Fork)
    requires repair::stock_read_rules(f,rho),crate::sender_forks::firsts(rho,b.notice),
    ensures ({
        let t=repair_cut(b,11);let r=nb::ordinary(rebuilding(f,rho),confirmed_at_site());
        nb::possible(r,|s:Cut|s.core.calls[2].answer.is_some(),repair_cut(b,0)) && t.core.calls[2].answer==Some(1)
            && t.net.pending.get(2)==Some(packet_for(b,2)) && !crate::read_recovery::compatible(b,1)
    }),
{
    hide(rebuilding);hide(confirmed_at_site);hide(repair_cut);hide(nb::within);hide(repair::repair_step);
    hide(crate::sender_forks::prefix_taken);hide(repair::stock_read_rules);
    let r=nb::ordinary(rebuilding(f,rho),confirmed_at_site());let d=|s:Cut|s.core.calls[2].answer.is_some();
    repair::original_forks_with_rebuild(f,rho,b.notice);
    match b.branch {crate::Branch::Alpha=>{assert(b==alpha(b.notice));},crate::Branch::Beta=>{assert(b==beta(b.notice));}}
    assert(repair::repaired(f,rho,b));
    let a=rpc::read_actions(b,BeforeSample::RestoreImages);
    let t=wait::Path{states:Seq::new(12,|i:int|repair_cut(b,i as nat)),actions:a};
    assert forall|i:int| 0<=i<a.len() implies r(t.states[i],#[trigger] a[i],t.states[i+1]) by {
        assert(repair::repair_step(f,rho,b,i as nat));rebuilt_edge(f,rho,b,i as nat);
    }
    assert(t.states.last()==repair_cut(b,11));
    assert(t.states.last().core==genesis::at_read(b,11)) by {reveal(repair_cut);}
    nb::from_path(r,d,t,0);reveal(repair_cut);
}

// G was true before SR1. On this completed gated execution the enabling
// receipt has an exact index, no register changes, and no C2 publication
// on the receipt. The selector has no constraints on its result.
pub proof fn knowing_g_can_unlock(sel:Select)
    ensures ({
        let b=alpha(Notice::G);let local=sr2::reader(b,set![Replica::R2],sel);let res=|s:Reader|s.returned;
        let a=sr2::notified_actions(b);let s=Seq::new(11,|i:int|sr2::notified_net(b,i as nat));
        pre_sr1_g(b,weak_assignment(b,true).ops) && truthful_notice(b,weak_assignment(b,true).ops)
            && contract::decisive_receipt(Notice::G,local,res,s,a,4)
            && s[4].locals==s[5].locals && sr2_result(local,res,call::obs(call::prefix(s,a,5))).is_none()
    }),
{
    hide(svc::response_path);hide(call::step);hide(nb::possible);hide(sr2::read_update);
    let b=alpha(Notice::G);let owner=Replica::R2;let local=sr2::reader(b,set![owner],sel);let res=|s:Reader|s.returned;
    let net=checkpoint_end(b);let ids=delayed_slots();let d=call::posted(local,res);
    let r=nb::ordinary(call::step(local,res,ids),call::receipt(owner));let x=call::launch(net);
    let a=sr2::notified_actions(b);let s=Seq::new(11,|i:int|sr2::notified_net(b,i as nat));
    sr2::already_g_receipt_is_indispensable_to_gated_read(sel);
    if nb::possible(r,d,x) {
        let l=contract::without_receipt(local,res,net,ids,owner);
        assert(svc::consumed_issue(net,2,l.nets,l.actions));
        assert(delivery::trace(|x,w|cell(x,w),l.nets,l.actions)) by {reveal(svc::response_path);}
        contract::avoids_issued(net,l,2,owner);
    }
    let v=sel(sr2::report(b,Replica::R1),sr2::report(b,Replica::R2));
    let i=contract::actual_unlock(Notice::G,local,res,s,a,v);
    prefix_index(i as int);assert(i==4);
    call::lift_response(local,res,net,ids,s,a,v);
    let l=call::prefix(s,a,5);let hs=call::obs(l);let es=observations(s,a);
    assert(hs =~= es.take(5));crate::protocol::memory_on_common_prefix(local,Process::SecondClient,hs,es,5);
    assert(pending_before_end(local,res,es)) by {reveal(svc::response_path);}
    assert(res(memory(local,Process::SecondClient,es,5)).is_none());
}
proof fn normal_response(sel:Select,b:Fork)
    ensures ({
        let local=sr2::reader(b,Set::empty(),sel);let res=|s:Reader|s.returned;
        svc::response_path(local,res,checkpoint_end(b),delayed_slots(),sr2::exchange_states(b,true),sr2::completed_actions(b),
            sel(sr2::report(b,Replica::R1),sr2::report(b,Replica::R2)))
    }),
{
    hide(memory);hide(crate::protocol::accepted);hide(delivery::trace);hide(sr2::read_update);
    hide(sr2::exchange_states);hide(checkpoint_end);hide(sr2::reader);
    let local=sr2::reader(b,Set::empty(),sel);let res=|s:Reader|s.returned;
    let a=sr2::completed_actions(b);let s=sr2::exchange_states(b,true);let es=observations(s,a);
    sr2::ordinary_quorum_can_return(b,Set::empty(),sel);
    assert forall|i:nat| i<es.len() implies res(#[trigger] memory(local,Process::SecondClient,es,i)).is_none() by {
        sr2::exchange_tracks_private_memory(b,Set::empty(),sel,true,Process::SecondClient,i);
    }
    assert forall|i:int| 0<=i<a.len() implies crate::confirmation::fresh_send(#[trigger] a[i],delayed_slots()) by {prefix_index(i);}
    sr2::exchange_tracks_private_memory(b,Set::empty(),sel,true,Process::SecondClient,0);reveal_with_fuel(memory,1);
}
proof fn normal_edge_omits_receipt(b:Fork,i:nat)
    requires i<9,
    ensures ({
        let s=sr2::exchange_states(b,true);let a=sr2::completed_actions(b);
        !call::receipt(origin(b.branch))(call::prefix(s,a,i),a[i as int],call::prefix(s,a,i+1))
    }),
{
    hide(sr2::exchange_states);let s=sr2::exchange_states(b,true);let a=sr2::completed_actions(b);
    sr2::only_initial_sr2_requests_are_sent(b,true);
    assert(s.len()==10) by {reveal(sr2::exchange_states);}
    assert(call::prefix(s,a,i).nets.last()==s[i as int]);prefix_index(i as int);
}
pub proof fn already_g_can_be_read_normally(sel:Select,b:Fork)
    requires b.notice==Notice::G,
    ensures ({
        let local=sr2::reader(b,Set::empty(),sel);let res=|s:Reader|s.returned;
        let r=nb::ordinary(call::step(local,res,delayed_slots()),call::receipt(origin(b.branch)));
        pre_sr1_g(b,weak_assignment(b,true).ops) && nb::possible(r,call::posted(local,res),call::launch(checkpoint_end(b)))
    }),
{
    hide(call::step);hide(sr2::reader);hide(call::receipt);hide(call::posted);
    hide(svc::response_path);hide(call::prefix);hide(sr2::exchange_states);
    let local=sr2::reader(b,Set::empty(),sel);let res=|s:Reader|s.returned;let net=checkpoint_end(b);
    let a=sr2::completed_actions(b);let s=sr2::exchange_states(b,true);
    let ids=delayed_slots();let v=sel(sr2::report(b,Replica::R1),sr2::report(b,Replica::R2));
    normal_response(sel,b);weak_assignment_at_delivery(b,true);
    call::lift_response(local,res,net,ids,s,a,v);
    let t=call::history(s,a);let full=call::step(local,res,ids);
    let r=nb::ordinary(full,call::receipt(origin(b.branch)));
    assert forall|i:int| 0<=i<a.len() implies r(t.states[i],#[trigger] a[i],t.states[i+1]) by {
        assert(full(t.states[i],a[i],t.states[i+1]));normal_edge_omits_receipt(b,i as nat);
    }
    nb::from_path(r,call::posted(local,res),t,0);
}

}
