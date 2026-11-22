// Ordinary response capability of a pending call in the actual message
// protocol. History is an external monitor, invisible to the local callbacks.
use vstd::prelude::*;
use crate::Replica;
use crate::attribution as source;
use crate::checkpoint::*;
use crate::confirmation::finite_fair_service;
use crate::delivery::*;
use crate::progress::{Execution,actions_before,states_through,delivery_fair,process_fair,eventually_responds};
use crate::promotion_wait as wait;
use crate::protocol::*;
use crate::read_call::{self as call,Program,Log,Net,Event};
use crate::read_nonblocking as nb;
use crate::service as svc;
use crate::service_obstruction::{original_reads,suffix_protocol};
use crate::survivors::{after_crash,sr2_result};
verus! {

pub open spec fn fork_conflict<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>) -> bool {
    exists|a:Seq<Event>,v:int| #[trigger] svc::incompatible_completions(n,m,first,res,a,v)
}

// Obtain a real C2 path with every R3 status for this recipient still held.
pub proof fn without_receipt<S>(local:Program<S>,res:spec_fn(S)->Option<int>,net:Net,ids:Set<nat>,owner:Replica)
    -> (l:Log)
    requires nb::possible(nb::ordinary(call::step(local,res,ids),call::receipt(owner)),call::posted(local,res),call::launch(net)),
    ensures svc::response_path(local,res,net,ids,l.nets,l.actions,sr2_result(local,res,call::obs(l)).unwrap()),
        call::avoids(l,owner),
{
    let full=call::step(local,res,ids);let plain=nb::ordinary(full,call::receipt(owner));
    let done=call::posted(local,res);let x=call::launch(net);
    assert(!done(x)) by {assert(live_pair().contains(Replica::R1));}
    let t=nb::to_path(plain,done,x,choose|k:nat| #[trigger] nb::within(plain,done,x,k));
    assert forall|i:int| 0<=i<t.actions.len() implies full(t.states[i],#[trigger] t.actions[i],t.states[i+1])
        by {assert(plain(t.states[i],t.actions[i],t.states[i+1]));}
    call::real_response(local,res,net,ids,t);
    call::no_receipt_in_log(local,res,net,ids,owner,t,t.actions.len());
    t.states.last()
}

pub(crate) proof fn avoids_issued(net:Net,l:Log,id:nat,r:Replica)
    requires call::avoids(l,r),trace(|x,w|cell(x,w),l.nets,l.actions),
        net.pending.contains_key(id),notice_to(net.pending[id],at(r)),
    ensures !svc::consumed_issue(net,id,l.nets,l.actions),
{
    if svc::consumed_issue(net,id,l.nets,l.actions) {
        let i=choose|i:int| 0<=i<l.actions.len() && #[trigger] l.actions[i]==Action::Deliver(id)
            && call::obs(l)[i].incoming==Some(net.pending[id]);
        assert(enabled(l.nets[i],l.actions[i]));assert(l.nets[i].pending[id]==net.pending[id]);
    }
}

pub(crate) proof fn fork_on_held_log<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Log)
    requires original_reads(n,m,first),call::avoids(l,Replica::R2),
        svc::response_path(suffix_protocol(m,n),res,checkpoint_end(alpha(n)),delayed_slots(),l.nets,l.actions,
            sr2_result(suffix_protocol(m,n),res,call::obs(l)).unwrap()),
    ensures svc::incompatible_completions(n,m,first,res,l.actions,sr2_result(suffix_protocol(m,n),res,call::obs(l)).unwrap()),
{
    hide(svc::incompatible_completions);hide(accepted);hide(completed_quorum_sample);
    let b=alpha(n);let net=checkpoint_end(b);let local=suffix_protocol(m,n);
    let v=sr2_result(local,res,call::obs(l)).unwrap();
    avoids_issued(net,l,2,Replica::R2);
    svc::path_without_notice_preserves_delays(n,local,res,l.nets,l.actions,v);
    svc::held_path_is_an_ordinary_opportunity(n,local,res,l.nets,l.actions,v);
    let t=crate::delivery::replay(|x,w|cell(x,w),crate::confirmation::after_receipt(n),l.actions);
    svc::pair_from_ordinary_path(n,m,first,res,t,l.actions,v);
}
pub proof fn ordinary_opportunity_yields_fork<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires original_reads(n,m,first),
        nb::possible(nb::ordinary(call::step(suffix_protocol(m,n),res,delayed_slots()),call::receipt(Replica::R2)),
            call::posted(suffix_protocol(m,n),res),call::launch(checkpoint_end(alpha(n)))),
    ensures fork_conflict(n,m,first,res),
{
    hide(svc::incompatible_completions);hide(accepted);hide(completed_quorum_sample);
    let b=alpha(n);let net=checkpoint_end(b);let local=suffix_protocol(m,n);let ids=delayed_slots();
    let l=without_receipt(local,res,net,ids,Replica::R2);
    fork_on_held_log(n,m,first,res,l);
}

// This index is in an actual response trace. It identifies a change of
// capability, as well as the old queue item delivered by the crashed sender.
pub open spec fn decisive_receipt<S>(n:Notice,local:Program<S>,res:spec_fn(S)->Option<int>,
    s:Seq<Net>,a:Seq<Event>,i:nat) -> bool {
    let r=call::step(local,res,delayed_slots());let d=call::posted(local,res);
    i<a.len() && a[i as int]==Action::Deliver(2) && observations(s,a)[i as int].incoming==Some(packet_for(alpha(n),2))
      && nb::unlocks(r,d,call::receipt(Replica::R2),call::prefix(s,a,i),a[i as int],call::prefix(s,a,i+1))
}

pub proof fn actual_unlock<S>(n:Notice,local:Program<S>,res:spec_fn(S)->Option<int>,s:Seq<Net>,a:Seq<Event>,v:int)
    -> (i:nat)
    requires svc::response_path(local,res,checkpoint_end(alpha(n)),delayed_slots(),s,a,v),
        !nb::possible(nb::ordinary(call::step(local,res,delayed_slots()),call::receipt(Replica::R2)),
            call::posted(local,res),call::launch(checkpoint_end(alpha(n)))),
    ensures decisive_receipt(n,local,res,s,a,i),
        call::consistent(local,res,checkpoint_end(alpha(n)),delayed_slots(),call::prefix(s,a,i)),
{
    let net=checkpoint_end(alpha(n));let ids=delayed_slots();let r=call::step(local,res,ids);
    let d=call::posted(local,res);let t=call::history(s,a);let who=Replica::R2;
    call::lift_response(local,res,net,ids,s,a,v);
    let i=nb::find_unlock(r,d,call::receipt(who),t,0);
    call::run_prefix(local,res,net,ids,t,i);
    let x=call::prefix(s,a,i);let e=a[i as int];assert(x.nets.last()==s[i as int]);
    assert(call::receipt(who)(x,e,t.states[i as int+1]));
    if let Action::Deliver(id)=e {
        assert(notice_to(s[i as int].pending[id],at(who)));
        source::only_issued_arrival_from_r3(n,s,a,i);
    }
    i
}

pub open spec fn necessarily_unlocked<S>(n:Notice,local:Program<S>,res:spec_fn(S)->Option<int>) -> bool {
    let net=checkpoint_end(alpha(n));let ids=delayed_slots();
    svc::can_respond(local,res,net,ids) && forall|s:Seq<Net>,a:Seq<Event>,v:int|
        #[trigger] svc::response_path(local,res,net,ids,s,a,v) ==> exists|i:nat| #[trigger] decisive_receipt(n,local,res,s,a,i)
}
pub open spec fn trapped<S>(local:Program<S>,res:spec_fn(S)->Option<int>,net:Net,ids:Set<nat>) -> bool {
    let r=call::step(local,res,ids);let d=call::posted(local,res);
    exists|b:nb::Region<Log>| #[trigger] nb::pending_trap(r,d,b) && b(call::launch(net))
}

// Only the accepted original first reads are required. No response, source
// policy, fairness, no-await test, or stock/hybrid simulation is assumed.
pub proof fn original_outcomes<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires original_reads(n,m,first),
    ensures fork_conflict(n,m,first,res) || necessarily_unlocked(n,suffix_protocol(m,n),res)
        || trapped(suffix_protocol(m,n),res,checkpoint_end(alpha(n)),delayed_slots()),
{
    hide(fork_conflict);hide(original_reads);hide(svc::response_path);hide(call::step);hide(call::posted);
    let net=checkpoint_end(alpha(n));let local=suffix_protocol(m,n);let ids=delayed_slots();
    let r=call::step(local,res,ids);let d=call::posted(local,res);let x=call::launch(net);
    if nb::possible(nb::ordinary(r,call::receipt(Replica::R2)),d,x) {
        ordinary_opportunity_yields_fork(n,m,first,res);
    } else if nb::possible(r,d,x) {
        call::exact_service(local,res,net,ids);
        assert forall|s:Seq<Net>,a:Seq<Event>,v:int| #[trigger] svc::response_path(local,res,net,ids,s,a,v)
            implies exists|i:nat| #[trigger] decisive_receipt(n,local,res,s,a,i) by {actual_unlock(n,local,res,s,a,v);}
    } else {
        nb::largest_trap(r,d);let b=nb::hopeless(r,d);assert(b(x));
        assert(nb::pending_trap(r,d,b));
    }
}

// Admission and the stable-slot allocator belong to the workload/transport.
// All reachable invocations with this R3 failure and this driver's live
// quorum are in scope, independent of their data, strong memories or results.
pub open spec fn fresh_call<S>(m:Program<S>,entry:Net,h:Log,ids:Set<nat>) -> bool {
    h.nets[0]==entry && trace(|x,w|cell(x,w),h.nets,h.actions) && accepted(m,call::obs(h))
      && h.actions.len()>0 && h.actions.last()==Action::StartSecondClient && after_crash(h.nets.last())
      && source::allocated_before_read(h.nets,h.actions,ids)
}
pub open spec fn at_entry(net:Net) -> nb::Region<Log> { |l:Log| l==call::launch(net) }
pub open spec fn service_at<S>(m:Program<S>,res:spec_fn(S)->Option<int>,h:Log,ids:Set<nat>) -> bool {
    let local=resume_at(m,call::obs(h));let net=h.nets.last();
    nb::nonblocking(call::step(local,res,ids),call::posted(local,res),at_entry(net))
}
pub open spec fn read_availability<S>(m:Program<S>,res:spec_fn(S)->Option<int>,entry:Net,slots:spec_fn(Log)->Set<nat>) -> bool {
    forall|h:Log| #[trigger] fresh_call(m,entry,h,slots(h)) ==> service_at(m,res,h,slots(h))
}
// The selected audit proves the opaque R3 carrier certifies real copying.
// The semantic no-await law covers every admitted pending prefix, even if
// other implementations have different, mandatory, ordinary service steps.
pub open spec fn no_confirm_wait_at<S>(m:Program<S>,res:spec_fn(S)->Option<int>,h:Log,ids:Set<nat>,owner:Replica) -> bool {
    let local=resume_at(m,call::obs(h));let net=h.nets.last();let r=call::step(local,res,ids);
    nb::no_unlock(r,call::posted(local,res),call::receipt(owner),|l:Log|call::consistent(local,res,net,ids,l))
}
pub open spec fn no_confirm_wait<S>(m:Program<S>,res:spec_fn(S)->Option<int>,entry:Net,slots:spec_fn(Log)->Set<nat>) -> bool {
    forall|h:Log,owner:Replica| fresh_call(m,entry,h,slots(h)) && source::arrival_certifies_copy(m,owner)
        ==> #[trigger] no_confirm_wait_at(m,res,h,slots(h),owner)
}
pub open spec fn past(b:Fork) -> Log { Log{nets:checkpoint_states(b),actions:actions_to_crash(b)} }

// This uses only an actual responding path and its consistent prefixes.
// No change to an alpha history or to a beta private state is needed.
pub proof fn no_wait_excludes_unlock<S>(n:Notice,m:Program<S>,res:spec_fn(S)->Option<int>)
    requires no_confirm_wait_at(m,res,past(alpha(n)),delayed_slots(),Replica::R2),
    ensures !necessarily_unlocked(n,suffix_protocol(m,n),res),
{
    hide(svc::response_path);hide(call::step);hide(call::posted);
    let b=alpha(n);let local=suffix_protocol(m,n);let ids=delayed_slots();let net=checkpoint_end(b);
    prefix_transport_is_enabled(b);
    if necessarily_unlocked(n,local,res) {
        let (s,a,v)=choose|s:Seq<Net>,a:Seq<Event>,v:int| #[trigger] svc::response_path(local,res,net,ids,s,a,v);
        let i=choose|i:nat| #[trigger] decisive_receipt(n,local,res,s,a,i);
        let t=call::history(s,a);call::lift_response(local,res,net,ids,s,a,v);call::run_prefix(local,res,net,ids,t,i);
        assert(call::consistent(local,res,net,ids,call::prefix(s,a,i)));
        assert(nb::unlocks(call::step(local,res,ids),call::posted(local,res),call::receipt(Replica::R2),
            call::prefix(s,a,i),a[i as int],call::prefix(s,a,i+1)));
    }
}

// Tie the consumer-side capacity change back to the earlier source-checked
// AwaitWeak test. Source provenance is needed only for this interpretation.
pub proof fn decisive_signal_attests_a_weak_wait<S>(n:Notice,m:Program<S>,res:spec_fn(S)->Option<int>)
    requires accepted(m,checkpoint_observations(alpha(n))),source::arrival_certifies_copy(m,Replica::R2),
        necessarily_unlocked(n,suffix_protocol(m,n),res),
    ensures source::waits_for_replication(m,checkpoint_states(alpha(n)),actions_to_crash(alpha(n)),1,Replica::R2,2,res,delayed_slots()),
        !source::no_causal_await(m,res),
{
    hide(svc::response_path);hide(accepted);hide(nb::unlocks);hide(source::arrival_certifies_copy);
    let b=alpha(n);let net=checkpoint_end(b);let local=suffix_protocol(m,n);let ids=delayed_slots();
    source::actual_status_issuance(n);prefix_transport_is_enabled(b);
    assert forall|s:Seq<Net>,a:Seq<Event>,v:int| #[trigger] svc::response_path(local,res,net,ids,s,a,v)
        implies svc::consumed_issue(net,2,s,a) by {
        let i=choose|i:nat| #[trigger] decisive_receipt(n,local,res,s,a,i);
        assert(a[i as int]==Action::Deliver(2) && observations(s,a)[i as int].incoming==Some(net.pending[2]));
    }
    assert(svc::receipt_prerequisite(local,res,net,ids,2));
}
pub proof fn original_pair_under_contract<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    slots:spec_fn(Log)->Set<nat>)
    requires original_reads(n,m,first),slots(past(alpha(n)))==delayed_slots(),
        source::arrival_certifies_copy(m,Replica::R2),
        read_availability(m,res,after_local_rmws(),slots),no_confirm_wait(m,res,after_local_rmws(),slots),
    ensures fork_conflict(n,m,first,res),
{
    hide(fork_conflict);hide(svc::response_path);hide(accepted);hide(call::step);hide(call::posted);
    let b=alpha(n);let h=past(b);let local=suffix_protocol(m,n);let ids=delayed_slots();let net=checkpoint_end(b);
    prefix_transport_is_enabled(b);source::actual_status_issuance(n);
    assert(fresh_call(m,after_local_rmws(),h,slots(h)));
    assert(service_at(m,res,h,ids));assert(no_confirm_wait_at(m,res,h,ids,Replica::R2));
    let r=call::step(local,res,ids);let d=call::posted(local,res);let x=call::launch(net);
    nb::nonblocking_iff(r,d,at_entry(net));assert(at_entry(net)(x));
    original_outcomes(n,m,first,res);no_wait_excludes_unlock(n,m,res);
    if trapped(local,res,net,ids) {
        let b=choose|b:nb::Region<Log>| #[trigger] nb::pending_trap(r,d,b) && b(x);
        nb::trap_excludes_service(r,d,b,x);
    }
}

// Necessary consequence of manuscript H for this four-operation workload.
// Each individual completed read must have its own legal history. This
// neither couples the histories nor requires a pending read to respond.
pub open spec fn admits_strong_history<S>(b:Fork,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>) -> bool {
    forall|a:Seq<Event>,v:int| #[trigger] crate::confirmation::completed_at(b,m,res,a,v) &&
        svc::first_return_at(b,m,res,a) &&
        (forall|i:int| 0<=i<a.len() ==> crate::confirmation::fresh_send(#[trigger] a[i],delayed_slots()))
        ==> exists|ops:Seq<crate::Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,first_result(m,first,b),v)
}
pub(crate) proof fn safe_branches_exclude_conflict<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires admits_strong_history(alpha(n),m,first,res),admits_strong_history(beta(n),m,first,res),
    ensures !fork_conflict(n,m,first,res),
{
    hide(crate::legal);hide(crate::confirmation::completed_at);hide(svc::first_return_at);hide(first_result);
    if fork_conflict(n,m,first,res) {
        let (a,v)=choose|a:Seq<Event>,v:int| #[trigger] svc::incompatible_completions(n,m,first,res,a,v);
        assert forall|i:int| 0<=i<a.len() implies crate::confirmation::fresh_send(#[trigger] a[i],delayed_slots()) by {
            assert(crate::survivors::keeps_delayed_slots(a[i],delayed_slots()));
            if let Action::Send(id,p)=a[i] {
                if delayed_slots().contains(id) {assert(crate::scheduling::untouched_slot(a[i],id));}
            }
        }
        let (ao,ax)=choose|ops:Seq<crate::Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,first_result(m,first,alpha(n)),v);
        let (bo,bx)=choose|ops:Seq<crate::Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,first_result(m,first,beta(n)),v);
        assert(crate::legal(ao,ax,5,v) && crate::legal(bo,bx,2,v));
    }
}

// Contrapositive on the two actual workloads. H and the source-checked
// forward no-await rule force loss of ALL hybrid service, even on suffixes
// allowed to receive weak traffic. No positive hybrid progress premise.
pub proof fn safety_and_no_await_force_loss<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires original_reads(n,m,first),admits_strong_history(alpha(n),m,first,res),admits_strong_history(beta(n),m,first,res),
        source::arrival_certifies_copy(m,Replica::R2),source::no_causal_await(m,res),
    ensures ({
        let local=suffix_protocol(m,n);let ids=delayed_slots();let net=checkpoint_end(alpha(n));
        let r=call::step(local,res,ids);let d=call::posted(local,res);let dead=nb::hopeless(r,d);
        nb::pending_trap(r,d,dead) && dead(call::launch(net)) && !svc::can_respond(local,res,net,ids)
    }),
{
    hide(svc::can_respond);hide(original_reads);hide(admits_strong_history);hide(fork_conflict);
    let local=suffix_protocol(m,n);let net=checkpoint_end(alpha(n));let ids=delayed_slots();
    let r=call::step(local,res,ids);let d=call::posted(local,res);let x=call::launch(net);
    safe_branches_exclude_conflict(n,m,first,res);original_outcomes(n,m,first,res);
    if necessarily_unlocked(n,local,res) {
        assert(accepted(m,checkpoint_observations(alpha(n)))) by {reveal(original_reads);}
        decisive_signal_attests_a_weak_wait(n,m,res);
    }
    let b=choose|b:nb::Region<Log>| #[trigger] nb::pending_trap(r,d,b) && b(x);
    nb::trap_excludes_service(r,d,b,x);nb::largest_trap(r,d);call::exact_service(local,res,net,ids);
}
pub proof fn no_return_on_admitted_run<S>(net:Net,local:Program<S>,res:spec_fn(S)->Option<int>,e:Execution<int,Wire>)
    requires !svc::can_respond(local,res,net,delayed_slots()),crate::confirmation::admissible_service(net,local,res,e),
    ensures forall|k:nat| sr2_result(local,res,observations(states_through(e,k),#[trigger] actions_before(e,k))).is_none(),
{
    assert forall|j:nat| sr2_result(local,res,observations(states_through(e,j),#[trigger] actions_before(e,j))).is_none() by {
        if sr2_result(local,res,observations(states_through(e,j),actions_before(e,j))).is_some() {
            let (k,v)=crate::confirmation::finite_observed_service(net,local,res,e,j);
            assert(svc::response_path(local,res,net,delayed_slots(),states_through(e,k),actions_before(e,k),v));
        }
    }
}

// Fair majority availability is one sufficient justification. Both the
// fair execution and its applicability to the actual hybrid client remain
// independent of the no-await rule. No fairness of an infinite hold.
pub proof fn from_fair_hybrid_run<S>(m:Program<S>,res:spec_fn(S)->Option<int>,h:Log,
    e:Execution<int,Wire>,runnable:spec_fn(Net,Process)->bool)
    requires after_crash(h.nets.last()),crate::confirmation::admissible_service(h.nets.last(),resume_at(m,call::obs(h)),res,e),
        delivery_fair(e),process_fair(e,runnable),
        eventually_responds(e,runnable,|s,a|sr2_result(resume_at(m,call::obs(h)),res,observations(s,a)).is_some()),
    ensures service_at(m,res,h,delayed_slots()),
{
    let local=resume_at(m,call::obs(h));let net=h.nets.last();let ids=delayed_slots();
    let (k,v)=finite_fair_service(net,local,res,e,runnable);
    assert(svc::response_path(local,res,net,ids,states_through(e,k),actions_before(e,k),v));
    assert(svc::can_respond(local,res,net,ids));
    call::exact_service(local,res,net,ids);nb::nonblocking_iff(call::step(local,res,ids),call::posted(local,res),at_entry(net));
}

}
