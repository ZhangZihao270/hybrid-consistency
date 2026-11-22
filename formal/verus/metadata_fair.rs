use vstd::prelude::*;
use crate::{Replica, origin};
use crate::checkpoint::*;
use crate::confirmation::{admissible_service, fresh_send};
use crate::delivery::*;
use crate::metadata_pair::*;
use crate::metadata_reader::{reference_read, reference_reader_after_actual_sr1, starts_sr2};
use crate::mixed_sources::actual_disk_before_sr2;
use crate::progress::*;
use crate::protocol::*;
use crate::quorum_progress::delivery_witness;
use crate::quorum_rpc::Resolver;
use crate::survivors::sr2_result;

verus! {

// After collecting the two ordinary replies, the two weak holders each
// send their actual value before processing the other's payload. The old
// notice is also delivered. Only dead/stopped recipients retain packets.
pub open spec fn background(b: Fork, i: nat) -> Action<Wire> {
    if i < 9 { read_actions(b,BeforeSample::Unchanged)[i as int] }
    else if i == 9 { weak_offer(15) }
    else if i == 10 { send(16,Path::Weak,at(Replica::R2),at(Replica::R1),Wire::Copy(5)) }
    else if i == 11 { Action::Deliver(15) }
    else if i == 12 { Action::Deliver(16) }
    else if i == 13 { Action::Deliver(2) }
    else { Action::Strong(if i%3==0 { at(Replica::R1) } else if i%3==1 { at(Replica::R2) } else { Process::SecondClient }) }
}

pub open spec fn network(b: Fork, k: nat) -> Network<int,Wire> {
    if k <= 9 { read_net(b,BeforeSample::Unchanged,k) }
    else {
        let s=read_net(b,BeforeSample::Unchanged,9);
        let p=if k>=14 { s.pending.remove(2) } else { s.pending };
        let p=if 10<=k<12 { p.insert(15,background(b,9)->Send_1) } else { p };
        let p=if 11<=k<13 { p.insert(16,background(b,10)->Send_1) } else { p };
        Network { pending: p, locals: |r| if r==Replica::R1 && k>=13 { 5 }
            else if r==Replica::R2 && k>=12 { 2 } else { (s.locals)(r) }, ..s }
    }
}

pub open spec fn run(b: Fork) -> Execution<int,Wire> {
    Execution { state: |k| network(b,k), action: |k| background(b,k) }
}

pub open spec fn private(b: Fork, rho: Resolver, p: Process, k: nat) -> Local {
    if k<=9 { during(b,rho,Set::empty(),BeforeSample::Unchanged,p,k) }
    else {
        let s=during(b,rho,Set::empty(),BeforeSample::Unchanged,p,9);
        let copy=if k>=12 && p==at(Replica::R2) { Some(2) }
            else if k>=13 && p==at(Replica::R1) { Some(5) } else { s.first.weak_copy };
        Local { first: Control { weak_copy: copy, learned: if k>=14 && p==at(origin(b.branch)) { Some(b.notice) }
            else { s.first.learned }, ..s.first }, ..s }
    }
}

pub(crate) proof fn state_at(b: Fork, rho: Resolver, p: Process, k: nat, end: nat)
    requires k<=end, rho(first_rows(b,13))==Some(first_value(b)),
    ensures ({
        let e=run(b); let es=observations(states_through(e,end),actions_before(e,end));
        memory(starts_sr2(b,rho,Set::empty()),p,es,k)==private(b,rho,p,k)
    }),
    decreases k,
{
    if k==0 { real_first_with(rho,rho,b,Set::empty()); }
    else {
        let j=(k-1) as nat; state_at(b,rho,p,j,end);
        if j<14 { prefix_index(j as int); }
        actual_disk_before_sr2(b,17,Replica::R1); actual_disk_before_sr2(b,17,Replica::R2);
    }
}

proof fn allowed_action(b: Fork,rho: Resolver,i: nat)
    ensures ({
        let ev=process_step(network(b,i),background(b,i)); permits(private(b,rho,ev.actor,i),ev)
    }),
{
    let ev=process_step(network(b,i),background(b,i)); let none=Set::empty();
    if i<9 {
        let work=BeforeSample::Unchanged; let a=read_actions(b,work); let t=read_states(b,work);
        let es=observations(t,a); let m=resumed(b,rho,none);
        sampled_exchange(b,rho,none,work);
        assert(es[i as int] == ev);
        read_memory(b,rho,none,work,ev.actor,i);
        assert((m.accept)(memory(m,ev.actor,es,i),ev));
    } else if i<14 { prefix_index(i as int); }
}

pub(crate) proof fn accepted_background(b: Fork, rho: Resolver)
    requires rho(first_rows(b,13))==Some(first_value(b)),
    ensures admissible_service(checkpoint_end(b),starts_sr2(b,rho,Set::empty()),|s: Local|s.returned,run(b)),
{
    let e=run(b); let pre=starts_sr2(b,rho,Set::empty()); let c=Process::SecondClient;
    assert((e.state)(0).locals =~= checkpoint_end(b).locals);
    assert forall|k: nat| {
        let a=#[trigger] (e.action)(k); let s=(e.state)(k);
        enabled(s,a) && (e.state)(k+1)==advance(|v,w| cell(v,w),s,a) && fresh_send(a,delayed_slots())
    } by {
        if k<14 { prefix_index(k as int); }
        let next=advance(|v,w| cell(v,w),(e.state)(k),(e.action)(k));
        assert(next.locals =~= (e.state)(k+1).locals); assert(next.pending =~= (e.state)(k+1).pending);
    }
    assert forall|k: nat| {
        let a=#[trigger] actions_before(e,k); let es=observations(states_through(e,k),a);
        accepted(pre,es) && only_request_sends(a,c,live_pair()) && fanout_before_receiving(es,c)
            && (sr2_result(pre,|s: Local|s.returned,es).is_some() ==> invocation_only(a,c,live_pair()))
    } by {
        let a=actions_before(e,k); let es=observations(states_through(e,k),a);
        assert forall|i: int| 0<=i<k implies {
            let ev=#[trigger] es[i]; (pre.accept)(memory(pre,ev.actor,es,i as nat),ev)
        } by {
            state_at(b,rho,es[i].actor,i as nat,k);
            allowed_action(b,rho,i as nat);
            assert(es[i]==process_step(network(b,i as nat),background(b,i as nat)));
        }
        assert forall|i: int| 0<=i<k implies match #[trigger] a[i] {
            Action::Send(_,p) if p.from==c => invocation_packet(p) && live_pair().contains(p.to->At_0)
                && (forall|j: int| 0<=j<i ==> !client_sends_to(#[trigger] a[j],c,p.to->At_0)), _=>true,
        } by { if i<14 { prefix_index(i); } }
        assert forall|i: int,j: int| 0<=j<i<es.len() implies match (#[trigger] es[i]).action {
            Action::Send(_,p) if p.from==c => (#[trigger] es[j]).actor!=c || es[j].incoming.is_none(), _=>true,
        } by { if i<14 { prefix_index(i); } }
        state_at(b,rho,c,k,k);
        if k>=2 { assert(client_sends_to(a[0],c,Replica::R1) && client_sends_to(a[1],c,Replica::R2)); }
    }
}

proof fn fair_background(b: Fork)
    ensures delivery_fair(run(b)), process_fair(run(b),|s,p| live(s,p)),
{
    let e=run(b);
    assert forall|i: nat,id: nat| #[trigger] (e.state)(i).pending.contains_key(id) implies
        exists|j: nat| j>=i && (#[trigger] (e.action)(j)==Action::Deliver(id) || !live((e.state)(j),(e.state)(i).pending[id].to)) by {
        let j=if !live((e.state)(i),(e.state)(i).pending[id].to) { i }
            else if id==11 { 2nat } else if id==12 { 3nat } else if id==13 { 6nat } else if id==14 { 7nat }
            else if id==15 { 11nat } else if id==16 { 12nat } else { 13nat };
        if i<14 { prefix_index(i as int); }
        delivery_witness(e,i,id,j);
    }
    let live_here=|s,p| live(s,p);
    assert forall|i: nat,p: Process| #[trigger] continuously_runnable(e,live_here,i,p) implies
        exists|j: nat| j>=i && #[trigger] runs_at(e,j,p) by {
        assert(live_here((e.state)(i),p));
        let delta:nat=if p==at(Replica::R1) {0} else if p==at(Replica::R2) {1} else {2};
        let j=3*(i+14)+delta; assert(j%3==delta); assert(j>=i && runs_at(e,j,p));
    }
}

// A concrete fair continuation with all live data and G-status deliveries,
// checked in *each* actual branch. Both clients run the same read program.
pub proof fn pending_after_all_live_deliveries(b: Fork)
    ensures ({
        let rho=reference_read(Replica::R3); let pre=starts_sr2(b,rho,Set::empty()); let e=run(b);
        admissible_service(checkpoint_end(b),pre,|s: Local| s.returned,e) && delivery_fair(e) && process_fair(e,|s,p|live(s,p))
            && pre_sr1_g(b,weak_assignment(b,true).ops)
            && (forall|k: nat| majority_up(#[trigger] (e.state)(k))
                && sr2_result(pre,|s: Local|s.returned,observations(states_through(e,k),actions_before(e,k))).is_none())
            && (forall|id: nat| #[trigger] (e.state)(14).pending.contains_key(id) ==> !live((e.state)(14),(e.state)(14).pending[id].to))
            && private(b,rho,at(origin(b.branch)),14).first.learned == Some(b.notice)
    }),
{
    hide(admissible_service); hide(delivery_fair); hide(process_fair); hide(checkpoint_observations); hide(memory);
    let rho=reference_read(Replica::R3); let e=run(b); let pre=starts_sr2(b,rho,Set::empty());
    reference_reader_after_actual_sr1(b,Set::empty()); assert(crate::metadata_reader::unanimous(first_rows(b,13)));
    accepted_background(b,rho); fair_background(b);
    actual_disk_before_sr2(b,17,Replica::R1); actual_disk_before_sr2(b,17,Replica::R2);
    let rows=sample_rows(b,BeforeSample::Unchanged);
    assert(rows.contains_key(Replica::R1) && rows[Replica::R1].version==0 && rows[Replica::R1].value==2);
    assert(!crate::metadata_reader::valid_root(rows) && !rows.contains_key(Replica::R3));
    assert(rho(rows).is_none());
    assert forall|k: nat| majority_up(#[trigger] (e.state)(k))
        && sr2_result(pre,|s: Local|s.returned,observations(states_through(e,k),actions_before(e,k))).is_none() by {
        state_at(b,rho,Process::SecondClient,k,k);
    }
}

}
