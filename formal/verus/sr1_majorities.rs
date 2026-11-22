// Compose the two SR1 majority prefixes without granting the idle minority
// an enabled reply. Its permission comes from its own run as a responder.
use vstd::prelude::*;
use crate::{Branch,Replica,checkpoint::*,delivery::*,protocol::*};
use crate::read_call::{Event,Net,Program};
use crate::service_obstruction::original_reads;
use crate::stock_first::sampled_in_interval;

verus! {

pub open spec fn missing(b:Fork) -> Replica {
    if b.branch==Branch::Alpha {Replica::R1} else {Replica::R2}
}
pub open spec fn other(b:Fork) -> Fork {
    if b.branch==Branch::Alpha {beta(b.notice)} else {alpha(b.notice)}
}
pub open spec fn receive_index(b:Fork) -> nat {if b.branch==Branch::Alpha {5} else {6}}
// The omitted actions are the failed replica's receive and its reply send.
// The request addressed to it was actually issued and stays pending.
pub open spec fn kept_index(b:Fork,j:nat) -> nat {
    let d=receive_index(b);
    if j<d {j} else if j+1<d+3 {j+1} else {j+2}
}
pub(crate) open spec fn count(b:Fork,k:nat) -> nat {
    let d=receive_index(b);
    if k<=d {k} else if k<=d+3 {(k-1) as nat} else {(k-2) as nat}
}
pub open spec fn actions(b:Fork) -> Seq<Event> {
    Seq::new(13,|i:int|actions_to_crash(b)[kept_index(b,i as nat) as int])
}
pub open spec fn net(b:Fork,j:nat) -> Net {
    let k=kept_index(b,j);let n=state_after(b,k);
    let req:nat=if b.branch==Branch::Alpha {3} else {4};let reply=req+3;
    let packets=n.pending.remove(reply);
    Net{unavailable:Some(missing(b)),pending:if k>receive_index(b) {
        packets.insert(req,packet_for(b,req))
    } else {packets},..n}
}
pub open spec fn states(b:Fork) -> Seq<Net> { Seq::new(14,|i:int|net(b,i as nat)) }
pub open spec fn obs(b:Fork) -> Seq<ProcessStep<int,Wire>> {observations(states(b),actions(b))}

pub proof fn majority_transport(b:Fork)
    ensures trace(|v,w|cell(v,w),states(b),actions(b)),
        net(b,0)==(Net{unavailable:Some(missing(b)),..after_local_rmws()}),
        !net(b,13).r3_crashed && net(b,13).first_stopped,
        net(b,13).pending.get(2)==Some(packet_for(b,2)) && live(net(b,13),packet_for(b,2).to),
        net(b,13).pending.get(if b.branch==Branch::Alpha {3nat} else {4nat})
            ==Some(packet_for(b,if b.branch==Branch::Alpha {3nat} else {4nat})),
        forall|j:nat| j<13 ==> #[trigger] obs(b)[j as int]==checkpoint_observations(b)[kept_index(b,j) as int],
{
    prefix_transport_is_enabled(b);
    assert(net(b,0).pending =~= after_local_rmws().pending);
    assert forall|i:int| 0<=i<13 implies {
        let a=#[trigger] actions(b)[i];let s=states(b)[i];let u=states(b)[i+1];
        enabled(s,a) && u==advance(|v,w|cell(v,w),s,a) && obs(b)[i]==checkpoint_observations(b)[kept_index(b,i as nat) as int]
    } by {
        prefix_index(i);let s=states(b)[i];let u=states(b)[i+1];let a=actions(b)[i];
        assert(u.pending =~= advance(|v,w|cell(v,w),s,a).pending);
        assert(u.locals =~= advance(|v,w|cell(v,w),s,a).locals);
    }
}

pub(crate) proof fn local_at<S>(m:Program<S>,b:Fork,p:Process,k:nat)
    requires k<=15,p!=at(missing(b)),
    ensures memory(m,p,checkpoint_observations(b),k)==memory(m,p,obs(b),count(b,k)),
    decreases k,
{
    if k>0 {
        let j=(k-1) as nat;local_at(m,b,p,j);prefix_index(j as int);
        let es=checkpoint_observations(b);
        if j==receive_index(b) || j==receive_index(b)+3 {assert(es[j as int].actor==at(missing(b)));}
        else {
            majority_transport(b);
            assert(kept_index(b,count(b,j))==j);
            assert(obs(b)[count(b,j) as int]==es[j as int]);
        }
    }
}

// A finite direct-service premise for the crash reference. It includes
// every earlier guard, SR1's real return, and the shared-state quorum
// sampling rule. No first-read value is specified.
pub open spec fn served<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork) -> bool {
    let c=Process::FirstClient;let es=obs(b);
    let end=if (m.done)(memory(m,c,es,11)) {11nat} else {12nat};
    accepted(m,es) && (forall|k:nat| k<=10 ==> !(m.done)(#[trigger] memory(m,c,es,k)))
        && sampled_in_interval(crate::first_quorum(b.branch),states(b),actions(b),2,end,m,first)
}
// The old trace interface runs a callback at physical failure. Only the
// local R3 state at the end of this prefix is relevant. C2's startup reads
// its own initial memory; it receives no result from C1.
pub open spec fn crash_input(v:int) -> ProcessStep<int,Wire> {
    ProcessStep{actor:at(Replica::R3),action:Action::CrashR3,incoming:None,own_local:Some(v)}
}
pub open spec fn lifecycle_at<S>(m:Program<S>,b:Fork) -> bool {
    (m.accept)(memory(m,at(Replica::R3),obs(b),13),crash_input(first_value(b))) &&
        (m.accept)((m.initial)(Process::SecondClient),crate::read_issue::local_event(Action::StartSecondClient))
}

proof fn own_guard<S>(m:Program<S>,b:Fork,k:nat)
    requires accepted(m,obs(b)),k<15,checkpoint_observations(b)[k as int].actor!=at(missing(b)),
    ensures ({
        let es=checkpoint_observations(b);let e=es[k as int]; (m.accept)(memory(m,e.actor,es,k),e)
    }),
{
    let es=checkpoint_observations(b);let e=es[k as int];prefix_index(k as int);
    local_at(m,b,e.actor,k);majority_transport(b);
    let j=count(b,k);assert(j<13 && kept_index(b,j)==k);
    assert(obs(b)[j as int]==e);
    assert((m.accept)(memory(m,e.actor,obs(b),j),obs(b)[j as int]));
}
proof fn accepted_on_all_three<S>(m:Program<S>,b:Fork)
    requires accepted(m,obs(b)),accepted(m,obs(other(b))),lifecycle_at(m,b),
    ensures accepted(m,checkpoint_observations(b)),
{
    let es=checkpoint_observations(b);let d=other(b);
    assert forall|i:int| 0<=i<es.len() implies {
        let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)
    } by {
        let e=es[i];prefix_index(i);
        if i<15 {
            if e.actor!=at(missing(b)) {own_guard(m,b,i as nat);}
            else {
                assert(e==checkpoint_observations(d)[i]);
                own_guard(m,d,i as nat);
                arbitrary_survivor_memory_agrees(b.notice,m,e.actor,i as nat);
            }
        } else if i==15 {
            assert(e==crash_input(first_value(b)));local_at(m,b,at(Replica::R3),15);
        }
        else {
            assert(e==crate::read_issue::local_event(Action::StartSecondClient));
            assert forall|j:int| 0<=j<16 implies (#[trigger] es[j]).actor!=Process::SecondClient by {prefix_index(j);}
            memory_during_quiescence(m,es,Process::SecondClient,0,16);
        }
    }
}
proof fn first_sample<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork)
    requires served(m,first,b),
    ensures completed_quorum_sample(m,first,b),first_result(m,first,b)==first_value(b),
{
    let c=Process::FirstClient;let es=obs(b);let q=crate::first_quorum(b.branch);
    local_at(m,b,c,13);local_at(m,b,c,14);
    let j=if (m.done)(memory(m,c,es,11)) {11nat} else {12nat};
    let end=first_return_len(m,b);assert(end==j+2);
    assert forall|k:nat| k<=12 implies !(m.done)(#[trigger] first_client_at(m,b,k)) by {
        local_at(m,b,c,k);assert(!(m.done)(memory(m,c,es,count(b,k))));
    }
    let (r,i)=choose|r:Replica,i:int| q.contains(r) && 2<=i<=j && #[trigger] (states(b)[i].locals)(r)==first(memory(m,c,es,j));
    assert((states(b)[i].locals)(r)==first_value(b));
    assert(q.contains(crate::origin(b.branch)) && during_sr1(b,2,crate::origin(b.branch))==first_value(b));
}

// Conversely, an accepted original direct prefix supplies its own
// crash-majority reference. This compares finite cuts with a single failure
// in each execution, without recovering a crashed replica.
pub proof fn reference_from_original<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork)
    requires accepted(m,checkpoint_observations(b)),completed_quorum_sample(m,first,b),
    ensures served(m,first,b),lifecycle_at(m,b),
{
    let es=checkpoint_observations(b);let ref_es=obs(b);let c=Process::FirstClient;
    majority_transport(b);stable_responder_cells_fix_first_sample(m,first,b);
    assert forall|i:int| 0<=i<ref_es.len() implies {
        let e=#[trigger] ref_es[i];(m.accept)(memory(m,e.actor,ref_es,i as nat),e)
    } by {
        let j=kept_index(b,i as nat);let e=ref_es[i];prefix_index(i);
        assert(e==es[j as int] && e.actor!=at(missing(b)) && count(b,j)==i);
        local_at(m,b,e.actor,j);assert((m.accept)(memory(m,e.actor,es,j),e));
    }
    assert forall|k:nat| k<=10 implies !(m.done)(#[trigger] memory(m,c,ref_es,k)) by {
        let j=kept_index(b,k);local_at(m,b,c,j);assert(count(b,j)==k);
        assert(!(m.done)(first_client_at(m,b,j)));
    }
    local_at(m,b,c,13);local_at(m,b,c,14);
    let end=if (m.done)(memory(m,c,ref_es,11)) {11nat} else {12nat};
    assert(first(memory(m,c,ref_es,end))==first_result(m,first,b));
    assert(crate::first_quorum(b.branch).contains(crate::origin(b.branch)));
    assert((states(b)[2].locals)(crate::origin(b.branch))==first_value(b));
    local_at(m,b,at(Replica::R3),15);
    assert(es[15]==crash_input(first_value(b)));
    assert((m.accept)(memory(m,es[15].actor,es,15),es[15]));
    assert forall|j:int| 0<=j<16 implies (#[trigger] es[j]).actor!=Process::SecondClient by {prefix_index(j);}
    memory_during_quiescence(m,es,Process::SecondClient,0,16);
    assert((m.accept)(memory(m,es[16].actor,es,16),es[16]));
}

pub proof fn direct_readers_supply_references(b:Fork,gates:Set<Replica>,sel:crate::sr2::Select)
    ensures ({
        let m=crate::sr2::read_protocol(gates,b.notice,sel);
        served(m,|s:crate::sr2::Reader|s.prior.reply.unwrap(),b) && lifecycle_at(m,b)
    }),
{
    let m=crate::sr2::read_protocol(gates,b.notice,sel);
    crate::sr2::fresh_reader_resumes_actual_sr1_state(b,gates,sel);crate::sr2::combined_reader_supplies_sr1_sample(b,gates,sel);
    reference_from_original(m,|s:crate::sr2::Reader|s.prior.reply.unwrap(),b);
}

pub proof fn recover_both_prefixes<S>(m:Program<S>,first:spec_fn(S)->int,n:Notice)
    requires served(m,first,alpha(n)),served(m,first,beta(n)),lifecycle_at(m,alpha(n)),lifecycle_at(m,beta(n)),
    ensures original_reads(n,m,first),
{
    accepted_on_all_three(m,alpha(n));accepted_on_all_three(m,beta(n));
    first_sample(m,first,alpha(n));first_sample(m,first,beta(n));
}

pub proof fn hot_from_majority_service<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    n:Notice,runnable:crate::fair_read::Runnable)
    requires served(m,first,alpha(n)),served(m,first,beta(n)),lifecycle_at(m,alpha(n)),lifecycle_at(m,beta(n)),crate::read_issue::can_issue(m,res),
        crate::fair_read::fair_majority_availability(m,res,crate::early_crash::entry(m),runnable),
        crate::fair_read::pending_turns(m,res,crate::early_crash::entry(m),runnable),
    ensures exists|a:Seq<Event>,v:int| #[trigger] crate::service::incompatible_completions(n,m,first,res,a,v)
        && a.len()>=2 && a[0]==crate::read_issue::send_first() && a[1]==crate::read_issue::send_second(),
{
    recover_both_prefixes(m,first,n);
    crate::fair_read::fair_progress_offers_service(m,res,crate::early_crash::entry(m),runnable);
    crate::early_crash::original_pair_from_hybrid_service(n,m,first,res);
}

}
