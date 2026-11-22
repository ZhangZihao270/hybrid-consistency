use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::metadata_pair::*;
use crate::metadata_reader::{single,starts_sr2,compare_after_first,reference_read,unanimous};
use crate::ordered_store::{Stamp,value_at};
use crate::protocol::*;
use crate::quorum_rpc::Resolver;
use crate::service::*;
use crate::confirmation::after_receipt;
use crate::survivors::sr2_result;

verus! {

// This handler owns the ordinary genesis configuration and its local
// applied journal, including the empty journal. A stored snapshot is a
// different source. Reads on the weak overlay still sample the shared cell.
pub open spec fn rebuild(s: Local) -> Stamp {
    Stamp {version:s.applied.len(),value:value_at(s.applied,s.applied.len())}
}
pub open spec fn replay_allowed(s: Local,e: ProcessStep<int,Wire>) -> bool {
    match e.action {
        Action::Local(r,Wire::Copy(v)) => e.actor==at(r) && e.own_local.is_some() && e.own_local!=Some(v) && v==rebuild(s).value,
        _=>permits(s,e),
    }
}
pub open spec fn journal_reader(rho: Resolver) -> LocalProtocol<Local,int,Wire> {
    LocalProtocol {accept: |s,e|replay_allowed(s,e),..single(rho,Set::empty())}
}
pub open spec fn no_image(s: Local) -> Local {Local {backup:None,..s}}
proof fn ignores_image(rho: Resolver,s: Local,e: ProcessStep<int,Wire>)
    ensures step(rho,no_image(s),e)==no_image(step(rho,s,e)),
{}
proof fn local_memory(archived: LocalProtocol<Local,int,Wire>,journal: LocalProtocol<Local,int,Wire>,
    rho: Resolver,p: Process,es: Seq<ProcessStep<int,Wire>>,k: nat)
    requires k<=es.len(),(journal.initial)(p)==no_image((archived.initial)(p)),
        archived.update==single(rho,live_pair()).update,journal.update==journal_reader(rho).update,
    ensures memory(journal,p,es,k)==no_image(memory(archived,p,es,k)),
    decreases k,
{
    if k>0 {
        let h=(k-1) as nat; local_memory(archived,journal,rho,p,es,h);
        ignores_image(rho,memory(archived,p,es,h),es[h as int]);
    }
}
proof fn first_read(b: Fork,rho: Resolver)
    requires rho(first_rows(b,13))==Some(first_value(b)),
    ensures ({
        let m=journal_reader(rho); let es=checkpoint_observations(b);
        accepted(m,es) && completed_quorum_sample(m,|s: Local|s.returned.unwrap(),b)
            && forall|p: Process| #[trigger] (resume_at(m,es).initial)(p)==no_image(at_cut(b,p,live_pair()))
    }),
{
    hide(memory); let old=single(rho,live_pair()); let m=journal_reader(rho);
    let c=Process::FirstClient; let es=checkpoint_observations(b); real_first_with(rho,rho,b,live_pair());
    assert forall|k: nat| k<=14 implies (#[trigger] first_client_at(m,b,k)).returned==first_client_at(old,b,k).returned by {
        local_memory(old,m,rho,c,es,k);
    }
    assert forall|p: Process| #[trigger] (resume_at(m,es).initial)(p)==no_image(at_cut(b,p,live_pair())) by {
        local_memory(old,m,rho,p,es,es.len()); assert((resume_at(old,es).initial)(p)==at_cut(b,p,live_pair()));
    }
    assert forall|i: int| 0<=i<es.len() implies {
        let e=#[trigger] es[i]; (m.accept)(memory(m,e.actor,es,i as nat),e)
    } by {
        prefix_index(i); local_memory(old,m,rho,es[i].actor,es,i as nat);
        assert((old.accept)(memory(old,es[i].actor,es,i as nat),es[i]));
    }
    assert forall|i: nat| i<=12 implies !(m.done)(#[trigger] first_client_at(m,b,i)) by {
        assert(!(old.done)(first_client_at(old,b,i)));
    }
}
pub proof fn real_replay_service(b: Fork,rho: Resolver)
    requires rho(first_rows(b,13))==Some(first_value(b)),rho(sample_rows(b,BeforeSample::RestoreImages)).is_some(),
    ensures ({
        let j=journal_reader(rho); let m=resume_at(j,checkpoint_observations(b)); let work=BeforeSample::RestoreImages;
        let t=read_states(b,work); let a=read_actions(b,work); let es=observations(t,a);
        response_path(m,|s: Local|s.returned,checkpoint_end(b),delayed_slots(),t,a,rho(sample_rows(b,work)).unwrap())
        && (forall|i: int| 4<=i<=5 ==> {
            let ev=#[trigger] es[i]; let s=memory(m,ev.actor,es,i as nat);
            s.backup.is_none() && s.applied==Seq::<crate::ordered_store::Command>::empty() && ev.action==Action::Local(ev.actor->At_0,Wire::Copy(rebuild(s).value))
                && (t[i+1].locals)(ev.actor->At_0)==rebuild(s).value && t[i+1].pending==t[i].pending
        })
    }),
{
    hide(memory);hide(replay);hide(accepted);
    let work=BeforeSample::RestoreImages; let stores=live_pair(); let j=journal_reader(rho);
    let old=starts_sr2(b,rho,stores); let m=resume_at(j,checkpoint_observations(b)); let res=|s: Local|s.returned;
    let t=read_states(b,work); let a=read_actions(b,work); let es=observations(t,a); let v=rho(sample_rows(b,work)).unwrap();
    real_first_read(b,rho,stores); real_first_with(rho,rho,b,stores); first_read(b,rho);
    sampled_exchange(b,rho,stores,work);
    assert(response_path(resumed(b,rho,stores),res,checkpoint_end(b),delayed_slots(),t,a,v));
    compare_after_first(b,rho,stores,t,a,v);
    assert(response_path(old,res,checkpoint_end(b),delayed_slots(),t,a,v));
    assert(accepted(old,es));
    assert forall|p: Process| #[trigger] (m.initial)(p)==no_image((old.initial)(p)) by {
        assert((old.initial)(p)==at_cut(b,p,stores)); assert((m.initial)(p)==no_image(at_cut(b,p,stores)));
    }
    assert(old.initial =~= resumed(b,rho,stores).initial);
    assert forall|i: int| 0<=i<es.len() implies {
        let ev=#[trigger] es[i]; (m.accept)(memory(m,ev.actor,es,i as nat),ev)
    } by {
        let ev=es[i]; prefix_index(i); local_memory(old,m,rho,ev.actor,es,i as nat);
        assert((old.accept)(memory(old,ev.actor,es,i as nat),ev)) by {reveal(accepted);}
        if i==4 || i==5 {
            assert forall|h: int, s: Local| 0<=h<i implies #[trigger] same_callbacks(old,resumed(b,rho,stores),s,es[h]) by {
                prefix_index(h); assert(es[h].actor!=Process::FirstClient);
            }
            identical_callbacks_on_log(old,resumed(b,rho,stores),es,ev.actor,i as nat);
            read_memory(b,rho,stores,work,ev.actor,i as nat);
        }
    }
    assert forall|i:nat| i<es.len() implies (#[trigger] memory(m,Process::SecondClient,es,i)).returned.is_none() by {
        local_memory(old,m,rho,Process::SecondClient,es,i);assert(memory(old,Process::SecondClient,es,i).returned.is_none());
    }
    local_memory(old,m,rho,Process::SecondClient,es,es.len());
    assert(accepted(m,es)) by { reveal(accepted); }
    assert((m.initial)(Process::SecondClient).returned.is_none());
    assert(response_path(m,res,checkpoint_end(b),delayed_slots(),t,a,v));
    assert forall|i: int| 4<=i<=5 implies {
        let ev=#[trigger] es[i]; let s=memory(m,ev.actor,es,i as nat);
        s.backup.is_none() && s.applied==Seq::<crate::ordered_store::Command>::empty() && ev.action==Action::Local(ev.actor->At_0,Wire::Copy(rebuild(s).value))
            && (t[i+1].locals)(ev.actor->At_0)==rebuild(s).value && t[i+1].pending==t[i].pending
    } by {
        let p=es[i].actor; prefix_index(i); local_memory(old,m,rho,p,es,i as nat);
        assert forall|h: int,s: Local| 0<=h<i implies #[trigger] same_callbacks(old,resumed(b,rho,stores),s,es[h]) by { prefix_index(h); }
        identical_callbacks_on_log(old,resumed(b,rho,stores),es,p,i as nat); read_memory(b,rho,stores,work,p,i as nat);
    }
}
pub proof fn local_redo_gives_the_original_pair(n: Notice)
    ensures incompatible_completions(n,journal_reader(reference_read(Replica::R3)),|s: Local|s.returned.unwrap(),|s: Local|s.returned,
        read_actions(alpha(n),BeforeSample::RestoreImages),1),
{
    hide(memory);hide(accepted);hide(replay);hide(response_path);
    let rho=reference_read(Replica::R3); let b=alpha(n); let work=BeforeSample::RestoreImages;
    assert(unanimous(first_rows(b,13)) && unanimous(first_rows(beta(n),13)));
    crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R1);crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R2);
    assert(crate::metadata_reader::valid_root(sample_rows(b,work)) && rho(sample_rows(b,work))==Some(1));
    first_read(b,rho); first_read(beta(n),rho); real_replay_service(b,rho); sampled_exchange(b,rho,live_pair(),work);
    let m=journal_reader(rho); let pre=resume_at(m,checkpoint_observations(b));
    let a=read_actions(b,work); let t=read_states(b,work); let res=|s: Local|s.returned;
    held_path_is_an_ordinary_opportunity(n,pre,res,t,a,1);
    pair_from_ordinary_path(n,m,|s: Local|s.returned.unwrap(),res,replay(|v,w|cell(v,w),after_receipt(n),a),a,1);
}

}
