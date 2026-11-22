// Progress of the independent second client on the two original histories.
use vstd::prelude::*;
use crate::Replica;
use crate::attribution::{hot_or_causal_weak_wait, no_causal_await, source_discipline, waits_for_replication};
use crate::checkpoint::*;
use crate::confirmation::{admissible_service,finite_observed_service};
use crate::delivery::*;
use crate::ordinary_fairness::*;
use crate::progress::{Execution,actions_before,states_through};
use crate::protocol::{LocalProtocol,resume_at,accepted};
use crate::service::{can_respond,incompatible_completions,response_path};
use crate::stock_availability as stock;
use crate::ordinary_stutter as pad;
use stock::ReadSystem;
use crate::survivors::sr2_result;

verus! {

pub open spec fn suffix_protocol<S>(m:LocalProtocol<S,int,Wire>, n:Notice) -> LocalProtocol<S,int,Wire> {
    resume_at(m,checkpoint_observations(alpha(n)))
}
pub open spec fn read_at<S>(p:LocalProtocol<S,int,Wire>, result:spec_fn(S)->Option<int>, e:Execution<int,Wire>, i:nat) -> Option<int> {
    sr2_result(p,result,observations(states_through(e,i),actions_before(e,i)))
}
pub open spec fn c2_emissions<S>(p:LocalProtocol<S,int,Wire>, result:spec_fn(S)->Option<int>, e:Execution<int,Wire>) -> spec_fn(nat)->bool {
    |i:nat| read_at(p,result,e,i).is_none() && read_at(p,result,e,i+1).is_some()
}
pub open spec fn original_reads<S>(n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int) -> bool {
    accepted(m,checkpoint_observations(alpha(n))) && accepted(m,checkpoint_observations(beta(n)))
        && completed_quorum_sample(m,first,alpha(n)) && completed_quorum_sample(m,first,beta(n))
}
pub open spec fn conflict_or_await<S>(n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int,result:spec_fn(S)->Option<int>) -> bool {
    (exists|a:Seq<Action<Wire>>,v:int| #[trigger] incompatible_completions(n,m,first,result,a,v))
      || (waits_for_replication(m,checkpoint_states(alpha(n)),actions_to_crash(alpha(n)),1,Replica::R2,2,result,delayed_slots())
          && !no_causal_await(m,result))
}

pub(crate) proof fn from_publication<S>(n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int,result:spec_fn(S)->Option<int>,
    e:Execution<int,Wire>,copy:spec_fn(S)->bool,i:nat)
    requires original_reads(n,m,first), source_discipline(m,Replica::R2,copy),
        admissible_service(checkpoint_end(alpha(n)),suffix_protocol(m,n),result,e),
        c2_emissions(suffix_protocol(m,n),result,e)(i),
    ensures conflict_or_await(n,m,first,result),
{
    hide(accepted); hide(admissible_service); hide(incompatible_completions); hide(source_discipline);
    let net=checkpoint_end(alpha(n)); let pre=suffix_protocol(m,n);
    let (k,v)=finite_observed_service(net,pre,result,e,i+1);
    assert(response_path(pre,result,net,delayed_slots(),states_through(e,k),actions_before(e,k),v));
    assert(can_respond(pre,result,net,delayed_slots()));
    hot_or_causal_weak_wait(n,m,first,result,copy);
}

// With an arbitrary unfiltered ordinary replay, stock A yields either a
// concrete finite publication mismatch or a scheduler obligation missed on
// that replay when both desired safety/no-await properties are maintained.
pub proof fn diagnose_originals<S,X,E,J>(n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int,result:spec_fn(S)->Option<int>,
    e:Execution<int,Wire>,copy:spec_fn(S)->bool,
    p:ReadSystem<X,E>,tasks:Scheduler<X,E,J>,r:Replay<X,E>)
    requires original_reads(n,m,first), source_discipline(m,Replica::R2,copy),
        admissible_service(checkpoint_end(alpha(n)),suffix_protocol(m,n),result,e),
        stock::eventual(p,|s|fair(duties(tasks,s))),invocation(p,r.start),idle_legal(p,r.idle),
    ensures conflict_or_await(n,m,first,result) || ({
        let s=projection(p,r); let out=c2_emissions(suffix_protocol(m,n),result,e);
        (exists|i:nat| #[trigger] emitted_at(p,s,i) && !out(i))
            || (exists|j:J, start:nat| !#[trigger] scheduled(duties(tasks,s),start,j))
    }),
{
    hide(conflict_or_await); hide(original_reads); hide(source_discipline); hide(admissible_service);
    let s=projection(p,r); let out=c2_emissions(suffix_protocol(m,n),result,e);
    stock_progress_or_starvation(p,tasks,r);
    if exists|i:nat| #[trigger] emitted_at(p,s,i) {
        let i=choose|i:nat| #[trigger] emitted_at(p,s,i);
        if out(i) { from_publication(n,m,first,result,e,copy,i); }
    }
}

// The stock implementation has no idle requirement here. The diagnostic
// distinguishes a named ordinary duty from a projection that eventually
// stops taking actual stock steps. Neither proves a promotion dependency.
pub proof fn diagnose_without_stock_idle<S,X,E,J>(
    n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int,result:spec_fn(S)->Option<int>,
    e:Execution<int,Wire>,copy:spec_fn(S)->bool,p:ReadSystem<X,E>,tasks:Scheduler<X,E,J>,r:Replay<X,Option<E>>)
    requires original_reads(n,m,first),source_discipline(m,Replica::R2,copy),
        admissible_service(checkpoint_end(alpha(n)),suffix_protocol(m,n),result,e),
        stock::eventual(p,|s|fair(duties(tasks,s))),invocation(p,r.start),r.idle.is_none(),
    ensures conflict_or_await(n,m,first,result) || ({
        let t=projection(pad::padded(p),r); let out=c2_emissions(suffix_protocol(m,n),result,e);
        let d=duties(pad::scheduler(p,tasks),t);
        (exists|i:nat| #[trigger] emitted_at(pad::padded(p),t,i) && !out(i))
          || (exists|j:J,start:nat| !#[trigger] scheduled(d,start,pad::Duty::Ordinary(j)))
          || (exists|start:nat| !#[trigger] pad::advances(t,start)
              && (forall|i:nat| i>=start ==> (p.response)(#[trigger] (t.state)(i)).is_none()))
    }),
{
    hide(original_reads); hide(conflict_or_await); hide(admissible_service); hide(source_discipline);
    let src=pad::padded(p); let ts=pad::scheduler(p,tasks); let t=projection(src,r); let d=duties(ts,t);
    pad::preserves_eventual(p,tasks); pad::same_reach(p,r.start);
    diagnose_originals(n,m,first,result,e,copy,src,ts,r);
    if exists|j:pad::Duty<J>,start:nat| !#[trigger] scheduled(d,start,j) {
        let (j,start)=choose|j:pad::Duty<J>,start:nat| !#[trigger] scheduled(d,start,j);
        match j {
            pad::Duty::Ordinary(job)=>{assert(!scheduled(d,start,pad::Duty::Ordinary(job)));},
            pad::Duty::StockStep=>{
                assert forall|i:nat| i>=start implies (p.response)(#[trigger] (t.state)(i)).is_none()
                    by {assert(!discharged(d,i,j));}
                assert(!pad::advances(t,start)) by {
                    if pad::advances(t,start) {
                        let k=choose|k:nat| k>=start && (#[trigger] (t.event)(k)).is_some();
                        assert(!discharged(d,k,j));
                    }
                }
            },
        }
    }
}


}
