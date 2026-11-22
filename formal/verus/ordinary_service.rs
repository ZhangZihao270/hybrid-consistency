use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::progress::*;
use crate::confirmation::{admissible_service,finite_fair_service};
use crate::service::*;
use crate::attribution::{source_discipline,no_causal_await,hot_or_causal_weak_wait};
use crate::survivors::{sr2_result,after_crash};

verus! {

pub struct Configuration<S> {
    pub net: Network<int,Wire>,
    pub private: spec_fn(Process)->S,
}
pub enum Job { Packet(nat), Cpu(Process) }
#[verifier::reject_recursive_types(S)]
pub struct Work<S> {
    pub domain: spec_fn(Configuration<S>)->bool,
    pub rank: spec_fn(Configuration<S>)->nat,
    pub job: spec_fn(Configuration<S>)->Job,
}
pub open spec fn action(job: Job) -> Action<Wire> {
    match job {Job::Packet(id)=>Action::Deliver(id),Job::Cpu(p)=>Action::Strong(p)}
}
pub open spec fn allowed<S>(m: LocalProtocol<S,int,Wire>,s: Configuration<S>,a: Action<Wire>) -> bool {
    let ev=process_step(s.net,a);
    enabled(s.net,a) && (m.accept)((s.private)(ev.actor),ev)
}
pub open spec fn available<S>(m: LocalProtocol<S,int,Wire>,s: Configuration<S>,job: Job) -> bool {
    allowed(m,s,action(job)) && match job {
        Job::Cpu(_)=>true,
        Job::Packet(id)=>s.net.pending.contains_key(id) && s.net.pending[id].path!=Path::Weak,
    }
}
pub open spec fn apply<S>(m: LocalProtocol<S,int,Wire>,s: Configuration<S>,a: Action<Wire>) -> Configuration<S> {
    let ev=process_step(s.net,a);
    Configuration {net:advance(|x,w|cell(x,w),s.net,a),
        private:|p| if p==ev.actor {(m.update)((s.private)(p),ev)} else {(s.private)(p)} }
}
pub open spec fn pending<S>(s: Configuration<S>,result: spec_fn(S)->Option<int>) -> bool {
    result((s.private)(Process::SecondClient)).is_none()
}

// A local proof of progress. An obligation names an actual ordinary
// packet or an enabled CPU step. Other actions can alter private state,
// replace a job at lower rank, or leave its rank and identity unchanged.
// The adapter specifies the class of interference it can tolerate.
pub open spec fn certifies_work<S>(m: LocalProtocol<S,int,Wire>,result: spec_fn(S)->Option<int>,w: Work<S>,
    tolerated: spec_fn(Configuration<S>,Action<Wire>)->bool) -> bool {
    (forall|s: Configuration<S>| #[trigger] (w.domain)(s) && pending(s,result) ==> available(m,s,(w.job)(s)))
    && forall|s: Configuration<S>,a: Action<Wire>| (w.domain)(s) && pending(s,result) && allowed(m,s,a)
        && #[trigger] tolerated(s,a) ==> {
            let u=apply(m,s,a);
            pending(u,result) ==> (w.domain)(u) && ((w.rank)(u)<(w.rank)(s) ||
                ((w.rank)(u)==(w.rank)(s) && (w.job)(u)==(w.job)(s) && a!=action((w.job)(s))))
        }
}
pub open spec fn configuration<S>(m: LocalProtocol<S,int,Wire>,e: Execution<int,Wire>,i: nat) -> Configuration<S> {
    let es=observations(states_through(e,i),actions_before(e,i));
    Configuration {net:(e.state)(i),private:|p|memory(m,p,es,i)}
}
// A process can receive many unrelated messages while never polling. The
// reference schedules continuously enabled ordinary jobs specifically.
pub open spec fn taken_or_disabled<S>(m: LocalProtocol<S,int,Wire>,e: Execution<int,Wire>,k: nat,j: Job) -> bool {
    (e.action)(k)==action(j) || !available(m,configuration(m,e,k),j)
}
pub open spec fn job_scheduled<S>(m: LocalProtocol<S,int,Wire>,e: Execution<int,Wire>,i: nat,j: Job) -> bool {
    exists|k:nat| k>=i && #[trigger] taken_or_disabled(m,e,k,j)
}
proof fn turn<S>(m: LocalProtocol<S,int,Wire>,e: Execution<int,Wire>,from: nat,j: Job) -> (k: nat)
    requires job_scheduled(m,e,from,j),
    ensures k>=from && ((e.action)(k)==action(j) || !available(m,configuration(m,e,k),j)),
{
    choose|k:nat| k>=from && #[trigger] taken_or_disabled(m,e,k,j)
}
pub open spec fn fair_jobs<S>(m: LocalProtocol<S,int,Wire>,e: Execution<int,Wire>) -> bool {
    forall|i: nat,j: Job| #[trigger] job_scheduled(m,e,i,j)
}
pub(crate) proof fn one_step<S>(start: Network<int,Wire>,m: LocalProtocol<S,int,Wire>,res: spec_fn(S)->Option<int>,
    e: Execution<int,Wire>,i: nat)
    requires admissible_service(start,m,res,e),
    ensures ({
        let s=configuration(m,e,i); let a=(e.action)(i);
        allowed(m,s,a) && configuration(m,e,i+1)==apply(m,s,a)
    }),
{
    let es=observations(states_through(e,i),actions_before(e,i)); let hs=observations(states_through(e,i+1),actions_before(e,i+1));
    let s=configuration(m,e,i); let a=(e.action)(i); let ev=process_step(s.net,a);
    assert forall|k: int| 0<=k<i implies #[trigger] es[k]==#[trigger] hs[k] by {};
    assert(accepted(m,observations(states_through(e,i+1),actions_before(e,i+1))));
    memory_on_common_prefix(m,ev.actor,es,hs,i); assert(hs[i as int]==ev);
    assert((m.accept)(memory(m,ev.actor,hs,i),ev));
    assert(configuration(m,e,i+1).private =~= apply(m,s,a).private) by {
        assert forall|p: Process| #[trigger] (configuration(m,e,i+1).private)(p)==(apply(m,s,a).private)(p) by {
            memory_on_common_prefix(m,p,es,hs,i);
        }
    }
}
pub(crate) proof fn minimum(f: spec_fn(nat)->nat,from: nat,candidate: nat) -> (at: nat)
    requires candidate>=from,
    ensures at>=from,forall|j: nat| j>=from ==> f(at)<=#[trigger] f(j),
    decreases f(candidate),
{
    if exists|j:nat|j>=from && #[trigger] f(j)<f(candidate) {
        minimum(f,from,choose|j:nat|j>=from && #[trigger] f(j)<f(candidate))
    } else {candidate}
}
proof fn after_start<S>(start: Network<int,Wire>,m: LocalProtocol<S,int,Wire>,res: spec_fn(S)->Option<int>,
    w: Work<S>,tol: spec_fn(Configuration<S>,Action<Wire>)->bool,e: Execution<int,Wire>,i: nat,k: nat)
    requires admissible_service(start,m,res,e),certifies_work(m,res,w,tol),i<=k,(w.domain)(configuration(m,e,i)),
        forall|j:nat| i<=j<=k ==> #[trigger] pending(configuration(m,e,j),res),
        forall|j:nat| i<=j<k ==> #[trigger] tol(configuration(m,e,j),(e.action)(j)),
    ensures ({
        let s=configuration(m,e,i); let u=configuration(m,e,k);
        (w.domain)(u) && (w.rank)(u)<=(w.rank)(s) &&
            ((w.rank)(s)==(w.rank)(u) ==> (w.job)(s)==(w.job)(u)
                && forall|j:nat| i<=j<k ==> (#[trigger] (e.action)(j))!=action((w.job)(s)))
    }),
    decreases k-i,
{
    hide(available); hide(configuration); hide(admissible_service);
    if i<k {
        let h=(k-1) as nat; after_start(start,m,res,w,tol,e,i,h); one_step(start,m,res,e,h);
        assert(tol(configuration(m,e,h),(e.action)(h))); assert(pending(configuration(m,e,k),res));
    }
}
pub proof fn service_after_quiescence<S>(start: Network<int,Wire>,m: LocalProtocol<S,int,Wire>,res: spec_fn(S)->Option<int>,
    w: Work<S>,tol: spec_fn(Configuration<S>,Action<Wire>)->bool,e: Execution<int,Wire>,from: nat)
    requires admissible_service(start,m,res,e),certifies_work(m,res,w,tol),fair_jobs(m,e),
        (w.domain)(configuration(m,e,from)),forall|i:nat| i>=from ==> #[trigger] tol(configuration(m,e,i),(e.action)(i)),
    ensures exists|i:nat| i>=from && !#[trigger] pending(configuration(m,e,i),res),
{
    hide(configuration);hide(admissible_service);hide(available);
    if !(exists|i:nat| i>=from && !#[trigger] pending(configuration(m,e,i),res)) {
        let f=|i| (w.rank)(configuration(m,e,i)); let at=minimum(f,from,from);
        after_start(start,m,res,w,tol,e,from,at);
        let job=(w.job)(configuration(m,e,at));
        assert(job_scheduled(m,e,at,job));
        let j=turn(m,e,at,job);
        after_start(start,m,res,w,tol,e,at,j); after_start(start,m,res,w,tol,e,at,j+1);
        assert(f(at)<=f(j) && f(at)<=f(j+1));
        assert(available(m,configuration(m,e,j),job));
        assert((e.action)(j)!=action(job));
    }
}

// From a real fair reference with a serviceable ordinary suffix, discharge
// the former finite-hybrid-completion premise. The replay may choose a
// different finite prefix. No condition compares two outputs or two ranks.
pub proof fn ordinary_service_and_no_await_give_hot<S>(n: Notice,m: LocalProtocol<S,int,Wire>,
    first: spec_fn(S)->int,res: spec_fn(S)->Option<int>,copy: spec_fn(S)->bool,runnable: spec_fn(Network<int,Wire>,Process)->bool,
    w: Work<S>,tol: spec_fn(Configuration<S>,Action<Wire>)->bool,e: Execution<int,Wire>,from: nat)
    requires
        accepted(m,checkpoint_observations(alpha(n))),accepted(m,checkpoint_observations(beta(n))),
        completed_quorum_sample(m,first,alpha(n)),completed_quorum_sample(m,first,beta(n)),
        source_discipline(m,Replica::R2,copy),no_causal_await(m,res),
        delivery_fair(e),process_fair(e,runnable),
        ({
            let pre=resume_at(m,checkpoint_observations(alpha(n)));
            admissible_service(checkpoint_end(alpha(n)),pre,res,e) && certifies_work(pre,res,w,tol)
                && fair_jobs(pre,e) && (w.domain)(configuration(pre,e,from))
                && forall|i:nat| i>=from ==> #[trigger] tol(configuration(pre,e,i),(e.action)(i))
        }),
    ensures exists|a: Seq<Action<Wire>>,v: int| #[trigger] incompatible_completions(n,m,first,res,a,v),
{
    hide(memory); hide(accepted); hide(trace); hide(available); hide(incompatible_completions);
    let b=alpha(n); let pre=resume_at(m,checkpoint_observations(b)); let start=checkpoint_end(b);
    service_after_quiescence(start,pre,res,w,tol,e,from);
    let h=choose|i:nat|i>=from && !#[trigger] pending(configuration(pre,e,i),res);
    let completed=|s,a|sr2_result(pre,res,observations(s,a)).is_some();
    assert(completed(states_through(e,h),actions_before(e,h)));
    assert(eventually_responds(e,runnable,completed)); assert(after_crash(start));
    let (k,v)=finite_fair_service(start,pre,res,e,runnable);
    assert(response_path(pre,res,start,delayed_slots(),states_through(e,k),actions_before(e,k),v));
    hot_or_causal_weak_wait(n,m,first,res,copy);
}

// A normal majority read can discharge the work rule directly at its
// mailbox. The collected rows survive all later deliveries. In particular
// this proof places no conditions on counters, clocks, or either disk.
pub open spec fn mailbox_work() -> Work<crate::metadata_pair::Local> {
    let c=Process::SecondClient;
    Work {domain:|s: Configuration<crate::metadata_pair::Local>| live(s.net,c)
        && crate::ordered_store::majority((s.private)(c).rows.dom()),
        rank:|_s|0,job:|_s|Job::Cpu(c)}
}
pub proof fn a_ready_mailbox_is_enough(b: Fork)
    ensures certifies_work(crate::metadata_reader::starts_sr2(b,|m|crate::quorum_rpc::latest(m),Set::empty()),
        |s:crate::metadata_pair::Local|s.returned,mailbox_work(),|_s,_a|true),
{
    let m=crate::metadata_reader::starts_sr2(b,|m|crate::quorum_rpc::latest(m),Set::empty());
    let w=mailbox_work();let res=|s:crate::metadata_pair::Local|s.returned; let c=Process::SecondClient;
    assert forall|s: Configuration<crate::metadata_pair::Local>,a: Action<Wire>| (w.domain)(s) && pending(s,res)
        && #[trigger] allowed(m,s,a) implies {
            let u=apply(m,s,a); !pending(u,res) || ((w.domain)(u) && a!=Action::Strong(c))
        } by {
        let x=(s.private)(c); let u=apply(m,s,a);
        assert(x.rows.dom().subset_of((u.private)(c).rows.dom()));
        if a==Action::Strong(c) {crate::quorum_rpc::latest_is_a_sample(x.rows);}
    }
}
proof fn job_witness<S>(m: LocalProtocol<S,int,Wire>,e: Execution<int,Wire>,i: nat,k:nat,j: Job)
    requires k>=i,taken_or_disabled(m,e,k,j),
    ensures job_scheduled(m,e,i,j),
{}
pub proof fn fair_after_real_deliveries<S>(m: LocalProtocol<S,int,Wire>,b: Fork)
    ensures fair_jobs(m,crate::metadata_fair::run(b)),
{
    let e=crate::metadata_fair::run(b);
    assert forall|i:nat,j:Job| #[trigger] job_scheduled(m,e,i,j) by {
        match j {
            Job::Packet(id)=>{
                let k=i+14;
                assert((e.state)(k).pending == (e.state)(14).pending);
                crate::metadata_fair::pending_after_all_live_deliveries(b);
                job_witness(m,e,i,k,j);
            },
            Job::Cpu(p)=>{
                let d:nat=if p==at(Replica::R1) {0} else if p==at(Replica::R2) {1} else {2};
                let k=3*(i+14)+d; assert(k%3==d); job_witness(m,e,i,k,j);
            }
        }
    }
}
// The additional service contract actually excludes the model that can
// poll forever. This holds for every proposed certificate and start time.
pub proof fn validator_cannot_supply_work(b: Fork,w: Work<crate::metadata_pair::Local>,
    tol: spec_fn(Configuration<crate::metadata_pair::Local>,Action<Wire>)->bool,from: nat)
    ensures ({
        let e=crate::metadata_fair::run(b);
        let m=crate::metadata_reader::starts_sr2(b,crate::metadata_reader::reference_read(Replica::R3),Set::empty());
        let res=|s:crate::metadata_pair::Local|s.returned;
        (w.domain)(configuration(m,e,from)) && (forall|i:nat| i>=from ==> #[trigger] tol(configuration(m,e,i),(e.action)(i)))
            ==> !certifies_work(m,res,w,tol)
    }),
{
    hide(configuration);hide(crate::confirmation::admissible_service);hide(certifies_work);
    let e=crate::metadata_fair::run(b);
    let m=crate::metadata_reader::starts_sr2(b,crate::metadata_reader::reference_read(Replica::R3),Set::empty());
    let res=|s:crate::metadata_pair::Local|s.returned;
    crate::metadata_fair::pending_after_all_live_deliveries(b); fair_after_real_deliveries(m,b);
    if certifies_work(m,res,w,tol) && (w.domain)(configuration(m,e,from))
        && (forall|i:nat| i>=from ==> #[trigger] tol(configuration(m,e,i),(e.action)(i))) {
        service_after_quiescence(checkpoint_end(b),m,res,w,tol,e,from);
        let i=choose|i:nat| i>=from && !#[trigger] pending(configuration(m,e,i),res);
        reveal(configuration);
        assert(sr2_result(m,res,observations(states_through(e,i),actions_before(e,i))).is_none());
    }
}

}
