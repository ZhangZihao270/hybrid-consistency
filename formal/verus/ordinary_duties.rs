// A state-based route from stock A to service in the original pair.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::admissible_service;
use crate::delivery::{self,Action,Network,Process,process_step};
use crate::ordinary_fairness::*;
use crate::ordinary_service::{self as local,Configuration,configuration,allowed,apply};
use crate::progress::{self,Execution,actions_before,states_through,delivery_fair,process_fair};
use crate::protocol::LocalProtocol;
use crate::service_obstruction::*;
use crate::stock_availability::{self as stock,ReadSystem,Stream};
use crate::survivors::{after_crash,postcrash_schedule_has_only_live_actors};

verus! {

// ProcessTurn means any real action by that process. It is weaker than
// the scheduler granting a particular poll. An unrelated turn counts here;
// the implementation proof must still explain the effect of that turn.
pub enum Helper { OrdinaryPacket(nat), ProcessTurn(Process) }
pub type Runnable=spec_fn(Network<int,Wire>,Process)->bool;
pub open spec fn actual_tasks<S>(m:LocalProtocol<S,int,Wire>, runnable:Runnable)
    -> Scheduler<Configuration<S>,Action<Wire>,Helper>
{
    Scheduler {
        enabled:|u:Configuration<S>,j| match j {
            Helper::OrdinaryPacket(id)=>local::available(m,u,local::Job::Packet(id)),
            Helper::ProcessTurn(p)=>runnable(u.net,p),
        },
        taken:|u:Configuration<S>,a,_v,j| match j {
            Helper::OrdinaryPacket(id)=>a==Action::Deliver(id),
            Helper::ProcessTurn(p)=>process_step(u.net,a).actor==p,
        },
    }
}
pub open spec fn physical<S>(m:LocalProtocol<S,int,Wire>, e:Execution<int,Wire>) -> Stream<Configuration<S>,Action<Wire>> {
    Stream {state:|i|configuration(m,e,i), event:e.action}
}

proof fn same_live<S>(m:LocalProtocol<S,int,Wire>,result:spec_fn(S)->Option<int>,e:Execution<int,Wire>,i:nat,j:nat,p:Process)
    requires after_crash((e.state)(0)),admissible_service((e.state)(0),m,result,e),
    ensures delivery::live((e.state)(i),p)==delivery::live((e.state)(j),p),
{
    let u=|x,w|cell(x,w);
    progress::finite_prefix_is_protocol_trace(e,u,|_s,_a|true,i);
    progress::finite_prefix_is_protocol_trace(e,u,|_s,_a|true,j);
    postcrash_schedule_has_only_live_actors(u,states_through(e,i),actions_before(e,i),i);
    postcrash_schedule_has_only_live_actors(u,states_through(e,j),actions_before(e,j),j);
    match p {Process::At(_)=>{}, _=>{}}
}
proof fn packet_guard<S>(m:LocalProtocol<S,int,Wire>,e:Execution<int,Wire>,runnable:Runnable,i:nat,id:nat)
    ensures ({
        let h=duties(actual_tasks(m,runnable),physical(m,e)); let j=Helper::OrdinaryPacket(id);
        ((h.enabled)(i,j) ==> (e.state)(i).pending.contains_key(id)
            && delivery::live((e.state)(i),(e.state)(i).pending[id].to))
        && (h.taken)(i,j)==((e.action)(i)==Action::Deliver(id))
    }),
{}
proof fn process_guard<S>(m:LocalProtocol<S,int,Wire>,e:Execution<int,Wire>,runnable:Runnable,i:nat,p:Process)
    ensures ({
        let h=duties(actual_tasks(m,runnable),physical(m,e)); let j=Helper::ProcessTurn(p);
        (h.enabled)(i,j)==runnable((e.state)(i),p) && (h.taken)(i,j)==progress::runs_at(e,i,p)
    }),
{}

pub proof fn actual_fairness<S>(m:LocalProtocol<S,int,Wire>,result:spec_fn(S)->Option<int>,e:Execution<int,Wire>,runnable:Runnable)
    requires after_crash((e.state)(0)),admissible_service((e.state)(0),m,result,e),delivery_fair(e),process_fair(e,runnable),
    ensures fair(duties(actual_tasks(m,runnable),physical(m,e))),
{
    hide(admissible_service); hide(physical); hide(actual_tasks); hide(configuration);
    let h=duties(actual_tasks(m,runnable),physical(m,e));
    assert forall|start:nat,j:Helper| #[trigger] scheduled(h,start,j) by {
        if !scheduled(h,start,j) {
            assert(!discharged(h,start,j));
            match j {
                Helper::OrdinaryPacket(id)=>{
                    packet_guard(m,e,runnable,start,id); let u=(e.state)(start); assert(u.pending.contains_key(id));
                    let k=choose|k:nat| k>=start && (#[trigger] (e.action)(k)==Action::Deliver(id)
                        || !delivery::live((e.state)(k),u.pending[id].to));
                    same_live(m,result,e,start,k,u.pending[id].to); packet_guard(m,e,runnable,k,id);
                    assert(discharged(h,k,j));
                },
                Helper::ProcessTurn(p)=>{
                    assert forall|k:nat| k>=start implies #[trigger] runnable((e.state)(k),p) by {
                        process_guard(m,e,runnable,k,p); assert(!discharged(h,k,j));
                    }
                    assert(progress::continuously_runnable(e,runnable,start,p));
                    let k=choose|k:nat| k>=start && #[trigger] progress::runs_at(e,k,p);
                    process_guard(m,e,runnable,k,p);
                    assert(discharged(h,k,j));
                },
            }
        }
    }
}

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(E)]
#[verifier::reject_recursive_types(J)]
pub struct Adapter<S,X,E,J> {
    pub start:X, pub idle:E,
    pub decode:spec_fn(X,Configuration<S>,Action<Wire>)->(E,X),
    pub domain:spec_fn(X,Configuration<S>)->bool,
    pub remaining:spec_fn(X,Configuration<S>,J)->nat,
    pub helper:spec_fn(X,Configuration<S>,J)->Helper,
}

pub open spec fn returns<S>(result:spec_fn(S)->Option<int>,u:Configuration<S>,v:Configuration<S>) -> bool {
    local::pending(u,result) && !local::pending(v,result)
}

proof fn emission_in_configuration<S>(m:LocalProtocol<S,int,Wire>,result:spec_fn(S)->Option<int>,e:Execution<int,Wire>,i:nat)
    ensures c2_emissions(m,result,e)(i)==returns(result,configuration(m,e,i),configuration(m,e,i+1)),
{
    assert(delivery::observations(crate::progress::states_through(e,i),crate::progress::actions_before(e,i)).len()==i);
    assert(delivery::observations(crate::progress::states_through(e,i+1),crate::progress::actions_before(e,i+1)).len()==i+1);
}

// Local check for one ordinary job on the two concrete transition edges.
pub open spec fn pays_job<S,X,E,J>(tasks:Scheduler<X,E,J>, m:LocalProtocol<S,int,Wire>, runnable:Runnable,
    d:Adapter<S,X,E,J>, x:X, b:E, y:X, u:Configuration<S>, a:Action<Wire>, v:Configuration<S>, j:J) -> bool {
    let h=actual_tasks(m,runnable); let k=(d.helper)(x,u,j);
    (tasks.enabled)(x,j) && !(tasks.taken)(x,b,y,j) && (tasks.enabled)(y,j)
        ==> (d.remaining)(y,v,j)<(d.remaining)(x,u,j)
        || ((d.remaining)(y,v,j)==(d.remaining)(x,u,j) && (d.helper)(y,v,j)==k && (h.enabled)(u,k) && !(h.taken)(u,a,v,k))
}

// Test only pre-return edges of the chosen environment. All protocol
// states, strong coordination, in-flight packets and local memories remain
// present. An implementation may prove the rule on an inductive domain.
// It is a progress refinement for ordinary obligations in general. No
// observed writer, H history, or particular return value occurs here.
pub open spec fn covers_edge<S,X,E,J>(p:ReadSystem<X,E>, tasks:Scheduler<X,E,J>, m:LocalProtocol<S,int,Wire>,
    result:spec_fn(S)->Option<int>, runnable:Runnable, d:Adapter<S,X,E,J>, x:X, u:Configuration<S>, a:Action<Wire>) -> bool {
    let v=apply(m,u,a); let emitted=returns(result,u,v);
    let (b,y)=legal_candidate(p,d.idle,x,public_candidate(p,d.idle,x,(d.decode)(x,u,a),emitted));
    emitted || ((d.domain)(y,v) && forall|j:J| #[trigger] pays_job(tasks,m,runnable,d,x,b,y,u,a,v,j))
}
pub open spec fn covers_work<S,X,E,J>(p:ReadSystem<X,E>,tasks:Scheduler<X,E,J>,m:LocalProtocol<S,int,Wire>,
    result:spec_fn(S)->Option<int>,runnable:Runnable,d:Adapter<S,X,E,J>,env:spec_fn(Configuration<S>,Action<Wire>)->bool) -> bool {
    forall|x:X,u:Configuration<S>,a:Action<Wire>| (d.domain)(x,u) && allowed(m,u,a) && env(u,a)
        ==> #[trigger] covers_edge(p,tasks,m,result,runnable,d,x,u,a)
}
pub open spec fn decoder<S,X,E,J>(d:Adapter<S,X,E,J>, m:LocalProtocol<S,int,Wire>, e:Execution<int,Wire>) -> Replay<X,E> {
    Replay {start:d.start,idle:d.idle,propose:|x,i|(d.decode)(x,configuration(m,e,i),(e.action)(i))}
}
pub open spec fn image<S,X,E,J>(p:ReadSystem<X,E>,d:Adapter<S,X,E,J>,m:LocalProtocol<S,int,Wire>,
    result:spec_fn(S)->Option<int>,e:Execution<int,Wire>) -> Replay<X,E> {
    marked_replay(p,decoder(d,m,e),c2_emissions(m,result,e))
}
proof fn in_domain<S,X,E,J>(p:ReadSystem<X,E>,tasks:Scheduler<X,E,J>,m:LocalProtocol<S,int,Wire>,
    result:spec_fn(S)->Option<int>,runnable:Runnable,d:Adapter<S,X,E,J>,env:spec_fn(Configuration<S>,Action<Wire>)->bool,
    e:Execution<int,Wire>,i:nat)
    requires admissible_service((e.state)(0),m,result,e),covers_work(p,tasks,m,result,runnable,d,env),
        (d.domain)(d.start,configuration(m,e,0)), forall|k:nat| #[trigger] env(configuration(m,e,k),(e.action)(k)),
        forall|k:nat| !#[trigger] c2_emissions(m,result,e)(k),
    ensures (d.domain)(state_at(p,image(p,d,m,result,e),i),configuration(m,e,i)),
    decreases i,
{
    hide(admissible_service); hide(allowed); hide(local::available);
    if i>0 {
        let k=(i-1) as nat; let r=image(p,d,m,result,e); let x=state_at(p,r,k); let u=configuration(m,e,k);
        let a=(e.action)(k); let v=configuration(m,e,i);
        in_domain(p,tasks,m,result,runnable,d,env,e,k); local::one_step((e.state)(0),m,result,e,k);
        emission_in_configuration(m,result,e,k);
        assert(!c2_emissions(m,result,e)(k) && !returns(result,u,v));
        assert(env(u,a) && covers_edge(p,tasks,m,result,runnable,d,x,u,a));
        assert(state_at(p,r,i)==ordinary_step(p,r,x,k).1);
    }
}

// From the two environmental fairness clauses and local transition laws.
// The numerical measure belongs to a particular outstanding stock job.
// Stock A still supplies the implication from fair ordinary work to a
// client return, including protocols with no global rank to that return.
pub proof fn original_pair_from_local_duties<S,X,E,J>(
    n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int,result:spec_fn(S)->Option<int>,copy:spec_fn(S)->bool,
    e:Execution<int,Wire>,runnable:Runnable,p:ReadSystem<X,E>,tasks:Scheduler<X,E,J>,d:Adapter<S,X,E,J>,
    env:spec_fn(Configuration<S>,Action<Wire>)->bool)
    requires original_reads(n,m,first),crate::attribution::source_discipline(m,Replica::R2,copy),
        admissible_service(checkpoint_end(alpha(n)),suffix_protocol(m,n),result,e),delivery_fair(e),process_fair(e,runnable),
        stock::eventual(p,|s|fair(duties(tasks,s))),invocation(p,d.start),idle_legal(p,d.idle),
        covers_work(p,tasks,suffix_protocol(m,n),result,runnable,d,env),
        (d.domain)(d.start,configuration(suffix_protocol(m,n),e,0)),
        forall|k:nat| #[trigger] env(configuration(suffix_protocol(m,n),e,k),(e.action)(k)),
    ensures conflict_or_await(n,m,first,result),
{
    hide(covers_edge); hide(pays_job); hide(allowed); hide(actual_tasks); hide(conflict_or_await);
    hide(original_reads); hide(crate::attribution::source_discipline); hide(stock::eventual);
    hide(stock::reaches); hide(process_fair); hide(delivery_fair); hide(admissible_service);
    let pre=suffix_protocol(m,n); let out=c2_emissions(pre,result,e);
    let r=image(p,d,pre,result,e); let s=duties(tasks,projection(p,r));
    let h=duties(actual_tasks(pre,runnable),physical(pre,e));
    let plan=Support { remaining:|i,j|(d.remaining)(state_at(p,r,i),configuration(pre,e,i),j),
        helper:|i,j|(d.helper)(state_at(p,r,i),configuration(pre,e,i),j) };
    assert((e.state)(0)==checkpoint_end(alpha(n))) by {reveal(admissible_service);}
    assert(after_crash((e.state)(0))); actual_fairness(pre,result,e,runnable);
    if !(exists|i:nat| #[trigger] out(i)) {
        assert forall|i:nat,j:J| #[trigger] supports_at(s,h,plan,i,j) by {
            let x=state_at(p,r,i); let u=configuration(pre,e,i); let a=(e.action)(i); let v=configuration(pre,e,i+1);
            in_domain(p,tasks,pre,result,runnable,d,env,e,i);
            local::one_step((e.state)(0),pre,result,e,i);
            emission_in_configuration(pre,result,e,i);
            assert(covers_edge(p,tasks,pre,result,runnable,d,x,u,a)); reveal(covers_edge);
            assert(!out(i) && !returns(result,u,v));
            assert(state_at(p,r,i+1)==ordinary_step(p,r,x,i).1);
            let (b,y)=ordinary_step(p,r,x,i);
            assert(pays_job(tasks,pre,runnable,d,x,b,y,u,a,v,j)); reveal(pays_job);
        }
        ordinary_service_from_a(p,tasks,decoder(d,pre,e),out,h,plan);
    }
    let k=choose|i:nat| #[trigger] out(i);
    crate::service_obstruction::from_publication(n,m,first,result,e,copy,k);
}

// The original SMR need not have an idle instruction. None is a gap
// between projected events. A continuously pending stock invocation also
// owes genuine stock steps, so infinitely many gaps cannot simulate A.
pub proof fn original_pair_without_stock_idle<S,X,E,J>(
    n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int,result:spec_fn(S)->Option<int>,copy:spec_fn(S)->bool,
    e:Execution<int,Wire>,runnable:Runnable,p:ReadSystem<X,E>,tasks:Scheduler<X,E,J>,
    d:Adapter<S,X,Option<E>,crate::ordinary_stutter::Duty<J>>,env:spec_fn(Configuration<S>,Action<Wire>)->bool)
    requires original_reads(n,m,first),crate::attribution::source_discipline(m,Replica::R2,copy),
        admissible_service(checkpoint_end(alpha(n)),suffix_protocol(m,n),result,e),delivery_fair(e),process_fair(e,runnable),
        stock::eventual(p,|s|fair(duties(tasks,s))),invocation(p,d.start),d.idle.is_none(),
        covers_work(crate::ordinary_stutter::padded(p),crate::ordinary_stutter::scheduler(p,tasks),
            suffix_protocol(m,n),result,runnable,d,env),
        (d.domain)(d.start,configuration(suffix_protocol(m,n),e,0)),
        forall|k:nat| #[trigger] env(configuration(suffix_protocol(m,n),e,k),(e.action)(k)),
    ensures conflict_or_await(n,m,first,result),
{
    hide(original_reads); hide(conflict_or_await); hide(covers_work); hide(admissible_service);
    crate::ordinary_stutter::preserves_eventual(p,tasks);
    crate::ordinary_stutter::same_reach(p,d.start);
    original_pair_from_local_duties(n,m,first,result,copy,e,runnable,crate::ordinary_stutter::padded(p),
        crate::ordinary_stutter::scheduler(p,tasks),d,env);
}

}
