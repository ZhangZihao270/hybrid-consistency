use vstd::prelude::*;
use crate::Replica;
use crate::delivery::*;
use crate::checkpoint::*;
use crate::protocol::*;
use crate::confirmation::fresh_send;
use crate::ordinary_service::{Configuration,Work,apply,allowed,pending,action,certifies_work};
use crate::service::*;
use crate::attribution::{no_causal_await,source_discipline,hot_or_causal_weak_wait};
use crate::survivors::sr2_result;

verus! {

// A finite scheduling strategy at a pending read. Its measure may count
// unsent ordinary service messages, pending installations or retries. It
// need only decrease when the scheduler takes the indicated enabled step.
// Weak background steps are allowed too: the subsequent no-await argument
// checks a genuine dependence on their receipt separately.
#[verifier::reject_recursive_types(S)]
pub struct Strategy<S> {
    pub domain: spec_fn(Configuration<S>)->bool,
    pub remaining: spec_fn(Configuration<S>)->nat,
    pub next: spec_fn(Configuration<S>)->Action<Wire>,
}
pub open spec fn internal(a: Action<Wire>) -> bool {
    match a {
        Action::Local(_,_) | Action::Strong(_) | Action::Deliver(_)=>true,
        Action::Send(_,p)=>p.from is At, _=>false,
    }
}
pub open spec fn reduces<S>(m: LocalProtocol<S,int,Wire>,res: spec_fn(S)->Option<int>,s: Configuration<S>,
    plan: Strategy<S>,slots: Set<nat>) -> bool {
    let a=(plan.next)(s);let u=apply(m,s,a);
    internal(a) && fresh_send(a,slots) && allowed(m,s,a) &&
        (pending(u,res) ==> (plan.domain)(u) && (plan.remaining)(u)<(plan.remaining)(s))
}
pub open spec fn service_strategy<S>(m: LocalProtocol<S,int,Wire>,res: spec_fn(S)->Option<int>,plan: Strategy<S>,slots:Set<nat>) -> bool {
    forall|s: Configuration<S>| #[trigger] (plan.domain)(s) && pending(s,res) ==> reduces(m,res,s,plan,slots)
}
pub open spec fn at_end<S>(m:LocalProtocol<S,int,Wire>,t:Seq<Network<int,Wire>>,a:Seq<Action<Wire>>) -> Configuration<S> {
    let es=observations(t,a);
    Configuration {net:t.last(), private:|p| memory(m,p,es,es.len())}
}
// Both requests from C2 have already been sent. The prefix may include any
// allowed mandatory traffic and even receipt of R3's status. No response
// or selector agreement is required.
pub open spec fn requested_prefix<S>(m:LocalProtocol<S,int,Wire>,res:spec_fn(S)->Option<int>,
    net:Network<int,Wire>,slots:Set<nat>,t:Seq<Network<int,Wire>>,a:Seq<Action<Wire>>) -> bool {
    let es=observations(t,a);
    t[0]==net && trace(|x,w|cell(x,w),t,a) && accepted(m,es) && second_invocation(t,a)
        && res((m.initial)(Process::SecondClient)).is_none() && pending_before_end(m,res,es)
        && forall|i:int| 0<=i<a.len() ==> fresh_send(#[trigger] a[i],slots)
}
// Once both queries have gone out, clocks and other private inputs also
// preserve the invocation. Only another client send needs scrutiny here.
pub open spec fn no_client_send(event:Action<Wire>) -> bool {
    match event { Action::Send(_,p) => p.from is At, _ => true }
}
proof fn same_invocation_on_internal_step(t:Seq<Network<int,Wire>>,a:Seq<Action<Wire>>,next:Network<int,Wire>,event:Action<Wire>)
    requires t.len()==a.len()+1,second_invocation(t,a),no_client_send(event),
    ensures second_invocation(t.push(next),a.push(event)),
{
    let c=Process::SecondClient;let q=live_pair();let xs=t.push(next);let es=a.push(event);let k=a.len();
    let old=observations(t,a);let new=observations(xs,es);
    assert forall|i:int| 0<=i<es.len() implies match #[trigger] es[i] {
        Action::Send(_,p) if p.from==c=>invocation_packet(p) && q.contains(p.to->At_0)
            && (forall|j:int| 0<=j<i ==> !client_sends_to(#[trigger] es[j],c,p.to->At_0)),_=>true,
    } by {if i<k {assert(a[i]==es[i]);}}
    assert forall|r:Replica| #[trigger] q.contains(r) implies
        exists|i:int| 0<=i<es.len() && client_sends_to(#[trigger] es[i],c,r) by {
        let i=choose|i:int| 0<=i<k && client_sends_to(#[trigger] a[i],c,r);
        assert(client_sends_to(es[i],c,r));
    }
    assert forall|i:int,j:int| 0<=j<i<new.len() implies match (#[trigger] new[i]).action {
        Action::Send(_,p) if p.from==c=>(#[trigger] new[j]).actor!=c || new[j].incoming.is_none(),_=>true,
    } by {if i<k {assert(old[i]==new[i] && old[j]==new[j]);}}
}
pub(crate) proof fn append_observation<S>(m:LocalProtocol<S,int,Wire>,res:spec_fn(S)->Option<int>,es:Seq<ProcessStep<int,Wire>>,ev:ProcessStep<int,Wire>)
    requires accepted(m,es),pending_before_end(m,res,es),res(memory(m,Process::SecondClient,es,es.len())).is_none(),
        (m.accept)(memory(m,ev.actor,es,es.len()),ev),
    ensures accepted(m,es.push(ev)),pending_before_end(m,res,es.push(ev)),
        forall|p:Process| #[trigger] memory(m,p,es.push(ev),es.len()+1)==if p==ev.actor {
            (m.update)(memory(m,p,es,es.len()),ev)
        } else {memory(m,p,es,es.len())},
{
    let hs=es.push(ev);let k=es.len();let c=Process::SecondClient;
    assert forall|i:int| 0<=i<hs.len() implies {
        let e=#[trigger] hs[i];(m.accept)(memory(m,e.actor,hs,i as nat),e)
    } by {
        memory_on_common_prefix(m,hs[i].actor,es,hs,i as nat);
        if i<k {assert((m.accept)(memory(m,es[i].actor,es,i as nat),es[i]));}
    }
    assert forall|i:nat| i<hs.len() implies res(#[trigger] memory(m,c,hs,i)).is_none() by {memory_on_common_prefix(m,c,es,hs,i);}
    assert forall|p:Process| #[trigger] memory(m,p,hs,k+1)==if p==ev.actor {(m.update)(memory(m,p,es,k),ev)} else {memory(m,p,es,k)}
        by {memory_on_common_prefix(m,p,es,hs,k);}
}
pub(crate) proof fn append_delivery(t:Seq<Network<int,Wire>>,a:Seq<Action<Wire>>,event:Action<Wire>)
    requires trace(|x,w|cell(x,w),t,a),enabled(t.last(),event),
    ensures ({
        let u=advance(|x,w|cell(x,w),t.last(),event);let xs=t.push(u);let es=a.push(event);
        trace(|x,w|cell(x,w),xs,es) && observations(xs,es)==observations(t,a).push(process_step(t.last(),event))
    }),
{
    let xs=t.push(advance(|x,w|cell(x,w),t.last(),event));let es=a.push(event);
    assert forall|i:int| 0<=i<es.len() implies {
        let ev=#[trigger] es[i];enabled(xs[i],ev) && xs[i+1]==advance(|x,w|cell(x,w),xs[i],ev)
    } by {if i<a.len() {assert(enabled(t[i],a[i]) && t[i+1]==advance(|x,w|cell(x,w),t[i],a[i]));}}
    assert(observations(xs,es) =~= observations(t,a).push(process_step(t.last(),event)));
}

pub(crate) proof fn push_event<S>(m:LocalProtocol<S,int,Wire>,res:spec_fn(S)->Option<int>,net:Network<int,Wire>,slots:Set<nat>,
    t:Seq<Network<int,Wire>>,a:Seq<Action<Wire>>,event:Action<Wire>)
    requires requested_prefix(m,res,net,slots,t,a),pending(at_end(m,t,a),res),no_client_send(event),fresh_send(event,slots),
        allowed(m,at_end(m,t,a),event),
    ensures ({
        let u=apply(m,at_end(m,t,a),event);let states=t.push(u.net);let acts=a.push(event);
        requested_prefix(m,res,net,slots,states,acts) && at_end(m,states,acts)==u
    }),
{
    hide(second_invocation);hide(memory);hide(trace);hide(accepted);hide(pending_before_end);hide(process_step);
    assert(t.len()==a.len()+1) by {reveal(trace);}
    let s=at_end(m,t,a);let u=apply(m,s,event);let states=t.push(u.net);let acts=a.push(event);
    let es=observations(t,a);let ev=process_step(t.last(),event);
    append_delivery(t,a,event);append_observation(m,res,es,ev);same_invocation_on_internal_step(t,a,u.net,event);
    assert forall|i:int| 0<=i<acts.len() implies fresh_send(#[trigger] acts[i],slots) by {if i<a.len() {assert(fresh_send(a[i],slots));}}
    assert(at_end(m,states,acts).private =~= u.private) by {
        assert forall|p:Process| #[trigger] (at_end(m,states,acts).private)(p)==(u.private)(p) by {
            assert(memory(m,p,es.push(ev),es.len()+1)==if p==ev.actor {(m.update)(memory(m,p,es,es.len()),ev)} else {memory(m,p,es,es.len())});
        }
    }
}

proof fn original_prefix<A>(u:Seq<A>,xs:Seq<A>,v:A)
    requires u.len()>xs.len(),u.take(xs.len() as int+1)==xs.push(v),
    ensures u.take(xs.len() as int)==xs,
{
    assert(u.take(xs.len() as int) =~= xs) by {
        assert forall|i:int| 0<=i<xs.len() implies #[trigger] u.take(xs.len() as int)[i]==xs[i] by {
            assert(u.take(xs.len() as int+1)[i]==xs.push(v)[i]);
        }
    }
}
pub proof fn schedule_service<S>(m:LocalProtocol<S,int,Wire>,res:spec_fn(S)->Option<int>,net:Network<int,Wire>,
    slots:Set<nat>,t:Seq<Network<int,Wire>>,a:Seq<Action<Wire>>,plan:Strategy<S>)
    -> (out:(Seq<Network<int,Wire>>,Seq<Action<Wire>>,int))
    requires requested_prefix(m,res,net,slots,t,a),service_strategy(m,res,plan,slots),
        pending(at_end(m,t,a),res) ==> (plan.domain)(at_end(m,t,a)),
    ensures response_path(m,res,net,slots,out.0,out.1,out.2),out.0.len()>=t.len(),out.1.len()>=a.len(),out.0.take(t.len() as int)==t,out.1.take(a.len() as int)==a,
        out.1.len()<=a.len()+(plan.remaining)(at_end(m,t,a))+1,
    decreases (plan.remaining)(at_end(m,t,a)),
{
    hide(requested_prefix);hide(response_path);
    let s=at_end(m,t,a);
    if pending(s,res) {
        let ev=(plan.next)(s);let u=apply(m,s,ev);
        assert(reduces(m,res,s,plan,slots));push_event(m,res,net,slots,t,a,ev);
        let xs=t.push(u.net);let es=a.push(ev);
        if pending(u,res) {
            let out=schedule_service(m,res,net,slots,xs,es,plan);
            original_prefix(out.0,t,u.net);original_prefix(out.1,a,ev);out
        } else {
            reveal(requested_prefix);reveal(response_path);
            let v=res((u.private)(Process::SecondClient)).unwrap();
            assert(sr2_result(m,res,observations(xs,es))==Some(v));
            assert(xs.take(t.len() as int) =~= t);assert(es.take(a.len() as int) =~= a);(xs,es,v)
        }
    } else {
        reveal(requested_prefix);reveal(response_path);
        assert(t.take(t.len() as int) =~= t);assert(a.take(a.len() as int) =~= a);
        (t,a,res((s.private)(Process::SecondClient)).unwrap())
    }
}

pub proof fn finite_strategy_and_no_await_give_hot<S>(n:Notice,m:LocalProtocol<S,int,Wire>,first:spec_fn(S)->int,
    res:spec_fn(S)->Option<int>,copy:spec_fn(S)->bool,t:Seq<Network<int,Wire>>,a:Seq<Action<Wire>>,plan:Strategy<S>)
    requires accepted(m,checkpoint_observations(alpha(n))),accepted(m,checkpoint_observations(beta(n))),
        completed_quorum_sample(m,first,alpha(n)),completed_quorum_sample(m,first,beta(n)),
        source_discipline(m,Replica::R2,copy),no_causal_await(m,res),
        ({
            let pre=resume_at(m,checkpoint_observations(alpha(n))); let start=checkpoint_end(alpha(n));
            requested_prefix(pre,res,start,delayed_slots(),t,a) && pending(at_end(pre,t,a),res)
                && (plan.domain)(at_end(pre,t,a)) && service_strategy(pre,res,plan,delayed_slots())
        }),
    ensures exists|a:Seq<Action<Wire>>,v:int| #[trigger] incompatible_completions(n,m,first,res,a,v),
{
    hide(requested_prefix);hide(accepted);hide(incompatible_completions);hide(checkpoint_observations);hide(response_path);
    let b=alpha(n);let pre=resume_at(m,checkpoint_observations(b));
    let out=schedule_service(pre,res,checkpoint_end(b),delayed_slots(),t,a,plan);
    assert(can_respond(pre,res,checkpoint_end(b),delayed_slots()));
    hot_or_causal_weak_wait(n,m,first,res,copy);
}

pub open spec fn dispatch_job<S>(w:Work<S>) -> Strategy<S> {
    Strategy {domain:w.domain,remaining:w.rank,next:|s|action((w.job)(s))}
}
pub proof fn ordinary_jobs_can_be_scheduled<S>(m:LocalProtocol<S,int,Wire>,res:spec_fn(S)->Option<int>,
    w:Work<S>,tol:spec_fn(Configuration<S>,Action<Wire>)->bool,slots:Set<nat>)
    requires certifies_work(m,res,w,tol),
        forall|s:Configuration<S>| #[trigger] (w.domain)(s) && pending(s,res) ==> tol(s,action((w.job)(s))),
    ensures service_strategy(m,res,dispatch_job(w),slots),
{
    assert forall|s:Configuration<S>| #[trigger] (w.domain)(s) && pending(s,res) implies reduces(m,res,s,dispatch_job(w),slots)
        by {let a=action((w.job)(s));assert(tol(s,a));match (w.job)(s) {_=>{}}}
}

// For the ordinary latest-report reader the actual missing jobs at this
// cut are two already-issued SR2 replies, followed by a client poll.
type Local = crate::metadata_pair::Local;
pub open spec fn reply_slot(r:Replica) -> nat { if r==Replica::R1 {13} else {14} }
pub open spec fn has_row(s:Configuration<Local>,r:Replica) -> bool {
    (s.private)(Process::SecondClient).rows.contains_key(r)
}
pub open spec fn present_or_issued(s:Configuration<Local>,r:Replica) -> bool {
    let id=reply_slot(r);let pkt=s.net.pending[id];
    has_row(s,r) || (s.net.pending.contains_key(id) && crate::metadata_pair::replica_answer(pkt) && pkt.from==at(r))
}
pub open spec fn collect_replies() -> Strategy<Local> {
    let c=Process::SecondClient;let r1=Replica::R1;let r2=Replica::R2;
    Strategy { domain: |s:Configuration<Local>| live(s.net,c) && present_or_issued(s,r1) && present_or_issued(s,r2),
        remaining: |s| (if has_row(s,r1) {0nat} else {1nat}) + (if has_row(s,r2) {0nat} else {1nat}),
        next: |s| if !has_row(s,r1) {Action::Deliver(reply_slot(r1))} else if !has_row(s,r2) {Action::Deliver(reply_slot(r2))}
            else {Action::Strong(c)},
    }
}
proof fn collecting_decreases(b:Fork)
    ensures service_strategy(crate::metadata_reader::starts_sr2(b,|m|crate::quorum_rpc::latest(m),Set::empty()),
        |x:Local|x.returned,collect_replies(),delayed_slots()),
{
    let pre=crate::metadata_reader::starts_sr2(b,|m|crate::quorum_rpc::latest(m),Set::empty());
    let w=collect_replies();let c=Process::SecondClient;let res=|x:Local|x.returned;
    assert forall|s:Configuration<Local>| #[trigger] (w.domain)(s) && pending(s,res) implies reduces(pre,res,s,w,delayed_slots()) by {
        let ev=(w.next)(s);let u=apply(pre,s,ev);
        if !has_row(s,Replica::R1) {assert(has_row(u,Replica::R1));}
        else if !has_row(s,Replica::R2) {assert(has_row(u,Replica::R2));}
        else {crate::quorum_rpc::latest_is_a_sample((s.private)(c).rows);}
    }
}

pub proof fn actual_packets_supply_the_strategy(b:Fork)
    ensures ({
        let rho=|m|crate::quorum_rpc::latest(m);let pre=crate::metadata_reader::starts_sr2(b,rho,Set::empty());
        let e=crate::metadata_fair::run(b);let a=crate::progress::actions_before(e,6);let t=crate::progress::states_through(e,6);
        let w=collect_replies();let res=|x:Local|x.returned;let s=at_end(pre,t,a);
        service_strategy(pre,res,w,delayed_slots()) && requested_prefix(pre,res,checkpoint_end(b),delayed_slots(),t,a)
            && pending(s,res) && (w.domain)(s) && (w.remaining)(s)==2
            && exists|u:Seq<Network<int,Wire>>,acts:Seq<Action<Wire>>,v:int|
                #[trigger] response_path(pre,res,checkpoint_end(b),delayed_slots(),u,acts,v) && acts.len()<=9 && acts.take(6)==a
    }),
{
    hide(response_path);hide(service_strategy);hide(crate::protocol::accepted);hide(crate::checkpoint::only_request_sends);
    hide(crate::checkpoint::fanout_before_receiving);hide(crate::delivery::trace);
    let rho=|m|crate::quorum_rpc::latest(m);let pre=crate::metadata_reader::starts_sr2(b,rho,Set::empty());
    let e=crate::metadata_fair::run(b);let a=crate::progress::actions_before(e,6);let t=crate::progress::states_through(e,6);
    let w=collect_replies();let res=|x:Local|x.returned;let c=Process::SecondClient;
    collecting_decreases(b);
    let first=crate::metadata_pair::first_rows(b,13);
    crate::quorum_rpc::latest_is_a_sample(first);assert(rho(first)==Some(first_value(b)));
    // Admissibility supplies only the real pending prefix. No progress
    // assumption or previously computed SR2 answer is used here.
    crate::metadata_fair::accepted_background(b,rho);
    crate::progress::finite_prefix_is_protocol_trace(e,|x,w|cell(x,w),|s,a|true,6);
    let es=observations(t,a);assert(accepted(pre,es) && only_request_sends(a,c,live_pair()) && fanout_before_receiving(es,c));
    assert forall|r:Replica| #[trigger] live_pair().contains(r) implies exists|i:int| 0<=i<a.len() && client_sends_to(#[trigger] a[i],c,r)
        by {let j:int=if r==Replica::R1 {0} else {1};assert(client_sends_to(a[j],c,r));}
    assert forall|i:nat| i<=6 implies res(#[trigger] memory(pre,c,es,i)).is_none() && memory(pre,c,es,i).rows.dom().is_empty()
        by {crate::metadata_fair::state_at(b,rho,c,i,6);prefix_index(i as int);}
    crate::metadata_fair::state_at(b,rho,c,0,6);
    assert(res((pre.initial)(c)).is_none());
    assert forall|i:int| 0<=i<a.len() implies fresh_send(#[trigger] a[i],delayed_slots())
        by {assert(fresh_send((e.action)(i as nat),delayed_slots()));}
    assert(second_invocation(t,a));
    assert(requested_prefix(pre,res,checkpoint_end(b),delayed_slots(),t,a));
    let out=schedule_service(pre,res,checkpoint_end(b),delayed_slots(),t,a,w);
}

}
