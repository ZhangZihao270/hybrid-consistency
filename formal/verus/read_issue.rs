// Independent C2's local send opportunity, before any reply. No premise
// concerning either survivor's read/repair guard or protocol state.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::read_call::{self as call,Log,Net,Event,Program};
use crate::read_nonblocking as nb;
use crate::read_service_contract as contract;
use crate::service_obstruction::suffix_protocol;

verus! {

pub open spec fn send_first() -> Event { Action::Send(11,crate::sr2::query_packet(Replica::R1)) }
pub open spec fn send_second() -> Event { Action::Send(12,crate::sr2::query_packet(Replica::R2)) }
pub open spec fn local_event(a:Event) -> ProcessStep<int,Wire> {
    ProcessStep{actor:Process::SecondClient,action:a,incoming:None,own_local:None}
}
pub open spec fn started<S>(m:Program<S>) -> S {
    (m.update)((m.initial)(Process::SecondClient),local_event(Action::StartSecondClient))
}
pub open spec fn can_issue<S>(m:Program<S>,res:spec_fn(S)->Option<int>) -> bool {
    let x=started(m);let a=local_event(send_first());let b=local_event(send_second());
    let y=(m.update)(x,a);
    res(x).is_none() && (m.accept)(x,a) && res(y).is_none() && (m.accept)(y,b) && res((m.update)(y,b)).is_none()
}

// A single actual stock or hybrid client reference with these initial sends
// suffices, even with unrelated processes acting between C2's steps. A's
// any-majority clause alone does not prescribe this startup interface.
pub proof fn issue_from_reference<S>(m:Program<S>,res:spec_fn(S)->Option<int>,s:Seq<Net>,a:Seq<Event>,i:nat,j:nat,k:nat)
    requires trace(|x,w|cell(x,w),s,a),accepted(m,observations(s,a)),i<j<k<a.len(),
        a[i as int]==Action::StartSecondClient,a[j as int]==send_first(),a[k as int]==send_second(),
        forall|z:int| 0<=z<k && z!=i && z!=j ==> (#[trigger] observations(s,a)[z]).actor!=Process::SecondClient,
        pending_before_end(m,res,observations(s,a)),res(memory(m,Process::SecondClient,observations(s,a),k+1)).is_none(),
    ensures can_issue(m,res),
{
    let es=observations(s,a);let c=Process::SecondClient;
    memory_during_quiescence(m,es,c,0,i);memory_during_quiescence(m,es,c,i+1,j);memory_during_quiescence(m,es,c,j+1,k);
    assert(es[i as int]==local_event(Action::StartSecondClient));
    assert(es[j as int]==local_event(send_first()));assert(es[k as int]==local_event(send_second()));
    assert(memory(m,c,es,i+1)==started(m));assert((m.accept)(memory(m,c,es,j),es[j as int]));
    assert((m.accept)(memory(m,c,es,k),es[k as int]));
}

pub open spec fn issued(b:Fork) -> Log {
    call::append(call::append(call::launch(checkpoint_end(b)),send_first()),send_second())
}
pub proof fn issue_on_original<S>(b:Fork,m:Program<S>,res:spec_fn(S)->Option<int>)
    requires can_issue(m,res),
    ensures ({
        let net=checkpoint_end(b);let local=resume_at(m,checkpoint_observations(b));let ids=delayed_slots();
        let r=call::step(local,res,ids);let x=call::launch(net);let y=call::append(x,send_first());let u=issued(b);
        r(x,send_first(),y) && r(y,send_second(),u) && !call::posted(local,res)(u) &&
            second_invocation(u.nets,u.actions) && call::consistent(local,res,net,ids,u)
            && u.nets.last().pending==net.pending.insert(11,crate::sr2::query_packet(Replica::R1)).insert(12,crate::sr2::query_packet(Replica::R2))
            && u.nets.last().pending.get(2)==Some(packet_for(b,2)) && u.nets.last().locals==net.locals
    }),
{
    hide(checkpoint_end);hide(memory);hide(call::step);hide(second_invocation);
    let net=checkpoint_end(b);let prior=checkpoint_observations(b);let c=Process::SecondClient;
    let local=resume_at(m,prior);let ids=delayed_slots();let r=call::step(local,res,ids);
    let x=call::launch(net);let y=call::append(x,send_first());let u=issued(b);
    assert(prior.len()==17 && prior[16]==local_event(Action::StartSecondClient));
    assert forall|k:int| 0<=k<16 implies (#[trigger] prior[k]).actor!=c by {prefix_index(k);}
    memory_during_quiescence(m,prior,c,0,16);
    assert((local.initial)(c)==started(m)) by {reveal_with_fuel(memory,2);}
    assert(net.second_started && !net.pending.contains_key(11) && !net.pending.contains_key(12)
        && net.pending.get(2)==Some(packet_for(b,2))) by {reveal(checkpoint_end);}
    assert(call::obs(y) =~= seq![local_event(send_first())]);
    assert(call::obs(u) =~= seq![local_event(send_first()),local_event(send_second())]);
    assert(r(x,send_first(),y) && r(y,send_second(),u)) by {reveal(call::step);reveal_with_fuel(memory,3);}
    assert(!call::posted(local,res)(u)) by {reveal_with_fuel(memory,3);}
    let t=crate::promotion_wait::Path{states:seq![x,y,u],actions:seq![send_first(),send_second()]};
    assert(crate::promotion_wait::valid_edges(r,t));call::run_prefix(local,res,net,ids,t,2);
    assert(second_invocation(u.nets,u.actions)) by {
        reveal(second_invocation);
        assert forall|p:Replica| #[trigger] live_pair().contains(p) implies exists|i:int| 0<=i<u.actions.len()
            && client_sends_to(#[trigger] u.actions[i],c,p) by {
            let i:int=if p==Replica::R1 {0} else {1};assert(client_sends_to(u.actions[i],c,p));
        }
    }
    assert(y.nets.last().locals =~= net.locals);assert(u.nets.last().locals =~= net.locals);
}
pub proof fn loss_after_actual_submission<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires crate::service_obstruction::original_reads(n,m,first),can_issue(m,res),
        contract::admits_strong_history(alpha(n),m,first,res),contract::admits_strong_history(beta(n),m,first,res),
        crate::attribution::arrival_certifies_copy(m,Replica::R2),crate::attribution::no_causal_await(m,res),
    ensures ({
        let local=suffix_protocol(m,n);let r=call::step(local,res,delayed_slots());let d=call::posted(local,res);
        let a=issued(alpha(n));let b=issued(beta(n));
        second_invocation(a.nets,a.actions) && second_invocation(b.nets,b.actions) &&
            a.actions==b.actions && a.nets.last().pending.get(2)==Some(packet_for(alpha(n),2))
            && b.nets.last().pending.get(2)==Some(packet_for(beta(n),2)) && !nb::possible(r,d,a)
    }),
{
    hide(call::step);hide(call::posted);hide(second_invocation);hide(contract::admits_strong_history);
    let b=alpha(n);let local=suffix_protocol(m,n);let step=call::step(local,res,delayed_slots());let done=call::posted(local,res);
    let start=call::launch(checkpoint_end(b));let mid=call::append(start,send_first());let lost=nb::hopeless(step,done);
    contract::safety_and_no_await_force_loss(n,m,first,res);issue_on_original(b,m,res);issue_on_original(beta(n),m,res);
    assert(lost(mid));assert(lost(issued(b)));
}
// An operation-local capacity certificate at the already issued read is
// enough. The same TWO sends start the resulting completed alpha and beta
// suffixes. No response or ordinary-only path is assumed at that cut.
pub proof fn pair_from_service_after_issue<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    rank:crate::read_service_rank::Rank<Log>)
    requires crate::service_obstruction::original_reads(n,m,first),can_issue(m,res),
        contract::no_confirm_wait_at(m,res,contract::past(alpha(n)),delayed_slots(),Replica::R2),
        crate::read_service_rank::valid(call::step(suffix_protocol(m,n),res,delayed_slots()),
            call::posted(suffix_protocol(m,n),res),rank),(rank.domain)(issued(alpha(n))),
    ensures exists|a:Seq<Event>,v:int| #[trigger] crate::service::incompatible_completions(n,m,first,res,a,v)
        && 2<=a.len() && a[0]==send_first() && a[1]==send_second(),
{
    hide(call::step);hide(call::posted);hide(second_invocation);hide(crate::service::incompatible_completions);
    hide(crate::service::response_path);
    let b=alpha(n);let local=suffix_protocol(m,n);let ids=delayed_slots();let net=checkpoint_end(b);
    let step=call::step(local,res,ids);let done=call::posted(local,res);let effect=call::receipt(Replica::R2);
    let plain=nb::ordinary(step,effect);let scope=|l:Log|call::consistent(local,res,net,ids,l);
    let start=call::launch(net);let mid=call::append(start,send_first());let cut=issued(b);
    issue_on_original(b,m,res);prefix_transport_is_enabled(b);
    assert forall|l:Log,a:Event,u:Log| scope(l) && !done(l) && #[trigger] step(l,a,u) && !done(u) implies scope(u)
        by {call::step_consistent(local,res,net,ids,l,a,u);}
    assert(nb::no_unlock(step,done,effect,scope));
    crate::read_service_rank::schedule_exit(step,done,rank,cut);
    nb::ordinary_option_at(step,done,effect,scope,cut);
    let tail=nb::to_path(plain,done,cut,choose|k:nat| #[trigger] nb::within(plain,done,cut,k));
    let t=crate::promotion_wait::Path{states:seq![start,mid]+tail.states,actions:seq![send_first(),send_second()]+tail.actions};
    assert forall|i:int| 0<=i<t.actions.len() implies plain(t.states[i],#[trigger] t.actions[i],t.states[i+1])
        && step(t.states[i],t.actions[i],t.states[i+1]) by {
        if i>=2 {assert(plain(tail.states[i-2],tail.actions[i-2],tail.states[i-1]));}
    }
    assert(!done(start) && !done(mid)) by {
        reveal(call::posted);assert(live_pair().contains(Replica::R2));reveal(second_invocation);
        assert(!(exists|i:int| 0<=i<mid.actions.len() && client_sends_to(#[trigger] mid.actions[i],Process::SecondClient,Replica::R2)));
    }
    assert forall|i:int| 0<=i<t.actions.len() implies !done(#[trigger] t.states[i]) by {
        if i>=2 {assert(!done(tail.states[i-2]));}
    }
    assert(t.states.last()==tail.states.last());
    call::real_response(local,res,net,ids,t);call::no_receipt_in_log(local,res,net,ids,Replica::R2,t,t.actions.len());
    let l=t.states.last();contract::fork_on_held_log(n,m,first,res,l);
    assert(l.actions==t.actions && crate::service::incompatible_completions(n,m,first,res,l.actions,
        crate::survivors::sr2_result(local,res,call::obs(l)).unwrap()));
}
pub proof fn gated_and_ungated_clients_issue(need:Notice,gates:Set<Replica>,select:crate::sr2::Select)
    ensures can_issue(crate::sr2::read_protocol(gates,need,select),|s:crate::sr2::Reader|s.returned),
{}
}
