// Derive the guards to emit both replies from service *before* either
// request has been delivered. Expose genuine ordinary preparations.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::*};
use crate::first_mailbox as mail;
use crate::first_schedule::{self as first,reference};
use crate::independent_read::{self as read,State};
use crate::read_call::{Event,Program};
use crate::promotion_wait::{self as wait,Relation};
use crate::read_nonblocking as nb;
use crate::sr1_majorities as maj;

verus! {

pub open spec fn launched<S>(m:Program<S>,b:Fork) -> bool {
    let es=maj::obs(b);
    forall|i:int| 0<=i<5 ==> {let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)}
}
// The sole C1 prerequisite is one initially enabled fanout. The startup
// trace can be taken from a stock execution with the same client callbacks.
pub open spec fn initial_sends() -> Seq<ProcessStep<int,Wire>> {
    let c=Process::FirstClient;
    Seq::new(3,|i:int|ProcessStep{actor:c,incoming:None,own_local:None,
        action:send((i+3) as nat,Path::Strong,c,at(if i==0 {Replica::R1} else if i==1 {Replica::R2} else {Replica::R3}),Wire::Request)})
}
pub open spec fn initiates<S>(m:Program<S>) -> bool {
    let es=initial_sends();accepted(m,es)
        && forall|k:nat| k<=3 ==> !(m.done)(#[trigger] memory(m,Process::FirstClient,es,k))
}
// Invocation interface only. Once a fresh caller has published, the
// workload does not require it to send another request.
pub open spec fn pending_fanout<S>(m:Program<S>) -> bool {
    let es=initial_sends(); let c=Process::FirstClient;
    !(m.done)((m.initial)(c)) && forall|i:nat| i<3 && !(m.done)(#[trigger] memory(m,c,es,i))
        ==> (m.accept)(memory(m,c,es,i),es[i as int])
}
pub open spec fn weak_open<S>(m:Program<S>,b:Fork) -> bool {
    let es=maj::obs(b);let r=at(Replica::R3);
    (m.accept)((m.initial)(r),es[0]) && (m.accept)((m.update)((m.initial)(r),es[0]),es[1])
}
pub(crate) proof fn caller_memory<S>(m:Program<S>,b:Fork,k:nat)
    requires k<=11,
    ensures ({let j=if k<=2 {0nat} else if k<=5 {(k-2) as nat} else {3nat};
        memory(m,Process::FirstClient,checkpoint_observations(b),k)==memory(m,Process::FirstClient,initial_sends(),j)}),
    decreases k,
{
    if k>0 {let i=(k-1) as nat;caller_memory(m,b,i);prefix_index(i as int);
        if 2<=i<5 {assert(checkpoint_observations(b)[i as int]==initial_sends()[i-2]);}}
}
pub proof fn fanout_and_weak_open_launch<S>(m:Program<S>,b:Fork)
    requires initiates(m),weak_open(m,b),
    ensures launched(m,b),first::before_answers(m,b),
{
    let es=maj::obs(b);let c=Process::FirstClient;maj::majority_transport(b);
    assert forall|i:int| 0<=i<5 implies {let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)} by {
        if i<2 {
            assert(i==0 || i==1);assert(es[0].actor==at(Replica::R3) && es[1].actor==at(Replica::R3));
            if i==0 {assert(memory(m,es[i].actor,es,0)==(m.initial)(at(Replica::R3)));}
            else {assert(memory(m,es[i].actor,es,1)==(m.update)((m.initial)(at(Replica::R3)),es[0])) by {reveal_with_fuel(memory,2);}}
        }
        else {assert(es[i]==initial_sends()[i-2] && es[i].actor==c);caller_memory(m,b,i as nat);maj::local_at(m,b,c,i as nat);
            assert(maj::count(b,i as nat)==i);assert(memory(m,c,es,i as nat)==memory(m,c,initial_sends(),(i-2) as nat));
            assert((m.accept)(memory(m,c,initial_sends(),(i-2) as nat),initial_sends()[i-2]));}
    }
    assert forall|k:nat| k<=11 implies !(m.done)((#[trigger] first::cfg(m,b,k).private)(c)) by {
        caller_memory(m,b,k);
        let j=if k<=2 {0nat} else if k<=5 {(k-2) as nat} else {3nat};
        assert(!(m.done)(memory(m,c,initial_sends(),j)));
    }
}
proof fn same_local_step<S>(m:Program<S>,p:Process,es:Seq<ProcessStep<int,Wire>>,hs:Seq<ProcessStep<int,Wire>>,i:nat,j:nat)
    requires i<es.len(),j<hs.len(),es[i as int]==hs[j as int],memory(m,p,es,i)==memory(m,p,hs,j),
    ensures memory(m,p,es,i+1)==memory(m,p,hs,j+1),
{}
pub proof fn fanout_from_one_execution<S>(m:Program<S>,states:Seq<crate::read_call::Net>,
    actions:Seq<Event>,i:nat,j:nat,k:nat)
    requires trace(|v,w|cell(v,w),states,actions),accepted(m,observations(states,actions)),i<j<k<actions.len(),
        actions[i as int]==initial_sends()[0].action,actions[j as int]==initial_sends()[1].action,actions[k as int]==initial_sends()[2].action,
        forall|h:int| 0<=h<k && h!=i && h!=j ==> (#[trigger] observations(states,actions)[h]).actor!=Process::FirstClient,
        forall|h:nat| h<=k+1 ==> !(m.done)(#[trigger] memory(m,Process::FirstClient,observations(states,actions),h)),
    ensures initiates(m),
{
    hide(trace);hide(memory);
    let c=Process::FirstClient;let es=observations(states,actions);let out=initial_sends();
    memory_during_quiescence(m,es,c,0,i);memory_during_quiescence(m,es,c,i+1,j);memory_during_quiescence(m,es,c,j+1,k);
    assert(es[i as int]==out[0] && es[j as int]==out[1] && es[k as int]==out[2]);
    assert(memory(m,c,out,0)==memory(m,c,es,0)) by {reveal(memory);}
    same_local_step(m,c,out,es,0,i);same_local_step(m,c,out,es,1,j);same_local_step(m,c,out,es,2,k);
    assert forall|h:int| 0<=h<3 implies {let e=#[trigger] out[h];(m.accept)(memory(m,e.actor,out,h as nat),e)} by {
        let t=if h==0 {i} else if h==1 {j} else {k};assert(h==0 || h==1 || h==2);
        assert((m.accept)(memory(m,c,es,t),es[t as int]));
    }
    assert forall|h:nat| h<=3 implies !(m.done)(#[trigger] memory(m,c,out,h)) by {
        let t=if h==0 {i} else if h==1 {j} else if h==2 {k} else {k+1};assert(h==0 || h==1 || h==2 || h==3);
        assert(!(m.done)(memory(m,c,es,t)));
    }
}
pub proof fn launch_cut<S>(m:Program<S>,b:Fork)
    requires launched(m,b),
    ensures first::reached_in(m,b)(reference(m,b,5)),mail::submitted(reference(m,b,5)),
        mail::inbox(reference(m,b,5)).packets==Map::<nat,Packet<Wire>>::empty(),
{
    first::ref_suffix(m,b,0,5);
    assert(nb::within(read::prefix_step(m),read::at_state(reference(m,b,5)),reference(m,b,0),5));
    let x=reference(m,b,5);let r=crate::origin(b.branch);
    assert(live(x.cfg.net,at(r)) && live(x.cfg.net,at(Replica::R3)));
    assert(x.first_requested.contains(r) && x.first_requested.contains(Replica::R3));
    assert(mail::for_client(x.cfg.net.pending) =~= Map::<nat,Packet<Wire>>::empty());
}
pub open spec fn request_id(r:Replica) -> nat {
    match r {Replica::R1=>3,Replica::R2=>4,Replica::R3=>5}
}
pub open spec fn request(r:Replica) -> Packet<Wire> {
    Packet{from:Process::FirstClient,to:at(r),path:Path::Strong,input:Wire::Request}
}
pub open spec fn offer(r:Replica,v:int) -> Event {
    send(request_id(r)+3,Path::FirstReadReply,at(r),Process::FirstClient,Wire::Reply(v))
}
pub open spec fn intake(r:Replica,v:int) -> ProcessStep<int,Wire> {
    ProcessStep{actor:at(r),action:Action::Deliver(request_id(r)),incoming:Some(request(r)),own_local:Some(v)}
}
pub open spec fn report(r:Replica,v:int) -> ProcessStep<int,Wire> {
    ProcessStep{actor:at(r),action:offer(r,v),incoming:None,own_local:Some(v)}
}
// This is a local opportunity, tested on the current shared value and
// arbitrary private memory. It specifies neither a read outcome nor a
// progress property. Network freshness is checked at the original cut.
pub open spec fn ready<S>(m:Program<S>,x:State<S>,r:Replica) -> bool {
    let v=(x.cfg.net.locals)(r);let s=(x.cfg.private)(at(r));let e=intake(r,v);
    if x.cfg.net.pending.get(request_id(r))==Some(request(r)) {
        (m.accept)(s,e) && (m.accept)((m.update)(s,e),report(r,v))
    } else { (m.accept)(s,report(r,v)) }
}
pub open spec fn enabling<S>(m:Program<S>,r:Replica) -> Relation<State<S>,Event> {
    |x,a,y| !ready(m,x,r) && ready(m,y,r)
}
// An unrelated actor cannot change this opportunity. The normal handling
// of the issued request cannot create it either: its guard and successor
// are precisely the first half of the opportunity tested beforehand.
pub proof fn enabling_is_extra_local_work<S>(m:Program<S>,x:State<S>,a:Event,y:State<S>,r:Replica)
    requires mail::active_step(m)(x,a,y),enabling(m,r)(x,a,y),
    ensures process_step(x.cfg.net,a).actor==at(r),
        !(a==Action::<Wire>::Deliver(request_id(r)) && x.cfg.net.pending.get(request_id(r))==Some(request(r))),
{
    let n=x.cfg.net;let e=process_step(n,a);
    if e.actor!=at(r) {
        if let Action::Send(id,p)=a {assert(p!=request(r));}
        assert((y.cfg.net.pending.get(request_id(r))==Some(request(r)))==(n.pending.get(request_id(r))==Some(request(r))));
        assert(local_input(n,a,r).is_none());
    }
    if a==Action::<Wire>::Deliver(request_id(r)) && n.pending.get(request_id(r))==Some(request(r)) {
        assert(e==intake(r,(n.locals)(r)));assert(local_input(n,a,r).is_none());
    }
}
pub open spec fn received_from<S>(p:wait::Path<State<S>,Event>,i:int,r:Replica) -> bool {
    let e=process_step(p.states[i].cfg.net,p.actions[i]);
    e.incoming.is_some() && first_reply(e.incoming.unwrap()) && e.incoming.unwrap().from==at(r)
}
// Safety of actual read publication, independent of its value and
// availability. This is a direct-response interface, stronger than A's
// value-membership rule alone.
pub open spec fn returned_without_two<S>(m:Program<S>,x:State<S>) -> bool {
    exists|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),x,p)
        && !(exists|i:int,j:int,r:Replica,s:Replica| 0<=i<p.actions.len() && 0<=j<p.actions.len() && r!=s
            && #[trigger] received_from(p,i,r) && #[trigger] received_from(p,j,s))
}
pub open spec fn two_reporters<S>(m:Program<S>,x:State<S>) -> bool { !returned_without_two(m,x) }
pub open spec fn native_reply<S>(x:State<S>,a:Event,r:Replica) -> bool {
    a==offer(r,(x.cfg.net.locals)(r)) && x.cfg.net.pending.get(request_id(r))!=Some(request(r))
}
pub open spec fn responder_step<S>(m:Program<S>,p:wait::Path<State<S>,Event>,j:int,r:Replica) -> bool {
    let x=p.states[j];let a=p.actions[j];let y=p.states[j+1];
    (a is Send && a->Send_1.from==at(r) && first_reply(a->Send_1) && !native_reply(x,a,r))
        || (enabling(m,r)(x,a,y) && process_step(x.cfg.net,a).actor==at(r)
            && !(a==Action::<Wire>::Deliver(request_id(r)) && x.cfg.net.pending.get(request_id(r))==Some(request(r))))
}
pub open spec fn before_consumed_answer<S>(m:Program<S>,p:wait::Path<State<S>,Event>,j:int,r:Replica) -> bool {
    responder_step(m,p,j,r) && exists|i:int,k:int| j<=i<k<p.actions.len() && #[trigger] mail::same_issue(p,i,k)
        && first_reply(p.actions[i]->Send_1) && p.actions[i]->Send_1.from==at(r)
}
pub open spec fn needs_preparation<S>(m:Program<S>,x:State<S>,r:Replica,effect:Relation<State<S>,Event>) -> bool {
    let step=mail::active_step(m);let d=mail::posted(m);
    (exists|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(step,d,x,p) && !wait::uses(p,effect))
    && forall|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(step,d,x,p) && !wait::uses(p,effect)
        ==> exists|j:int| 0<=j<p.actions.len() && #[trigger] before_consumed_answer(m,p,j,r)
}
proof fn mask_persists<S>(m:Program<S>,p:wait::Path<State<S>,Event>,j:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::active_step(m),p),j<=p.actions.len(),
    ensures p.states[j as int].cfg.net.unavailable==p.states[0].cfg.net.unavailable,
    decreases j,
{
    if j>0 {let k=(j-1) as nat;mask_persists(m,p,k);assert(mail::active_step(m)(p.states[k as int],p.actions[k as int],p.states[j as int]));}
}
pub(crate) proof fn sending_cut<S>(m:Program<S>,b:Fork,p:wait::Path<State<S>,Event>,j:nat,r:Replica) -> (i:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::active_step(m),p),j<p.actions.len(),
        p.states[0]==reference(m,b,5),received_from(p,j as int,r),
    ensures i<j,p.actions[i as int] is Send,first_reply(p.actions[i as int]->Send_1),p.actions[i as int]->Send_1.from==at(r),
        r!=maj::missing(b),mail::same_issue(p,i as int,j as int),
{
    let a=p.actions[j as int];let x=p.states[j as int];let id=a->Deliver_0;let packet=x.cfg.net.pending[id];
    assert(a is Deliver && packet.to==Process::FirstClient && packet.from==at(r));
    assert(p.states[0].cfg.net.pending.get(id)!=Some(packet));
    let i=mail::last_send(m,p,j,id,packet);mask_persists(m,p,i);i
}
proof fn first_preparation<S>(m:Program<S>,p:wait::Path<State<S>,Event>,r:Replica,j:nat) -> (h:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::active_step(m),p),j<=p.actions.len(),
        !ready(m,p.states[0],r),ready(m,p.states[j as int],r),
    ensures h<j,responder_step(m,p,h as int,r),
    decreases j,
{
    let k=(j-1) as nat;
    if ready(m,p.states[k as int],r) {first_preparation(m,p,r,k)}
    else {assert(mail::active_step(m)(p.states[k as int],p.actions[k as int],p.states[j as int]));
        enabling_is_extra_local_work(m,p.states[k as int],p.actions[k as int],p.states[j as int],r);k}
}
pub proof fn direct_or_indispensable_preparation<S>(m:Program<S>,b:Fork,r:Replica,effect:Relation<State<S>,Event>)
    requires r!=maj::missing(b),!mail::posted(m)(reference(m,b,5)),two_reporters(m,reference(m,b,5)),
        nb::possible(mail::active_step(m),mail::posted(m),reference(m,b,5)),
    ensures ({let x=reference(m,b,5);ready(m,x,r) || wait::needs_class(mail::active_step(m),mail::posted(m),x,effect)
        || needs_preparation(m,x,r,effect)}),
{
    let x=reference(m,b,5);let step=mail::active_step(m);let d=mail::posted(m);
    if !ready(m,x,r) && !wait::needs_class(step,d,x,effect) {
        nb::first_response_iff(step,d,x);
        assert(exists|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(step,d,x,p) && !wait::uses(p,effect));
        assert forall|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(step,d,x,p) && !wait::uses(p,effect)
            implies exists|j:int| 0<=j<p.actions.len() && #[trigger] before_consumed_answer(m,p,j,r) by {
            let (i,j,g,h)=choose|i:int,j:int,g:Replica,h:Replica| 0<=i<p.actions.len() && 0<=j<p.actions.len()
                && g!=h && #[trigger] received_from(p,i,g) && #[trigger] received_from(p,j,h);
            let ig=sending_cut(m,b,p,i as nat,g);let ih=sending_cut(m,b,p,j as nat,h);
            assert(g==r || h==r);let k=if g==r {ig} else {ih};let a=p.actions[k as int];
            assert(step(p.states[k as int],a,p.states[k as int+1]));
            if native_reply(p.states[k as int],a,r) {
                assert(ready(m,p.states[k as int],r));let z=first_preparation(m,p,r,k);assert(before_consumed_answer(m,p,z as int,r));
            } else {assert(responder_step(m,p,k as int,r));assert(before_consumed_answer(m,p,k as int,r));}
        }
    }
}

pub proof fn enabled_responders_supply_offers<S>(m:Program<S>,b:Fork)
    requires launched(m,b),ready(m,reference(m,b,5),crate::origin(b.branch)),ready(m,reference(m,b,5),Replica::R3),
    ensures first::emitted(m,b),
{
    let x=reference(m,b,5);let es=maj::obs(b);let orig=crate::origin(b.branch);
    assert forall|i:int| 0<=i<9 implies {let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)} by {
        if i>=5 {
            let r=if i==5 || i==7 {orig} else {Replica::R3};let p=at(r);let v=(x.cfg.net.locals)(r);
            let k=if r==orig {5nat} else {6nat};
            assert(x.cfg.net.pending.get(request_id(r))==Some(request(r)));
            assert(es[k as int]==intake(r,v) && es[k as int+2]==report(r,v));
            assert forall|j:int| 5<=j<k implies (#[trigger] es[j]).actor!=p by {};
            memory_during_quiescence(m,es,p,5,k);
            assert(es[k as int+1].actor!=p);memory_during_quiescence(m,es,p,k+1,k+2);
            assert(i==k || i==k+2);
        }
    }
}


// Replay a proposed C1-only return on its *own* crash reference starting
// before either request delivery. This derives receipt of both selected
// replies whenever all publications there require two actual reporters.
spec fn place<S>(m:Program<S>,b:Fork,t:mail::Inbox<S>) -> State<S> {
    let root=reference(m,b,9);let x=root.cfg;let q=x.net.pending.remove(first::origin_slot(b)).remove(8nat);
    State{cfg:crate::ordinary_service::Configuration{net:crate::read_call::Net{pending:q.union_prefer_right(t.packets),..x.net},
        private:|who|if who==Process::FirstClient {t.local} else {(x.private)(who)}},..root}
}
pub proof fn quorum_from_reference<S>(m:Program<S>,b:Fork)
    requires first::emitted(m,b),two_reporters(m,reference(m,b,5)),
    ensures first::inbox_quorum(m,b),
{
    first::reference_cut(m,b);let r=mail::client_step(m);let d=mail::local_done(m);let root=first::initial_client(m,b);
    assert forall|p:first::ClientPath<S>| #[trigger] wait::first_return(r,d,root,p) implies first::both_receipts(b,p) by {
        let u=wait::Path{states:Seq::new(4,|i:int|reference(m,b,5+i as nat))+Seq::new(p.states.len(),|i:int|place(m,b,p.states[i])),
            actions:maj::actions(b).subrange(5,9)+p.actions};
        let step=mail::active_step(m);let done=mail::posted(m);let c=Process::FirstClient;
        assert(place(m,b,root).cfg.private =~= reference(m,b,9).cfg.private);
        assert(place(m,b,root).cfg.net.pending =~= reference(m,b,9).cfg.net.pending);
        assert forall|i:int| 0<=i<u.actions.len() implies step(u.states[i],#[trigger] u.actions[i],u.states[i+1]) by {
            if i<4 {first::reference_edge(m,b,5+i as nat);}
            else {
                let j=i-4;let t=p.states[j];let a=p.actions[j];let x=u.states[i];let y=u.states[i+1];let next=read::next(m,x,a);
                assert(r(t,a,p.states[j+1]));first::subset_after(m,p,j as nat);
                if let Action::Deliver(id)=a {assert(t.packets.dom().contains(id));assert(id==8 || id==first::origin_slot(b));}
                assert(process_step(x.cfg.net,a)==mail::event(t,a));assert(next.cfg.net.pending =~= y.cfg.net.pending);
                assert(next.cfg.net.locals =~= y.cfg.net.locals);assert(next.cfg.private =~= y.cfg.private);
            }
        }
        assert forall|i:int| 0<=i<u.actions.len() implies !done(#[trigger] u.states[i]) by {
            if i<4 {
                let es=maj::obs(b);
                assert forall|h:int| 5+i<=h<9 implies (#[trigger] es[h]).actor!=c by {prefix_index(h);}
                memory_during_quiescence(m,es,c,5+i as nat,9);
            } else {assert(!d(p.states[i-4]));}
        }
        assert(u.states.len()==u.actions.len()+1 && u.states[0]==reference(m,b,5));
        assert(u.states.last()==place(m,b,p.states.last()));assert(d(p.states.last()));assert(done(u.states.last()));
        assert(!done(u.states[0]));assert(wait::first_return(step,done,reference(m,b,5),u));
        let (i,j,g,h)=choose|i:int,j:int,g:Replica,h:Replica| 0<=i<u.actions.len() && 0<=j<u.actions.len() && g!=h
            && #[trigger] received_from(u,i,g) && #[trigger] received_from(u,j,h);
        assert forall|k:int,w:Replica| 0<=k<u.actions.len() && #[trigger] received_from(u,k,w) implies
            k>=4 && (w==Replica::R3 || w==crate::origin(b.branch))
                && p.actions[k-4]==Action::<Wire>::Deliver(if w==Replica::R3 {8nat} else {first::origin_slot(b)}) by {
            if k<4 {prefix_index(k+5);} else {
                let j=k-4;let a=p.actions[j];assert(r(p.states[j],a,p.states[j+1]));first::subset_after(m,p,j as nat);
                assert(a is Deliver);assert(p.states[j].packets.dom().contains(a->Deliver_0));
                assert(a->Deliver_0==8 || a->Deliver_0==first::origin_slot(b));
            }
        }
        assert(first::both_receipts(b,p));
    }
}

// Fair reference existence and the availability implication are distinct.
// At the second cut a reference is needed only after real emission has
// been established. Neither condition fixes which messages arrive next.
pub open spec fn first_service<S>(m:Program<S>,first_value_of:spec_fn(S)->int,b:Fork,run:crate::fair_read::Runnable) -> bool {
    let x=reference(m,b,5);let y=reference(m,b,9);
    launched(m,b) && first::before_answers(m,b)
        && first::value_rule(m,first_value_of,b)
        && mail::first_availability(m,run,first::reached_in(m,b))
        && mail::fair_opportunity(m,run,x) && (first::emitted(m,b) ==> mail::fair_opportunity(m,run,y))
}
pub open spec fn weak_wait<S>(m:Program<S>,x:State<S>,effect:Relation<State<S>,Event>) -> bool {
    wait::needs_class(mail::active_step(m),mail::posted(m),x,effect)
}
pub open spec fn obstruction<S>(m:Program<S>,b:Fork,effect:Relation<State<S>,Event>) -> bool {
    let x=reference(m,b,5);let y=reference(m,b,9);
    returned_without_two(m,x) || weak_wait(m,x,effect)
        || (exists|r:Replica| r!=maj::missing(b) && !ready(m,x,r) && #[trigger] needs_preparation(m,x,r,effect))
        || (first::emitted(m,b) && (weak_wait(m,y,effect) || mail::needs_further_input(m,y,effect)))
}
pub proof fn service_before_either_reply<S>(m:Program<S>,first_value_of:spec_fn(S)->int,b:Fork,run:crate::fair_read::Runnable,
    effect:Relation<State<S>,Event>)
    requires first_service(m,first_value_of,b,run),
    ensures obstruction(m,b,effect) || first::service_at_offers(m,first_value_of,b),
{
    let x=reference(m,b,5);let y=reference(m,b,9);let scope=first::reached_in(m,b);let r=crate::origin(b.branch);
    launch_cut(m,b);mail::fair_first_service(m,run,scope,x);maj::local_at(m,b,Process::FirstClient,5);
    assert(maj::count(b,5)==5);
    assert(!(m.done)((first::cfg(m,b,5).private)(Process::FirstClient)));
    assert(!mail::posted(m)(x));
    if !obstruction(m,b,effect) {
        direct_or_indispensable_preparation(m,b,r,effect);direct_or_indispensable_preparation(m,b,Replica::R3,effect);
        if !ready(m,x,r) {assert(needs_preparation(m,x,r,effect));}
        if !ready(m,x,Replica::R3) {assert(needs_preparation(m,x,Replica::R3,effect));}
        enabled_responders_supply_offers(m,b);first::reference_cut(m,b);quorum_from_reference(m,b);
        mail::fair_first_service(m,run,scope,y);mail::finish_or_new_input(m,y,effect);
    }
}

pub proof fn fair_service_or_wire_obstruction<S>(n:Notice,m:Program<S>,first_value_of:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    run:crate::fair_read::Runnable,effect:Relation<State<S>,Event>)
    requires first::startup(m),crate::read_issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] first_service(m,first_value_of,b,run),
        crate::fair_read::fair_majority_availability(m,res,crate::early_crash::entry(m),run),
        crate::fair_read::pending_turns(m,res,crate::early_crash::entry(m),run),
    ensures first::conflict(n,m,first_value_of,res) || obstruction(m,alpha(n),effect) || obstruction(m,beta(n),effect),
{
    if !obstruction(m,alpha(n),effect) && !obstruction(m,beta(n),effect) {
        let a=alpha(n);let b=beta(n);
        assert(first_service(m,first_value_of,a,run) && first_service(m,first_value_of,b,run));
        service_before_either_reply(m,first_value_of,a,run,effect);
        service_before_either_reply(m,first_value_of,b,run,effect);
        assert(first::service_at_offers(m,first_value_of,a) && first::service_at_offers(m,first_value_of,b));
        first::assemble_offers(m,a);crate::early_crash::reachable_independent_call(m,res,a);
        crate::fair_read::fair_progress_offers_service(m,res,crate::early_crash::entry(m),run);
        assert(read::reached(m,crate::early_crash::entry(m),crate::early_crash::cut(m,11)));
        first::pair_with_variable_sr1(n,m,first_value_of,res);
    }
}

// Apply the sequential part of H only to actual returns in each original.
// A pending C2 has no return to account for in this safety condition.
pub open spec fn admits_history<S>(m:Program<S>,first_value_of:spec_fn(S)->int,res:spec_fn(S)->Option<int>,b:Fork) -> bool {
    forall|p:first::ClientPath<S>,nets:Seq<crate::read_call::Net>,actions:Seq<Event>,v:int| first::first_read(m,first_value_of,b,p)
        && #[trigger] crate::service::response_path(first::resumed(m,b,p),res,checkpoint_end(b),delayed_slots(),nets,actions,v)
        ==> {let ret=first::original(m,b,p).states[11+p.actions.len() as int];
            exists|ops:Seq<crate::Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,first_value_of((ret.private)(Process::FirstClient)),v)}
}
proof fn histories_exclude_pair<S>(n:Notice,m:Program<S>,first_value_of:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires admits_history(m,first_value_of,res,alpha(n)),admits_history(m,first_value_of,res,beta(n)),
    ensures !first::conflict(n,m,first_value_of,res),
{
    hide(crate::legal);hide(crate::service::response_path);hide(wait::valid_edges);
    if first::conflict(n,m,first_value_of,res) {
        let (a,b,sa,sb,v)=choose|a:first::ClientPath<S>,b:first::ClientPath<S>,sa:crate::read_call::Log,sb:crate::read_call::Log,v:int|
            #[trigger] first::completed_pair(n,m,first_value_of,res,a,b,sa,sb,v);
        assert(crate::service::response_path(first::resumed(m,alpha(n),a),res,checkpoint_end(alpha(n)),delayed_slots(),sa.nets,sa.actions,v));
        assert(crate::service::response_path(first::resumed(m,beta(n),b),res,checkpoint_end(beta(n)),delayed_slots(),sb.nets,sb.actions,v));
        let (ao,ax)=choose|ao:Seq<crate::Op>,ax:Seq<int>| #[trigger] crate::legal(ao,ax,5,v);
        let (bo,bx)=choose|bo:Seq<crate::Op>,bx:Seq<int>| #[trigger] crate::legal(bo,bx,2,v);
        crate::conditional_history_contradiction(ao,ax,bo,bx,v);
    }
}
pub proof fn h_cost_of_first_service<S>(n:Notice,m:Program<S>,first_value_of:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    run:crate::fair_read::Runnable,effect:Relation<State<S>,Event>)
    requires first::startup(m),crate::read_issue::can_issue(m,res),
        first_service(m,first_value_of,alpha(n),run),first_service(m,first_value_of,beta(n),run),
        admits_history(m,first_value_of,res,alpha(n)),admits_history(m,first_value_of,res,beta(n)),
    ensures ({let x=crate::early_crash::cut(m,11);
        obstruction(m,alpha(n),effect) || obstruction(m,beta(n),effect)
            || (read::reached(m,crate::early_crash::entry(m),x) && read::issued_to_majority(x)
                && !read::returned(res)(x) && !nb::possible(read::service_step(m),read::returned(res),x))}),
{
    let a=alpha(n);let b=beta(n);let x=crate::early_crash::cut(m,11);
    if !obstruction(m,a,effect) && !obstruction(m,b,effect) {
        service_before_either_reply(m,first_value_of,a,run,effect);service_before_either_reply(m,first_value_of,b,run,effect);
        first::assemble_offers(m,a);crate::early_crash::reachable_independent_call(m,res,a);histories_exclude_pair(n,m,first_value_of,res);
        if nb::possible(read::service_step(m),read::returned(res),x) {first::pair_with_variable_sr1(n,m,first_value_of,res);}
    }
}

// A sufficient direct-RPC implementation contract. Check this on the
// transition relation, independently of whether there is a response.
// Other actors and ordinary steps, clocks and arbitrary private metadata
// remain free whenever they do not newly enable the missing local service.
pub open spec fn direct_responder<S>(m:Program<S>,scope:nb::Region<State<S>>,r:Replica,effect:Relation<State<S>,Event>) -> bool {
    forall|x:State<S>,a:Event,y:State<S>| scope(x) && !mail::posted(m)(x) && #[trigger] mail::active_step(m)(x,a,y)
        && !effect(x,a,y) ==> {
            (a is Send && a->Send_1.from==at(r) && first_reply(a->Send_1) ==> native_reply(x,a,r))
            && (ready(m,y,r) ==> ready(m,x,r))
        }
}
proof fn no_extra_preparation<S>(m:Program<S>,x:State<S>,scope:nb::Region<State<S>>,r:Replica,effect:Relation<State<S>,Event>)
    requires scope(x),mail::closed_while_pending(m,scope),direct_responder(m,scope,r,effect),
    ensures !needs_preparation(m,x,r,effect),
{
    let step=mail::active_step(m);let d=mail::posted(m);
    if needs_preparation(m,x,r,effect) {
        let p=choose|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(step,d,x,p) && !wait::uses(p,effect);
        let j=choose|j:int| 0<=j<p.actions.len() && #[trigger] before_consumed_answer(m,p,j,r);
        mail::pending_scope(m,scope,p,j as nat);assert(step(p.states[j],p.actions[j],p.states[j+1]));
        assert(!effect(p.states[j],p.actions[j],p.states[j+1]));
    }
}
pub open spec fn response_interface<S>(m:Program<S>,b:Fork,pre:nb::Region<State<S>>,sent:nb::Region<State<S>>,
    evidence:spec_fn(Packet<Wire>)->bool) -> bool {
    let x=reference(m,b,5);let y=reference(m,b,9);let effect=mail::receipt_of(evidence);
    let run=mail::active_step(m);let d=mail::posted(m);
    two_reporters(m,x) && pre(x) && mail::closed_while_pending(m,pre) && wait::no_await(run,d,pre,effect)
        && (forall|r:Replica| r!=maj::missing(b) ==> #[trigger] direct_responder(m,pre,r,effect))
        && (first::emitted(m,b) ==> sent(y) && mail::closed_while_pending(m,sent)
            && wait::no_await(run,d,sent,effect) && (mail::no_new_ordinary_send(m,sent,evidence)
                || mail::preserves_issued_service(m,sent,first::selected(b),evidence)))
}
pub proof fn direct_majority_service_gives_hot<S>(n:Notice,m:Program<S>,first_value_of:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    run:crate::fair_read::Runnable,evidence:spec_fn(Packet<Wire>)->bool,pre:spec_fn(Fork)->nb::Region<State<S>>,
    sent:spec_fn(Fork)->nb::Region<State<S>>)
    requires first::startup(m),crate::read_issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] first_service(m,first_value_of,b,run) && response_interface(m,b,pre(b),sent(b),evidence),
        crate::fair_read::fair_majority_availability(m,res,crate::early_crash::entry(m),run),
        crate::fair_read::pending_turns(m,res,crate::early_crash::entry(m),run),
    ensures first::conflict(n,m,first_value_of,res),
{
    let e=mail::receipt_of(evidence);
    assert forall|b:Fork| b.notice==n implies ! #[trigger] obstruction(m,b,e) by {
        let x=reference(m,b,5);let y=reference(m,b,9);assert(first_service(m,first_value_of,b,run));
        assert forall|r:Replica| r!=maj::missing(b) implies ! #[trigger] needs_preparation(m,x,r,e) by {
            no_extra_preparation(m,x,pre(b),r,e);
        }
        if first::emitted(m,b) {first::reference_cut(m,b);mail::closed_channel_suffices(m,sent(b),evidence,y);}
    }
    fair_service_or_wire_obstruction(n,m,first_value_of,res,run,e);
}

}
