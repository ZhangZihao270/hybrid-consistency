use vstd::prelude::*;
use crate::{Branch,Replica,origin};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Packet,Process,ProcessStep,observations};
use crate::protocol::{LocalProtocol,accepted,memory};
use crate::ordinary_service::{Configuration,allowed,apply};
use crate::fanout_service::{done,reaches,reached,run_step};
use crate::promotion_wait::{self as wait,Path};

verus! {

type Machine<S> = LocalProtocol<S,int,Wire>;
pub type C<S> = Configuration<S>;
pub type Event = Action<Wire>;

// b names the origin whose reply C1 receives first. In this auxiliary
// schedule R3 receives the OTHER weak write first. Both receipts attest
// only replication. The two writes have independent original invocations.
pub open spec fn rival(b:Fork) -> Fork {
    if b.branch==Branch::Alpha {beta(Notice::Replication)} else {alpha(Notice::Replication)}
}
pub open spec fn copy_id(b:Fork) -> nat { if b.branch==Branch::Alpha {1} else {0} }
pub open spec fn reply_id(b:Fork) -> nat { if b.branch==Branch::Alpha {7} else {6} }
pub open spec fn receipt(b:Fork) -> Packet<Wire> {
    Packet {path:delivery::Path::Weak,from:at(Replica::R3),to:at(origin(b.branch)),input:Wire::WeakConfirm(Notice::Replication)}
}
pub open spec fn action(b:Fork,k:nat) -> Event {
    if k<10 {actions_to_crash(rival(b))[k as int]}
    else if k==10 {Action::Deliver(reply_id(b))}
    else if k==11 {Action::Deliver(copy_id(b))}
    else if k==12 {Action::Send(9,receipt(b))}
    else if k==13 {actions_to_crash(b)[10]}
    else {actions_to_crash(b)[k-2]}
}
pub open spec fn net(b:Fork,k:nat) -> Network<int,Wire> {
    if k<=10 {state_after(rival(b),k)} else {
        let before=state_after(rival(b),10);
        let queued=before.pending.remove(reply_id(b));
        let queued=if k>=12 {queued.remove(copy_id(b))} else {queued};
        let queued=if k>=13 {queued.insert(9,receipt(b))} else {queued};
        let queued=if k==14 {queued.insert(8,packet_for(b,8))} else {queued};
        Network {pending:queued,locals:if k>=12 {state_after(b,12).locals} else {before.locals},
            first_stopped:k>=17,r3_crashed:k>=18,second_started:k>=19,..before}
    }
}
pub open spec fn actions(b:Fork) -> Seq<Event> { Seq::new(19,|i:int|action(b,i as nat)) }
pub open spec fn states(b:Fork) -> Seq<Network<int,Wire>> { Seq::new(20,|i:int|net(b,i as nat)) }
pub open spec fn events(b:Fork) -> Seq<ProcessStep<int,Wire>> { observations(states(b),actions(b)) }
pub open spec fn cfg<S>(m:Machine<S>,b:Fork,k:nat) -> C<S> {
    C {net:net(b,k),private:|p|memory(m,p,events(b),k)}
}
pub open spec fn segment<S>(m:Machine<S>,b:Fork,lo:nat,hi:nat) -> Path<C<S>,Event> {
    Path {states:Seq::new((hi-lo+1) as nat,|i:int|cfg(m,b,lo+i as nat)),
        actions:Seq::new((hi-lo) as nat,|i:int|action(b,lo+i as nat))}
}
pub proof fn transport(b:Fork)
    ensures delivery::trace(|x,w|cell(x,w),states(b),actions(b)),net(b,0)==after_local_rmws(),
        invocation_only(actions(b),Process::FirstClient,all_replicas()),
        net(b,11).pending.get(copy_id(b))==Some(packet_for(b,copy_id(b))),
        !net(b,11).pending.contains_key(8) && (net(b,11).locals)(Replica::R3)==first_value(rival(b)),
        (forall|k:int| 0<=k<11 ==> {
            let e=#[trigger] events(b)[k];
            e.actor==at(Replica::R3) && e.incoming.is_some() ==> e.incoming.unwrap().input!=Wire::Copy(first_value(b))
        }),
        net(b,11).pending.get(reply_id(rival(b)))==Some(packet_for(b,reply_id(rival(b)))),
        net(b,19).pending.get(2)==Some(receipt(rival(b))),net(b,19).pending.get(9)==Some(receipt(b)),
        net(b,19).pending.get(reply_id(rival(b)))==Some(packet_for(b,reply_id(rival(b)))),
        net(b,19).r3_crashed && net(b,19).first_stopped && net(b,19).second_started,
{
    prefix_transport_is_enabled(rival(b));
    assert forall|i:int| 0<=i<19 implies {
        let a=#[trigger] actions(b)[i];let n=states(b)[i];
        delivery::enabled(n,a) && states(b)[i+1]==delivery::advance(|x,w|cell(x,w),n,a)
    } by {
        if i<10 {prefix_index(i);} else if i<17 {prefix_index(i);}
        let u=delivery::advance(|x,w|cell(x,w),states(b)[i],actions(b)[i]);
        assert(u.locals =~= states(b)[i+1].locals);assert(u.pending =~= states(b)[i+1].pending);
    }
    assert forall|k:int| 0<=k<11 implies {
        let e=#[trigger] events(b)[k];
        e.actor==at(Replica::R3) && e.incoming.is_some() ==> e.incoming.unwrap().input!=Wire::Copy(first_value(b))
    } by {prefix_index(k);}
    let c=Process::FirstClient;
    assert forall|i:int| 0<=i<19 implies match #[trigger] actions(b)[i] {
        Action::Send(_,p) if p.from==c=>invocation_packet(p) && all_replicas().contains(p.to->At_0)
            && (forall|j:int| 0<=j<i ==> !client_sends_to(#[trigger] actions(b)[j],c,p.to->At_0)),
        _=>true,
    } by {if i<17 {prefix_index(i);}}
    assert forall|r:Replica| #[trigger] all_replicas().contains(r) implies exists|i:int| 0<=i<19
        && client_sends_to(#[trigger] actions(b)[i],c,r) by {
        let i:int=if r==Replica::R1 {2} else if r==Replica::R2 {3} else {4};
        assert(client_sends_to(actions(b)[i],c,r));
    }
}

// Every non-R3 process has its exact local history from original b.
// Counting the unobserved steps differently accounts for both deliveries.
pub open spec fn original_time(k:nat) -> nat { if k<=10 {k} else if k<=14 {12} else {(k-2) as nat} }
pub proof fn same_private<S>(m:Machine<S>,b:Fork,p:Process,k:nat)
    requires k<=19,p!=at(Replica::R3),
    ensures (cfg(m,b,k).private)(p)==memory(m,p,checkpoint_observations(b),original_time(k)),
    decreases k,
{
    if k>0 {
        let j=(k-1) as nat;same_private(m,b,p,j);
        if j<17 {prefix_index(j as int);}
        if j==10 {
            assert(checkpoint_observations(b)[10].actor==at(Replica::R3));
            reveal_with_fuel(memory,2);
        }
    }
}
pub proof fn prior_r3<S>(m:Machine<S>,b:Fork,k:nat)
    requires k<=11,
    ensures (cfg(m,b,k).private)(at(Replica::R3))==memory(m,at(Replica::R3),checkpoint_observations(rival(b)),if k<=10 {k} else {10}),
    decreases k,
{
    if k>0 {let j=(k-1) as nat;prior_r3(m,b,j);prefix_index(j as int);}
}
pub open spec fn guard<S>(m:Machine<S>,b:Fork,k:nat) -> bool {
    let e=events(b)[k as int]; (m.accept)((cfg(m,b,k).private)(e.actor),e)
}
pub(crate) proof fn projected_step<S>(m:Machine<S>,b:Fork,k:nat)
    requires k<19,guard(m,b,k),
    ensures allowed(m,cfg(m,b,k),action(b,k)),apply(m,cfg(m,b,k),action(b,k))==cfg(m,b,k+1),
{
    transport(b);let s=cfg(m,b,k);let a=action(b,k);
    assert(states(b)[k as int]==s.net && actions(b)[k as int]==a);
    assert(apply(m,s,a).private =~= cfg(m,b,k+1).private);
}
pub proof fn inherited_guard<S>(m:Machine<S>,b:Fork,k:nat)
    requires accepted(m,checkpoint_observations(b)),accepted(m,checkpoint_observations(rival(b))),
        k<19,k!=11,k!=12,k!=13,k!=17,
    ensures guard(m,b,k),
{
    if k<17 {prefix_index(k as int);}
    let e=events(b)[k as int];
    if e.actor==at(Replica::R3) {
        prior_r3(m,b,k);
        assert(e==checkpoint_observations(rival(b))[k as int]);
    } else {
        same_private(m,b,e.actor,k);
        let original=if k==10 {11nat} else {original_time(k)};
        assert(e==checkpoint_observations(b)[original as int]);
        if k==10 { assert(checkpoint_observations(b)[10].actor!=e.actor); }
        assert((m.accept)(memory(m,e.actor,checkpoint_observations(b),original),e));
    }
}

// The cut needs no new callback premise. Through the first return only
// R3's acceptance of the second installation, its receipt send, and its
// subsequent ordinary reply are new. A different protocol may need work
// at these points. No delivery of either notice is required by this witness.
pub proof fn cut_reachable<S>(m:Machine<S>,b:Fork)
    requires accepted(m,checkpoint_observations(b)),accepted(m,checkpoint_observations(rival(b))),
    ensures reached(m,cfg(m,b,11)),
{
    transport(b);let p=segment(m,b,0,11);
    assert(p.states[0].private =~= m.initial);
    assert forall|i:int| 0<=i<11 implies allowed(m,p.states[i],#[trigger] p.actions[i]) && p.states[i+1]==apply(m,p.states[i],p.actions[i])
        by {inherited_guard(m,b,i as nat);projected_step(m,b,i as nat);}
    assert(reaches(m,cfg(m,b,11),p));
}
pub proof fn first_return_after_second_copy<S>(m:Machine<S>,b:Fork,value:spec_fn(S)->int)
    requires accepted(m,checkpoint_observations(b)),accepted(m,checkpoint_observations(rival(b))),completed_quorum_sample(m,value,b),
        guard(m,b,11),guard(m,b,12),guard(m,b,13),
    ensures ({
        let end=first_return_len(m,b)+2;let p=segment(m,b,11,end);
        wait::first_return(run_step(m),done(m),cfg(m,b,11),p)
            && value((p.states.last().private)(Process::FirstClient))==first_value(b)
    }),
{
    let c=Process::FirstClient;let end=first_return_len(m,b)+2;let p=segment(m,b,11,end);
    assert forall|i:int| 0<=i<p.actions.len() implies run_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
        let k=11+i as nat;if k>=14 {inherited_guard(m,b,k);}
        projected_step(m,b,k);prefix_index(k as int);
    }
    assert(wait::valid_edges(run_step(m),p));
    assert forall|i:int| 0<=i<p.actions.len() implies !done(m)(#[trigger] p.states[i]) by {
        let k=11+i as nat;same_private(m,b,c,k);
        if k<=14 {assert(!(m.done)(first_client_at(m,b,12)));}
    }
    same_private(m,b,c,11);same_private(m,b,c,end);assert(!(m.done)(first_client_at(m,b,12)));
    stable_responder_cells_fix_first_sample(m,value,b);
}
// The R3 work need not have the length or the receipt format of the
// explicit witness. It may deliver mandatory traffic and change survivor
// state. We reuse C1's original guard only while its own history is intact.
pub open spec fn preparation<S>(m:Machine<S>,b:Fork,p:Path<C<S>,Event>) -> bool {
    p.states.len()==p.actions.len()+1 && p.states[0]==cfg(m,b,11) && wait::valid_edges(run_step(m),p)
        && forall|i:int| 0<=i<p.actions.len() ==> delivery::process_step(p.states[i].net,#[trigger] p.actions[i]).actor!=Process::FirstClient
}
pub open spec fn sample<S>(s:C<S>) -> Event {
    send(8,delivery::Path::FirstReadReply,at(Replica::R3),Process::FirstClient,Wire::Reply((s.net.locals)(Replica::R3)))
}
proof fn client_through<S>(m:Machine<S>,b:Fork,p:Path<C<S>,Event>,k:nat)
    requires preparation(m,b,p),k<=p.actions.len(),
    ensures (p.states[k as int].private)(Process::FirstClient)==first_client_at(m,b,12),
        !p.states[k as int].net.first_stopped,
    decreases k,
{
    if k==0 {same_private(m,b,Process::FirstClient,11);}
    else {
        let i=(k-1) as nat;client_through(m,b,p,i);
        assert(run_step(m)(p.states[i as int],p.actions[i as int],p.states[k as int]));
        assert(delivery::process_step(p.states[i as int].net,p.actions[i as int]).actor!=Process::FirstClient);
    }
}

pub proof fn completed_from_prepared_sample<S>(m:Machine<S>,value:spec_fn(S)->int,b:Fork,prep:Path<C<S>,Event>) -> (p:Path<C<S>,Event>)
    requires accepted(m,checkpoint_observations(b)),completed_quorum_sample(m,value,b),preparation(m,b,prep),
        (prep.states.last().net.locals)(Replica::R3)==first_value(b),allowed(m,prep.states.last(),sample(prep.states.last())),
    ensures wait::first_return(run_step(m),done(m),cfg(m,b,11),p),
        value((p.states.last().private)(Process::FirstClient))==first_value(b),
        p.actions==prep.actions+seq![sample(prep.states.last()),Action::Deliver(8)]
            +(if first_return_len(m,b)==13 {seq![]} else {seq![Action::Strong(Process::FirstClient)]}),
        p.states.last().net.pending==prep.states.last().net.pending,
{
    let k=prep.actions.len();let s=prep.states.last();let c=Process::FirstClient;
    client_through(m,b,prep,k);
    let emit=sample(s);let u=apply(m,s,emit);let take=Action::Deliver(8);let v=apply(m,u,take);
    let poll=Action::Strong(c);let z=apply(m,v,poll);let es=checkpoint_observations(b);
    assert(delivery::process_step(u.net,take)==es[12] && (u.private)(c)==first_client_at(m,b,12));
    assert((m.accept)(memory(m,c,es,12),es[12]));
    assert(run_step(m)(u,take,v));assert((v.private)(c)==first_client_at(m,b,13));
    let early=first_return_len(m,b)==13;
    if !early {
        assert(delivery::process_step(v.net,poll)==es[13]);assert((m.accept)(memory(m,c,es,13),es[13]));
        assert(run_step(m)(v,poll,z));assert((z.private)(c)==first_client_at(m,b,14));
    }
    let p=Path{states:prep.states+seq![u,v]+(if early {seq![]} else {seq![z]}),
        actions:prep.actions+seq![emit,take]+(if early {seq![]} else {seq![poll]})};
    assert forall|i:int| 0<=i<p.actions.len() implies run_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        && !done(m)(p.states[i]) by {
        if i<k {assert(run_step(m)(prep.states[i],prep.actions[i],prep.states[i+1]));client_through(m,b,prep,i as nat);}
        else {assert(i==k || i==k+1 || i==k+2);}
    }
    assert(wait::valid_edges(run_step(m),p));
    assert forall|i:int| 0<=i<p.actions.len() implies !done(m)(#[trigger] p.states[i]) by {
        assert(run_step(m)(p.states[i],p.actions[i],p.states[i+1]) && !done(m)(p.states[i]));
    }
    assert(p.states[0]==cfg(m,b,11));assert(p.states.len()==p.actions.len()+1);
    assert(!done(m)(p.states[0]) && done(m)(p.states.last()));
    assert(p.states.last().net.pending =~= s.net.pending);
    stable_responder_cells_fix_first_sample(m,value,b);p
}

}
