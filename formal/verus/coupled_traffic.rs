// Cross-run replay of ordinary SR1 work. The source is one native replica
// trace. A delivery schedule names an envelope slot, never an incoming body.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*, protocol::*};
use crate::first_assembly::{self as assembly, Lanes, Service};
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::reference;
use crate::first_splice::{self as tape, Observation, Tape};
use crate::fork_dependencies as dep;
use crate::hybrid_fork as fork;
use crate::independent_read::{self as read, State};
use crate::read_call::{Event, Program};

verus! {

// The source is a registered, returning majority reference. Its client's
// exact private computation can always run last, even if replica replies
// were interleaved with required peer deliveries in the original service.
pub proof fn move_caller_last<S>(m:Program<S>, b:Fork, p:Service<S>, who:fork::Issuer)
    requires cause::returning(m,b,p), fork::native(p,who),
    ensures ({
        let x=reference(m,b,5); let t=tape::record(p,0); let c=Process::FirstClient;
        let replicas=tape::pick(t,c,false); let caller=tape::pick(t,c,true);
        tape::plays(m,x,replicas) && tape::plays(m,tape::after(m,x,replicas),caller)
            && tape::after(m,tape::after(m,x,replicas),caller)==p.states.last()
    }),
{
    let x=reference(m,b,5); let t=tape::record(p,0); let c=Process::FirstClient;
    fork::finite_allocation(p,p,who);
    dep::envelope_lifetimes(m,p,b,fork::allocation(who,p,p));
    tape::recorded(m,p,0);
    assert(tape::reorderable(t,c,false)) by {
        assert forall|i:int,j:int| 0<=i<j<t.len() && (#[trigger] t[i]).actor==c
            && (#[trigger] t[j]).actor!=c implies tape::independent(t[i],t[j]) by {
            let a=p.actions[i]; assert(mail::active_step(m)(p.states[i],a,p.states[i+1]));
            assert(!(a is Send));
        }
    }
    tape::factor_group(m,x,t,c,false);
    tape::concat(m,x,tape::pick(t,c,false),tape::pick(t,c,true));
}

pub type Encoding = spec_fn(Packet<Wire>)->Wire;
pub type Relation<S> = spec_fn(S,S)->bool;

pub open spec fn sampled_reply(v:int) -> Encoding {
    |q:Packet<Wire>| if first_reply(q) {Wire::Reply(v)} else {q.input}
}
pub open spec fn image(f:Encoding, q:Packet<Wire>) -> Packet<Wire> {
    if q.from==at(Replica::R3) && q.path!=Path::Weak {Packet{input:f(q),..q}} else {q}
}
pub open spec fn packet(f:Encoding, q:Option<Packet<Wire>>) -> Option<Packet<Wire>> {
    match q {Some(p)=>Some(image(f,p)),None=>None}
}
pub open spec fn action(f:Encoding, a:Event) -> Event {
    match a {Action::Send(id,q)=>Action::Send(id,image(f,q)), _=>a}
}
pub open spec fn observation(f:Encoding, e:Observation, target_cell:int) -> Observation {
    ProcessStep{action:action(f,e.action),incoming:packet(f,e.incoming),
        own_local:if e.actor==at(Replica::R3) {Some(target_cell)} else {e.own_local},..e}
}
pub open spec fn translated(f:Encoding, t:Tape, v:int) -> Tape {
    t.map_values(|e:Observation| observation(f,e,v))
}

// An altered peer header is admissible only if the actual receive callback
// can consume it with the same effect. A different reply to C1 is private.
// This test is independent of the set of read histories and their outcomes.
pub open spec fn recipient_use<S>(m:Program<S>, f:Encoding) -> bool {
    forall|s:S,e:Observation| survivor_actor(e.actor) && e.action is Deliver && e.incoming.is_some()
        && e.incoming.unwrap().to==e.actor
        && #[trigger] (m.accept)(s,e) ==> {
            let h=observation(f,e,0);
            (m.accept)(s,h) && (m.update)(s,h)==(m.update)(s,e)
        }
}

// The exceptional slots are the two originally issued weak copies and
// R3's real confirmation. None is used by this ordinary preparation.
pub open spec fn weak_queue<S>(x:State<S>, b:Fork) -> bool {
    forall|id:nat| id<=2 ==> #[trigger] x.cfg.net.pending.get(id)==state_after(b,5).pending.get(id)
}
pub open spec fn preparation_input(e:Observation) -> bool {
    e.actor is At && tape::moves(e.action)
        && match tape::slot(e.action) {Some(i)=>i>2 && i!=11 && i!=12,None=>true}
        && match e.action {
            Action::Send(_,q)=>q.path!=Path::Weak,
            Action::Deliver(_)=>e.incoming.is_some() && e.incoming.unwrap().path!=Path::Weak,
            Action::Local(_,w)=>!(w is Copy),
            Action::Strong(_)=>true, _=>false,
        }
}
pub open spec fn paired<S>(x:State<S>, y:State<S>, n:Notice, f:Encoding) -> bool {
    let a=x.cfg.net; let b=y.cfg.net;
    weak_queue(x,alpha(n)) && weak_queue(y,beta(n))
        && a.locals==state_after(alpha(n),5).locals && b.locals==state_after(beta(n),5).locals
        && !a.first_stopped && !a.r3_crashed && !a.second_started && a.unavailable.is_none()
        && !b.first_stopped && !b.r3_crashed && !b.second_started && b.unavailable.is_none()
        && x.owners==y.owners && x.reserved==y.reserved && x.calls==y.calls
        && x.requested==y.requested && x.first_requested==y.first_requested
        && (forall|i:nat| i>2 ==> #[trigger] b.pending.get(i)==packet(f,a.pending.get(i)))
        && (forall|p:Process| p!=at(Replica::R3) ==> #[trigger] (x.cfg.private)(p)==(y.cfg.private)(p))
}
pub proof fn pair_at_fanout<S>(m:Program<S>, l:Lanes,n:Notice,f:Encoding)
    ensures paired(assembly::root(m,l,Some(alpha(n))),assembly::root(m,l,Some(beta(n))),n,f),
{
    let x=assembly::root(m,l,Some(alpha(n)));let y=assembly::root(m,l,Some(beta(n)));
    assert forall|p:Process| p!=at(Replica::R3) implies #[trigger] (x.cfg.private)(p)==(y.cfg.private)(p) by {
        if survivor_actor(p) {arbitrary_survivor_memory_agrees(n,m,p,5);}
        else {
            assert(p==Process::FirstClient);
            assert forall|i:int| 0<=i<5 implies {
                let e=#[trigger] checkpoint_observations(alpha(n))[i];let h=checkpoint_observations(beta(n))[i];
                (e.actor==p || h.actor==p) ==> e==h
            } by {prefix_index(i);}
            reveal_with_fuel(memory,6);
        }
    }
}

// A sufficient rule on the sender's local transition function. The scope
// can restrict this test to the ordinary operations of the read. In
// particular it need not relate the data or strong-private memory of R3.
pub open spec fn sender_control<S>(m:Program<S>, f:Encoding, rel:Relation<S>, scope:spec_fn(Observation)->bool, v:int) -> bool {
    forall|s:S,t:S,e:Observation| #[trigger] rel(s,t) && e.actor==at(Replica::R3)
        && crate::confirmation::transport_event(e) && preparation_input(e) && scope(e) && #[trigger] (m.accept)(s,e) ==> {
            let h=observation(f,e,v);
            (m.accept)(t,h) && rel((m.update)(s,e),(m.update)(t,h))
        }
}

// Transport enabling is unconditional at this point. Only R3 can reject
// the proposed counterpart if an altered peer header passes recipient_use.
proof fn try_input<S>(m:Program<S>,n:Notice,f:Encoding,x:State<S>,y:State<S>,e:Observation)
    requires paired(x,y,n,f), preparation_input(e),recipient_use(m,f),
        process_step(x.cfg.net,e.action)==e, read::service_step(m)(x,e.action,read::next(m,x,e.action)),
    ensures ({
        let h=observation(f,e,2);let b=h.action;let u=read::next(m,x,e.action);let v=read::next(m,y,b);
        process_step(y.cfg.net,b)==h && enabled(y.cfg.net,b) && read::names_sender(y,b)
        && crate::confirmation::fresh_send(b,y.reserved)
        && (!(m.accept)((y.cfg.private)(h.actor),h) ==> h.actor==at(Replica::R3))
        && ((m.accept)((y.cfg.private)(h.actor),h) ==> read::service_step(m)(y,b,v) && paired(u,v,n,f))
    }),
{
    let a=e.action;let h=observation(f,e,2);let b=h.action;
    let u=read::next(m,x,a);let v=read::next(m,y,b);
    if let Action::Deliver(id)=a {
        assert(y.cfg.net.pending.get(id)==Some(image(f,x.cfg.net.pending[id])));
    }
    if let Action::Send(id,q)=a {
        assert(x.cfg.net.pending.get(id)==None);
        assert(y.cfg.net.pending.get(id)==packet(f,x.cfg.net.pending.get(id)));
        assert(!y.cfg.net.pending.contains_key(id));
    }
    assert(process_step(y.cfg.net,b)==h);
    assert forall|r:Replica| #[trigger] (u.cfg.net.locals)(r)==(x.cfg.net.locals)(r)
        && (v.cfg.net.locals)(r)==(y.cfg.net.locals)(r) by {
        if let Some(w)=local_input(x.cfg.net,a,r) {assert(!(w is Copy));}
    }
    assert(u.cfg.net.locals =~= x.cfg.net.locals);assert(v.cfg.net.locals =~= y.cfg.net.locals);
    if e.actor!=at(Replica::R3) {
        let s=(x.cfg.private)(e.actor);assert(s==(y.cfg.private)(e.actor));
        if a is Deliver {assert(survivor_actor(e.actor));assert(h==observation(f,e,0));} else {assert(h==e);}
        assert((m.accept)(s,h) && (m.update)(s,e)==(m.update)(s,h));
    }
    assert forall|i:nat| i>2 implies #[trigger] v.cfg.net.pending.get(i)==packet(f,u.cfg.net.pending.get(i)) by {
        if tape::slot(a)!=Some(i) {assert(v.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));}
    }
    assert forall|p:Process| p!=at(Replica::R3) implies #[trigger] (u.cfg.private)(p)==(v.cfg.private)(p) by {
        assert((x.cfg.private)(p)==(y.cfg.private)(p));
    }
    assert forall|i:nat| i<=2 implies #[trigger] u.cfg.net.pending.get(i)==x.cfg.net.pending.get(i)
        && v.cfg.net.pending.get(i)==y.cfg.net.pending.get(i) by {assert(tape::slot(a)!=Some(i));}
    assert(weak_queue(u,alpha(n)) && weak_queue(v,beta(n)));
    assert(enabled(y.cfg.net,b));
    assert(read::names_sender(y,b));
    assert(crate::confirmation::fresh_send(b,y.reserved));
    assert(paired(u,v,n,f));
}

pub open spec fn fitted(t:Tape,scope:spec_fn(Observation)->bool) -> bool {
    forall|i:int| 0<=i<t.len() ==> preparation_input(#[trigger] t[i]) && scope(t[i])
}
pub open spec fn at_cut<S>(m:Program<S>,x:State<S>,t:Tape,k:nat) -> State<S> {
    tape::after(m,x,t.take(k as int))
}

// Maximal replay of the given ordinary preparation. No paired trace is an
// input. If it stops, the first failure is an actual target R3 guard, on
// a physically enabled translated action and the target's own queued input.
pub proof fn replay_preparation<S>(m:Program<S>,n:Notice,f:Encoding,scope:spec_fn(Observation)->bool,rel:Relation<S>,
    x:State<S>,y:State<S>,t:Tape) -> (k:nat)
    requires paired(x,y,n,f),tape::plays(m,x,t),fitted(t,scope),recipient_use(m,f),
    ensures k<=t.len(), ({
        let u=translated(f,t,2);let s=at_cut(m,x,t,k);let z=at_cut(m,y,u,k);
        tape::plays(m,y,u.take(k as int)) && paired(s,z,n,f)
        && (k<t.len() ==> {
            let e=t[k as int];let h=u[k as int];let p=at(Replica::R3);
            e.actor==p && h.actor==p && (m.accept)((s.cfg.private)(p),e)
                && process_step(z.cfg.net,h.action)==h && enabled(z.cfg.net,h.action)
                && !(m.accept)((z.cfg.private)(p),h)
        })
        && (sender_control(m,f,rel,scope,2) && rel((x.cfg.private)(at(Replica::R3)),(y.cfg.private)(at(Replica::R3)))
            ==> k==t.len())
    }),
    decreases t.len(),
{
    let u=translated(f,t,2);
    if t.len()==0 {assert(t.take(0) =~= Seq::<Observation>::empty());assert(u.take(0) =~= t);0}
    else {
        let e=t[0];let h=u[0];let s=read::next(m,x,e.action);let z=read::next(m,y,h.action);
        assert(crate::confirmation::transport_event(e)) by {
            assert(enabled(x.cfg.net,e.action) && process_step(x.cfg.net,e.action)==e);
        }
        try_input(m,n,f,x,y,e);
        if !(m.accept)((y.cfg.private)(h.actor),h) {
            assert(t.take(0) =~= Seq::<Observation>::empty());assert(u.take(0) =~= t.take(0));0
        } else {
            let tail=t.drop_first();
            assert(fitted(tail,scope)) by {assert forall|i:int| 0<=i<tail.len() implies preparation_input(#[trigger] tail[i]) && scope(tail[i]) by {assert(tail[i]==t[i+1]);}}
            assert(translated(f,tail,2) =~= u.drop_first());
            let r=at(Replica::R3);
            if sender_control(m,f,rel,scope,2) && rel((x.cfg.private)(r),(y.cfg.private)(r)) {
                assert(rel((s.cfg.private)(r),(z.cfg.private)(r)));
            }
            let j=replay_preparation(m,n,f,scope,rel,s,z,tail);let k=j+1;
            assert(t.take(k as int)[0]==e && t.take(k as int).drop_first() =~= tail.take(j as int));
            assert(u.take(k as int)[0]==h && u.take(k as int).drop_first() =~= u.drop_first().take(j as int));
            if k<t.len() {assert(t[k as int]==tail[j as int] && u[k as int]==u.drop_first()[j as int]);}
            k
        }
    }
}
}
