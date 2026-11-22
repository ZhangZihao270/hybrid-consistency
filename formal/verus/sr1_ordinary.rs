// Deleting one receipt on a real majority reference. All later ordinary
// traffic, clocks and local work in the reference are tried in their order.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::confirmation::fresh_send;
use crate::fair_read as fair;
use crate::first_assembly::Service;
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::{self as first, reference};
use crate::first_service_loss as loss;
use crate::first_splice::{self as s, Tape};
use crate::fork_dependencies as dep;
use crate::hybrid_fork as fork;
use crate::hybrid_majority as model;
use crate::hybrid_transparency as trans;
use crate::independent_read::{self as read, State};
use crate::promotion_wait as wait;
use crate::read_call::{Net, Event, Program};
use crate::read_nonblocking as nb;

verus! {

pub open spec fn weak_free_return<S>(m:Program<S>, b:Fork, audit:trans::PacketAudit, p:Service<S>) -> bool {
    wait::first_return(trans::without_weak(m,b,audit),mail::posted(m),reference(m,b,5),p)
}
pub(crate) proof fn ordinary_edges<S>(m:Program<S>, b:Fork, audit:trans::PacketAudit, p:Service<S>)
    requires weak_free_return(m,b,audit,p),
    ensures cause::returning(m,b,p), !wait::uses(p,dep::promotion(b)), !wait::uses(p,mail::receipt_of(audit)),
{
    let st=trans::without_weak(m,b,audit);
    assert forall|j:int| 0<=j<p.actions.len() implies mail::active_step(m)(p.states[j],#[trigger] p.actions[j],p.states[j+1])
        && !dep::promotion(b)(p.states[j],p.actions[j],p.states[j+1])
        && !mail::receipt_of(audit)(p.states[j],p.actions[j],p.states[j+1]) by {
        assert(st(p.states[j],p.actions[j],p.states[j+1]));
    }
}
pub proof fn service_with_ordinary_traffic<S>(m:Program<S>, b:Fork, res:spec_fn(S)->Option<int>, run:fair::Runnable,
    audit:trans::PacketAudit) -> (p:Service<S>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b), trans::no_first_wait(m,b,audit),
        model::eventual(m,res,reference(m,b,0),run), mail::fair_opportunity(m,run,reference(m,b,5)),
    ensures weak_free_return(m,b,audit,p),
{
    let x=reference(m,b,5);let st=mail::active_step(m);let d=mail::posted(m);
    model::availability_at_both_clients(m,res,reference(m,b,0),run);
    dispatch::fanout_and_weak_open_launch(m,b);dispatch::launch_cut(m,b);
    loss::finite_service(m,b,run);
    let path=choose|p:Service<S>| #[trigger] cause::returning(m,b,p);
    let effect=trans::weak_work(b,audit);
    let p=wait::extract_without_promotion(st,d,first::reached_in(m,b),effect,x,path);
    assert forall|j:int| 0<=j<p.actions.len() implies
        trans::without_weak(m,b,audit)(p.states[j],#[trigger] p.actions[j],p.states[j+1]) by {
        assert(st(p.states[j],p.actions[j],p.states[j+1]));
        assert(!effect(p.states[j],p.actions[j],p.states[j+1]));
    }
    p
}

pub open spec fn shortest<S>(m:Program<S>, b:Fork, audit:trans::PacketAudit, p:Service<S>) -> bool {
    weak_free_return(m,b,audit,p) && forall|u:Service<S>| #[trigger] weak_free_return(m,b,audit,u) ==> p.actions.len()<=u.actions.len()
}
pub(crate) proof fn minimize<S>(m:Program<S>, b:Fork, audit:trans::PacketAudit, p:Service<S>) -> (q:Service<S>)
    requires weak_free_return(m,b,audit,p),
    ensures shortest(m,b,audit,q),
    decreases p.actions.len(),
{
    if exists|u:Service<S>| #[trigger] weak_free_return(m,b,audit,u) && u.actions.len()<p.actions.len() {
        minimize(m,b,audit,choose|u:Service<S>| #[trigger] weak_free_return(m,b,audit,u) && u.actions.len()<p.actions.len())
    } else {p}
}
proof fn prefix_bound<S>(st:wait::Relation<State<S>,Event>,d:nb::Region<State<S>>,p:Service<S>,i:nat,k:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(st,p),i<=p.actions.len(),nb::within(st,d,p.states[i as int],k),
    ensures nb::within(st,d,p.states[0],k+i),
    decreases i,
{
    if i>0 {let j=(i-1) as nat;assert(st(p.states[j as int],p.actions[j as int],p.states[i as int]));
        assert(nb::within(st,d,p.states[j as int],k+1));prefix_bound(st,d,p,j,k+1);}
}

// The state with the receipt withheld has exactly one extra queued
// envelope. Only the recipient's private memory may differ.
pub open spec fn held<S>(x:State<S>,y:State<S>,id:nat,q:Packet<Wire>) -> bool {
    !y.cfg.net.pending.contains_key(id)
    && x.cfg.net==(Net{pending:y.cfg.net.pending.insert(id,q),..y.cfg.net})
    && x==(State{cfg:x.cfg,..y})
    && forall|p:Process| p!=q.to ==> #[trigger] (x.cfg.private)(p)==(y.cfg.private)(p)
}

proof fn skip_receipt<S>(m:Program<S>,b:Fork,x:State<S>,a:Event,y:State<S>)
    requires mail::active_step(m)(x,a,y),dep::crossing(b,x,a),!cause::changes_sample(b,x,y),
    ensures a is Deliver,held(x,y,a->Deliver_0,x.cfg.net.pending[a->Deliver_0]),
{
    let id=a->Deliver_0;let q=x.cfg.net.pending[id];assert(q.to==at(crate::origin(b.branch)));
    assert(x.cfg.net.pending =~= y.cfg.net.pending.insert(id,q));
    assert(x.cfg.net.locals =~= y.cfg.net.locals) by {
        assert forall|r:Replica| #[trigger] (x.cfg.net.locals)(r)==(y.cfg.net.locals)(r) by {
            if at(r)!=q.to {assert(local_input(x.cfg.net,a,r).is_none());}
            else {assert(cause::quorum(b,r));}
        }
    }
}

// Network enabling and all protocol guards except possibly the recipient's
// are preserved. The trial reads the envelope in its own queue.
proof fn try_step<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit,x:State<S>,y:State<S>,a:Event,z:State<S>,id:nat,q:Packet<Wire>)
    requires held(x,y,id,q),q.to==at(crate::origin(b.branch)),s::slot(a)!=Some(id),s::moves(a),
        trans::without_weak(m,b,audit)(y,a,z),
    ensures ({
        let e=process_step(y.cfg.net,a);let u=read::next(m,x,a);let ok=(m.accept)((x.cfg.private)(e.actor),e);
        process_step(x.cfg.net,a)==e && enabled(x.cfg.net,a) && read::names_sender(x,a) && fresh_send(a,x.reserved)
            && (m.accept)((y.cfg.private)(e.actor),e) && (!ok ==> e.actor==q.to)
            && (ok ==> trans::without_weak(m,b,audit)(x,a,u) && held(u,z,id,q))
    }),
{
    let e=process_step(y.cfg.net,a);let u=read::next(m,x,a);
    if let Action::Deliver(j)=a {assert(x.cfg.net.pending.get(j)==y.cfg.net.pending.get(j));}
    if let Action::Send(j,_)=a {assert(x.cfg.net.pending.get(j)==y.cfg.net.pending.get(j));}
    assert(process_step(x.cfg.net,a)==e);
    assert(u.cfg.net.pending =~= z.cfg.net.pending.insert(id,q));
    assert(u.cfg.net.locals =~= z.cfg.net.locals) by {
        assert forall|r:Replica| #[trigger] local_input(x.cfg.net,a,r)==local_input(y.cfg.net,a,r) by {}
    }
    if (m.accept)((x.cfg.private)(e.actor),e) {
        assert(mail::active_step(m)(x,a,u));assert(!dep::promotion(b)(x,a,u));
        assert(!mail::receipt_of(audit)(x,a,u));
        assert forall|p:Process| p!=q.to implies #[trigger] (u.cfg.private)(p)==(z.cfg.private)(p) by {
            assert((x.cfg.private)(p)==(y.cfg.private)(p));
        }
    }
}

// Same local input, protocol-accepted on the source and protocol-rejected
// on its genuine replay prefix. Every preceding callback was accepted.
pub open spec fn refuses<S>(m:Program<S>,p:Service<S>,j:int,k:int,x:State<S>,id:nat,q:Packet<Wire>) -> bool {
    let tape=s::record(p,0);let prefix=tape.subrange(j,k);let before=s::after(m,x,prefix);
    let source=p.states[k];let a=p.actions[k];let e=tape[k];
    s::plays(m,x,prefix) && held(before,source,id,q) && e.actor==q.to
        && process_step(before.cfg.net,a)==e && enabled(before.cfg.net,a)
        && read::names_sender(before,a) && fresh_send(a,before.reserved)
        && (m.accept)((source.cfg.private)(e.actor),e) && !(m.accept)((before.cfg.private)(e.actor),e)
}

proof fn first_refusal<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit,p:Service<S>,j:nat,x:State<S>,id:nat,q:Packet<Wire>)
    -> (k:nat)
    requires weak_free_return(m,b,audit,p),j<=p.actions.len(),q.to==at(crate::origin(b.branch)),held(x,p.states[j as int],id,q),
        forall|h:int| j<=h<p.actions.len() ==> s::slot(#[trigger] p.actions[h])!=Some(id),
        !nb::within(trans::without_weak(m,b,audit),mail::posted(m),x,(p.actions.len()-j) as nat),
    ensures j<=k<p.actions.len(),refuses(m,p,j as int,k as int,x,id,q),
    decreases p.actions.len()-j,
{
    let y=p.states[j as int];let d=mail::posted(m);let st=trans::without_weak(m,b,audit);let t=s::record(p,0);
    assert((x.cfg.private)(Process::FirstClient)==(y.cfg.private)(Process::FirstClient));
    if j==p.actions.len() {assert(d(x));assert(nb::within(st,d,x,0));}
    let a=p.actions[j as int];let e=t[j as int];let z=p.states[j as int+1];let u=read::next(m,x,a);
    assert(st(y,a,z));assert(!d(y));assert(s::moves(a));assert(s::slot(a)!=Some(id));
    try_step(m,b,audit,x,y,a,z,id,q);
    if !(m.accept)((x.cfg.private)(e.actor),e) {
        assert(t.subrange(j as int,j as int) =~= Seq::empty());j
    } else {
        assert(st(x,a,u));let remaining=(p.actions.len()-j-1) as nat;
        if nb::within(st,d,u,remaining) {assert(nb::within(st,d,x,remaining+1));}
        let k=first_refusal(m,b,audit,p,j+1,u,id,q);
        let span=t.subrange(j as int,k as int);
        assert(span[0]==e && span.drop_first() =~= t.subrange(j as int+1,k as int));k
    }
}

// A justification for an ordinary message can now be challenged at the
// precise guard. A mere difference between two private memories is weaker.
pub proof fn shortest_receipt_requires_guard<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit,p:Service<S>,who:fork::Issuer,i:nat)
    -> (k:nat)
    requires shortest(m,b,audit,p),fork::native(p,who),i<p.actions.len(),
        dep::crossing(b,p.states[i as int],p.actions[i as int]),!cause::changes_sample(b,p.states[i as int],p.states[i as int+1]),
    ensures i<k<p.actions.len(), ({
        let a=p.actions[i as int];let x=p.states[i as int];let id=a->Deliver_0;
        refuses(m,p,i as int+1,k as int,x,id,x.cfg.net.pending[id])
    }),
{
    ordinary_edges(m,b,audit,p);fork::finite_allocation(p,p,who);
    dep::envelope_lifetimes(m,p,b,fork::allocation(who,p,p));
    let a=p.actions[i as int];let x=p.states[i as int];let y=p.states[i as int+1];
    let st=trans::without_weak(m,b,audit);let d=mail::posted(m);let t=s::record(p,0);
    assert(st(x,a,y));skip_receipt(m,b,x,a,y);let id=a->Deliver_0;let q=x.cfg.net.pending[id];
    assert forall|j:int| i<j<p.actions.len() implies s::slot(#[trigger] p.actions[j])!=Some(id) by {
        assert(t[i as int].action==a && t[j].action==p.actions[j]);
        if s::slot(p.actions[j])==Some(id) {assert(t[i as int].action is Send);}
    }
    let budget=(p.actions.len()-i-1) as nat;
    if nb::within(st,d,x,budget) {
        prefix_bound(st,d,p,i,budget);
        let u=nb::to_path(st,d,p.states[0],budget+i);assert(weak_free_return(m,b,audit,u));
        assert(p.actions.len()<=u.actions.len());
    }
    first_refusal(m,b,audit,p,i+1,x,id,q)
}

// A sufficient local test for dropping private bookkeeping. It compares
// acceptance and updates at one replica. It says nothing about return
// values, histories at C1, or how many instructions a read will take.
pub type Relation<S> = spec_fn(Replica,S,S)->bool;
pub open spec fn follows<S>(m:Program<S>,rel:Relation<S>) -> bool {
    forall|r:Replica,s:S,t:S,e:s::Observation| #[trigger] rel(r,s,t) && e.actor==at(r) && #[trigger] (m.accept)(t,e)
        ==> (m.accept)(s,e) && rel(r,(m.update)(s,e),(m.update)(t,e))
}
proof fn segment<S>(m:Program<S>,b:Fork,p:Service<S>,lo:nat,hi:nat)
    requires cause::returning(m,b,p),lo<=hi<=p.actions.len(),
    ensures ({let t=s::record(p,0).subrange(lo as int,hi as int);let x=p.states[lo as int];
        s::plays(m,x,t) && s::after(m,x,t)==p.states[hi as int]}),
    decreases hi-lo,
{
    let sub=s::record(p,0).subrange(lo as int,hi as int);
    if lo<hi {
        segment(m,b,p,lo+1,hi);
        assert(sub.drop_first() =~= s::record(p,0).subrange(lo as int+1,hi as int));
        assert(mail::active_step(m)(p.states[lo as int],sub[0].action,p.states[lo as int+1]));
        assert(!mail::posted(m)(p.states[lo as int]));assert(s::moves(sub[0].action));
    }
}
proof fn follows_trace<S>(m:Program<S>,rel:Relation<S>,r:Replica,x:State<S>,y:State<S>,t:Tape)
    requires follows(m,rel),s::plays(m,x,t),s::plays(m,y,t),rel(r,(x.cfg.private)(at(r)),(y.cfg.private)(at(r))),
    ensures rel(r,(s::after(m,x,t).cfg.private)(at(r)),(s::after(m,y,t).cfg.private)(at(r))),
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let actor=at(r);let u=read::next(m,x,e.action);let v=read::next(m,y,e.action);
        if e.actor==actor {
            assert((m.accept)((y.cfg.private)(actor),e));
            assert(rel(r,(m.update)((x.cfg.private)(actor),e),(m.update)((y.cfg.private)(actor),e)));
        }
        follows_trace(m,rel,r,u,v,t.drop_first());
    }
}
pub proof fn refusal_separates_local_memories<S>(m:Program<S>,b:Fork,p:Service<S>,i:int,k:int,rel:Relation<S>)
    requires cause::returning(m,b,p),0<=i<k<p.actions.len(),follows(m,rel),
        dep::crossing(b,p.states[i],p.actions[i]),
        ({let x=p.states[i];let id=p.actions[i]->Deliver_0;refuses(m,p,i+1,k,x,id,x.cfg.net.pending[id])}),
    ensures ({let r=crate::origin(b.branch);!rel(r,(p.states[i].cfg.private)(at(r)),(p.states[i+1].cfg.private)(at(r)))}),
{
    let r=crate::origin(b.branch);let actor=at(r);let x=p.states[i];let y=p.states[i+1];
    if rel(r,(x.cfg.private)(actor),(y.cfg.private)(actor)) {
        let t=s::record(p,0).subrange(i+1,k);let u=s::after(m,x,t);let z=p.states[k];let e=s::record(p,0)[k];
        segment(m,b,p,(i+1) as nat,k as nat);follows_trace(m,rel,r,x,y,t);
        assert(e.actor==actor);assert((m.accept)((z.cfg.private)(actor),e));
        assert((m.accept)((u.cfg.private)(actor),e));
    }
}

}
