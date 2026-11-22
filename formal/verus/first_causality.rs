// Source-trace interfaces. The quorum-value rule concerns the shared cells;
// reply provenance is independent of the representation of their values.
use vstd::prelude::*;
use crate::{Branch,Replica,checkpoint::*,delivery::*,protocol::*};
use crate::first_assembly::*;
use crate::first_splice::{self as s,Tape,Observation,pick};
use crate::first_schedule::{self as first,reference};
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::independent_read::State;
use crate::promotion_wait as wait;
use crate::read_call::{Program,Event};
use crate::sr1_majorities as maj;

verus! {

// A sufficient interface for using native single-use envelope identities.
// It is needed only on the slice being scheduled. The more general splice
// accepts name reuse when no inverted pair of operations conflicts on it.
pub open spec fn routed(e:Observation,b:Fork,l:Lanes) -> bool {
    let id=s::slot(e.action);let r=crate::origin(b.branch);
    if e.actor==at(r) {id.is_none() || names(l,r).contains(id.unwrap())} else {
        tail_actors().contains(e.actor) && (id.is_none() || tail_slots(b,l).contains(id.unwrap()))
            && match e.action {Action::Send(i,p)=>p.from==at(Replica::R3) && names(l,Replica::R3).contains(i),_=>true}
    }
}
pub open spec fn one_envelope(t:Tape) -> bool {
    forall|i:int,j:int| 0<=i<j<t.len() && s::slot((#[trigger] t[i]).action).is_some()
        && s::slot(t[i].action)==s::slot((#[trigger] t[j]).action) ==> t[i].action is Send && t[j].action is Deliver
}
pub proof fn routing_allows_preparation(t:Tape,b:Fork,l:Lanes)
    requires one_envelope(t),forall|i:int| 0<=i<t.len() ==> routed(#[trigger] t[i],b,l),
    ensures separable(t,b,l),
{
    let r=crate::origin(b.branch);let u=working(t,b);let v=remaining(t,b);
    assert forall|i:int,j:int| 0<=i<j<t.len() && (#[trigger] t[i]).actor!=at(r) && (#[trigger] t[j]).actor==at(r)
        implies s::independent(t[i],t[j]) by {
        let a=t[i].action;let k=s::slot(a);
        if k.is_some() && k==s::slot(t[j].action) {
            assert(a is Send);assert(names(l,Replica::R3).contains(k.unwrap()) && names(l,r).contains(k.unwrap()));
        }
    }
    assert forall|i:int| 0<=i<u.len() implies {let e=#[trigger] u[i];site(r).contains(e.actor)
        && (s::slot(e.action).is_some() ==> names(l,r).contains(s::slot(e.action).unwrap()))} by {
        s::picked(t,at(r),true,i);let j=choose|j:int| 0<=j<t.len() && t[j]==u[i];assert(routed(t[j],b,l));
    }
    assert forall|i:int| 0<=i<v.len() implies {let e=#[trigger] v[i];tail_actors().contains(e.actor)
        && (s::slot(e.action).is_some() ==> tail_slots(b,l).contains(s::slot(e.action).unwrap()))
        && match e.action {Action::Send(id,p)=>p.from==at(Replica::R3) && names(l,Replica::R3).contains(id),_=>true}} by {
        s::picked(t,at(r),false,i);let j=choose|j:int| 0<=j<t.len() && t[j]==v[i];assert(routed(t[j],b,l));
    }
}
pub proof fn pick_concat(t:Tape,u:Tape,p:Process,keep:bool)
    ensures pick(t+u,p,keep)==pick(t,p,keep)+pick(u,p,keep),
    decreases t.len(),
{
    if t.len()==0 {assert(t+u =~= u);} else {
        assert((t+u).drop_first() =~= t.drop_first()+u);pick_concat(t.drop_first(),u,p,keep);
    }
}
pub(crate) proof fn nested(t:Tape,p:Process,keep:bool,q:Process)
    ensures pick(pick(t,p,keep),q,true)==(if (p==q)==keep {pick(t,q,true)} else {Seq::<Observation>::empty()}),
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let u=t.drop_first();nested(u,p,keep,q);
        if (e.actor==p)==keep {assert(pick(t,p,keep).drop_first() =~= pick(u,p,keep));}
    }
}
pub open spec fn tape(b:Fork,ta:Tape,tb:Tape) -> Tape {
    work_pair(ta,tb,b.notice)+remaining(if b.branch==Branch::Alpha {ta} else {tb},b)
}
// In particular, every receive, send, clock and private callback of both
// survivors is the same in the two originals. C1 has only its own branch's
// receives. R3 likewise sees exactly its own source run.
pub proof fn local_history(b:Fork,ta:Tape,tb:Tape,p:Process)
    ensures p==Process::FirstClient || p==at(Replica::R3) ==> pick(tape(b,ta,tb),p,true)==pick(if b.branch==Branch::Alpha {ta} else {tb},p,true),
{
    let n=b.notice;let c=work_pair(ta,tb,n);let t=if b.branch==Branch::Alpha {ta} else {tb};
    pick_concat(c,remaining(t,b),p,true);pick_concat(working(tb,beta(n)),working(ta,alpha(n)),p,true);
    nested(tb,at(Replica::R1),true,p);nested(ta,at(Replica::R2),true,p);nested(t,at(crate::origin(b.branch)),false,p);
}
pub proof fn survivor_history(b:Fork,ta:Tape,tb:Tape,l:Lanes,r:Replica)
    requires r!=Replica::R3,separable(if b.branch==Branch::Alpha {ta} else {tb},b,l),
    ensures pick(tape(b,ta,tb),at(r),true)==pick(if r==Replica::R1 {tb} else {ta},at(r),true),
{
    let p=at(r);let n=b.notice;let t=if b.branch==Branch::Alpha {ta} else {tb};let tail=remaining(t,b);
    pick_concat(work_pair(ta,tb,n),tail,p,true);pick_concat(working(tb,beta(n)),working(ta,alpha(n)),p,true);
    nested(tb,at(Replica::R1),true,p);nested(ta,at(Replica::R2),true,p);
    if pick(tail,p,true).len()>0 {
        s::picked(tail,p,true,0);let e=pick(tail,p,true)[0];let i=choose|i:int| 0<=i<tail.len() && tail[i]==e;
        assert(tail_actors().contains(tail[i].actor));
    }
    assert(pick(tail,p,true) =~= Seq::<Observation>::empty());
}
pub open spec fn pending_inputs<S>(m:Program<S>,local:S,t:Tape) -> bool
    decreases t.len(),
{
    t.len()==0 || (!(m.done)(local) && pending_inputs(m,(m.update)(local,t[0]),t.drop_first()))
}
pub proof fn pending_on_caller<S>(m:Program<S>,p:Service<S>,j:nat)
    requires p.states.len()==p.actions.len()+1,j<=p.actions.len(),wait::valid_edges(mail::active_step(m),p),
        wait::pending_before(mail::posted(m),p),
    ensures pending_inputs(m,(p.states[j as int].cfg.private)(Process::FirstClient),pick(s::record(p,j),Process::FirstClient,true)),
    decreases p.actions.len()-j,
{
    if j<p.actions.len() {
        let c=Process::FirstClient;let x=p.states[j as int];let a=p.actions[j as int];
        assert(mail::active_step(m)(x,a,p.states[j as int+1]));assert(!mail::posted(m)(x));
        assert(s::record(p,j).drop_first() =~= s::record(p,j+1));pending_on_caller(m,p,j+1);
        let t=pick(s::record(p,j),c,true);if process_step(x.cfg.net,a).actor==c {assert(t.drop_first() =~= pick(s::record(p,j+1),c,true));}
    }
}
pub open spec fn returning<S>(m:Program<S>,b:Fork,p:Service<S>) -> bool {
    wait::first_return(mail::active_step(m),mail::posted(m),reference(m,b,5),p)
}
pub open spec fn quorum(b:Fork,r:Replica) -> bool { r!=maj::missing(b) }
// The first request starts at cut 2. The return may take arbitrarily many
// steps after cut 5. A sample from either part of this interval is legal.
pub open spec fn member_sample<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork) -> bool {
    forall|p:Service<S>| #[trigger] returning(m,b,p) ==> {
        let v=first((p.states.last().cfg.private)(Process::FirstClient));
        (exists|j:nat,r:Replica| 2<=j<=5 && quorum(b,r) && #[trigger] (maj::net(b,j).locals)(r)==v)
        || (exists|j:int,r:Replica| 0<=j<p.states.len() && quorum(b,r) && #[trigger] (p.states[j].cfg.net.locals)(r)==v)
    }
}
pub open spec fn changes_sample<S>(b:Fork,x:State<S>,y:State<S>) -> bool {
    exists|r:Replica| quorum(b,r) && #[trigger] (x.cfg.net.locals)(r)!=(y.cfg.net.locals)(r)
}
pub proof fn stable_value<S>(m:Program<S>,p:Service<S>,b:Fork,j:nat,r:Replica)
    requires returning(m,b,p),j<p.states.len(),quorum(b,r),
        forall|i:int| 0<=i<p.actions.len() ==> !changes_sample(b,#[trigger] p.states[i],p.states[i+1]),
    ensures (p.states[j as int].cfg.net.locals)(r)==first_value(b),
    decreases j,
{
    if j>0 {let k=(j-1) as nat;stable_value(m,p,b,k,r);assert(!changes_sample(b,p.states[k as int],p.states[k as int+1]));}
}
pub proof fn forced_sample<S>(m:Program<S>,first:spec_fn(S)->int,p:Service<S>,b:Fork)
    requires returning(m,b,p),member_sample(m,first,b),
        forall|i:int| 0<=i<p.actions.len() ==> !changes_sample(b,#[trigger] p.states[i],p.states[i+1]),
    ensures first((p.states.last().cfg.private)(Process::FirstClient))==first_value(b),
{
    let v=first((p.states.last().cfg.private)(Process::FirstClient));
    if exists|j:int,r:Replica| 0<=j<p.states.len() && quorum(b,r) && #[trigger] (p.states[j].cfg.net.locals)(r)==v {
        let (j,r)=choose|j:int,r:Replica| 0<=j<p.states.len() && quorum(b,r) && #[trigger] (p.states[j].cfg.net.locals)(r)==v;
        stable_value(m,p,b,j as nat,r);
    } else {
        let (j,r)=choose|j:nat,r:Replica| 2<=j<=5 && quorum(b,r) && #[trigger] (maj::net(b,j).locals)(r)==v;
        assert(j==2 || j==3 || j==4 || j==5);
    }
}
// C1 and a responder's two local histories identify the RPC independently
// of the wire encoding of its reply and independently of the returned value.
pub open spec fn intake_at(e:Observation,r:Replica) -> bool {
    e.action==Action::<Wire>::Deliver(dispatch::request_id(r)) && e.incoming==Some(dispatch::request(r))
}
pub open spec fn answer_at(e:Observation,r:Replica,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    match e.action {Action::Send(_,p)=>p.from==at(r) && p.to==Process::FirstClient && answers(p),_=>false}
}
pub open spec fn delivered(e:Observation,f:Observation) -> bool {
    match e.action {Action::Send(id,p)=>f.action==Action::<Wire>::Deliver(id) && f.incoming==Some(p),_=>false}
}
pub open spec fn exchange(t:Tape,r:Replica,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    let site=pick(t,at(r),true);let client=pick(t,Process::FirstClient,true);
    exists|i:int,j:int,k:int| 0<=i<j<site.len() && 0<=k<client.len() && intake_at(#[trigger] site[i],r)
        && answer_at(#[trigger] site[j],r,answers) && delivered(site[j],#[trigger] client[k])
}
pub open spec fn source_shape(t:Tape,b:Fork,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    exchange(t,crate::origin(b.branch),answers) && exchange(t,Replica::R3,answers)
}
pub open spec fn replied(t:Tape,r:Replica,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    let part=pick(t,at(r),true);
    exists|i:int,j:int| 0<=i<j<part.len() && intake_at(#[trigger] part[i],r) && answer_at(#[trigger] part[j],r,answers)
}
pub proof fn actual_respondents(ta:Tape,tb:Tape,b:Fork,l:Lanes,answers:spec_fn(Packet<Wire>)->bool,r:Replica)
    requires separable(ta,alpha(b.notice),l),separable(tb,beta(b.notice),l),
        source_shape(ta,alpha(b.notice),answers),source_shape(tb,beta(b.notice),answers),
    ensures replied(tape(b,ta,tb),r,answers),quorum(b,r) ==> exchange(tape(b,ta,tb),r,answers),
{
    let n=b.notice;let t=if b.branch==Branch::Alpha {ta} else {tb};
    if b.branch==Branch::Alpha {assert(b==alpha(n));} else {assert(b==beta(n));}
    local_history(b,ta,tb,Process::FirstClient);local_history(b,ta,tb,at(r));
    if r!=Replica::R3 {survivor_history(b,ta,tb,l,r);}
    let src=if r==Replica::R1 {tb} else if r==Replica::R2 {ta} else {t};
    let server=pick(src,at(r),true);let client=pick(src,Process::FirstClient,true);
    assert(exchange(src,r,answers));
    let (i,j,k)=choose|i:int,j:int,k:int| 0<=i<j<server.len() && 0<=k<client.len() && intake_at(#[trigger] server[i],r)
        && answer_at(#[trigger] server[j],r,answers) && delivered(server[j],#[trigger] client[k]);
    assert(pick(tape(b,ta,tb),at(r),true)==server);if quorum(b,r) {assert(t==src);}
}
// Every C1 receipt in a real one-crash reference has a live source. The
// initial mailbox is empty. The other origin cannot report its participation
// to C1 through this failed process or through an invented C1 send.
pub proof fn caller_sources<S>(m:Program<S>,b:Fork,p:Service<S>,j:int)
    requires returning(m,b,p),0<=j<pick(s::record(p,0),Process::FirstClient,true).len(),
    ensures ({let e=pick(s::record(p,0),Process::FirstClient,true)[j];
        e.incoming.is_some() ==> e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3)}),
{
    let c=Process::FirstClient;let t=s::record(p,0);let e=pick(t,c,true)[j];
    s::picked(t,c,true,j);let i=choose|i:int| 0<=i<t.len() && t[i]==e;
    if e.incoming.is_some() {
        let a=p.actions[i];let q=e.incoming.unwrap();assert(a is Deliver && q.to==c);
        let id=a->Deliver_0;let x=p.states[i];assert(mail::active_step(m)(x,a,p.states[i+1]));
        assert(x.cfg.net.pending.get(id)==Some(q));assert(p.states[0].cfg.net.pending.get(id)!=Some(q));
        let k=mail::last_send(m,p,i as nat,id,q);assert(mail::active_step(m)(p.states[k as int],p.actions[k as int],p.states[k as int+1]));
        prefix_mask(m,p,k);assert(live(p.states[k as int].cfg.net,q.from));
    }
}
pub(crate) proof fn prefix_mask<S>(m:Program<S>,p:Service<S>,j:nat)
    requires p.states.len()==p.actions.len()+1,j<p.states.len(),wait::valid_edges(mail::active_step(m),p),
    ensures p.states[j as int].cfg.net.unavailable==p.states[0].cfg.net.unavailable,
        p.states[j as int].cfg.net.second_started==p.states[0].cfg.net.second_started,
    decreases j,
{
    if j>0 {prefix_mask(m,p,(j-1) as nat);assert(mail::active_step(m)(p.states[j-1],p.actions[j-1],p.states[j as int]));}
}

}
