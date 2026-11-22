// Weak conflict handling at R3 in the supplementary one-failure schedules.
// The strong RPC code, both original C1 histories, and the two origin sites
// are unchanged. Weak receiver memory can retain either or both invocations.
use vstd::prelude::*;
use crate::{Op,Replica,origin,next};
use crate::checkpoint::*;
use crate::delivery::{self,Action};
use crate::facade_hybrid::inner;
use crate::facade_linear::CommandSemantics;
use crate::fallback_program::{self as program,apply_event};
use crate::first_copy_wait::Cut;
use crate::live_quorum as rpc;
use crate::ordered_round::{engine,Store};
use crate::quorum_rpc::Resolver;
use crate::read_recovery::compatible;
use crate::sender_forks::{self as forks,firsts};
use crate::stock_facade::*;

verus! {

#[verifier::reject_recursive_types(X)]
pub struct Receiver<X> {
    pub empty:X, pub journal:spec_fn(X,Op)->X, pub expose:spec_fn(X)->int,
}
pub open spec fn writer(v:int) -> Op {if v==2 {Op::W1} else {Op::W2}}
pub open spec fn before<X>(m:Receiver<X>,b:Fork,k:nat) -> X {
    if k==0 {m.empty} else {(m.journal)(m.empty,observed_writer(b))}
}
pub open spec fn after<X>(m:Receiver<X>,b:Fork) -> X {
    (m.journal)(before(m,b,15),observed_writer(forks::opposite(b)))
}
pub open spec fn isolated<X>(m:Receiver<X>) -> bool {
    (m.expose)(m.empty)==1 && (m.expose)((m.journal)(m.empty,Op::W1))==2 && (m.expose)((m.journal)(m.empty,Op::W2))==5
}
// The two sides may have different internal order or provenance even when
// their working values converge. Both laws concern only weak installations.
pub open spec fn commutes_on_values<X>(m:Receiver<X>) -> bool {
    forall|a:Op,b:Op| (a==Op::W1 || a==Op::W2) && (b==Op::W1 || b==Op::W2) ==>
        #[trigger] (m.expose)((m.journal)((m.journal)(m.empty,a),b))==(m.expose)((m.journal)((m.journal)(m.empty,b),a))
}
pub open spec fn selects_a_writer<X>(m:Receiver<X>) -> bool {
    forall|a:Op,b:Op| (a==Op::W1 || a==Op::W2) && (b==Op::W1 || b==Op::W2) ==>
        {let v=#[trigger] (m.expose)((m.journal)((m.journal)(m.empty,a),b));v==next(a,1) || v==next(b,1)}
}
pub open spec fn inbound(s:Cut,ev:rpc::Ev) -> bool {
    ev is Deliver && s.net.pending.contains_key(ev->Deliver_0) && {
        let p=s.net.pending[ev->Deliver_0];p.to==at(Replica::R3) && crate::metadata_provenance::authentic_copy(p)
    }
}
pub open spec fn install<X>(m:Receiver<X>,x:X,s:Cut,ev:rpc::Ev) -> (X,Cut) {
    let r=Replica::R3;let packet=s.net.pending[ev->Deliver_0];let v=packet.input->Copy_0;
    let y=(m.journal)(x,writer(v));let exposed=(m.expose)(y);let disk=s.core.base.disk;
    let bus=delivery::advance(|old,w|if w is Copy {exposed} else {old},s.net,ev);
    let core=State{base:Store{disk:|site|if site==r {crate::ordered_store::Stamp{value:exposed,..disk(site)}} else {disk(site)},..s.core.base},..s.core};
    (y,Cut{net:bus,core})
}
pub open spec fn edge<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,x:X,s:Cut,ev:rpc::Ev,y:X,u:Cut) -> bool {
    if inbound(s,ev) {
        (s.net.locals)(Replica::R3)==(m.expose)(x) && (s.core.base.disk)(Replica::R3).value==(m.expose)(x)
            && delivery::enabled(s.net,ev) && inner(s.net,ev) is Idle && enabled(engine(f),s.core,Event::Idle)
            && apply_event(rho,engine(f),s.core,Event::Idle)==s.core && install(m,x,s,ev)==(y,u)
    } else {y==x && program::joint(f,rho,s,ev,u)}
}
pub open spec fn original_trace<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,b:Fork) -> bool {
    forks::prefix_taken(f,rho,b) && (forall|k:nat| k<17 ==> edge(m,f,rho,before(m,b,k),program::original(b,k),
        #[trigger] actions_to_crash(b)[k as int],before(m,b,k+1),program::original(b,k+1))) && forks::actual_sr2(f,rho,b)
}
pub open spec fn post<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,b:Fork) -> Cut {
    let dead=origin(b.branch);let x=forks::crash(f,rho,program::original(b,15),dead);
    forks::begin(f,rho,install(m,before(m,b,15),x,Action::Deliver(forks::late(b))).1)
}
pub open spec fn alternate_trace<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,b:Fork) -> bool {
    let old=program::original(b,15);let d=forks::opposite(b);let l=origin(d.branch);let r=Replica::R3;
    let x=forks::crash(f,rho,old,origin(b.branch));let ev:rpc::Ev=Action::Deliver(forks::late(b));
    let (y,u)=install(m,before(m,b,15),x,ev);let s=post(m,f,rho,b);
    forks::one_failure(f,old,origin(b.branch)) && x.net.pending==old.net.pending && inbound(x,ev)
        && edge(m,f,rho,before(m,b,15),x,ev,y,u) && y==after(m,b) && forks::new_client(f,u)
        && s.net.pending==old.net.pending.remove(forks::late(b)) && s.core.calls[1]==old.core.calls[1]
        && (s.core.base.disk)(r).value==(m.expose)(y) && (s.core.base.disk)(l)==(old.core.base.disk)(l)
        && rpc::exchange(f,rho,s,l,r) && rpc::at_step(rho,s,l,r,9).core.calls[1].answer==Some(first_value(b))
}
#[verifier::rlimit(16)]
proof fn prefix_edge<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,b:Fork,k:nat)
    requires isolated(m),k<17,forks::prefix_taken(f,rho,b),
    ensures edge(m,f,rho,before(m,b,k),program::original(b,k),actions_to_crash(b)[k as int],before(m,b,k+1),program::original(b,k+1)),
{
    hide(program::joint);hide(first_round);hide(crate::facade_hybrid::prefix_entry);
    let s=program::original(b,k);let u=program::original(b,k+1);let ev=actions_to_crash(b)[k as int];
    prefix_index(k as int);assert(program::joint(f,rho,s,ev,u));
    if k==0 {
        let v=install(m,m.empty,s,ev).1;let ordinary=apply_event(rho,engine(f),s.core,Event::Idle);
        assert(v.core.base.disk =~= u.core.base.disk);assert(v.net.locals =~= u.net.locals);assert(v.net.pending =~= u.net.pending);
        assert(ordinary.closed =~= s.core.closed);assert(ordinary==s.core);
        assert(v.core.base.live =~= u.core.base.live);
        assert(v==u);assert(install(m,m.empty,s,ev).0==before(m,b,1));
        assert(inbound(s,ev));assert(delivery::enabled(s.net,ev));assert(inner(s.net,ev) is Idle);
    } else {assert(!inbound(s,ev));}
}
proof fn origin_survivors<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,b:Fork)
    requires isolated(m),forks::release_after_origin_crash(f,rho,b),
    ensures alternate_trace(m,f,rho,b),
{
    hide(rpc::exchange);hide(program::joint);let d=forks::opposite(b);let r=Replica::R3;
    let old=program::original(b,15);let x=forks::crash(f,rho,old,origin(b.branch));let ev:rpc::Ev=Action::Deliver(forks::late(b));
    let s=post(m,f,rho,b);crate::facade_transport::actual_first_rpc(b,15);
    assert(apply_event(rho,engine(f),x.core,Event::Idle).closed =~= x.core.closed);
    assert(rpc::fresh_majority(s,origin(d.branch),r));rpc::addressed_exchange(f,rho,s,origin(d.branch),r);
}
proof fn schedules<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,b:Fork)
    requires isolated(m),firsts(rho,b.notice),
    ensures original_trace(m,f,rho,b),alternate_trace(m,f,rho,b),
{
    hide(edge);hide(forks::prefix_taken);hide(forks::actual_sr2);hide(forks::release_after_origin_crash);hide(alternate_trace);
    forks::both_schedules(f,rho,b);origin_survivors(m,f,rho,b);
    assert forall|k:nat| k<17 implies edge(m,f,rho,before(m,b,k),program::original(b,k),
        #[trigger] actions_to_crash(b)[k as int],before(m,b,k+1),program::original(b,k+1)) by {prefix_edge(m,f,rho,b,k);}
}
pub open spec fn fails_at_alternate<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,b:Fork) -> bool {
    let l=origin(forks::opposite(b).branch);let s=post(m,f,rho,b);let q=rpc::at_step(rho,s,l,Replica::R3,9);
    q.core.calls[2].answer==Some(first_value(forks::opposite(b))) && !compatible(b,q.core.calls[2].answer.unwrap())
}
// Both origin-crash continuations execute. A weak receiver which exposes
// the same contributing writer after both arrival orders must lose the
// SR1 history in at least one. No receiver order is attributed to T.
pub proof fn convergent_receiver<X>(m:Receiver<X>,f:CommandSemantics,rho:Resolver,n:Notice)
    requires isolated(m),commutes_on_values(m),selects_a_writer(m),firsts(rho,n),
    ensures original_trace(m,f,rho,alpha(n)),original_trace(m,f,rho,beta(n)),
        alternate_trace(m,f,rho,alpha(n)),alternate_trace(m,f,rho,beta(n)),
        fails_at_alternate(m,f,rho,alpha(n)) || fails_at_alternate(m,f,rho,beta(n)),
{
    let a=alpha(n);let d=beta(n);schedules(m,f,rho,a);schedules(m,f,rho,d);
    let v=(m.expose)(after(m,a));assert(v==(m.expose)(after(m,d)) && (v==2 || v==5));
    let b=if v==2 {a} else {d};let other=forks::opposite(b);let s=post(m,f,rho,b);
    crate::metadata_reader::actual_first_decision(other,rho,Set::empty());
    assert(rpc::reports(s,origin(other.branch),Replica::R3) =~= crate::metadata_pair::first_rows(other,13));
    crate::read_recovery::history_accepts_exactly_observed_value(b,first_value(other));
}
pub open spec fn by_priority(prefer:Op) -> Receiver<Set<Op>> {
    Receiver{empty:Set::empty(),journal:|s:Set<Op>,w|s.insert(w),expose:|s:Set<Op>|
        if s.contains(prefer) {next(prefer,1)} else if s.contains(Op::W1) {2} else if s.contains(Op::W2) {5} else {1}}
}
pub open spec fn by_arrival() -> Receiver<Seq<Op>> {
    Receiver{empty:Seq::empty(),journal:|s:Seq<Op>,w|s.push(w),expose:|s:Seq<Op>|if s.len()>0 {next(s[0],1)} else {1}}
}
pub proof fn arrival_and_priority(f:CommandSemantics,b:Fork,prefer:Op)
    requires prefer==Op::W1 || prefer==Op::W2,
    ensures ({
        let priority=by_priority(prefer);let first=by_arrival();let rho=crate::mixed_service_transfer::reference_sample();
        let s=post(first,f,rho,b);let q=rpc::at_step(rho,s,origin(forks::opposite(b).branch),Replica::R3,9);
        isolated(priority) && commutes_on_values(priority) && selects_a_writer(priority)
            && (fails_at_alternate(priority,f,rho,alpha(b.notice)) || fails_at_alternate(priority,f,rho,beta(b.notice)))
            && isolated(first) && !commutes_on_values(first) && selects_a_writer(first)
            && after(first,b).contains(Op::W1) && after(first,b).contains(Op::W2)
            && original_trace(first,f,rho,b) && alternate_trace(first,f,rho,b)
            && q.core.calls[2].answer==Some(first_value(b)) && compatible(b,first_value(b))
    }),
{
    hide(original_trace);hide(fails_at_alternate);hide(rpc::exchange);hide(forks::prefix_taken);
    hide(completed_quorum_sample);hide(crate::promotion_wait::needs_class);
    let rho=crate::mixed_service_transfer::reference_sample();let d=forks::opposite(b);let p=by_priority(prefer);let m=by_arrival();
    crate::mixed_service_transfer::ordinary_reference_escape(b);crate::mixed_service_transfer::ordinary_reference_escape(d);
    crate::metadata_pair::real_first_with(rho,rho,alpha(b.notice),Set::empty());
    crate::metadata_pair::real_first_with(rho,rho,beta(b.notice),Set::empty());
    assert(firsts(rho,b.notice));
    convergent_receiver(p,f,rho,b.notice);schedules(m,f,rho,b);
    assert(isolated(p) && selects_a_writer(p) && commutes_on_values(p));
    assert(isolated(m) && selects_a_writer(m));
    assert((m.expose)((m.journal)((m.journal)(m.empty,Op::W1),Op::W2))==2);
    assert((m.expose)((m.journal)((m.journal)(m.empty,Op::W2),Op::W1))==5);
    assert(!commutes_on_values(m));
    let history=after(m,b);
    assert(history[0]==observed_writer(b) && history[1]==observed_writer(d));
    assert(history.contains(Op::W1) && history.contains(Op::W2));
    let s=post(m,f,rho,b);let l=origin(d.branch);
    assert(rpc::reports(s,l,Replica::R3).dom() =~= set![l,Replica::R3]);
    assert((s.core.base.disk)(Replica::R3).value==first_value(b));
    assert(rho(rpc::reports(s,l,Replica::R3))==Some(first_value(b)));
    assert(rpc::at_step(rho,s,l,Replica::R3,9).core.calls[2].answer==Some(first_value(b)));
    crate::read_recovery::history_accepts_exactly_observed_value(b,first_value(b));
}

}
