// A necessary service alternative with both paper origins still alive.
// The auxiliary cut precedes either background installation. A copy is
// operation-specific durable storage; knowledge or a vote is insufficient.
use vstd::prelude::*;
use crate::{Op,Replica,RecoveredOrder};
use crate::checkpoint::*;
use crate::delivery::Action;
use crate::fallback_program as front;
use crate::first_copy_wait::Cut;
use crate::isolated_sender::{holders,take};
use crate::ordered_store::majority;
use crate::promotion_wait::*;
use crate::quorum_rpc::Resolver;
use crate::weak_round::{self as weak,paper_ops};

verus! {

pub open spec fn issued() -> weak::World {
    let f=paper_ops();let s=weak::step(f,weak::start(),weak::Action::Send(0,weak::request(Op::W1)));
    let s=weak::step(f,s,weak::Action::Send(1,weak::request(Op::W2)));
    let s=weak::step(f,weak::step(f,s,weak::Action::Handle(0)),weak::Action::Handle(1));
    weak::step(f,weak::step(f,s,weak::Action::Receive(0)),weak::Action::Receive(1))
}
pub open spec fn actions(b:Fork) -> Seq<Action<Wire>> {
    seq![Action::CrashR3,Action::Send(3,packet_for(b,3)),Action::Send(4,packet_for(b,4)),Action::Send(5,packet_for(b,5))]
}
pub open spec fn at_cut(b:Fork,rho:Resolver,k:nat) -> Cut
    decreases k,
{
    if k==0 {front::original(b,0)} else {let j=k-1;take(rho,at_cut(b,rho,j as nat),actions(b)[j])}
}
proof fn fanout_disk(b:Fork,rho:Resolver,k:nat)
    requires k<=4,
    ensures at_cut(b,rho,k).core.base.disk==front::original(b,0).core.base.disk,
    decreases k,
{
    if k>0 {let j=(k-1) as nat;fanout_disk(b,rho,j);
        assert(j==0 || j==1 || j==2 || j==3);
        assert(at_cut(b,rho,k).core.base.disk==at_cut(b,rho,j).core.base.disk);
    }
}
#[verifier::rlimit(14)]
pub proof fn reachable_cut(b:Fork,rho:Resolver)
    ensures ({
        let s=issued();let x=at_cut(b,rho,4);
        s.front==front::original(b,0).core && s.answers.get(weak::request(Op::W1).id)==Some(1)
            && s.answers.get(weak::request(Op::W2).id)==Some(1)
            && holders(s,weak::request(Op::W1).id)==set![Replica::R1] && holders(s,weak::request(Op::W2).id)==set![Replica::R2]
            && crate::facade_hybrid::prefix_entry(paper_ops(),b)
            && (forall|k:nat| k<4 ==> front::joint(paper_ops(),rho,at_cut(b,rho,k),#[trigger] actions(b)[k as int],at_cut(b,rho,k+1)))
            && (forall|k:nat| k<=4 ==> (#[trigger] at_cut(b,rho,k)).core.base.disk==s.front.base.disk)
            && x.core.base.live==live_pair() && x.core.base.disk==s.front.base.disk && x.core.calls[1].answer.is_none()
            && (x.core.base.disk)(Replica::R1).value==2 && (x.core.base.disk)(Replica::R2).value==5
            && x.net.pending==front::original(b,0).net.pending.insert(3,packet_for(b,3)).insert(4,packet_for(b,4)).insert(5,packet_for(b,5))
    }),
{
    weak::actual_overlap(b);crate::facade_hybrid::weak_calls_and_issued_offers(paper_ops(),b);reveal_with_fuel(at_cut,5);
    let s=issued();assert(holders(s,weak::request(Op::W1).id) =~= set![Replica::R1]);
    assert(holders(s,weak::request(Op::W2).id) =~= set![Replica::R2]);
    assert forall|k:nat| k<4 implies front::joint(paper_ops(),rho,at_cut(b,rho,k),#[trigger] actions(b)[k as int],at_cut(b,rho,k+1))
        by {assert(k==0 || k==1 || k==2 || k==3);}
    assert forall|k:nat| k<=4 implies (#[trigger] at_cut(b,rho,k)).core.base.disk==s.front.base.disk
        by {fanout_disk(b,rho,k);}
    assert(at_cut(b,rho,4).core.base.live =~= live_pair());
}

#[verifier::reject_recursive_types(S)]
pub struct ReadAudit<S> {
    pub response:spec_fn(S)->Option<int>,pub cell:spec_fn(S,Replica)->int,pub durable:spec_fn(S,Op)->Set<Replica>,
}
pub open spec fn read_done<S>(m:ReadAudit<S>) -> spec_fn(S)->bool { |s|(m.response)(s).is_some() }
pub open spec fn pending_split<S>(m:ReadAudit<S>,s:S) -> bool {
    (m.response)(s).is_none() && (m.cell)(s,Replica::R1)==2 && (m.cell)(s,Replica::R2)==5 &&
        !majority((m.durable)(s,Op::W1)) && !majority((m.durable)(s,Op::W2))
}
pub open spec fn new_majority<S,A>(m:ReadAudit<S>) -> Relation<S,A> {
    |s:S,_a:A,u:S|exists|w:Op,r:Replica| (w==Op::W1 || w==Op::W2)
        && !majority((m.durable)(s,w)) && majority((m.durable)(u,w))
        && !(m.durable)(s,w).contains(r) && #[trigger] (m.durable)(u,w).contains(r)
}
pub open spec fn restores_one<S,A>(m:ReadAudit<S>) -> Relation<S,A> {
    |s:S,_a:A,u:S|exists|r:Replica| live_pair().contains(r) && (m.cell)(s,r)!=1 && #[trigger] (m.cell)(u,r)==1
}
// Credit any majority established up to the return, even one that has
// since lost a copy. The cut has no earlier majority. A complete
// protocol must instantiate durable with its actual storage semantics.
pub open spec fn safe_return<S,A>(m:ReadAudit<S>,p:Path<S,A>) -> bool {
    let v=(m.response)(p.states.last()).unwrap();
    (exists|r:Replica,k:int| live_pair().contains(r) && 0<=k<p.states.len() && #[trigger] (m.cell)(p.states[k],r)==v) &&
    exists|h:RecoveredOrder| #[trigger] crate::irrevocable_order::single_read(h,v) &&
        forall|j:int,i:int| 0<=j<i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 && (#[trigger] h.ops[j]==Op::W1 || h.ops[j]==Op::W2)
        ==> exists|k:int| 0<=k<p.states.len() && majority(#[trigger] (m.durable)(p.states[k],h.ops[j]))
}
pub(crate) proof fn crossing<S>(pred:spec_fn(S)->bool,t:Seq<S>,k:nat) -> (j:int)
    requires k<t.len(),!pred(t[0]),pred(t[k as int]),
    ensures 0<=j<k,!pred(t[j]),pred(t[j+1]),
    decreases k,
{
    let i=k-1;if pred(t[i]) {crossing(pred,t,i as nat)} else {i}
}
proof fn classify<S,A>(m:ReadAudit<S>,s:S,step:Relation<S,A>,p:Path<S,A>)
    requires pending_split(m,s),first_return(step,read_done(m),s,p),safe_return(m,p),
    ensures uses(p,new_majority(m)) || ((m.response)(p.states.last())==Some(1) && uses(p,restores_one(m))),
{
    let t=p.states;let v=(m.response)(t.last()).unwrap();
    if v==1 {
        let (r,k)=choose|r:Replica,k:int| live_pair().contains(r) && 0<=k<t.len() && #[trigger] (m.cell)(t[k],r)==1;
        let j=crossing(|x|(m.cell)(x,r)==1,t,k as nat);assert(restores_one(m)(t[j],p.actions[j],t[j+1]));
    } else {
        let h=choose|h:RecoveredOrder| #[trigger] crate::irrevocable_order::single_read(h,v) &&
            forall|j:int,i:int| 0<=j<i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 && (#[trigger] h.ops[j]==Op::W1 || h.ops[j]==Op::W2)
            ==> exists|k:int| 0<=k<t.len() && majority(#[trigger] (m.durable)(t[k],h.ops[j]));
        let i=choose|i:int| 0<=i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 && h.states[i]==v;
        crate::irrevocable_order::writer_before(h,i as nat);
        let z=choose|z:int| 0<=z<i && (#[trigger] h.ops[z]==Op::W1 && v==2 || h.ops[z]==Op::W2 && v==5);let w=h.ops[z];
        let k=choose|k:int| 0<=k<t.len() && majority(#[trigger] (m.durable)(t[k],w));
        let j=crossing(|x|majority((m.durable)(x,w)),t,k as nat);
        let old=(m.durable)(t[j],w);let later=(m.durable)(t[j+1],w);
        let r=if later.contains(Replica::R1) && !old.contains(Replica::R1) {Replica::R1}
            else if later.contains(Replica::R2) && !old.contains(Replica::R2) {Replica::R2} else {Replica::R3};
        assert(later.contains(r) && !old.contains(r));assert(new_majority(m)(t[j],p.actions[j],t[j+1]));
    }
}
// No particular RPC sequence, selector or metadata projection in this
// implication. No feasibility assumption in the disjunction. A permanently
// impossible read is explicitly a different outcome from a causal wait.
pub proof fn service_alternatives<S,A>(m:ReadAudit<S>,s:S,step:Relation<S,A>)
    requires pending_split(m,s),
    ensures ({
        let done=read_done(m);let effect=new_majority(m);
        !can_finish(step,done,s) || needs_class(step,done,s,effect) ||
            exists|p:Path<S,A>| #[trigger] first_return(step,done,s,p) && !uses(p,effect) &&
                (!safe_return(m,p) || ((m.response)(p.states.last())==Some(1) && uses(p,restores_one(m))))
    }),
{
    let done=read_done(m);let effect=new_majority(m);
    if can_finish(step,done,s) && !needs_class(step,done,s,effect) {
        let p=choose|p:Path<S,A>| #[trigger] first_return(step,done,s,p) && !uses(p,effect);
        if safe_return(m,p) {classify(m,s,step,p);}
    }
}
pub proof fn at_real_split<S,A>(b:Fork,rho:Resolver,m:ReadAudit<S>,s:S,step:Relation<S,A>)
    requires (m.response)(s)==at_cut(b,rho,4).core.calls[1].answer,
        forall|r:Replica| #[trigger] (m.cell)(s,r)==(at_cut(b,rho,4).core.base.disk)(r).value,
        forall|w:Op| w==Op::W1 || w==Op::W2 ==> #[trigger] (m.durable)(s,w)==holders(issued(),weak::request(w).id),
    ensures ({
        let done=read_done(m);let effect=new_majority(m);
        !can_finish(step,done,s) || needs_class(step,done,s,effect) ||
            exists|p:Path<S,A>| #[trigger] first_return(step,done,s,p) && !uses(p,effect) &&
                (!safe_return(m,p) || ((m.response)(p.states.last())==Some(1) && uses(p,restores_one(m))))
    }),
{
    reachable_cut(b,rho);service_alternatives(m,s,step);
}
// With an actual completion witness and the independently defined no-await
// rule, recover an enabled restoration path, with no constraint on sender
// choice or on how many ordinary protocol steps the read takes.
pub proof fn no_await_needs_a_restore<S,A>(m:ReadAudit<S>,s:S,step:Relation<S,A>,admitted:spec_fn(S)->bool,
    witness:Path<S,A>) -> (p:Path<S,A>)
    requires pending_split(m,s),admitted(s),
        first_return(step,read_done(m),s,witness),
        no_await(step,read_done(m),admitted,new_majority(m)),
        forall|path:Path<S,A>| #[trigger] first_return(step,read_done(m),s,path) &&
            !uses(path,new_majority(m)) ==> safe_return(m,path),
    ensures first_return(step,read_done(m),s,p),!uses(p,new_majority(m)),
        (m.response)(p.states.last())==Some(1),uses(p,restores_one(m)),
{
    let p=extract_without_promotion(step,read_done(m),admitted,new_majority(m),s,witness);
    classify(m,s,step,p);p
}

}
