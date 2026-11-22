use vstd::prelude::*;
use crate::{Op,Replica};
use crate::checkpoint::*;
use crate::delivery::{Action,Process,process_step};
use crate::fanout_replay as moved;
use crate::ordinary_service::{Configuration,allowed,apply};
use crate::protocol::{LocalProtocol,accepted,memory};
use crate::promotion_wait::{self as wait,Path,Relation};

verus! {

type Machine<S> = LocalProtocol<S,int,Wire>;
type C<S> = Configuration<S>;
type A = Action<Wire>;

pub open spec fn state<S>(m:Machine<S>,b:Fork,k:nat) -> C<S> {
    C {net:moved::net(b,k),private:|p|memory(m,p,moved::events(b),k)}
}
pub open spec fn done<S>(m:Machine<S>) -> spec_fn(C<S>)->bool {
    |s:C<S>| (m.done)((s.private)(Process::FirstClient))
}

// The original external workload after C1 has sent its requests. Network
// and private protocol guards still govern every replica emit and delivery.
// CPUs and accepted local inputs of the running participants are available.
// An integration must account for an actual source for each such input.
pub open spec fn internal(a:A) -> bool {
    match a {
        Action::Send(_,p)=>p.from is At,
        Action::StopFirstClient | Action::StartSecondClient=>false,
        _=>true,
    }
}
pub open spec fn run_step<S>(m:Machine<S>) -> Relation<C<S>,A> {
    |s:C<S>,a:A,u:C<S>| internal(a) && allowed(m,s,a) && u==apply(m,s,a)
}
pub open spec fn segment<S>(m:Machine<S>,b:Fork,lo:nat,hi:nat) -> Path<C<S>,A> {
    Path {states:Seq::new((hi-lo+1) as nat,|i:int|state(m,b,lo+i as nat)),
          actions:Seq::new((hi-lo) as nat,|i:int|moved::actions(b)[lo+i])}
}
// Reachability starts just after the two actual local RMWs and their
// offers. Full prefix feasibility for a candidate protocol is separate.
pub open spec fn reaches<S>(m:Machine<S>,s:C<S>,p:Path<C<S>,A>) -> bool {
    p.states.len()==p.actions.len()+1
        && p.states[0].net==after_local_rmws() && p.states[0].private==m.initial
        && p.states.last()==s && wait::valid_edges(|s,a,u|allowed(m,s,a) && u==apply(m,s,a),p)
}
pub open spec fn reached<S>(m:Machine<S>,s:C<S>) -> bool {
    exists|p:Path<C<S>,A>| #[trigger] reaches(m,s,p)
}

proof fn one<S>(m:Machine<S>,b:Fork,k:nat)
    requires accepted(m,moved::events(b)),k<17,
    ensures ({
        let s=state(m,b,k);let a=moved::actions(b)[k as int];
        allowed(m,s,a) && apply(m,s,a)==state(m,b,k+1)
    }),
{
    moved::same_physical_events(b);
    let s=state(m,b,k);let a=moved::actions(b)[k as int];
    let ev=process_step(s.net,a);let es=moved::events(b);
    assert(moved::states(b)[k as int]==s.net && es[k as int]==ev);
    assert((m.accept)(memory(m,ev.actor,es,k),ev));
    assert(apply(m,s,a).private =~= state(m,b,k+1).private);
}
pub proof fn actual_opportunity<S>(m:Machine<S>,b:Fork,value:spec_fn(S)->int)
    requires accepted(m,checkpoint_observations(b)),completed_quorum_sample(m,value,b),
    ensures reached(m,state(m,b,3)),
        wait::first_return(run_step(m),done(m),state(m,b,3),segment(m,b,3,first_return_len(m,b))),
{
    moved::retiming_preserves_service(m,b,value);
    let to_cut=segment(m,b,0,3);
    assert(to_cut.states[0].private =~= m.initial);
    assert forall|i:int| 0<=i<3 implies allowed(m,to_cut.states[i],#[trigger] to_cut.actions[i])
            && to_cut.states[i+1]==apply(m,to_cut.states[i],to_cut.actions[i]) by {one(m,b,i as nat);}
    assert(to_cut.states.last()==state(m,b,3));
    moved::same_physical_events(b);
    assert(reaches(m,state(m,b,3),to_cut));
    let end=first_return_len(m,b);let path=segment(m,b,3,end);let transition=run_step(m);let d=done(m);
    assert forall|i:int| 0<=i<path.actions.len() implies !d(path.states[i])
            && transition(path.states[i],#[trigger] path.actions[i],path.states[i+1]) by {
        let k=3+i as nat;one(m,b,k);prefix_index(k as int);
        moved::same_local_history(m,b,Process::FirstClient,k);
        let j=moved::local_index(Process::FirstClient,k);
        if j<=12 {assert(!(m.done)(first_client_at(m,b,j)));}
    }
    assert(wait::valid_edges(transition,path));
    assert forall|i:int| 0<=i<path.actions.len() implies !d(#[trigger] path.states[i])
        by {assert(transition(path.states[i],path.actions[i],path.states[i+1]));}
    assert(wait::pending_before(d,path));
}

// A protocol-specific physical account of where an operation is stored.
// This can include logs, encoded storage and separately retained copies.
// A reply payload in transit is not yet a copy stored at its receiver.
pub type Copies<S> = spec_fn(C<S>,Op)->Set<Replica>;
pub open spec fn grows<S>(copies:Copies<S>) -> Relation<C<S>,A> {
    |s:C<S>,_a:A,u:C<S>| !copies(u,Op::W1).subset_of(copies(s,Op::W1))
                       || !copies(u,Op::W2).subset_of(copies(s,Op::W2))
}
proof fn no_growth<S>(copies:Copies<S>,p:Path<C<S>,A>,k:nat,w:Op)
    requires p.states.len()==p.actions.len()+1,k<=p.actions.len(),w==Op::W1 || w==Op::W2,
        !wait::uses(p,grows(copies)),
    ensures copies(p.states[k as int],w).subset_of(copies(p.states[0],w)),
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat;no_growth(copies,p,i,w);
        assert(!(grows(copies))(p.states[i as int],p.actions[i as int],p.states[k as int]));
    }
}

// The part of H needed for ONE completed read, without inventing a later
// response. Commands keep their recorded returns. A read-from writer must
// have reached a majority by the read's return. Even a previously reached
// majority during this interval is credited. Before the cut each RMW was
// local in this workload. No ordering certificate layout is needed.
pub open spec fn copied_by<S>(copies:Copies<S>,p:Path<C<S>,A>,w:Op) -> bool {
    exists|i:int| 0<=i<p.states.len() && crate::ordered_store::majority(copies(#[trigger] p.states[i],w))
}
pub open spec fn prefix_h<S>(copies:Copies<S>,p:Path<C<S>,A>,prior_majorities:Set<Op>,v:int,h:crate::RecoveredOrder) -> bool {
    crate::legal_recovery(h) && h.ops.no_duplicates() && h.ops.len()>0 && h.ops.last()==Op::SR1
        && !h.ops.contains(Op::SR2) && h.states[h.ops.len()-1]==v
        && (h.ops.len()>1 ==> {
            let writer=h.ops[h.ops.len()-2];
            prior_majorities.contains(writer) || copied_by(copies,p,writer)
        })
}
proof fn singleton_has_no_majority(q:Set<Replica>,owner:Replica)
    requires q.subset_of(set![owner]),
    ensures !crate::ordered_store::majority(q),
{}

// A constructive restriction on ANY compliant escape from the split cut.
// Both newly copying writes are excluded as a class, not just a named ACK.
// This clause excludes new replica copies. Dependencies on information
// about a prior copy or order are separate T audits.
pub proof fn first_opportunity_without_new_copies<S>(m:Machine<S>,b:Fork,value:spec_fn(S)->int,copies:Copies<S>)
        -> (p:Path<C<S>,A>)
    requires accepted(m,checkpoint_observations(b)),completed_quorum_sample(m,value,b),
        wait::no_await(run_step(m),done(m),|s|reached(m,s),grows(copies)),
        copies(state(m,b,3),Op::W1).subset_of(set![Replica::R1]),
        copies(state(m,b,3),Op::W2).subset_of(set![Replica::R2]),
    ensures wait::first_return(run_step(m),done(m),state(m,b,3),p),!wait::uses(p,grows(copies)),
        !copied_by(copies,p,Op::W1),!copied_by(copies,p,Op::W2),
        forall|past:Set<Op>,h:crate::RecoveredOrder| #![trigger prefix_h(copies,p,past,value((p.states.last().private)(Process::FirstClient)),h)] {
            let v=value((p.states.last().private)(Process::FirstClient));
            prefix_h(copies,p,past,v,h) ==> v==1 || (past.contains(Op::W1) && v==2) || (past.contains(Op::W2) && v==5)
        },
{
    actual_opportunity(m,b,value);
    let p=wait::extract_without_promotion(run_step(m),done(m),|s|reached(m,s),grows(copies),state(m,b,3),
        segment(m,b,3,first_return_len(m,b)));
    let u=p.states.last();let v=value((u.private)(Process::FirstClient));
    assert forall|i:int| 0<=i<p.states.len() implies !crate::ordered_store::majority(copies(#[trigger] p.states[i],Op::W1))
            && !crate::ordered_store::majority(copies(p.states[i],Op::W2)) by {
        no_growth(copies,p,i as nat,Op::W1);no_growth(copies,p,i as nat,Op::W2);
        singleton_has_no_majority(copies(p.states[i],Op::W1),Replica::R1);
        singleton_has_no_majority(copies(p.states[i],Op::W2),Replica::R2);
    }
    assert forall|past:Set<Op>,h:crate::RecoveredOrder| #[trigger] prefix_h(copies,p,past,v,h) implies
            v==1 || (past.contains(Op::W1) && v==2) || (past.contains(Op::W2) && v==5) by {
        if h.ops.len()>1 {
            let i=h.ops.len()-2;let w=h.ops[i];
            assert(w!=Op::SR1 && w!=Op::SR2);
            assert(h.states[i]==1 && h.states[i+1]==crate::next(w,1));
            assert(!copied_by(copies,p,w));
        }
    }
    p
}

pub open spec fn sampled<S>(p:Path<C<S>,A>,q:Set<Replica>,v:int) -> bool {
    exists|r:Replica,i:int| 0<=i<p.states.len() && q.contains(r) && (#[trigger] (p.states[i].net.locals)(r))==v
}
pub open spec fn supplied_genesis<S>(s:C<S>,a:A,u:C<S>,r:Replica) -> bool {
    (s.net.locals)(r)!=1 && (u.net.locals)(r)==1 && match a {
        Action::Local(at,Wire::Copy(v))=>at==r && v==1,
        Action::Deliver(id)=>s.net.pending.contains_key(id) && s.net.pending[id].to==at(r)
            && s.net.pending[id].path==crate::delivery::Path::Weak && s.net.pending[id].input==Wire::Copy(1),
        _=>false,
    }
}
proof fn find_install<S>(m:Machine<S>,p:Path<C<S>,A>,r:Replica,k:nat) -> (i:int)
    requires wait::valid_edges(run_step(m),p),p.states.len()==p.actions.len()+1,k<=p.actions.len(),
        (p.states[0].net.locals)(r)!=1,(p.states[k as int].net.locals)(r)==1,
    ensures 0<=i<k,supplied_genesis(p.states[i],p.actions[i],p.states[i+1],r),
    decreases k,
{
    let j=(k-1) as nat;
    if (p.states[j as int].net.locals)(r)==1 {find_install(m,p,r,j)} else {
        let s=p.states[j as int];let a=p.actions[j as int];let u=p.states[k as int];
        assert(run_step(m)(s,a,u));
        assert(crate::delivery::local_input(s.net,a,r)==Some(Wire::Copy(1)));
        j as int
    }
}

// Apply just the member-value clause, if it is valid for this hybrid read.
// A cannot guarantee that a stock run or a legitimate ordinary restore
// actually exists here. No survivor is asked to exchange data with a peer.
pub proof fn source_of_copy_free_first_response<S>(m:Machine<S>,b:Fork,value:spec_fn(S)->int,copies:Copies<S>,
    p:Path<C<S>,A>,q:Set<Replica>,h:crate::RecoveredOrder)
    requires wait::first_return(run_step(m),done(m),state(m,b,3),p),
        prefix_h(copies,p,Set::empty(),value((p.states.last().private)(Process::FirstClient)),h),
        !copied_by(copies,p,Op::W1),!copied_by(copies,p,Op::W2),
        sampled(p,q,value((p.states.last().private)(Process::FirstClient))),
    ensures value((p.states.last().private)(Process::FirstClient))==1,
        (q.contains(Replica::R3) && exists|i:int| 0<=i<p.states.len() && (#[trigger] (p.states[i].net.locals)(Replica::R3))==1)
        || exists|i:int,r:Replica| 0<=i<p.actions.len() && q.contains(r) && live_pair().contains(r)
            && #[trigger] supplied_genesis(p.states[i],p.actions[i],p.states[i+1],r),
{
    if h.ops.len()>1 {
        let w=h.ops[h.ops.len()-2];assert(w!=Op::SR1 && w!=Op::SR2);
    }
    let (r,k)=choose|r:Replica,k:int| 0<=k<p.states.len() && q.contains(r) && (#[trigger] (p.states[k].net.locals)(r))==1;
    if r!=Replica::R3 {
        let i=find_install(m,p,r,k as nat);
        assert(supplied_genesis(p.states[i],p.actions[i],p.states[i+1],r));
    }
}
}
