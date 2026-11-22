use vstd::prelude::*;
use crate::{Op,Replica};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Packet,Path as Route,Process};
use crate::facade_linear::CommandSemantics;
use crate::facade_transport::{actual_first_rpc,client1,valid,service};
use crate::facade_hybrid::{inner,joint,prefix,storage,weak_part};
use crate::fanout_replay as early;
use crate::ordered_round::{self as base,Store,Work};
use crate::ordered_store::{Stamp,majority};
use crate::metadata_reader::reference_read;
use crate::promotion_wait::*;
use crate::stock_facade::*;

verus! {

pub struct Cut { pub core:State<Store>, pub net:Network<int,Wire> }
pub struct Turn { pub ordinary:Event<Work>, pub wire:Action<Wire> }

pub open spec fn at_time(b:Fork,k:nat) -> Cut {
    let net=early::net(b,k);
    let core=if k>=5 {prefix(b,k)} else {
        let c=client1(b,early::local_index(Process::FirstClient,k));
        State {base:storage(net),closed:Set::empty(),calls:if k==0 {Map::empty()} else {Map::empty().insert(1nat,c)}}
    };
    Cut {net,core}
}

pub open spec fn data(p:Packet<Wire>) -> bool {
    p.path==Route::Weak && p.input is Copy
}
pub open spec fn genuine(p:Packet<Wire>) -> bool {
    data(p) && p.from is At && p.to is At && p.from!=p.to && (p.input==Wire::Copy(2) || p.input==Wire::Copy(5))
}
pub open spec fn offered(s:Cut,a:Action<Wire>) -> bool {
    match a {
        Action::Send(_,p) if data(p)=> genuine(p) && (s.core.base.disk)(p.from->At_0).value==p.input->Copy_0,
        _=>true,
    }
}

// This relation overapproximates the internal schedules of the no-restore
// implementation. It can pair ANY enabled ordinary action with a physical
// event. An impossibility for this larger relation also holds for the real
// schedules. The positive witnesses below check the joint decoder as well.
pub open spec fn apply_data(s:Cut,a:Turn) -> bool {
    match a.wire {
        Action::Deliver(id)=>s.net.pending.contains_key(id) && data(s.net.pending[id]),
        _=>false,
    }
}
// install=false is a diagnostic intervention on the installation alone.
// Even that delivery consumes the actual envelope. No prescribed reply
// containing the old branch payload may stand in for a fresh sample.
pub open spec fn transition(f:CommandSemantics,s:Cut,a:Turn,u:Cut,install:bool) -> bool {
    let raw=delivery::advance(|x,w|cell(x,w),s.net,a.wire);
    let next=crate::stock_facade::step(base::engine(f),s.core,a.ordinary);
    !(a.ordinary is Invoke) && enabled(base::engine(f),s.core,a.ordinary) && delivery::enabled(s.net,a.wire)
        && offered(s,a.wire) && if install || !apply_data(s,a) {
            u.net==raw && u.core==weak_part(next,s.net,a.wire)
        } else {u.net==(Network {locals:s.net.locals,..raw}) && u.core==next}
}
pub open spec fn step(f:CommandSemantics,s:Cut,a:Turn,u:Cut) -> bool {
    transition(f,s,a,u,true)
}
pub open spec fn response(s:Cut) -> bool { s.core.calls.contains_key(1) && s.core.calls[1].answer.is_some() }
pub open spec fn value_of(w:Op) -> int { crate::next(w,1) }

// Require an issued application packet, delivery to a different replica
// and a new materialized effect there. Merely sending/receiving a notice,
// or repeating installation of a value already there, does not qualify.
pub open spec fn installs(w:Op,s:Cut,a:Turn,u:Cut) -> bool {
    (w==Op::W1 || w==Op::W2) && match a.wire {
        Action::Deliver(id) if s.net.pending.contains_key(id)=>{
            let p=s.net.pending[id];
            genuine(p) && p.input==Wire::Copy(value_of(w)) &&
                (s.core.base.disk)(p.to->At_0).value!=value_of(w) && (u.core.base.disk)(p.to->At_0).value==value_of(w)
        },
        _=>false,
    }
}
pub open spec fn new_copy(s:Cut,a:Turn,u:Cut) -> bool {
    installs(Op::W1,s,a,u) || installs(Op::W2,s,a,u)
}
pub open spec fn original(r:Replica) -> Stamp {
    Stamp {version:0,value:match r {Replica::R1=>2,Replica::R2=>5,Replica::R3=>1}}
}
pub open spec fn split_leg(r:Replica,l:Leg) -> bool {
    match l {Leg::Received(v) | Leg::InFlight(v)=>v==original(r), _=>true}
}
pub open spec fn unchanged(s:Cut) -> bool {
    s.core.closed.is_empty() && s.core.base.calls.dom().is_empty() && s.core.calls.dom()==set![1nat]
        && s.core.calls[1].method is Read && !s.core.calls[1].submitted && !response(s)
        && (forall|r:Replica| #[trigger] (s.core.base.disk)(r)==original(r))
        && (forall|r:Replica| #[trigger] split_leg(r,(s.core.calls[1].legs)(r)))
        && forall|id:nat| #[trigger] s.net.pending.contains_key(id) && data(s.net.pending[id]) ==> genuine(s.net.pending[id])
}

proof fn rejects_every_split_quorum(c:Call)
    requires c.method is Read,!c.submitted,c.answer.is_none(),forall|r:Replica| #[trigger] split_leg(r,(c.legs)(r)),
    ensures early(c),!delegate(c), local_poll(c,None)==c,
{
    let q=rows(c);
    assert forall|r:Replica| #[trigger] q.contains_key(r) implies q[r]==original(r)
        by {assert(split_leg(r,(c.legs)(r)));}
    if majority(q.dom()) {
        let r=if q.contains_key(Replica::R1) {Replica::R1} else {Replica::R2};
        let t=if r==Replica::R1 && q.contains_key(Replica::R2) {Replica::R2} else {Replica::R3};
        assert(q.contains_key(r) && q.contains_key(t) && q[r].value!=q[t].value);
        assert(!crate::metadata_reader::unanimous(q) && !crate::metadata_reader::valid_root(q));
        assert(reference_read(Replica::R3)(q).is_none());
    }
}

pub proof fn before_a_new_copy(f:CommandSemantics,s:Cut,a:Turn,u:Cut)
    requires unchanged(s),step(f,s,a,u) || transition(f,s,a,u,false),!new_copy(s,a,u),
    ensures unchanged(u),
{
    let p=base::engine(f);let v=crate::stock_facade::step(p,s.core,a.ordinary);
    rejects_every_split_quorum(s.core.calls[1]);
    if let Event::Poll(id)=a.ordinary {assert(id==1);}
    if let Event::Work(Work::Serve(id,_))=a.ordinary {assert(!s.core.base.calls.contains_key(id));}
    assert(v.base.disk =~= s.core.base.disk);assert(v.closed =~= s.core.closed);
    assert forall|r:Replica| #[trigger] (u.core.base.disk)(r)==original(r) by {
        assert((s.core.base.disk)(r)==original(r));
        if let Action::Deliver(id)=a.wire {
            if data(s.net.pending[id]) {
                let pkt=s.net.pending[id];assert(genuine(pkt));
                if pkt.to==at(r) && pkt.input!=Wire::Copy(original(r).value) && (u.core.base.disk)(r)!=original(r) {
                    let w=if pkt.input==Wire::Copy(2) {Op::W1} else {Op::W2};
                    assert(installs(w,s,a,u));
                }
            }
        }
    }
    assert forall|r:Replica| #[trigger] split_leg(r,(u.core.calls[1].legs)(r)) by {assert(split_leg(r,(s.core.calls[1].legs)(r)));}
    assert forall|id:nat| #[trigger] u.net.pending.contains_key(id) && data(u.net.pending[id]) implies genuine(u.net.pending[id]) by {
        if s.net.pending.contains_key(id) {assert(s.net.pending[id]==u.net.pending[id]);}
    }
    assert(u.core.calls.dom() =~= s.core.calls.dom());
}

pub proof fn receipt_without_installation(f:CommandSemantics,b:Fork) -> (u:Cut)
    ensures ({
        let s=at_time(b,3);let a=action_at(b,3);let id=if b.branch==crate::Branch::Alpha {1nat} else {0nat};
        a.wire==Action::Deliver(id) && apply_data(s,a) && transition(f,s,a,u,false) && unchanged(u)
          && u.net.pending==at_time(b,4).net.pending && !u.net.pending.contains_key(id)
          && (u.core.base.disk)(Replica::R3).value==1
          && step(f,s,a,at_time(b,4)) && (at_time(b,4).core.base.disk)(Replica::R3).value==first_value(b)
    }),
{
    let s=at_time(b,3);let a=action_at(b,3);let with_copy=at_time(b,4);
    let n=Network {locals:s.net.locals,..with_copy.net};let u=Cut {net:n,core:s.core};
    split_cut(b);real_witness(f,b);
    let path=after_fanout(b);
    assert(step(f,path.states[0],path.actions[0],path.states[1]));
    let idle=crate::stock_facade::step(base::engine(f),s.core,a.ordinary);
    assert(idle.closed =~= s.core.closed);assert(idle==s.core);
    assert(transition(f,s,a,u,false));
    before_a_new_copy(f,s,a,u);u
}

pub proof fn split_cut(b:Fork)
    ensures unchanged(at_time(b,3)),at_time(b,3)==at_time(alpha(Notice::G),3),
{
    let s=at_time(b,3);let other=at_time(alpha(Notice::G),3);
    actual_first_rpc(b,5);actual_first_rpc(alpha(Notice::G),5);
    assert(s.core.calls.dom() =~= set![1nat]);
    assert(s.net.pending =~= other.net.pending);
    assert(s.net.locals =~= other.net.locals);
    assert(s.core.base.disk =~= other.core.base.disk);assert(s.core.base.live =~= other.core.base.live);
    assert(s.core.calls[1].legs =~= other.core.calls[1].legs);assert(s.core.calls =~= other.core.calls);
}

pub open spec fn action_at(b:Fork,k:nat) -> Turn {
    let wire=early::actions(b)[k as int];
    Turn {ordinary:inner(early::net(b,k),wire),wire}
}
pub open spec fn after_fanout(b:Fork) -> Path<Cut,Turn> {
    Path {states:Seq::new(12,|i:int|at_time(b,3+i as nat)),actions:Seq::new(11,|i:int|action_at(b,3+i as nat))}
}
pub open spec fn actual_first_step(f:CommandSemantics,b:Fork,k:nat) -> bool {
    let s=at_time(b,k); let u=at_time(b,k+1);let a=action_at(b,k);
    let c=if k==0 {fresh(Method::Read)} else {s.core.calls[1]};
    joint(f,s.net,a.wire,s.core,u.core) && valid(s.net,service(s.net,a.wire,Process::FirstClient),c,Process::FirstClient)
}
pub proof fn real_witness(f:CommandSemantics,b:Fork)
    ensures first_return(|s,a,u|step(f,s,a,u),|s|response(s),at_time(b,3),after_fanout(b)),
        (forall|k:nat| k<14 ==> #[trigger] actual_first_step(f,b,k)),
        (forall|i:int| #![trigger after_fanout(b).actions[i]] 0<=i<11 ==> {
            let path=after_fanout(b);
            new_copy(path.states[i],path.actions[i],path.states[i+1])==(i==0)
                && !installs(if b.branch==crate::Branch::Alpha {Op::W1} else {Op::W2},path.states[i],path.actions[i],path.states[i+1])
        }),
        at_time(b,14).core.calls[1].answer==Some(first_value(b)),
{
    hide(crate::facade_transport::at_time);early::same_physical_events(b);
    assert forall|k:nat| k<14 implies #[trigger] actual_first_step(f,b,k)
        && (k>=3 ==> step(f,at_time(b,k),action_at(b,k),at_time(b,k+1)) && !response(at_time(b,k))) by {
        early::same_physical_events(b);prefix_index(k as int);
        let s=at_time(b,k);let u=at_time(b,k+1); let n=s.net;let a=action_at(b,k);
        let c=if k==0 {fresh(Method::Read)} else {s.core.calls[1]};
        actual_first_rpc(b,early::local_index(Process::FirstClient,k));
        actual_first_rpc(b,early::local_index(Process::FirstClient,k+1));
        assert(valid(n,service(n,a.wire,Process::FirstClient),c,Process::FirstClient));
        assert(early::states(b)[k as int]==n && early::actions(b)[k as int]==a.wire);
        assert(delivery::enabled(n,a.wire));
        assert(u.net==delivery::advance(|x,w|cell(x,w),n,a.wire));
        if k>=5 {crate::facade_hybrid::real_prefix(f,b,k);}
        else {
            let mid=crate::stock_facade::step(base::engine(f),s.core,crate::facade_hybrid::invocation(s.core,n,a.wire));
            let post=weak_part(crate::stock_facade::step(base::engine(f),mid,a.ordinary),n,a.wire);
            assert(post.base.disk =~= u.core.base.disk);assert(post.base.live =~= u.core.base.live);
            assert(post.closed =~= u.core.closed);assert(post.calls[1].legs =~= u.core.calls[1].legs);
            assert(post.calls =~= u.core.calls);
        }
        assert(joint(f,n,a.wire,s.core,u.core));
        if k>=3 {
            let v=crate::stock_facade::step(base::engine(f),s.core,Event::Idle);
            assert(v.closed =~= s.core.closed);
            assert(v==s.core);
            assert(step(f,s,a,u));
        }
    }
    let path=after_fanout(b);
    assert forall|i:int| 0<=i<11 implies {
        let a=#[trigger] path.actions[i];let s=path.states[i];let u=path.states[i+1];
        new_copy(s,a,u)==(i==0) && !installs(if b.branch==crate::Branch::Alpha {Op::W1} else {Op::W2},s,a,u)
    } by {prefix_index(i);}
    assert(actual_first_step(f,b,3));
    actual_first_rpc(b,14);
    assert(response(path.states.last()));
    let transition: Relation<Cut,Turn>=|s,a,u|step(f,s,a,u);
    let done: spec_fn(Cut)->bool=|s|response(s);
    assert(path.states.len()==path.actions.len()+1 && path.states[0]==at_time(b,3));
    assert(!done(at_time(b,3)) && done(path.states.last()));
    assert forall|i:int| 0<=i<path.actions.len() implies transition(path.states[i],#[trigger] path.actions[i],path.states[i+1]) by {
        assert(actual_first_step(f,b,3+i as nat));
    }
    assert(valid_edges(transition,path));
    assert forall|i:int| 0<=i<path.actions.len() implies !done(#[trigger] path.states[i]) by {
        assert(actual_first_step(f,b,3+i as nat));
    }
    assert(pending_before(done,path));
}

proof fn unchanged_through(f:CommandSemantics,s:Cut,path:Path<Cut,Turn>,k:nat)
    requires unchanged(s),first_return(|s,a,u|step(f,s,a,u),|s|response(s),s,path),
        !uses(path,|s,a,u|new_copy(s,a,u)),k<=path.actions.len(),
    ensures unchanged(path.states[k as int]),
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat;unchanged_through(f,s,path,i);
        let nxt=|s,a,u|step(f,s,a,u);
        assert(nxt(path.states[i as int],path.actions[i as int],path.states[k as int]));
        assert(!new_copy(path.states[i as int],path.actions[i as int],path.states[k as int]));
        before_a_new_copy(f,path.states[i as int],path.actions[i as int],path.states[k as int]);
    }
}

pub proof fn delivery_alone_never_serves(f:CommandSemantics,b:Fork,path:Path<Cut,Turn>,k:nat)
    requires path.states.len()==path.actions.len()+1,path.states[0]==at_time(b,3),k<=path.actions.len(),
        valid_edges(|s,a,u|transition(f,s,a,u,false),path),
    ensures unchanged(path.states[k as int]),!response(path.states[k as int]),
    decreases k,
{
    if k==0 {split_cut(b);} else {
        let i=(k-1) as nat;delivery_alone_never_serves(f,b,path,i);
        let s=path.states[i as int];let a=path.actions[i as int];let u=path.states[k as int];
        assert(transition(f,s,a,u,false));
        if apply_data(s,a) {
            if let Event::Work(Work::Serve(id,_q))=a.ordinary {assert(!s.core.base.calls.contains_key(id));}
            assert(u.core.base.disk =~= s.core.base.disk);
        }
        assert(!new_copy(s,a,u));before_a_new_copy(f,s,a,u);
    }
}

// Restrict the overapproximation to the actual enabled front-end decoder.
// No client emits an additional message after the common fanout. An adapter
// may further restrict the physical schedules while admitting the two runs.
pub open spec fn physical(f:CommandSemantics,s:Cut,a:Turn,u:Cut) -> bool {
    let client=Process::FirstClient;
    step(f,s,a,u) && crate::fanout_service::internal(a.wire) && a.ordinary==inner(s.net,a.wire)
        && joint(f,s.net,a.wire,s.core,u.core) && valid(s.net,service(s.net,a.wire,client),s.core.calls[1],client)
}
pub proof fn any_admitted_restriction_waits(f:CommandSemantics,n:Notice,restricted:Relation<Cut,Turn>)
    requires forall|s:Cut,a:Turn,u:Cut| #[trigger] restricted(s,a,u) ==> step(f,s,a,u),
        valid_edges(restricted,after_fanout(alpha(n))),valid_edges(restricted,after_fanout(beta(n))),
    ensures ({
        let s=at_time(alpha(n),3);let d=|s|response(s);
        needs_class(restricted,d,s,|s,a,u|new_copy(s,a,u))
            && !needs_class(restricted,d,s,|s,a,u|installs(Op::W1,s,a,u))
            && !needs_class(restricted,d,s,|s,a,u|installs(Op::W2,s,a,u))
    }),
{
    hide(step);hide(unchanged);hide(new_copy);hide(installs);hide(actual_first_step);
    let a=alpha(n);let b=beta(n);let s=at_time(a,3);let done=|s|response(s);let big=|s,a,u|step(f,s,a,u);
    split_cut(a);split_cut(b);real_witness(f,a);real_witness(f,b);
    assert(first_return(restricted,done,s,after_fanout(a)));assert(first_return(restricted,done,s,after_fanout(b)));
    validator_awaits_replication(f,n);
    assert forall|p:Path<Cut,Turn>| #[trigger] first_return(restricted,done,s,p) implies uses(p,|s,a,u|new_copy(s,a,u)) by {
        assert forall|i:int| 0<=i<p.actions.len() implies big(p.states[i],#[trigger] p.actions[i],p.states[i+1])
            by {assert(restricted(p.states[i],p.actions[i],p.states[i+1]));}
        assert(first_return(big,done,s,p));
    }
    assert(!uses(after_fanout(a),|s,a,u|installs(Op::W1,s,a,u)));
    assert(!uses(after_fanout(b),|s,a,u|installs(Op::W2,s,a,u)));
}
pub proof fn actual_validator_has_class_wait(f:CommandSemantics,n:Notice)
    ensures needs_class(|s,a,u|physical(f,s,a,u),|s|response(s),at_time(alpha(n),3),|s,a,u|new_copy(s,a,u)),
{
    let small=|s,a,u|physical(f,s,a,u);
    assert forall|b:Fork| #[trigger] valid_edges(small,after_fanout(b)) by {
        real_witness(f,b);let p=after_fanout(b);
        assert forall|i:int| 0<=i<p.actions.len() implies small(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
            assert(step(f,p.states[i],p.actions[i],p.states[i+1]));
            assert(actual_first_step(f,b,3+i as nat));prefix_index(3+i);
        }
    }
    any_admitted_restriction_waits(f,n,small);
}

pub proof fn validator_awaits_replication(f:CommandSemantics,n:Notice)
    ensures ({
        let s=at_time(alpha(n),3);let next=|s,a,u|step(f,s,a,u);let done=|s|response(s);
        needs_class(next,done,s,|s,a,u|new_copy(s,a,u))
            && !needs_class(next,done,s,|s,a,u|installs(Op::W1,s,a,u))
            && !needs_class(next,done,s,|s,a,u|installs(Op::W2,s,a,u))
    }),
{
    hide(step);hide(unchanged);hide(actual_first_step);
    let a=alpha(n);let b=beta(n);let s=at_time(a,3);
    let next=|s,a,u|step(f,s,a,u);let done=|s|response(s);
    split_cut(a);split_cut(b);real_witness(f,a);real_witness(f,b);
    assert(first_return(next,done,s,after_fanout(a)));assert(first_return(next,done,s,after_fanout(b)));
    assert(can_finish(next,done,s));
    assert forall|p:Path<Cut,Turn>| #[trigger] first_return(next,done,s,p) implies uses(p,|s,a,u|new_copy(s,a,u)) by {
        if !uses(p,|s,a,u|new_copy(s,a,u)) {
            unchanged_through(f,s,p,p.actions.len());reveal(unchanged);
        }
    }
    assert(!uses(after_fanout(a),|s,a,u|installs(Op::W1,s,a,u)));
    assert(!uses(after_fanout(b),|s,a,u|installs(Op::W2,s,a,u)));
}

}
