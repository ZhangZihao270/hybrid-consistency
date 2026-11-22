use vstd::prelude::*;
use crate::{Replica,origin};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Process};
use crate::facade_hybrid::{inner,weak_part};
use crate::facade_transport::{service,valid};
use crate::facade_linear::CommandSemantics;
use crate::first_copy_wait::{Cut,Turn,offered,genuine,data,response};
use crate::ordered_round::{engine,Work};
use crate::ordered_store::{Stamp,majority};
use crate::stock_facade::*;
use crate::genesis_escape::resolver;
use crate::genesis_service::{rebuild,can_rebuild};
use crate::fallback_program::{self as program,apply_event};
use crate::second_copy_schedule as sched;
use crate::promotion_wait::*;

verus! {

// All enabled ordinary work, without new application invocations. A configured
// site may also rebuild from its ordinary genesis at position zero. The larger
// relation even lets the ordinary and transport schedulers move independently.
pub open spec fn step(f:CommandSemantics,repairs:Set<Replica>,s:Cut,a:Turn,u:Cut) -> bool {
    let v=apply_event(resolver(),engine(f),s.core,a.ordinary);
    !(a.ordinary is Invoke) && enabled(engine(f),s.core,a.ordinary) && delivery::enabled(s.net,a.wire)
        && offered(s,a.wire) && u.net==delivery::advance(|x,w|cell(x,w),s.net,a.wire)
        && match a.wire {
            Action::Local(r,Wire::Copy(x))=>x==1 && repairs.contains(r) && can_rebuild(v,r) && u.core==rebuild(v,r),
            _=>u.core==weak_part(v,s.net,a.wire),
        }
}
pub open spec fn physical(f:CommandSemantics,repairs:Set<Replica>,s:Cut,a:Turn,u:Cut) -> bool {
    step(f,repairs,s,a,u) && crate::fanout_service::internal(a.wire) && a.ordinary==inner(s.net,a.wire)
        && valid(s.net,service(s.net,a.wire,Process::FirstClient),s.core.calls[1],Process::FirstClient)
}
pub open spec fn emitted(l:Leg,v:spec_fn(int)->bool,r:Replica) -> bool {
    match l {Leg::Received(x) | Leg::InFlight(x)=>x.version==0 && (r==Replica::R3 ==> v(x.value)),_=>true}
}
pub open spec fn anchored(b:Fork,c:Call) -> bool {
    c.method is Read && !c.submitted &&
        (c.legs)(origin(b.branch))==Leg::Received(Stamp{version:0,value:first_value(b)})
}
// Once an origin sample is saved, the fallback requires an actual R3 sample.
// It must be genesis or the same value as that origin, even on three replies.
proof fn poll_source(b:Fork,c:Call,ok:spec_fn(int)->bool)
    requires anchored(b,c),forall|r:Replica| #[trigger] emitted((c.legs)(r),ok,r),
    ensures early(c),!delegate(c),match resolver()(rows(c)) {
        Some(v)=> (v==1 || v==first_value(b)) && ok(v) && rows(c).get(Replica::R3)==Some(Stamp{version:0,value:v}),
        None=>true,
    },
{
    let m=rows(c);let r3=Replica::R3;let a=origin(b.branch);
    assert(m.contains_key(a) && first_value(b)!=1);
    assert forall|r:Replica| #[trigger] m.contains_key(r) implies m[r].version==0 by {assert(emitted((c.legs)(r),ok,r));}
    assert(!crate::metadata_reader::valid_root(m));
    if crate::metadata_reader::reference_read(r3)(m).is_some() {
        crate::quorum_rpc::latest_is_a_sample(m);
        let r=crate::quorum_rpc::latest_site(m);
        assert(crate::metadata_reader::unanimous(m) && m.contains_key(r3));
        assert(m[r].value==m[a].value && m[r3].value==m[a].value);
    }
    assert(emitted((c.legs)(r3),ok,r3));
}
pub open spec fn audit(b:Fork,s:Cut,ok:spec_fn(int)->bool) -> bool {
    let c=s.core.calls[1];let r3=Replica::R3;
    s.core.closed.is_empty() && s.core.base.calls.is_empty() && s.core.calls.dom()==set![1nat]
        && anchored(b,c) && ok((s.core.base.disk)(r3).value)
        && (forall|r:Replica| #[trigger] emitted((c.legs)(r),ok,r))
        && (forall|id:nat| #[trigger] s.net.pending.contains_key(id) && data(s.net.pending[id]) ==> genuine(s.net.pending[id]))
        && match c.answer {None=>true,Some(v)=>(v==1 || v==first_value(b)) && ok(v)}
}
// Trace the transition producing a fresh value at R3, including the
// authenticated, already-issued application packet for a copy. Zero
// version is an ordinary storage fact, not a weak order certificate.
pub open spec fn source(v:int,s:Cut,a:Turn,u:Cut) -> bool {
    let r=Replica::R3;
    (s.core.base.disk)(r).value!=v && (u.core.base.disk)(r).value==v && match a.wire {
        Action::Local(site,Wire::Copy(x))=>site==r && x==1 && v==1,
        Action::Deliver(id)=>s.net.pending.contains_key(id) && genuine(s.net.pending[id])
            && s.net.pending[id].to==at(r) && s.net.pending[id].input==Wire::Copy(v),
        _=>false,
    }
}
proof fn entry(b:Fork,ok:spec_fn(int)->bool)
    requires ok(first_value(sched::rival(b))),
    ensures audit(b,program::cut(b,11),ok),
{
    let s=program::cut(b,11);
    assert(s.core.calls.dom() =~= set![1nat]);
    assert forall|r:Replica| #[trigger] emitted((s.core.calls[1].legs)(r),ok,r) by {};
    assert forall|id:nat| #[trigger] s.net.pending.contains_key(id) && data(s.net.pending[id]) implies genuine(s.net.pending[id]) by {};
}
proof fn preserve(b:Fork,f:CommandSemantics,repairs:Set<Replica>,s:Cut,a:Turn,u:Cut,ok:spec_fn(int)->bool)
    requires audit(b,s,ok),step(f,repairs,s,a,u),
        forall|v:int| #[trigger] source(v,s,a,u) ==> ok(v),
    ensures audit(b,u,ok),
{
    let p=engine(f);let v=apply_event(resolver(),p,s.core,a.ordinary);let c=s.core.calls[1];let r3=Replica::R3;
    poll_source(b,c,ok);
    if let Event::Poll(id)=a.ordinary {assert(id==1);}
    if let Event::Work(Work::Serve(id,_))=a.ordinary {assert(!s.core.base.calls.contains_key(id));}
    assert(v.base.disk =~= s.core.base.disk);assert(v.closed =~= s.core.closed);
    assert(u.core.calls.dom() =~= s.core.calls.dom());
    assert forall|r:Replica| #[trigger] emitted((u.core.calls[1].legs)(r),ok,r) by {
        assert(emitted((c.legs)(r),ok,r));
    }
    let x=(u.core.base.disk)(r3).value;
    if x!=(s.core.base.disk)(r3).value {
        if let Action::Deliver(id)=a.wire {assert(data(s.net.pending[id]) && genuine(s.net.pending[id]));}
        assert(source(x,s,a,u));
    }
    assert forall|id:nat| #[trigger] u.net.pending.contains_key(id) && data(u.net.pending[id]) implies genuine(u.net.pending[id]) by {
        if s.net.pending.contains_key(id) {assert(s.net.pending[id]==u.net.pending[id]);}
    }
}
proof fn through(b:Fork,f:CommandSemantics,repairs:Set<Replica>,path:Path<Cut,Turn>,ok:spec_fn(int)->bool,k:nat)
    requires path.states.len()==path.actions.len()+1,path.states[0]==program::cut(b,11),k<=path.actions.len(),
        valid_edges(|s,a,u|step(f,repairs,s,a,u),path),ok(first_value(sched::rival(b))),
        forall|i:int,v:int| 0<=i<path.actions.len() && #[trigger] source(v,path.states[i],path.actions[i],path.states[i+1]) ==> ok(v),
    ensures audit(b,path.states[k as int],ok),
    decreases k,
{
    if k==0 {entry(b,ok);} else {
        let i=(k-1) as nat;through(b,f,repairs,path,ok,i);
        assert(step(f,repairs,path.states[i as int],path.actions[i as int],path.states[k as int]));
        preserve(b,f,repairs,path.states[i as int],path.actions[i as int],path.states[k as int],ok);
    }
}
pub proof fn every_return_has_a_source(b:Fork,f:CommandSemantics,repairs:Set<Replica>,path:Path<Cut,Turn>)
    requires first_return(|s,a,u|step(f,repairs,s,a,u),|s|response(s),program::cut(b,11),path),
    ensures ({
        let v=path.states.last().core.calls[1].answer.unwrap();
        (v==1 || v==first_value(b)) && uses(path,|s,a,u|source(v,s,a,u))
            && (v==1 ==> repairs.contains(Replica::R3))
    }),
{
    let k=path.actions.len();let v=path.states.last().core.calls[1].answer.unwrap();
    through(b,f,repairs,path,|x|true,k);
    if !uses(path,|s,a,u|source(v,s,a,u)) {
        assert forall|i:int,x:int| 0<=i<k && #[trigger] source(x,path.states[i],path.actions[i],path.states[i+1]) implies x!=v by {
            if x==v {assert(!source(v,path.states[i],path.actions[i],path.states[i+1]));}
        }
        through(b,f,repairs,path,|x|x!=v,k);
    }
    if v==1 {
        let i=choose|i:int| 0<=i<k && source(v,path.states[i],#[trigger] path.actions[i],path.states[i+1]);
        assert(step(f,repairs,path.states[i],path.actions[i],path.states[i+1]));
    }
}
pub open spec fn turn(b:Fork,k:nat) -> Turn {
    let a=sched::action(b,k);Turn{ordinary:inner(sched::net(b,k),a),wire:a}
}
pub open spec fn completion(b:Fork) -> Path<Cut,Turn> {
    Path {states:Seq::new(6,|i:int|program::cut(b,11+i as nat)),actions:Seq::new(5,|i:int|turn(b,11+i as nat))}
}
pub proof fn switched_returns(b:Fork,f:CommandSemantics,repairs:Set<Replica>)
    ensures first_return(|s,a,u|physical(f,repairs,s,a,u),|s|response(s),program::cut(b,11),completion(b)),
        completion(b).states.last().core.calls[1].answer==Some(first_value(b)),
{
    let p=completion(b);
    assert forall|i:int| 0<=i<p.actions.len() implies physical(f,repairs,p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
        let k=11+i as nat;program::executes_switched_prefix(f,b,k);prefix_index(k as int);
        let s=p.states[i];let idle=apply_event(resolver(),engine(f),s.core,Event::Idle);
        assert(idle.closed =~= s.core.closed);assert(idle==s.core);
    }
    assert(pending_before(|s|response(s),p));
}
pub proof fn fallback_awaits_target_installation(b:Fork,f:CommandSemantics,repairs:Set<Replica>)
    requires !repairs.contains(Replica::R3),
    ensures needs_class(|s,a,u|physical(f,repairs,s,a,u),|s|response(s),program::cut(b,11),
        |s,a,u|source(first_value(b),s,a,u)),
{
    let step=|s,a,u|physical(f,repairs,s,a,u);let done=|s|response(s);let cut=program::cut(b,11);
    switched_returns(b,f,repairs);assert(can_finish(step,done,cut));
    assert forall|p:Path<Cut,Turn>| #[trigger] first_return(step,done,cut,p)
        implies uses(p,|s,a,u|source(first_value(b),s,a,u)) by {
        assert forall|i:int| 0<=i<p.actions.len() implies self::step(f,repairs,p.states[i],#[trigger] p.actions[i],p.states[i+1])
            by {assert(step(p.states[i],p.actions[i],p.states[i+1]));}
        every_return_has_a_source(b,f,repairs,p);
    }
}
}
