use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Process,Path};
use crate::stock_facade::*;
use crate::facade_linear::CommandSemantics;
use crate::facade_transport::{Service,service,client1};
use crate::ordered_round::{self as base,Store,Work,engine};
use crate::ordered_store::Stamp;

verus! {

// There is ONE working cell per replica. Weak installations overwrite the
// value read by the backend and front end. The backend's tip is a ghost and
// is never a repair input. No ordinary image is stored separately here.
pub open spec fn storage(n: Network<int,Wire>) -> Store {
    Store { disk: |r| Stamp {version:0,value:(n.locals)(r)},
        live:all_replicas().filter(|r|delivery::live(n,at(r))),
        stopped:if n.first_stopped {set![1nat]} else {Set::empty()},..base::start() }
}
pub open spec fn prefix(b: Fork,k: nat) -> State<Store> {
    let map=if k>=3 {Map::empty().insert(1nat,client1(b,k))} else {Map::empty()};
    State {base:storage(state_after(b,k)),closed:Set::empty(),calls:if k>=17 {map.insert(2, fresh(Method::Read))} else {map}}
}
pub open spec fn request(e: Service,id: nat) -> Event<Work> {
    match e {Service::Rpc(r,st,_)=>Event::Rpc(id,r,st),Service::Poll=>Event::Poll(id),_=>Event::Idle}
}
pub open spec fn inner(n: Network<int,Wire>,a: Action<Wire>) -> Event<Work> {
    let c=service(n,a,Process::FirstClient); let d=service(n,a,Process::SecondClient);
    if !(c is Other) {request(c,1)} else if !(d is Other) {request(d,2)} else {
        match a {
            Action::CrashR3=>Event::Work(Work::Crash(Replica::R3)), Action::StopFirstClient=>Event::Work(Work::StopClient(1)),
            Action::StartSecondClient=>Event::Invoke(2,Method::Read), Action::Strong(Process::At(r))=>Event::Work(Work::Tick(r)),
            _=>Event::Idle,
        }
    }
}
pub open spec fn invocation(s: State<Store>,n: Network<int,Wire>,a: Action<Wire>) -> Event<Work> {
    if !s.calls.contains_key(1) && service(n,a,Process::FirstClient) is Rpc {Event::Invoke(1,Method::Read)} else {Event::Idle}
}
pub open spec fn weak_part(s: State<Store>,n: Network<int,Wire>,a: Action<Wire>) -> State<Store> {
    match a {
        Action::Deliver(id) if n.pending.contains_key(id) && n.pending[id].path==Path::Weak
            && n.pending[id].to is At && n.pending[id].input is Copy =>{
            let d=s.base; let p=n.pending[id];
            State { base:Store { disk:|r| if p.to==at(r) {Stamp {value:p.input->Copy_0,..(d.disk)(r)}} else {(d.disk)(r)}, ..d },..s }
        }, _=>s
    }
}
pub open spec fn joint(f: CommandSemantics,n: Network<int,Wire>,a: Action<Wire>,s: State<Store>,u: State<Store>) -> bool {
    let p=engine(f); let begin=invocation(s,n,a); let middle=step(p,s,begin); let ev=inner(n,a);
    delivery::enabled(n,a) && enabled(p,s,begin) && enabled(p,middle,ev)
        && u==weak_part(step(p,middle,ev),n,a)
        && !(input(s,begin) is Submit) && !(input(middle,ev) is Submit)
}

// Both external weak invocations are outstanding. Each RMW reads and
// returns the same shared cell that an ordinary RPC would sample here.
pub open spec fn weak_rmw(s:State<Store>,site:Replica,op:crate::Op) -> (State<Store>,int) {
    let old=(s.base.disk)(site);
    let disk=|r:Replica| if r==site {Stamp {value:crate::next(op,old.value),..old}} else {(s.base.disk)(r)};
    (State {base:Store{disk,..s.base},..s},old.value)
}
pub open spec fn prefix_entry(f:CommandSemantics,b:Fork) -> bool {
    let s=initial(engine(f));let r1=Replica::R1;let r2=Replica::R2;let r3=Replica::R3;
    let first=weak_rmw(s,r1,crate::Op::W1);let second=weak_rmw(s,r2,crate::Op::W2);
    let ab=weak_rmw(first.0,r2,crate::Op::W2);let ba=weak_rmw(second.0,r1,crate::Op::W1);
    let n=local_rmw_cells();
    let one=send(0,Path::Weak,at(r1),at(r3),Wire::Copy((ab.0.base.disk)(r1).value));
    let two=send(1,Path::Weak,at(r2),at(r3),Wire::Copy((ab.0.base.disk)(r2).value));
    let middle=delivery::advance(|x,w|cell(x,w),n,one);
    first.1==1 && second.1==1 && ab.1==1 && ba.1==1 && ab.0==ba.0 && ab.0==prefix(b,0)
        && joint(f,n,one,ab.0,ab.0) && joint(f,middle,two,ab.0,prefix(b,0))
        && delivery::advance(|x,w|cell(x,w),middle,two)==state_after(b,0)
}
pub proof fn weak_calls_and_issued_offers(f:CommandSemantics,b:Fork)
    ensures prefix_entry(f,b),
{
    origin_updates_are_actually_offered();crate::isolated_rmws();prefix_transport_is_enabled(b);
    let s=initial(engine(f));let r1=Replica::R1;let r2=Replica::R2;
    let ab=weak_rmw(weak_rmw(s,r1,crate::Op::W1).0,r2,crate::Op::W2).0;
    let ba=weak_rmw(weak_rmw(s,r2,crate::Op::W2).0,r1,crate::Op::W1).0;
    assert(ab.base.disk =~= ba.base.disk);assert(ab.base.disk =~= prefix(b,0).base.disk);
    assert(prefix(b,0).base.live =~= all_replicas());
    assert(ab==prefix(b,0) && ba==ab);
    let n=local_rmw_cells();let r3=Replica::R3;
    let one=send(0,Path::Weak,at(r1),at(r3),Wire::Copy(2));
    let two=send(1,Path::Weak,at(r2),at(r3),Wire::Copy(5));
    let middle=delivery::advance(|x,w|cell(x,w),n,one);
    assert(step(engine(f),ab,Event::Idle).closed =~= ab.closed);
    assert(step(engine(f),ab,Event::Idle)==ab);
    assert(joint(f,n,one,ab,ab));assert(joint(f,middle,two,ab,prefix(b,0)));
    assert(checkpoint_states(b)[0]==state_after(b,0) && state_after(b,0)==after_local_rmws());
    assert(delivery::advance(|x,w|cell(x,w),middle,two)==after_local_rmws());
}

}
