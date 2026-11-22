use vstd::prelude::*;
use crate::{Op,Replica};
use crate::facade_linear::CommandSemantics;
use crate::ordered_round::{self as base,Store};
use crate::ordered_store::Stamp;
use crate::stock_facade::{State,Method,initial};
use crate::checkpoint::Fork;
use crate::facade_hybrid::prefix;
use crate::read_recovery::Record;

verus! {

// A local weak RPC adapter for the same register and command API as the
// stock front end. Weak caller IDs are independent of the two strong calls.
pub type Id = (nat,nat); // weak client, that client's invocation number
pub struct Request { pub id:Id, pub site:Replica, pub method:Method }
pub struct Receipt { pub method:Method, pub before:int,pub after:int,pub response:int }
pub enum Packet { Request(Request), Reply(Id,int) }
pub struct World {
    pub front:State<Store>,pub wire:Map<nat,Packet>,
    pub issued:Set<Id>,pub answers:Map<Id,int>,pub stopped:Set<nat>,
    pub journal:spec_fn(Replica)->Map<Id,Receipt>,
}
pub enum Action { Send(nat,Request), Handle(nat), Receive(nat), Duplicate(nat,nat) }
pub open spec fn enabled(s:World,a:Action) -> bool {
    match a {
        Action::Send(slot,q)=>!s.wire.contains_key(slot) && !s.issued.contains(q.id) && !s.stopped.contains(q.id.0),
        Action::Handle(i)=>s.wire.contains_key(i) && s.wire[i] is Request && s.front.base.live.contains(s.wire[i]->Request_0.site),
        Action::Receive(i)=>s.wire.contains_key(i) && s.wire[i] is Reply && !s.stopped.contains(s.wire[i]->Reply_0.0),
        Action::Duplicate(i,j)=>s.wire.contains_key(i) && !s.wire.contains_key(j),
    }
}
pub open spec fn evaluate(f:CommandSemantics,q:Request,x:int) -> Receipt {
    let (new,returned)=match q.method {Method::Read=>(x,x),Method::Command(code)=>f(code,x)};
    Receipt {method:q.method,before:x,after:new,response:returned}
}
pub open spec fn serve(f:CommandSemantics,s:World,i:nat,q:Request) -> World {
    let seen=(s.journal)(q.site);
    if seen.contains_key(q.id) {
        World {wire:s.wire.insert(i,Packet::Reply(q.id,seen[q.id].response)),..s}
    } else {
        let entry=evaluate(f,q,(s.front.base.disk)(q.site).value);
        let disk=|r|if r==q.site {Stamp{value:entry.after,..(s.front.base.disk)(r)}} else {(s.front.base.disk)(r)};
        World {wire:s.wire.insert(i,Packet::Reply(q.id,entry.response)),
            journal:|r|if r==q.site {seen.insert(q.id,entry)} else {(s.journal)(r)},
            front:State{base:Store{disk,..s.front.base},..s.front},..s}
    }
}
pub open spec fn step(f:CommandSemantics,s:World,a:Action) -> World {
    match a {
        Action::Send(i,q)=>World {wire:s.wire.insert(i,Packet::Request(q)),issued:s.issued.insert(q.id),..s},
        Action::Handle(i)=>serve(f,s,i,s.wire[i]->Request_0),
        Action::Receive(i)=>World {answers:s.answers.insert(s.wire[i]->Reply_0,s.wire[i]->Reply_1),wire:s.wire.remove(i),..s},
        Action::Duplicate(i,j)=>World {wire:s.wire.insert(j,s.wire[i]),..s},
    }
}

// A bound on allocated network slots and per-client sequence numbers.
// Ordinary/background service can change the shared state and liveness.
// Only the weak RPC endpoints own these request IDs, replies and receipts.
pub open spec fn bounded(s:World,n:nat) -> bool {
    (forall|id:Id| #[trigger] s.issued.contains(id) ==> id.1<n)
    && (forall|id:Id| #[trigger] s.answers.contains_key(id) ==> id.1<n)
    && (forall|r:Replica,id:Id| #[trigger] (s.journal)(r).contains_key(id) ==> id.1<n)
    && forall|i:nat| #[trigger] s.wire.contains_key(i) ==> i<n && match s.wire[i] {
        Packet::Request(q)=>q.id.1<n, Packet::Reply(id,_)=>id.1<n,
    }
}
pub open spec fn paper_ops() -> CommandSemantics {
    |code:nat,x:int| (if code==0 {x+1} else {5*x},x)
}
pub open spec fn request(w:Op) -> Request {
    if w==Op::W1 {Request{id:(0,0),site:Replica::R1,method:Method::Command(0)}}
    else {Request{id:(1,0),site:Replica::R2,method:Method::Command(1)}}
}
pub open spec fn start() -> World {
    World {front:initial(base::engine(paper_ops())),wire:Map::empty(),issued:Set::empty(),answers:Map::empty(),
        stopped:Set::empty(),journal:|_r|Map::empty()}
}
pub open spec fn origin_only(s:World) -> bool {
    forall|r:Replica| {
        let log=#[trigger] (s.journal)(r);
        (log.contains_key(request(Op::W1).id) ==> r==Replica::R1)
            && (log.contains_key(request(Op::W2).id) ==> r==Replica::R2)
    }
}
// Both calls are outstanding before either site acts. The replies are
// consumed by their original weak clients, never by C1 or C2.
pub proof fn actual_overlap(b:Fork)
    ensures bounded(start(),0),({
        let f=paper_ops();let x=start();let q=request(Op::W1);let t=request(Op::W2);
        let one=step(f,x,Action::Send(0,q));let both=step(f,one,Action::Send(1,t));
        let left=step(f,both,Action::Handle(0));let right=step(f,both,Action::Handle(1));
        let lr=step(f,left,Action::Handle(1));let rl=step(f,right,Action::Handle(0));
        let got=step(f,lr,Action::Receive(0));let end=step(f,got,Action::Receive(1));
        enabled(x,Action::Send(0,q)) && enabled(one,Action::Send(1,t))
          && enabled(both,Action::Handle(0)) && enabled(both,Action::Handle(1))
          && enabled(left,Action::Handle(1)) && enabled(right,Action::Handle(0)) && lr==rl
          && enabled(lr,Action::Receive(0)) && enabled(got,Action::Receive(1))
          && end.answers.get(q.id)==Some(1) && end.answers.get(t.id)==Some(1)
          && end.wire.is_empty() && end.front==prefix(b,0)
          && origin_only(x) && origin_only(one) && origin_only(both)
          && origin_only(left) && origin_only(right) && origin_only(lr) && origin_only(rl) && origin_only(got) && origin_only(end)
          && projection((end.journal)(q.site)[q.id],Op::W1)==(crate::read_recovery::origin_records(f).records)(q.site)[0]
          && projection((end.journal)(t.site)[t.id],Op::W2)==(crate::read_recovery::origin_records(f).records)(t.site)[0]
    }),
{
    let f=paper_ops();let x=start();let both=step(f,step(f,x,Action::Send(0,request(Op::W1))),Action::Send(1,request(Op::W2)));
    let lr=step(f,step(f,both,Action::Handle(0)),Action::Handle(1));let rl=step(f,step(f,both,Action::Handle(1)),Action::Handle(0));
    crate::facade_hybrid::weak_calls_and_issued_offers(f,b);
    assert(lr.front.base.disk =~= rl.front.base.disk && lr.front.base.disk =~= prefix(b,0).base.disk);
    assert(lr.journal =~= rl.journal);assert(lr.wire =~= rl.wire);
    assert(step(f,step(f,lr,Action::Receive(0)),Action::Receive(1)).wire =~= Map::<nat,Packet>::empty());
}
pub open spec fn projection(entry:Receipt,w:Op) -> Record {
    Record {op:w,returned:entry.response,installed:entry.after}
}
}
