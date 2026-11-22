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
pub open spec fn fresh(s:World,q:Request) -> bool {
    !s.issued.contains(q.id) && !s.answers.contains_key(q.id)
        && !(s.journal)(q.site).contains_key(q.id)
}
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
pub open spec fn finish(f:CommandSemantics,s:World,i:nat,q:Request) -> World {
    step(f,step(f,step(f,s,Action::Send(i,q)),Action::Handle(i)),Action::Receive(i))
}
// Existential one-RTT service for EVERY register method, any live replica
// and nonfaulty requester. No assumption about agreement of replica states,
// a weak status, an ordinary image, or background protocol progress.
pub proof fn any_method_one_local_round(f:CommandSemantics,s:World,i:nat,q:Request)
    requires fresh(s,q),!s.wire.contains_key(i),s.front.base.live.contains(q.site),!s.stopped.contains(q.id.0),
    ensures ({
        let sent=step(f,s,Action::Send(i,q));let handled=step(f,sent,Action::Handle(i));let u=finish(f,s,i,q);
        let entry=evaluate(f,q,(s.front.base.disk)(q.site).value);
        enabled(s,Action::Send(i,q)) && enabled(sent,Action::Handle(i)) && enabled(handled,Action::Receive(i))
          && sent.wire[i]==Packet::Request(q) && handled.wire[i]==Packet::Reply(q.id,entry.response)
          && u.wire==s.wire && (u.front.base.disk)(q.site).value==entry.after
          && u.answers.get(q.id)==Some(entry.response) && (u.journal)(q.site).get(q.id)==Some(entry)
          && u.front.calls==s.front.calls && u.front.closed==s.front.closed
          && forall|r:Replica| r!=q.site ==> (#[trigger] (u.front.base.disk)(r))==(s.front.base.disk)(r)
                && (u.journal)(r)==(s.journal)(r)
    }),
{
    assert(finish(f,s,i,q).wire =~= s.wire);
}
pub proof fn delayed_duplicate_keeps_original_result(f:CommandSemantics,s:World,i:nat,q:Request)
    requires enabled(s,Action::Handle(i)),s.wire[i]==Packet::Request(q),(s.journal)(q.site).contains_key(q.id),
    ensures ({
        let u=step(f,s,Action::Handle(i));
        u.front==s.front && u.journal==s.journal && u.wire[i]==Packet::Reply(q.id,(s.journal)(q.site)[q.id].response)
    }),
{}

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
pub open spec fn increment(a:Option<Action>) -> nat {
    match a {Some(Action::Send(i,q))=>1+i+q.id.1,Some(Action::Duplicate(_,j))=>1+j,_=>0}
}
pub open spec fn ports_step(f:CommandSemantics,s:World,a:Option<Action>,u:World) -> bool {
    match a {
        Some(ev)=>enabled(s,ev) && u==step(f,s,ev),
        None=>u==World {front:u.front,stopped:u.stopped,..s},
    }
}
proof fn preserves_bound(f:CommandSemantics,s:World,a:Option<Action>,u:World,n:nat)
    requires bounded(s,n),ports_step(f,s,a,u),
    ensures bounded(u,n+increment(a)),
{
    if let Some(Action::Handle(i))=a {assert(s.wire.contains_key(i));}
    if let Some(Action::Receive(i))=a {assert(s.wire.contains_key(i));}
    if let Some(Action::Duplicate(i,_j))=a {assert(s.wire.contains_key(i));}
    assert forall|id:Id| #[trigger] u.issued.contains(id) implies id.1<n+increment(a) by {
        if s.issued.contains(id) {assert(id.1<n);}
    }
    assert forall|id:Id| #[trigger] u.answers.contains_key(id) implies id.1<n+increment(a) by {
        if s.answers.contains_key(id) {assert(id.1<n);}
    }
    assert forall|i:nat| #[trigger] u.wire.contains_key(i) implies i<n+increment(a) && match u.wire[i] {
        Packet::Request(q)=>q.id.1<n+increment(a),Packet::Reply(id,_)=>id.1<n+increment(a),
    } by {if s.wire.contains_key(i) {assert(i<n);}}
    assert forall|r:Replica,id:Id| #[trigger] (u.journal)(r).contains_key(id) implies id.1<n+increment(a) by {
        if (s.journal)(r).contains_key(id) {assert(id.1<n);}
    }
}
pub open spec fn bound(a:Seq<Option<Action>>,k:nat) -> nat decreases k {
    if k==0 {0} else {bound(a,(k-1) as nat)+increment(a[k-1])}
}
proof fn allocation_after_prefix(f:CommandSemantics,t:Seq<World>,a:Seq<Option<Action>>,k:nat)
    requires t.len()==a.len()+1,k<=a.len(),bounded(t[0],0),
        forall|i:int| 0<=i<a.len() ==> ports_step(f,t[i],#[trigger] a[i],t[i+1]),
    ensures bounded(t[k as int],bound(a,k)),
    decreases k,
{
    if k>0 {
        let j=(k-1) as nat;allocation_after_prefix(f,t,a,j);
        preserves_bound(f,t[j as int],a[j as int],t[k as int],bound(a,j));
    }
}
pub proof fn local_round_after_any_prefix(f:CommandSemantics,t:Seq<World>,a:Seq<Option<Action>>,client:nat,r:Replica,method:Method)
        -> (serial:nat)
    requires t.len()==a.len()+1,bounded(t[0],0),t.last().front.base.live.contains(r),!t.last().stopped.contains(client),
        forall|i:int| 0<=i<a.len() ==> ports_step(f,t[i],#[trigger] a[i],t[i+1]),
    ensures ({
        let s=t.last();let q=Request{id:(client,serial),site:r,method};let sent=step(f,s,Action::Send(serial,q));
        let handled=step(f,sent,Action::Handle(serial));let u=finish(f,s,serial,q);
        fresh(s,q) && enabled(s,Action::Send(serial,q)) && enabled(sent,Action::Handle(serial))
          && enabled(handled,Action::Receive(serial)) && u.answers.get(q.id)==Some(evaluate(f,q,(s.front.base.disk)(r).value).response)
          && u.wire==s.wire
    }),
{
    allocation_after_prefix(f,t,a,a.len());let n=bound(a,a.len());let s=t.last();
    let q=Request{id:(client,n),site:r,method};assert(!(s.journal)(r).contains_key(q.id));
    any_method_one_local_round(f,s,n,q);n
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
// Once both weak clients have received their responses, this adapter can
// only serve another application call if a client actually issues one.
// The separate background data offers to R3 remain in the HOT transport.
pub proof fn quiet_weak_ports(s:World,a:Action)
    requires s.wire.is_empty(),!(a is Send),
    ensures !enabled(s,a),
{}
}
