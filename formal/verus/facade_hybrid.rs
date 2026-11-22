use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Process,Path};
use crate::stock_facade::*;
use crate::facade_progress::{Run,front_fair,scheduled,project};
use crate::facade_linear::CommandSemantics;
use crate::facade_transport::{Service,service,client1,client2,actual_first_rpc,actual_second_rpc};
use crate::metadata_fair::{network,background,pending_after_all_live_deliveries};
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
pub open spec fn suffix(b: Fork,k: nat) -> State<Store> {
    State {base:storage(network(b,k)),closed:Set::empty(),calls:Map::empty().insert(1nat,client1(b,17)).insert(2,client2(b,k))}
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

// The first two weak RMWs are local, with the ordinary store still at
// position zero. This includes the two real initial offers in the mailbox.
pub proof fn real_prefix(f: CommandSemantics,b: Fork,k: nat)
    requires k<17,
    ensures joint(f,state_after(b,k),actions_to_crash(b)[k as int],prefix(b,k),prefix(b,k+1)),
{
    hide(crate::facade_transport::at_time);
    prefix_index(k as int); actual_first_rpc(b,k); actual_first_rpc(b,k+1); prefix_transport_is_enabled(b);
    let n=state_after(b,k); let a=actions_to_crash(b)[k as int]; let p=engine(f); let s=prefix(b,k);let u=prefix(b,k+1);
    let m=step(p,s,invocation(s,n,a)); let ordinary=step(p,m,inner(n,a)); let post=weak_part(ordinary,n,a);
    assert(m.base==s.base && m.closed =~= s.closed);
    assert(ordinary.base.disk =~= s.base.disk);
    assert(post.base.disk =~= u.base.disk);assert(post.base.live =~= u.base.live);assert(post.closed =~= u.closed);
    assert(post.calls =~= u.calls) by {
        if post.calls.contains_key(1) {
            assert(post.calls[1].legs =~= u.calls[1].legs);
        }
    }
    assert(delivery::enabled(n,a)) by {assert(checkpoint_states(b)[k as int]==n);}
}
pub proof fn real_suffix(f: CommandSemantics,b: Fork,k: nat)
    ensures joint(f,network(b,k),background(b,k),suffix(b,k),suffix(b,k+1)),
{
    hide(crate::facade_transport::at_time);
    if k<14 {prefix_index(k as int);}
    actual_second_rpc(b,k);actual_second_rpc(b,k+1);actual_first_rpc(b,17);
    crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R1);crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R2);
    let n=network(b,k);let a=background(b,k);let s=suffix(b,k);let u=suffix(b,k+1);let p=engine(f);
    let m=step(p,s,invocation(s,n,a));let ordinary=step(p,m,inner(n,a));let post=weak_part(ordinary,n,a);
    assert(m.base==s.base && m.closed =~= s.closed);
    assert(ordinary.base.disk =~= s.base.disk);
    assert(post.base.disk =~= u.base.disk);assert(post.base.live =~= u.base.live);assert(post.closed =~= u.closed);
    assert(post.calls[2].legs =~= u.calls[2].legs);assert(post.calls =~= u.calls);
}

pub open spec fn projected(b: Fork) -> Run<Store,Work> {
    crate::stock_availability::Stream {state:|i|suffix(b,i),event:|i|inner(network(b,i),background(b,i))}
}
proof fn stock_turn(e: crate::facade_progress::StockRun<Store,Work>,i: nat,j: nat,w: Work)
    requires j>=i,(e.event)(j)==Input::Work(w) || !base::ready((e.state)(j),Input::Work(w)),
    ensures base::scheduled(e,i,w),
{ assert(base::served_or_disabled(e,j,w)); }
proof fn front_turn(f: CommandSemantics,e: Run<Store,Work>,i:nat,j:nat,a: Event<Work>)
    requires j>=i,(e.event)(j)==a || !enabled(engine(f),(e.state)(j),a),
    ensures scheduled(engine(f),e,a,i),
{ assert((e.event)(j)==a || !enabled(engine(f),(e.state)(j),a)); }
pub proof fn real_workers_are_fair(f: CommandSemantics,b: Fork)
    ensures base::fair(project(projected(b))),front_fair(engine(f),projected(b)),
{
    let e=projected(b);let z=project(e);let p=engine(f);
    assert forall|i: nat,id:nat,q: Set<Replica>| #[trigger] base::scheduled(z,i,Work::Serve(id,q)) by {
        let j=i+14;stock_turn(z,i,j,Work::Serve(id,q));
    }
    assert forall|i: nat,r: Replica| #[trigger] base::scheduled(z,i,Work::Tick(r)) by {
        let d:nat=if r==Replica::R1 {0} else {1};let j=3*(i+14)+d;assert(j%3==d);
        stock_turn(z,i,j,Work::Tick(r));
    }
    assert forall|i: nat,id: nat| #[trigger] scheduled(p,e,Event::Poll(id),i) by {
        let j=3*(i+14)+2;assert(j%3==2);assert((e.event)(j)==Event::Poll(2));
        front_turn(f,e,i,j,Event::Poll(id));
    }
    assert forall|i: nat,id:nat,r:Replica,st:Stage| #[trigger] scheduled(p,e,Event::Rpc(id,r,st),i) by {
        let j=i+14;actual_first_rpc(b,17);actual_second_rpc(b,j);
        assert(rows(client2(b,j)).dom() =~= live_pair());let a=Event::Rpc(id,r,st);
        assert(!enabled(p,(e.state)(j),a));front_turn(f,e,i,j,a);
    }
}

pub open spec fn completed_sr1(b:Fork) -> bool {
    prefix(b,17)==suffix(b,0) && prefix(b,17).calls[1].answer==Some(first_value(b))
}
pub open spec fn post_step(f:CommandSemantics,b:Fork,k:nat) -> bool {
    joint(f,network(b,k),background(b,k),suffix(b,k),suffix(b,k+1))
        && suffix(b,k).calls[2].answer.is_none() && !suffix(b,k).calls[2].submitted && suffix(b,k).base.calls.is_empty()
}
pub open spec fn physical_path(f:CommandSemantics,b:Fork) -> bool {
    completed_sr1(b)
    && (forall|k:nat| k<17 ==> #[trigger] joint(f,state_after(b,k),actions_to_crash(b)[k as int],prefix(b,k),prefix(b,k+1)))
    && forall|k:nat| #[trigger] post_step(f,b,k)
}
pub(crate) proof fn join_read_prefix(b:Fork)
    ensures completed_sr1(b),
{
    hide(crate::facade_transport::at_time);actual_first_rpc(b,17);actual_second_rpc(b,0);
    assert(network(b,0).locals =~= state_after(b,17).locals);
    assert(prefix(b,17).base.disk =~= suffix(b,0).base.disk);assert(prefix(b,17).base.live =~= suffix(b,0).base.live);
    assert(client2(b,0).legs =~= fresh(Method::Read).legs);
    assert(prefix(b,17).calls =~= suffix(b,0).calls);
}
proof fn actual_program_path(f:CommandSemantics,b:Fork)
    ensures physical_path(f,b),
{
    hide(joint);hide(completed_sr1);hide(crate::facade_transport::at_time);join_read_prefix(b);
    assert forall|k:nat| k<17 implies #[trigger] joint(f,state_after(b,k),actions_to_crash(b)[k as int],prefix(b,k),prefix(b,k+1))
        by {real_prefix(f,b,k);}
    assert forall|k:nat| #[trigger] post_step(f,b,k) by {real_suffix(f,b,k);actual_second_rpc(b,k);}
}
pub proof fn same_stock_program_on_fair_hybrid(f: CommandSemantics,b: Fork)
    ensures ({
        let p=engine(f);
        crate::facade_contract::all_calls_served(p,|e|base::fair(e)) && crate::facade_contract::any_read_quorum(p,base::used())
        && crate::facade_contract::read_values_valid(p,base::used()) && crate::facade_contract::outer_linearizable(p,f)
        && prefix_entry(f,b) && physical_path(f,b) && pre_sr1_g(b,weak_assignment(b,true).ops)
        && base::fair(project(projected(b))) && front_fair(p,projected(b))
        && crate::progress::delivery_fair(crate::metadata_fair::run(b))
        && crate::progress::process_fair(crate::metadata_fair::run(b),|s,p|delivery::live(s,p))
    }),
{
    hide(crate::facade_contract::all_calls_served);hide(crate::facade_contract::any_read_quorum);
    hide(crate::facade_contract::read_values_valid);hide(crate::facade_contract::outer_linearizable);
    hide(crate::confirmation::admissible_service);hide(base::fair);hide(front_fair);hide(physical_path);hide(prefix_entry);
    hide(crate::progress::delivery_fair);hide(crate::progress::process_fair);
    weak_calls_and_issued_offers(f,b);actual_program_path(f,b);
    base::concrete_full_a(f);real_workers_are_fair(f,b);pending_after_all_live_deliveries(b);
}

// Direct strong RPCs retain their honest request/reply slots. None can
// write a shared cell, publish C1's response to C2, or update the engine.
pub proof fn direct_read_effects(f:CommandSemantics,s:State<Store>,id:nat,a:Event<Work>)
    requires s.calls.contains_key(id),s.calls[id].method is Read,enabled(engine(f),s,a),
        (a==Event::Poll(id) && !delegate(s.calls[id])) || (a is Rpc && a->Rpc_0==id),
    ensures input(s,a) is Idle,step(engine(f),s,a).base==s.base,
        step(engine(f),s,a).closed==s.closed,
        forall|other:nat| other!=id ==> #[trigger] step(engine(f),s,a).calls.get(other)==s.calls.get(other),
{
    assert(step(engine(f),s,a).closed =~= s.closed);
}
// All private ordinary metadata, other calls, weak receipts and backend
// results can vary. Once both authentic replies are in this call's open
// mailbox, the validation rule and the ability to poll use no G-status bit.
pub proof fn direct_poll_reads_its_own_mailbox(f:CommandSemantics,s:State<Store>,u:State<Store>,id:nat)
    requires s.calls.contains_key(id),u.calls.contains_key(id),s.calls[id]==u.calls[id],
        s.calls[id].method is Read && !s.calls[id].submitted && !delegate(s.calls[id]),
        !s.base.stopped.contains(id),!u.base.stopped.contains(id),
    ensures enabled(engine(f),s,Event::Poll(id))==s.calls[id].answer.is_none(),
        enabled(engine(f),u,Event::Poll(id))==s.calls[id].answer.is_none(),
        poll(engine(f),s,id)==poll(engine(f),u,id),
{}

}
