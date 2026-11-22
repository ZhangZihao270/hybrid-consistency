use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::all_replicas;
use crate::ordered_store::{Stamp,majority};
use crate::quorum_rpc::{latest_site,latest_is_a_sample};
use crate::stock_facade::*;
use crate::facade_progress::{StockRun,stock_execution,stock_operation_progress,live_from};
use crate::facade_quorum::{Used,base_service,any_backend_majority};
use crate::facade_history::stock_sample_valid;
use crate::facade_linear::{CommandSemantics,Grid,Entry,ordered,certifies,slot_matches,accounted,effect,base_linearizable};

verus! {

// A nonempty instance of the backend contract at the atomic ordered-quorum
// interface. Serving a command on Q is one atomic service round here.
// Implementing that primitive by asynchronous consensus is external to this
// instance; the wrapper proof above accepts arbitrary real backend steps.
pub enum Work { Serve(nat,Set<Replica>), Crash(Replica), Tick(Replica), StopClient(nat) }
pub struct Store {
    pub calls: Map<nat,Method>, pub done: Map<nat,int>, pub stopped: Set<nat>, pub live: Set<Replica>,
    pub disk: spec_fn(Replica)->Stamp,
    pub tip: Stamp, // ghost proof of the newest published ordinary state
}
pub open spec fn start() -> Store {
    let root=Stamp{version:0,value:1};
    Store {calls:Map::empty(),done:Map::empty(),stopped:Set::empty(),live:all_replicas(),disk:|_r|root,tip:root}
}
pub open spec fn current(s: Store,q: Set<Replica>) -> Replica { latest_site(Map::new(q,s.disk)) }
pub open spec fn ready(s: Store,a: Input<Work>) -> bool {
    match a {
        Input::Idle=>true, Input::Submit(id,_)=>!s.calls.contains_key(id),
        Input::Work(Work::Tick(r))=>s.live.contains(r),
        Input::Work(Work::StopClient(id))=>!s.stopped.contains(id),
        Input::Work(Work::Crash(r))=>s.live.contains(r) && majority(s.live.remove(r)),
        Input::Work(Work::Serve(id,q))=>s.calls.contains_key(id) && !s.done.contains_key(id) && majority(q) && q.subset_of(s.live),
    }
}
pub open spec fn advance(f: CommandSemantics,s: Store,a: Input<Work>) -> Store {
    match a {
        Input::Submit(id,m)=>Store {calls:s.calls.insert(id,m),..s},
        Input::Work(Work::StopClient(id))=>Store{stopped:s.stopped.insert(id),..s},
        Input::Work(Work::Crash(r))=>Store {live:s.live.remove(r),..s},
        Input::Work(Work::Serve(id,q))=>{
            let d=(s.disk)(current(s,q));
            match s.calls[id] {
                Method::Read=>Store {done:s.done.insert(id,d.value),..s},
                Method::Command(code)=>{
                    let (new,ret)=f(code,d.value); let entry=Stamp{version:d.version+1,value:new};
                    Store {disk:|r|if q.contains(r){entry}else{(s.disk)(r)},tip:entry,done:s.done.insert(id,ret),..s}
                },
            }
        },
        _=>s,
    }
}
pub open spec fn engine(f: CommandSemantics) -> Engine<Store,Work> {
    Engine {initial:start(),ready:|s,a|ready(s,a),step:|s,a|advance(f,s,a),up:|s: Store|s.live,client:|s: Store,id|!s.stopped.contains(id),
        cell:|s: Store,r|(s.disk)(r).value,submitted:|s: Store,id|s.calls.get(id),reply:|s: Store,id|s.done.get(id)}
}
pub open spec fn used() -> Used<Store,Work> {
    |id,_s,a| match a { Input::Work(Work::Serve(other,q)) if other==id=>q, _=>Set::empty() }
}
pub open spec fn healthy(s: Store) -> bool {
    majority(s.live) && s.done.dom().subset_of(s.calls.dom())
        && majority(all_replicas().filter(|r| (s.disk)(r)==s.tip))
        && forall|r: Replica| (#[trigger] (s.disk)(r)).version<=s.tip.version
            && ((s.disk)(r).version==s.tip.version ==> (s.disk)(r)==s.tip)
}
proof fn sees_tip(s: Store,q: Set<Replica>)
    requires healthy(s),majority(q),
    ensures q.contains(current(s,q)),(s.disk)(current(s,q))==s.tip,
{
    let m=Map::new(q,s.disk);latest_is_a_sample(m);
    let holders=all_replicas().filter(|r| (s.disk)(r)==s.tip);
    let r=if holders.contains(Replica::R1) && q.contains(Replica::R1) {Replica::R1}
        else if holders.contains(Replica::R2) && q.contains(Replica::R2) {Replica::R2} else {Replica::R3};
    assert(holders.contains(r) && m.contains_key(r));assert(m[r].version<=m[latest_site(m)].version);
}
proof fn one_round(f: CommandSemantics,s: Store,a: Input<Work>)
    requires healthy(s),ready(s,a),
    ensures healthy(advance(f,s,a)),advance(f,s,a).live.subset_of(s.live),
{
    let t=advance(f,s,a);
    if let Input::Work(Work::Serve(id,q))=a {
        sees_tip(s,q);
        if s.calls[id] is Command {
            assert forall|r: Replica| q.contains(r) implies #[trigger] (t.disk)(r)==t.tip by {};
        }
    }
}
pub proof fn invariant(f: CommandSemantics,t: Seq<Store>,a: Seq<Input<Work>>,k: nat)
    requires backend_path(engine(f),t,a),t[0]==start(),k<=a.len(),
    ensures healthy(t[k as int]),
    decreases k,
{
    if k>0 {let h=(k-1) as nat;invariant(f,t,a,h);one_round(f,t[h as int],a[h as int]);}
    else { assert(all_replicas().filter(|r: Replica|(start().disk)(r)==start().tip) =~= all_replicas()); }
}
proof fn reachable_ok(f: CommandSemantics,s: Store)
    requires backend_reachable(engine(f),s),
    ensures healthy(s),
{
    let (t,a)=choose|t: Seq<Store>,a: Seq<Input<Work>>| #[trigger] backend_path(engine(f),t,a) && t[0]==start() && t.last()==s;
    invariant(f,t,a,a.len());
}

pub proof fn api_and_majorities(f: CommandSemantics)
    ensures ports(engine(f)),any_backend_majority(engine(f),used()),
{
    let p=engine(f);
    assert forall|x: Store,id: nat,q: Set<Replica>| #[trigger] backend_reachable(p,x) && (#[trigger] (p.submitted)(x,id)).is_none()
        && (p.client)(x,id) && #[trigger] majority(q) && q.subset_of((p.up)(x))
        implies exists|t: Seq<Store>,w: Seq<Work>,v: int| #[trigger] base_service(p,used(),x,id,q,t,w,v) by {
        reachable_ok(f,x); sees_tip(x,q); let y=advance(f,x,Input::Submit(id,Method::Read));
        let w=Work::Serve(id,q); let z=advance(f,y,Input::Work(w)); let t=seq![y,z]; let a=seq![w];
        assert(current(y,q)==current(x,q)); let v=x.tip.value; let r=current(x,q);
        assert((p.cell)(t[0],r)==v && q.contains(r));assert(base_service(p,used(),x,id,q,t,a,v));
    }
    assert forall|x: Store,a: Input<Work>| backend_reachable(p,x) && #[trigger] (p.ready)(x,a) implies {
        let y=(p.step)(x,a);
        (p.up)(y).subset_of((p.up)(x))
        && (a is Submit ==> (p.up)(y)==(p.up)(x) && forall|id: nat| #[trigger] (p.client)(y,id)==(p.client)(x,id))
        && forall|id: nat| #[trigger] (p.submitted)(y,id)==match a { Input::Submit(i,m) if i==id=>Some(m), _=>(p.submitted)(x,id) }
            && ((p.reply)(x,id).is_some() ==> (p.reply)(y,id)==(p.reply)(x,id))
    } by { reachable_ok(f,x); one_round(f,x,a); }
}

pub open spec fn served_or_disabled(e: StockRun<Store,Work>,j:nat,w:Work) -> bool {
    (e.event)(j)==Input::Work(w) || !ready((e.state)(j),Input::Work(w))
}
pub open spec fn scheduled(e: StockRun<Store,Work>,i: nat,w: Work) -> bool {
    exists|j: nat| j>=i && #[trigger] served_or_disabled(e,j,w)
}
pub open spec fn fair(e: StockRun<Store,Work>) -> bool {
    (forall|i: nat,id: nat,q: Set<Replica>| #[trigger] scheduled(e,i,Work::Serve(id,q)))
        && forall|i: nat,r: Replica| #[trigger] scheduled(e,i,Work::Tick(r))
}
proof fn durable(f: CommandSemantics,e: StockRun<Store,Work>,i: nat,j: nat,id: nat)
    requires stock_execution(engine(f),e),i<=j,
    ensures (e.state)(j).live.subset_of((e.state)(i).live),
        (e.state)(i).calls.contains_key(id) ==> (e.state)(j).calls.contains_key(id) && (e.state)(j).calls[id]==(e.state)(i).calls[id],
    decreases j-i,
{
    if i<j {let h=(j-1) as nat;durable(f,e,i,h,id);let a=(e.event)(h);assert((e.state)(j)==advance(f,(e.state)(h),a));}
}
pub proof fn every_commit_served(f: CommandSemantics)
    ensures stock_operation_progress(engine(f),|e|fair(e)),
{
    let p=engine(f);
    assert forall|e: StockRun<Store,Work>,k: nat,id: nat| stock_execution(p,e) && fair(e) &&
        (p.submitted)(#[trigger] (e.state)(k),id).is_some() && #[trigger] live_from(p,e,k,id)
        implies exists|j: nat| j>=k && (p.reply)(#[trigger] (e.state)(j),id).is_some() by {
        let (h,absent)=if exists|i:nat,r:Replica|i>=k && !#[trigger] (e.state)(i).live.contains(r) {
            choose|i:nat,r:Replica|i>=k && !#[trigger] (e.state)(i).live.contains(r)
        } else { (k,Replica::R3) };
        let q=(e.state)(h).live; assert(majority(q));
        let w=Work::Serve(id,q); assert(scheduled(e,h,w));
        assert(exists|j:nat|j>=h && #[trigger] served_or_disabled(e,j,w));
        let j=choose|j:nat|j>=h && #[trigger] served_or_disabled(e,j,w);
        durable(f,e,h,j,id);durable(f,e,k,j,id);let s=(e.state)(j);assert(majority((p.up)(s)));
        assert(s.live =~= q) by {
            assert forall|r: Replica| #[trigger] q.contains(r) implies s.live.contains(r) by { match (r,absent) { _=>{} } }
        }
        if !s.done.contains_key(id) {
            assert(ready(s,Input::Work(w)) && (e.event)(j)==Input::Work(w));
            assert((e.state)(j+1)==advance(f,s,Input::Work(w)) && (p.reply)((e.state)(j+1),id).is_some());
        }
    }
}

pub proof fn dispatcher_result(f: CommandSemantics,t: Seq<Store>,a: Seq<Input<Work>>,k: nat,id: nat) -> (j: nat)
    requires backend_path(engine(f),t,a),t[0]==start(),k<=a.len(),t[k as int].done.contains_key(id),
    ensures j<k,a[j as int] is Work && a[j as int]->Work_0 is Serve && a[j as int]->Work_0->Serve_0==id,
        !t[j as int].done.contains_key(id),t[j as int+1].done[id]==t[k as int].done[id],
    decreases k,
{
    assert(k>0);let h=(k-1) as nat;let s=t[h as int];let ev=a[h as int]; assert(ready(s,ev) && t[k as int]==advance(f,s,ev));
    if s.done.contains_key(id) {dispatcher_result(f,t,a,h,id)} else {h}
}
pub proof fn request_source(f: CommandSemantics,t: Seq<Store>,a: Seq<Input<Work>>,k: nat,id: nat) -> (j: nat)
    requires backend_path(engine(f),t,a),t[0]==start(),k<=a.len(),t[k as int].calls.contains_key(id),
    ensures j<k,a[j as int]==Input::Submit(id,t[k as int].calls[id]),
    decreases k,
{
    assert(k>0);let h=(k-1) as nat;assert(ready(t[h as int],a[h as int]) && t[k as int]==advance(f,t[h as int],a[h as int]));
    if t[h as int].calls.contains_key(id) {request_source(f,t,a,h,id)} else {h}
}
proof fn map_extension(f: CommandSemantics,t: Seq<Store>,a: Seq<Input<Work>>,i: nat,k: nat,id: nat)
    requires backend_path(engine(f),t,a),i<=k<=a.len(),
    ensures t[i as int].calls.contains_key(id) ==> t[k as int].calls.get(id)==Some(t[i as int].calls[id]),
        t[i as int].done.contains_key(id) ==> t[k as int].done.get(id)==Some(t[i as int].done[id]),
    decreases k-i,
{
    if i<k {let h=(k-1) as nat;map_extension(f,t,a,i,h,id);assert(ready(t[h as int],a[h as int]) && t[k as int]==advance(f,t[h as int],a[h as int]));}
}
pub proof fn every_read_samples(f: CommandSemantics)
    ensures stock_sample_valid(engine(f),used()),
{
    let p=engine(f);let role=used();
    assert forall|t: Seq<Store>,a: Seq<Input<Work>>,id:nat,q:Set<Replica>,i:nat,k:nat|
        #[trigger] backend_path(p,t,a) && t[0]==p.initial && i<k<=a.len() && #[trigger] a[i as int]==Input::Submit(id,Method::Read)
        && #[trigger] majority(q) && (#[trigger] (p.reply)(t[k as int],id)).is_some()
        && (forall|j:int|i<=j<k && a[j] is Work ==> #[trigger] role(id,t[j],a[j]).subset_of(q))
        implies exists|j:int,r:Replica|i<=j<=k && q.contains(r) && #[trigger] (p.cell)(t[j],r)==(p.reply)(t[k as int],id).unwrap() by {
        let d=dispatcher_result(f,t,a,k,id); let s=t[d as int]; let ev=a[d as int]; let sites=ev->Work_0->Serve_1;
        assert(ready(s,ev) && t[d as int+1]==advance(f,s,ev));
        if d<=i {map_extension(f,t,a,d,i,id);assert(ready(t[i as int],a[i as int]));}
        assert(t[i as int+1]==advance(f,t[i as int],a[i as int]));map_extension(f,t,a,i+1,d,id);
        invariant(f,t,a,d);sees_tip(s,sites);let r=current(s,sites);
        assert(role(id,s,ev).subset_of(q));assert(q.contains(r) && (p.cell)(s,r)==t[k as int].done[id]);
    }
}
pub open spec fn serves(a: Input<Work>,id: nat) -> bool {
    a is Work && a->Work_0 is Serve && a->Work_0->Serve_0==id
}
pub open spec fn grid(t: Seq<Store>,a: Seq<Input<Work>>) -> Grid {
    Grid {width:|_i|1, value:|i:nat,j:nat|if j==0 {t[i as int].tip.value} else {t[i as int+1].tip.value},
        op:|i:nat,_j:nat| match a[i as int] {
            Input::Work(Work::Serve(id,_))=>Some(Entry{id,method:t[i as int].calls[id],result:t[i as int+1].done[id]}), _=>None,
        },
        location:|id| (choose|i:nat| i<a.len() && #[trigger] serves(a[i as int],id),0) }
}
proof fn unique_service(f: CommandSemantics,t: Seq<Store>,a: Seq<Input<Work>>,d:nat,id:nat)
    requires backend_path(engine(f),t,a),d<a.len(),serves(a[d as int],id),
    ensures (grid(t,a).location)(id)==(d,0),
{
    let i=choose|i:nat| i<a.len() && #[trigger] serves(a[i as int],id);
    if i!=d {let l=if i<d {i} else {d};let h=if i<d {d} else {i};
        assert(t[l as int+1]==advance(f,t[l as int],a[l as int]));map_extension(f,t,a,l+1,h,id);assert(ready(t[h as int],a[h as int]));}
}
pub proof fn strong_safety(f: CommandSemantics,t: Seq<Store>,a: Seq<Input<Work>>)
    requires backend_path(engine(f),t,a),t[0]==start(),
    ensures ordered(grid(t,a),f,a.len()),certifies(grid(t,a),a.len(),|i:nat,id:nat,m:Method|a[i as int]==Input::Submit(id,m),
        |i:nat,id:nat|(engine(f).reply)(t[i as int],id)),
{
    let g=grid(t,a);let begin=|i:nat,id:nat,m:Method| a[i as int]==Input::Submit(id,m);
    assert forall|i:nat,j:nat| i<a.len() && j<(g.width)(i) implies effect(f,(g.value)(i,j),#[trigger] (g.op)(i,j),(g.value)(i,j+1)) by {
        let s=t[i as int];let ev=a[i as int];assert(ready(s,ev) && t[i as int+1]==advance(f,s,ev));
        if let Input::Work(Work::Serve(id,q))=ev {invariant(f,t,a,i);sees_tip(s,q);}
    }
    assert forall|i:nat,j:nat| i<a.len() && j<(g.width)(i) implies #[trigger] slot_matches(g,i,j,begin) by {
        if let Input::Work(Work::Serve(id,q))=a[i as int] {
            assert(ready(t[i as int],a[i as int]));unique_service(f,t,a,i,id);let h=request_source(f,t,a,i,id);
            let op=(g.op)(i,j).unwrap();
            assert(op.id==id && op.method==t[i as int].calls[id] && j==0);
            assert(begin(h,op.id,op.method));
            assert(exists|l:nat| l<=i && #[trigger] begin(l,op.id,op.method));
        }
    }
    assert forall|k:nat,id:nat| k<=a.len() && (#[trigger] (engine(f).reply)(t[k as int],id)).is_some()
        implies accounted(g,k,id,t[k as int].done[id]) by {
        let d=dispatcher_result(f,t,a,k,id);unique_service(f,t,a,d,id);
    }
}

pub proof fn concrete_full_a(f: CommandSemantics)
    ensures ports(engine(f)),crate::facade_contract::stock_a(engine(f),|e|fair(e),used()),base_linearizable(engine(f),f),
        crate::facade_contract::all_calls_served(engine(f),|e|fair(e)),crate::facade_contract::any_read_quorum(engine(f),used()),
        crate::facade_contract::read_values_valid(engine(f),used()),crate::facade_contract::outer_linearizable(engine(f),f),
{
    let p=engine(f);api_and_majorities(f);every_commit_served(f);every_read_samples(f);
    assert forall|t: Seq<Store>,a: Seq<Input<Work>>| #[trigger] backend_path(p,t,a) && t[0]==p.initial
        implies exists|g: Grid| #[trigger] ordered(g,f,a.len()) && certifies(g,a.len(),
            |i:nat,id:nat,m:Method|a[i as int]==Input::Submit(id,m),|i:nat,id:nat|(p.reply)(t[i as int],id)) by {
        strong_safety(f,t,a);
    }
    crate::facade_contract::construction_preserves_full_a_and_safety(p,f,|e|fair(e),used());
}

// A finite witness through the public invocation and physical RPC interface.
// Each primitive below is an enabled successor of a reachable state.
proof fn take(f: CommandSemantics,s: State<Store>,a: Event<Work>) -> (u: State<Store>)
    requires reachable(engine(f),s),enabled(engine(f),s,a),
    ensures u==step(engine(f),s,a),reachable(engine(f),u),
{
    let p=engine(f);let u=step(p,s,a);
    crate::facade_quorum::extend_reach(p,s,seq![s,u],seq![a]);u
}
proof fn command_ack(f:CommandSemantics,s:State<Store>,r:Replica) -> (u:State<Store>)
    requires reachable(engine(f),s),s.calls.contains_key(0),s.calls[0].method is Command,
        !s.base.stopped.contains(0),s.base.live.contains(r),(s.calls[0].legs)(r) is Unsent,
        !majority(rows(s.calls[0]).dom()),
    ensures reachable(engine(f),u),u.base==s.base,u.closed==s.closed.insert(r),u.calls.contains_key(0),
        u.calls[0].method==s.calls[0].method,u.calls[0].answer==s.calls[0].answer,u.calls[0].submitted==s.calls[0].submitted,
        u.calls.dom()==s.calls.dom(),(u.calls[0].legs)(r) is Received,
        forall|site:Replica| site!=r ==> (#[trigger] (u.calls[0].legs)(site))==(s.calls[0].legs)(site),
{
    let a=take(f,s,Event::Rpc(0,r,Stage::Offer));let b=take(f,a,Event::Rpc(0,r,Stage::DeliverRequest));
    let c=take(f,b,Event::Rpc(0,r,Stage::EmitReply));let d=take(f,c,Event::Rpc(0,r,Stage::DeliverReply));
    assert(d.closed =~= s.closed.insert(r));d
}
pub proof fn nonuniform_read_after_increment() -> (witness: (State<Store>,State<Store>))
    ensures ({
        let (cut,end)=witness;let p=engine(|_code:nat,x:int|(x+1,x));
        reachable(p,cut) && reachable(p,end) && cut.calls[0].answer==Some(1) && cut.calls[1]==fresh(Method::Read)
            && stamp(p,cut,Replica::R1)==(Stamp{version:1,value:2})
            && stamp(p,cut,Replica::R2)==(Stamp{version:0,value:1})
            && rows(end.calls[1]).dom()==crate::checkpoint::live_pair()
            && rows(end.calls[1])[Replica::R1]==stamp(p,cut,Replica::R1)
            && rows(end.calls[1])[Replica::R2]==stamp(p,cut,Replica::R2)
            && end.calls[1].answer==Some(2)
    }),
{
    let f=|_code:nat,x:int|(x+1,x);let p=engine(f);let s=initial(p);
    let empty=Seq::<Event<Work>>::empty();assert(path(p,seq![s],empty));assert(reachable(p,s));
    let a=take(f,s,Event::Invoke(0,Method::Command(0)));let b=command_ack(f,a,Replica::R1);
    assert(rows(b.calls[0]).dom() =~= set![Replica::R1]);let c=command_ack(f,b,Replica::R3);
    assert(rows(c.calls[0]).dom() =~= set![Replica::R1,Replica::R3]);
    let d=take(f,c,Event::Poll(0));let writers=set![Replica::R1,Replica::R3];
    let e=take(f,d,Event::Work(Work::Serve(0,writers)));let g=take(f,e,Event::Poll(0));
    let x=take(f,g,Event::Invoke(1,Method::Read));let q=crate::checkpoint::live_pair();
    api_and_majorities(f);crate::facade_quorum::physical_survey(p,x,1,q);
    let offers=crate::facade_quorum::survey(1,q); let t=crate::facade_quorum::states(p,x,offers);
    crate::facade_quorum::extend_reach(p,x,t,offers);let h=t.last();
    assert(rows(h.calls[1]).contains_key(Replica::R1) && rows(h.calls[1])[Replica::R1].version==1);
    let i=take(f,h,Event::Poll(1));let j=take(f,i,Event::Work(Work::Serve(1,q)));
    let k=take(f,j,Event::Poll(1));
    assert(current(i.base,q)==Replica::R1);(x,k)
}

}
