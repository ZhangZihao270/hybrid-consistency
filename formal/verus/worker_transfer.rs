// Transfer ordinary work, including work that changes application state.
// A is used on a reachable execution of the actual stock engine. The
// controller laws below are a sufficient implementation property, not T.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::{Fork,live_pair};
use crate::facade_linear::CommandSemantics;
use crate::facade_quorum::{Used,base_service,any_backend_majority};
use crate::ordered_round::{self as base,Store,Work,engine};
use crate::ordered_store::majority;
use crate::stock_facade::*;

verus! {

// Everything an ordinary service scheduler tests may go in 'private',
// e.g. an applied position, addressed queue occupancy, or a local timer.
// The queue records IDs. Application data and the values in reply records
// belong to the actual engine, and are read from the particular execution.
pub struct Queue<C> {
    pub private:C, pub up:Set<Replica>, pub stopped:Set<nat>,
    pub registered:Map<nat,Method>, pub published:Set<nat>,
}
pub type Inspect<X,C> = spec_fn(X)->Queue<C>;

pub open spec fn faithful<X,E,C>(p:Engine<X,E>,view:Inspect<X,C>,x:X,id:nat) -> bool {
    let q=view(x);
    (p.up)(x)==q.up && (p.client)(x,id)==!q.stopped.contains(id) &&
        (p.submitted)(x,id)==q.registered.get(id) && (p.reply)(x,id).is_some()==q.published.contains(id)
}
pub open spec fn read_work<E>(a:Input<E>) -> bool {
    a is Work || (a is Submit && a->Submit_1==Method::Read)
}
// One-way simulation on ordinary worker instructions. A source is always
// stock-reachable. An implementation may also enable extra hybrid work.
// 'a' schedules a real job or a stable message slot, not an injected
// payload. The actual engine reads/sends its own data when it steps.
pub open spec fn ordinary_jobs<X,E,C>(p:Engine<X,E>,used:Used<X,E>,view:Inspect<X,C>) -> bool {
    (forall|x:X,id:nat| #[trigger] faithful(p,view,x,id)) &&
    forall|x:X,y:X,a:Input<E>| #[trigger] backend_reachable(p,x) && view(x)==#[trigger] view(y) &&
        #[trigger] (p.ready)(x,a) && read_work(a) ==> {
            (p.ready)(y,a) && view((p.step)(x,a))==view((p.step)(y,a)) &&
                forall|id:nat| #[trigger] used(id,y,a).subset_of(used(id,x,a))
        }
}

pub open spec fn run<X,E>(p:Engine<X,E>,x:X,work:Seq<E>,k:nat) -> X
    decreases k,
{
    if k==0 {x} else {(p.step)(run(p,x,work,(k-1) as nat),Input::Work(work[k-1]))}
}

pub(crate) proof fn reachable_step<X,E>(p:Engine<X,E>,s:X,a:Input<E>)
    requires backend_reachable(p,s),(p.ready)(s,a),
    ensures backend_reachable(p,(p.step)(s,a)),
{
    let (t,es)=choose|t:Seq<X>,es:Seq<Input<E>>| #[trigger] backend_path(p,t,es) && t[0]==p.initial && t.last()==s;
    let us=t.push((p.step)(s,a));let bs=es.push(a);
    assert forall|i:int| 0<=i<bs.len() implies (p.ready)(us[i],#[trigger] bs[i]) && us[i+1]==(p.step)(us[i],bs[i])
        by {if i<es.len() {assert((p.ready)(t[i],es[i]) && t[i+1]==(p.step)(t[i],es[i]));}}
    assert(backend_path(p,us,bs) && us[0]==p.initial && us.last()==(p.step)(s,a));
}
proof fn lift_through<X,E,C>(p:Engine<X,E>,used:Used<X,E>,view:Inspect<X,C>,t:Seq<X>,w:Seq<E>,x:X,k:nat)
    requires ordinary_jobs(p,used,view),k<=w.len(),t.len()==w.len()+1,
        view(t[0])==view(x),backend_reachable(p,t[0]),
        forall|i:int| 0<=i<w.len() ==> {
            let a=Input::Work(#[trigger] w[i]);(p.ready)(t[i],a) && t[i+1]==(p.step)(t[i],a)
        },
    ensures view(run(p,x,w,k))==view(t[k as int]),backend_reachable(p,t[k as int]),
        k<w.len() ==> (p.ready)(run(p,x,w,k),Input::Work(w[k as int])) &&
            forall|id:nat| #[trigger] used(id,run(p,x,w,k),Input::Work(w[k as int])).subset_of(used(id,t[k as int],Input::Work(w[k as int]))),
    decreases k,
{
    if k>0 {
        let h=(k-1) as nat;lift_through(p,used,view,t,w,x,h);
        let a=Input::Work(w[h as int]);assert((p.ready)(t[h as int],a));reachable_step(p,t[h as int],a);
    }
    if k<w.len() {assert((p.ready)(t[k as int],Input::Work(w[k as int])));}
}
// No equal stock/hybrid data, return value, or enabled hybrid completion
// witness in the premises. The available-majority clause of stock A picks
// the real service sequence. It can include repairs and mandatory messages.
pub open spec fn service<X,E>(p:Engine<X,E>,used:Used<X,E>,x:X,id:nat,q:Set<Replica>,w:Seq<E>) -> bool {
    let submit=Input::Submit(id,Method::Read);let s=(p.step)(x,submit);
    (p.ready)(x,submit) && (p.reply)(run(p,s,w,w.len()),id).is_some() &&
        (forall|i:nat| i<=w.len() ==> (p.client)(#[trigger] run(p,s,w,i),id) && q.subset_of((p.up)(run(p,s,w,i)))) &&
        forall|i:int| 0<=i<w.len() ==> {let e=Input::Work(#[trigger] w[i]);let y=run(p,s,w,i as nat);
            (p.ready)(y,e) && used(id,y,e).subset_of(q)}
}
proof fn copy_enabled_service<X,E,C>(p:Engine<X,E>,used:Used<X,E>,view:Inspect<X,C>,stock:X,actual:X,id:nat,q:Set<Replica>,
    t:Seq<X>,w:Seq<E>,ret:int)
    requires ordinary_jobs(p,used,view),backend_reachable(p,stock),view(stock)==view(actual),
        (p.ready)(stock,Input::Submit(id,Method::Read)),base_service(p,used,stock,id,q,t,w,ret),
    ensures service(p,used,actual,id,q,w),
{
    let ask=Input::Submit(id,Method::Read);assert((p.ready)(stock,ask));
    let x=(p.step)(actual,ask);reachable_step(p,stock,ask);assert(view(t[0])==view(x));
    assert forall|i:nat| i<=w.len() implies (p.client)(#[trigger] run(p,x,w,i),id) && q.subset_of((p.up)(run(p,x,w,i))) by {
        lift_through(p,used,view,t,w,x,i);
        assert(faithful(p,view,t[i as int],id) && faithful(p,view,run(p,x,w,i),id));
    }
    assert forall|i:int| 0<=i<w.len() implies {let a=Input::Work(#[trigger] w[i]);let y=run(p,x,w,i as nat);
        (p.ready)(y,a) && used(id,y,a).subset_of(q)} by {
        let a=Input::Work(w[i]);let y=run(p,x,w,i as nat);
        lift_through(p,used,view,t,w,x,i as nat);
        assert(used(id,y,a).subset_of(used(id,t[i],a)));
        assert(used(id,t[i],a).subset_of(q));
        assert forall|r:Replica| #[trigger] used(id,y,a).contains(r) implies q.contains(r) by {};
    }
    lift_through(p,used,view,t,w,x,w.len());
    assert(faithful(p,view,t.last(),id) && faithful(p,view,run(p,x,w,w.len()),id));
}

pub proof fn stock_a_supplies_jobs<X,E,C>(p:Engine<X,E>,used:Used<X,E>,view:Inspect<X,C>,stock:X,actual:X,id:nat,q:Set<Replica>) -> (w:Seq<E>)
    requires ports(p),any_backend_majority(p,used),ordinary_jobs(p,used,view),backend_reachable(p,stock),
        view(stock)==view(actual),(p.submitted)(stock,id).is_none(),(p.client)(stock,id),majority(q),q.subset_of((p.up)(stock)),
    ensures service(p,used,actual,id,q,w),
{
    let (t,w,ret)=choose|t:Seq<X>,w:Seq<E>,v:int| #[trigger] base_service(p,used,stock,id,q,t,w,v);
    copy_enabled_service(p,used,view,stock,actual,id,q,t,w,ret);
    w
}

pub open spec fn queue(s:Store) -> Queue<()> {
    Queue{private:(),up:s.live,stopped:s.stopped,registered:s.calls,published:s.done.dom()}
}
proof fn queue_laws(f:CommandSemantics)
    ensures ordinary_jobs(engine(f),base::used(),|s|queue(s)),
{
    let p=engine(f);let used=base::used();let inspect=|s|queue(s);
    assert forall|x:Store,id:nat| #[trigger] faithful(p,inspect,x,id) by {};
    assert forall|x:Store,y:Store,a:Input<Work>| #[trigger] backend_reachable(p,x) && inspect(x)==#[trigger] inspect(y) &&
        #[trigger] (p.ready)(x,a) && read_work(a) implies {
            (p.ready)(y,a) && inspect((p.step)(x,a))==inspect((p.step)(y,a)) &&
                forall|id:nat| #[trigger] used(id,y,a).subset_of(used(id,x,a))
    } by {
        match a {
            Input::Work(Work::Serve(id,q))=>{
                let s=base::advance(f,x,a);let t=base::advance(f,y,a);
                assert(s.done.dom() =~= t.done.dom());
            },
            _=>{},
        }
    }
}

// The original backend saw C1 stop and R3 fail. Its read bypass did not
// submit a command. Replay those actual lifecycle events from stock genesis.
// The constructed stock image has different data, at the same service queue.
pub open spec fn shadow(f:CommandSemantics) -> Store {
    base::advance(f,base::advance(f,base::start(),Input::Work(Work::StopClient(1))),Input::Work(Work::Crash(Replica::R3)))
}
pub proof fn stock_queue_at_originals(f:CommandSemantics,b:Fork)
    ensures backend_reachable(engine(f),shadow(f)),queue(shadow(f))==queue(crate::facade_hybrid::prefix(b,17).base),
        (shadow(f).disk)(Replica::R1).value==1 && (shadow(f).disk)(Replica::R2).value==1,
        (crate::facade_hybrid::prefix(b,17).base.disk)(Replica::R1).value==2 &&
            (crate::facade_hybrid::prefix(b,17).base.disk)(Replica::R2).value==5,
{
    let x=base::start();let p=engine(f);let a=Input::Work(Work::StopClient(1));let y=base::advance(f,x,a);
    assert(backend_path(p,seq![x],Seq::empty()));assert(backend_reachable(p,x));
    reachable_step(p,x,a);reachable_step(p,y,Input::Work(Work::Crash(Replica::R3)));
    assert(shadow(f).live =~= crate::facade_hybrid::prefix(b,17).base.live);
}
// The same stock witness works on BOTH real backends. The client still
// needs an enabled local route to submit its read in each enclosing front.
pub proof fn common_worker_at_originals(f:CommandSemantics,n:crate::checkpoint::Notice) -> (w:Seq<Work>)
    ensures service(engine(f),base::used(),crate::facade_hybrid::prefix(crate::checkpoint::alpha(n),17).base,2,live_pair(),w),
        service(engine(f),base::used(),crate::facade_hybrid::prefix(crate::checkpoint::beta(n),17).base,2,live_pair(),w),
{
    let a=crate::checkpoint::alpha(n);let b=crate::checkpoint::beta(n);let p=engine(f);let x=shadow(f);let q=live_pair();
    let left=crate::facade_hybrid::prefix(a,17).base;let right=crate::facade_hybrid::prefix(b,17).base;
    queue_laws(f);stock_queue_at_originals(f,a);stock_queue_at_originals(f,b);base::api_and_majorities(f);
    assert(majority(q) && q.subset_of((p.up)(x)) && (p.submitted)(x,2).is_none() && (p.client)(x,2));
    assert(exists|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] base_service(p,base::used(),x,2,q,t,w,v));
    let (t,w,v)=choose|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] base_service(p,base::used(),x,2,q,t,w,v);
    copy_enabled_service(p,base::used(),|s|queue(s),x,left,2,q,t,w,v);
    copy_enabled_service(p,base::used(),|s|queue(s),x,right,2,q,t,w,v);
    w
}
}
