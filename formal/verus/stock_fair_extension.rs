use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::all_replicas;
use crate::ordered_store::majority;
use crate::stock_facade::*;
use crate::facade_progress::{Run,execution,front_fair,scheduled,project,live_from};
use crate::facade_linear::CommandSemantics;
use crate::ordered_round::{self as base,Store,Work,engine};

// A real fair extension of every finite stock prefix in the concrete
// ordered-quorum instance. No crash, new invocation or repair is needed
// in this extension. The scheduler schedules only enabled actions.
verus! {

pub open spec fn position(n:nat) -> (nat,nat)
    decreases n,
{
    if n==0 {(0,0)} else {let (lap,slot)=position((n-1) as nat);if lap==slot {(lap+1,0)} else {(lap,slot+1)}}
}
pub open spec fn beginning(lap:nat) -> nat
    decreases lap,
{
    if lap==0 {0} else {beginning((lap-1) as nat)+lap}
}
pub(crate) proof fn visits(lap:nat,slot:nat)
    requires slot<=lap,
    ensures position(beginning(lap)+slot)==(lap,slot),beginning(lap)>=lap,
    decreases lap,slot,
{
    if slot>0 {visits(lap,(slot-1) as nat);} else if lap>0 {visits((lap-1) as nat,(lap-1) as nat);}
}

pub open spec fn replica(x:nat) -> Replica { if x==0 {Replica::R1} else if x==1 {Replica::R2} else {Replica::R3} }
pub open spec fn index(r:Replica) -> nat {match r {Replica::R1=>0,Replica::R2=>1,Replica::R3=>2}}
pub open spec fn kind(x:nat) -> Stage {
    if x==0 {Stage::Offer} else if x==1 {Stage::DeliverRequest} else if x==2 {Stage::EmitReply} else {Stage::DeliverReply}
}
pub open spec fn number(s:Stage) -> nat {match s {Stage::Offer=>0,Stage::DeliverRequest=>1,Stage::EmitReply=>2,Stage::DeliverReply=>3}}
pub open spec fn quorum(x:nat) -> Set<Replica> {
    if x<3 {all_replicas().remove(replica(x))} else {all_replicas()}
}
pub open spec fn candidate(n:nat) -> Event<Work> {
    let id=n/32;let slot=n%32;
    if slot==0 {Event::Poll(id)}
    else if slot<=12 {let k=(slot-1) as nat;Event::Rpc(id,replica(k/4),kind(k%4))}
    else if slot<=16 {Event::Work(Work::Serve(id,quorum((slot-13) as nat)))}
    else if slot<=19 {Event::Work(Work::Tick(replica((slot-17) as nat)))} else {Event::Idle}
}
pub open spec fn select(f:CommandSemantics,s:State<Store>,n:nat) -> Event<Work> {
    let a=candidate(position(n).1); if enabled(engine(f),s,a) {a} else {Event::Idle}
}
pub open spec fn future(f:CommandSemantics,x:State<Store>,k:nat) -> State<Store>
    decreases k,
{
    if k==0 {x} else {let j=(k-1) as nat;let s=future(f,x,j);step(engine(f),s,select(f,s,j))}
}
pub open spec fn extend(f:CommandSemantics,t:Seq<State<Store>>,a:Seq<Event<Work>>) -> Run<Store,Work> {
    crate::stock_availability::Stream {state: |i:nat|if i<=a.len(){t[i as int]}else{future(f,t.last(),(i-a.len()) as nat)},
        event:|i:nat|if i<a.len(){a[i as int]}else{let j=(i-a.len()) as nat;select(f,future(f,t.last(),j),j)} }
}
proof fn stable_workers(f:CommandSemantics,x:State<Store>,k:nat)
    ensures future(f,x,k).base.live==x.base.live,future(f,x,k).base.stopped==x.base.stopped,
    decreases k,
{
    if k>0 {let h=(k-1) as nat;stable_workers(f,x,h);let s=future(f,x,h);let ev=select(f,s,h);
        assert(!(input(s,ev) is Work) || (!(input(s,ev)->Work_0 is Crash) && !(input(s,ev)->Work_0 is StopClient)));}
}
proof fn picked(f:CommandSemantics,t:Seq<State<Store>>,a:Seq<Event<Work>>,from:nat,code:nat) -> (j:nat)
    requires t.len()==a.len()+1,
    ensures j>=a.len() && j>=from && ({
        let e=extend(f,t,a); let ev=candidate(code); (e.event)(j)==ev || !enabled(engine(f),(e.state)(j),ev)
    }),
{
    let lap=code+from+1;visits(lap,code);a.len()+beginning(lap)+code
}
pub proof fn every_stock_prefix_has_a_fair_extension(f:CommandSemantics,t:Seq<State<Store>>,a:Seq<Event<Work>>)
    requires t[0]==initial(engine(f)),path(engine(f),t,a),
    ensures ({
        let e=extend(f,t,a);execution(engine(f),e) && front_fair(engine(f),e) && base::fair(project(e))
            && (forall|i:nat| i<=a.len() ==> #[trigger] (e.state)(i)==t[i as int])
            && (forall|i:nat| i<a.len() ==> #[trigger] (e.event)(i)==a[i as int])
            && forall|i:nat| i>=a.len() ==> (#[trigger] (e.state)(i)).base.live==t.last().base.live
                && (e.state)(i).base.stopped==t.last().base.stopped
    }),
{
    let p=engine(f);let e=extend(f,t,a);let z=project(e);
    assert forall|i:nat| {
        let ev=#[trigger] (e.event)(i);let s=(e.state)(i);enabled(p,s,ev) && (e.state)(i+1)==step(p,s,ev)
    } by {if i<a.len(){assert(enabled(p,t[i as int],a[i as int]));}else{let k=(i-a.len()) as nat;assert(future(f,t.last(),k+1)==step(p,future(f,t.last(),k),select(f,future(f,t.last(),k),k)));}}
    assert forall|i:nat| i>=a.len() implies (#[trigger] (e.state)(i)).base.live==t.last().base.live
        && (e.state)(i).base.stopped==t.last().base.stopped by {stable_workers(f,t.last(),(i-a.len()) as nat);}
    assert forall|i:nat,id:nat| #[trigger] scheduled(p,e,Event::Poll(id),i) by {
        let j=picked(f,t,a,i,32*id);let ev=Event::Poll(id);assert((e.event)(j)==ev || !enabled(p,(e.state)(j),ev));
    }
    assert forall|i:nat,id:nat,r:Replica,s:Stage| #[trigger] scheduled(p,e,Event::Rpc(id,r,s),i) by {
        let code=32*id+1+4*index(r)+number(s);assert(candidate(code)==Event::Rpc(id,r,s));
        let j=picked(f,t,a,i,code);let ev=Event::Rpc(id,r,s);assert((e.event)(j)==ev || !enabled(p,(e.state)(j),ev));
    }
    assert forall|i:nat,id:nat,q:Set<Replica>| #[trigger] base::scheduled(z,i,Work::Serve(id,q)) by {
        let w=Work::Serve(id,q);
        if majority(q) {
            let k=if !q.contains(Replica::R1){0nat}else if !q.contains(Replica::R2){1}else if !q.contains(Replica::R3){2}else{3};
            assert(q =~= quorum(k)) by {assert forall|r:Replica| #[trigger] q.contains(r)==quorum(k).contains(r) by {match r {_=>{}}}}
            let code=32*id+13+k;assert(candidate(code)==Event::Work(w));let j=picked(f,t,a,i,code);
            assert(base::served_or_disabled(z,j,w));
        } else {assert(base::served_or_disabled(z,i,w));}
    }
    assert forall|i:nat,r:Replica| #[trigger] base::scheduled(z,i,Work::Tick(r)) by {
        let code=17+index(r);let j=picked(f,t,a,i,code);assert(base::served_or_disabled(z,j,Work::Tick(r)));
    }
}

pub proof fn fair_stock_completion_from_every_cut(f:CommandSemantics,t:Seq<State<Store>>,a:Seq<Event<Work>>,id:nat)
    requires t[0]==initial(engine(f)),path(engine(f),t,a),majority(t.last().base.live),
        t.last().calls.contains_key(id),!t.last().base.stopped.contains(id),
    ensures ({
        let e=extend(f,t,a);execution(engine(f),e) && front_fair(engine(f),e) && base::fair(project(e))
            && exists|i:nat| i>=a.len() && crate::facade_history::answer((#[trigger] (e.state)(i)),id).is_some()
    }),
{
    every_stock_prefix_has_a_fair_extension(f,t,a);base::concrete_full_a(f);let e=extend(f,t,a);let p=engine(f);
    assert(live_from(p,project(e),a.len(),id));assert((e.state)(a.len()).calls.contains_key(id));
}

}
