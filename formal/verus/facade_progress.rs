use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::all_replicas;
use crate::ordered_store::majority;
use crate::stock_availability::Stream;
use crate::stock_facade::*;

verus! {

pub type Run<X,E> = Stream<State<X>,Event<E>>;
pub type StockRun<X,E> = Stream<X,Input<E>>;

pub open spec fn execution<X,E>(p: Engine<X,E>, e: Run<X,E>) -> bool {
    (e.state)(0)==initial(p) && forall|i: nat| {
        let a=#[trigger] (e.event)(i); let s=(e.state)(i);
        enabled(p,s,a) && (e.state)(i+1)==step(p,s,a)
    }
}
pub open spec fn stock_execution<X,E>(p: Engine<X,E>,e: StockRun<X,E>) -> bool {
    (e.state)(0)==p.initial && forall|i: nat| {
        let a=#[trigger] (e.event)(i); let s=(e.state)(i);
        (p.ready)(s,a) && (e.state)(i+1)==(p.step)(s,a)
    }
}
pub open spec fn project<X,E>(e: Run<X,E>) -> StockRun<X,E> {
    Stream { state: |i| (e.state)(i).base, event: |i| input((e.state)(i),(e.event)(i)) }
}
pub open spec fn live_from<X,E>(p: Engine<X,E>, e: StockRun<X,E>, k: nat, id: nat) -> bool {
    forall|i: nat| i>=k ==> (p.client)(#[trigger] (e.state)(i),id) && majority((p.up)((e.state)(i)))
}

// Manuscript A's first clause for ALL submitted commands and reads. Fair
// is the supplied stock service's scheduler on its real projected events.
pub open spec fn stock_operation_progress<X,E>(p: Engine<X,E>, fair: spec_fn(StockRun<X,E>)->bool) -> bool {
    forall|e: StockRun<X,E>, k: nat, id: nat| stock_execution(p,e) && fair(e)
        && (p.submitted)(#[trigger] (e.state)(k),id).is_some() && #[trigger] live_from(p,e,k,id)
        ==> exists|j: nat| j>=k && (p.reply)(#[trigger] (e.state)(j),id).is_some()
}
// Weak fairness of each enabled front-end process / issued packet. It
// refers only to machine actions; an unsuccessful CPU poll counts.
pub open spec fn scheduled<X,E>(p: Engine<X,E>, e: Run<X,E>, a: Event<E>, i: nat) -> bool {
    exists|j: nat| j>=i && (#[trigger] (e.event)(j)==a || !enabled(p,(e.state)(j),a))
}
proof fn scheduled_witness<X,E>(p: Engine<X,E>,e: Run<X,E>,a: Event<E>,i: nat) -> (round: nat)
    requires scheduled(p,e,a,i),
    ensures round>=i && ((e.event)(round)==a || !enabled(p,(e.state)(round),a)),
{
    choose|j: nat| j>=i && (#[trigger] (e.event)(j)==a || !enabled(p,(e.state)(j),a))
}
pub open spec fn front_fair<X,E>(p: Engine<X,E>,e: Run<X,E>) -> bool {
    (forall|i: nat,id: nat| #[trigger] scheduled(p,e,Event::Poll(id),i))
    && forall|i: nat,id: nat,r: Replica,st: Stage| #[trigger] scheduled(p,e,Event::Rpc(id,r,st),i)
}

pub proof fn in_run<X,E>(p: Engine<X,E>, e: Run<X,E>,k: nat)
    requires ports(p), execution(p,e),
    ensures good(p,(e.state)(k)), backend_reachable(p,(e.state)(k).base), reachable(p,(e.state)(k)),
{
    let t=Seq::new(k+1,|i: int|(e.state)(i as nat)); let a=Seq::new(k,|i: int|(e.event)(i as nat));
    assert forall|i: int| 0<=i<a.len() implies enabled(p,t[i],#[trigger] a[i]) && t[i+1]==step(p,t[i],a[i]) by {
        assert(enabled(p,(e.state)(i as nat),(e.event)(i as nat)));
    }
    assert(path(p,t,a)); good_at(p,t,a,k);
}
pub open spec fn stage(c: Call,r: Replica) -> nat {
    match (c.legs)(r) { Leg::Unsent=>0, Leg::Request=>1, Leg::AtServer=>2, Leg::InFlight(_)=>3, Leg::Received(_)=>4 }
}
pub open spec fn expected(n: nat) -> Stage {
    if n==0 {Stage::Offer} else if n==1 {Stage::DeliverRequest} else if n==2 {Stage::EmitReply} else {Stage::DeliverReply}
}

pub proof fn later<X,E>(p: Engine<X,E>,e: Run<X,E>,i: nat,j: nat,id: nat,r: Replica)
    requires ports(p), execution(p,e), i<=j,
    ensures ({
        let s=(e.state)(i); let t=(e.state)(j);
        (p.up)(t.base).subset_of((p.up)(s.base))
        && ((p.reply)(s.base,id).is_some() ==> (p.reply)(t.base,id)==(p.reply)(s.base,id))
        && (s.calls.contains_key(id) ==> {
            let c=s.calls[id]; let d=t.calls[id]; t.calls.contains_key(id) && d.method==c.method
                && stage(c,r)<=stage(d,r) && (c.submitted ==> d.submitted)
                && (c.answer.is_some() ==> d.answer==c.answer)
        })
    }),
    decreases j-i,
{
    if i<j {
        let h=(j-1) as nat; later(p,e,i,h,id,r); in_run(p,e,h);
        let s=(e.state)(h); let evt=(e.event)(h);
        assert(enabled(p,s,evt) && (e.state)(j)==step(p,s,evt));
        let y=(e.state)(j); let prev=(e.state)(i);
        assert((p.ready)(s.base,input(s,evt)));
        assert((p.up)(y.base).subset_of((p.up)(s.base)));
        assert((p.submitted)(y.base,id) == match input(s,evt) {
            Input::Submit(key,m) if key==id => Some(m), _ => (p.submitted)(s.base,id),
        });
        if (p.reply)(s.base,id).is_some() { assert((p.reply)(y.base,id)==(p.reply)(s.base,id)); }
        if s.calls.contains_key(id) {
            assert(y.calls.contains_key(id));
            assert(stage(y.calls[id],r)>=stage(s.calls[id],r));
            assert(s.calls[id].submitted ==> y.calls[id].submitted);
        }
        assert((p.up)(y.base).subset_of((p.up)(prev.base)));
    }
}

pub proof fn permanent_majority<X,E>(p: Engine<X,E>,e: Run<X,E>,k: nat,id: nat) -> (q: Set<Replica>)
    requires ports(p), execution(p,e), live_from(p,project(e),k,id),
    ensures majority(q), forall|i: nat| i>=k ==> q.subset_of((p.up)((#[trigger] (e.state)(i)).base)),
{
    if exists|i: nat,r: Replica| i>=k && !(#[trigger] (p.up)((e.state)(i).base).contains(r)) {
        let (h,r)=choose|i: nat,r: Replica| i>=k && !(#[trigger] (p.up)((e.state)(i).base).contains(r));
        let q=all_replicas().remove(r);
        assert forall|i: nat| i>=k implies q.subset_of((p.up)((#[trigger] (e.state)(i)).base)) by {
            let j=if i>=h {i} else {h}; later(p,e,h,j,id,r); later(p,e,i,j,id,r);
            assert(majority((p.up)((project(e).state)(j))));
            assert forall|s: Replica| q.contains(s) implies (p.up)((e.state)(j).base).contains(s) by {
                match (r,s) { _=>{} }
            }
        }
        q
    } else { all_replicas() }
}
proof fn reach_stage<X,E>(p: Engine<X,E>,e: Run<X,E>,k: nat,id: nat,r: Replica,n: nat) -> (j: nat)
    requires ports(p), execution(p,e), front_fair(p,e), n<=4, (e.state)(k).calls.contains_key(id),
        forall|i: nat| i>=k && (#[trigger] (e.state)(i)).calls.contains_key(id) ==> !majority(rows((e.state)(i).calls[id]).dom()),
        forall|i: nat| i>=k ==> (p.up)((#[trigger] (e.state)(i)).base).contains(r) && (p.client)((e.state)(i).base,id),
    ensures j>=k, (e.state)(j).calls.contains_key(id), stage((e.state)(j).calls[id],r)>=n,
    decreases n,
{
    if n==0 { k } else {
        let h=reach_stage(p,e,k,id,r,(n-1) as nat);
        let a=Event::Rpc(id,r,expected((n-1) as nat));
        assert(scheduled(p,e,a,h));
        let w=scheduled_witness(p,e,a,h);
        later(p,e,h,w,id,r); in_run(p,e,w);
        let s=(e.state)(w);
        if stage(s.calls[id],r)>=n { w } else {
            assert(input(s,a) == Input::<E>::Idle);
            assert((p.ready)(s.base,Input::Idle));
            assert(enabled(p,s,a) && (e.event)(w)==a);
            assert((e.state)(w+1)==step(p,s,a));
            w+1
        }
    }
}
proof fn poll_after<X,E>(p: Engine<X,E>,e: Run<X,E>,k: nat,id: nat) -> (j: nat)
    requires ports(p),execution(p,e),front_fair(p,e),live_from(p,project(e),k,id),(e.state)(k).calls.contains_key(id),
    ensures j>=k, (e.event)(j)==Event::Poll(id) || (e.state)(j).calls[id].answer.is_some(),
{
    let a=Event::Poll(id);
    assert(scheduled(p,e,a,k));
    let w=scheduled_witness(p,e,a,k);
    later(p,e,k,w,id,Replica::R1); in_run(p,e,w); let s=(e.state)(w);
    assert((p.client)((project(e).state)(w),id));
    if delegate(s.calls[id]) { assert((p.submitted)(s.base,id).is_none()); }
    if s.calls[id].answer.is_none() {assert(enabled(p,s,a));} w
}

pub proof fn every_outer_operation_finishes<X,E>(p: Engine<X,E>,fair: spec_fn(StockRun<X,E>)->bool,
    e: Run<X,E>,k: nat,id: nat) -> (answer_at: nat)
    requires ports(p),stock_operation_progress(p,fair),execution(p,e),fair(project(e)),front_fair(p,e),
        (e.state)(k).calls.contains_key(id),live_from(p,project(e),k,id),
    ensures answer_at>=k, (e.state)(answer_at).calls[id].answer.is_some(),
{
    hide(step);
    let q=permanent_majority(p,e,k,id);
    if !(exists|i: nat| i>=k && majority(rows((#[trigger] (e.state)(i)).calls[id]).dom())) {
        let end=|r: Replica| choose|i: nat| i>=k && stage((#[trigger] (e.state)(i)).calls[id],r)==4;
        assert forall|r: Replica| #[trigger] q.contains(r) implies end(r)>=k && stage((e.state)(end(r)).calls[id],r)==4 by {
            assert forall|i: nat| i>=k implies (p.up)((#[trigger] (e.state)(i)).base).contains(r) && (p.client)((e.state)(i).base,id) by {
                assert((p.client)((project(e).state)(i),id)); assert(q.subset_of((p.up)((e.state)(i).base)));
            }
            let i=reach_stage(p,e,k,id,r,4);
            assert(stage((e.state)(i).calls[id],r)==4);
        }
        let time=|r: Replica| if q.contains(r) {end(r)} else {0nat};
        let stop=k+time(Replica::R1)+time(Replica::R2)+time(Replica::R3);
        assert forall|r: Replica| q.contains(r) implies #[trigger] rows((e.state)(stop).calls[id]).contains_key(r) by {
            assert(end(r)<=stop); later(p,e,k,end(r),id,r); later(p,e,end(r),stop,id,r);
        }
        assert(majority(rows((e.state)(stop).calls[id]).dom()));
    }
    let stop=choose|i: nat| i>=k && majority(rows((#[trigger] (e.state)(i)).calls[id]).dom());
    later(p,e,k,stop,id,Replica::R1);
    assert(live_from(p,project(e),stop,id));
    let j=poll_after(p,e,stop,id);
    let s=(e.state)(j); let c=s.calls[id]; let z=project(e);
    if c.answer.is_some() { return j; }
    assert forall|r: Replica| rows((e.state)(stop).calls[id]).contains_key(r) implies #[trigger] rows(c).contains_key(r) by {
        later(p,e,stop,j,id,r);
    }
    assert(majority(rows(c).dom()));
    in_run(p,e,j);
    assert((e.state)(j+1)==step(p,s,Event::Poll(id)));
    if !c.submitted && early(c) { early_stock_answer(c); }
    assert((e.state)(j+1).calls[id]==poll(p,s,id)) by { reveal(step); }
    assert((e.state)(j+1).calls.contains_key(id)) by {reveal(step);}
    if (e.state)(j+1).calls[id].answer.is_some() { j+1 } else {
        let u=(e.state)(j+1); in_run(p,e,j+1);
        assert(u.calls.contains_key(id)) by { reveal(step); }
        assert(u.calls[id].submitted && (p.submitted)(u.base,id).is_some());
        assert forall|i: nat| {
            let a=#[trigger] (z.event)(i); (p.ready)((z.state)(i),a) && (z.state)(i+1)==(p.step)((z.state)(i),a)
        } by { let a=(e.event)(i); assert((e.state)(i+1)==step(p,(e.state)(i),a)); reveal(step); }
        assert(stock_execution(p,z) && live_from(p,z,j+1,id));
        assert((p.submitted)((z.state)(j+1),id).is_some() && fair(z));
        assert(exists|i: nat| i>=j+1 && (p.reply)(#[trigger] (z.state)(i),id).is_some());
        let i=choose|i: nat| i>=j+1 && (p.reply)(#[trigger] (z.state)(i),id).is_some();
        later(p,e,j+1,i,id,Replica::R1);
        let w=poll_after(p,e,i,id);
        later(p,e,j+1,w,id,Replica::R1); later(p,e,i,w,id,Replica::R1);
        if (e.state)(w).calls[id].answer.is_some() { return w; }
        assert((e.state)(w+1)==step(p,(e.state)(w),Event::Poll(id)));
        assert((e.state)(w+1).calls[id].answer.is_some()) by { reveal(step); }
        w+1
    }
}

}
