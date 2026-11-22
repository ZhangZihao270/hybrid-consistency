use vstd::prelude::*;
use crate::Replica;
use crate::ordered_store::{Stamp,majority};
use crate::stock_facade::*;
use crate::facade_quorum::Used;

verus! {

pub open spec fn answer<X>(s: State<X>,id: nat) -> Option<int> {
    if s.calls.contains_key(id) {s.calls[id].answer} else {None}
}
pub open spec fn base_states<X>(t: Seq<State<X>>) -> Seq<X> {
    Seq::new(t.len(),|i: int| t[i].base)
}
pub open spec fn base_events<X,E>(t: Seq<State<X>>,a: Seq<Event<E>>) -> Seq<Input<E>> {
    Seq::new(a.len(),|i: int| input(t[i],a[i]))
}
pub proof fn projection<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>)
    requires path(p,t,a),
    ensures backend_path(p,base_states(t),base_events(t,a)),
{
    let xs=base_states(t); let es=base_events(t,a);
    assert forall|i: int| 0<=i<es.len() implies (p.ready)(xs[i],#[trigger] es[i]) && xs[i+1]==(p.step)(xs[i],es[i]) by {
        assert(enabled(p,t[i],a[i]) && t[i+1]==step(p,t[i],a[i]));
    }
}

pub proof fn persists<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,i: nat,k: nat,id: nat)
    requires path(p,t,a),i<=k<=a.len(),
    ensures ({
        let s=t[i as int]; let u=t[k as int];
        s.closed.subset_of(u.closed) && (s.calls.contains_key(id) ==> {
            let c=s.calls[id]; let d=u.calls[id];
            u.calls.contains_key(id) && d.method==c.method && (c.submitted ==> d.submitted)
                && (c.answer.is_some() ==> c.answer==d.answer && c.submitted==d.submitted)
        })
    }),
    decreases k-i,
{
    if i<k {
        let h=(k-1) as nat; persists(p,t,a,i,h,id);
        assert(enabled(p,t[h as int],a[h as int]) && t[k as int]==step(p,t[h as int],a[h as int]));
    }
}
pub proof fn birth<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,k: nat,id: nat) -> (i: nat)
    requires path(p,t,a),t[0]==initial(p),k<=a.len(),t[k as int].calls.contains_key(id),
    ensures i<k, a[i as int]==Event::Invoke(id,t[k as int].calls[id].method), !t[i as int].calls.contains_key(id),
    decreases k,
{
    assert(k>0); let h=(k-1) as nat; let s=t[h as int]; let e=a[h as int];
    assert(t[k as int]==step(p,s,e) && enabled(p,s,e));
    if s.calls.contains_key(id) { birth(p,t,a,h,id) } else { h }
}
pub proof fn one_invocation<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,i: nat,j: nat,id: nat)
    requires path(p,t,a),i< j < a.len(),a[i as int] is Invoke,a[i as int]->Invoke_0==id,
    ensures !(a[j as int] is Invoke && a[j as int]->Invoke_0==id),
{
    assert(t[i as int+1]==step(p,t[i as int],a[i as int]));
    persists(p,t,a,i+1,j,id); assert(enabled(p,t[j as int],a[j as int]));
}

pub open spec fn body(c: Call,r: Replica) -> Option<Stamp> {
    match (c.legs)(r) { Leg::InFlight(x)|Leg::Received(x)=>Some(x), _=>None }
}
pub proof fn source<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,k: nat,id: nat,r: Replica) -> (h: nat)
    requires path(p,t,a),t[0]==initial(p),k<=a.len(),t[k as int].calls.contains_key(id),body(t[k as int].calls[id],r).is_some(),
    ensures h<k,t[h as int].calls.contains_key(id),a[h as int]==Event::Rpc(id,r,Stage::EmitReply),
        body(t[k as int].calls[id],r)==Some(stamp(p,t[h as int],r)),
    decreases k,
{
    assert(k>0); let j=(k-1) as nat; let s=t[j as int]; let ev=a[j as int];
    assert(enabled(p,s,ev) && t[k as int]==step(p,s,ev));
    if ev==Event::Rpc(id,r,Stage::EmitReply) { j } else {
        assert(s.calls.contains_key(id) && body(s.calls[id],r)==body(t[k as int].calls[id],r));
        source(p,t,a,j,id,r)
    }
}
pub proof fn decision<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,k: nat,id: nat) -> (j: nat)
    requires path(p,t,a),t[0]==initial(p),k<=a.len(),answer(t[k as int],id).is_some(),
    ensures ({
        let s=t[j as int]; let c=s.calls[id]; let d=t[k as int].calls[id]; let result=answer(t[k as int],id);
        j<k && s.calls.contains_key(id) && c.answer.is_none() && a[j as int]==Event::Poll(id) && c.method==d.method
            && c.submitted==d.submitted && if c.submitted {(p.reply)(s.base,id)==result}
            else {majority(rows(c).dom()) && early(c) && crate::metadata_reader::reference_read(Replica::R3)(rows(c))==result}
    }),
    decreases k,
{
    assert(k>0); let h=(k-1) as nat; let s=t[h as int]; let ev=a[h as int];
    assert(t[k as int]==step(p,s,ev) && enabled(p,s,ev));
    if answer(s,id).is_some() { decision(p,t,a,h,id) } else { h }
}
pub proof fn submission<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,k: nat,id: nat) -> (j: nat)
    requires path(p,t,a),t[0]==initial(p),k<=a.len(),t[k as int].calls.contains_key(id),t[k as int].calls[id].submitted,
    ensures j<k, input(t[j as int],a[j as int])==Input::Submit(id,t[k as int].calls[id].method),
    decreases k,
{
    assert(k>0); let h=(k-1) as nat; let s=t[h as int]; let ev=a[h as int];
    assert(enabled(p,s,ev) && t[k as int]==step(p,s,ev));
    if s.calls.contains_key(id) && s.calls[id].submitted { submission(p,t,a,h,id) } else { h }
}

// For delayed reports the linearization point is the *invocation*. A write
// may already have completed by the time the last open sample arrives.
pub proof fn fast_invoked_before_commands<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,
    k: nat,id: nat,i: nat)
    requires ports(p),path(p,t,a),t[0]==initial(p),k<=a.len(),i<k,
        a[i as int]==Event::Invoke(id,Method::Read),answer(t[k as int],id).is_some(),!t[k as int].calls[id].submitted,
    ensures answer(t[k as int],id)==Some(1),
        forall|w: int| 0<=w<=i ==> !(#[trigger] input(t[w],a[w]) is Submit && input(t[w],a[w])->Submit_1 is Command),
{
    let j=decision(p,t,a,k,id); let c=t[j as int].calls[id];
    good_at(p,t,a,j); early_stock_answer(c);
    assert forall|w: int| 0<=w<=i implies !(#[trigger] input(t[w],a[w]) is Submit && input(t[w],a[w])->Submit_1 is Command) by {
        let ev=input(t[w],a[w]);
        if ev is Submit && ev->Submit_1 is Command {
            let command=t[w].calls[ev->Submit_0]; good_at(p,t,a,w as nat);
            assert(command.method is Command && majority(rows(command).dom()));
            assert(exists|r: Replica| #[trigger] rows(command).contains_key(r) && #[trigger] rows(c).contains_key(r)) by {
                if rows(command).contains_key(Replica::R1) && rows(c).contains_key(Replica::R1) {}
                else if rows(command).contains_key(Replica::R2) && rows(c).contains_key(Replica::R2) {}
                else {assert(rows(command).contains_key(Replica::R3) && rows(c).contains_key(Replica::R3));}
            }
            let r=choose|r: Replica| #[trigger] rows(command).contains_key(r) && #[trigger] rows(c).contains_key(r);
            assert(t[w].closed.contains(r));
            let h=source(p,t,a,j,id,r);
            assert(rows(c)[r].version==0 && !t[h as int].closed.contains(r));
            if h<=i {
                persists(p,t,a,h,i,id); assert(enabled(p,t[i as int],a[i as int]));
            }
            persists(p,t,a,w as nat,h,id);
        }
    }
}

// Universal held-value clause of the underlying read. If the actual service
// used only Q, the result has a real sample in Q during that invocation.
pub open spec fn stock_sample_valid<X,E>(p: Engine<X,E>,used: Used<X,E>) -> bool {
    forall|xs: Seq<X>,es: Seq<Input<E>>,id: nat,q: Set<Replica>,i: nat,k: nat|
        #[trigger] backend_path(p,xs,es) && xs[0]==p.initial && i<k<=es.len() && #[trigger] es[i as int]==Input::Submit(id,Method::Read)
        && #[trigger] majority(q) && (#[trigger] (p.reply)(xs[k as int],id)).is_some()
        && (forall|j: int| i<=j<k && es[j] is Work ==> #[trigger] used(id,xs[j],es[j]).subset_of(q))
        ==> exists|j: int,r: Replica| i<=j<=k && q.contains(r) && #[trigger] (p.cell)(xs[j],r)==(p.reply)(xs[k as int],id).unwrap()
}

// Only underlying service work can constrain the choice of Q here. An
// unanswered probe, even to a third site, cannot supply the returned value.
pub open spec fn serving_work<X,E>(used: Used<X,E>,id: nat,s: State<X>,a: Event<E>) -> Set<Replica> {
    match a {Event::Work(w)=>used(id,s.base,Input::Work(w)), _=>Set::empty()}
}
pub proof fn actual_sample<X,E>(p: Engine<X,E>,used: Used<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,
    id: nat,q: Set<Replica>,i: nat,k: nat)
    requires ports(p),stock_sample_valid(p,used),path(p,t,a),t[0]==initial(p),i<k<=a.len(),
        a[i as int]==Event::Invoke(id,Method::Read),majority(q),answer(t[k as int],id).is_some(),
        forall|j: int| i<=j<k ==> #[trigger] serving_work(used,id,t[j],a[j]).subset_of(q),
    ensures exists|h: int,r: Replica| i<=h<=k && q.contains(r) && #[trigger] (p.cell)(t[h].base,r)==answer(t[k as int],id).unwrap(),
{
    let d=decision(p,t,a,k,id); let c=t[d as int].calls[id]; let v=answer(t[k as int],id).unwrap();
    assert(enabled(p,t[i as int],a[i as int]));
    if d<=i { persists(p,t,a,d,i,id); }
    assert(t[i as int+1]==step(p,t[i as int],a[i as int])); persists(p,t,a,i+1,d,id);
    if c.submitted {
        let s=submission(p,t,a,d,id); projection(p,t,a);
        if s<=i { assert(t[s as int].calls.contains_key(id)); persists(p,t,a,s,i,id); }
        let xs=base_states(t); let es=base_events(t,a);
        assert forall|j: int| s<=j<d && es[j] is Work implies #[trigger] used(id,xs[j],es[j]).subset_of(q) by {
            assert(serving_work(used,id,t[j],a[j]).subset_of(q));
        }
        assert(es[s as int]==Input::Submit(id,Method::Read) && (p.reply)(xs[d as int],id)==Some(v));
        let (h,r)=choose|h: int,r: Replica| s<=h<=d && q.contains(r) && #[trigger] (p.cell)(xs[h],r)==v;
        assert((p.cell)(t[h].base,r)==v);
    } else {
        good_at(p,t,a,d); early_stock_answer(c);
        let r=if rows(c).contains_key(Replica::R1) && q.contains(Replica::R1) {Replica::R1}
            else if rows(c).contains_key(Replica::R2) && q.contains(Replica::R2) {Replica::R2} else {Replica::R3};
        assert(rows(c).contains_key(r) && q.contains(r));
        let h=source(p,t,a,d,id,r);
        if h<=i { persists(p,t,a,h,i,id); }
        assert(rows(c)[r].version==0 && rows(c)[r].value==1);
        assert((p.cell)(t[h as int].base,r)==v);
    }
}

}
