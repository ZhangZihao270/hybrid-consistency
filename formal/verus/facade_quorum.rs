use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::prefix_index;
use crate::ordered_store::majority;
use crate::stock_facade::*;

// Finite, physical service of any chosen live majority. Work is a genuine
// backend action. "used" names sites serving this invocation, not unrelated
// traffic or probes which need no reply.
verus! {

pub type Used<X,E> = spec_fn(nat,X,Input<E>) -> Set<Replica>;

pub open spec fn base_service<X,E>(p: Engine<X,E>,used: Used<X,E>,x: X,id: nat,q: Set<Replica>,
    t: Seq<X>,w: Seq<E>,v: int) -> bool {
    t.len()==w.len()+1 && t[0]==(p.step)(x,Input::Submit(id,Method::Read))
    && (p.reply)(t.last(),id)==Some(v)
    && (forall|i: int| 0<=i<t.len() ==> (p.client)(#[trigger] t[i],id) && q.subset_of((p.up)(t[i])))
    && (forall|i: int| 0<=i<w.len() ==> {
        let a=Input::Work(#[trigger] w[i]);
        (p.ready)(t[i],a) && t[i+1]==(p.step)(t[i],a) && used(id,t[i],a).subset_of(q)
    })
    && exists|i: int,r: Replica| 0<=i<t.len() && q.contains(r) && #[trigger] (p.cell)(t[i],r)==v
}

pub open spec fn any_backend_majority<X,E>(p: Engine<X,E>,used: Used<X,E>) -> bool {
    forall|x: X,id: nat,q: Set<Replica>| #[trigger] backend_reachable(p,x) && (#[trigger] (p.submitted)(x,id)).is_none()
        && (p.client)(x,id) && #[trigger] majority(q) && q.subset_of((p.up)(x))
        ==> exists|t: Seq<X>,w: Seq<E>,v: int| #[trigger] base_service(p,used,x,id,q,t,w,v)
}

pub open spec fn run_to<X,E>(p: Engine<X,E>,x: State<X>,a: Seq<Event<E>>,k: nat) -> State<X>
    decreases k,
{
    if k==0 {x} else { step(p,run_to(p,x,a,(k-1) as nat),a[k-1]) }
}
pub open spec fn states<X,E>(p: Engine<X,E>,x: State<X>,a: Seq<Event<E>>) -> Seq<State<X>> {
    Seq::new(a.len()+1, |i: int| run_to(p,x,a,i as nat))
}
pub open spec fn site(i: nat) -> Replica {
    if i<3 {Replica::R1} else if i<6 {Replica::R2} else {Replica::R3}
}
pub open spec fn slot(r: Replica) -> nat {
    match r {Replica::R1=>0,Replica::R2=>3,Replica::R3=>6}
}
pub open spec fn survey<E>(id: nat,q: Set<Replica>) -> Seq<Event<E>> {
    Seq::new(12,|i: int| {
        let r=if i<3 {site(3*(i as nat))} else {site((i-3) as nat)};
        if !q.contains(r) {Event::Idle} else if i<3 { Event::Rpc(id,r,Stage::Offer) }
        else {Event::Rpc(id,r,if i%3==0 {Stage::DeliverRequest} else if i%3==1 {Stage::EmitReply} else {Stage::DeliverReply})}
    })
}
pub open spec fn at_site<X,E>(p: Engine<X,E>,x: State<X>,r: Replica,q: Set<Replica>,k: nat) -> Leg {
    let s=slot(r)+3;
    if !q.contains(r) || k<=slot(r)/3 {Leg::Unsent} else if k<=s { Leg::Request }
    else if k==s+1 {Leg::AtServer} else if k==s+2 {Leg::InFlight(stamp(p,x,r))}
    else {Leg::Received(stamp(p,x,r))}
}

proof fn survey_step<X,E>(p: Engine<X,E>,x: State<X>,id: nat,q: Set<Replica>,k: nat)
    requires ports(p),backend_reachable(p,x.base),(p.client)(x.base,id),q.subset_of((p.up)(x.base)),
        x.calls.contains_key(id),x.calls[id]==fresh(Method::Read),k<=12,
    ensures ({
        let a=survey(id,q); let s=run_to(p,x,a,k);
        s.base==x.base && s.closed==x.closed && s.calls.contains_key(id) &&
        s.calls[id]==(Call {legs: |r| at_site(p,x,r,q,k), ..fresh(Method::Read)})
            && (k<12 ==> enabled(p,s,a[k as int]))
    }),
    decreases k,
{
    let a=survey(id,q); let s=run_to(p,x,a,k);
    prefix_index(k as int);
    if k>0 {
        let h=(k-1) as nat; survey_step(p,x,id,q,h); let old=run_to(p,x,a,h);
        assert(s==step(p,old,a[h as int]));
    }
    assert(s.calls[id].legs =~= (|r| at_site(p,x,r,q,k)));
}

pub proof fn physical_survey<X,E>(p: Engine<X,E>,x: State<X>,id: nat,q: Set<Replica>)
    requires ports(p),reachable(p,x),(p.client)(x.base,id),q.subset_of((p.up)(x.base)),
        x.calls.contains_key(id),x.calls[id]==fresh(Method::Read), majority(q),
    ensures ({
        let a=survey(id,q); let t=states(p,x,a); let s=t.last();
        path(p,t,a) && t[0]==x && s.base==x.base && s.calls.contains_key(id)
            && rows(s.calls[id]).dom()==q && !s.calls[id].submitted && s.calls[id].method is Read && s.calls[id].answer.is_none()
            && (forall|r: Replica| #[trigger] q.contains(r) ==> rows(s.calls[id])[r]==stamp(p,x,r))
            && (forall|i: int| 0<=i<t.len() ==> (#[trigger] t[i]).base==x.base)
    }),
{
    reachable_good(p,x); let a=survey(id,q); let t=states(p,x,a);
    assert forall|i: int| 0<=i<a.len() implies enabled(p,t[i],#[trigger] a[i]) && t[i+1]==step(p,t[i],a[i])
        by { survey_step(p,x,id,q,i as nat); }
    assert forall|i: int| 0<=i<t.len() implies (#[trigger] t[i]).base==x.base by {survey_step(p,x,id,q,i as nat);}
    survey_step(p,x,id,q,12); assert(rows(t.last().calls[id]).dom() =~= q);
}
pub proof fn join<X,E>(p: Engine<X,E>,s: Seq<State<X>>,a: Seq<Event<E>>,t: Seq<State<X>>,b: Seq<Event<E>>)
    requires path(p,s,a), path(p,t,b), s.last()==t[0],
    ensures path(p,s+t.drop_first(),a+b),
{
    let u=s+t.drop_first(); let c=a+b;
    assert forall|i: int| 0<=i<c.len() implies enabled(p,u[i],#[trigger] c[i]) && u[i+1]==step(p,u[i],c[i]) by {
        if i<a.len() { assert(enabled(p,s[i],a[i])); } else {
            let j=i-a.len(); assert(enabled(p,t[j],b[j])); assert(u[i]==t[j] && u[i+1]==t[j+1]);
        }
    }
}
pub proof fn extend_reach<X,E>(p: Engine<X,E>,x: State<X>,t: Seq<State<X>>,a: Seq<Event<E>>)
    requires reachable(p,x),t[0]==x,path(p,t,a),
    ensures reachable(p,t.last()),
{
    let (s,b)=choose|s: Seq<State<X>>,b: Seq<Event<E>>| #[trigger] path(p,s,b) && s[0]==initial(p) && s.last()==x;
    join(p,s,b,t,a); let all=s+t.drop_first(); assert(all.last()==t.last());
}
proof fn lifted_work<X,E>(p: Engine<X,E>,start: State<X>,t: Seq<X>,w: Seq<E>,i: nat)
    requires t.len()==w.len()+1,t[0]==start.base,i<=w.len(),
        forall|j: int| 0<=j<w.len() ==> (p.ready)(t[j],Input::Work(#[trigger] w[j])) && t[j+1]==(p.step)(t[j],Input::Work(w[j])),
    ensures ({
        let acts=Seq::new(w.len(),|j: int| Event::Work(w[j])); let s=run_to(p,start,acts,i);
        s.base==t[i as int] && s.calls==start.calls
    }),
    decreases i,
{
    if i>0 { let j=(i-1) as nat; lifted_work(p,start,t,w,j); assert((p.ready)(t[j as int],Input::Work(w[j as int]))); }
}

pub open spec fn participants<X,E>(used: Used<X,E>,id: nat,s: State<X>,a: Event<E>) -> Set<Replica> {
    match a {
        Event::Rpc(i,r,_) if i==id => set![r],
        Event::Work(w) => used(id,s.base,Input::Work(w)), _=>Set::empty(),
    }
}
pub open spec fn held<X,E>(p: Engine<X,E>,t: Seq<State<X>>,q: Set<Replica>,v: int) -> bool {
    exists|i: int,r: Replica| 0<=i<t.len() && q.contains(r) && #[trigger] (p.cell)(t[i].base,r)==v
}
proof fn sampled_at<X,E>(p: Engine<X,E>,t: Seq<State<X>>,q: Set<Replica>,v: int,i: int,r: Replica)
    requires 0<=i<t.len(),q.contains(r),(p.cell)(t[i].base,r)==v,
    ensures held(p,t,q,v),
{}

pub open spec fn pending_within<X,E>(used: Used<X,E>,id: nat,q: Set<Replica>,s: State<X>,a: Event<E>) -> bool {
    s.calls.contains_key(id) && s.calls[id].answer.is_none() && participants(used,id,s,a).subset_of(q)
}
pub open spec fn live_quorum<X,E>(p: Engine<X,E>,s: State<X>,id: nat,q: Set<Replica>) -> bool {
    (p.client)(s.base,id) && q.subset_of((p.up)(s.base))
}

pub open spec fn outer_service<X,E>(p: Engine<X,E>,used: Used<X,E>,x: State<X>,id: nat,q: Set<Replica>,
    t: Seq<State<X>>,a: Seq<Event<E>>,v: int) -> bool {
    path(p,t,a) && t[0]==x && t.last().calls[id].answer==Some(v)
        && (forall|i: int| 0<=i<a.len() ==> #[trigger] pending_within(used,id,q,t[i],a[i]))
        && (forall|i: int| 0<=i<t.len() ==> #[trigger] live_quorum(p,t[i],id,q))
        && held(p,t,q,v)
}

#[verifier::rlimit(16)]
pub proof fn any_live_majority_serves<X,E>(p: Engine<X,E>,used: Used<X,E>,x: State<X>,id: nat,q: Set<Replica>)
    requires ports(p), any_backend_majority(p,used),reachable(p,x), x.calls.contains_key(id),x.calls[id]==fresh(Method::Read),
        (p.client)(x.base,id),majority(q),q.subset_of((p.up)(x.base)),
    ensures exists|t: Seq<State<X>>,a: Seq<Event<E>>,v: int| #[trigger] outer_service(p,used,x,id,q,t,a,v),
{
    hide(run_to); hide(reachable); hide(backend_reachable); hide(fresh); hide(inspectable);
    let a=survey(id,q); let t=states(p,x,a); let s=t.last(); let call=Event::Poll(id);
    physical_survey(p,x,id,q); extend_reach(p,x,t,a); reachable_good(p,s);
    let u=step(p,s,call); let init=t.push(u); let seq=a.push(call);
    assert((p.submitted)(s.base,id).is_none() && enabled(p,s,call));
    join(p,t,a,seq![s,u],seq![call]); assert(init =~= t+seq![s,u].drop_first()); assert(seq =~= a+seq![call]);
    assert forall|i: int| 0<=i<a.len() implies #[trigger] pending_within(used,id,q,t[i],a[i]) by {
        reachable_good(p,x); survey_step(p,x,id,q,i as nat); reveal(fresh);
    }
    if early(s.calls[id]) {
        early_stock_answer(s.calls[id]);
        let r=choose|r: Replica| q.contains(r); assert(q.contains(r) && rows(s.calls[id]).contains_key(r));
        assert((p.cell)(x.base,r)==1 && (p.cell)(init[0].base,r)==1);
        assert(u.base==x.base && u.calls[id].answer==Some(1));
        assert forall|i: int| 0<=i<seq.len() implies #[trigger] pending_within(used,id,q,init[i],seq[i]) by {
            if i<a.len() {
                reachable_good(p,x); survey_step(p,x,id,q,i as nat); reveal(fresh);
                assert(t[i].calls.contains_key(id) && t[i].calls[id].answer.is_none());
                assert(!((a[i] is Rpc) && !q.contains(a[i]->Rpc_1)));
            }
        }
        assert forall|i: int| 0<=i<init.len() implies #[trigger] live_quorum(p,init[i],id,q) by {
            if i<t.len() { assert(t[i].base==x.base); }
        }
        sampled_at(p,init,q,1,0,r);
        assert(path(p,init,seq) && init[0]==x && init.last().calls[id].answer==Some(1));
        assert(outer_service(p,used,x,id,q,init,seq,1));
    } else {
        assert(backend_reachable(p,s.base) && (p.submitted)(s.base,id).is_none() && (p.client)(s.base,id));
        assert(exists|bt: Seq<X>,w: Seq<E>,v: int| #[trigger] base_service(p,used,s.base,id,q,bt,w,v));
        let (bt,w,v)=choose|bt: Seq<X>,w: Seq<E>,v: int| #[trigger] base_service(p,used,s.base,id,q,bt,w,v);
        let acts=Seq::new(w.len(),|i: int| Event::Work(w[i])); let bs=states(p,u,acts);
        assert forall|i: int| 0<=i<bs.len() implies (#[trigger] bs[i]).base==bt[i] && bs[i].calls==u.calls by {
            lifted_work(p,u,bt,w,i as nat);
        }
        assert forall|i: int| 0<=i<w.len() implies enabled(p,bs[i],#[trigger] acts[i]) && bs[i+1]==step(p,bs[i],acts[i]) by {
            assert((p.ready)(bt[i],Input::Work(w[i]))); reveal(run_to);
        }
        assert(bs[0]==u) by {reveal(run_to);}
        assert(path(p,bs,acts)); join(p,init,seq,bs,acts);
        let middle=init+bs.drop_first(); let events=seq+acts; let last=middle.last();
        assert(last==bs.last()); extend_reach(p,x,middle,events); reachable_good(p,last);
        assert(enabled(p,last,call)); let end=step(p,last,call);
        join(p,middle,events,seq![last,end],seq![call]); let result=middle.push(end); let all=events.push(call);
        assert(result =~= middle+seq![last,end].drop_first()); assert(all =~= events+seq![call]);
        assert forall|i: int| 0<=i<all.len() implies #[trigger] pending_within(used,id,q,result[i],all[i]) by {
            if i>=seq.len() && i<events.len() {
                let j=i-seq.len(); assert(result[i]==bs[j]);
                assert(used(id,bt[j],Input::Work(w[j])).subset_of(q));
            } else if i==events.len() { assert(result[i]==last); } else if i<a.len() {assert(pending_within(used,id,q,t[i],a[i]));}
        }
        assert forall|i: int| 0<=i<result.len() implies #[trigger] live_quorum(p,result[i],id,q) by {
            if seq.len()<=i<=events.len() { let j=i-seq.len(); assert(result[i]==bs[j]); assert((p.client)(bt[j],id)); }
            else if i>events.len() { assert(end.base==last.base && (p.client)(bt.last(),id)); }
        }
        let (j,r)=choose|j: int,r: Replica| 0<=j<bt.len() && q.contains(r) && #[trigger] (p.cell)(bt[j],r)==v;
        assert(result[seq.len()+j]==bs[j] && (p.cell)(result[seq.len()+j].base,r)==v);
        sampled_at(p,result,q,v,seq.len()+j,r);
        assert(result.last()==end && end.calls[id].answer==Some(v));
        assert(path(p,result,all) && result[0]==x);
        assert(outer_service(p,used,x,id,q,result,all,v));
    }
}

}
