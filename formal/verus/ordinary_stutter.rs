// Omit hybrid-only events without adding a protocol idle instruction to A.
// A fair, pending padded run must keep taking actual stock transitions.
// Those transitions form an infinite fair execution of the original SMR.
use vstd::prelude::*;
use crate::ordinary_fairness::{self as jobs,Scheduler};
use crate::stock_availability::{self as stock,ReadSystem,Stream};

verus! {

pub open spec fn erase<X,E>(t:Seq<X>,a:Seq<Option<E>>,k:nat) -> (Seq<X>,Seq<E>)
    decreases k,
{
    if k==0 { (seq![t[0]],Seq::empty()) } else {
        let i=(k-1) as nat; let (states,acts)=erase(t,a,i);
        match a[i as int] { Some(ev)=>(states.push(t[k as int]),acts.push(ev)), None=>(states,acts) }
    }
}
pub open spec fn padded<X,E>(p:ReadSystem<X,E>) -> ReadSystem<X,Option<E>> {
    ReadSystem {
        initial:p.initial,invoked:p.invoked,client_live:p.client_live,up:p.up,value:p.value,response:p.response,
        next:|x,o,y| match o {Some(a)=>(p.next)(x,a,y),None=>x==y},
        served_by:|t,a:Seq<Option<E>>,q| {let (s,b)=erase(t,a,a.len()); (p.served_by)(s,b,q)},
    }
}
proof fn erase_legal<X,E>(p:ReadSystem<X,E>,t:Seq<X>,a:Seq<Option<E>>,k:nat)
    requires stock::path(padded(p),t,a), k<=a.len(),
    ensures ({let (s,b)=erase(t,a,k); stock::path(p,s,b) && s[0]==t[0] && s.last()==t[k as int]}),
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat; let (s,b)=erase(t,a,i); erase_legal(p,t,a,i);
        assert((padded(p).next)(t[i as int],a[i as int],t[k as int]));
        if let Some(ev)=a[i as int] {
            let u=s.push(t[k as int]); let c=b.push(ev);
            assert forall|j:int| 0<=j<c.len() implies (p.next)(u[j],#[trigger] c[j],u[j+1]) by {
                if j<b.len() {assert((p.next)(s[j],b[j],s[j+1]));}
            }
        }
    }
}
pub proof fn same_reach<X,E>(p:ReadSystem<X,E>, x:X)
    ensures stock::reaches(padded(p),x)==stock::reaches(p,x),
{
    let m=padded(p);
    if stock::reaches(m,x) {
        let (t,a)=choose|t:Seq<X>,a:Seq<Option<E>>| #[trigger] stock::path(m,t,a) && (m.initial)(t[0]) && t.last()==x;
        let (s,b)=erase(t,a,a.len()); erase_legal(p,t,a,a.len());
        assert(stock::path(p,s,b) && (p.initial)(s[0]) && s.last()==x);
    } else if stock::reaches(p,x) {
        let (s,b)=choose|s:Seq<X>,b:Seq<E>| #[trigger] stock::path(p,s,b) && (p.initial)(s[0]) && s.last()==x;
        let a=Seq::new(b.len(),|i:int|Some(b[i]));
        assert forall|j:int| 0<=j<a.len() implies (m.next)(s[j],#[trigger] a[j],s[j+1]) by {assert((p.next)(s[j],b[j],s[j+1]));}
        assert(stock::path(m,s,a));
    }
}

pub enum Duty<J> { Ordinary(J), StockStep }
pub open spec fn scheduler<X,E,J>(p:ReadSystem<X,E>, t:Scheduler<X,E,J>) -> Scheduler<X,Option<E>,Duty<J>> {
    Scheduler {
        enabled:|x,j| match j {Duty::Ordinary(w)=>(t.enabled)(x,w),Duty::StockStep=>(p.response)(x).is_none()},
        taken:|x,a:Option<E>,y,j| match (a,j) {
            (Some(b),Duty::Ordinary(w))=>(t.taken)(x,b,y,w), (Some(_),Duty::StockStep)=>true, _=>false,
        },
    }
}
pub open spec fn first_real<X,E>(e:Stream<X,Option<E>>, from:nat, i:nat) -> bool {
    i>=from && (e.event)(i).is_some() && forall|k:nat| from<=k<i ==> (#[trigger] (e.event)(k)).is_none()
}
spec fn next_real<X,E>(e:Stream<X,Option<E>>, from:nat) -> nat {
    choose|i:nat| #[trigger] first_real(e,from,i)
}
spec fn cut<X,E>(e:Stream<X,Option<E>>, n:nat) -> nat decreases n {
    if n==0 {0} else {next_real(e,cut(e,(n-1) as nat))+1}
}
pub open spec fn advances<X,E>(e:Stream<X,Option<E>>,from:nat) -> bool {
    exists|i:nat| i>=from && (#[trigger] (e.event)(i)).is_some()
}
proof fn next_exists<X,E>(e:Stream<X,Option<E>>, from:nat)
    requires advances(e,from),
    ensures first_real(e,from,next_real(e,from)),
{
    let i=choose|i:nat| i>=from && (#[trigger] (e.event)(i)).is_some();
    let occurs=|n:nat|n>=from && (e.event)(n).is_some();
    let k=crate::confirmation::first_true(occurs,i);
    assert forall|h:nat| from<=h<k implies (#[trigger] (e.event)(h)).is_none() by {assert(!occurs(h));}
    assert(first_real(e,from,k));
}
spec fn compact<X,E>(e:Stream<X,Option<E>>) -> Stream<X,E> {
    Stream {state:|n| (e.state)(cut(e,n)),event:|n| (e.event)(next_real(e,cut(e,n))).unwrap()}
}
proof fn unchanged_until<X,E>(p:ReadSystem<X,E>,e:Stream<X,Option<E>>,from:nat,i:nat)
    requires stock::follows_stock(padded(p),e),advances(e,from),from<=i<=next_real(e,from),
    ensures (e.state)(i)==(e.state)(from),
    decreases i-from,
{
    if i>from {
        let k=(i-1) as nat; unchanged_until(p,e,from,k); next_exists(e,from);
        assert((e.event)(k).is_none());
        assert((padded(p).next)((e.state)(k),(e.event)(k),(e.state)(i)));
    }
}
// Locate a physical scheduler instant inside its finite block of padding
// and the one genuine stock event at the end of that block.
proof fn enclosing<X,E>(e:Stream<X,Option<E>>, n:nat, i:nat) -> (h:nat)
    requires forall|k:nat| #[trigger] advances(e,k), cut(e,n)<=i,
    ensures h>=n, cut(e,h)<=i<cut(e,h+1),
    decreases i-cut(e,n),
{
    next_exists(e,cut(e,n)); assert(cut(e,n+1)==next_real(e,cut(e,n))+1);
    if i<cut(e,n+1) {n} else {enclosing(e,n+1,i)}
}

proof fn compact_is_fair<X,E,J>(p:ReadSystem<X,E>, ts:Scheduler<X,E,J>, e:Stream<X,Option<E>>)
    requires stock::follows_stock(padded(p),e),jobs::fair(jobs::duties(scheduler(p,ts),e)),forall|k:nat| #[trigger] advances(e,k),
    ensures stock::follows_stock(p,compact(e)),jobs::fair(jobs::duties(ts,compact(e))),
{
    let s=compact(e); let native=jobs::duties(ts,s); let pad=jobs::duties(scheduler(p,ts),e);
    assert forall|n:nat| (p.next)((s.state)(n),#[trigger] (s.event)(n),(s.state)(n+1)) by {
        let from=cut(e,n); let i=next_real(e,from); next_exists(e,from); unchanged_until(p,e,from,i);
        assert(cut(e,n+1)==i+1);
        assert((padded(p).next)((e.state)(i),(e.event)(i),(e.state)(i+1)));
    }
    assert forall|n:nat,j:J| #[trigger] jobs::scheduled(native,n,j) by {
        let start=cut(e,n); let w=Duty::Ordinary(j);
        assert(jobs::scheduled(pad,start,w));
        let i=choose|i:nat| i>=start && #[trigger] jobs::discharged(pad,i,w);
        let h=enclosing(e,n,i); let from=cut(e,h); let at=next_real(e,from);
        assert(cut(e,h+1)==at+1); next_exists(e,from); unchanged_until(p,e,from,i);
        if (pad.taken)(i,w) {
            assert((e.event)(i).is_some()); assert(at==i);
        }
        assert(jobs::discharged(native,h,j));
    }
}

// Lift the stock A premise itself, for every reachable stock invocation.
// No fair progress claim is made on an infinite sequence of idle slots.
pub proof fn preserves_eventual<X,E,J>(p:ReadSystem<X,E>,tasks:Scheduler<X,E,J>)
    requires stock::eventual(p,|s| jobs::fair(jobs::duties(tasks,s))),
    ensures stock::eventual(padded(p),|e| jobs::fair(jobs::duties(scheduler(p,tasks),e))),
        jobs::idle_legal(padded(p),None),
{
    let m=padded(p); let t=scheduler(p,tasks); let f=|e:Stream<X,Option<E>>| jobs::fair(jobs::duties(t,e));
    assert forall|e:Stream<X,Option<E>>| #[trigger] stock::follows_stock(m,e) && f(e) && stock::reaches(m,(e.state)(0))
        && (m.invoked)((e.state)(0)) && (m.response)((e.state)(0)).is_none()
        && (forall|i:nat| (m.client_live)(#[trigger] (e.state)(i)) && crate::ordered_store::majority((m.up)((e.state)(i))))
        implies exists|k:nat| (m.response)(#[trigger] (e.state)(k)).is_some() by {
        if !(exists|k:nat| (m.response)(#[trigger] (e.state)(k)).is_some()) {
            let d=jobs::duties(t,e);
            assert forall|k:nat| #[trigger] advances(e,k) by {
                let j=Duty::<J>::StockStep; assert(jobs::scheduled(d,k,j));
                let i=choose|i:nat| i>=k && #[trigger] jobs::discharged(d,i,j);
                assert((e.event)(i).is_some());
            }
            compact_is_fair(p,tasks,e); let s=compact(e); same_reach(p,(e.state)(0));
            assert((s.state)(0)==(e.state)(0));
            assert forall|i:nat| (p.client_live)(#[trigger] (s.state)(i)) && crate::ordered_store::majority((p.up)((s.state)(i)))
                by {assert((m.client_live)((e.state)(cut(e,i))) && crate::ordered_store::majority((m.up)((e.state)(cut(e,i)))));}
            let sf=|s:Stream<X,E>|jobs::fair(jobs::duties(tasks,s)); assert(stock::follows_stock(p,s) && sf(s));
            let k=choose|k:nat| (p.response)(#[trigger] (s.state)(k)).is_some();
            assert((m.response)((e.state)(cut(e,k))).is_none());
        }
    }
}

// A's any-majority service may begin with any number of genuine internal
// self-loops. Its first state-changing transition still leaves exactly the
// invocation state. The transition can affect ordinary private memory only.
proof fn first_change<X,E>(p:ReadSystem<X,E>,t:Seq<X>,a:Seq<E>,k:nat) -> (i:nat)
    requires stock::path(p,t,a),k<t.len(),t[k as int]!=t[0],
    ensures i<k,t[i as int]==t[0],t[i as int+1]!=t[0],(p.next)(t[0],a[i as int],t[i as int+1]),
    decreases k,
{
    let j=(k-1) as nat;
    if t[j as int]!=t[0] {first_change(p,t,a,j)} else {
        assert((p.next)(t[j as int],a[j as int],t[k as int])); j
    }
}
pub open spec fn accounts_for_changes<X,E,J>(p:ReadSystem<X,E>,ts:Scheduler<X,E,J>,x:X) -> bool {
    forall|a:E,y:X| x!=y && #[trigger] (p.next)(x,a,y) ==>
        exists|j:J| #[trigger] (ts.taken)(x,a,y,j) && (ts.enabled)(x,j)
}
proof fn frozen_from<X,E>(p:ReadSystem<X,E>,e:Stream<X,Option<E>>,start:nat,i:nat)
    requires stock::follows_stock(padded(p),e),!advances(e,start),i>=start,
    ensures (e.state)(i)==(e.state)(start),
    decreases i-start,
{
    if i>start {
        let k=(i-1) as nat; frozen_from(p,e,start,k);
        assert((e.event)(k).is_none());
        assert((padded(p).next)((e.state)(k),(e.event)(k),(e.state)(i)));
    }
}

// Sharpen the finite-projection arm at a cut where A actually grants
// service on Q. If the scheduler accounts for the native first change,
// the stopped projection is also missing a named, continually enabled
// native job. No hybrid action is supplied by the stock witness.
pub proof fn majority_at_frozen_cut<X,E,J>(p:ReadSystem<X,E>,ts:Scheduler<X,E,J>,e:Stream<X,Option<E>>,
    start:nat,q:Set<crate::Replica>) -> (witness:(Seq<X>,Seq<E>,int,nat))
    requires stock::follows_stock(padded(p),e),!advances(e,start),jobs::invocation(p,(e.state)(start)),
        stock::available_majorities(p),crate::ordered_store::majority(q),q.subset_of((p.up)((e.state)(start))),
    ensures ({
        let x=(e.state)(start); let (t,a,v,i)=witness;
        stock::quorum_witness(p,x,q,t,a,v) && i<a.len() && t[i as int]==x && t[i as int+1]!=x
          && (p.next)(x,a[i as int],t[i as int+1])
          && (accounts_for_changes(p,ts,x) ==> exists|j:J| #[trigger] (ts.taken)(x,a[i as int],t[i as int+1],j)
              && (ts.enabled)(x,j) && !jobs::scheduled(jobs::duties(scheduler(p,ts),e),start,Duty::Ordinary(j)))
    }),
{
    let x=(e.state)(start);
    let (t,a,v)=choose|t:Seq<X>,a:Seq<E>,v:int| #[trigger] stock::quorum_witness(p,x,q,t,a,v);
    assert(t.last()!=x); let i=first_change(p,t,a,a.len());
    if accounts_for_changes(p,ts,x) {
        let j=choose|j:J| #[trigger] (ts.taken)(x,a[i as int],t[i as int+1],j) && (ts.enabled)(x,j);
        let d=jobs::duties(scheduler(p,ts),e); let work=Duty::Ordinary(j);
        assert forall|k:nat| k>=start implies !#[trigger] jobs::discharged(d,k,work) by {
            frozen_from(p,e,start,k); assert((e.event)(k).is_none());
        }
        assert(!jobs::scheduled(d,start,work));
    }
    (t,a,v,i)
}

}
