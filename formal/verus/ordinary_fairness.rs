// Ordinary scheduler obligations on a stock projection of a hybrid execution.
use vstd::prelude::*;
use crate::stock_availability as stock;
use stock::{ReadSystem, Stream};
use crate::ordered_store::majority;

verus! {

#[verifier::reject_recursive_types(J)]
pub struct Duties<J> {
    pub enabled: spec_fn(nat, J) -> bool,
    pub taken: spec_fn(nat, J) -> bool,
}

pub open spec fn discharged<J>(d: Duties<J>, i: nat, j: J) -> bool {
    !(d.enabled)(i,j) || (d.taken)(i,j)
}
pub open spec fn scheduled<J>(d: Duties<J>, from: nat, j: J) -> bool {
    exists|i: nat| i >= from && #[trigger] discharged(d,i,j)
}
pub open spec fn fair<J>(d: Duties<J>) -> bool {
    forall|from: nat, j: J| #[trigger] scheduled(d,from,j)
}

#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(E)]
#[verifier::reject_recursive_types(J)]
pub struct Scheduler<X,E,J> {
    pub enabled: spec_fn(X,J) -> bool,
    pub taken: spec_fn(X,E,X,J) -> bool,
}
pub open spec fn duties<X,E,J>(tasks: Scheduler<X,E,J>, e: Stream<X,E>) -> Duties<J> {
    Duties {
        enabled: |i:nat,j| (tasks.enabled)((e.state)(i),j),
        taken: |i:nat,j| (tasks.taken)((e.state)(i),(e.event)(i),(e.state)(i+1),j),
    }
}

// A helper is the identity of actual ordinary work (a pending delivery,
// local job, timer, etc.). Each persistent stock obligation gets its own
// measure. Different obligations may borrow the same implementation job.
#[verifier::reject_recursive_types(J)]
#[verifier::reject_recursive_types(K)]
pub struct Support<J,K> {
    pub remaining: spec_fn(nat,J) -> nat,
    pub helper: spec_fn(nat,J) -> K,
}

pub open spec fn supports_at<J,K>(s: Duties<J>, h: Duties<K>, p: Support<J,K>, i: nat, j: J) -> bool {
    if discharged(s,i,j) || !(s.enabled)(i+1,j) { true } else {
        let k = (p.helper)(i,j);
        (p.remaining)(i+1,j) < (p.remaining)(i,j)
        || ((p.remaining)(i+1,j) == (p.remaining)(i,j) && (p.helper)(i+1,j) == k
            && (h.enabled)(i,k) && !(h.taken)(i,k))
    }
}
pub open spec fn supports<J,K>(s: Duties<J>, h: Duties<K>, p: Support<J,K>) -> bool {
    forall|i: nat, j: J| #[trigger] supports_at(s,h,p,i,j)
}

proof fn constant_helper<J,K>(s: Duties<J>, h: Duties<K>, p: Support<J,K>, j: J, at: nat, i: nat)
    requires supports(s,h,p), !scheduled(s,at,j), at <= i,
        forall|u: nat| u >= at ==> (p.remaining)(at,j) <= #[trigger] (p.remaining)(u,j),
    ensures (p.remaining)(i,j) == (p.remaining)(at,j), (p.helper)(i,j) == (p.helper)(at,j),
        !discharged(h,i,(p.helper)(at,j)),
    decreases i - at,
{
    if i > at {
        let k = (i-1) as nat;
        constant_helper(s,h,p,j,at,k);
        assert(!discharged(s,k,j) && !discharged(s,i,j) && supports_at(s,h,p,k,j));
    }
    assert(!discharged(s,i,j) && !discharged(s,i+1,j) && supports_at(s,h,p,i,j));
    assert((p.remaining)(i+1,j) >= (p.remaining)(at,j));
}

// No fairness of infinitely withheld packets and no rank to a read result.
pub proof fn fair_support_transfers<J,K>(s: Duties<J>, h: Duties<K>, p: Support<J,K>)
    requires fair(h), supports(s,h,p),
    ensures fair(s),
{
    assert forall|start: nat, j: J| #[trigger] scheduled(s,start,j) by {
        if !scheduled(s,start,j) {
            let debt=|i:nat| (p.remaining)(i,j);
            let at=crate::ordinary_service::minimum(debt,start,start);
            assert forall|u:nat| u>=at implies (p.remaining)(at,j) <= #[trigger] (p.remaining)(u,j) by {assert(debt(at)<=debt(u));}
            assert(!scheduled(s,at,j)) by {
                if scheduled(s,at,j) {
                    let i = choose|i:nat| i >= at && #[trigger] discharged(s,i,j);
                    assert(scheduled(s,start,j));
                }
            }
            let helper = (p.helper)(at,j);
            assert(scheduled(h,at,helper));
            let i = choose|i:nat| i >= at && #[trigger] discharged(h,i,helper);
            constant_helper(s,h,p,j,at,i);
        }
    }
}

// For identified jobs with the same occurrence, fair scheduling yields a
// precise diagnosis. Hybrid refusal recurs arbitrarily late; it need not
// be permanent.
pub open spec fn refused_after<J>(d: Duties<J>, t: nat, j: J) -> bool {
    exists|i:nat| i>=t && !(#[trigger] (d.enabled)(i,j))
}
pub open spec fn refusals<J>(d: Duties<J>, start: nat, j: J) -> bool {
    forall|t: nat| t >= start ==> #[trigger] refused_after(d,t,j)
}
pub proof fn locate_refusal<J>(s: Duties<J>, h: Duties<J>, start: nat, j: J)
    requires !scheduled(s,start,j), fair(h),
        forall|i: nat| i >= start && #[trigger] (h.taken)(i,j) ==> (s.taken)(i,j),
    ensures refusals(h,start,j),
{
    assert forall|t:nat| t>=start implies #[trigger] refused_after(h,t,j) by {
        assert(scheduled(h,t,j));
        let i = choose|i:nat| i>=t && #[trigger] discharged(h,i,j);
        assert(!discharged(s,i,j));
    }
}

// Instrument the distinguished client's ordinary pending-to-answered edge.
// No condition compares the values of replies on two executions.
pub open spec fn published<X,E>(p:ReadSystem<X,E>, x:X, y:X) -> bool {
    (p.response)(x).is_none() && (p.response)(y).is_some()
}
pub open spec fn live<X,E>(p: ReadSystem<X,E>, x: X) -> bool {
    (p.client_live)(x) && majority((p.up)(x))
}
pub open spec fn invocation<X,E>(p: ReadSystem<X,E>, x: X) -> bool {
    stock::reaches(p,x) && (p.invoked)(x) && (p.response)(x).is_none() && live(p,x)
}
pub open spec fn idle_legal<X,E>(p: ReadSystem<X,E>, idle: E) -> bool {
    forall|x:X| live(p,x) ==> #[trigger] (p.next)(x,idle,x)
}

#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(E)]
pub struct Replay<X,E> {
    pub start:X, pub idle:E,
    // Ordinary input and proposed stock successor at this actual event.
    pub propose:spec_fn(X,nat)->(E,X),
}
pub open spec fn legal_candidate<X,E>(p:ReadSystem<X,E>, idle:E, x:X, edge:(E,X)) -> (E,X) {
    let (a,y)=edge;
    if (p.next)(x,a,y) && live(p,y) { edge } else { (idle,x) }
}
pub open spec fn ordinary_step<X,E>(p:ReadSystem<X,E>, r:Replay<X,E>, x:X, i:nat) -> (E,X) {
    legal_candidate(p,r.idle,x,(r.propose)(x,i))
}
pub open spec fn state_at<X,E>(p:ReadSystem<X,E>, r:Replay<X,E>, i:nat) -> X
    decreases i,
{
    if i==0 { r.start } else {
        let k=(i-1) as nat; ordinary_step(p,r,state_at(p,r,k),k).1
    }
}
pub open spec fn projection<X,E>(p:ReadSystem<X,E>, r:Replay<X,E>) -> Stream<X,E> {
    Stream { state:|i| state_at(p,r,i), event:|i| ordinary_step(p,r,state_at(p,r,i),i).0 }
}
proof fn live_at<X,E>(p:ReadSystem<X,E>, r:Replay<X,E>, i:nat)
    requires live(p,r.start),
    ensures live(p,state_at(p,r,i)),
    decreases i,
{
    if i>0 { live_at(p,r,(i-1) as nat); }
}
pub proof fn legal_projection<X,E>(p:ReadSystem<X,E>, r:Replay<X,E>)
    requires invocation(p,r.start), idle_legal(p,r.idle),
    ensures stock::follows_stock(p,projection(p,r)),
        forall|i:nat| live(p,#[trigger] state_at(p,r,i)),
{
    let e=projection(p,r);
    assert forall|i:nat| live(p,#[trigger] state_at(p,r,i)) by { live_at(p,r,i); }
    assert forall|i:nat| (p.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i+1)) by {
        assert(state_at(p,r,i+1)==ordinary_step(p,r,(e.state)(i),i).1);
    }
}

pub open spec fn emitted_at<X,E>(p:ReadSystem<X,E>, e:Stream<X,E>, i:nat) -> bool {
    published(p,(e.state)(i),(e.state)(i+1))
}
proof fn find_publication<X,E>(p:ReadSystem<X,E>, e:Stream<X,E>, i:nat) -> (k:nat)
    requires (p.response)((e.state)(0)).is_none(), (p.response)((e.state)(i)).is_some(),
    ensures k<i, emitted_at(p,e,k),
    decreases i,
{
    let j=(i-1) as nat;
    if (p.response)((e.state)(j)).is_some() { find_publication(p,e,j) } else { j }
}

// The unfiltered diagnosis. The proposal is entirely unrestricted and
// may even produce a stock publication which the real client never made.
// That is a separate, finite discrepancy, never evidence of a weak wait.
pub proof fn stock_progress_or_starvation<X,E,J>(p:ReadSystem<X,E>, tasks:Scheduler<X,E,J>, r:Replay<X,E>)
    requires stock::eventual(p,|e| fair(duties(tasks,e))), invocation(p,r.start), idle_legal(p,r.idle),
    ensures (exists|i:nat| #[trigger] emitted_at(p,projection(p,r),i))
        || (exists|j:J, from:nat| !#[trigger] scheduled(duties(tasks,projection(p,r)),from,j)),
{
    let e=projection(p,r); let f=|e:Stream<X,E>| fair(duties(tasks,e));
    legal_projection(p,r);
    if fair(duties(tasks,e)) {
        assert((e.state)(0)==r.start);
        assert forall|i:nat| (p.client_live)(#[trigger] (e.state)(i)) && majority((p.up)((e.state)(i))) by {
            live_at(p,r,i);
        }
        assert(stock::follows_stock(p,e) && f(e));
        let i=choose|i:nat| (p.response)(#[trigger] (e.state)(i)).is_some();
        let k=find_publication(p,e,i);
        assert(emitted_at(p,e,k));
    }
}

// An ordinary projection can drop a step that would invent a client
// return. It may ignore an actual return or return a different value.
// A real idle must be legal; skipping a job does not pay its fairness debt.
pub open spec fn public_candidate<X,E>(p:ReadSystem<X,E>, idle:E, x:X, edge:(E,X), real_return:bool) -> (E,X) {
    if published(p,x,edge.1) && !real_return { (idle,x) } else { edge }
}
pub open spec fn marked_replay<X,E>(p:ReadSystem<X,E>, r:Replay<X,E>, output:spec_fn(nat)->bool) -> Replay<X,E> {
    Replay { propose:|x,i| public_candidate(p,r.idle,x,(r.propose)(x,i),output(i)), ..r }
}
pub proof fn projection_reports_only_real_events<X,E>(p:ReadSystem<X,E>, r:Replay<X,E>, out:spec_fn(nat)->bool, i:nat)
    ensures emitted_at(p,projection(p,marked_replay(p,r,out)),i) ==> out(i),
{
    let t=marked_replay(p,r,out); let x=state_at(p,t,i);
    assert(state_at(p,t,i+1)==ordinary_step(p,t,x,i).1);
}

// This is one sufficient hybrid progress condition. The new obligation
// concerns scheduling of individual ordinary jobs, including local work
// and outstanding strong messages. It does not choose either read's value.
pub proof fn ordinary_service_from_a<X,E,J,K>(p: ReadSystem<X,E>, tasks: Scheduler<X,E,J>,
    r: Replay<X,E>, output: spec_fn(nat)->bool, actual: Duties<K>, support: Support<J,K>)
    requires stock::eventual(p,|e| fair(duties(tasks,e))), invocation(p,r.start), idle_legal(p,r.idle),
        fair(actual), supports(duties(tasks,projection(p,marked_replay(p,r,output))),actual,support),
    ensures exists|i:nat| #[trigger] output(i),
{
    let t=marked_replay(p,r,output); let e=projection(p,t);
    fair_support_transfers(duties(tasks,e),actual,support);
    stock_progress_or_starvation(p,tasks,t);
    let k=choose|i:nat| #[trigger] emitted_at(p,e,i);
    projection_reports_only_real_events(p,r,output,k);
}

}
