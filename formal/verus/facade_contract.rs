use vstd::prelude::*;
use crate::Replica;
use crate::ordered_store::majority;
use crate::stock_facade::*;
use crate::facade_progress::*;
use crate::facade_quorum::*;
use crate::facade_history::*;
use crate::facade_linear::*;

verus! {

pub open spec fn stock_a<X,E>(p: Engine<X,E>,fair: spec_fn(StockRun<X,E>)->bool,used: Used<X,E>) -> bool {
    stock_operation_progress(p,fair) && any_backend_majority(p,used) && stock_sample_valid(p,used)
}
pub open spec fn all_calls_served<X,E>(p: Engine<X,E>,fair: spec_fn(StockRun<X,E>)->bool) -> bool {
    forall|e: Run<X,E>,i: nat,id: nat| execution(p,e) && fair(project(e)) && front_fair(p,e)
        && (#[trigger] (e.state)(i)).calls.contains_key(id) && #[trigger] live_from(p,project(e),i,id)
        ==> exists|k: nat| k>=i && (#[trigger] answer((e.state)(k),id)).is_some()
}
pub open spec fn any_read_quorum<X,E>(p: Engine<X,E>,used: Used<X,E>) -> bool {
    forall|x: State<X>,id: nat,q: Set<Replica>| #[trigger] reachable(p,x) && x.calls.contains_key(id)
        && #[trigger] x.calls[id]==fresh(Method::Read) && (p.client)(x.base,id) && #[trigger] majority(q) && q.subset_of((p.up)(x.base))
        ==> exists|t: Seq<State<X>>,a: Seq<Event<E>>,v: int| #[trigger] outer_service(p,used,x,id,q,t,a,v)
}
pub open spec fn has_sample<X,E>(p: Engine<X,E>,t: Seq<State<X>>,q: Set<Replica>,id: nat,i: nat,k: nat) -> bool {
    exists|h: int,r: Replica| i<=h<=k && q.contains(r) && #[trigger] (p.cell)(t[h].base,r)==answer(t[k as int],id).unwrap()
}
pub open spec fn read_values_valid<X,E>(p: Engine<X,E>,used: Used<X,E>) -> bool {
    forall|t: Seq<State<X>>,a: Seq<Event<E>>,id: nat,q: Set<Replica>,i: nat,k: nat|
        #[trigger] path(p,t,a) && t[0]==initial(p) && i<k<=a.len() && #[trigger] a[i as int]==Event::Invoke(id,Method::Read)
        && #[trigger] majority(q) && (#[trigger] answer(t[k as int],id)).is_some()
        && (forall|j: int| i<=j<k ==> #[trigger] serving_work(used,id,t[j],a[j]).subset_of(q))
        ==> has_sample(p,t,q,id,i,k)
}
pub open spec fn outer_linearizable<X,E>(p: Engine<X,E>,f: CommandSemantics) -> bool {
    forall|t: Seq<State<X>>,a: Seq<Event<E>>| #[trigger] path(p,t,a) && t[0]==initial(p)
        ==> exists|g: Grid| #[trigger] ordered(g,f,a.len()) && certifies(g,a.len(),
            |i: nat,id: nat,m: Method| a[i as int]==Event::Invoke(id,m),|i: nat,id: nat|answer(t[i as int],id))
}

// Uniform in the supplied backend, its full command language and all its
// reachable schedules. There is no postulated linearization or progress of
// the new front end. Idle represents unobserved front-only steps of the API.
pub proof fn construction_preserves_full_a_and_safety<X,E>(p: Engine<X,E>,f: CommandSemantics,
    fair: spec_fn(StockRun<X,E>)->bool,used: Used<X,E>)
    requires ports(p),stock_a(p,fair,used),base_linearizable(p,f),
    ensures all_calls_served(p,fair),any_read_quorum(p,used),read_values_valid(p,used),outer_linearizable(p,f),
{
    hide(outer_service); hide(path); hide(reachable); hide(ordered); hide(certifies); hide(live_from); hide(front_fair);
    assert forall|e: Run<X,E>,i: nat,id: nat| execution(p,e) && fair(project(e)) && front_fair(p,e)
        && (#[trigger] (e.state)(i)).calls.contains_key(id) && #[trigger] live_from(p,project(e),i,id)
        implies exists|k: nat| k>=i && (#[trigger] answer((e.state)(k),id)).is_some() by {
        let k=every_outer_operation_finishes(p,fair,e,i,id);
        later(p,e,i,k,id,Replica::R1); assert(answer((e.state)(k),id).is_some());
    }
    assert forall|x: State<X>,id: nat,q: Set<Replica>| #[trigger] reachable(p,x) && x.calls.contains_key(id)
        && #[trigger] x.calls[id]==fresh(Method::Read) && (p.client)(x.base,id) && #[trigger] majority(q) && q.subset_of((p.up)(x.base))
        implies exists|t: Seq<State<X>>,a: Seq<Event<E>>,v: int| #[trigger] outer_service(p,used,x,id,q,t,a,v) by {
        any_live_majority_serves(p,used,x,id,q);
    }
    assert forall|t: Seq<State<X>>,a: Seq<Event<E>>,id: nat,q: Set<Replica>,i: nat,k: nat|
        #[trigger] path(p,t,a) && t[0]==initial(p) && i<k<=a.len() && #[trigger] a[i as int]==Event::Invoke(id,Method::Read)
        && #[trigger] majority(q) && (#[trigger] answer(t[k as int],id)).is_some()
        && (forall|j: int| i<=j<k ==> #[trigger] serving_work(used,id,t[j],a[j]).subset_of(q))
        implies has_sample(p,t,q,id,i,k) by { actual_sample(p,used,t,a,id,q,i,k); }
    assert forall|t: Seq<State<X>>,a: Seq<Event<E>>| #[trigger] path(p,t,a) && t[0]==initial(p)
        implies exists|g: Grid| #[trigger] ordered(g,f,a.len()) && certifies(g,a.len(),
            |i: nat,id: nat,m: Method| a[i as int]==Event::Invoke(id,m),|i: nat,id: nat|answer(t[i as int],id))
        by { all_outer_histories_linearize(p,f,t,a); }
}

}
