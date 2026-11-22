// Start with an actual stock witness served by the selected majority.
// Follow real hybrid progress options until C2 posts or a local obligation
// fails. No correspondence of return values or complete execution states.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::promotion_wait::{self as wait,Path,Relation};
use crate::read_call::{self as call,Program,Log,Event};
use crate::read_nonblocking::{self as nb,Region};
use crate::read_service_contract as contract;
use crate::service_obstruction::{original_reads,suffix_protocol};
use crate::stock_availability as stock;

verus! {

#[verifier::reject_recursive_types(X)]
#[verifier::reject_recursive_types(E)]
#[verifier::reject_recursive_types(Y)]
#[verifier::reject_recursive_types(A)]
pub struct Correspondence<X,E,Y,A> {
    pub represents: spec_fn(X,Y)->bool,
    pub preparation: spec_fn(X,Y)->nat,
    pub implements: spec_fn(X,E,X,Y,A,Y)->bool,
}

// Cursor i counts actual instructions on this stock path. Preparation may
// involve any number of ordinary changes, including other strong messages.
// The current hybrid handler sees no stock state or cursor.
pub open spec fn advances<X,E,Y,A>(stock:Path<X,E>,physical:Relation<Y,A>,done:Region<Y>,
    impls:Correspondence<X,E,Y,A>) -> Relation<(nat,Y),A> {
    |p:(nat,Y),a,u:(nat,Y)| {
        let i=p.0;let j=u.0;let x=stock.states[i as int];let y=p.1;let v=u.1;
        i<=stock.actions.len() && physical(y,a,v) && (
            (j==i && (done(v) || ((impls.represents)(x,v) && (impls.preparation)(x,v)<(impls.preparation)(x,y))))
            || (j==i+1 && i<stock.actions.len() && (impls.represents)(stock.states[j as int],v)
                && (impls.implements)(x,stock.actions[i as int],stock.states[j as int],y,a,v)))
    }
}
pub open spec fn offered<Y,A>(r:Relation<(nat,Y),A>,p:(nat,Y)) -> bool {
    exists|a:A,u:(nat,Y)| #[trigger] r(p,a,u)
}
pub open spec fn reached<Y,A>(r:Relation<(nat,Y),A>,t:Path<(nat,Y),A>,start:(nat,Y)) -> bool {
    t.states.len()==t.actions.len()+1 && t.states[0]==start && wait::valid_edges(r,t)
}
pub proof fn audit<X,E,Y,A>(s:Path<X,E>,physical:Relation<Y,A>,done:Region<Y>,impls:Correspondence<X,E,Y,A>,
    i:nat,y:Y) -> (t:Path<(nat,Y),A>)
    requires s.states.len()==s.actions.len()+1,i<=s.actions.len(),(impls.represents)(s.states[i as int],y),
    ensures ({
        let r=advances(s,physical,done,impls);let end=t.states.last();
        reached(r,t,(i,y)) && end.0<=s.actions.len() &&
            (done(end.1) || (impls.represents)(s.states[end.0 as int],end.1))
    }),
        done(t.states.last().1) || !offered(advances(s,physical,done,impls),t.states.last()),
    decreases s.actions.len()-i,(impls.preparation)(s.states[i as int],y),
{
    let r=advances(s,physical,done,impls);let p=(i,y);
    if done(y) || !offered(r,p) {Path{states:seq![p],actions:seq![]}}
    else {
        let (a,u)=choose|a:A,u:(nat,Y)| #[trigger] r(p,a,u);
        if done(u.1) {
            let t=Path{states:seq![p,u],actions:seq![a]};assert(wait::valid_edges(r,t));t
        } else {
            let rest=audit(s,physical,done,impls,u.0,u.1);
            let t=Path{states:seq![p]+rest.states,actions:seq![a]+rest.actions};
            assert forall|k:int| 0<=k<t.actions.len() implies r(t.states[k],#[trigger] t.actions[k],t.states[k+1]) by {
                if k>0 {assert(r(rest.states[k-1],rest.actions[k-1],rest.states[k]));}
            }
            assert(t.states.last()==rest.states.last());t
        }
    }
}
pub open spec fn actual<Y,A>(t:Path<(nat,Y),A>) -> Path<Y,A> {
    Path{states:Seq::new(t.states.len(),|k:int|t.states[k].1),actions:t.actions}
}
pub proof fn actual_edges<X,E,Y,A>(s:Path<X,E>,physical:Relation<Y,A>,done:Region<Y>,impls:Correspondence<X,E,Y,A>,
    t:Path<(nat,Y),A>,start:Y)
    requires reached(advances(s,physical,done,impls),t,(0nat,start)),
    ensures wait::valid_edges(physical,actual(t)),actual(t).states[0]==start,actual(t).states.last()==t.states.last().1,
{
    let r=advances(s,physical,done,impls);let path=actual(t);
    assert forall|k:int| 0<=k<t.actions.len() implies physical(path.states[k],#[trigger] path.actions[k],path.states[k+1])
        by {assert(r(t.states[k],t.actions[k],t.states[k+1]));}
}

pub open spec fn quorum_route<X,E>(p:stock::ReadSystem<X,E>,x:X,q:Set<Replica>,s:Path<X,E>,v:int) -> bool {
    stock::quorum_witness(p,x,q,s.states,s.actions,v)
}
// Selection is existential under A. More than one legal choice can exist.
pub proof fn route_from_a<X,E>(p:stock::ReadSystem<X,E>,x:X,q:Set<Replica>) -> (w:(Path<X,E>,int))
    requires stock::available_majorities(p),nb::stock_scope(p,q)(x),
    ensures quorum_route(p,x,q,w.0,w.1),
{
    let (s,a,v)=choose|s:Seq<X>,a:Seq<E>,v:int| #[trigger] stock::quorum_witness(p,x,q,s,a,v);
    (Path{states:s,actions:a},v)
}

pub open spec fn routed_call<S,X,E>(n:Notice,m:Program<S>,res:spec_fn(S)->Option<int>,s:Path<X,E>,
    t:Correspondence<X,E,Log,Event>) -> Relation<(nat,Log),Event> {
    let local=suffix_protocol(m,n);
    advances(s,call::step(local,res,delayed_slots()),call::posted(local,res),t)
}
pub open spec fn audit_outcome<S,X,E>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    s:Path<X,E>,impls:Correspondence<X,E,Log,Event>,t:Path<(nat,Log),Event>) -> bool {
    let net=checkpoint_end(alpha(n));let start=call::launch(net);let r=routed_call(n,m,res,s,impls);
    let end=t.states.last();let local=suffix_protocol(m,n);let ids=delayed_slots();
    reached(r,t,(0nat,start)) && call::consistent(local,res,net,ids,end.1) && end.1.actions==t.actions &&
        (contract::fork_conflict(n,m,first,res) || contract::necessarily_unlocked(n,local,res)
            || (!call::posted(local,res)(end.1) && end.0<=s.actions.len() && (impls.represents)(s.states[end.0 as int],end.1)
                && !offered(r,end)))
}

// For any served-by-Q stock witness, report the local failure on an actual
// accepted alpha prefix or obtain the two-run conclusion. No hypotheses on
// any fair hybrid reference, service guard, scheduler, or weak provenance.
pub proof fn check_route_at_originals<S,X,E>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    p:stock::ReadSystem<X,E>,x:X,q:Set<Replica>,s:Path<X,E>,v:int,impls:Correspondence<X,E,Log,Event>)
    -> (t:Path<(nat,Log),Event>)
    requires original_reads(n,m,first),quorum_route(p,x,q,s,v),(impls.represents)(x,call::launch(checkpoint_end(alpha(n)))),
    ensures audit_outcome(n,m,first,res,s,impls,t),
{
    hide(contract::fork_conflict);hide(contract::necessarily_unlocked);hide(original_reads);hide(call::step);hide(call::posted);
    let net=checkpoint_end(alpha(n));let start=call::launch(net);let local=suffix_protocol(m,n);let ids=delayed_slots();
    let r=call::step(local,res,ids);let done=call::posted(local,res);let t=audit(s,r,done,impls,0,start);
    let path=actual(t);actual_edges(s,r,done,impls,t,start);
    call::run_prefix(local,res,net,ids,path,path.actions.len());
    assert(path.actions.take(path.actions.len() as int) =~= t.actions);
    if done(t.states.last().1) {
        nb::from_path(r,done,path,0);contract::original_outcomes(n,m,first,res);
        if contract::trapped(local,res,net,ids) {
            let trap=choose|b:Region<Log>| #[trigger] nb::pending_trap(r,done,b) && b(start);
            nb::trap_excludes_service(r,done,trap,start);
        }
    }
    t
}

// A produces a real stock path and a held response on this very majority.
// The hybrid result and every audit action come from their own machine.
pub proof fn compare_with_stock_a<S,X,E>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    p:stock::ReadSystem<X,E>,x:X,q:Set<Replica>,impls:Correspondence<X,E,Log,Event>)
    -> (w:(Path<X,E>,int,Path<(nat,Log),Event>))
    requires original_reads(n,m,first),stock::available_majorities(p),nb::stock_scope(p,q)(x),
        (impls.represents)(x,call::launch(checkpoint_end(alpha(n)))),
    ensures quorum_route(p,x,q,w.0,w.1),audit_outcome(n,m,first,res,w.0,impls,w.2),
{
    let (s,v)=route_from_a(p,x,q);
    let t=check_route_at_originals(n,m,first,res,p,x,q,s,v,impls);
    (s,v,t)
}

// Independent optional local obligation. Only reached, pending cursor
// positions matter. Every candidate move must be an enabled physical edge.
pub open spec fn supported<Y,A>(edge:Relation<(nat,Y),A>,done:Region<Y>,start:Y) -> bool {
    forall|t:Path<(nat,Y),A>| #[trigger] reached(edge,t,(0nat,start)) && !done(t.states.last().1) ==> offered(edge,t.states.last())
}
pub proof fn pair_from_supported_route<S,X,E>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    p:stock::ReadSystem<X,E>,x:X,q:Set<Replica>,s:Path<X,E>,v:int,impls:Correspondence<X,E,Log,Event>)
    requires original_reads(n,m,first),quorum_route(p,x,q,s,v),(impls.represents)(x,call::launch(checkpoint_end(alpha(n)))),
        supported(routed_call(n,m,res,s,impls),call::posted(suffix_protocol(m,n),res),call::launch(checkpoint_end(alpha(n)))),
        contract::no_confirm_wait_at(m,res,contract::past(alpha(n)),delayed_slots(),Replica::R2),
    ensures contract::fork_conflict(n,m,first,res),
{
    let t=check_route_at_originals(n,m,first,res,p,x,q,s,v,impls);
    contract::no_wait_excludes_unlock(n,m,res);
}

}
