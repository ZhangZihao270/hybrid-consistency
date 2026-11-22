use vstd::prelude::*;

verus! {

// A service test for a pending operation with a fixed external workload.
// The transition relation includes the protocol's guards and transport.
// The designated class can be supplied by a data-installation or evidence
// audit. The rule concerns finite opportunity, not the returned value.
pub type Relation<S,A> = spec_fn(S,A,S)->bool;
pub struct Path<S,A> { pub states: Seq<S>, pub actions: Seq<A> }

pub open spec fn valid_edges<S,A>(step:Relation<S,A>,path:Path<S,A>) -> bool {
    forall|i:int| 0<=i<path.actions.len() ==> step(path.states[i],#[trigger] path.actions[i],path.states[i+1])
}
pub open spec fn pending_before<S,A>(done:spec_fn(S)->bool,path:Path<S,A>) -> bool {
    forall|i:int| 0<=i<path.actions.len() ==> !done(#[trigger] path.states[i])
}
pub open spec fn first_return<S,A>(step: Relation<S,A>, done: spec_fn(S)->bool, start:S, path:Path<S,A>) -> bool {
    path.states.len()==path.actions.len()+1 && path.states[0]==start && !done(start) && done(path.states.last())
        && valid_edges(step,path) && pending_before(done,path)
}

pub open spec fn uses<S,A>(path:Path<S,A>, effect:Relation<S,A>) -> bool {
    exists|i:int| 0<=i<path.actions.len() && effect(path.states[i],#[trigger] path.actions[i],path.states[i+1])
}


pub open spec fn can_finish<S,A>(step:Relation<S,A>,done:spec_fn(S)->bool,start:S) -> bool {
    exists|p:Path<S,A>| #[trigger] first_return(step,done,start,p)
}

pub open spec fn needs_class<S,A>(step:Relation<S,A>,done:spec_fn(S)->bool,start:S,effect:Relation<S,A>) -> bool {
    can_finish(step,done,start) && forall|p:Path<S,A>| #[trigger] first_return(step,done,start,p) ==> uses(p,effect)
}

}
