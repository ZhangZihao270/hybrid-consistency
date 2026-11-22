// Nonblocking service and causal waiting for an arbitrary pending operation.
// The caller supplies a fixed workload, the actual transition relation and
// the observer of this operation (or an ordinary protocol milestone).
use vstd::prelude::*;
use crate::promotion_wait::{self as wait, Path, Relation};

verus! {

// Predicates allow regions over unbounded queues and internal memories.
pub type Region<S> = spec_fn(S)->bool;

// Backward reachability using only real transitions. There is no finite
// state bound. A different public result may be reached on every path.
pub open spec fn within<S,A>(step:Relation<S,A>, posted:spec_fn(S)->bool, x:S, n:nat) -> bool
    decreases n,
{
    posted(x) || (n>0 && exists|a:A,y:S| #[trigger] step(x,a,y) && within(step,posted,y,(n-1) as nat))
}
pub open spec fn possible<S,A>(step:Relation<S,A>, posted:spec_fn(S)->bool, x:S) -> bool {
    exists|n:nat| #[trigger] within(step,posted,x,n)
}

pub proof fn from_path<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,t:Path<S,A>,i:nat)
    requires t.states.len()==t.actions.len()+1,wait::valid_edges(step,t),posted(t.states.last()),i<=t.actions.len(),
    ensures within(step,posted,t.states[i as int],(t.actions.len()-i) as nat),
    decreases t.actions.len()-i,
{
    if i<t.actions.len() {
        from_path(step,posted,t,i+1);
        assert(step(t.states[i as int],t.actions[i as int],t.states[i as int+1]));
    }
}

pub proof fn to_path<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,x:S,n:nat) -> (t:Path<S,A>)
    requires within(step,posted,x,n),
    ensures t.states.len()==t.actions.len()+1,t.states[0]==x,t.actions.len()<=n,
        wait::valid_edges(step,t),wait::pending_before(posted,t),posted(t.states.last()),
        !posted(x) ==> wait::first_return(step,posted,x,t),
    decreases n,
{
    if posted(x) {Path{states:seq![x],actions:Seq::empty()}} else {
        let (a,y)=choose|a:A,y:S| #[trigger] step(x,a,y) && within(step,posted,y,(n-1) as nat);
        let rest=to_path(step,posted,y,(n-1) as nat);
        let t=Path{states:seq![x]+rest.states,actions:seq![a]+rest.actions};
        assert forall|i:int| 0<=i<t.actions.len() implies step(t.states[i],#[trigger] t.actions[i],t.states[i+1]) by {
            if i>0 {assert(step(rest.states[i-1],rest.actions[i-1],rest.states[i]));}
        }
        assert forall|i:int| 0<=i<t.actions.len() implies !posted(#[trigger] t.states[i]) by {
            if i>0 {assert(!posted(rest.states[i-1]));}
        }
        t
    }
}
pub proof fn first_response_iff<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,x:S)
    ensures possible(step,posted,x)==(posted(x)||wait::can_finish(step,posted,x)),
{
    if posted(x) {assert(within(step,posted,x,0));}
    else if possible(step,posted,x) {
        let t=to_path(step,posted,x,choose|n:nat| #[trigger] within(step,posted,x,n));
        assert(wait::first_return(step,posted,x,t));
    } else if wait::can_finish(step,posted,x) {
        let t=choose|t:Path<S,A>| #[trigger] wait::first_return(step,posted,x,t);
        from_path(step,posted,t,0);
    }
}

}
