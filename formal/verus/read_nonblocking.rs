// Nonblocking service and causal waiting for an arbitrary pending operation.
// The caller supplies a fixed workload, the actual transition relation and
// the observer of this operation (or an ordinary protocol milestone).
use vstd::prelude::*;
use crate::promotion_wait::{self as wait, Path, Relation};
use crate::stock_availability as stock;
use crate::Replica;
use crate::ordered_store::majority;

verus! {

// Predicates allow regions over unbounded queues and internal memories.
pub type Region<S> = spec_fn(S)->bool;
pub open spec fn disjoint<S>(b:Region<S>,c:Region<S>) -> bool {
    forall|x:S| #[trigger] b(x) ==> !c(x)
}

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
pub open spec fn ordinary<S,A>(step:Relation<S,A>, promotion:Relation<S,A>) -> Relation<S,A> {
    |x,a,y| step(x,a,y) && !promotion(x,a,y)
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

pub proof fn predecessor<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,x:S,a:A,y:S)
    requires step(x,a,y),possible(step,posted,y),
    ensures possible(step,posted,x),
{
    let n=choose|n:nat| #[trigger] within(step,posted,y,n);
    assert(within(step,posted,x,n+1));
}

// A trap is an inductive invariant, closed even under ordinary repairs,
// deliveries, timeouts and weak work if the step relation includes them.
pub open spec fn pending_trap<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,b:Region<S>) -> bool {
    (forall|x:S| #[trigger] b(x) ==> !posted(x)) &&
    (forall|x:S,a:A,y:S| b(x) && #[trigger] step(x,a,y) ==> b(y))
}
pub open spec fn nonblocking<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,eligible:Region<S>) -> bool {
    forall|b:Region<S>| #[trigger] pending_trap(step,posted,b) ==> disjoint(b,eligible)
}
pub open spec fn hopeless<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool) -> Region<S> {
    |x:S| !possible(step,posted,x)
}
pub proof fn largest_trap<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool)
    ensures pending_trap(step,posted,hopeless(step,posted)),
{
    let b=hopeless(step,posted);
    assert forall|x:S| #[trigger] b(x) implies !posted(x) by {if posted(x) {assert(within(step,posted,x,0));}}
    assert forall|x:S,a:A,y:S| b(x) && #[trigger] step(x,a,y) implies b(y) by {
        if possible(step,posted,y) {predecessor(step,posted,x,a,y);}
    }
}
proof fn excludes_layer<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,b:Region<S>,x:S,n:nat)
    requires pending_trap(step,posted,b),b(x),
    ensures !within(step,posted,x,n),
    decreases n,
{
    if within(step,posted,x,n) {
        let (a,y)=choose|a:A,y:S| #[trigger] step(x,a,y) && within(step,posted,y,(n-1) as nat);
        excludes_layer(step,posted,b,y,(n-1) as nat);
    }
}
pub proof fn trap_excludes_service<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,b:Region<S>,x:S)
    requires pending_trap(step,posted,b),b(x),
    ensures !possible(step,posted,x),
{
    if possible(step,posted,x) {excludes_layer(step,posted,b,x,choose|n:nat| #[trigger] within(step,posted,x,n));}
}
pub proof fn nonblocking_iff<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,eligible:Region<S>)
    ensures nonblocking(step,posted,eligible) == (forall|x:S| #[trigger] eligible(x) ==> possible(step,posted,x)),
{
    let lost=hopeless(step,posted); largest_trap(step,posted);
    if nonblocking(step,posted,eligible) {
        assert(disjoint(lost,eligible));
        assert forall|x:S| #[trigger] eligible(x) implies possible(step,posted,x) by {
            if !possible(step,posted,x) {assert(lost(x));assert(!eligible(x));}
        }
    }
    else {
        let b=choose|b:Region<S>| #[trigger] pending_trap(step,posted,b) && !disjoint(b,eligible);
        let x=choose|x:S| #[trigger] b(x) && eligible(x);
        trap_excludes_service(step,posted,b,x);
    }
}

// A strong read may use independently stabilized data. This clause only
// asks whether an actual audited transition made an ordinary milestone
// reachable that had previously been out of reach. posted(y) also counts
// if publication happens atomically with the promotion event.
pub open spec fn unlocks<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,promotion:Relation<S,A>,x:S,a:A,y:S) -> bool {
    let plain=ordinary(step,promotion);
    step(x,a,y) && promotion(x,a,y) && !possible(plain,posted,x) && possible(plain,posted,y)
}
pub open spec fn no_unlock<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,promotion:Relation<S,A>,scope:Region<S>) -> bool {
    forall|x:S,a:A,y:S| scope(x) ==> !#[trigger] unlocks(step,posted,promotion,x,a,y)
}
pub open spec fn stays_in_scope<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,scope:Region<S>) -> bool {
    forall|x:S,a:A,y:S| scope(x) && !posted(x) && #[trigger] step(x,a,y) && !posted(y) ==> scope(y)
}

// Any given successful real trace from an ordinary-blocked state contains
// a concrete causal edge. Subsequent ordinary service can take a different
// path than that trace and can return a different value.
pub proof fn find_unlock<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,promotion:Relation<S,A>,t:Path<S,A>,i:nat)
    -> (at:nat)
    requires t.states.len()==t.actions.len()+1,wait::valid_edges(step,t),i<t.states.len(),
        !possible(ordinary(step,promotion),posted,t.states[i as int]),posted(t.states.last()),
    ensures i<=at<t.actions.len(),unlocks(step,posted,promotion,t.states[at as int],t.actions[at as int],t.states[at as int+1]),
    decreases t.actions.len()-i,
{
    let plain=ordinary(step,promotion); let x=t.states[i as int];
    if i==t.actions.len() {assert(within(plain,posted,x,0));}
    let a=t.actions[i as int]; let y=t.states[i as int+1];
    assert(step(x,a,y));
    if possible(plain,posted,y) {
        if !promotion(x,a,y) {predecessor(plain,posted,x,a,y);}
        i
    } else {find_unlock(step,posted,promotion,t,i+1)}
}

proof fn scope_at<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,t:Path<S,A>,scope:Region<S>,i:nat)
    requires stays_in_scope(step,posted,scope),scope(t.states[0]),i<t.actions.len(),
        wait::valid_edges(step,t),wait::pending_before(posted,t),
    ensures scope(t.states[i as int]),
    decreases i,
{
    if i>0 {let k=(i-1) as nat; scope_at(step,posted,t,scope,k);assert(step(t.states[k as int],t.actions[k as int],t.states[i as int]));}
}
pub proof fn unlocks_require_service<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,promotion:Relation<S,A>,x:S,a:A,y:S)
    requires unlocks(step,posted,promotion,x,a,y),
    ensures possible(step,posted,x),
{
    let r=ordinary(step,promotion);
    let t=to_path(r,posted,y,choose|n:nat| #[trigger] within(r,posted,y,n));
    assert forall|i:int| 0<=i<t.actions.len() implies step(t.states[i],#[trigger] t.actions[i],t.states[i+1]) by {
        assert(r(t.states[i],t.actions[i],t.states[i+1]));
    }
    from_path(step,posted,t,0);predecessor(step,posted,x,a,y);
}
pub proof fn omission_iff_no_unlock<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,promotion:Relation<S,A>,scope:Region<S>)
    requires stays_in_scope(step,posted,scope),
    ensures no_unlock(step,posted,promotion,scope) == wait::no_await(step,posted,|x:S|scope(x),promotion),
{
    let plain=ordinary(step,promotion);
    let admitted=|x:S|scope(x);
    if !wait::no_await(step,posted,admitted,promotion) {
        let x=choose|x:S| #[trigger] admitted(x) && wait::needs_class(step,posted,x,promotion);
        if possible(plain,posted,x) {
            let t=to_path(plain,posted,x,choose|n:nat| #[trigger] within(plain,posted,x,n));
            assert forall|i:int| 0<=i<t.actions.len() implies step(t.states[i],#[trigger] t.actions[i],t.states[i+1])
                && !promotion(t.states[i],t.actions[i],t.states[i+1]) by {assert(plain(t.states[i],t.actions[i],t.states[i+1]));}
            let witness=choose|p:Path<S,A>| #[trigger] wait::first_return(step,posted,x,p);
            assert(!posted(x));
            assert(!posted(x) && wait::first_return(step,posted,x,t) && !wait::uses(t,promotion));
        }
        let t=choose|t:Path<S,A>| #[trigger] wait::first_return(step,posted,x,t);
        let i=find_unlock(step,posted,promotion,t,0);scope_at(step,posted,t,scope,i);
        assert(unlocks(step,posted,promotion,t.states[i as int],t.actions[i as int],t.states[i as int+1]));
    } else if !no_unlock(step,posted,promotion,scope) {
        let (x,a,y)=choose|x:S,a:A,y:S| scope(x) && #[trigger] unlocks(step,posted,promotion,x,a,y);
        unlocks_require_service(step,posted,promotion,x,a,y); first_response_iff(step,posted,x);
        if posted(x) {assert(within(plain,posted,x,0));}
        let t=choose|t:Path<S,A>| #[trigger] wait::first_return(step,posted,x,t);
        let w=wait::extract_without_promotion(step,posted,admitted,promotion,x,t);
        assert forall|i:int| 0<=i<w.actions.len() implies plain(w.states[i],#[trigger] w.actions[i],w.states[i+1])
            by {assert(step(w.states[i],w.actions[i],w.states[i+1]));}
        from_path(plain,posted,w,0);
    }
}

pub proof fn ordinary_option_at<S,A>(step:Relation<S,A>,posted:Region<S>,promotion:Relation<S,A>,scope:Region<S>,x:S)
    requires stays_in_scope(step,posted,scope),no_unlock(step,posted,promotion,scope),scope(x),possible(step,posted,x),
    ensures possible(ordinary(step,promotion),posted,x),
{
    let plain=ordinary(step,promotion);
    if !possible(plain,posted,x) {
        if posted(x) {assert(within(plain,posted,x,0));}
        first_response_iff(step,posted,x);
        let t=choose|t:Path<S,A>| #[trigger] wait::first_return(step,posted,x,t);
        let i=find_unlock(step,posted,promotion,t,0);scope_at(step,posted,t,scope,i);
        assert(unlocks(step,posted,promotion,t.states[i as int],t.actions[i as int],t.states[i as int+1]));
    }
}

// The positive availability clause and the no-await clause have distinct
// content. Together they are exactly nonblockingness after suppressing the
// audited effects, on a workload closed through the pending operation.
pub proof fn factor_service<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,promotion:Relation<S,A>,scope:Region<S>)
    requires stays_in_scope(step,posted,scope),
    ensures nonblocking(ordinary(step,promotion),posted,scope)
        == (nonblocking(step,posted,scope) && no_unlock(step,posted,promotion,scope)),
{
    let r=ordinary(step,promotion);
    nonblocking_iff(r,posted,scope);nonblocking_iff(step,posted,scope);
    if nonblocking(r,posted,scope) {
        assert forall|x:S| #[trigger] scope(x) implies possible(step,posted,x) by {
            let t=to_path(r,posted,x,choose|n:nat| #[trigger] within(r,posted,x,n));
            assert forall|i:int| 0<=i<t.actions.len() implies step(t.states[i],#[trigger] t.actions[i],t.states[i+1])
                by {assert(r(t.states[i],t.actions[i],t.states[i+1]));}
            from_path(step,posted,t,0);
        }
        assert forall|x:S,a:A,y:S| scope(x) implies !#[trigger] unlocks(step,posted,promotion,x,a,y)
            by {assert(possible(r,posted,x));}
    } else if nonblocking(step,posted,scope) && no_unlock(step,posted,promotion,scope) {
        assert forall|x:S| #[trigger] scope(x) implies possible(r,posted,x) by {
            ordinary_option_at(step,posted,promotion,scope,x);
        }
    }
}

// A real ordinary prefix may update logs, clocks, message counters or
// strong control. If it can get to a serviceable state on its own, a
// coincident weak signal cannot be indispensable on that account.
pub proof fn detour_preserves_service<S,A>(step:Relation<S,A>,posted:Region<S>,t:Path<S,A>,i:nat)
    requires t.states.len()==t.actions.len()+1,wait::valid_edges(step,t),i<=t.actions.len(),
        possible(step,posted,t.states.last()),
    ensures possible(step,posted,t.states[i as int]),
    decreases t.actions.len()-i,
{
    if i<t.actions.len() {
        detour_preserves_service(step,posted,t,i+1);
        assert(step(t.states[i as int],t.actions[i as int],t.states[i as int+1]));
        predecessor(step,posted,t.states[i as int],t.actions[i as int],t.states[i as int+1]);
    }
}
// If a protocol genuinely exposes delivery/ordinary handling and acquiring
// the promotion information as separate transitions, charge the latter
// exactly when it supplies the missing capability. Both the prefix and the
// evidence step must exist in the protocol.
pub proof fn ordinary_part_of_receipt<S,A>(step:Relation<S,A>,posted:Region<S>,promotion:Relation<S,A>,
    before:Path<S,A>,b:A,y:S)
    requires before.states.len()==before.actions.len()+1,wait::valid_edges(ordinary(step,promotion),before),
        step(before.states.last(),b,y),promotion(before.states.last(),b,y),
    ensures ({
        let plain=ordinary(step,promotion);let x=before.states[0];let z=before.states.last();
        (possible(plain,posted,z) ==> possible(plain,posted,x)) &&
        ((!possible(plain,posted,x) && possible(plain,posted,y)) ==> unlocks(step,posted,promotion,z,b,y))
    }),
{
    let r=ordinary(step,promotion);
    if possible(r,posted,before.states.last()) {detour_preserves_service(r,posted,before,0);}
}

// Operation safety is independent of readiness. On a forward-closed set
// where every actual publication is legal, adding the legality check to
// the observer leaves both the reachability layers and unlocks unchanged.
pub open spec fn sound_publications<S,A>(step:Relation<S,A>,posted:Region<S>,legal:Region<S>,domain:Region<S>) -> bool {
    (forall|x:S| #[trigger] domain(x) && posted(x) ==> legal(x)) &&
    (forall|x:S,a:A,y:S| domain(x) && #[trigger] step(x,a,y) ==> domain(y))
}
proof fn safe_layer<S,A>(step:Relation<S,A>,posted:Region<S>,legal:Region<S>,domain:Region<S>,x:S,k:nat)
    requires sound_publications(step,posted,legal,domain),domain(x),
    ensures within(step,posted,x,k)==within(step,|y:S|posted(y) && legal(y),x,k),
    decreases k,
{
    let safe=|y:S|posted(y) && legal(y);
    if k>0 && !posted(x) {
        if within(step,posted,x,k) {
            let (a,y)=choose|a:A,y:S| #[trigger] step(x,a,y) && within(step,posted,y,(k-1) as nat);
            safe_layer(step,posted,legal,domain,y,(k-1) as nat);
        } else if within(step,safe,x,k) {
            let (a,y)=choose|a:A,y:S| #[trigger] step(x,a,y) && within(step,safe,y,(k-1) as nat);
            safe_layer(step,posted,legal,domain,y,(k-1) as nat);
        }
    }
}
pub proof fn waiting_for_a_legal_result<S,A>(step:Relation<S,A>,posted:Region<S>,legal:Region<S>,domain:Region<S>,
    promotion:Relation<S,A>,x:S,a:A,y:S)
    requires sound_publications(step,posted,legal,domain),domain(x),step(x,a,y),
    ensures unlocks(step,posted,promotion,x,a,y)==unlocks(step,|z:S|posted(z) && legal(z),promotion,x,a,y),
{
    let r=ordinary(step,promotion);let safe=|z:S|posted(z) && legal(z);
    assert forall|s:S,e:A,u:S| domain(s) && #[trigger] r(s,e,u) implies domain(u) by {assert(step(s,e,u));}
    assert(sound_publications(r,posted,legal,domain));
    assert forall|s:S,k:nat| domain(s) implies
        #[trigger] within(r,posted,s,k)==#[trigger] within(r,safe,s,k) by {safe_layer(r,posted,legal,domain,s,k);}
    assert forall|s:S| #[trigger] domain(s) implies possible(r,posted,s)==possible(r,safe,s) by {
        if possible(r,posted,s) {
            let k=choose|k:nat| #[trigger] within(r,posted,s,k);safe_layer(r,posted,legal,domain,s,k);
        } else if possible(r,safe,s) {
            let k=choose|k:nat| #[trigger] within(r,safe,s,k);safe_layer(r,posted,legal,domain,s,k);
        }
    }
    assert(domain(y));
}

pub open spec fn stock_scope<X,E>(p:stock::ReadSystem<X,E>,q:Set<Replica>) -> Region<X> {
    |x:X| stock::reaches(p,x) && (p.invoked)(x) && (p.response)(x).is_none() &&
        (p.client_live)(x) && majority(q) && q.subset_of((p.up)(x))
}
pub open spec fn live_stock_step<X,E>(p:stock::ReadSystem<X,E>,q:Set<Replica>) -> Relation<X,E> {
    |x,a,y| (p.next)(x,a,y) && (p.client_live)(y) && q.subset_of((p.up)(y))
}
pub proof fn from_stock_a<X,E>(p:stock::ReadSystem<X,E>,q:Set<Replica>)
    requires stock::available_majorities(p),
    ensures nonblocking(live_stock_step(p,q),|x:X|(p.response)(x).is_some(),stock_scope(p,q)),
{
    let step=live_stock_step(p,q);let done=|x:X|(p.response)(x).is_some();let scope=stock_scope(p,q);
    nonblocking_iff(step,done,scope);
    assert forall|x:X| #[trigger] scope(x) implies possible(step,done,x) by {
        assert(stock::reaches(p,x) && majority(q));
        let (s,a,v)=choose|s:Seq<X>,a:Seq<E>,v:int| #[trigger] stock::quorum_witness(p,x,q,s,a,v);
        let t=Path{states:s,actions:a};
        assert forall|i:int| 0<=i<a.len() implies step(s[i],#[trigger] a[i],s[i+1])
            by {assert((p.next)(s[i],a[i],s[i+1]) && (p.client_live)(s[i+1]) && q.subset_of((p.up)(s[i+1])));}
        from_path(step,done,t,0);
    }
}

}
