// Local obligations for a finite service opportunity. An implementation may
// certify any one enabled choice; other choices may stall or change values.
use vstd::prelude::*;
use crate::promotion_wait::Relation;
use crate::read_nonblocking::{self as nb,Region};

verus! {

#[verifier::reject_recursive_types(S)]
pub struct Rank<S> {
    pub domain: Region<S>,
    pub distance: spec_fn(S)->nat,
}
pub open spec fn covers<S>(eligible:Region<S>,posted:Region<S>,rank:Rank<S>) -> bool {
    forall|x:S| #[trigger] eligible(x) && !posted(x) ==> (rank.domain)(x)
}
pub open spec fn exit<S,A>(step:Relation<S,A>,posted:Region<S>,rank:Rank<S>,x:S) -> bool {
    exists|a:A,y:S| #[trigger] step(x,a,y) && (posted(y) ||
        ((rank.domain)(y) && (rank.distance)(y)<(rank.distance)(x)))
}
pub open spec fn valid<S,A>(step:Relation<S,A>,posted:Region<S>,rank:Rank<S>) -> bool {
    forall|x:S| #[trigger] (rank.domain)(x) && !posted(x) ==> exit(step,posted,rank,x)
}
pub proof fn schedule_exit<S,A>(step:Relation<S,A>,posted:Region<S>,rank:Rank<S>,x:S)
    requires valid(step,posted,rank),posted(x) || (rank.domain)(x),
    ensures nb::possible(step,posted,x),
    decreases (rank.distance)(x),
{
    if posted(x) {assert(nb::within(step,posted,x,0));}
    else {
        assert(exit(step,posted,rank,x));
        let (a,y)=choose|a:A,y:S| #[trigger] step(x,a,y) && (posted(y) ||
            ((rank.domain)(y) && (rank.distance)(y)<(rank.distance)(x)));
        if posted(y) {assert(nb::within(step,posted,y,0));} else {schedule_exit(step,posted,rank,y);}
        nb::predecessor(step,posted,x,a,y);
    }
}
pub proof fn certificate_yields_service<S,A>(step:Relation<S,A>,posted:Region<S>,eligible:Region<S>,rank:Rank<S>)
    requires valid(step,posted,rank),covers(eligible,posted,rank),
    ensures nb::nonblocking(step,posted,eligible),
{
    nb::nonblocking_iff(step,posted,eligible);
    assert forall|x:S| #[trigger] eligible(x) implies nb::possible(step,posted,x) by {schedule_exit(step,posted,rank,x);}
}

pub open spec fn shortest<S,A>(step:Relation<S,A>,posted:Region<S>,x:S,k:nat) -> bool {
    nb::within(step,posted,x,k) && forall|j:nat| j<k ==> !#[trigger] nb::within(step,posted,x,j)
}
pub open spec fn canonical<S,A>(step:Relation<S,A>,posted:Region<S>) -> Rank<S> {
    Rank{domain:|x:S|nb::possible(step,posted,x),
        distance:|x:S|choose|k:nat| #[trigger] shortest(step,posted,x,k)}
}
proof fn minimum_length<S,A>(step:Relation<S,A>,posted:Region<S>,x:S)
    requires nb::possible(step,posted,x),
    ensures shortest(step,posted,x,(canonical(step,posted).distance)(x)),
{
    let k=choose|k:nat| #[trigger] nb::within(step,posted,x,k);
    let pred=|j:nat| nb::within(step,posted,x,j);
    let first=crate::confirmation::first_true(pred,k);
    assert forall|j:nat| j<first implies !#[trigger] nb::within(step,posted,x,j) by {assert(!pred(j));}
    assert(shortest(step,posted,x,first));
}
pub proof fn canonical_is_valid<S,A>(step:Relation<S,A>,posted:Region<S>)
    ensures valid(step,posted,canonical(step,posted)),
{
    let rank=canonical(step,posted);
    assert forall|x:S| #[trigger] (rank.domain)(x) && !posted(x) implies exit(step,posted,rank,x) by {
        minimum_length(step,posted,x);let k=(rank.distance)(x);
        assert(nb::within(step,posted,x,k));assert(k>0);
        let (a,y)=choose|a:A,y:S| #[trigger] step(x,a,y) && nb::within(step,posted,y,(k-1) as nat);
        minimum_length(step,posted,y);
        if (rank.distance)(y)>k-1 {assert(!nb::within(step,posted,y,(k-1) as nat));}
        assert((rank.domain)(y) && (rank.distance)(y)<k);
    }
}

// Exact for finite opportunity. The canonical example uses a shortest path;
// a runtime protocol need neither know this distance nor implement this proof.
pub proof fn exact_local_condition<S,A>(step:Relation<S,A>,posted:Region<S>,eligible:Region<S>)
    ensures nb::nonblocking(step,posted,eligible) ==
        (exists|rank:Rank<S>| #[trigger] valid(step,posted,rank) && covers(eligible,posted,rank)),
{
    if nb::nonblocking(step,posted,eligible) {
        let rank=canonical(step,posted);canonical_is_valid(step,posted);nb::nonblocking_iff(step,posted,eligible);
        assert(covers(eligible,posted,rank));
    } else if exists|rank:Rank<S>| #[trigger] valid(step,posted,rank) && covers(eligible,posted,rank) {
        let rank=choose|rank:Rank<S>| #[trigger] valid(step,posted,rank) && covers(eligible,posted,rank);
        certificate_yields_service(step,posted,eligible,rank);
    }
}

}
