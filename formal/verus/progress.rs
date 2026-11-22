use vstd::prelude::*;
use crate::delivery::*;

verus! {

#[verifier::reject_recursive_types(L)]
#[verifier::reject_recursive_types(I)]
pub struct Execution<L, I> {
    pub state: spec_fn(nat) -> Network<L, I>,
    pub action: spec_fn(nat) -> Action<I>,
}

// An issued packet cannot be postponed forever while its recipient
// remains live. This is tested on the reference execution only.
pub open spec fn delivery_fair<L, I>(e: Execution<L, I>) -> bool {
    forall|i: nat, id: nat| #[trigger] (e.state)(i).pending.contains_key(id)
        ==> exists|j: nat| j >= i && (#[trigger] (e.action)(j) == Action::Deliver(id)
            || !live((e.state)(j), (e.state)(i).pending[id].to))
}

pub open spec fn continuously_runnable<L, I>(
    e: Execution<L, I>, runnable: spec_fn(Network<L, I>, Process) -> bool,
    from: nat, p: Process,
) -> bool {
    forall|i: nat| i >= from ==> #[trigger] runnable((e.state)(i), p)
}

pub open spec fn runs_at<L, I>(e: Execution<L, I>, j: nat, p: Process) -> bool {
    process_step((e.state)(j), (e.action)(j)).actor == p
}

pub open spec fn process_fair<L, I>(
    e: Execution<L, I>, runnable: spec_fn(Network<L, I>, Process) -> bool,
) -> bool {
    forall|from: nat, p: Process| #[trigger] continuously_runnable(e, runnable, from, p)
        ==> exists|j: nat| j >= from && #[trigger] runs_at(e, j, p)
}

}
