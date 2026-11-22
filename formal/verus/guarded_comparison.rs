use vstd::prelude::*;
use crate::delivery::*;
use crate::first_splice::Observation;

verus! {

// SR2 starts after its invocation. Protect the three original weak slots.
// Every other ordinary packet is offered to the real handler. After its
// own first return an arm stops taking proposals.
pub open spec fn weak_work(e:Observation) -> bool {
    match e.action {
        Action::Send(_,q) => q.path==Path::Weak,
        Action::Deliver(_) => e.incoming.is_some() && e.incoming.unwrap().path==Path::Weak,
        Action::Local(_,w) | Action::ClientInput(_,w) => w is Copy || w is WeakConfirm,
        _ => false,
    }
}
}
