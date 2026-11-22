use vstd::prelude::*;
use crate::Replica;
use crate::metadata_stock::*;
use crate::ordered_store::*;
use crate::quorum_rpc::{Resolver, latest};

verus! {

// A designated reference site can permit a cheaper unanimous-read check.
// Without that site, position zero is validated against the ordinary
// initial image. This remains an any-majority protocol on stock states.
pub open spec fn unanimous(m: Rows) -> bool {
    forall|i: Replica,j: Replica| #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) ==> m[i].value==m[j].value
}

pub open spec fn valid_root(m: Rows) -> bool {
    forall|r: Replica| #[trigger] m.contains_key(r) && m[r].version==0 ==> m[r].value==sample(initial_store(),r).value
}

pub open spec fn root_or_reference(reference: Replica, m: Rows) -> bool {
    (m.contains_key(reference) && unanimous(m)) || valid_root(m)
}

pub open spec fn reference_read(reference: Replica) -> Resolver {
    |m: Rows| if root_or_reference(reference,m) { latest(m) } else { None }
}

}
