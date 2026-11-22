use vstd::prelude::*;
use crate::{Op, Replica};

verus! {

// G records membership in the total order and replication of the
// operation. It does not say which replica encodes the order position.
pub open spec fn ordered_on_majority(order: Seq<Op>, copies: Set<Replica>, w: Op) -> bool {
    order.contains(w) && copies.len() >= 2
}

}
