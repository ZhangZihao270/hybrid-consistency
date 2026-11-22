use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;

verus! {

// An independent order currently places preferred after the rival, or
// includes preferred while omitting the rival. A particular order need
// not impose any preference between these two versions.
pub open spec fn has_precedence<V>(order: Seq<V>, preferred: V, rival: V) -> bool {
    preferred != rival && exists|i: int| 0 <= i < order.len() && #[trigger] order[i] == preferred
        && (forall|j: int| i < j < order.len() ==> #[trigger] order[j] != rival)
}

pub struct IndependentView {
    pub cells: (int, int),
    pub left: Control,
    pub right: Control,
}

pub open spec fn independent_view(b: Fork) -> IndependentView {
    IndependentView {
        cells: survivor(checkpoint_end(b)),
        left: checkpoint_control(b, at(Replica::R1)),
        right: checkpoint_control(b, at(Replica::R2)),
    }
}

}
