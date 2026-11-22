use vstd::prelude::*;
use crate::Replica;
use crate::ordered_store::*;

verus! {

pub type Rows = Map<Replica, Stamp>;

}
