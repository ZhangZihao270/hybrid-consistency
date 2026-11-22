use vstd::prelude::*;
use crate::Op;

verus! {

pub open spec fn legal_returns(v:int,w:int) -> bool {
    exists|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,v,w)
}
}
