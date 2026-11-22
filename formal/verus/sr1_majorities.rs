use vstd::prelude::*;
use crate::{Branch,Replica,checkpoint::*};

verus! {

pub open spec fn missing(b:Fork) -> Replica {
    if b.branch==Branch::Alpha {Replica::R1} else {Replica::R2}
}

}
