use vstd::prelude::*;
use crate::delivery::*;

verus! {

pub open spec fn after_crash<L, I>(s: Network<L, I>) -> bool {
    s.r3_crashed && s.first_stopped && s.second_started && s.unavailable.is_none()
}

}
