use vstd::prelude::*;
use crate::delivery::*;

verus! {

pub open spec fn fresh_send<I>(a: Action<I>, reserved: Set<nat>) -> bool {
    match a { Action::Send(id, _) => !reserved.contains(id), _ => true }
}

}
