use vstd::prelude::*;

verus! {

pub type CommandSemantics = spec_fn(nat,int)->(int,int); // new state, return value

}
