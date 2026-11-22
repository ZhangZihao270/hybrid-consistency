use vstd::prelude::*;
use crate::delivery::*;
use crate::independent_read::State;

verus! {

pub open spec fn caller2<S>(x:State<S>) -> S {(x.cfg.private)(Process::SecondClient)}

}
