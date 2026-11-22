use vstd::prelude::*;
use crate::delivery::*;
use crate::read_call::Event;

verus! {

pub open spec fn wake() -> Seq<Event> {seq![Action::StopFirstClient,Action::CrashR3,Action::StartSecondClient]}

}
