use vstd::prelude::*;
use crate::delivery::*;
use crate::read_call::Program;
use crate::read_issue as issue;

verus! {

pub open spec fn startup<S>(m:Program<S>) -> bool {
    (m.accept)((m.initial)(Process::SecondClient),issue::local_event(Action::StartSecondClient))
}

}
