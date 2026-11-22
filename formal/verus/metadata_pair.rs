use vstd::prelude::*;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::ordered_store::Stamp;

// One physical request and sampled reply per selected site. The header
// in the *issued packet* is the number of locally applied ordinary
// commands. C2 has no access to the sender's later state.
verus! {

pub open spec fn replica_answer(p: Packet<Wire>) -> bool {
    p.from is At && p.to == Process::SecondClient && p.path == Path::Strong && p.input is StampedAnswer
}

pub open spec fn signed_row(p: Packet<Wire>) -> Stamp {
    Stamp { value: p.input->StampedAnswer_0.value, version: p.input->StampedAnswer_1 }
}

}
