use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;

verus! {

pub open spec fn query_packet(r: Replica) -> Packet<Wire> {
    Packet { path: Path::Strong, from: Process::SecondClient, to: at(r), input: Wire::Query2 }
}

}
