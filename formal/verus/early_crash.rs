// A liveness probe for the direct SR1 prefixes. Only alpha and beta enter
// the history contradiction. In the probe C1 stays live and C2 starts
// independently. Receipt at C1 stays private. Each issued packet
// remains queued until an actual delivery.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::independent_read::{self as independent, State};
use crate::ordinary_service::Configuration;
use crate::read_call::{Event, Program};
use crate::read_issue::{send_first, send_second};

verus! {

pub open spec fn actions() -> Seq<Event> {
    let c=Process::FirstClient;
    seq![send(3,Path::Strong,c,at(Replica::R1),Wire::Request),
         send(4,Path::Strong,c,at(Replica::R2),Wire::Request),
         send(5,Path::Strong,c,at(Replica::R3),Wire::Request),
         Action::Deliver(3),Action::Deliver(4),
         send(6,Path::FirstReadReply,at(Replica::R1),c,Wire::Reply(2)),
         send(7,Path::FirstReadReply,at(Replica::R2),c,Wire::Reply(5)),
         Action::CrashR3, Action::StartSecondClient, send_first(),send_second()]
}
// Two in-flight weak offers to R3. Envelope 2 belongs to R3 even in
// executions where R3 dies before using it. No live sender needs that name.
pub open spec fn entry<S>(m:Program<S>) -> State<S> {
    State {calls:independent::Calls{first:all_replicas(),second:live_pair()},owners:Map::empty().insert(2nat,at(Replica::R3)),first_requested:Set::empty(),
        cfg:Configuration{net:after_local_rmws(),private:m.initial},reserved:Set::empty(),requested:Set::empty()}
}

}
