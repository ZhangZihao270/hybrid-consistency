// Independent C2's local send opportunity, before any reply. No premise
// concerning either survivor's read/repair guard or protocol state.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::read_call::Event;

verus! {

pub open spec fn send_first() -> Event { Action::Send(11,crate::sr2::query_packet(Replica::R1)) }
pub open spec fn send_second() -> Event { Action::Send(12,crate::sr2::query_packet(Replica::R2)) }
pub open spec fn local_event(a:Event) -> ProcessStep<int,Wire> {
    ProcessStep{actor:Process::SecondClient,action:a,incoming:None,own_local:None}
}
}
