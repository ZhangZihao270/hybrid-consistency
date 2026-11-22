use vstd::prelude::*;
use crate::Replica;

verus! {

// These are ordinary command invocations in the comparison SMR. Each
// returns the old register and installs the new one. Distinct log entries
// denote distinct invocations, including entries with the same command.
pub enum Command { Increment, TimesFive }

pub open spec fn majority(q: Set<Replica>) -> bool {
    (q.contains(Replica::R1) && q.contains(Replica::R2))
        || (q.contains(Replica::R1) && q.contains(Replica::R3))
        || (q.contains(Replica::R2) && q.contains(Replica::R3))
}

pub struct Disk {
    pub known: nat, // Available decided entries, including unapplied ones
    pub applied: nat, // Position actually installed in the shared register
    pub value: int,
}

pub struct LogPacket { pub from: Replica, pub to: Replica, pub entries: Seq<Command> }

pub struct Store {
    pub log: Seq<Command>,
    pub disk: spec_fn(Replica) -> Disk,
    pub pending: Map<nat, LogPacket>,
}

pub open spec fn initial_store() -> Store {
    Store { log: Seq::empty(), disk: |r| Disk { known: 0, applied: 0, value: 1 }, pending: Map::empty() }
}

pub struct Stamp { pub version: nat, pub value: int }

pub open spec fn sample(s: Store, r: Replica) -> Stamp {
    Stamp { version: (s.disk)(r).applied, value: (s.disk)(r).value }
}

}
