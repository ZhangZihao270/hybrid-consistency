use vstd::prelude::*;
use crate::Replica;

verus! {

pub enum Process {
    At(Replica),
    FirstClient,
    SecondClient,
}

pub enum Path { Weak, FirstReadReply, Strong }

pub struct Packet<I> {
    pub path: Path,
    pub from: Process,
    pub to: Process,
    pub input: I,
}

pub enum Action<I> {
    Local(Replica, I),
    Send(nat, Packet<I>),
    Deliver(nat),
    Strong(Process),
    ClientInput(Process, I),
    StopFirstClient,
    CrashR3,
    StartSecondClient,
}

pub struct Network<L, I> {
    pub locals: spec_fn(Replica) -> L,
    pub pending: Map<nat, Packet<I>>,
    pub first_stopped: bool,
    pub r3_crashed: bool,
    pub second_started: bool,
    pub unavailable: Option<Replica>,
}

pub open spec fn live<L, I>(s: Network<L, I>, p: Process) -> bool {
    match p {
        Process::At(r) => s.unavailable != Some(r) && (r != Replica::R3 || !s.r3_crashed),
        Process::FirstClient => !s.first_stopped,
        Process::SecondClient => s.second_started,
    }
}

pub open spec fn outside_replica(p: Process) -> bool {
    p == Process::FirstClient || p == Process::SecondClient
}

pub open spec fn enabled<L, I>(s: Network<L, I>, a: Action<I>) -> bool {
    match a {
        Action::Send(id, packet) => !s.pending.contains_key(id) && live(s, packet.from)
            && (packet.path != Path::FirstReadReply || packet.to == Process::FirstClient),
        Action::Deliver(id) => s.pending.contains_key(id) && live(s, s.pending[id].to),
        Action::Local(r, _) => live(s, Process::At(r)),
        Action::Strong(p) => live(s, p),
        Action::ClientInput(p, _) => outside_replica(p) && live(s, p),
        Action::StopFirstClient => !s.first_stopped,
        Action::CrashR3 => live(s, Process::At(Replica::R3)),
        Action::StartSecondClient => s.first_stopped && s.r3_crashed && !s.second_started,
    }
}

pub open spec fn local_input<L, I>(s: Network<L, I>, a: Action<I>, r: Replica) -> Option<I> {
    match a {
        Action::Local(at, input) if at == r => Some(input),
        Action::Deliver(id) if s.pending.contains_key(id) && s.pending[id].to == Process::At(r)
            && s.pending[id].path == Path::Weak =>
            Some(s.pending[id].input),
        _ => None,
    }
}

pub open spec fn advance<L, I>(
    update: spec_fn(L, I) -> L, s: Network<L, I>, a: Action<I>,
) -> Network<L, I> {
    let pending = match a {
        Action::Send(id, packet) => s.pending.insert(id, packet),
        Action::Deliver(id) => s.pending.remove(id),
        _ => s.pending,
    };
    Network {
        pending,
        first_stopped: s.first_stopped || a == Action::StopFirstClient,
        r3_crashed: s.r3_crashed || a == Action::CrashR3,
        second_started: s.second_started || a == Action::StartSecondClient,
        unavailable: s.unavailable,
        locals: |r: Replica| match local_input(s, a, r) {
            Some(input) => update((s.locals)(r), input),
            None => (s.locals)(r),
        },
    }
}

pub open spec fn trace<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
) -> bool {
    states.len() == actions.len() + 1
    && forall|k: int| 0 <= k < actions.len() ==> {
        let a = #[trigger] actions[k];
        enabled(states[k], a) && states[k + 1] == advance(update, states[k], a)
    }
}

pub open spec fn survivor<L, I>(s: Network<L, I>) -> (L, L) {
    ((s.locals)(Replica::R1), (s.locals)(Replica::R2))
}

pub open spec fn packet_at<L, I>(s: Network<L, I>, id: nat) -> Option<Packet<I>> {
    if s.pending.contains_key(id) { Some(s.pending[id]) } else { None }
}

// What the active process sees at one step. A network delivery exposes
// the actual packet, including source and payload, rather than a crash bit.
pub struct ProcessStep<L, I> {
    pub actor: Process,
    pub action: Action<I>,
    pub own_local: Option<L>,
    pub incoming: Option<Packet<I>>,
}

pub open spec fn process_step<L, I>(s: Network<L, I>, a: Action<I>) -> ProcessStep<L, I> {
    let incoming = match a {
        Action::Deliver(id) => packet_at(s, id),
        _ => None,
    };
    let actor = match a {
        Action::Local(r, _) => Process::At(r),
        Action::Send(_, p) => p.from,
        Action::Deliver(_) => match incoming {
            Some(p) => p.to,
            None => Process::FirstClient,
        },
        Action::Strong(p) | Action::ClientInput(p, _) => p,
        Action::StopFirstClient => Process::FirstClient,
        Action::CrashR3 => Process::At(Replica::R3),
        Action::StartSecondClient => Process::SecondClient,
    };
    ProcessStep { actor, action: a, incoming, own_local: match actor {
        Process::At(r) => Some((s.locals)(r)),
        _ => None,
    } }
}

pub open spec fn observations<L, I>(
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
) -> Seq<ProcessStep<L, I>> {
    Seq::new(actions.len(), |i: int| process_step(states[i], actions[i]))
}

}
