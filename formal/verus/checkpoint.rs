use vstd::prelude::*;
use crate::{Branch, Replica, origin};
use crate::delivery::*;
use crate::protocol::*;
use crate::Op;

verus! {

// The content of a status notice is distinct from the underlying fact.
pub enum Notice { Replication, Ordering, G }

pub struct Fork {
    pub branch: Branch,
    pub notice: Notice,
}

pub struct Report {
    pub value: int,
    pub answered_first: bool,
}

pub open spec fn alpha(n: Notice) -> Fork { Fork { branch: Branch::Alpha, notice: n } }
pub open spec fn beta(n: Notice) -> Fork { Fork { branch: Branch::Beta, notice: n } }

pub enum Wire {
    Copy(int),
    WeakConfirm(Notice),
    Request,
    Reply(int),
    Peer(int), // Ordinary replica protocol traffic.
    Query2,
    Answer2(Report),
    StampedAnswer(Report, nat),
}

pub open spec fn cell(x: int, message: Wire) -> int {
    match message { Wire::Copy(v) => v, _ => x }
}

pub open spec fn send(slot: nat, path: Path, from: Process, to: Process, input: Wire)
    -> Action<Wire>
{
    Action::Send(slot, Packet { path, from, to, input })
}

pub open spec fn at(r: Replica) -> Process { Process::At(r) }

pub open spec fn local_rmw_cells() -> Network<int, Wire> {
    Network {
        locals: |r: Replica| crate::load(crate::isolated(), r),
        pending: Map::empty(), first_stopped: false, r3_crashed: false, second_started: false,
        unavailable: None,
    }
}

pub open spec fn after_local_rmws() -> Network<int, Wire> {
    let a = advance(|x, i| cell(x, i), local_rmw_cells(),
        send(0, Path::Weak, at(Replica::R1), at(Replica::R3), Wire::Copy(2)));
    advance(|x, i| cell(x, i), a,
        send(1, Path::Weak, at(Replica::R2), at(Replica::R3), Wire::Copy(5)))
}

pub proof fn origin_updates_are_actually_offered()
    ensures ({
        let s = local_rmw_cells();
        let del = |x, i| cell(x, i);
        let first = send(0, Path::Weak, at(Replica::R1), at(Replica::R3), Wire::Copy((s.locals)(Replica::R1)));
        let second = send(1, Path::Weak, at(Replica::R2), at(Replica::R3), Wire::Copy((s.locals)(Replica::R2)));
        let middle = advance(del, s, first);
        trace(del, seq![s, middle, after_local_rmws()], seq![first, second])
    }),
{
    crate::isolated_rmws();
    let s = local_rmw_cells();
    let del = |x, i| cell(x, i);
    let first = send(0, Path::Weak, at(Replica::R1), at(Replica::R3), Wire::Copy(2));
    let second = send(1, Path::Weak, at(Replica::R2), at(Replica::R3), Wire::Copy(5));
    let actions = seq![first, second];
    let states = seq![s, advance(del, s, first), after_local_rmws()];
    assert forall|i: int| 0 <= i < 2 implies {
        let action = #[trigger] actions[i];
        enabled(states[i], action) && states[i + 1] == advance(del, states[i], action)
    } by { assert(i == 0 || i == 1); }
}

pub open spec fn first_value(b: Fork) -> int {
    match b.branch { Branch::Alpha => 5, Branch::Beta => 2 }
}

pub open spec fn received_replies(b: Fork) -> Seq<Action<Wire>> {
    let c = Process::FirstClient;
    let v = first_value(b);
    seq![
        Action::Deliver(if b.branch == Branch::Alpha { 1 } else { 0 }),
        send(2, Path::Weak, at(Replica::R3), at(origin(b.branch)), Wire::WeakConfirm(b.notice)),
        send(3, Path::Strong, c, at(Replica::R1), Wire::Request),
        send(4, Path::Strong, c, at(Replica::R2), Wire::Request),
        send(5, Path::Strong, c, at(Replica::R3), Wire::Request),
        Action::Deliver(3), Action::Deliver(4), Action::Deliver(5),
        send(6, Path::FirstReadReply, at(Replica::R1), c, Wire::Reply(2)),
        send(7, Path::FirstReadReply, at(Replica::R2), c, Wire::Reply(5)),
        send(8, Path::FirstReadReply, at(Replica::R3), c, Wire::Reply(v)),
        Action::Deliver(if b.branch == Branch::Alpha { 7 } else { 6 }),
        Action::Deliver(8),
    ]
}

pub open spec fn actions_to_crash(b: Fork) -> Seq<Action<Wire>> {
    received_replies(b)
        + seq![Action::Strong(Process::FirstClient), Action::StopFirstClient,
            Action::CrashR3, Action::StartSecondClient]
}

pub struct Control {
    pub requested: bool,
    pub sent_requests: Set<Replica>,
    pub replies_from: Set<Replica>,
    pub answered_first: bool,
    pub reply: Option<int>,
    pub finished: bool,
    pub learned: Option<Notice>,
    pub weak_copy: Option<int>,
}

pub open spec fn initial_control() -> Control {
    Control { requested: false, sent_requests: Set::empty(), replies_from: Set::empty(),
        answered_first: false, reply: None, finished: false, learned: None, weak_copy: None }
}

pub open spec fn notice_to(packet: Packet<Wire>, recipient: Process) -> bool {
    packet.path == Path::Weak && packet.from == at(Replica::R3) && packet.to == recipient
        && (recipient == at(Replica::R1) || recipient == at(Replica::R2))
        && (packet.input is WeakConfirm)
}

// The sender's own initial invocation is the only source of client packets.
pub open spec fn invocation_packet(p: Packet<Wire>) -> bool {
    p.path == Path::Strong && match (p.from, p.to) {
        (Process::FirstClient, Process::At(_)) => p.input == Wire::Request,
        (Process::SecondClient, Process::At(r)) => r != Replica::R3 && p.input == Wire::Query2,
        _ => false,
    }
}

pub open spec fn first_reply(p: Packet<Wire>) -> bool {
    p.path == Path::FirstReadReply && p.from is At && p.to == Process::FirstClient && p.input is Reply
}

pub open spec fn change_control(s: Control, event: ProcessStep<int, Wire>) -> Control {
    match event.incoming {
        Some(p) => match p.input {
            Wire::Copy(v) if p.path == Path::Weak => Control { weak_copy: Some(v), ..s },
            Wire::WeakConfirm(n) if notice_to(p, event.actor) => Control { learned: Some(n), ..s },
            Wire::Request => Control { requested: true, ..s },
            Wire::Reply(v) if first_reply(p) => Control {
                replies_from: s.replies_from.insert(p.from->At_0), reply: Some(v), ..s
            },
            _ => s,
        },
        None => match event.action {
            Action::Send(_, p) if invocation_packet(p) =>
                Control { sent_requests: s.sent_requests.insert(p.to->At_0), ..s },
            Action::Send(_, p) if first_reply(p) => Control { answered_first: true, ..s },
            Action::Strong(Process::FirstClient) => Control { finished: true, ..s },
            _ => s,
        },
    }
}

pub open spec fn permits_step(s: Control, e: ProcessStep<int, Wire>)
    -> bool
{
    match e.action {
        Action::Send(_, p) if outside_replica(p.from) =>
            invocation_packet(p) && !s.sent_requests.contains(p.to->At_0)
                && s.replies_from.is_empty() && !s.finished,
        Action::Send(_, packet) => match packet.input {
            Wire::WeakConfirm(_) => notice_to(packet, packet.to) && e.actor == at(Replica::R3)
                && s.weak_copy == e.own_local && s.weak_copy == Some(
                    if packet.to == at(Replica::R1) { 2int } else { 5int }),
            Wire::Reply(v) => first_reply(packet) && s.requested && e.own_local == Some(v),
            Wire::Request | Wire::Query2 => false,
            _ => true,
        },
        Action::Strong(p) if p == Process::FirstClient =>
            s.replies_from.len() == 2,
        Action::StopFirstClient => s.finished,
        _ => match e.incoming {
            Some(packet) => match packet.input {
                Wire::Reply(v) => s.reply.is_none() || s.reply == Some(v),
                _ => true,
            },
            _ => true,
        },
    }
}

pub open spec fn checkpoint_machine()
    -> LocalProtocol<Control, int, Wire>
{
    LocalProtocol {
        initial: |p: Process| initial_control(),
        accept: |s, e| permits_step(s, e),
        update: |s, e| change_control(s, e),
        done: |s: Control| s.finished,
    }
}

// Slot contents are read from the transport state on delivery. These packet
// lifetimes give a finite witness; the step proof below checks each send,
// delivery, local value and lifecycle flag against the transport relation.
pub open spec fn in_flight(b: Fork, k: nat, id: nat) -> bool {
    match id {
        _ if id == 0 => k == 0 || b.branch == Branch::Alpha,
        _ if id == 1 => k == 0 || b.branch == Branch::Beta,
        _ if id == 2 => k >= 2,
        _ if id == 3 || id == 4 || id == 5 => id <= k && k < id + 3,
        _ if id == 6 => 9 <= k && (b.branch == Branch::Alpha || k < 12),
        _ if id == 7 => 10 <= k && (b.branch == Branch::Beta || k < 12),
        _ if id == 8 => 11 <= k && k < 13,
        _ => false,
    }
}

pub open spec fn packet_for(b: Fork, id: nat) -> Packet<Wire> {
    let c = Process::FirstClient;
    let owner = at(origin(b.branch));
    let r1 = at(Replica::R1);
    let r2 = at(Replica::R2);
    let r3 = at(Replica::R3);
    let (path, from, to, input) = match id {
        _ if id == 0 => (Path::Weak, r1, r3, Wire::Copy(2)),
        _ if id == 1 => (Path::Weak, r2, r3, Wire::Copy(5)),
        _ if id == 2 => (Path::Weak, r3, owner, Wire::WeakConfirm(b.notice)),
        _ if id == 3 || id == 4 || id == 5 => (Path::Strong, c, if id == 3 { r1 } else if id == 4 { r2 } else { r3 },
            Wire::Request),
        _ if id == 6 || id == 7 || id == 8 => (Path::FirstReadReply, if id == 6 { r1 } else if id == 7 { r2 } else { r3 },
            c, Wire::Reply(if id == 6 { 2 } else if id == 7 { 5 } else { first_value(b) })),
        _ => (Path::Strong, c, r3, Wire::Request), // Outside the domain of the SR1 queue.
    };
    Packet { path, from, to, input }
}

pub open spec fn state_after(b: Fork, k: nat) -> Network<int, Wire> {
    Network {
        locals: |r: Replica| match r {
            Replica::R1 => 2, Replica::R2 => 5,
            Replica::R3 => if k == 0 { 1 } else { first_value(b) },
        },
        pending: Map::new(set![0nat, 1, 2, 3, 4, 5, 6, 7, 8]
            .filter(|id: nat| in_flight(b, k, id)), |id: nat| packet_for(b, id)),
        first_stopped: k >= 15, r3_crashed: k >= 16,
        second_started: k >= 17, unavailable: None,
    }
}

pub open spec fn checkpoint_states(b: Fork) -> Seq<Network<int, Wire>> {
    Seq::new(actions_to_crash(b).len() + 1,
        |i: int| state_after(b, i as nat))
}

pub open spec fn checkpoint_observations(b: Fork)
    -> Seq<ProcessStep<int, Wire>>
{
    observations(checkpoint_states(b), actions_to_crash(b))
}

pub open spec fn checkpoint_control(b: Fork, p: Process) -> Control {
    let obs = checkpoint_observations(b);
    memory(checkpoint_machine(), p, obs, obs.len())
}

pub proof fn prefix_transport_is_enabled(b: Fork)
    ensures
        trace(|x, i| cell(x, i), checkpoint_states(b), actions_to_crash(b)),
        checkpoint_states(b)[0] == after_local_rmws(),
{
    let s0 = state_after(b, 0);
    let entry = after_local_rmws();
    assert(s0.pending =~= entry.pending);
    assert(s0.locals =~= entry.locals);
    let actions = actions_to_crash(b);
    let states = checkpoint_states(b);
    assert forall|i: int| 0 <= i < actions.len() implies {
        let action = #[trigger] actions[i];
        enabled(states[i], action) && states[i + 1] == advance(|x, m| cell(x, m), states[i], action)
    } by {
        prefix_index(i);
        let next = advance(|x, m| cell(x, m), states[i], actions[i]);
        assert(next.locals =~= states[i + 1].locals);
        assert(next.pending =~= states[i + 1].pending);
    }
}

pub(crate) proof fn prefix_index(i: int)
    requires 0 <= i <= 16,
    ensures i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5 || i == 6
        || i == 7 || i == 8 || i == 9 || i == 10 || i == 11 || i == 12 || i == 13
        || i == 14 || i == 15 || i == 16,
{}

pub open spec fn checkpoint_end(b: Fork) -> Network<int, Wire> {
    checkpoint_states(b)[actions_to_crash(b).len() as int]
}

pub open spec fn all_replicas() -> Set<Replica> { set![Replica::R1, Replica::R2, Replica::R3] }
pub open spec fn live_pair() -> Set<Replica> { set![Replica::R1, Replica::R2] }

pub open spec fn observed_writer(b: Fork) -> Op {
    match b.branch { Branch::Alpha => Op::W2, Branch::Beta => Op::W1 }
}

// The origin already applied its own RMW. Count R3 only for the addressed
// delivery of that origin's actual update, checked before SR1 starts.
pub open spec fn copies_of(b: Fork, w: Op) -> Set<Replica> {
    if w == Op::W1 || w == Op::W2 {
        let (owner, value) = if w == Op::W1 { (Replica::R1, 2int) } else { (Replica::R2, 5int) };
        let applied = checkpoint_observations(b)[0];
        let packet = Packet { path: Path::Weak, from: at(owner), to: at(Replica::R3), input: Wire::Copy(value) };
        let base = set![owner];
        if applied.actor == at(Replica::R3) && applied.incoming == Some(packet) { base.insert(Replica::R3) } else { base }
    } else { Set::empty() }
}

pub open spec fn weak_copies_before_sr1(b: Fork) -> Set<Replica> {
    copies_of(b, observed_writer(b))
}

pub open spec fn write_at_g(b: Fork, weak_order: Seq<Op>, w: Op) -> bool {
    crate::guarantee::ordered_on_majority(weak_order, copies_of(b, w), w)
}

pub open spec fn pre_sr1_g(b: Fork, weak_order: Seq<Op>) -> bool {
    write_at_g(b, weak_order, observed_writer(b))
}

// An Order or G attestation needs independent ordering evidence at issue.
// A copy receipt only attests the weak application. No strong read or
// future response appears in this prefix-level definition of G.
pub open spec fn truthful_notice(b: Fork, weak_order: Seq<Op>) -> bool {
    match b.notice {
        Notice::Replication => weak_copies_before_sr1(b).len() >= 2,
        Notice::Ordering => weak_order.contains(observed_writer(b)),
        Notice::G => pre_sr1_g(b, weak_order),
    }
}

// Optional weak-path assignment on this delivery. The choice represents
// an independent ordering decision. Replication alone does not set it.
pub open spec fn weak_assignment(b: Fork, assigns_position: bool) -> crate::RecoveredOrder {
    if assigns_position && weak_copies_before_sr1(b).contains(Replica::R3) {
        crate::RecoveredOrder { ops: seq![observed_writer(b)], states: seq![1int, first_value(b)] }
    } else { crate::RecoveredOrder { ops: seq![], states: seq![1int] } }
}

}
