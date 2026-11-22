use vstd::prelude::*;
use crate::{Branch, Replica, origin};
use crate::delivery::*;
use crate::protocol::*;
use crate::survivors::{outside_delays, keeps_delayed_slots, sr2_result, replay_with_actual_private_checkpoints};
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

// Independent closed form for checkpoint memory. Its proof checks
// one actual addressed delivery/step at a time.
pub open spec fn expected_control(b: Fork, p: Process, k: nat) -> Control {
    let client = p == Process::FirstClient;
    Control {
        requested: (p == at(Replica::R1) && 6 <= k)
            || (p == at(Replica::R2) && 7 <= k)
            || (p == at(Replica::R3) && 8 <= k),
        sent_requests: if !client || k < 3 { set![] } else if k < 4 { set![Replica::R1] }
            else if k < 5 { set![Replica::R1, Replica::R2] }
            else { set![Replica::R1, Replica::R2, Replica::R3] },
        replies_from: if !client || k < 12 { set![] } else if k < 13 { set![origin(b.branch)] }
            else { set![origin(b.branch), Replica::R3] },
        answered_first: (p == at(Replica::R1) && k >= 9)
            || (p == at(Replica::R2) && k >= 10) || (p == at(Replica::R3) && k >= 11),
        reply: if client && 12 <= k { Some(first_value(b)) } else { None },
        learned: None,
        weak_copy: if p == at(Replica::R3) && k >= 1 { Some(first_value(b)) } else { None },
        finished: client && 14 <= k,
    }
}

pub(crate) proof fn prefix_index(i: int)
    requires 0 <= i <= 16,
    ensures i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5 || i == 6
        || i == 7 || i == 8 || i == 9 || i == 10 || i == 11 || i == 12 || i == 13
        || i == 14 || i == 15 || i == 16,
{}

proof fn expected_control_after_one_step(b: Fork, p: Process, i: nat)
    requires i < actions_to_crash(b).len(),
    ensures ({
        let event = checkpoint_observations(b)[i as int];
        (if event.actor == p { change_control(expected_control(b, p, i), event) }
         else { expected_control(b, p, i) }) == expected_control(b, p, i + 1)
    }),
{
    prefix_index(i as int);
}

pub proof fn prefix_memory_tracks_actual_messages(b: Fork, p: Process, k: nat)
    requires k <= actions_to_crash(b).len(),
    ensures memory(checkpoint_machine(), p, checkpoint_observations(b), k)
        == expected_control(b, p, k),
    decreases k,
{
    if k > 0 {
        let i = (k - 1) as nat;
        prefix_memory_tracks_actual_messages(b, p, i);
        expected_control_after_one_step(b, p, i);
    }
}

proof fn expected_step_is_permitted(b: Fork, i: nat)
    requires i < actions_to_crash(b).len(),
    ensures ({
        let event = checkpoint_observations(b)[i as int];
        permits_step(expected_control(b, event.actor, i), event)
    }),
{
    prefix_index(i as int);
}

proof fn checkpoint_transport_post(b: Fork)
    ensures ({
        let actions = actions_to_crash(b);
        let end = checkpoint_states(b)[actions.len() as int];
        end.first_stopped && end.r3_crashed && end.second_started && end.unavailable.is_none()
            && survivor(end) == (2int, 5int)
            && end.pending.contains_key(2)
            && end.pending.contains_key(if b.branch == Branch::Alpha { 6 } else { 7 })
    }),
{
}

proof fn checkpoint_is_accepted(b: Fork)
    ensures accepted(checkpoint_machine(), checkpoint_observations(b)),
{
    let obs = checkpoint_observations(b);
    let m = checkpoint_machine();
    assert forall|i: int| 0 <= i < obs.len() implies {
        let event = #[trigger] obs[i];
        (m.accept)(memory(m, event.actor, obs, i as nat), event)
    } by {
        prefix_memory_tracks_actual_messages(b, obs[i].actor, i as nat);
        expected_step_is_permitted(b, i as nat);
    }
}

pub proof fn both_prefixes_are_enabled_and_client_finishes(b: Fork)
    ensures ({
        let actions = actions_to_crash(b);
        let states = checkpoint_states(b);
        let obs = checkpoint_observations(b);
        let end = states[actions.len() as int];
        states[0] == after_local_rmws() && trace(|x, i| cell(x, i), states, actions)
            && accepted(checkpoint_machine(), obs)
            && completes(checkpoint_machine(), obs)
            && checkpoint_control(b, Process::FirstClient).reply == Some(first_value(b))
            && end.first_stopped && end.r3_crashed && end.second_started && end.unavailable.is_none()
            && survivor(end) == (2int, 5int)
            && end.pending.contains_key(2)
            && end.pending.contains_key(if b.branch == Branch::Alpha { 6 } else { 7 })
    }),
{
    let actions = actions_to_crash(b);
    let obs = checkpoint_observations(b);
    prefix_transport_is_enabled(b);
    checkpoint_is_accepted(b);
    checkpoint_transport_post(b);
    prefix_memory_tracks_actual_messages(b, Process::FirstClient, actions.len());
}

pub open spec fn finished_sr1(b: Fork) -> bool {
    let obs = checkpoint_observations(b);
    checkpoint_states(b)[0] == after_local_rmws()
        && trace(|x, i| cell(x, i), checkpoint_states(b), actions_to_crash(b))
        && accepted(checkpoint_machine(), obs) && completes(checkpoint_machine(), obs)
        && checkpoint_control(b, Process::FirstClient).reply == Some(first_value(b))
}

pub open spec fn checkpoint_end(b: Fork) -> Network<int, Wire> {
    checkpoint_states(b)[actions_to_crash(b).len() as int]
}

pub open spec fn delayed_slots() -> Set<nat> {
    Set::empty().insert(0nat).insert(1nat).insert(2nat).insert(6nat).insert(7nat)
}

pub open spec fn client_sends_to(a: Action<Wire>, who: Process, r: Replica) -> bool {
    match a {
        Action::Send(_, p) => p.from == who && p.to == at(r),
        _ => false,
    }
}

// Count logical invocations from the sender's actions. Network Deliver
// events, including a delayed reply, never count as a new client send.
pub open spec fn only_request_sends(actions: Seq<Action<Wire>>, who: Process, targets: Set<Replica>) -> bool {
    forall|i: int| 0 <= i < actions.len() ==> match #[trigger] actions[i] {
        Action::Send(_, p) if p.from == who => invocation_packet(p) && targets.contains(p.to->At_0)
            && (forall|j: int| 0 <= j < i ==> !client_sends_to(#[trigger] actions[j], who, p.to->At_0)),
        _ => true,
    }
}

pub open spec fn invocation_only(actions: Seq<Action<Wire>>, who: Process, targets: Set<Replica>) -> bool {
    only_request_sends(actions, who, targets)
        && forall|r: Replica| #[trigger] targets.contains(r) ==> exists|i: int|
            0 <= i < actions.len() && client_sends_to(#[trigger] actions[i], who, r)
}

// Copies of an initial fan-out precede the client's first receipt. Thus
// neither a later destination nor the contents of a send reports an answer.
pub open spec fn fanout_before_receiving(es: Seq<ProcessStep<int, Wire>>, who: Process) -> bool {
    forall|i: int, j: int| 0 <= j < i < es.len() ==> match (#[trigger] es[i]).action {
        Action::Send(_, p) if p.from == who => (#[trigger] es[j]).actor != who || es[j].incoming.is_none(),
        _ => true,
    }
}

pub open spec fn second_invocation(states: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>) -> bool {
    invocation_only(a, Process::SecondClient, live_pair())
        && fanout_before_receiving(observations(states, a), Process::SecondClient)
}

pub open spec fn all_replicas() -> Set<Replica> { set![Replica::R1, Replica::R2, Replica::R3] }
pub open spec fn live_pair() -> Set<Replica> { set![Replica::R1, Replica::R2] }

// Check the send, its actual delivery and both local records for each
// replica. C1 learns which replies arrived only through its own mailbox.
pub open spec fn first_round(b: Fork) -> bool {
    let a = actions_to_crash(b);
    let o = checkpoint_observations(b);
    let end = checkpoint_end(b);
    let client = checkpoint_control(b, Process::FirstClient);
    let delayed = if b.branch == Branch::Alpha { 6nat } else { 7nat };
    let other_copy = if b.branch == Branch::Alpha { 0nat } else { 1nat };
    invocation_only(a, Process::FirstClient, all_replicas()) && fanout_before_receiving(o, Process::FirstClient)
        && invocation_only(a, Process::SecondClient, Set::empty())
        && client.sent_requests == all_replicas() && client.replies_from == crate::first_quorum(b.branch)
        && client.reply == Some(first_value(b)) && client.finished
        && (forall|r: Replica| {
            let i: int = match r { Replica::R1 => 0, Replica::R2 => 1, Replica::R3 => 2 };
            let request = packet_for(b, (3 + i) as nat);
            let reply = packet_for(b, (6 + i) as nat);
            let local = #[trigger] checkpoint_control(b, at(r));
            a[2+i] == Action::Send((3+i) as nat, request)
                && o[5+i].incoming == Some(request) && o[5+i].actor == at(r)
                && a[8+i] == Action::Send((6+i) as nat, reply)
                && first_reply(reply) && reply.from == at(r)
                && o[8+i].own_local == Some(reply.input->Reply_0)
                && local.requested && local.answered_first && local.replies_from.is_empty()
        })
        && o[11].incoming == Some(packet_for(b, if delayed == 6 { 7 } else { 6 }))
        && o[12].incoming == Some(packet_for(b, 8))
        && a[13] == Action::Strong(Process::FirstClient) && a[14] == Action::StopFirstClient
        && a[15] == Action::CrashR3 && a[16] == Action::StartSecondClient
        && end.pending.dom() == set![delayed, other_copy, 2nat]
        && packet_at(end, delayed) == Some(packet_for(b, delayed))
        && !live(end, end.pending[delayed].to) && !live(end, end.pending[other_copy].to)
        && packet_at(end, 2) == Some(packet_for(b, 2)) && live(end, end.pending[2].to)
}

pub proof fn fanout_and_reply_deliveries(b: Fork)
    ensures first_round(b),
{
    let a = actions_to_crash(b);
    let c = Process::FirstClient;
    both_prefixes_are_enabled_and_client_finishes(b);
    prefix_memory_tracks_actual_messages(b, c, a.len());
    assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
        Action::Send(_, p) if p.from == c => invocation_packet(p) && all_replicas().contains(p.to->At_0)
            && (forall|j: int| 0 <= j < i ==> !client_sends_to(#[trigger] a[j], c, p.to->At_0)),
        _ => true,
    } by {
        prefix_index(i);
        if let Action::Send(_, p) = a[i] {
            if p.from == c {
                assert forall|j: int| 0 <= j < i implies !client_sends_to(#[trigger] a[j], c, p.to->At_0)
                    by { prefix_index(j); }
            }
        }
    }
    assert forall|r: Replica| #[trigger] all_replicas().contains(r) implies
        exists|i: int| 0 <= i < a.len() && client_sends_to(#[trigger] a[i], c, r) by {
        let i: int = match r { Replica::R1 => 2, Replica::R2 => 3, Replica::R3 => 4 };
        assert(client_sends_to(a[i], c, r));
    }
    assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
        Action::Send(_, p) => p.from != Process::SecondClient,
        _ => true,
    } by { prefix_index(i); }
    assert forall|r: Replica| #[trigger] checkpoint_control(b, at(r))
        == expected_control(b, at(r), a.len()) by {
        prefix_memory_tracks_actual_messages(b, at(r), a.len());
    }
    let es = checkpoint_observations(b);
    assert forall|i: int, j: int| 0 <= j < i < es.len() implies match (#[trigger] es[i]).action {
        Action::Send(_, p) if p.from == c => (#[trigger] es[j]).actor != c || es[j].incoming.is_none(),
        _ => true,
    } by { prefix_index(i); prefix_index(j); }
    let delayed = if b.branch == Branch::Alpha { 6nat } else { 7nat };
    let other_copy = if b.branch == Branch::Alpha { 0nat } else { 1nat };
    assert(checkpoint_end(b).pending.dom() =~= set![delayed, other_copy, 2nat]);
}

pub proof fn surviving_checkpoint_agreement(n: Notice)
    ensures
        outside_delays(checkpoint_end(alpha(n)),
            checkpoint_end(beta(n)), delayed_slots()),
        forall|p: Process| #[trigger] survivor_actor(p) ==>
            checkpoint_control(alpha(n), p) == checkpoint_control(beta(n), p),
        checkpoint_control(alpha(n), Process::FirstClient).reply == Some(5),
        checkpoint_control(beta(n), Process::FirstClient).reply == Some(2),
{
    both_prefixes_are_enabled_and_client_finishes(alpha(n));
    both_prefixes_are_enabled_and_client_finishes(beta(n));
    assert forall|p: Process| #[trigger] survivor_actor(p) implies
        checkpoint_control(alpha(n), p) == checkpoint_control(beta(n), p) by {
        prefix_memory_tracks_actual_messages(alpha(n), p,
            actions_to_crash(alpha(n)).len());
        prefix_memory_tracks_actual_messages(beta(n), p,
            actions_to_crash(beta(n)).len());
    }
    assert forall|id: nat| !delayed_slots().contains(id) implies
        #[trigger] packet_at(checkpoint_end(beta(n)), id)
            == packet_at(checkpoint_end(alpha(n)), id) by {
    }
}

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

pub proof fn copies_and_knowledge_at_checkpoint(b: Fork, weak_order: Seq<Op>)
    ensures
        weak_copies_before_sr1(b) == set![origin(b.branch), Replica::R3],
        pre_sr1_g(b, weak_order) == weak_order.contains(observed_writer(b)),
        checkpoint_control(b, at(origin(b.branch))).learned.is_none(),
        packet_at(checkpoint_end(b), 2) == Some(packet_for(b, 2)),
{
    prefix_memory_tracks_actual_messages(b, at(origin(b.branch)), actions_to_crash(b).len());
    assert(weak_copies_before_sr1(b).len() == 2);
}

// Optional weak-path assignment on this delivery. The choice represents
// an independent ordering decision. Replication alone does not set it.
pub open spec fn weak_assignment(b: Fork, assigns_position: bool) -> crate::RecoveredOrder {
    if assigns_position && weak_copies_before_sr1(b).contains(Replica::R3) {
        crate::RecoveredOrder { ops: seq![observed_writer(b)], states: seq![1int, first_value(b)] }
    } else { crate::RecoveredOrder { ops: seq![], states: seq![1int] } }
}

pub proof fn weak_assignment_at_delivery(b: Fork, assigns_position: bool)
    ensures ({
        let weak = weak_assignment(b, assigns_position);
        crate::legal_recovery(weak)
            && (pre_sr1_g(b, weak.ops) == assigns_position)
            && (truthful_notice(b, weak.ops) == (b.notice == Notice::Replication || assigns_position))
            && (assigns_position ==> weak.ops == seq![observed_writer(b)])
    }),
{
    let weak = weak_assignment(b, assigns_position);
    copies_and_knowledge_at_checkpoint(b, weak.ops);
    assert(weak_copies_before_sr1(b).contains(Replica::R3));
    assert(weak_copies_before_sr1(b).len() == 2);
    if assigns_position {
        assert(weak.ops[0] == observed_writer(b));
        assert(weak.ops.contains(observed_writer(b)));
    } else {
        assert(weak.ops.len() == 0);
        assert(!weak.ops.contains(observed_writer(b)));
    }
    assert(crate::legal_recovery(weak)) by {
        assert forall|i: int| 0 <= i < weak.ops.len() implies {
            let op = #[trigger] weak.ops[i];
            weak.states[i + 1] == crate::next(op, weak.states[i])
                && (op == Op::W1 || op == Op::W2 ==> weak.states[i] == 1)
        } by { assert(i == 0); }
    }
}

// At each step of these concrete prefixes, a live actor sees identical
// events or takes no step in either branch. This includes the sender's
// view of every mandatory send, as well as actual delivered payloads.
proof fn live_steps_in_both_prefixes(n: Notice, p: Process, i: nat)
    requires survivor_actor(p), i < actions_to_crash(alpha(n)).len(),
    ensures ({
        let a = checkpoint_observations(alpha(n))[i as int];
        let b = checkpoint_observations(beta(n))[i as int];
        a == b || (a.actor != p && b.actor != p)
    }),
{
    prefix_index(i as int);
}

pub proof fn arbitrary_survivor_memory_agrees<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, p: Process, k: nat,
)
    requires survivor_actor(p), k <= actions_to_crash(alpha(n)).len(),
    ensures memory(m, p, checkpoint_observations(alpha(n)), k)
        == memory(m, p, checkpoint_observations(beta(n)), k),
    decreases k,
{
    if k > 0 {
        let prev = (k - 1) as nat;
        arbitrary_survivor_memory_agrees(n, m, p, prev);
        live_steps_in_both_prefixes(n, p, prev);
    }
}

// Private memory can itself be a complete process history. Include every
// network slot the continuation can inspect while the three old packets
// at its own cut remain pending. The physical queue is retained separately.
pub struct SurvivorView<S> {
    pub cells: (int, int),
    pub left: S,
    pub right: S,
    pub second: S,
    pub pending: Map<nat, Packet<Wire>>,
}

pub open spec fn survivor_view<S>(b: Fork, m: LocalProtocol<S, int, Wire>) -> SurvivorView<S> {
    let obs = checkpoint_observations(b);
    let cut = checkpoint_end(b);
    SurvivorView {
        cells: survivor(cut),
        left: memory(m, at(Replica::R1), obs, obs.len()),
        right: memory(m, at(Replica::R2), obs, obs.len()),
        second: memory(m, Process::SecondClient, obs, obs.len()),
        pending: cut.pending.restrict(cut.pending.dom().difference(delayed_slots())),
    }
}

pub proof fn private_participation_cannot_identify_c1_quorum<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, decode: spec_fn(SurvivorView<S>) -> Set<Replica>,
)
    ensures
        first_round(alpha(n)), first_round(beta(n)),
        survivor_view(alpha(n), m) == survivor_view(beta(n), m),
        !(decode(survivor_view(alpha(n), m)) == checkpoint_control(alpha(n), Process::FirstClient).replies_from
            && decode(survivor_view(beta(n), m)) == checkpoint_control(beta(n), Process::FirstClient).replies_from),
{
    let a = alpha(n); let b = beta(n);
    fanout_and_reply_deliveries(a);
    fanout_and_reply_deliveries(b);
    let k = actions_to_crash(a).len();
    arbitrary_survivor_memory_agrees(n, m, at(Replica::R1), k);
    arbitrary_survivor_memory_agrees(n, m, at(Replica::R2), k);
    arbitrary_survivor_memory_agrees(n, m, Process::SecondClient, k);
    assert(survivor_view(a,m).pending =~= Map::empty());
    assert(survivor_view(b,m).pending =~= Map::empty());
    assert(crate::first_quorum(a.branch).contains(Replica::R2) && !crate::first_quorum(b.branch).contains(Replica::R2));
}

// Assign each observed write a weak-path position at the real delivery to
// R3. Neither the complete surviving histories nor a selector on those
// histories can then identify both objective G writes in this window.
pub proof fn objective_g_not_deducible_at_common_checkpoint<S>(
    m: LocalProtocol<S, int, Wire>, w: Op, decide: spec_fn(SurvivorView<S>, Op) -> bool,
)
    requires w == Op::W1 || w == Op::W2,
    ensures ({
        let a = alpha(Notice::G); let b = beta(Notice::G);
        let ao = weak_assignment(a, true).ops; let bo = weak_assignment(b, true).ops;
        truthful_notice(a, ao) && truthful_notice(b, bo)
            && (write_at_g(a, ao, w) == (w == Op::W2)) && (write_at_g(b, bo, w) == (w == Op::W1))
            && checkpoint_control(a, at(Replica::R2)).learned.is_none()
            && checkpoint_control(b, at(Replica::R1)).learned.is_none()
            && !(decide(survivor_view(a, m), w) == write_at_g(a, ao, w)
                && decide(survivor_view(b, m), w) == write_at_g(b, bo, w))
    }),
{
    let a = alpha(Notice::G); let b = beta(Notice::G);
    weak_assignment_at_delivery(a, true); weak_assignment_at_delivery(b, true);
    let ao = weak_assignment(a, true).ops; let bo = weak_assignment(b, true).ops;
    copies_and_knowledge_at_checkpoint(a, ao); copies_and_knowledge_at_checkpoint(b, bo);
    assert(ao == seq![Op::W2] && bo == seq![Op::W1]);
    assert(!ao.contains(Op::W1) && !bo.contains(Op::W2));
    private_participation_cannot_identify_c1_quorum(Notice::G, m, |v| Set::empty());
}

pub open spec fn during_sr1(b: Fork, k: int, r: Replica) -> int {
    (checkpoint_states(b)[k].locals)(r)
}

pub open spec fn first_client_at<S>(m: LocalProtocol<S, int, Wire>, b: Fork, k: nat) -> S {
    memory(m, Process::FirstClient, checkpoint_observations(b), k)
}

// Both replies are present after step 12. SR1 may return on that delivery
// or on the following local C1 step. Stopping C1 is a later network event.
pub open spec fn first_return_len<S>(m: LocalProtocol<S, int, Wire>, b: Fork) -> nat {
    if (m.done)(first_client_at(m, b, 13)) { 13 } else { 14 }
}

pub open spec fn first_result<S>(m: LocalProtocol<S, int, Wire>, value: spec_fn(S) -> int, b: Fork) -> int {
    value(first_client_at(m, b, first_return_len(m, b)))
}

// The observer and sample belong to the actual invocation through return.
// C1 can discard its response when it stops without changing this witness.
pub open spec fn completed_quorum_sample<S>(
    m: LocalProtocol<S, int, Wire>, value: spec_fn(S) -> int, b: Fork,
) -> bool {
    let end = first_return_len(m, b);
    (forall|k: nat| k <= 12 ==> !(m.done)(#[trigger] first_client_at(m, b, k)))
        && (m.done)(first_client_at(m, b, end))
        && exists|r: Replica, k: int| crate::first_quorum(b.branch).contains(r) && 2 <= k <= end
            && #[trigger] during_sr1(b, k, r) == first_result(m, value, b)
}

pub proof fn stable_responder_cells_fix_first_sample<S>(
    m: LocalProtocol<S, int, Wire>, value: spec_fn(S) -> int, b: Fork,
)
    requires completed_quorum_sample(m, value, b),
    ensures first_result(m, value, b) == first_value(b),
{
    let (r, k) = choose|r: Replica, k: int| crate::first_quorum(b.branch).contains(r)
        && 2 <= k <= first_return_len(m, b)
        && #[trigger] during_sr1(b, k, r) == first_result(m, value, b);
}

pub proof fn checkpoint_monitor_supplies_its_sample(b: Fork)
    ensures completed_quorum_sample(checkpoint_machine(), |s: Control| s.reply.unwrap(), b),
{
    both_prefixes_are_enabled_and_client_finishes(b);
    let m = checkpoint_machine(); let c = Process::FirstClient;
    assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m, b, k))
        by { prefix_memory_tracks_actual_messages(b, c, k); }
    prefix_memory_tracks_actual_messages(b, c, 13);
    prefix_memory_tracks_actual_messages(b, c, 14);
    assert(crate::first_quorum(b.branch).contains(origin(b.branch)));
    assert(during_sr1(b, 10, origin(b.branch)) == first_value(b));
}

// This result quantifies over any local machine admitting the specified
// prefixes, including arbitrary private protocol and client histories.
pub proof fn replay_completed_sr2_at_checkpoints<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    a: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>, v: int,
)
    requires
        accepted(m, checkpoint_observations(alpha(n))),
        accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)),
        completed_quorum_sample(m, first, beta(n)),
        second_invocation(a, actions),
        result((resume_at(m, checkpoint_observations(alpha(n))).initial)(Process::SecondClient)).is_none(),
        a[0] == checkpoint_end(alpha(n)),
        trace(|x, i| cell(x, i), a, actions),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], delayed_slots()),
        accepted(resume_at(m, checkpoint_observations(alpha(n))), observations(a, actions)),
        sr2_result(resume_at(m, checkpoint_observations(alpha(n))), result, observations(a, actions)) == Some(v),
    ensures ({
        let later = replay(|x, i| cell(x, i), checkpoint_end(beta(n)), actions);
        let resumed = resume_at(m, checkpoint_observations(beta(n)));
        trace(|x, i| cell(x, i), later, actions) && accepted(resumed, observations(later, actions))
            && sr2_result(resumed, result, observations(later, actions)) == Some(v)
            && first_result(m, first, alpha(n)) == 5 && first_result(m, first, beta(n)) == 2
    }),
{
    hide(memory);
    hide(replay);
    hide(resume_at);
    hide(outside_delays);
    hide(accepted);
    hide(trace);
    surviving_checkpoint_agreement(n);
    stable_responder_cells_fix_first_sample(m, first, alpha(n));
    stable_responder_cells_fix_first_sample(m, first, beta(n));
    let earlier_a = checkpoint_observations(alpha(n));
    let earlier_b = checkpoint_observations(beta(n));
    assert(earlier_a.len() == earlier_b.len() && earlier_a.len() == actions_to_crash(alpha(n)).len());
    assert forall|p: Process| #[trigger] survivor_actor(p) implies
        memory(m, p, earlier_a, earlier_a.len()) == memory(m, p, earlier_b, earlier_b.len()) by {
        arbitrary_survivor_memory_agrees(n, m, p, earlier_a.len());
    }
    replay_with_actual_private_checkpoints(|x, i| cell(x, i), m, earlier_a, earlier_b,
        a, checkpoint_end(beta(n)), actions, delayed_slots(), result, v);
}

pub proof fn one_completed_sr2_from_constructed_prefixes<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    a: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>, v: int,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>,
)
    requires
        accepted(m, checkpoint_observations(alpha(n))),
        accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)),
        completed_quorum_sample(m, first, beta(n)),
        second_invocation(a, actions),
        result((resume_at(m, checkpoint_observations(alpha(n))).initial)(Process::SecondClient)).is_none(),
        a[0] == checkpoint_end(alpha(n)),
        trace(|x, i| cell(x, i), a, actions),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], delayed_slots()),
        accepted(resume_at(m, checkpoint_observations(alpha(n))), observations(a, actions)),
        sr2_result(resume_at(m, checkpoint_observations(alpha(n))), result, observations(a, actions)) == Some(v),
    ensures ({
        let later = replay(|x, i| cell(x, i), checkpoint_end(beta(n)), actions);
        let resumed = resume_at(m, checkpoint_observations(beta(n)));
        trace(|x, i| cell(x, i), later, actions) && accepted(resumed, observations(later, actions))
            && sr2_result(resumed, result, observations(later, actions)) == Some(v)
            && first_result(m, first, alpha(n)) == 5 && first_result(m, first, beta(n)) == 2
            && !(crate::legal(ao, ax, 5, v) && crate::legal(bo, bx, 2, v))
    }),
{
    replay_completed_sr2_at_checkpoints(n, m, first, result, a, actions, v);
    if crate::legal(ao, ax, 5, v) && crate::legal(bo, bx, 2, v) {
        crate::conditional_history_contradiction(ao, ax, bo, bx, v);
    }
}

}
