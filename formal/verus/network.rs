// BEGIN MODULE: delivery
pub mod delivery {
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
}
// END MODULE: delivery

// BEGIN MODULE: progress
pub mod progress {
    use vstd::prelude::*;
    use crate::delivery::*;

    verus! {

    #[verifier::reject_recursive_types(L)]
    #[verifier::reject_recursive_types(I)]
    pub struct Execution<L, I> {
        pub state: spec_fn(nat) -> Network<L, I>,
        pub action: spec_fn(nat) -> Action<I>,
    }

    // An issued packet cannot be postponed forever while its recipient
    // remains live. This is tested on the reference execution only.
    pub open spec fn delivery_fair<L, I>(e: Execution<L, I>) -> bool {
        forall|i: nat, id: nat| #[trigger] (e.state)(i).pending.contains_key(id)
            ==> exists|j: nat| j >= i && (#[trigger] (e.action)(j) == Action::Deliver(id)
                || !live((e.state)(j), (e.state)(i).pending[id].to))
    }

    pub open spec fn continuously_runnable<L, I>(
        e: Execution<L, I>, runnable: spec_fn(Network<L, I>, Process) -> bool,
        from: nat, p: Process,
    ) -> bool {
        forall|i: nat| i >= from ==> #[trigger] runnable((e.state)(i), p)
    }

    pub open spec fn runs_at<L, I>(e: Execution<L, I>, j: nat, p: Process) -> bool {
        process_step((e.state)(j), (e.action)(j)).actor == p
    }

    pub open spec fn process_fair<L, I>(
        e: Execution<L, I>, runnable: spec_fn(Network<L, I>, Process) -> bool,
    ) -> bool {
        forall|from: nat, p: Process| #[trigger] continuously_runnable(e, runnable, from, p)
            ==> exists|j: nat| j >= from && #[trigger] runs_at(e, j, p)
    }

    }
}
// END MODULE: progress

// BEGIN MODULE: guarantee
pub mod guarantee {
    use vstd::prelude::*;
    use crate::{Op, Replica};

    verus! {

    // G records membership in the total order and replication of the
    // operation. It does not say which replica encodes the order position.
    pub open spec fn ordered_on_majority(order: Seq<Op>, copies: Set<Replica>, w: Op) -> bool {
        order.contains(w) && copies.len() >= 2
    }

    }
}
// END MODULE: guarantee

// BEGIN MODULE: survivors
pub mod survivors {
    use vstd::prelude::*;
    use crate::delivery::*;

    verus! {

    pub open spec fn after_crash<L, I>(s: Network<L, I>) -> bool {
        s.r3_crashed && s.first_stopped && s.second_started && s.unavailable.is_none()
    }

    }
}
// END MODULE: survivors

// BEGIN MODULE: checkpoint
pub mod checkpoint {
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
}
// END MODULE: checkpoint

// BEGIN MODULE: confirmation
pub mod confirmation {
    use vstd::prelude::*;
    use crate::delivery::*;

    verus! {

    pub open spec fn fresh_send<I>(a: Action<I>, reserved: Set<nat>) -> bool {
        match a { Action::Send(id, _) => !reserved.contains(id), _ => true }
    }

    }
}
// END MODULE: confirmation

// BEGIN MODULE: protocol
pub mod protocol {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::delivery::*;

    verus! {

    #[verifier::reject_recursive_types(S)]
    #[verifier::reject_recursive_types(L)]
    #[verifier::reject_recursive_types(I)]
    pub struct LocalProtocol<S, L, I> {
        pub initial: spec_fn(Process) -> S,
        pub accept: spec_fn(S, ProcessStep<L, I>) -> bool,
        pub update: spec_fn(S, ProcessStep<L, I>) -> S,
        pub done: spec_fn(S) -> bool,
    }

    // The protocol keeps arbitrary private memory, including any local clock
    // readings or failure suspicions received as explicit scheduled inputs.
    pub open spec fn memory<S, L, I>(
        m: LocalProtocol<S, L, I>, who: Process, obs: Seq<ProcessStep<L, I>>, k: nat,
    ) -> S
        decreases k,
    {
        if k == 0 {
            (m.initial)(who)
        } else {
            let before = memory(m, who, obs, (k - 1) as nat);
            let ev = obs[k - 1];
            if ev.actor == who { (m.update)(before, ev) } else { before }
        }
    }

    pub open spec fn survivor_actor(p: Process) -> bool {
        p == Process::At(Replica::R1) || p == Process::At(Replica::R2) || p == Process::SecondClient
    }

    }
}
// END MODULE: protocol

// BEGIN MODULE: async_messages
pub mod async_messages {
    // A send proposes a message, including its application-supplied ID. Only
    // the scheduler selects a queue occurrence for delivery.
    use vstd::prelude::*;
    use crate::checkpoint::Wire;
    use crate::delivery::{Action, Packet, Path, Process, enabled, live, process_step};
    use crate::first_assembly as asm;
    use crate::first_splice::{Observation, slot};
    use crate::guarded_comparison::weak_work;
    use crate::independent_read::{self as read, State};
    use crate::native_fork as native;
    use crate::protocol::LocalProtocol;
    use crate::read_call::{Event, Net, Program};

    verus! {

    pub struct Message { pub id: nat, pub body: Packet<Wire> }
    pub enum Command { Send(Message), Deliver(nat), Other(Event) }

    // A representation of (message ID, occurrence) in the existing nat-keyed
    // queue. Every ID has arbitrarily many representations. Finite overrides
    // allow the existing workload prefix to carry any chosen application IDs.
    pub type Headers = Map<nat, spec_fn(Packet<Wire>) -> nat>;

    pub closed spec fn unpack(h: nat) -> nat
        decreases h,
    {
        if h % 2 == 0 { h / 2 } else { unpack(h / 2) }
    }

    pub open spec fn message(headers: Headers, h: nat, body: Packet<Wire>) -> Message {
        Message { id: if headers.contains_key(h) { (headers[h])(body) } else { unpack(h) }, body }
    }

    pub open spec fn queue(headers: Headers, n: Net) -> Map<nat, Message> {
        Map::new(n.pending.dom(), |h: nat| message(headers, h, n.pending[h]))
    }

    proof fn above(set: Set<nat>) -> (n: nat)
        ensures forall|i: nat| #[trigger] set.contains(i) ==> i < n,
        decreases set.len(),
    {
        if set.is_empty() { 0 } else {
            let h = set.choose();
            let b = above(set.remove(h));
            b + h + 1
        }
    }

    proof fn encode_above(id: nat, bound: nat) -> (h: nat)
        ensures h >= bound, unpack(h) == id,
        decreases bound,
    {
        if bound == 0 { 2 * id } else {
            let j = encode_above(id, (bound - 1) as nat);
            let h = 2 * j + 1;
            assert(h / 2 == j && h % 2 == 1);
            h
        }
    }

    // The program uses the original callback data types. Their message number
    // now comes from the payload for both the send and the actual receipt.
    pub open spec fn callback(headers: Headers, e: Observation) -> Observation {
        Observation { action: match e.action {
            Action::Send(h, p) => Action::Send(message(headers, h, p).id, p),
            Action::Deliver(h) if e.incoming.is_some() =>
                Action::Deliver(message(headers, h, e.incoming.unwrap()).id),
            _ => e.action,
        }, ..e }
    }

    pub open spec fn implementation<S>(headers: Headers, p: Program<S>) -> Program<S> {
        LocalProtocol { initial: p.initial, done: p.done,
            accept: |s: S, e: Observation| (p.accept)(s, callback(headers, e)),
            update: |s: S, e: Observation| (p.update)(s, callback(headers, e)) }
    }

    pub open spec fn command(headers: Headers, a: Event) -> Command {
        match a {
            Action::Send(h, p) => Command::Send(message(headers, h, p)),
            Action::Deliver(h) => Command::Deliver(h),
            _ => Command::Other(a),
        }
    }

    // Independent store specification. Its entries carry the complete public
    // message. In particular, receipt chooses h but passes msg.id to the code.
    pub open spec fn public_input(n: Net, packets: Map<nat, Message>, c: Command) -> Observation {
        match c {
            Command::Send(msg) => process_step(n, Action::Send(msg.id, msg.body)),
            Command::Deliver(h) => {
                let msg = packets[h]; let actor = msg.body.to;
                Observation { actor, action: Action::Deliver(msg.id), incoming: Some(msg.body),
                    own_local: match actor { Process::At(r) => Some((n.locals)(r)), _ => None } }
            },
            Command::Other(a) => process_step(n, a),
        }
    }

    pub open spec fn permitted<S>(p: Program<S>, x: State<S>, packets: Map<nat, Message>, c: Command, quiet: bool) -> bool {
        let n = x.cfg.net;
        let e = public_input(n, packets, c);
        let accepts = (p.accept)((x.cfg.private)(e.actor), e);
        (!quiet || !weak_work(e)) && match c {
            Command::Send(msg) => live(n, msg.body.from)
                && (msg.body.path != Path::FirstReadReply || msg.body.to == Process::FirstClient)
                && read::initial_send(x, Action::Send(msg.id, msg.body)) && accepts,
            Command::Deliver(h) => packets.contains_key(h) && live(n, packets[h].body.to) && accepts,
            Command::Other(a) => slot(a).is_none() && match a {
                Action::CrashR3 => enabled(n, a) && n.unavailable.is_none(),
                Action::StartSecondClient => !n.second_started && accepts,
                _ => enabled(n, a) && accepts,
            },
        }
    }

    pub open spec fn input(headers: Headers, n: Net, c: Command) -> Observation {
        public_input(n, queue(headers, n), c)
    }
    pub open spec fn ready<S>(p: Program<S>, headers: Headers, x: State<S>, c: Command, quiet: bool) -> bool {
        permitted(p, x, queue(headers, x.cfg.net), c, quiet)
    }

    pub open spec fn allocatable<S>(x: State<S>, a: Event) -> bool {
        match a {
            Action::Send(h, _) => !x.cfg.net.pending.contains_key(h) && !x.reserved.contains(h) && read::names_sender(x, a),
            _ => true,
        }
    }

    // Exact guarded projection, with the actual post-queue and local update.
    pub proof fn project_step<S>(p: Program<S>, headers: Headers, x: State<S>, a: Event, quiet: bool)
        ensures ({
            let m = implementation(headers, p); let y = read::next(m, x, a);
            let c = command(headers, a); let e = input(headers, x.cfg.net, c);
            (native::step(m, quiet)(x, a, y) == (ready(p, headers, x, c, quiet) && allocatable(x, a)))
            && (native::step(m, quiet)(x, a, y) ==>
                e == callback(headers, process_step(x.cfg.net, a))
                && (y.cfg.private)(e.actor) == (p.update)((x.cfg.private)(e.actor), e)
                && queue(headers, y.cfg.net) == match a {
                    Action::Send(h, body) => queue(headers, x.cfg.net).insert(h, message(headers, h, body)),
                    Action::Deliver(h) => queue(headers, x.cfg.net).remove(h),
                    _ => queue(headers, x.cfg.net),
                })
        }),
    {
        let m = implementation(headers, p); let y = read::next(m, x, a);
        match a {
            Action::Send(h, body) => {
                assert(queue(headers, y.cfg.net) =~= queue(headers, x.cfg.net).insert(h, message(headers, h, body)));
            },
            Action::Deliver(h) => { assert(queue(headers, y.cfg.net) =~= queue(headers, x.cfg.net).remove(h)); },
            _ => { assert(queue(headers, y.cfg.net) =~= queue(headers, x.cfg.net)); },
        }
    }

    // A logical send has a real implementation outside ANY finite set of
    // handles. Receipts keep the selected occurrence, even if it is in avoid.
    pub proof fn realize_step<S>(p: Program<S>, headers: Headers, x: State<S>, c: Command, quiet: bool,
        avoid: Set<nat>) -> (a: Event)
        requires ready(p, headers, x, c, quiet),
        ensures ({
            let m = implementation(headers, p);
            command(headers, a) == c && !native::masks_send(avoid, a)
                && native::step(m, quiet)(x, a, read::next(m, x, a))
                && callback(headers, process_step(x.cfg.net, a)) == input(headers, x.cfg.net, c)
        }),
    {
        let a = match c {
            Command::Send(msg) => {
                let used = x.cfg.net.pending.dom().union(x.reserved).union(x.owners.dom()).union(headers.dom()).union(avoid);
                let bound = above(used);
                let h = encode_above(msg.id, bound);
                assert(!used.contains(h));
                Action::Send(h, msg.body)
            },
            Command::Deliver(h) => Action::Deliver(h),
            Command::Other(a) => a,
        };
        project_step(p, headers, x, a, quiet);
        a
    }

    pub open spec fn queue_after(q: Map<nat, Message>, c: Command, handle: nat) -> Map<nat, Message> {
        match c { Command::Send(msg) => q.insert(handle, msg), Command::Deliver(h) => q.remove(h), _ => q }
    }

    // Use the existing cell, client and process transitions for the selected
    // callback. All queued packets live in packets. The auxiliary State
    // carries only process state, liveness and invocation data across turns.
    pub struct Channel<S> { pub local: State<S>, pub packets: Map<nat, Message> }
    pub type Turn = (Command, nat); // The second component allocates a Send.

    pub open spec fn control<S>(x: State<S>) -> State<S> {
        State { owners: Map::empty(), reserved: Set::empty(),
            cfg: crate::ordinary_service::Configuration { net: Net { pending: Map::empty(), ..x.cfg.net }, ..x.cfg }, ..x }
    }
    pub open spec fn snapshot<S>(k: Headers, x: State<S>) -> Channel<S> {
        Channel { local: control(x), packets: queue(k, x.cfg.net) }
    }

    pub open spec fn apply_turn<S>(p: Program<S>, x: Channel<S>, t: Turn) -> Channel<S> {
        let e = public_input(x.local.cfg.net, x.packets, t.0);
        // Give the cell transition exactly the received body at the callback's
        // public ID. This temporary map describes one input to read::next.
        let incoming = match t.0 {
            Command::Deliver(h) => map![x.packets[h].id => x.packets[h].body],
            _ => Map::empty(),
        };
        let one = State { cfg: crate::ordinary_service::Configuration {
            net: Net { pending: incoming, ..x.local.cfg.net }, ..x.local.cfg }, ..x.local };
        Channel { local: control(read::next(p, one, e.action)), packets: queue_after(x.packets, t.0, t.1) }
    }

    pub open spec fn turn_enabled<S>(p: Program<S>, x: Channel<S>, t: Turn, original: bool) -> bool {
        (t.0 is Send ==> !x.packets.contains_key(t.1)) && if original && t.0 == Command::Other(Action::StopFirstClient) {
            !x.local.cfg.net.first_stopped && crate::first_mailbox::posted(p)(x.local)
        } else { permitted(p, x.local, x.packets, t.0, false) }
    }

    pub open spec fn printed(headers: Headers, a: Event) -> Turn {
        (command(headers, a), if a is Send { a->Send_0 } else { 0 })
    }

    pub open spec fn trace<S>(p: Program<S>, x: Channel<S>, turns: Seq<Turn>, original: bool) -> bool
        decreases turns.len(),
    {
        turns.len() == 0 || (turn_enabled(p, x, turns[0], original)
            && trace(p, apply_turn(p, x, turns[0]), turns.drop_first(), original))
    }
    pub open spec fn end<S>(p: Program<S>, x: Channel<S>, turns: Seq<Turn>) -> Channel<S>
        decreases turns.len(),
    {
        if turns.len() == 0 { x } else { end(p, apply_turn(p, x, turns[0]), turns.drop_first()) }
    }
    pub open spec fn turns(headers: Headers, s: Seq<Event>) -> Seq<Turn> {
        s.map_values(|a: Event| printed(headers, a))
    }

    pub open spec fn quiet_return<S>(p: Program<S>, res: spec_fn(S) -> Option<int>, x: Channel<S>, ts: Seq<Turn>) -> bool
        decreases ts.len(),
    {
        if ts.len() == 0 { read::returned(res)(x.local) } else {
            let (c, h) = ts[0];
            !read::returned(res)(x.local) && (c is Send ==> !x.packets.contains_key(h))
                && permitted(p, x.local, x.packets, c, true) && quiet_return(p, res, apply_turn(p, x, ts[0]), ts.drop_first())
        }
    }

    proof fn same_control_step<S>(p: Program<S>, k: Headers, x: State<S>, public: Channel<S>, c: Command,
        handle: nat, a: Event)
        requires public.local == control(x),
            callback(k, process_step(x.cfg.net, a)) == public_input(public.local.cfg.net, public.packets, c),
            match c {
                Command::Send(msg) => a is Send && message(k, a->Send_0, a->Send_1) == msg,
                Command::Deliver(h) => a is Deliver && public.packets.contains_key(h)
                    && queue(k, x.cfg.net).get(a->Deliver_0) == Some(public.packets[h]),
                Command::Other(event) => event == a && slot(event).is_none(),
            },
        ensures apply_turn(p, public, (c, handle)).local == control(read::next(implementation(k, p), x, a)),
    {
        let y = read::next(implementation(k, p), x, a); let v = apply_turn(p, public, (c, handle)).local;
        assert(v.cfg.private =~= y.cfg.private);
        assert(v.cfg.net.locals =~= y.cfg.net.locals);
    }

    pub proof fn project_prefix<S>(p: Program<S>, k: Headers, x: State<S>, s: Seq<Event>, original: bool,
        res: spec_fn(S) -> Option<int>)
        requires asm::prefix(implementation(k, p), x, s, original),
        ensures trace(p, snapshot(k, x), turns(k, s), original),
            end(p, snapshot(k, x), turns(k, s)) == snapshot(k, asm::drive(implementation(k, p), x, s)),
            quiet_return(p, res, snapshot(k, x), turns(k, s)) == native::completes(implementation(k, p), res, x, s, true),
        decreases s.len(),
    {
        if s.len() > 0 {
            let a = s[0]; let m = implementation(k, p); let y = read::next(m, x, a);
            let c = command(k, a); let t = printed(k, a); let initial = snapshot(k, x);
            if !original || a != Action::StopFirstClient { project_step(p, k, x, a, false); }
            project_step(p, k, x, a, true);
            assert(turn_enabled(p, initial, t, original));
            assert(public_input(initial.local.cfg.net, initial.packets, c) == callback(k, process_step(x.cfg.net, a)));
            same_control_step(p, k, x, initial, c, t.1, a);
            assert(apply_turn(p, initial, t).packets =~= queue(k, y.cfg.net));
            assert(turns(k, s).drop_first() =~= turns(k, s.drop_first()));
            project_prefix(p, k, y, s.drop_first(), original, res);
        }
    }

    }
}
// END MODULE: async_messages
