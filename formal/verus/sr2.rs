use vstd::prelude::*;
use crate::{Branch, Op, Replica, origin, legal, conditional_history_contradiction};
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::survivors::sr2_result;
use crate::transparency::{StrongEffect, permitted};

verus! {

// A fresh client queries the two live replicas. Selection may use the
// shared cell and the sending replica's own SR1 participation in each actual strong reply.
pub type Select = spec_fn(Report, Report) -> int;

pub struct Reader {
    pub prior: Control,
    pub asked: bool,
    pub r1: Option<Report>,
    pub r2: Option<Report>,
    pub returned: Option<int>,
}

pub open spec fn empty_exchange(prior: Control) -> Reader {
    Reader { prior, asked: false, r1: None, r2: None, returned: None }
}

pub open spec fn reader_at(b: Fork, p: Process) -> Reader {
    empty_exchange(checkpoint_control(b, p))
}

pub open spec fn report_from(p: Packet<Wire>, r: Replica) -> bool {
    p.path == Path::Strong && p.from == at(r) && p.to == Process::SecondClient
        && (p.input is Answer2)
}

pub open spec fn reports(s: Reader, r: Replica) -> Option<Report> {
    if r == Replica::R1 { s.r1 } else { s.r2 }
}

pub open spec fn read_update(s: Reader, e: ProcessStep<int, Wire>, select: Select) -> Reader {
    let next = Reader { prior: change_control(s.prior, e), ..s };
    match e.incoming {
        Some(p) => match p.input {
            Wire::Query2 if p.path == Path::Strong && p.from == Process::SecondClient =>
                Reader { asked: true, ..next },
            Wire::Answer2(v) if report_from(p, Replica::R1) => Reader { r1: Some(v), ..next },
            Wire::Answer2(v) if report_from(p, Replica::R2) => Reader { r2: Some(v), ..next },
            _ => next,
        },
        None if e.action == Action::Strong(Process::SecondClient) =>
            Reader { returned: Some(select(s.r1.unwrap(), s.r2.unwrap())), ..next },
        _ => next,
    }
}

pub open spec fn supports(learned: Option<Notice>, need: Notice) -> bool {
    learned == Some(need) || learned == Some(Notice::G)
}

pub open spec fn read_accept(
    s: Reader, e: ProcessStep<int, Wire>, gates: Set<Replica>, need: Notice,
) -> bool {
    match e.action {
        Action::Send(_, p) => match p.input {
            Wire::Answer2(v) => match p.from {
                Process::At(r) => r != Replica::R3 && report_from(p, r) && s.asked
                    && e.own_local == Some(v.value) && s.prior.answered_first == v.answered_first
                    && (!gates.contains(r) || supports(s.prior.learned, need)),
                _ => false,
            },
            _ => true,
        },
        Action::Strong(Process::SecondClient) => s.r1.is_some() && s.r2.is_some(),
        _ => true,
    }
}

// One machine starts before SR1 in both executions. All guards inspect
// local memory and the local event. Its policy is fixed across branches.
pub open spec fn read_protocol(gates: Set<Replica>, need: Notice, select: Select)
    -> LocalProtocol<Reader, int, Wire>
{
    LocalProtocol {
        initial: |p| empty_exchange(initial_control()),
        accept: |s: Reader, e| permits_step(s.prior, e) && read_accept(s, e, gates, need),
        update: |s, e| read_update(s, e, select),
        done: |s: Reader| s.prior.finished || s.returned.is_some(),
    }
}

pub open spec fn reader(b: Fork, gates: Set<Replica>, select: Select)
    -> LocalProtocol<Reader, int, Wire>
{
    LocalProtocol { initial: |p| reader_at(b, p), ..read_protocol(gates, b.notice, select) }
}

proof fn sr1_step_in_combined_machine(
    b: Fork, gates: Set<Replica>, select: Select, i: nat, s: Control,
)
    requires i < actions_to_crash(b).len(),
    ensures ({
        let e = checkpoint_observations(b)[i as int];
        let m = read_protocol(gates, b.notice, select);
        (m.accept)(empty_exchange(s), e) == permits_step(s, e)
            && (m.update)(empty_exchange(s), e) == empty_exchange(change_control(s, e))
    }),
{
    crate::checkpoint::prefix_index(i as int);
}

pub(crate) proof fn sr1_preserves_all_private_memory(
    b: Fork, gates: Set<Replica>, select: Select, p: Process, k: nat,
)
    requires k <= actions_to_crash(b).len(),
    ensures ({
        let obs = checkpoint_observations(b);
        memory(read_protocol(gates, b.notice, select), p, obs, k)
            == empty_exchange(memory(checkpoint_machine(), p, obs, k))
    }),
    decreases k,
{
    if k > 0 {
        let prev = (k - 1) as nat;
        sr1_preserves_all_private_memory(b, gates, select, p, prev);
        let obs = checkpoint_observations(b);
        sr1_step_in_combined_machine(b, gates, select, prev,
            memory(checkpoint_machine(), p, obs, prev));
    }
}

pub open spec fn resumes_actual_reader(b: Fork, gates: Set<Replica>, select: Select)
    -> bool
{
    let m = read_protocol(gates, b.notice, select);
    let obs = checkpoint_observations(b);
    finished_sr1(b) && accepted(m, obs) && resume_at(m, obs) == reader(b, gates, select)
        && memory(m, Process::FirstClient, obs, obs.len()).prior.finished
        && memory(m, Process::FirstClient, obs, obs.len()).prior.reply == Some(first_value(b))
}

pub proof fn fresh_reader_resumes_actual_sr1_state(b: Fork, gates: Set<Replica>, select: Select)
    ensures resumes_actual_reader(b, gates, select),
{
    hide(memory);
    let m = read_protocol(gates, b.notice, select);
    let prior = checkpoint_machine();
    let obs = checkpoint_observations(b);
    both_prefixes_are_enabled_and_client_finishes(b);
    assert forall|i: int| 0 <= i < obs.len() implies {
        let e = #[trigger] obs[i]; (m.accept)(memory(m, e.actor, obs, i as nat), e)
    } by {
        let e = obs[i];
        let s = memory(prior, e.actor, obs, i as nat);
        assert((prior.accept)(s, e));
        sr1_step_in_combined_machine(b, gates, select, i as nat, s);
        sr1_preserves_all_private_memory(b, gates, select, e.actor, i as nat);
    }
    let resumed = resume_at(m, obs);
    let actual = reader(b, gates, select);
    assert(resumed.initial =~= actual.initial) by {
        assert forall|p: Process| #[trigger] (resumed.initial)(p) == (actual.initial)(p) by {
            sr1_preserves_all_private_memory(b, gates, select, p, obs.len());
        }
    }
    sr1_preserves_all_private_memory(b, gates, select, Process::FirstClient, obs.len());
}

pub proof fn combined_reader_supplies_sr1_sample(b: Fork, gates: Set<Replica>, select: Select)
    ensures completed_quorum_sample(read_protocol(gates, b.notice, select), |s: Reader| s.prior.reply.unwrap(), b),
{
    fresh_reader_resumes_actual_sr1_state(b, gates, select);
    let m = read_protocol(gates, b.notice, select); let c = Process::FirstClient;
    assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m, b, k)) by {
        sr1_preserves_all_private_memory(b, gates, select, c, k);
        prefix_memory_tracks_actual_messages(b, c, k);
    }
    sr1_preserves_all_private_memory(b, gates, select, c, 13);
    sr1_preserves_all_private_memory(b, gates, select, c, 14);
    prefix_memory_tracks_actual_messages(b, c, 13);
    prefix_memory_tracks_actual_messages(b, c, 14);
    assert(crate::first_quorum(b.branch).contains(origin(b.branch)));
    assert(during_sr1(b, 10, origin(b.branch)) == first_value(b));
}

pub open spec fn query_packet(r: Replica) -> Packet<Wire> {
    Packet { path: Path::Strong, from: Process::SecondClient, to: at(r), input: Wire::Query2 }
}

pub open spec fn queries() -> Seq<Action<Wire>> {
    seq![Action::Send(11, query_packet(Replica::R1)), Action::Send(12, query_packet(Replica::R2)),
        Action::Deliver(11), Action::Deliver(12)]
}

pub open spec fn answer_packet(r: Replica, value: Report) -> Packet<Wire> {
    Packet { path: Path::Strong, from: at(r), to: Process::SecondClient, input: Wire::Answer2(value) }
}

pub open spec fn reply_action(r: Replica, value: Report) -> Action<Wire> {
    Action::Send(if r == Replica::R1 { 13 } else { 14 }, answer_packet(r, value))
}

pub open spec fn report(b: Fork, r: Replica) -> Report {
    Report { value: (checkpoint_end(b).locals)(r),
        answered_first: checkpoint_control(b, at(r)).answered_first }
}

pub open spec fn completed_actions(b: Fork) -> Seq<Action<Wire>> {
    queries() + seq![reply_action(Replica::R1, report(b, Replica::R1)),
        reply_action(Replica::R2, report(b, Replica::R2)), Action::Deliver(13),
        Action::Deliver(14), Action::Strong(Process::SecondClient)]
}

pub open spec fn exchange_actions(b: Fork, full: bool) -> Seq<Action<Wire>> {
    if full { completed_actions(b) } else { queries() }
}

// The SR2 exchange uses four fresh slots. Every older packet remains
// queued; trace checking verifies that no slot is overwritten.
pub open spec fn exchange_net(b: Fork, k: nat) -> Network<int, Wire> {
    let start = checkpoint_end(b);
    let p = start.pending;
    let p = if 1 <= k < 3 { p.insert(11, query_packet(Replica::R1)) } else { p };
    let p = if 2 <= k < 4 { p.insert(12, query_packet(Replica::R2)) } else { p };
    let p = if 5 <= k < 7 {
        p.insert(13, answer_packet(Replica::R1, report(b, Replica::R1)))
    } else { p };
    let p = if 6 <= k < 8 {
        p.insert(14, answer_packet(Replica::R2, report(b, Replica::R2)))
    } else { p };
    Network { pending: p, ..start }
}

pub open spec fn exchange_states(b: Fork, full: bool) -> Seq<Network<int, Wire>> {
    Seq::new(exchange_actions(b, full).len() + 1, |i: int| exchange_net(b, i as nat))
}

// Complete traffic accounting for either finite continuation: the pending
// wait witness ends after the queries, the return witness includes the replies.
pub open spec fn second_round_requests(b: Fork, full: bool) -> bool {
    let a = exchange_actions(b, full);
    let s = exchange_states(b, full);
    let e = observations(s, a);
    second_invocation(s, a)
        && invocation_only(a, Process::FirstClient, Set::empty())
        && e[2].actor == at(Replica::R1) && e[2].incoming == Some(query_packet(Replica::R1))
        && e[3].actor == at(Replica::R2) && e[3].incoming == Some(query_packet(Replica::R2))
        && (full ==> e[6].incoming == Some(answer_packet(Replica::R1, report(b, Replica::R1)))
            && e[7].incoming == Some(answer_packet(Replica::R2, report(b, Replica::R2))))
        && forall|k: int, id: nat| 0 <= k <= a.len() && delayed_slots().contains(id)
            ==> #[trigger] packet_at(s[k], id) == packet_at(checkpoint_end(b), id)
}

pub proof fn only_initial_sr2_requests_are_sent(b: Fork, full: bool)
    ensures second_round_requests(b, full),
{
    let a = exchange_actions(b, full);
    let c = Process::SecondClient;
    assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
        Action::Send(_, p) if p.from == c => invocation_packet(p) && live_pair().contains(p.to->At_0)
            && (forall|j: int| 0 <= j < i ==> !client_sends_to(#[trigger] a[j], c, p.to->At_0)),
        _ => true,
    } by {
        exchange_index(i);
        if let Action::Send(_, p) = a[i] {
            if p.from == c {
                assert forall|j: int| 0 <= j < i implies !client_sends_to(#[trigger] a[j], c, p.to->At_0)
                    by { exchange_index(j); }
            }
        }
    }
    assert forall|r: Replica| #[trigger] live_pair().contains(r) implies
        exists|i: int| 0 <= i < a.len() && client_sends_to(#[trigger] a[i], c, r) by {
        let i: int = if r == Replica::R1 { 0 } else { 1 };
        assert(client_sends_to(a[i], c, r));
    }
    let es = observations(exchange_states(b, full), a);
    assert forall|i: int, j: int| 0 <= j < i < es.len() implies match (#[trigger] es[i]).action {
        Action::Send(_, p) if p.from == c => (#[trigger] es[j]).actor != c || es[j].incoming.is_none(),
        _ => true,
    } by { exchange_index(i); exchange_index(j); }
    assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
        Action::Send(_, p) => p.from != Process::FirstClient,
        _ => true,
    } by { exchange_index(i); }
}

pub open spec fn exchange_memory(b: Fork, select: Select, p: Process, k: nat) -> Reader {
    let one = report(b, Replica::R1);
    let two = report(b, Replica::R2);
    let client = p == Process::SecondClient;
    Reader {
        asked: (p == at(Replica::R1) && k >= 3) || (p == at(Replica::R2) && k >= 4),
        r1: if client && k >= 7 { Some(one) } else { None },
        r2: if client && k >= 8 { Some(two) } else { None },
        returned: if client && k >= 9 { Some(select(one, two)) } else { None },
        prior: if client && k >= 1 {
            Control { sent_requests: if k >= 2 { set![Replica::R1, Replica::R2] } else { set![Replica::R1] },
                ..checkpoint_control(b, p) }
        } else { checkpoint_control(b, p) },
    }
}

proof fn exchange_index(i: int)
    requires 0 <= i < 9,
    ensures i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5
        || i == 6 || i == 7 || i == 8,
{}

pub(crate) proof fn exchange_tracks_private_memory(
    b: Fork, gates: Set<Replica>, select: Select, full: bool, p: Process, k: nat,
)
    requires k <= exchange_actions(b, full).len(),
    ensures memory(reader(b, gates, select), p,
        observations(exchange_states(b, full), exchange_actions(b, full)), k)
            == exchange_memory(b, select, p, k),
    decreases k,
{
    prefix_memory_tracks_actual_messages(b, Process::SecondClient, actions_to_crash(b).len());
    if k > 0 {
        let prev = (k - 1) as nat;
        exchange_tracks_private_memory(b, gates, select, full, p, prev);
        exchange_index(prev as int);
    }
}

proof fn exchange_is_enabled(
    b: Fork, gates: Set<Replica>, select: Select, full: bool,
)
    requires full ==> !gates.contains(Replica::R1) && !gates.contains(Replica::R2),
    ensures ({
        let s = exchange_states(b, full);
        let a = exchange_actions(b, full);
        s[0] == checkpoint_end(b) && trace(|x, i| cell(x, i), s, a)
            && accepted(reader(b, gates, select), observations(s, a))
    }),
{
    let s = exchange_states(b, full);
    let a = exchange_actions(b, full);
    let m = reader(b, gates, select);
    let obs = observations(s, a);
    prefix_memory_tracks_actual_messages(b, Process::SecondClient, actions_to_crash(b).len());
    assert forall|i: int| 0 <= i < a.len() implies {
        let step = #[trigger] a[i];
        enabled(s[i], step) && s[i + 1] == advance(|x, z| cell(x, z), s[i], step)
    } by {
        exchange_index(i);
        let next = advance(|x, z| cell(x, z), s[i], a[i]);
        assert(next.pending =~= s[i + 1].pending);
        assert(next.locals =~= s[i + 1].locals);
    }
    assert forall|i: int| 0 <= i < obs.len() implies {
        let e = #[trigger] obs[i]; (m.accept)(memory(m, e.actor, obs, i as nat), e)
    } by {
        exchange_index(i);
        exchange_tracks_private_memory(b, gates, select, full, obs[i].actor, i as nat);
    }
}

pub proof fn queries_reach_both_survivors(b: Fork, gates: Set<Replica>, select: Select)
    ensures ({
        let actions = queries();
        let s = exchange_states(b, false);
        let events = observations(s, actions);
        let m = reader(b, gates, select);
        trace(|x, i| cell(x, i), s, actions) && accepted(m, events)
            && packet_at(s[4], 2) == Some(packet_for(b, 2))
            && survivor(s[4]) == (2int, 5int)
            && (forall|r: Replica| r != Replica::R3 ==> {
                let local = #[trigger] memory(m, at(r), events, 4);
                local.asked && local.prior == checkpoint_control(b, at(r))
                    && local.prior.learned.is_none()
            })
            && sr2_result(m, |s: Reader| s.returned, events).is_none()
    }),
{
    exchange_is_enabled(b, gates, select, false);
    let m = reader(b, gates, select);
    let events = observations(exchange_states(b, false), queries());
    assert forall|r: Replica| r != Replica::R3 implies {
        let local = #[trigger] memory(m, at(r), events, 4);
        local.asked && local.prior == checkpoint_control(b, at(r))
            && local.prior.learned.is_none()
    } by {
        exchange_tracks_private_memory(b, gates, select, false, at(r), 4);
        prefix_memory_tracks_actual_messages(b, at(r), actions_to_crash(b).len());
    }
    exchange_tracks_private_memory(b, gates, select, false, Process::SecondClient, 4);
}

pub proof fn ordinary_quorum_can_return(b: Fork, gates: Set<Replica>, select: Select)
    requires !gates.contains(Replica::R1), !gates.contains(Replica::R2),
    ensures ({
        let a = completed_actions(b);
        let s = exchange_states(b, true);
        let obs = observations(s, a);
        let m = reader(b, gates, select);
        returned_on_exchange(b, gates, select,
            select(report(b, Replica::R1), report(b, Replica::R2)))
            && memory(m, Process::SecondClient, obs, 8).returned.is_none()
            && (m.accept)(memory(m, Process::SecondClient, obs, 8), obs[8])
    }),
{
    hide(memory);
    hide(checkpoint_control);
    let a = completed_actions(b);
    let s = exchange_states(b, true);
    let obs = observations(s, a);
    let m = reader(b, gates, select);
    assert(obs.len() == 9);
    only_initial_sr2_requests_are_sent(b, true);
    release_notice_in_one_finite_step(b, 9);
    exchange_is_enabled(b, gates, select, true);
    exchange_tracks_private_memory(b, gates, select, true, Process::SecondClient, 8);
    exchange_tracks_private_memory(b, gates, select, true, Process::SecondClient, 9);
    assert(obs[8].actor == Process::SecondClient);
    assert((m.accept)(memory(m, obs[8].actor, obs, 8), obs[8]));
    assert(memory(m, Process::SecondClient, obs, 9)
        == exchange_memory(b, select, Process::SecondClient, 9));
}

// A local control-dependence test. The ordinary strong action and all
// of its inputs are fixed. Only receipt of the genuine weak status
// notice is varied. Necessity of this responder is proved separately.
pub open spec fn notice_unlocks<S>(
    m: LocalProtocol<S, int, Wire>, local: S,
    delivery: ProcessStep<int, Wire>, ordinary: ProcessStep<int, Wire>,
) -> bool {
    delivery.actor == ordinary.actor && delivery.incoming.is_some()
        && notice_to(delivery.incoming.unwrap(), ordinary.actor)
        && delivery.own_local == ordinary.own_local
        && !(m.accept)(local, ordinary) && (m.accept)((m.update)(local, delivery), ordinary)
}

// A one-delivery extension of either finite witness. Remaining packets
// target R3 or the quiescent C1. This is a transport suffix, not a claim
// about infinite process fairness or future protocol work.
pub open spec fn may_receive_notice(s: Reader, event: ProcessStep<int, Wire>,
    gates: Set<Replica>, n: Notice) -> bool
{
    permits_step(s.prior, event) && read_accept(s, event, gates, n)
}

pub open spec fn notice_drains_live_backlog(b: Fork, net: Network<int, Wire>) -> bool {
    let ack = Action::Deliver(2);
    let next = advance(|x, i| cell(x, i), net, ack);
    packet_at(net, 2) == Some(packet_for(b, 2)) && enabled(net, ack)
        && (forall|s: Reader, gates: Set<Replica>|
            #[trigger] may_receive_notice(s, process_step(net, ack), gates, b.notice))
        && next.first_stopped && next.r3_crashed && next.unavailable.is_none() && next.second_started
        && forall|id: nat| #[trigger] next.pending.contains_key(id) ==> !live(next, next.pending[id].to)
}

pub proof fn release_notice_in_one_finite_step(b: Fork, k: nat)
    requires k == 4 || k == 9,
    ensures notice_drains_live_backlog(b, exchange_net(b, k)),
{
    let net = exchange_net(b, k);
    let next = advance(|x, i| cell(x, i), net, Action::Deliver(2));
    assert forall|id: nat| #[trigger] next.pending.contains_key(id) implies
        !live(next, next.pending[id].to) by {
        assert(id == 0 || id == 1 || id == 6 || id == 7);
    }
}

pub open spec fn pivotal_at_survivor(b: Fork, gates: Set<Replica>, select: Select)
    -> bool
{
    let r = origin(b.branch);
    let m = reader(b, gates, select);
    let q = exchange_states(b, false);
    let pre = q[4];
    let ack = Action::Deliver(2);
    let reply = reply_action(r, report(b, r));
    let seen = observations(q, queries());
    let state = memory(m, at(r), seen, seen.len());
    let receipt = process_step(pre, ack);
    let post = advance(|x, i| cell(x, i), pre, ack);
    notice_drains_live_backlog(b, pre) && enabled(pre, ack)
        && (m.accept)(state, receipt) && enabled(pre, reply) && enabled(post, reply)
        && receipt.incoming == Some(packet_for(b, 2))
        && process_step(pre, reply) == process_step(post, reply)
        && notice_unlocks(m, state, receipt, process_step(pre, reply))
}

pub proof fn actual_weak_notice_enables_the_same_strong_reply(
    b: Fork, gates: Set<Replica>, select: Select,
)
    requires gates.contains(origin(b.branch)),
    ensures pivotal_at_survivor(b, gates, select),
{
    queries_reach_both_survivors(b, gates, select);
    release_notice_in_one_finite_step(b, 4);
    let q = exchange_states(b, false);
    let r = origin(b.branch);
    let m = reader(b, gates, select);
    let obs = observations(q, queries());
    let local = memory(m, at(r), obs, 4);
    assert(local.asked && local.prior == checkpoint_control(b, at(r)));
}

// Three local protocol facts suffice to establish that the guarded step
// cannot be bypassed. The projection functions may inspect arbitrary
// private memory. Other strong messages, timers and steps are unrestricted.
#[verifier::reject_recursive_types(S)]
pub struct ReplyChain<S> {
    pub knows: spec_fn(S) -> bool,
    pub has_reply: spec_fn(S) -> bool,
    pub finished: spec_fn(S) -> bool,
}

pub open spec fn confirms(p: Packet<Wire>, r: Replica, need: Notice) -> bool {
    notice_to(p, at(r)) && match p.input {
        Wire::WeakConfirm(n) => supports(Some(n), need),
        _ => false,
    }
}

pub open spec fn permission_from_r3(r: Replica, need: Notice) -> spec_fn(Packet<Wire>) -> bool {
    |p| confirms(p, r, need)
}

pub open spec fn follows_reply_chain<S>(
    m: LocalProtocol<S, int, Wire>, c: ReplyChain<S>, r: Replica, grants: spec_fn(Packet<Wire>) -> bool,
    s: S, e: ProcessStep<int, Wire>,
) -> bool {
    let next = (m.update)(s, e);
    let incoming = e.incoming;
    (m.accept)(s, e) ==> (
        (e.actor == at(r) ==> (
            (!(c.knows)(s) && (c.knows)(next) ==>
                incoming.is_some() && grants(incoming.unwrap()))
            && (match e.action {
                Action::Send(_, p) if report_from(p, r) => (c.knows)(s),
                _ => true,
            })
        )) && (e.actor == Process::SecondClient ==> (
            (!(c.has_reply)(s) && (c.has_reply)(next) ==>
                incoming.is_some() && report_from(incoming.unwrap(), r))
            && (!(c.finished)(s) && (c.finished)(next) ==> (c.has_reply)(s) || (c.has_reply)(next))
        ))
    )
}

pub open spec fn chain_for(r: Replica, n: Notice) -> ReplyChain<Reader> {
    ReplyChain {
        knows: |s: Reader| supports(s.prior.learned, n),
        has_reply: |s: Reader| reports(s, r).is_some(),
        finished: |s: Reader| s.returned.is_some(),
    }
}

pub proof fn guarded_reader_obeys_reply_chain(
    b: Fork, gates: Set<Replica>, select: Select, r: Replica,
)
    requires r != Replica::R3, gates.contains(r),
    ensures forall|s: Reader, e: ProcessStep<int, Wire>|
        #[trigger] follows_reply_chain(reader(b, gates, select),
            chain_for(r, b.notice), r, permission_from_r3(r, b.notice), s, e),
{}

pub open spec fn got_permission(
    event: ProcessStep<int, Wire>, r: Replica, grants: spec_fn(Packet<Wire>) -> bool,
) -> bool {
    event.actor == at(r) && event.incoming.is_some() && grants(event.incoming.unwrap())
}

// Causality for any supplied permission-packet predicate, including
// alternate routes and duplicate packets. The network condition concerns
// actual observations. It says nothing about which packets can be delayed.
pub proof fn no_response_before_permission<S>(
    update: spec_fn(int, Wire) -> int, m: LocalProtocol<S, int, Wire>,
    c: ReplyChain<S>, r: Replica, grants: spec_fn(Packet<Wire>) -> bool,
    states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>, k: nat,
)
    requires
        r != Replica::R3, trace(update, states, actions), k <= actions.len(),
        accepted(m, observations(states, actions)),
        forall|id: nat| #[trigger] states[0].pending.contains_key(id) ==> !report_from(states[0].pending[id], r),
        !(c.knows)((m.initial)(at(r))),
        !(c.has_reply)((m.initial)(Process::SecondClient)), !(c.finished)((m.initial)(Process::SecondClient)),
        forall|s: S, e: ProcessStep<int, Wire>| crate::confirmation::transport_event(e) ==> #[trigger] follows_reply_chain(m, c, r, grants, s, e),
        forall|i: int| 0 <= i < k ==> !got_permission(#[trigger] observations(states, actions)[i], r, grants),
    ensures ({
        let events = observations(states, actions);
        let client = memory(m, Process::SecondClient, events, k);
        let net = states[k as int];
        (forall|id: nat| #[trigger] net.pending.contains_key(id) ==> !report_from(net.pending[id], r))
            && !(c.knows)(memory(m, at(r), events, k)) && !(c.has_reply)(client) && !(c.finished)(client)
    }),
    decreases k,
{
    if k > 0 {
        let i = (k - 1) as nat;
        no_response_before_permission(update, m, c, r, grants, states, actions, i);
        let pre = states[i as int];
        let post = states[k as int];
        let events = observations(states, actions);
        let action = actions[i as int];
        let e = events[i as int];
        let local = memory(m, e.actor, events, i);
        assert(e == process_step(pre, action) && !got_permission(e, r, grants));
        assert(enabled(pre, action) && post == advance(update, pre, action));
        assert((m.accept)(local, e));
        assert(crate::confirmation::transport_event(e)) by { assert(enabled(pre, e.action) && process_step(pre,e.action)==e); }
        assert(follows_reply_chain(m, c, r, grants, local, e));
        match action {
            Action::Deliver(id) => {
                assert(pre.pending.contains_key(id) && !report_from(pre.pending[id], r));
            },
            Action::Send(_, p) if report_from(p, r) => {
                assert(e.actor == at(r) && !(c.knows)(local));
                assert(false);
            },
            _ => {},
        }
        assert forall|id: nat| #[trigger] post.pending.contains_key(id) implies
            !report_from(post.pending[id], r) by {
            match action {
                Action::Send(j, p) if j == id => { assert(post.pending[id] == p); },
                _ => { assert(pre.pending.contains_key(id) && post.pending[id] == pre.pending[id]); },
            }
        }
    }
}

pub open spec fn skips_delivery(action: Action<Wire>, held: Set<nat>) -> bool {
    match action { Action::Deliver(id) => !held.contains(id), _ => true }
}

// Transport supplies the missing input for the actual R3 notice. All
// matching queued packets must be in the designated slots. A new R3
// packet cannot appear after its crash. Other strong deliveries can run.
pub proof fn held_r3_notices_are_unseen(
    update: spec_fn(int, Wire) -> int, r: Replica, need: Notice, held: Set<nat>,
    states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>, k: nat,
)
    requires
        trace(update, states, actions), k <= actions.len(), states[0].r3_crashed,
        forall|id: nat| #[trigger] states[0].pending.contains_key(id)
            && confirms(states[0].pending[id], r, need) ==> held.contains(id),
        forall|i: int| 0 <= i < k ==> skips_delivery(#[trigger] actions[i], held),
    ensures ({
        let net = states[k as int];
        let obs = observations(states, actions);
        net.r3_crashed
            && (forall|id: nat| #[trigger] net.pending.contains_key(id)
                && confirms(net.pending[id], r, need) ==> held.contains(id))
            && (forall|i: int| 0 <= i < k ==> !got_permission(#[trigger] obs[i], r, permission_from_r3(r, need)))
    }),
    decreases k,
{
    if k > 0 {
        let i = (k - 1) as nat;
        held_r3_notices_are_unseen(update, r, need, held, states, actions, i);
        let pre = states[i as int];
        let post = states[k as int];
        let action = actions[i as int];
        assert(enabled(pre, action) && post == advance(update, pre, action));
        match action {
            Action::Deliver(id) => {
                assert(skips_delivery(actions[i as int], held));
                assert(!held.contains(id));
                assert(pre.pending.contains_key(id) && !confirms(pre.pending[id], r, need));
            },
            Action::Send(_, p) => { assert(p.from != at(Replica::R3)); },
            _ => {},
        }
        assert forall|id: nat| #[trigger] post.pending.contains_key(id)
            && confirms(post.pending[id], r, need) implies held.contains(id) by {
            match action {
                Action::Send(j, p) if j == id => { assert(post.pending[id] == p); },
                _ => { assert(pre.pending.contains_key(id) && post.pending[id] == pre.pending[id]); },
            }
        }
        let obs = observations(states, actions);
        assert(obs[i as int] == process_step(pre, action));
        assert(!got_permission(obs[i as int], r, permission_from_r3(r, need)));
    }
}

pub open spec fn cell_trace(states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>) -> bool {
    trace(|x, i| cell(x, i), states, actions)
}

pub open spec fn no_bypass(b: Fork, gates: Set<Replica>, select: Select) -> bool {
    let m = reader(b, gates, select);
    forall|states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>|
        #[trigger] cell_trace(states, actions)
            && states[0] == checkpoint_end(b) && accepted(m, observations(states, actions))
            && (forall|i: int| 0 <= i < actions.len() ==>
                #[trigger] actions[i] != Action::<Wire>::Deliver(2))
        ==> sr2_result(m, |s: Reader| s.returned, observations(states, actions)).is_none()
}

pub proof fn no_strong_detour_around_gate(b: Fork, gates: Set<Replica>, select: Select)
    requires gates.contains(origin(b.branch)),
    ensures no_bypass(b, gates, select),
{
    hide(memory);
    hide(trace);
    hide(accepted);
    hide(follows_reply_chain);
    hide(got_permission);
    let m = reader(b, gates, select);
    let r = origin(b.branch);
    let c = chain_for(r, b.notice);
    let start = checkpoint_end(b);
    copies_and_knowledge_at_checkpoint(b, seq![]);
    assert(!(c.knows)((m.initial)(at(r))) && !(c.has_reply)((m.initial)(Process::SecondClient))
        && !(c.finished)((m.initial)(Process::SecondClient)));
    guarded_reader_obeys_reply_chain(b, gates, select, r);
    assert forall|id: nat| #[trigger] start.pending.contains_key(id) implies
        !report_from(start.pending[id], r) && (confirms(start.pending[id], r, b.notice) ==> id == 2)
        by {};
    assert forall|states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>|
        #[trigger] cell_trace(states, actions)
            && states[0] == start && accepted(m, observations(states, actions))
            && (forall|i: int| 0 <= i < actions.len() ==>
                #[trigger] actions[i] != Action::<Wire>::Deliver(2))
        implies sr2_result(m, |s: Reader| s.returned, observations(states, actions)).is_none()
        by {
            let held = set![2nat];
            assert forall|i: int| 0 <= i < actions.len() implies skips_delivery(#[trigger] actions[i], held) by {
                assert(actions[i] != Action::<Wire>::Deliver(2));
            }
            held_r3_notices_are_unseen(|x, i| cell(x, i), r, b.notice, held, states, actions, actions.len());
            no_response_before_permission(|x, i| cell(x, i), m, c, r, permission_from_r3(r, b.notice),
                states, actions, actions.len());
        }
}

// Apply this local no-await test to a mandatory reply. It examines the
// transition guard and the received packet. It has no history, G bit,
// branch, eventual-completion predicate or selected value as input.
pub open spec fn required_reply_effect<S>(
    m: LocalProtocol<S, int, Wire>, local: S, receipt: ProcessStep<int, Wire>,
    reply: ProcessStep<int, Wire>, r: Replica,
) -> StrongEffect<Op> {
    match reply.action {
        Action::Send(_, p) if r != Replica::R3 && report_from(p, r)
            && notice_unlocks(m, local, receipt, reply) =>
            StrongEffect::AwaitWeak(if r == Replica::R1 { Op::W1 } else { Op::W2 }),
        _ => StrongEffect::StrongOnly,
    }
}

pub open spec fn effect_at_reply(b: Fork, gates: Set<Replica>, select: Select)
    -> StrongEffect<Op>
{
    let r = origin(b.branch);
    let m = reader(b, gates, select);
    let q = exchange_states(b, false);
    let obs = observations(q, queries());
    required_reply_effect(m, memory(m, at(r), obs, obs.len()), process_step(q[4], Action::Deliver(2)),
        process_step(q[4], reply_action(r, report(b, r))), r)
}

pub open spec fn witnessed_weak_wait(b: Fork, gates: Set<Replica>, select: Select)
    -> bool
{
    let q = exchange_states(b, false);
    let m = reader(b, gates, select);
    let obs = observations(q, queries());
    let effect = effect_at_reply(b, gates, select);
    cell_trace(q, queries()) && q[0] == checkpoint_end(b) && accepted(m, obs)
        && second_round_requests(b, false) && sr2_result(m, |s: Reader| s.returned, obs).is_none()
        && pivotal_at_survivor(b, gates, select) && no_bypass(b, gates, select)
        && effect == StrongEffect::AwaitWeak(observed_writer(b)) && !permitted(effect)
}

pub proof fn gated_reply_violates_no_await(b: Fork, gates: Set<Replica>, select: Select)
    requires gates.contains(origin(b.branch)),
    ensures witnessed_weak_wait(b, gates, select),
{
    hide(memory);
    only_initial_sr2_requests_are_sent(b, false);
    queries_reach_both_survivors(b, gates, select);
    actual_weak_notice_enables_the_same_strong_reply(b, gates, select);
    no_strong_detour_around_gate(b, gates, select);
}

pub open spec fn returned_on_exchange(b: Fork, gates: Set<Replica>, select: Select, v: int)
    -> bool
{
    let s = exchange_states(b, true);
    let a = completed_actions(b);
    let m = reader(b, gates, select);
    let obs = observations(s, a);
    s[0] == checkpoint_end(b) && cell_trace(s, a) && accepted(m, obs)
        && second_round_requests(b, true) && sr2_result(m, |x: Reader| x.returned, obs) == Some(v)
        && notice_drains_live_backlog(b, s[9])
}

// One fixed reader and one gate policy in both real branches. A gate at
// R2 has a real queued witness in alpha, a gate at R1 has one in beta.
// No branch is required to complete to prove the wait arm.
pub proof fn paired_read_or_confirmation_wait(
    n: Notice, gates: Set<Replica>, select: Select, assigned_alpha: bool, assigned_beta: bool,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>,
)
    requires n != Notice::Replication ==> assigned_alpha && assigned_beta,
    ensures
        first_round(alpha(n)), first_round(beta(n)),
        truthful_notice(alpha(n), weak_assignment(alpha(n), assigned_alpha).ops),
        truthful_notice(beta(n), weak_assignment(beta(n), assigned_beta).ops),
        resumes_actual_reader(alpha(n), gates, select) && resumes_actual_reader(beta(n), gates, select),
        (exists|u: int| #[trigger] returned_on_exchange(alpha(n), gates, select, u)
            && returned_on_exchange(beta(n), gates, select, u)
            && !(legal(ao, ax, 5, u) && legal(bo, bx, 2, u)))
        || witnessed_weak_wait(alpha(n), gates, select)
        || witnessed_weak_wait(beta(n), gates, select),
{
    hide(memory);
    hide(exchange_net);
    hide(first_round);
    let a = alpha(n);
    let b = beta(n);
    fanout_and_reply_deliveries(a);
    fanout_and_reply_deliveries(b);
    weak_assignment_at_delivery(a, assigned_alpha);
    weak_assignment_at_delivery(b, assigned_beta);
    fresh_reader_resumes_actual_sr1_state(a, gates, select);
    fresh_reader_resumes_actual_sr1_state(b, gates, select);
    if gates.contains(Replica::R2) {
        gated_reply_violates_no_await(a, gates, select);
    } else if gates.contains(Replica::R1) {
        gated_reply_violates_no_await(b, gates, select);
    } else {
        surviving_checkpoint_agreement(n);
        assert(survivor_actor(at(Replica::R1)) && survivor_actor(at(Replica::R2)));
        assert(report(a, Replica::R1) == report(b, Replica::R1));
        assert(report(a, Replica::R2) == report(b, Replica::R2));
        ordinary_quorum_can_return(a, gates, select);
        ordinary_quorum_can_return(b, gates, select);
        let u = select(report(a, Replica::R1), report(a, Replica::R2));
        assert(returned_on_exchange(a, gates, select, u));
        assert(returned_on_exchange(b, gates, select, u));
        if legal(ao, ax, 5, u) && legal(bo, bx, 2, u) {
            conditional_history_contradiction(ao, ax, bo, bx, u);
        }
    }
}

// A strong reply can be pending while its sender has no weak dependency.
// After both strong replies arrive C2 may also simply be unscheduled.
pub proof fn waiting_for_normal_quorum_is_independent_of_status(b: Fork, select: Select)
    ensures ({
        let gates = Set::empty();
        let m = reader(b, gates, select);
        let q = exchange_states(b, false);
        let obs = observations(q, queries());
        let finish = process_step(q[4], Action::Strong(Process::SecondClient));
        !(m.accept)(memory(m, Process::SecondClient, obs, 4), finish)
            && effect_at_reply(b, gates, select) == StrongEffect::StrongOnly
            && permitted(effect_at_reply(b, gates, select))
            && !pivotal_at_survivor(b, gates, select)
    }),
{
    hide(memory);
    queries_reach_both_survivors(b, Set::empty(), select);
    let r = origin(b.branch);
    exchange_tracks_private_memory(b, Set::empty(), select, false, at(r), 4);
    exchange_tracks_private_memory(b, Set::empty(), select, false, Process::SecondClient, 4);
}

// A direct interpretation for the existing strong handler. The strong
// step can inspect every ordinary field and its current shared cell.
pub open spec fn weak_item(w: Wire) -> bool { w is Copy || w is WeakConfirm }
pub open spec fn ordinary_packet(p: Packet<Wire>) -> bool { p.path != Path::Weak && !weak_item(p.input) }

pub open spec fn ordinary_step(n: Network<int, Wire>, a: Action<Wire>) -> bool {
    match a {
        Action::Send(_, p) => ordinary_packet(p),
        Action::Deliver(id) => n.pending.contains_key(id) && ordinary_packet(n.pending[id]),
        Action::Local(_, w) => !weak_item(w),
        _ => true,
    }
}

pub open spec fn weak_slot(n: Network<int, Wire>, id: nat) -> Option<Packet<Wire>> {
    if n.pending.contains_key(id) && n.pending[id].path == Path::Weak { Some(n.pending[id]) } else { None }
}

pub open spec fn erase_weak(s: Reader) -> Reader {
    Reader { prior: Control { learned: None, weak_copy: None, ..s.prior }, ..s }
}

pub open spec fn direct_step(
    m: LocalProtocol<Reader, int, Wire>, local: Reader, n: Network<int, Wire>, a: Action<Wire>,
) -> bool {
    let e = process_step(n, a);
    let next = (m.update)(local, e);
    let post = advance(|x, w| cell(x, w), n, a);
    (m.accept)(local, e) == (m.accept)(erase_weak(local), e)
        && erase_weak(next) == (m.update)(erase_weak(local), e)
        && next.prior.weak_copy == local.prior.weak_copy && next.prior.learned == local.prior.learned
        && post.locals == n.locals
        && (forall|id: nat| #[trigger] weak_slot(post, id) == weak_slot(n, id))
}

// This is a physical frame and a guard/handler test. Successful traces
// establish separately that an indirect prerequisite did not stall a read.
pub proof fn ungated_read_preserves_weak_work(
    need: Notice, select: Select, local: Reader, n: Network<int, Wire>, a: Action<Wire>,
)
    requires enabled(n, a), ordinary_step(n, a),
    ensures direct_step(read_protocol(Set::empty(), need, select), local, n, a),
{
    let post = advance(|x, w| cell(x, w), n, a);
    assert(post.locals =~= n.locals);
    assert forall|id: nat| #[trigger] weak_slot(post, id) == weak_slot(n, id) by {
        match a {
            Action::Send(j, p) if j == id => { assert(!n.pending.contains_key(id)); },
            Action::Deliver(j) if j == id => { assert(n.pending[id].path != Path::Weak); },
            _ => {},
        }
    }
}

pub proof fn already_g_wait_fails_direct_guard(b: Fork, select: Select)
    requires b.notice == Notice::G,
    ensures ({
        let weak = weak_assignment(b, true);
        let r = origin(b.branch); let gates = set![r];
        let m = reader(b, gates, select); let q = exchange_states(b, false);
        let seen = observations(q, queries());
        let local = memory(m, at(r), seen, 4);
        let notice = Action::Deliver(2); let reply = reply_action(r, report(b, r));
        let post = advance(|x, w| cell(x, w), q[4], notice);
        let learned = (m.update)(local, process_step(q[4], notice));
        pre_sr1_g(b, weak.ops) && witnessed_weak_wait(b, gates, select)
            && ordinary_step(post, reply) && (m.accept)(learned, process_step(post, reply))
            && !(m.accept)(erase_weak(learned), process_step(post, reply))
            && !direct_step(m, learned, post, reply)
    }),
{
    hide(memory);
    let r = origin(b.branch); let gates = set![r];
    weak_assignment_at_delivery(b, true);
    gated_reply_violates_no_await(b, gates, select);
}

// Let the real status reach R2 after both SR2 requests have been delivered.
// Only the two already-required strong replies follow it.
pub open spec fn notified_actions(b: Fork) -> Seq<Action<Wire>> {
    queries() + seq![Action::Deliver(2)] + completed_actions(b).skip(4)
}

pub open spec fn notified_net(b: Fork, k: nat) -> Network<int, Wire> {
    if k <= 4 { exchange_net(b, k) } else {
        let n = exchange_net(b, (k - 1) as nat);
        Network { pending: n.pending.remove(2), ..n }
    }
}

spec fn notified_reader(b: Fork, select: Select, p: Process, k: nat) -> Reader {
    if k <= 4 { exchange_memory(b, select, p, k) } else {
        let s = exchange_memory(b, select, p, (k - 1) as nat);
        if p == at(Replica::R2) { Reader { prior: Control { learned: Some(b.notice), ..s.prior }, ..s } } else { s }
    }
}

proof fn notified_memory(need: Notice, select: Select, p: Process, k: nat)
    requires k <= 10,
    ensures ({
        let b = alpha(need); let states = Seq::new(11, |i: int| notified_net(b, i as nat));
        let m = reader(b, set![Replica::R2], select);
        memory(m, p, observations(states, notified_actions(b)), k) == notified_reader(b, select, p, k)
    }),
    decreases k,
{
    let b = alpha(need);
    prefix_memory_tracks_actual_messages(b, Process::SecondClient, actions_to_crash(b).len());
    if k > 0 {
        let j = (k - 1) as nat;
        notified_memory(need, select, p, j); prefix_index(j as int);
    }
}

pub proof fn notified_gate_returns(need: Notice, select: Select)
    ensures ({
        let b = alpha(need); let gates = set![Replica::R2]; let pre = reader(b, gates, select);
        let net = checkpoint_end(b); let result = |s: Reader| s.returned;
        let s = Seq::new(11, |i: int| notified_net(b, i as nat)); let a = notified_actions(b);
        pre_sr1_g(b, weak_assignment(b, true).ops) && truthful_notice(b, weak_assignment(b, true).ops)
            && witnessed_weak_wait(b, gates, select)
            && crate::service::response_path(pre, result, net, delayed_slots(), s, a, select(report(b, Replica::R1), report(b, Replica::R2)))
            && crate::service::receipt_prerequisite(pre, result, net, delayed_slots(), 2)
    }),
{
    hide(memory);
    let b = alpha(need); let gates = set![Replica::R2]; let pre = reader(b, gates, select);
    let net = checkpoint_end(b); let result = |s: Reader| s.returned; let v = select(report(b, Replica::R1), report(b, Replica::R2));
    let a = notified_actions(b); let s = Seq::new(11, |i: int| notified_net(b, i as nat)); let es = observations(s, a);
    let c = Process::SecondClient;
    weak_assignment_at_delivery(b, true);
    gated_reply_violates_no_await(b, gates, select);
    prefix_memory_tracks_actual_messages(b, c, actions_to_crash(b).len());
    prefix_memory_tracks_actual_messages(b, at(Replica::R1), actions_to_crash(b).len());
    prefix_memory_tracks_actual_messages(b, at(Replica::R2), actions_to_crash(b).len());
    assert forall|i: int| 0 <= i < a.len() implies {
        let step = #[trigger] a[i]; let next = advance(|x, w| cell(x, w), s[i], step);
        enabled(s[i], step) && s[i + 1] == next && crate::confirmation::fresh_send(step, delayed_slots())
    } by {
        prefix_index(i);
        let next = advance(|x, w| cell(x, w), s[i], a[i]);
        assert(next.pending =~= s[i + 1].pending);
        assert(next.locals =~= s[i + 1].locals);
    }
    assert forall|i: int| 0 <= i < es.len() implies {
        let e = #[trigger] es[i]; (pre.accept)(memory(pre, e.actor, es, i as nat), e)
    } by {
        let e = es[i]; let state = notified_reader(b, select, e.actor, i as nat);
        notified_memory(need, select, e.actor, i as nat); prefix_index(i);
        assert(permits_step(state.prior, e));
        assert(read_accept(state, e, gates, need));
    }
    assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
        Action::Send(_, p) if p.from == c => invocation_packet(p) && live_pair().contains(p.to->At_0)
            && (forall|j: int| 0 <= j < i ==> !client_sends_to(#[trigger] a[j], c, p.to->At_0)),
        _ => true,
    } by { prefix_index(i); }
    assert forall|j: int, i: int| 0 <= j < i < es.len() implies match (#[trigger] es[i]).action {
        Action::Send(_, p) if p.from == c => (#[trigger] es[j]).actor != c || es[j].incoming.is_none(), _ => true,
    } by { prefix_index(i); }
    assert(client_sends_to(a[0], c, Replica::R1) && client_sends_to(a[1], c, Replica::R2));
    assert forall|k: nat| k < es.len() implies (#[trigger] memory(pre, c, es, k)).returned.is_none() by {
        notified_memory(need, select, c, k);
    }
    notified_memory(need, select, c, 10);
    assert(crate::service::response_path(pre, result, net, delayed_slots(), s, a, v));
    no_strong_detour_around_gate(b, gates, select);
    assert forall|t: Seq<Network<int, Wire>>, steps: Seq<Action<Wire>>, value: int|
        #[trigger] crate::service::response_path(pre, result, net, delayed_slots(), t, steps, value)
        implies crate::service::consumed_issue(net, 2, t, steps) by {
        if !crate::service::consumed_issue(net, 2, t, steps) {
            crate::service::path_without_notice_preserves_delays(need, pre, result, t, steps, value);
            assert(delayed_slots().contains(2nat));
            assert forall|i: int| 0 <= i < steps.len() implies #[trigger] steps[i] != Action::<Wire>::Deliver(2)
                by { assert(crate::survivors::keeps_delayed_slots(steps[i], delayed_slots())); }
            assert(cell_trace(t, steps));
            assert(sr2_result(pre, result, observations(t, steps)).is_none());
        }
    }
}

pub proof fn already_g_receipt_is_indispensable_to_gated_read(select: Select)
    ensures ({
        let b = alpha(Notice::G); let gates = set![Replica::R2]; let pre = reader(b, gates, select);
        let net = checkpoint_end(b); let result = |s: Reader| s.returned;
        let s = Seq::new(11, |i: int| notified_net(b, i as nat)); let a = notified_actions(b);
        pre_sr1_g(b, weak_assignment(b, true).ops) && truthful_notice(b, weak_assignment(b, true).ops)
            && witnessed_weak_wait(b, gates, select)
            && crate::service::response_path(pre, result, net, delayed_slots(), s, a, select(report(b, Replica::R1), report(b, Replica::R2)))
            && crate::service::receipt_prerequisite(pre, result, net, delayed_slots(), 2)
    }),
{
    notified_gate_returns(Notice::G,select);
}

}
