// The original two callers and weak fork, with a value-bearing SR1 peer
// message actually issued to each survivor. A finite service fragment.
use vstd::prelude::*;
use crate::{Branch, Op, Replica, checkpoint::*, delivery::*, protocol::*};
use crate::information_flow as flow;
use crate::precedence::{self, Side, at_side};
use crate::read_call::{Event, Log, Net, Program, obs};
use crate::first_splice::Observation;
use crate::sr2::{queries, query_packet};
use crate::independent_read as read;
use crate::hybrid_majority as majority;
use crate::promotion_wait as wait;
use crate::transparency::{self as effects, StrongEffect};

verus! {

pub type Row = (Report, nat);

#[verifier::reject_recursive_types(M)]
pub struct Rule<M> {
    pub empty: M,
    pub remember: spec_fn(M, int) -> M,
    pub header: spec_fn(M, int) -> nat,
    pub elect: spec_fn(Row, Row) -> Side,
}

pub struct Local<M> {
    pub control: Control,
    pub memo: M,
    pub asked: bool,
    pub left: Option<Row>,
    pub right: Option<Row>,
    pub choice: Option<Side>,
}

pub open spec fn peer(r: Replica, v: int) -> Packet<Wire> {
    Packet { path: Path::Strong, from: at(Replica::R3), to: at(r), input: Wire::Peer(v) }
}

pub open spec fn is_peer(q: Packet<Wire>) -> bool {
    q.input is Peer && (q == peer(Replica::R1, q.input->Peer_0) || q == peer(Replica::R2, q.input->Peer_0))
}

pub open spec fn answer(r: Replica, row: Row) -> Packet<Wire> {
    Packet { path: Path::Strong, from: at(r), to: Process::SecondClient,
        input: Wire::StampedAnswer(row.0, row.1) }
}

pub open spec fn row<M>(rule: Rule<M>, memo: M, v: int, answered_first: bool) -> Row {
    (Report { value: v, answered_first }, (rule.header)(memo, v))
}

pub open spec fn selected<M>(s: Local<M>) -> Option<int> {
    match s.choice {
        Some(side) => Some(at_side((s.left.unwrap().0.value, s.right.unwrap().0.value), side)),
        None => None,
    }
}

pub open spec fn accepts<M>(rule: Rule<M>, s: Local<M>, e: Observation) -> bool {
    // A split SR1 quorum may reply too. C1 publishes after any two distinct
    // reporters. The concrete receive schedule supplies agreeing values.
    let base = if e.incoming.is_some() && first_reply(e.incoming.unwrap()) {
        !s.control.finished
    } else if e.action == Action::Strong(Process::FirstClient) {
        !s.control.finished && s.control.replies_from.len() >= 2
    } else { permits_step(s.control, e) };
    base && match e.action {
        Action::Send(_, q) if q.input is Peer =>
            is_peer(q) && s.control.requested && e.own_local == Some(q.input->Peer_0),
        Action::Send(_, q) if q.input is StampedAnswer => {
            let r = q.from->At_0;
            q.from is At && live_pair().contains(r) && s.asked && e.own_local.is_some()
                && q == answer(r, row(rule, s.memo, e.own_local.unwrap(), s.control.answered_first))
        },
        Action::Send(_, q) => invocation_packet(q) || first_reply(q) || notice_to(q, q.to)
            || (q.path == Path::Weak && q.to == at(Replica::R3) && q.from is At
                && live_pair().contains(q.from->At_0) && q.input == Wire::Copy(e.own_local.unwrap())),
        Action::Strong(Process::SecondClient) => s.left.is_some() && s.right.is_some() && s.choice.is_none(),
        _ => true,
    }
}

pub open spec fn update<M>(rule: Rule<M>, s: Local<M>, e: Observation) -> Local<M> {
    let u = Local { control: change_control(s.control, e), ..s };
    match e.incoming {
        Some(q) if first_reply(q) => {
            let v = q.input->Reply_0;
            let best = if s.control.reply.is_some() && s.control.reply.unwrap() > v { s.control.reply } else { Some(v) };
            Local { control: Control { reply: best, ..u.control }, ..u }
        },
        Some(q) if is_peer(q) => Local { memo: (rule.remember)(s.memo, q.input->Peer_0), ..u },
        Some(q) if q.input == Wire::Query2 && invocation_packet(q) => Local { asked: true, ..u },
        Some(q) if q.input is StampedAnswer => {
            let value = (q.input->StampedAnswer_0, q.input->StampedAnswer_1);
            if q == answer(Replica::R1, value) { Local { left: Some(value), ..u } }
            else if q == answer(Replica::R2, value) { Local { right: Some(value), ..u } }
            else { u }
        },
        None if e.action == Action::Strong(Process::SecondClient) =>
            Local { choice: Some((rule.elect)(s.left.unwrap(), s.right.unwrap())), ..u },
        _ => u,
    }
}

pub open spec fn machine<M>(rule: Rule<M>) -> Program<Local<M>> {
    LocalProtocol {
        initial: |_p| Local { control: initial_control(), memo: rule.empty, asked: false,
            left: None, right: None, choice: None },
        accept: |s, e| accepts(rule, s, e),
        update: |s, e| update(rule, s, e),
        done: |s: Local<M>| s.control.finished || s.choice.is_some(),
    }
}

pub open spec fn fork(branch: Branch) -> Fork { Fork { branch, notice: Notice::Replication } }

pub open spec fn sample_row<M>(rule: Rule<M>, b: Fork, r: Replica) -> Row {
    row(rule, (rule.remember)(rule.empty, first_value(b)), (checkpoint_end(b).locals)(r), true)
}

// Keep the original weak installation, confirmation and SR1 fanout. Insert
// two sends and both deliveries after request intake and before C1's receives.
pub open spec fn actions<M>(rule: Rule<M>, b: Fork) -> Seq<Event> {
    let a = actions_to_crash(b);
    let one = Replica::R1;
    let two = Replica::R2;
    a.take(8) + seq![Action::Send(9, peer(one, first_value(b))), Action::Send(10, peer(two, first_value(b))),
        Action::Deliver(9), Action::Deliver(10)] + a.skip(8) + queries()
        + seq![Action::Send(13, answer(one, sample_row(rule, b, one))),
            Action::Send(14, answer(two, sample_row(rule, b, two))),
            Action::Deliver(13), Action::Deliver(14), Action::Strong(Process::SecondClient)]
}

pub open spec fn original_cut(k: nat) -> nat {
    if k <= 8 { k } else if k <= 12 { 8 } else if k <= 21 { (k - 4) as nat } else { 17 }
}

pub open spec fn net<M>(rule: Rule<M>, b: Fork, k: nat) -> Net {
    let base = state_after(b, original_cut(k));
    let one = Replica::R1;
    let two = Replica::R2;
    let p = base.pending;
    let p = if 9 <= k < 11 { p.insert(9, peer(one, first_value(b))) } else { p };
    let p = if 10 <= k < 12 { p.insert(10, peer(two, first_value(b))) } else { p };
    let p = if 22 <= k < 24 { p.insert(11, query_packet(one)) } else { p };
    let p = if 23 <= k < 25 { p.insert(12, query_packet(two)) } else { p };
    let p = if 26 <= k < 28 { p.insert(13, answer(one, sample_row(rule, b, one))) } else { p };
    let p = if 27 <= k < 29 { p.insert(14, answer(two, sample_row(rule, b, two))) } else { p };
    Network { pending: p, ..base }
}

pub open spec fn run<M>(rule: Rule<M>, b: Fork) -> Log {
    Log { nets: Seq::new(31, |k: int| net(rule, b, k as nat)), actions: actions(rule, b) }
}

pub open spec fn local<M>(rule: Rule<M>, b: Fork, p: Process, k: nat) -> Local<M> {
    let c = Process::SecondClient;
    let one = Replica::R1;
    let two = Replica::R2;
    let base = expected_control(b, p, original_cut(k));
    let control = if p == c && k >= 22 {
        Control { sent_requests: if k == 22 { set![one] } else { live_pair() }, ..base }
    } else { base };
    let saved = (p == at(one) && k >= 11) || (p == at(two) && k >= 12);
    let left = sample_row(rule, b, one);
    let right = sample_row(rule, b, two);
    Local { control, memo: if saved { (rule.remember)(rule.empty, first_value(b)) } else { rule.empty },
        asked: (p == at(one) && k >= 24) || (p == at(two) && k >= 25),
        left: if p == c && k >= 28 { Some(left) } else { None },
        right: if p == c && k >= 29 { Some(right) } else { None },
        choice: if p == c && k >= 30 { Some((rule.elect)(left, right)) } else { None } }
}

pub(crate) proof fn index(i: int)
    requires 0 <= i < 30,
    ensures i == 0 || i == 1 || i == 2 || i == 3 || i == 4 || i == 5 || i == 6 || i == 7
        || i == 8 || i == 9 || i == 10 || i == 11 || i == 12 || i == 13 || i == 14
        || i == 15 || i == 16 || i == 17 || i == 18 || i == 19 || i == 20 || i == 21
        || i == 22 || i == 23 || i == 24 || i == 25 || i == 26 || i == 27 || i == 28 || i == 29,
{}

// For unmodified cuts, take the verified original edge and private state.
// The inserted exchange has its own pending envelopes and addressed events.
pub(crate) proof fn transport_edge<M>(rule: Rule<M>, b: Fork, k: nat)
    requires k < 30,
    ensures ({
        let l = run(rule, b);
        let n = l.nets[k as int];
        let a = l.actions[k as int];
        enabled(n, a) && l.nets[k as int + 1] == advance(|x, w| cell(x, w), n, a)
    }),
{
    let l = run(rule, b);
    let n = l.nets[k as int];
    let a = l.actions[k as int];
    let next = advance(|x, w| cell(x, w), n, a);
    if k < 8 || 12 <= k < 21 {
        prefix_transport_is_enabled(b);
        let j = original_cut(k) as int;
        assert(checkpoint_states(b)[j] == n && actions_to_crash(b)[j] == a);
        assert(checkpoint_states(b)[j + 1] == l.nets[k as int + 1]);
    } else {
        index(k as int);
        assert(next.pending =~= l.nets[k as int + 1].pending);
        assert(next.locals =~= l.nets[k as int + 1].locals);
    }
}

pub(crate) proof fn handler_edge<M>(rule: Rule<M>, b: Fork, p: Process, k: nat)
    requires k < 30,
    ensures ({
        let e = obs(run(rule, b))[k as int];
        let s = local(rule, b, p, k);
        (e.actor == p ==> accepts(rule, s, e))
            && (if e.actor == p { update(rule, s, e) } else { s }) == local(rule, b, p, k + 1)
    }),
{
    index(k as int);
    if k < 8 || 12 <= k < 21 {
        let j = original_cut(k);
        let old = checkpoint_observations(b);
        let e = obs(run(rule, b))[k as int];
        assert(e == old[j as int]);
        both_prefixes_are_enabled_and_client_finishes(b);
        prefix_memory_tracks_actual_messages(b, p, j);
        prefix_memory_tracks_actual_messages(b, p, j + 1);
        assert((checkpoint_machine().accept)(memory(checkpoint_machine(), e.actor, old, j), e));
    }
}

pub proof fn actual_local<M>(rule: Rule<M>, b: Fork, p: Process, k: nat)
    requires k <= 30,
    ensures memory(machine(rule), p, obs(run(rule, b)), k) == local(rule, b, p, k),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        actual_local(rule, b, p, j);
        handler_edge(rule, b, p, j);
    }
}

pub open spec fn admitted<M>(rule: Rule<M>, b: Fork) -> bool {
    let l = run(rule, b);
    l.nets[0] == after_local_rmws() && trace(|x, w| cell(x, w), l.nets, l.actions)
        && accepted(machine(rule), obs(l))
}

pub proof fn value_service_executes<M>(rule: Rule<M>, b: Fork)
    ensures admitted(rule, b),
{
    let l = run(rule, b);
    prefix_transport_is_enabled(b);
    assert forall|i: int| 0 <= i < l.actions.len() implies {
        let a = #[trigger] l.actions[i];
        enabled(l.nets[i], a) && l.nets[i + 1] == advance(|x, w| cell(x, w), l.nets[i], a)
    } by { transport_edge(rule, b, i as nat); }
    assert forall|i: int| 0 <= i < l.actions.len() implies {
        let e = #[trigger] obs(l)[i];
        (machine(rule).accept)(memory(machine(rule), e.actor, obs(l), i as nat), e)
    } by {
        let p = obs(l)[i].actor;
        actual_local(rule, b, p, i as nat);
        handler_edge(rule, b, p, i as nat);
    }
}

// Observers below read the transport and deterministic private memory, not
// the closed forms used to verify the run.
pub open spec fn state<M>(rule: Rule<M>, b: Fork, p: Process, k: nat) -> Local<M> {
    memory(machine(rule), p, obs(run(rule, b)), k)
}

pub open spec fn first<M>(rule: Rule<M>, b: Fork) -> int {
    state(rule, b, Process::FirstClient, 18).control.reply.unwrap()
}

pub open spec fn second<M>(rule: Rule<M>, b: Fork) -> Option<int> {
    flow::result(machine(rule), |s: Local<M>| selected(s), run(rule, b))
}

pub open spec fn memos<M>(rule: Rule<M>, b: Fork, k: nat) -> (M, M) {
    (state(rule, b, at(Replica::R1), k).memo, state(rule, b, at(Replica::R2), k).memo)
}

pub open spec fn record_of(e: Observation) -> Row {
    let body = e.incoming.unwrap().input;
    (body->StampedAnswer_0, body->StampedAnswer_1)
}

// Underlying quorum samples, including ordinary participation but excluding
// the two headers. Take them from C2's actual deliveries.
pub open spec fn contest(l: Log) -> (Report, Report) {
    (record_of(obs(l)[27]).0, record_of(obs(l)[28]).0)
}

pub open spec fn elect_at<M>(rule: Rule<M>, samples: (Report, Report), retained: (M, M)) -> Side {
    (rule.elect)((samples.0, (rule.header)(retained.0, samples.0.value)),
                 (samples.1, (rule.header)(retained.1, samples.1.value)))
}

pub open spec fn independent<M>(rule: Rule<M>, b: Fork) -> precedence::IndependentView {
    precedence::IndependentView {
        cells: survivor(run(rule, b).nets[21]),
        left: state(rule, b, at(Replica::R1), 21).control,
        right: state(rule, b, at(Replica::R2), 21).control,
    }
}

pub open spec fn other_copy(b: Fork) -> nat { if b.branch == Branch::Alpha { 0 } else { 1 } }
pub open spec fn unheard(b: Fork) -> nat { if b.branch == Branch::Alpha { 6 } else { 7 } }

// Only the two weak invocations own these journals. Connect their actual
// replies and cells to the two enabled copy sends. Those sends are stutters
// on this strong service's private memory, including at their senders.
pub open spec fn weak_entry<M>(rule: Rule<M>, b: Fork) -> bool {
    let end = crate::guarded_history::weak_end();
    let start = local_rmw_cells();
    let w1 = crate::weak_round::request(Op::W1);
    let w2 = crate::weak_round::request(Op::W2);
    let a = send(0, Path::Weak, at(w1.site), at(Replica::R3), Wire::Copy((end.front.base.disk)(w1.site).value));
    let d = send(1, Path::Weak, at(w2.site), at(Replica::R3), Wire::Copy((end.front.base.disk)(w2.site).value));
    let n = advance(|x, w| cell(x, w), start, a);
    let m = machine(rule);
    let e = process_step(start, a);
    let f = process_step(n, d);
    end.answers.get(w1.id) == Some(1) && end.answers.get(w2.id) == Some(1) && end.wire.is_empty()
        && crate::weak_round::origin_only(end) && end.front == crate::facade_hybrid::prefix(b, 0)
        && enabled(start, a) && enabled(n, d) && advance(|x, w| cell(x, w), n, d) == run(rule, b).nets[0]
        && (m.accept)((m.initial)(e.actor), e) && (m.update)((m.initial)(e.actor), e) == (m.initial)(e.actor)
        && (m.accept)((m.initial)(f.actor), f) && (m.update)((m.initial)(f.actor), f) == (m.initial)(f.actor)
}

proof fn weak_entry_executes<M>(rule: Rule<M>, b: Fork)
    ensures weak_entry(rule, b),
{
    crate::weak_round::actual_overlap(b);
    crate::facade_hybrid::weak_calls_and_issued_offers(crate::weak_round::paper_ops(), b);
    origin_updates_are_actually_offered();
    prefix_transport_is_enabled(b);
}

// Exact lifecycle and sources through publication. The unselected SR1 reply
// remains addressed to C1. Every SR1 peer packet and both C2 answers arrive.
pub open spec fn calls<M>(rule: Rule<M>, b: Fork) -> bool {
    let l = run(rule, b);
    let es = obs(l);
    let c1 = Process::FirstClient;
    let c2 = Process::SecondClient;
    let ctrl = state(rule, b, c1, 18).control;
    let side = state(rule, b, c2, 30).choice.unwrap();
    let site = at_side((Replica::R1, Replica::R2), side);
    let v = first_value(b);
    let q = live_pair();
    ctrl.sent_requests == all_replicas() && ctrl.replies_from == set![crate::origin(b.branch), Replica::R3]
        && es[14].own_local == Some(v) && es[14].action == Action::Send(8, packet_for(b, 8))
        && es[15].incoming == Some(packet_for(b, if b.branch == Branch::Alpha { 7 } else { 6 }))
        && es[15].incoming.unwrap().input == Wire::Reply(v) && l.nets[16].pending.get(8) == Some(packet_for(b, 8))
        && es[16].incoming == Some(packet_for(b, 8)) && es[16].incoming.unwrap().input == Wire::Reply(v)
        && !state(rule, b, c1, 17).control.finished && ctrl.finished && ctrl.reply == Some(v)
        && l.actions[18] == Action::StopFirstClient && l.actions[19] == Action::CrashR3
        && l.actions[20] == Action::StartSecondClient && state(rule, b, c2, 20) == (machine(rule).initial)(c2)
        && l.actions.skip(21).take(4) == queries() && state(rule, b, c2, 30).control.sent_requests == q
        && crate::hybrid_majority::sole(l.nets[21], q) && q.contains(site)
        && selected(state(rule, b, c2, 29)).is_none() && second(rule, b) == Some((l.nets[29].locals)(site))
        && second(rule, b) == Some(at_side((record_of(es[27]).0.value, record_of(es[28]).0.value), side))
        && l.nets[30].pending.dom() == set![other_copy(b), 2nat, unheard(b)]
        && l.nets[30].pending.get(unheard(b)) == Some(packet_for(b, unheard(b)))
        && (forall|i: int| 2 <= i < 30 ==> {
            let e = #[trigger] es[i];
            !(e.action is Local) && !(e.action is ClientInput)
                && (e.action is Send ==> e.action->Send_1.path != Path::Weak)
                && (e.incoming.is_some() ==> e.incoming.unwrap().path != Path::Weak)
        })
        && (forall|i: int| 0 <= i < l.actions.len() ==> match #[trigger] l.actions[i] {
            Action::Send(_, p) if p.from == c1 => 2 <= i <= 4 && invocation_packet(p),
            Action::Send(_, p) if p.from == c2 => 21 <= i <= 22 && invocation_packet(p),
            _ => true,
        })
}

proof fn calls_execute<M>(rule: Rule<M>, b: Fork)
    ensures calls(rule, b),
{
    let l = run(rule, b);
    let c1 = Process::FirstClient;
    let c2 = Process::SecondClient;
    actual_local(rule, b, c1, 17);
    actual_local(rule, b, c1, 18);
    actual_local(rule, b, c2, 20);
    actual_local(rule, b, c2, 29);
    actual_local(rule, b, c2, 30);
    assert(l.actions.skip(21).take(4) =~= queries());
    assert(l.nets[30].pending.dom() =~= set![other_copy(b), 2nat, unheard(b)]);
    let es = obs(l);
    assert forall|i: int| 2 <= i < 30 implies {
        let e = #[trigger] es[i];
        !(e.action is Local) && !(e.action is ClientInput)
            && (e.action is Send ==> e.action->Send_1.path != Path::Weak)
            && (e.incoming.is_some() ==> e.incoming.unwrap().path != Path::Weak)
    } by { index(i); }
    assert forall|i: int| 0 <= i < l.actions.len() implies match #[trigger] l.actions[i] {
        Action::Send(_, p) if p.from == c1 => 2 <= i <= 4 && invocation_packet(p),
        Action::Send(_, p) if p.from == c2 => 21 <= i <= 22 && invocation_packet(p),
        _ => true,
    } by { index(i); }
}

// Every cut from issuance of the weak confirmation to SR2 publication has
// the same weak transport/cells and the same private weak records as cut 2
// of THIS run. The two global weak queues need not agree with each other.
pub open spec fn weak_frame<M>(rule: Rule<M>, b: Fork, k: nat) -> bool {
    let l = run(rule, b);
    let n = l.nets[k as int];
    n.locals == l.nets[2].locals && survivor(n) == (2int, 5int)
        && n.pending.get(2) == Some(packet_for(b, 2))
        && n.pending.get(other_copy(b)) == Some(packet_for(b, other_copy(b)))
        && (forall|id: nat| #[trigger] weak_at(n, id) == weak_at(l.nets[2], id))
        && (forall|p: Process| {
            let cur = #[trigger] state(rule, b, p, k);
            let old = state(rule, b, p, 2);
            cur.control.learned == old.control.learned && cur.control.weak_copy == old.control.weak_copy
        })
}

proof fn weak_frame_at<M>(rule: Rule<M>, b: Fork, k: nat)
    requires 2 <= k <= 30,
    ensures weak_frame(rule, b, k),
{
    let l = run(rule, b);
    let n = l.nets[k as int];
    assert(n.locals =~= l.nets[2].locals);
    assert forall|id: nat| #[trigger] weak_at(n, id) == weak_at(l.nets[2], id) by {
        if id <= 2 { assert(id == 0 || id == 1 || id == 2); }
    }
    assert forall|p: Process| {
        let cur = #[trigger] state(rule, b, p, k);
        let old = state(rule, b, p, 2);
        cur.control.learned == old.control.learned && cur.control.weak_copy == old.control.weak_copy
    } by {
        actual_local(rule, b, p, k);
        actual_local(rule, b, p, 2);
    }
}

// A provenance annotation for these two specific receipts. The
// weak copy's sender, value sampled, send, continuously queued envelope and actual
// receiver are checked separately. The strong code never sees this Op.
pub open spec fn source(l: Log, i: int) -> Option<Op> {
    if (i != 10 && i != 11) || l.actions.len() <= i { None } else {
        let es = obs(l);
        let r = if i == 10 { Replica::R1 } else { Replica::R2 };
        let put = es[i - 2];
        let id = (i - 1) as nat;
        let copy = es[0].incoming;
        let w = if copy == Some(Packet { path: Path::Weak, from: at(Replica::R2), to: at(Replica::R3),
                                          input: Wire::Copy(5) }) { Op::W2 } else { Op::W1 };
        let owner = if w == Op::W2 { Replica::R2 } else { Replica::R1 };
        let v = crate::next(w, 1);
        let q = peer(r, v);
        if copy == Some(Packet { path: Path::Weak, from: at(owner), to: at(Replica::R3), input: Wire::Copy(v) })
            && es[0].actor == at(Replica::R3) && (l.nets[1].locals)(Replica::R3) == v
            && (forall|j: int| 1 <= j < i - 2 ==>
                #[trigger] local_input(l.nets[j], l.actions[j], Replica::R3).is_none())
            && put.own_local == Some(v) && put.action == Action::Send(id, q)
            && (forall|j: int| i - 2 < j <= i ==> #[trigger] l.nets[j].pending.get(id) == Some(q))
            && es[i].action == Action::<Wire>::Deliver(id) && es[i].actor == at(r) && es[i].incoming == Some(q)
        { Some(w) } else { None }
    }
}

pub open spec fn forwarded<M>(rule: Rule<M>, b: Fork, r: Replica) -> bool {
    let l = run(rule, b);
    let es = obs(l);
    let j: int = if r == Replica::R1 { 0 } else { 1 };
    let i = 10 + j;
    let p = at(r);
    let v = first(rule, b);
    let own = (l.nets[25 + j].locals)(r);
    let saved = state(rule, b, p, (i + 1) as nat).memo;
    let out = row(rule, saved, own, true);
    source(l, i) == Some(observed_writer(b)) && es[i].incoming == Some(peer(r, v))
        && state(rule, b, p, i as nat).memo == rule.empty && saved == (rule.remember)(rule.empty, v)
        && state(rule, b, p, (25 + j) as nat).memo == saved && state(rule, b, p, (25 + j) as nat).asked
        && es[25 + j].own_local == Some(own) && l.actions[25 + j] == Action::Send((13 + j) as nat, answer(r, out))
        && l.nets[27 + j].pending.get((13 + j) as nat) == Some(answer(r, out))
        && es[27 + j].action == Action::<Wire>::Deliver((13 + j) as nat)
        && es[27 + j].incoming == Some(answer(r, out)) && record_of(es[27 + j]) == out
        && (if j == 0 { state(rule, b, Process::SecondClient, 29).left }
            else { state(rule, b, Process::SecondClient, 29).right }) == Some(out)
}

proof fn follow_packet<M>(rule: Rule<M>, b: Fork, r: Replica)
    requires live_pair().contains(r),
    ensures forwarded(rule, b, r),
{
    let l = run(rule, b);
    let j: int = if r == Replica::R1 { 0 } else { 1 };
    let i = 10 + j;
    assert forall|k: int| 1 <= k < i - 2 implies
        #[trigger] local_input(l.nets[k], l.actions[k], Replica::R3).is_none() by { index(k); }
    assert forall|k: int| i - 2 < k <= i implies
        #[trigger] l.nets[k].pending.get((i - 1) as nat) == Some(peer(r, first_value(b))) by { index(k); }
    actual_local(rule, b, at(r), i as nat);
    actual_local(rule, b, at(r), (i + 1) as nat);
    actual_local(rule, b, at(r), (25 + j) as nat);
    actual_local(rule, b, Process::FirstClient, 18);
    actual_local(rule, b, Process::SecondClient, 29);
}

pub open spec fn observed_choice<M>(rule: Rule<M>, b: Fork, k: nat) -> Side {
    elect_at(rule, contest(run(rule, b)), memos(rule, b, k))
}

// The fixed-input inspection of a retained checkpoint agrees with the
// actual distributed selection after both receipts.
proof fn resolver_connection<M>(rule: Rule<M>, b: Fork)
    ensures
        independent(rule, b) == precedence::independent_view(b),
        memos(rule, b, 10) == (rule.empty, rule.empty),
        observed_choice(rule, b, 10) == observed_choice(rule, alpha(b.notice), 10),
        state(rule, b, Process::SecondClient, 30).choice == Some(observed_choice(rule, b, 12)),
        second(rule, b) == Some(at_side((2int, 5int), observed_choice(rule, b, 12))),
        contest(run(rule, b)) == (Report { value: 2, answered_first: true }, Report { value: 5, answered_first: true }),
{
    let one = Replica::R1;
    let two = Replica::R2;
    actual_local(rule, b, at(one), 10); actual_local(rule, b, at(two), 10);
    actual_local(rule, alpha(b.notice), at(one), 10); actual_local(rule, alpha(b.notice), at(two), 10);
    actual_local(rule, b, at(one), 12); actual_local(rule, b, at(two), 12);
    actual_local(rule, b, at(one), 21); actual_local(rule, b, at(two), 21);
    prefix_memory_tracks_actual_messages(b, at(one), 17); prefix_memory_tracks_actual_messages(b, at(two), 17);
    actual_local(rule, b, Process::SecondClient, 30);
}

// Attach the existing independent-client monitor to the same physical log.
// Its startup transition inspects only C2. Its post-submission relation
// forbids client sends. Retire the three SR1 reply names and the actual
// failed-recipient backlog exactly as the monitor prescribes.
pub open spec fn monitored<M>(rule: Rule<M>, b: Fork, k: nat) -> read::State<Local<M>> {
    let base = crate::early_crash::entry(machine(rule));
    let ids = Set::<nat>::empty();
    let ids = if k >= 13 { ids.insert(6) } else { ids };
    let ids = if k >= 14 { ids.insert(7) } else { ids };
    let ids = if k >= 15 { ids.insert(8) } else { ids };
    let ids = if k >= 20 { ids.insert(2).insert(other_copy(b)) } else { ids };
    read::State { cfg: crate::ordinary_service::Configuration { net: net(rule, b, k), private: |p| state(rule, b, p, k) },
        first_requested: local(rule, b, Process::FirstClient, k).control.sent_requests,
        requested: local(rule, b, Process::SecondClient, k).control.sent_requests, reserved: ids, ..base }
}

pub open spec fn segment<M>(rule: Rule<M>, b: Fork, start: nat, length: nat)
    -> crate::first_assembly::Service<Local<M>>
{
    wait::Path { states: Seq::new(length + 1, |j: int| monitored(rule, b, (start + j) as nat)),
        actions: actions(rule, b).subrange(start as int, (start + length) as int) }
}

pub(crate) proof fn monitored_edge<M>(rule: Rule<M>, b: Fork, k: nat)
    requires k < 30,
    ensures ({
        let x = monitored(rule, b, k); let y = monitored(rule, b, k + 1); let a = actions(rule, b)[k as int];
        read::prefix_step(machine(rule))(x, a, y) && (k >= 23 ==> read::service_step(machine(rule))(x, a, y))
    }),
{
    let m = machine(rule); let x = monitored(rule, b, k); let y = monitored(rule, b, k + 1);
    let a = actions(rule, b)[k as int]; let e = process_step(x.cfg.net, a);
    let z = read::next(m, x, a);
    transport_edge(rule, b, k);
    actual_local(rule, b, e.actor, k); handler_edge(rule, b, e.actor, k);
    assert(z.cfg.private =~= y.cfg.private);
    if k == 19 { assert(read::retired_at_failure(x) =~= set![2nat, other_copy(b)]); }
    index(k as int);
    assert(z.reserved =~= y.reserved);
}

pub open spec fn native_quorum<M>(rule: Rule<M>, b: Fork) -> bool {
    let m = machine(rule); let q = live_pair();
    let h = segment(rule, b, 21, 2); let t = segment(rule, b, 23, 7);
    let res = |s: Local<M>| selected(s);
    read::reached(m, crate::early_crash::entry(m), h.states[0])
        && crate::first_schedule::startup(m) && crate::read_issue::can_issue(m, res)
        && majority::served(majority::Caller::Second, m, res, h, t, q)
        && majority::held(t.states, q, second(rule, b).unwrap())
}

proof fn reach_invocation<M>(rule: Rule<M>, b: Fork)
    ensures read::reached(machine(rule), crate::early_crash::entry(machine(rule)), monitored(rule, b, 21)),
{
    hide(read::prefix_step); hide(read::service_step);
    let m = machine(rule);
    let x = monitored(rule, b, 21);
    let entry = crate::early_crash::entry(m);
    let prefix = segment(rule, b, 0, 21);
    value_service_executes(rule, b);
    assert(monitored(rule, b, 0).cfg.private =~= m.initial);
    assert(monitored(rule, b, 0) == entry);
    assert forall|i: int| 0 <= i < 21 implies
        read::prefix_step(m)(prefix.states[i], #[trigger] prefix.actions[i], prefix.states[i + 1])
    by { monitored_edge(rule, b, i as nat); }
    crate::read_nonblocking::from_path(read::prefix_step(m), read::at_state(x), prefix, 0);
}

pub proof fn independent_quorum_service<M>(rule: Rule<M>, b: Fork)
    ensures native_quorum(rule, b),
{
    hide(read::prefix_step); hide(read::service_step); hide(read::reached); hide(memory);
    let m = machine(rule); let q = live_pair();
    let h = segment(rule, b, 21, 2); let t = segment(rule, b, 23, 7);
    let res = |s: Local<M>| selected(s);
    reach_invocation(rule, b);
    assert forall|i: int| 0 <= i < 2 implies
        read::prefix_step(m)(h.states[i], #[trigger] h.actions[i], h.states[i + 1])
    by { monitored_edge(rule, b, (21 + i) as nat); }
    assert forall|i: int| 0 <= i < 7 implies
        read::service_step(m)(t.states[i], #[trigger] t.actions[i], t.states[i + 1])
    by { monitored_edge(rule, b, (23 + i) as nat); }
    let c = Process::SecondClient;
    assert forall|i: int| 0 <= i < 2 implies !read::returned(res)(#[trigger] h.states[i])
    by { actual_local(rule, b, c, (21 + i) as nat); }
    assert forall|i: int| 0 <= i < 7 implies !read::returned(res)(#[trigger] t.states[i])
    by { actual_local(rule, b, c, (23 + i) as nat); }
    actual_local(rule, b, c, 23); actual_local(rule, b, c, 30);
    assert(live(h.states.last().cfg.net, at(Replica::R1)) && live(h.states.last().cfg.net, at(Replica::R2)));
    assert(read::issued_to_majority(h.states.last()));
    assert(majority::sole(h.states[0].cfg.net, q) && majority::sole(t.states.last().cfg.net, q));
    assert(wait::first_return(read::service_step(m), read::returned(res), h.states.last(), t));
    assert(majority::served(majority::Caller::Second, m, res, h, t, q));
    assert(crate::first_schedule::startup(m) && crate::read_issue::can_issue(m, res));
    let site = at_side((Replica::R1, Replica::R2), state(rule, b, c, 30).choice.unwrap());
    assert(q.contains(site) && (t.states[6].cfg.net.locals)(site) == second(rule, b).unwrap());
    assert(majority::held(t.states, q, second(rule, b).unwrap()));
}

// Finite executions, with no service, replay, or cross-run memory premise.
pub proof fn paired_trace_arm<M>(rule: Rule<M>, branch: Branch)
    ensures ({
        let b = fork(branch);
        weak_entry(rule, b) && admitted(rule, b) && calls(rule, b) && native_quorum(rule, b) && first(rule, b) == first_value(b)
            && forwarded(rule, b, Replica::R1) && forwarded(rule, b, Replica::R2)
            && truthful_notice(b, weak_assignment(b, false).ops) && !pre_sr1_g(b, weak_assignment(b, false).ops)
            && (forall|k: nat| 2 <= k <= 30 ==> #[trigger] weak_frame(rule, b, k))
    }),
{
    let b = fork(branch);
    weak_entry_executes(rule, b);
    independent_quorum_service(rule, b);
    value_service_executes(rule, b);
    calls_execute(rule, b);
    follow_packet(rule, b, Replica::R1);
    follow_packet(rule, b, Replica::R2);
    weak_assignment_at_delivery(b, false);
    assert forall|k: nat| 2 <= k <= 30 implies #[trigger] weak_frame(rule, b, k) by { weak_frame_at(rule, b, k); }
}

pub open spec fn aligned(a: Log, b: Log, i: int) -> bool {
    let x = obs(a)[i];
    let y = obs(b)[i];
    (survivor_actor(x.actor) || survivor_actor(y.actor)) ==> {
        x.actor == y.actor && x.own_local == y.own_local
            && (x.action == y.action || i == 25 || i == 26)
            && (x.incoming == y.incoming || i == 10 || i == 11 || i == 27 || i == 28)
            && (x.actor == Process::SecondClient ==> x.action == y.action)
    }
}

pub proof fn survivor_schedule<M>(rule: Rule<M>)
    ensures ({
        let a = run(rule, fork(Branch::Alpha));
        let b = run(rule, fork(Branch::Beta));
        a.nets[0] == b.nets[0] && survivor(a.nets[10]) == (2int, 5int) && survivor(b.nets[10]) == (2int, 5int)
            && (forall|p: Process| survivor_actor(p) ==>
                #[trigger] state(rule, fork(Branch::Alpha), p, 10) == state(rule, fork(Branch::Beta), p, 10))
            && independent(rule, fork(Branch::Alpha)) == independent(rule, fork(Branch::Beta))
            && flow::c2_schedule(a) == flow::c2_schedule(b)
            && (forall|i: int| 0 <= i < 30 ==> #[trigger] aligned(a, b, i))
    }),
{
    let a = run(rule, fork(Branch::Alpha));
    let b = run(rule, fork(Branch::Beta));
    let c = Process::SecondClient;
    let fa = fork(Branch::Alpha); let fb = fork(Branch::Beta);
    prefix_transport_is_enabled(fa); prefix_transport_is_enabled(fb);
    resolver_connection(rule, fa); resolver_connection(rule, fb);
    precedence::equal_independent_views(fb);
    assert forall|p: Process| survivor_actor(p) implies
        #[trigger] state(rule, fa, p, 10) == state(rule, fb, p, 10) by {
        actual_local(rule, fa, p, 10); actual_local(rule, fb, p, 10);
    }
    assert forall|i: int| 0 <= i < 30 implies #[trigger] aligned(a, b, i) by { index(i); }
    assert forall|i: int| 0 <= i < 30 implies {
        let x = #[trigger] obs(a)[i]; let y = #[trigger] obs(b)[i];
        (x.actor == c) == (y.actor == c) && (x.actor == c ==> x.action == y.action)
    } by { assert(aligned(a, b, i)); }
    flow::aligned_actions(obs(a), obs(b), c);
}

pub open spec fn audit<M>(rule: Rule<M>, b: Fork, credit: precedence::Credit) -> bool {
    let l = run(rule, b);
    flow::supported_retention(seq![10int, 11int],
        seq![memos(rule, b, 10), memos(rule, b, 11), memos(rule, b, 12)],
        |i: int| source(l, i), precedence::source_versions(),
        |m: (M, M)| elect_at(rule, contest(l), m), independent(rule, b), credit)
}

pub open spec fn explains<M>(rule: Rule<M>, b: Fork, ops: Seq<Op>, xs: Seq<int>) -> bool {
    flow::legal_result(machine(rule), |s: Local<M>| selected(s), run(rule, b), first(rule, b), ops, xs)
}

// Identify an actual recipient whose update changed its later header and
// thereby the quorum source favored by the unchanged resolver. Both sides
// of the update are reached states in the SAME branch.
pub open spec fn pivotal<M>(rule: Rule<M>, b: Fork, i: nat) -> bool {
    let l = run(rule, b);
    let left = i == 10;
    let r = if left { Replica::R1 } else { Replica::R2 };
    let p = at(r);
    let reply = record_of(obs(l)[if left { 27int } else { 28int }]);
    let old = state(rule, b, p, i).memo;
    let new = state(rule, b, p, i + 1).memo;
    let old_side = observed_choice(rule, b, i);
    let new_side = observed_choice(rule, b, i + 1);
    (i == 10 || i == 11) && forwarded(rule, b, r) && source(l, i as int) == Some(observed_writer(b))
        && old != new && (rule.header)(old, reply.0.value) != reply.1 && (rule.header)(new, reply.0.value) == reply.1
        && old_side != new_side && at_side(precedence::source_versions(), new_side) == observed_writer(b)
        && state(rule, b, Process::SecondClient, 30).choice == Some(new_side)
}

proof fn locate_gain<M>(rule: Rule<M>, b: Fork, credit: precedence::Credit)
    requires
        at_side(precedence::source_versions(), observed_choice(rule, b, 10)) != observed_writer(b),
        at_side(precedence::source_versions(), observed_choice(rule, b, 12)) == observed_writer(b),
        !credit(independent(rule, b), observed_writer(b), flow::rival(observed_writer(b))),
    ensures !audit(rule, b, credit), exists|i: nat| #[trigger] pivotal(rule, b, i),
{
    let sides = precedence::source_versions();
    let w = observed_writer(b);
    let i: nat = if at_side(sides, observed_choice(rule, b, 11)) == w { 10 } else { 11 };
    let r = if i == 10 { Replica::R1 } else { Replica::R2 };
    follow_packet(rule, b, r);
    resolver_connection(rule, b);
    actual_local(rule, b, at(Replica::R1), i); actual_local(rule, b, at(Replica::R2), i);
    actual_local(rule, b, at(Replica::R1), i + 1); actual_local(rule, b, at(Replica::R2), i + 1);
    assert(pivotal(rule, b, i));
    if audit(rule, b, credit) {
        let l = run(rule, b);
        let steps = seq![10int, 11int];
        let j = i as int - 10;
        assert(steps[j] == i);
        assert(precedence::supported_read_update(source(l, steps[j]), sides,
            observed_choice(rule, b, i), observed_choice(rule, b, i + 1), independent(rule, b), credit));
    }
}

// Only the necessary sequential-history clause of H is used. The two empty
// below-G weak orders are admissible at the independent cuts. Each credit
// must be sound for both. The program gets neither a credit nor a weak ID.
pub proof fn h_forces_retained_source_use<M>(rule: Rule<M>, credit: precedence::Credit,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>)
    requires
        explains(rule, fork(Branch::Alpha), ao, ax), explains(rule, fork(Branch::Beta), bo, bx),
        precedence::sound_credit(credit, precedence::actual_cuts(Notice::Replication, false, false)),
    ensures ({
        let a = fork(Branch::Alpha); let b = fork(Branch::Beta);
        second(rule, a) == Some(5) && second(rule, b) == Some(2)
            && flow::writer_before_reads(ao, Op::W2) && flow::writer_before_reads(bo, Op::W1)
            && independent(rule, a) == independent(rule, b)
            && flow::c2_schedule(run(rule, a)) == flow::c2_schedule(run(rule, b))
            && (exists|r: Replica| live_pair().contains(r) && #[trigger] forwarded(rule, a, r)
                && #[trigger] forwarded(rule, b, r) && sample_row(rule, a, r).1 != sample_row(rule, b, r).1)
            && ((!audit(rule, a, credit) && exists|i: nat| #[trigger] pivotal(rule, a, i))
                || (!audit(rule, b, credit) && exists|i: nat| #[trigger] pivotal(rule, b, i)))
    }),
{
    hide(flow::differing_receipts); hide(flow::splits); hide(flow::writer_before_reads);
    let a = fork(Branch::Alpha);
    let b = fork(Branch::Beta);
    paired_trace_arm(rule, Branch::Alpha); paired_trace_arm(rule, Branch::Beta);
    let m = machine(rule);
    flow::h_requires_distinguishing_input(m, m, |s: Local<M>| selected(s), run(rule, a), run(rule, b), ao, ax, bo, bx);
    flow::h_fixes_writer_and_value(a, ao, ax, 5); flow::h_fixes_writer_and_value(b, bo, bx, 2);
    survivor_schedule(rule);
    resolver_connection(rule, a); resolver_connection(rule, b);
    precedence::equal_independent_views(b);
    let credit_cuts = precedence::actual_cuts(Notice::Replication, false, false);
    precedence::two_real_cuts_exclude_both_credits(Notice::Replication, false, false, credit_cuts, credit);
    assert(observed_choice(rule, a, 12) == Side::Right && observed_choice(rule, b, 12) == Side::Left);
    if sample_row(rule, a, Replica::R1).1 == sample_row(rule, b, Replica::R1).1 {
        assert(sample_row(rule, a, Replica::R2).1 != sample_row(rule, b, Replica::R2).1) by {
            actual_local(rule, a, Process::SecondClient, 30);
            actual_local(rule, b, Process::SecondClient, 30);
        }
        assert(forwarded(rule, a, Replica::R2) && forwarded(rule, b, Replica::R2));
    } else { assert(forwarded(rule, a, Replica::R1) && forwarded(rule, b, Replica::R1)); }
    if observed_choice(rule, a, 10) == Side::Left { locate_gain(rule, a, credit); }
    else { locate_gain(rule, b, credit); }
}

// The same cache and identical on-wire headers in both implementations.
// The diagnostic changes only whether C2 consults the ordinary endorsement.
pub open spec fn value_cache(use_record: bool) -> Rule<Option<int>> {
    Rule { empty: None, remember: |_old: Option<int>, v: int| Some(v),
        header: |memo: Option<int>, v: int| if memo == Some(v) { 1nat } else { 0nat },
        elect: |left: Row, right: Row| if use_record && left.1 == 0 && right.1 == 1 { Side::Right } else { Side::Left } }
}

// Valid at any local weak-copy/confirmation state and for an arbitrary
// integer in the register. No proof or tag of weak origin enables the send,
// retention, endorsement or decision. Provenance belongs to the trace audit.
pub proof fn origin_blind_handlers<M>(rule: Rule<M>, s: Local<M>, r: Replica, id: nat, own: int, v: int)
    requires live_pair().contains(r),
    ensures ({
        let q = peer(r, v);
        let put = ProcessStep { actor: at(Replica::R3), action: Action::Send(id, q), own_local: Some(own), incoming: None };
        let take = ProcessStep { actor: at(r), action: Action::Deliver(id), own_local: Some(own), incoming: Some(q) };
        let report = answer(r, row(rule, s.memo, own, s.control.answered_first));
        let send_report = ProcessStep { actor: at(r), action: Action::Send(id, report), own_local: Some(own), incoming: None };
        let decide = ProcessStep { actor: Process::SecondClient, action: Action::Strong(Process::SecondClient),
            own_local: None, incoming: None };
        accepts(rule, s, put) == (s.control.requested && own == v)
            && accepts(rule, s, take) && update(rule, s, take) == (Local { memo: (rule.remember)(s.memo, v), ..s })
            && accepts(rule, s, send_report) == s.asked
            && accepts(rule, s, decide) == (s.left.is_some() && s.right.is_some() && s.choice.is_none())
    }),
{}

pub open spec fn local_ops(b: Fork) -> Seq<Op> { seq![observed_writer(b), Op::SR1, Op::SR2] }
pub open spec fn local_values(b: Fork) -> Seq<int> {
    let v = first_value(b);
    seq![1int, v, v, v]
}

pub open spec fn no_credit() -> precedence::Credit { |_e, _w, _v| false }

proof fn local_history(b: Fork)
    ensures crate::legal(local_ops(b), local_values(b), first_value(b), first_value(b)),
{
    let ops = local_ops(b); let xs = local_values(b);
    assert(ops[1] == Op::SR1 && ops[2] == Op::SR2);
    assert forall|k: int| 0 <= k < ops.len() implies {
        let op = #[trigger] ops[k];
        xs[k + 1] == crate::next(op, xs[k]) && xs[k] == match op {
            Op::W1 | Op::W2 => 1, _ => first_value(b),
        }
    } by { assert(k == 0 || k == 1 || k == 2); }
}

proof fn cache_audit(b: Fork)
    ensures
        audit(value_cache(false), b, no_credit()),
        b.branch == Branch::Alpha ==> pivotal(value_cache(true), b, 11) && !audit(value_cache(true), b, no_credit()),
        b.branch == Branch::Beta ==> audit(value_cache(true), b, no_credit()),
{
    let r = value_cache(true);
    resolver_connection(r, b);
    follow_packet(r, b, Replica::R2);
    let one = at(Replica::R1); let two = at(Replica::R2);
    actual_local(r, b, one, 11); actual_local(r, b, two, 11);
    actual_local(r, b, one, 12); actual_local(r, b, two, 12);
    if b.branch == Branch::Alpha {
        assert(pivotal(r, b, 11));
        if audit(r, b, no_credit()) {
            assert(seq![10int, 11int][1] == 11);
            assert(precedence::supported_read_update(source(run(r, b), 11), precedence::source_versions(),
                observed_choice(r, b, 11), observed_choice(r, b, 12), independent(r, b), no_credit()));
        }
    } else {
        assert(observed_choice(r, b, 10) == Side::Left && observed_choice(r, b, 11) == Side::Left
            && observed_choice(r, b, 12) == Side::Left);
    }
}

proof fn cache_answers(b: Fork, use_record: bool)
    ensures ({
        let r = value_cache(use_record);
        memos(r, b, 21) == (Some(first_value(b)), Some(first_value(b)))
            && second(r, b) == Some(if use_record { first_value(b) } else { 2int })
            && (use_record ==> explains(r, b, local_ops(b), local_values(b)))
            && (!use_record && b.branch == Branch::Alpha ==> forall|o: Seq<Op>, x: Seq<int>| !#[trigger] explains(r, b, o, x))
    }),
{
    hide(crate::legal);
    let r = value_cache(use_record);
    let one = at(Replica::R1); let two = at(Replica::R2);
    actual_local(r, b, one, 21); actual_local(r, b, two, 21);
    actual_local(r, b, Process::FirstClient, 18); actual_local(r, b, Process::SecondClient, 30);
    assert(second(r, b) == Some(if use_record { first_value(b) } else { 2int }));
    if use_record { local_history(b); }
    else if b.branch == Branch::Alpha {
        assert forall|o: Seq<Op>, x: Seq<int>| !#[trigger] explains(r, b, o, x) by {
            if explains(r, b, o, x) { crate::legal_history_keeps_first_read(o, x, 5, 2); }
        }
    }
}

proof fn same_cache_traffic(b: Fork)
    ensures run(value_cache(true), b) == run(value_cache(false), b),
{
    let r = value_cache(true); let log_only = value_cache(false);
    assert(run(r, b).nets =~= run(log_only, b).nets);
    assert(run(r, b).actions =~= run(log_only, b).actions);
}

// No H, A, T, credit or trace premise. The cache resolves the mixed
// quorum in favor of the ordinary SR1 sample in both actual executions.
pub proof fn value_cache_witness(branch: Branch)
    ensures ({
        let b = fork(branch);
        let r = value_cache(true); let log_only = value_cache(false);
        admitted(r, b) && weak_entry(r, b) && calls(r, b) && native_quorum(r, b)
            && memos(r, b, 21) == (Some(first_value(b)), Some(first_value(b)))
            && (forall|k: nat| 2 <= k <= 30 ==> #[trigger] weak_frame(r, b, k))
            && explains(r, b, local_ops(b), local_values(b)) && second(r, b) == Some(first_value(b))
            && forwarded(r, b, Replica::R1) && forwarded(r, b, Replica::R2)
            && (branch == Branch::Alpha ==> pivotal(r, b, 11) && !audit(r, b, no_credit()))
            && (branch == Branch::Beta ==> audit(r, b, no_credit()))
            && admitted(log_only, b) && run(r, b) == run(log_only, b)
            && memos(log_only, b, 21) == memos(r, b, 21)
            && audit(log_only, b, no_credit()) && second(log_only, b) == Some(2)
            && (branch == Branch::Alpha ==> forall|o: Seq<Op>, x: Seq<int>| !#[trigger] explains(log_only, b, o, x))
    }),
{
    hide(admitted); hide(calls); hide(native_quorum); hide(weak_entry); hide(weak_frame); hide(forwarded);
    hide(pivotal); hide(audit); hide(explains); hide(memos); hide(second); hide(run);
    let b = fork(branch);
    paired_trace_arm(value_cache(true), branch);
    paired_trace_arm(value_cache(false), branch);
    cache_answers(b, true); cache_answers(b, false);
    same_cache_traffic(b); cache_audit(b);
}

// Apply the existing effect audit at the single pivotal alpha receipt.
// Its "maintains" observer is the source of the quorum sample elected for
// SR2. Eligibility depends only on the actual causal source and the adjacent
// reached cuts. The earlier cut is a resolver input comparison, not a claim
// about a second continuation with alpha's entire history fixed.
pub type CachePair = (Option<int>, Option<int>);

pub open spec fn receipt_comparison(samples: (Report, Report), new: CachePair, old: CachePair, writer: Op) -> bool {
    let r = value_cache(true); let a = fork(Branch::Alpha); let l = run(r, a);
    samples == contest(l) && new == memos(r, a, 12) && old == memos(r, a, 11) && source(l, 11) == Some(writer)
}

pub open spec fn reports_alpha_use(labels: Set<StrongEffect<Op>>) -> bool {
    effects::reports_retained_order(
        |samples, m| elect_at(value_cache(true), samples, m),
        |_samples: (Report, Report), _m: CachePair| labels,
        |s: Side, w: Op| at_side(precedence::source_versions(), s) == w,
        |samples, new, old, w| receipt_comparison(samples, new, old, w))
}

// Instantiate the audit at a comparison whose provenance identifies one
// particular writer. Use the audit's own eligibility trigger.
proof fn label_for_writer<B, F, D, W>(resume: spec_fn(B, F) -> D, maintains: spec_fn(D, W) -> bool,
    eligible: spec_fn(B, F, F, W) -> bool, ctx: B, actual: F, prior: F, writer: W, labels: Set<StrongEffect<W>>)
    requires eligible(ctx, actual, prior, writer), maintains(resume(ctx, actual), writer),
        !maintains(resume(ctx, prior), writer),
        forall|c: B, n: F, o: F, w: W| #[trigger] eligible(c, n, o, w) ==> w == writer,
    ensures effects::reports_retained_order(resume, |_c: B, _m: F| labels, maintains, eligible)
        == labels.contains(StrongEffect::MaintainWeak(writer)),
{
    let effect_at = |_c: B, _m: F| labels;
    if effects::reports_retained_order(resume, effect_at, maintains, eligible) {
        assert(eligible(ctx, actual, prior, writer));
        assert(effect_at(ctx, actual).contains(StrongEffect::MaintainWeak(writer)));
    }
    if labels.contains(StrongEffect::MaintainWeak(writer)) {
        assert forall|c: B, n: F, o: F, w: W| #[trigger] eligible(c, n, o, w)
            && maintains(resume(c, n), w) && !maintains(resume(c, o), w)
            implies effect_at(c, n).contains(StrongEffect::MaintainWeak(w)) by { assert(w == writer); }
    }
}

proof fn label_at_alpha(labels: Set<StrongEffect<Op>>)
    ensures reports_alpha_use(labels) == labels.contains(StrongEffect::MaintainWeak(Op::W2)),
{
    hide(elect_at); hide(source); hide(memos); hide(contest); hide(run); hide(state); hide(audit); hide(forwarded);
    let r = value_cache(true); let a = fork(Branch::Alpha); let l = run(r, a);
    let samples = contest(l); let old = memos(r, a, 11); let new = memos(r, a, 12);
    cache_audit(a);
    assert(pivotal(r, a, 11) && source(l, 11) == Some(Op::W2));
    let elect = |s, m| elect_at(value_cache(true), s, m);
    let maintains = |s: Side, w: Op| at_side(precedence::source_versions(), s) == w;
    let eligible = |s, n, o, w| receipt_comparison(s, n, o, w);
    assert(maintains(elect(samples, new), Op::W2) && !maintains(elect(samples, old), Op::W2));
    assert forall|s: (Report, Report), n: CachePair, o: CachePair, w: Op|
        #[trigger] eligible(s, n, o, w) implies w == Op::W2 by {};
    label_for_writer(elect, maintains, eligible, samples, new, old, Op::W2, labels);
}

pub proof fn alpha_effect_boundary(labels: Set<StrongEffect<Op>>)
    ensures reports_alpha_use(labels) == labels.contains(StrongEffect::MaintainWeak(Op::W2)),
        reports_alpha_use(labels) ==> !effects::effects_transparent(labels),
        effects::effects_transparent(set![StrongEffect::<Op>::StrongOnly])
            && !reports_alpha_use(set![StrongEffect::<Op>::StrongOnly]),
{
    hide(reports_alpha_use);
    label_at_alpha(labels); label_at_alpha(set![StrongEffect::<Op>::StrongOnly]);
    assert(!effects::permitted(StrongEffect::MaintainWeak(Op::W2)));
}

}
