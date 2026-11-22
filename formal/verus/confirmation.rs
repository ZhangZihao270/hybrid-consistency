use vstd::prelude::*;
use crate::{Op, Replica, legal};
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::survivors::*;
use crate::sr2::{Reader, Select, reader, read_protocol, queries, report, reply_action,
    exchange_states, pivotal_at_survivor, actual_weak_notice_enables_the_same_strong_reply,
    combined_reader_supplies_sr1_sample, fresh_reader_resumes_actual_sr1_state, ordinary_quorum_can_return,
    only_initial_sr2_requests_are_sent, completed_actions};
use crate::scheduling::untouched_slot;
use crate::progress::{Execution, states_through, actions_before, follows, process_fair,
    delivery_fair, majority_up, eventually_responds, finite_prefix_is_protocol_trace};

verus! {

pub open spec fn transport_event<L, I>(e: ProcessStep<L, I>) -> bool {
    exists|n: Network<L, I>| enabled(n, e.action) && #[trigger] process_step(n, e.action) == e
}

proof fn trace_has_transport_events<L, I>(
    update: spec_fn(L, I) -> L, s: Seq<Network<L, I>>, actions: Seq<Action<I>>,
)
    requires trace(update, s, actions),
    ensures forall|i: int| 0 <= i < actions.len() ==> transport_event(#[trigger] observations(s, actions)[i]),
{
    assert forall|i: int| 0 <= i < actions.len() implies transport_event(#[trigger] observations(s, actions)[i])
        by {
            let e = observations(s, actions)[i];
            assert(enabled(s[i], e.action) && process_step(s[i], e.action) == e);
        }
}

// Directional simulation of one process's ordinary and mandatory steps,
// including the exact payload of each enabled send.
pub open spec fn simulates_handlers<S, L, I>(
    m: LocalProtocol<S, L, I>, who: Process, covers: spec_fn(S, S) -> bool,
) -> bool {
    forall|source: S, target: S, e: ProcessStep<L, I>|
        transport_event(e) && e.actor == who && #[trigger] covers(source, target) && #[trigger] (m.accept)(source, e)
        ==> (m.accept)(target, e) && covers((m.update)(source, e), (m.update)(target, e))
}

// Receiving a genuine weak status can change local memory. The process
// that has not received it can still take each action of its informed
// peer. No result, designated schedule or pair of reads occurs here.
pub open spec fn status_preserves_options<S>(
    m: LocalProtocol<S, int, Wire>, r: Replica, covers: spec_fn(S, S) -> bool,
) -> bool {
    (forall|s: S, e: ProcessStep<int, Wire>| transport_event(e) && e.actor == at(r) && e.incoming.is_some()
        && notice_to(e.incoming.unwrap(), at(r)) && #[trigger] (m.accept)(s, e)
        ==> covers((m.update)(s, e), s))
    && simulates_handlers(m, at(r), covers)
}

// The paired theorem only needs the relation to start at the one actual
// admitted receipt. Other private states need not arise at this cut.
pub open spec fn optional_at<S>(
    m: LocalProtocol<S, int, Wire>, r: Replica, local: S, e: ProcessStep<int, Wire>, covers: spec_fn(S, S) -> bool,
) -> bool {
    e.actor == at(r) && e.incoming.is_some() && notice_to(e.incoming.unwrap(), at(r))
        && (m.accept)(local, e) && covers((m.update)(local, e), local)
        && simulates_handlers(m, at(r), covers)
}

spec fn local_pair<S>(p: Process, who: Process, covers: spec_fn(S, S) -> bool, a: S, b: S) -> bool {
    if p == who { covers(a, b) } else { a == b }
}

proof fn replay_private_handlers<S, L, I>(
    src: LocalProtocol<S, L, I>, dst: LocalProtocol<S, L, I>, who: Process, covers: spec_fn(S, S) -> bool,
    es: Seq<ProcessStep<L, I>>, p: Process, k: nat,
)
    requires k <= es.len(), src.accept == dst.accept, src.update == dst.update,
        simulates_handlers(src, who, covers), accepted(src, es),
        forall|i: int| 0 <= i < es.len() ==> transport_event(#[trigger] es[i]),
        local_pair(p, who, covers, (src.initial)(p), (dst.initial)(p)),
    ensures local_pair(p, who, covers, memory(src, p, es, k), memory(dst, p, es, k)),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        replay_private_handlers(src, dst, who, covers, es, p, j);
        let e = es[j as int];
        assert((src.accept)(memory(src, e.actor, es, j), e));
    }
}

// Other processes, including the independent C2, retain their exact
// private histories even if the recipient's bookkeeping changes.
proof fn recipient_simulation_preserves_c2<S, L, I>(
    src: LocalProtocol<S, L, I>, dst: LocalProtocol<S, L, I>, r: Replica,
    covers: spec_fn(S, S) -> bool, es: Seq<ProcessStep<L, I>>,
)
    requires src.accept == dst.accept, src.update == dst.update, simulates_handlers(src, at(r), covers),
        forall|i: int| 0 <= i < es.len() ==> transport_event(#[trigger] es[i]),
        forall|p: Process| #[trigger] local_pair(p, at(r), covers, (src.initial)(p), (dst.initial)(p)),
        accepted(src, es),
    ensures accepted(dst, es), memory(src, Process::SecondClient, es, es.len())
        == memory(dst, Process::SecondClient, es, es.len()),
{
    assert forall|i: int| 0 <= i < es.len() implies {
        let e = #[trigger] es[i];
        (dst.accept)(memory(dst, e.actor, es, i as nat), e)
    } by {
        let e = es[i];
        assert((src.accept)(memory(src, e.actor, es, i as nat), e));
        replay_private_handlers(src, dst, at(r), covers, es, e.actor, i as nat);
    }
    replay_private_handlers(src, dst, at(r), covers, es, Process::SecondClient, es.len());
}

pub open spec fn fresh_send<I>(a: Action<I>, reserved: Set<nat>) -> bool {
    match a { Action::Send(id, _) => !reserved.contains(id), _ => true }
}

pub open spec fn absent_or_dead<L, I>(s: Network<L, I>, id: nat) -> bool {
    !s.pending.contains_key(id) || s.pending[id].to == Process::FirstClient
        || s.pending[id].to == Process::At(Replica::R3)
}

// No condition on reference deliveries. After R3's crash an old slot
// that is empty or addressed to R3 or C1 cannot be delivered. Fresh send
// identifiers keep it that way even if arbitrarily many strong steps run.
pub(crate) proof fn stale_slot_cannot_be_delivered<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
    reserved: Set<nat>, id: nat, k: nat,
)
    requires trace(update, states, actions), after_crash(states[0]), k <= actions.len(),
        reserved.contains(id), absent_or_dead(states[0], id),
        forall|i: int| 0 <= i < actions.len() ==> fresh_send(#[trigger] actions[i], reserved),
    ensures absent_or_dead(states[k as int], id),
        k < actions.len() ==> untouched_slot(actions[k as int], id),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        stale_slot_cannot_be_delivered(update, states, actions, reserved, id, j);
        assert(states[k as int] == advance(update, states[j as int], actions[j as int]));
        match actions[j as int] {
            Action::Send(slot, _) => { assert(slot != id); },
            Action::Deliver(slot) => { assert(slot != id); },
            _ => {},
        }
    }
    postcrash_schedule_has_only_live_actors(update, states, actions, k);
    if k < actions.len() {
        let a = actions[k as int];
        assert(enabled(states[k as int], a));
        assert(fresh_send(a, reserved));
    }
}

pub open spec fn receipt_event(n: Notice) -> ProcessStep<int, Wire> {
    process_step(checkpoint_end(alpha(n)), Action::Deliver(2))
}

pub open spec fn after_receipt(n: Notice) -> Network<int, Wire> {
    advance(|x, w| cell(x, w), checkpoint_end(alpha(n)), Action::Deliver(2))
}

pub open spec fn reference_machine<S>(m: LocalProtocol<S, int, Wire>, n: Notice) -> LocalProtocol<S, int, Wire> {
    resume_at(resume_at(m, checkpoint_observations(alpha(n))), seq![receipt_event(n)])
}

pub proof fn alpha_receipt_cut(n: Notice)
    ensures enabled(checkpoint_end(alpha(n)), Action::Deliver(2)),
        receipt_event(n).actor == at(Replica::R2) && receipt_event(n).incoming == Some(packet_for(alpha(n), 2))
            && notice_to(packet_for(alpha(n), 2), at(Replica::R2)),
        outside_delays(after_receipt(n), checkpoint_end(alpha(n)), delayed_slots()),
        forall|id: nat| #[trigger] delayed_slots().contains(id) ==> absent_or_dead(after_receipt(n), id),
{
    let a = checkpoint_end(alpha(n));
    assert forall|id: nat| !delayed_slots().contains(id) implies
        #[trigger] packet_at(a, id) == packet_at(after_receipt(n), id) by {};
}

pub proof fn reference_steps_avoid_old_slots(n: Notice, states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>)
    requires states[0] == after_receipt(n), trace(|x, w| cell(x, w), states, actions),
        forall|i: int| 0 <= i < actions.len() ==> fresh_send(#[trigger] actions[i], delayed_slots()),
    ensures forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], delayed_slots()),
{
    let update = |x, w| cell(x, w);
    alpha_receipt_cut(n);
    assert(after_crash(states[0]));
    assert forall|i: int| 0 <= i < actions.len() implies keeps_delayed_slots(#[trigger] actions[i], delayed_slots()) by {
        assert forall|id: nat| #[trigger] delayed_slots().contains(id) implies untouched_slot(actions[i], id) by {
            stale_slot_cannot_be_delivered(update, states, actions, delayed_slots(), id, i as nat);
        }
    }
}

pub open spec fn completed_at<S>(
    b: Fork, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    actions: Seq<Action<Wire>>, v: int,
) -> bool {
    let states = replay(|x, w| cell(x, w), checkpoint_end(b), actions);
    let local = resume_at(m, checkpoint_observations(b));
    let es = observations(states, actions);
    trace(|x, w| cell(x, w), states, actions) && accepted(local, es) && second_invocation(states, actions)
        && result((local.initial)(Process::SecondClient)).is_none() && sr2_result(local, result, es) == Some(v)
}

pub open spec fn can_release(b: Fork, actions: Seq<Action<Wire>>) -> bool {
    let end = replay(|x, w| cell(x, w), checkpoint_end(b), actions).last();
    packet_at(end, 2) == Some(packet_for(b, 2)) && enabled(end, Action::Deliver(2))
        && survivor(advance(|x, w| cell(x, w), end, Action::Deliver(2))) == survivor(end)
}

pub proof fn deferred_notice_is_transport_enabled(b: Fork, actions: Seq<Action<Wire>>)
    requires trace(|x, w| cell(x, w), replay(|x, w| cell(x, w), checkpoint_end(b), actions), actions),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], delayed_slots()),
    ensures can_release(b, actions),
{
    let update = |x, w| cell(x, w);
    let s = replay(update, checkpoint_end(b), actions);
    assert(s[0] == checkpoint_end(b)) by { reveal(replay); }
    assert(delayed_slots().contains(2nat));
    assert forall|i: int| 0 <= i < actions.len() implies untouched_slot(#[trigger] actions[i], 2)
        by { assert(keeps_delayed_slots(actions[i], delayed_slots())); }
    withheld_packet_stays_pending(update, s, actions, 2, actions.len() as int);
    postcrash_schedule_has_only_live_actors(update, s, actions, actions.len());
}

// The reference can have the status in hand before C2 even sends. Every
// mandatory step of its finite response suffix is replayed. Only fresh
// allocation of old packet identifiers is constrained, never a receive.
pub proof fn paired_completion_from_received_status<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    covers: spec_fn(S, S) -> bool, states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>, v: int,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>,
)
    requires
        accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        optional_at(m, Replica::R2, (resume_at(m, checkpoint_observations(alpha(n))).initial)(at(Replica::R2)),
            receipt_event(n), covers),
        states[0] == after_receipt(n), trace(|x, w| cell(x, w), states, actions),
        second_invocation(states, actions), result((reference_machine(m, n).initial)(Process::SecondClient)).is_none(),
        forall|i: int| 0 <= i < actions.len() ==> fresh_send(#[trigger] actions[i], delayed_slots()),
        accepted(reference_machine(m, n), observations(states, actions)),
        sr2_result(reference_machine(m, n), result, observations(states, actions)) == Some(v),
    ensures
        invocation_only(actions, Process::FirstClient, Set::empty()),
        forall|i: int| 0 <= i < actions.len() ==> keeps_delayed_slots(#[trigger] actions[i], delayed_slots()),
        completed_at(alpha(n), m, result, actions, v), completed_at(beta(n), m, result, actions, v),
        can_release(alpha(n), actions), can_release(beta(n), actions),
        first_result(m, first, alpha(n)) == 5 && first_result(m, first, beta(n)) == 2,
        !(legal(ao, ax, 5, v) && legal(bo, bx, 2, v)),
{
    hide(memory); hide(replay); hide(accepted); hide(legal);
    let update = |x, w| cell(x, w);
    let a = alpha(n);
    let ref_events = observations(states, actions);
    let before = resume_at(m, checkpoint_observations(a));
    alpha_receipt_cut(n);
    reference_steps_avoid_old_slots(n, states, actions);
    postcrash_schedule_has_only_live_actors(update, states, actions, actions.len());
    assert forall|i: int| 0 <= i < actions.len() implies match #[trigger] actions[i] {
        Action::Send(_, p) => p.from != Process::FirstClient,
        _ => true,
    } by { assert(survivor_actor(process_step(states[i], actions[i]).actor)); }
    trace_has_transport_events(update, states, actions);
    let informed = reference_machine(m, n);
    assert((informed.initial)(Process::SecondClient) == (before.initial)(Process::SecondClient)) by { reveal_with_fuel(memory, 2); }
    assert forall|p: Process| #[trigger] local_pair(p, at(Replica::R2), covers,
        (informed.initial)(p), (before.initial)(p)) by { reveal_with_fuel(memory, 2); }
    recipient_simulation_preserves_c2(informed, before, Replica::R2, covers, ref_events);
    replay_sr2_without_touching_delayed_slots(update, states, checkpoint_end(a), actions, delayed_slots());
    let delayed = replay(update, checkpoint_end(a), actions);
    assert(delayed[0] == checkpoint_end(a)) by { reveal(replay); }
    one_completed_sr2_from_constructed_prefixes(n, m, first, result, delayed, actions, v, ao, ax, bo, bx);
    let b = beta(n);
    replay_sr2_without_touching_delayed_slots(update, delayed, checkpoint_end(b), actions, delayed_slots());
    let fresh = Process::SecondClient;
    arbitrary_survivor_memory_agrees(n, m, fresh, actions_to_crash(a).len());
    assert((resume_at(m, checkpoint_observations(b)).initial)(fresh) == (before.initial)(fresh))
        by { reveal(resume_at); }
    deferred_notice_is_transport_enabled(a, actions);
    deferred_notice_is_transport_enabled(beta(n), actions);
}

pub open spec fn reference_response<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>,
) -> Option<int> {
    sr2_result(reference_machine(m, n), result, observations(states, actions))
}

// A reference is an execution of the actual private protocol. The client
// contract fixes the outgoing invocation on every completed prefix. It
// neither supplies a response nor puts any restriction on weak deliveries.
pub open spec fn admissible_service<S>(
    start: Network<int, Wire>, local: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, e: Execution<int, Wire>,
) -> bool {
    (e.state)(0) == start && follows(e, |x, w| cell(x, w), |s, a| true)
        && (forall|i: nat| fresh_send(#[trigger] (e.action)(i), delayed_slots()))
        && forall|k: nat| {
            let a = #[trigger] actions_before(e, k);
            let s = states_through(e, k);
            let es = observations(s, a);
            accepted(local, es) && only_request_sends(a, Process::SecondClient, live_pair())
                && fanout_before_receiving(es, Process::SecondClient)
                && (sr2_result(local, result, es).is_some()
                    ==> invocation_only(a, Process::SecondClient, live_pair()))
        }
}

pub open spec fn admissible_reference<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, e: Execution<int, Wire>,
) -> bool {
    admissible_service(after_receipt(n), reference_machine(m, n), result, e)
}

pub(crate) proof fn first_true(done: spec_fn(nat) -> bool, k: nat) -> (first: nat)
    requires done(k),
    ensures first <= k, done(first), forall|i: nat| i < first ==> !#[trigger] done(i),
    decreases k,
{
    if exists|i: nat| i < k && #[trigger] done(i) {
        first_true(done, choose|i: nat| i < k && #[trigger] done(i))
    } else { k }
}

// A response observed on an admissible prefix has an actual first return.
// Fairness is needed only by callers that obtain the observation using A.
pub proof fn finite_observed_service<S>(
    start: Network<int, Wire>, local: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    e: Execution<int, Wire>, some_k: nat,
) -> (answer: (nat, int))
    requires admissible_service(start, local, result, e),
        sr2_result(local, result, observations(states_through(e,some_k),actions_before(e,some_k))).is_some(),
    ensures answer.0 <= some_k, ({
        let (k, v) = answer;
        let s = states_through(e, k); let a = actions_before(e, k);
        s[0] == start && trace(|x, w| cell(x, w), s, a) && second_invocation(s, a)
            && accepted(local, observations(s, a))
            && result((local.initial)(Process::SecondClient)).is_none()
            && sr2_result(local, result, observations(s, a)) == Some(v) && pending_before_end(local, result, observations(s, a))
            && (forall|i: int| 0 <= i < a.len() ==> fresh_send(#[trigger] a[i], delayed_slots()))
    }),
{
    hide(accepted); hide(trace); hide(invocation_only);
    let update = |x, w| cell(x, w);
    let done = |s, a| sr2_result(local, result, observations(s, a)).is_some();
    let at_prefix = |j: nat| done(states_through(e, j), actions_before(e, j));
    let k = first_true(at_prefix, some_k);
    let a = actions_before(e, k); let s = states_through(e, k);
    let v = sr2_result(local, result, observations(s, a)).unwrap();
    finite_prefix_is_protocol_trace(e, update, |s, a| true, k);
    assert forall|i: int| 0 <= i < a.len() implies fresh_send(#[trigger] a[i], delayed_slots())
        by { assert(a[i] == (e.action)(i as nat)); }
    let empty = actions_before(e, 0);
    assert(empty.len() == 0 && live_pair().contains(Replica::R1));
    assert(!invocation_only(empty, Process::SecondClient, live_pair())) by {
        reveal(invocation_only);
        assert(!(exists|i: int| 0 <= i < empty.len() && client_sends_to(#[trigger] empty[i], Process::SecondClient, Replica::R1)));
    }
    assert(sr2_result(local, result, observations(states_through(e, 0), empty)).is_none());
    assert(result((local.initial)(Process::SecondClient)).is_none())
        by { reveal(memory); }
    let obs = observations(s, a);
    assert forall|j: nat| j < obs.len() implies result(#[trigger] memory(local, Process::SecondClient, obs, j)).is_none() by {
        let earlier = observations(states_through(e, j), actions_before(e, j));
        assert(!at_prefix(j));
        assert forall|i: int| 0 <= i < j implies #[trigger] earlier[i] == #[trigger] obs[i] by {};
        memory_on_common_prefix(local, Process::SecondClient, earlier, obs, j);
    }
    (k, v)
}

// Extract a real response before making any assumption about postponing the notice.
pub proof fn finite_fair_service<S>(
    start: Network<int, Wire>, local: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
) -> (answer: (nat, int))
    requires after_crash(start), admissible_service(start, local, result, e), delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| sr2_result(local, result, observations(s, a)).is_some()),
    ensures ({
        let (k, v) = answer;
        let s = states_through(e, k); let a = actions_before(e, k);
        s[0] == start && trace(|x, w| cell(x, w), s, a) && second_invocation(s, a)
            && accepted(local, observations(s, a))
            && result((local.initial)(Process::SecondClient)).is_none()
            && sr2_result(local, result, observations(s, a)) == Some(v) && pending_before_end(local, result, observations(s, a))
            && (forall|i: int| 0 <= i < a.len() ==> fresh_send(#[trigger] a[i], delayed_slots()))
    }),
{
    hide(accepted); hide(trace); hide(invocation_only);
    let update = |x, w| cell(x, w);
    let done = |s, a| sr2_result(local, result, observations(s, a)).is_some();
    assert forall|k: nat| majority_up(#[trigger] (e.state)(k)) by {
        let a = actions_before(e, k); let s = states_through(e, k);
        finite_prefix_is_protocol_trace(e, update, |s, a| true, k);
        assert(s[0] == start);
        postcrash_schedule_has_only_live_actors(update, s, a, k);
        assert(s[k as int] == (e.state)(k));
    }
    let some_k = choose|k: nat| #[trigger] done(states_through(e, k), actions_before(e, k));
    finite_observed_service(start,local,result,e,some_k)
}

pub proof fn finite_fair_reference_response<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
) -> (answer: (nat, int))
    requires admissible_reference(n, m, result, e), delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| reference_response(n, m, result, s, a).is_some()),
    ensures ({
        let (k, v) = answer;
        let s = states_through(e, k); let a = actions_before(e, k);
        s[0] == after_receipt(n) && trace(|x, w| cell(x, w), s, a) && second_invocation(s, a)
            && accepted(reference_machine(m, n), observations(s, a))
            && result((reference_machine(m, n).initial)(Process::SecondClient)).is_none()
            && reference_response(n, m, result, s, a) == Some(v)
            && pending_before_end(reference_machine(m, n), result, observations(s, a))
            && (forall|i: int| 0 <= i < a.len() ==> fresh_send(#[trigger] a[i], delayed_slots()))
    }),
{
    hide(accepted); hide(trace); hide(memory); hide(eventually_responds); hide(admissible_service);
    hide(second_invocation); hide(delivery_fair); hide(process_fair); hide(sr2_result);
    let local = reference_machine(m, n);
    let done = |s, a| reference_response(n, m, result, s, a).is_some();
    let observed = |s, a| sr2_result(local, result, observations(s, a)).is_some();
    assert(done =~= observed);
    assert(after_crash(after_receipt(n)));
    finite_fair_service(after_receipt(n), local, result, e, runnable)
}

// Fair progress is invoked only on the post-delivery reference. No
// assumption here supplies a finite response in either held execution.
pub proof fn fair_reference_gives_paired_sr2<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    covers: spec_fn(S, S) -> bool, e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>,
)
    requires
        accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        optional_at(m, Replica::R2, (resume_at(m, checkpoint_observations(alpha(n))).initial)(at(Replica::R2)),
            receipt_event(n), covers),
        admissible_reference(n, m, result, e), delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| reference_response(n, m, result, s, a).is_some()),
    ensures exists|k: nat, v: int| #![trigger completed_at(alpha(n), m, result, actions_before(e, k), v)] {
        let a = actions_before(e, k);
        reference_response(n, m, result, states_through(e, k), a) == Some(v)
            && invocation_only(a, Process::FirstClient, Set::empty()) && invocation_only(a, Process::SecondClient, live_pair())
            && (forall|i: int| 0 <= i < a.len() ==> keeps_delayed_slots(#[trigger] a[i], delayed_slots()))
            && completed_at(alpha(n), m, result, a, v) && completed_at(beta(n), m, result, a, v)
            && can_release(alpha(n), a) && can_release(beta(n), a)
            && first_result(m, first, alpha(n)) == 5 && first_result(m, first, beta(n)) == 2
            && !(legal(ao, ax, 5, v) && legal(bo, bx, 2, v))
    },
{
    hide(accepted); hide(trace); hide(legal); hide(completed_at); hide(invocation_only);
    let (k, v) = finite_fair_reference_response(n, m, result, e, runnable);
    let a = actions_before(e, k); let s = states_through(e, k);
    paired_completion_from_received_status(n, m, first, result, covers, s, a, v, ao, ax, bo, bx);
    assert(completed_at(alpha(n), m, result, actions_before(e, k), v));
}

// All ordinary state, including the first participation flags, request
// sets, and actual strong replies, can be consulted by the ungated reader.
// The weak delivery can change the recipient's private knowledge.
pub open spec fn same_except_status(a: Reader, b: Reader) -> bool {
    Reader { prior: Control { learned: b.prior.learned, ..a.prior }, ..a } == b
}

pub proof fn ungated_reader_preserves_options(r: Replica, n: Notice, select: Select)
    ensures status_preserves_options(read_protocol(Set::empty(), n, select), r, |a, b| same_except_status(a, b)),
{
    let m = read_protocol(Set::empty(), n, select);
    assert forall|s: Reader, e: ProcessStep<int, Wire>| e.actor == at(r) && e.incoming.is_some()
        && notice_to(e.incoming.unwrap(), at(r)) && #[trigger] (m.accept)(s, e)
        implies same_except_status((m.update)(s, e), s) by {};
}

// Instantiate the received-status premise on a real, completed reference
// of the same reader. Its second responder learns G before the exchange.
// Its different private knowledge is preserved throughout the replay.
pub proof fn actual_g_reference_supports_the_held_pair(
    select: Select, ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>,
)
    ensures ({
        let n = Notice::G; let a = alpha(n); let b = beta(n);
        let m = read_protocol(Set::empty(), n, select);
        let steps = completed_actions(a); let result = |s: Reader| s.returned;
        let src = replay(|x, w| cell(x, w), after_receipt(n), steps);
        let v = select(report(a, Replica::R1), report(a, Replica::R2));
        pre_sr1_g(a, weak_assignment(a, true).ops) && pre_sr1_g(b, weak_assignment(b, true).ops)
            && trace(|x, w| cell(x, w), src, steps) && accepted(reference_machine(m, n), observations(src, steps))
            && (reference_machine(m, n).initial)(at(Replica::R2)).prior.learned == Some(Notice::G)
            && checkpoint_control(a, at(Replica::R2)).learned.is_none()
            && reference_response(n, m, result, src, steps) == Some(v)
            && completed_at(a, m, result, steps, v) && completed_at(b, m, result, steps, v)
            && !(legal(ao, ax, 5, v) && legal(bo, bx, 2, v))
    }),
{
    hide(memory); hide(replay); hide(trace); hide(accepted); hide(legal); hide(completed_at);
    let n = Notice::G; let a = alpha(n); let b = beta(n); let gates = Set::empty();
    let m = read_protocol(gates, n, select); let result = |s: Reader| s.returned;
    let first = |s: Reader| s.prior.reply.unwrap(); let covers = |x,y| same_except_status(x,y);
    let update = |x, w| cell(x, w);
    let steps = completed_actions(a); let old = exchange_states(a, true);
    let es = observations(old, steps); let v = select(report(a, Replica::R1), report(a, Replica::R2));
    weak_assignment_at_delivery(a, true); weak_assignment_at_delivery(b, true);
    copies_and_knowledge_at_checkpoint(a, weak_assignment(a, true).ops);
    alpha_receipt_cut(n);
    fresh_reader_resumes_actual_sr1_state(a, gates, select);
    fresh_reader_resumes_actual_sr1_state(b, gates, select);
    combined_reader_supplies_sr1_sample(a, gates, select);
    combined_reader_supplies_sr1_sample(b, gates, select);
    only_initial_sr2_requests_are_sent(a, true);
    ordinary_quorum_can_return(a, gates, select);
    assert(outside_delays(checkpoint_end(a), after_receipt(n), delayed_slots()));
    assert forall|i: int| 0 <= i < steps.len() implies keeps_delayed_slots(#[trigger] steps[i], delayed_slots())
        && fresh_send(steps[i], delayed_slots()) by { crate::checkpoint::prefix_index(i); }
    replay_sr2_without_touching_delayed_slots(update, old, after_receipt(n), steps, delayed_slots());
    let src = replay(update, after_receipt(n), steps);
    let before = reader(a, gates, select); let informed = reference_machine(m, n);
    ungated_reader_preserves_options(Replica::R2, n, select);
    assert forall|p: Process| #[trigger] local_pair(p, at(Replica::R2), covers,
        (before.initial)(p), (informed.initial)(p)) by { reveal_with_fuel(memory, 2); }
    trace_has_transport_events(update, old, steps);
    recipient_simulation_preserves_c2(before, informed, Replica::R2, covers, es);
    assert(transport_event(receipt_event(n))) by {
        let cut = checkpoint_end(a); let e = receipt_event(n);
        assert(enabled(cut, e.action) && process_step(cut, e.action) == e);
    }
    assert(optional_at(m, Replica::R2, (before.initial)(at(Replica::R2)), receipt_event(n), covers));
    assert(src[0] == after_receipt(n)) by { reveal(replay); }
    assert((informed.initial)(Process::SecondClient) == (before.initial)(Process::SecondClient))
        by { reveal_with_fuel(memory, 2); }
    paired_completion_from_received_status(n, m, first, result, covers, src, steps, v, ao, ax, bo, bx);
    assert((informed.initial)(at(Replica::R2)).prior.learned == Some(Notice::G))
        by { reveal_with_fuel(memory, 2); }
}

pub proof fn pivotal_gate_fails_every_simulation(b: Fork, select: Select, covers: spec_fn(Reader, Reader) -> bool)
    ensures !status_preserves_options(read_protocol(set![crate::origin(b.branch)], b.notice, select), crate::origin(b.branch), covers),
{
    hide(memory);
    let r = crate::origin(b.branch); let gates = set![r];
    let m = reader(b, gates, select);
    let q = exchange_states(b, false);
    let obs = observations(q, queries());
    let local = memory(m, at(r), obs, obs.len());
    let notice = process_step(q[4], Action::Deliver(2));
    let reply = process_step(q[4], reply_action(r, report(b, r)));
    actual_weak_notice_enables_the_same_strong_reply(b, gates, select);
    assert(pivotal_at_survivor(b, gates, select));
    assert(transport_event(notice) && transport_event(reply)) by {
        assert(process_step(q[4], notice.action) == notice && enabled(q[4], notice.action));
        assert(process_step(q[4], reply.action) == reply && enabled(q[4], reply.action));
    }
    if status_preserves_options(read_protocol(gates, b.notice, select), r, covers) {
        assert(covers((m.update)(local, notice), local));
        assert((m.accept)((m.update)(local, notice), reply));
        assert((m.accept)(local, reply));
    }
}

// Boundary of the sufficient simulation rule. A replica stamps an
// ordinary peer message with a counter incremented on *every* delivery.
// Its peer needs the message but ignores the stamp when serving a read.
pub struct Clocked { pub ticks: nat, pub peer_arrived: bool }

pub open spec fn stamped_request(t: nat) -> Action<Wire> {
    send(15, Path::Strong, at(Replica::R2), at(Replica::R1), Wire::Peer(t as int))
}

pub open spec fn clock_handler() -> LocalProtocol<Clocked, int, Wire> {
    LocalProtocol {
        initial: |p| Clocked { ticks: 0, peer_arrived: false },
        accept: |s: Clocked, e: ProcessStep<int, Wire>| match e.action {
            Action::Send(_, p) if p.input is Peer => e.action == stamped_request(s.ticks),
            Action::Send(_, p) if p.input is Answer2 => s.peer_arrived && e.own_local == Some(p.input->Answer2_0.value),
            _ => true,
        },
        update: |s: Clocked, e: ProcessStep<int, Wire>| match e.incoming {
            Some(p) => Clocked { ticks: s.ticks + 1, peer_arrived: s.peer_arrived
                || (p.from == at(Replica::R2) && p.to == at(Replica::R1) && p.path == Path::Strong && p.input is Peer) },
            None => s,
        },
        done: |s: Clocked| s.peer_arrived,
    }
}

pub open spec fn peer_can_reply(t: nat, delivered: bool) -> bool {
    let b = alpha(Notice::G); let old = crate::sr2::exchange_net(b, 4); let m = clock_handler();
    let up = |x, w| cell(x, w); let ack = Action::Deliver(2);
    let s = Clocked { ticks: t, peer_arrived: false };
    let net = if delivered { advance(up, old, ack) } else { old };
    let sender = if delivered { (m.update)(s, process_step(old, ack)) } else { s };
    let ping = stamped_request(sender.ticks);
    let mid = advance(up, net, ping); let receive = Action::Deliver(15);
    let end = advance(up, mid, receive);
    let e = process_step(mid, receive);
    let reply = reply_action(Replica::R1, report(b, Replica::R1));
    enabled(old, ack) && (m.accept)(s, process_step(old, ack))
        && enabled(net, ping) && (m.accept)(sender, process_step(net, ping))
        && enabled(mid, receive) && (m.accept)(s, e)
        && !(m.accept)(s, process_step(net, reply))
        && enabled(end, reply) && (m.accept)((m.update)(s, e), process_step(end, reply))
        && process_step(net, reply) == process_step(end, reply)
        && end.pending.contains_key(2) == !delivered
}

pub proof fn a_changed_clock_header_need_not_block_a_quorum_reply(t: nat, covers: spec_fn(Clocked, Clocked) -> bool)
    ensures peer_can_reply(t, true), peer_can_reply(t, false),
        !status_preserves_options(clock_handler(), Replica::R2, covers),
{
    let b = alpha(Notice::G); let n = crate::sr2::exchange_net(b, 4); let m = clock_handler();
    prefix_memory_tracks_actual_messages(b, at(Replica::R1), actions_to_crash(b).len());
    let s = Clocked { ticks: t, peer_arrived: false };
    let ack = process_step(n, Action::Deliver(2)); let informed = (m.update)(s, ack);
    let stamp = process_step(n, stamped_request(t + 1));
    assert(transport_event(ack) && transport_event(stamp)) by {
        assert(process_step(n, ack.action) == ack && enabled(n, ack.action));
        assert(process_step(n, stamp.action) == stamp && enabled(n, stamp.action));
    }
    if status_preserves_options(m, Replica::R2, covers) {
        assert((m.accept)(s, ack) && notice_to(ack.incoming.unwrap(), at(Replica::R2)));
        assert(covers(informed, s));
        assert((m.accept)(informed, stamp));
        assert((m.accept)(s, stamp));
    }
}

}
