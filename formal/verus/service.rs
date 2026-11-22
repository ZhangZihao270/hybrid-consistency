use vstd::prelude::*;
use crate::{Op, Replica, legal};
use crate::checkpoint::*;
use crate::confirmation::*;
use crate::delivery::*;
use crate::progress::{Execution, actions_before, states_through, delivery_fair, process_fair, eventually_responds};
use crate::protocol::*;
use crate::survivors::*;

verus! {

// A finite behavior of one pending read. Freshness concerns allocation only.
// The protocol can require any enabled message or local step before responding.
pub open spec fn response_path<S>(
    m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, net: Network<int, Wire>,
    reserved: Set<nat>, states: Seq<Network<int, Wire>>, actions: Seq<Action<Wire>>, v: int,
) -> bool {
    let obs = observations(states, actions);
    states[0] == net && trace(|x, w| cell(x, w), states, actions)
        && accepted(m, obs) && second_invocation(states, actions)
        && result((m.initial)(Process::SecondClient)).is_none() && pending_before_end(m, result, obs) && sr2_result(m, result, obs) == Some(v)
        && forall|i: int| 0 <= i < actions.len() ==> fresh_send(#[trigger] actions[i], reserved)
}

pub proof fn response_uses_local_callbacks<S>(
    m:LocalProtocol<S,int,Wire>, other:LocalProtocol<S,int,Wire>, result:spec_fn(S)->Option<int>,
    net:Network<int,Wire>, reserved:Set<nat>, t:Seq<Network<int,Wire>>, a:Seq<Action<Wire>>, v:int,
)
    requires m.initial==other.initial,
        forall|i:int,x:S| 0<=i<a.len() ==> #[trigger] same_callbacks(m,other,x,observations(t,a)[i]),
    ensures response_path(m,result,net,reserved,t,a,v)==response_path(other,result,net,reserved,t,a,v),
{
    hide(trace); hide(second_invocation); hide(fresh_send); hide(memory);
    let es=observations(t,a); let c=Process::SecondClient;
    assert forall|i:int| 0<=i<a.len() implies {
        let e=#[trigger] es[i]; (m.accept)(memory(m,e.actor,es,i as nat),e)==(other.accept)(memory(other,e.actor,es,i as nat),e)
    } by {
        let e=es[i]; identical_callbacks_on_log(m,other,es,e.actor,i as nat);
        assert(same_callbacks(m,other,memory(m,e.actor,es,i as nat),e));
    }
    assert forall|k:nat| k<=es.len() implies #[trigger] memory(m,c,es,k)==#[trigger] memory(other,c,es,k)
        by { identical_callbacks_on_log(m,other,es,c,k); }
    assert(accepted(m,es)==accepted(other,es));
    assert(pending_before_end(m,result,es)==pending_before_end(other,result,es)) by {
        if pending_before_end(m,result,es) {
            assert forall|k:nat| k<es.len() implies result(#[trigger] memory(other,c,es,k)).is_none()
                by { identical_callbacks_on_log(m,other,es,c,k); assert(result(memory(m,c,es,k)).is_none()); }
        }
        if pending_before_end(other,result,es) {
            assert forall|k:nat| k<es.len() implies result(#[trigger] memory(m,c,es,k)).is_none()
                by { identical_callbacks_on_log(m,other,es,c,k); assert(result(memory(other,c,es,k)).is_none()); }
        }
    }
    identical_callbacks_on_log(m,other,es,c,es.len());
}

pub open spec fn can_respond<S>(
    m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, net: Network<int, Wire>, reserved: Set<nat>,
) -> bool {
    exists|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int| #[trigger] response_path(m, result, net, reserved, s, a, v)
}

// A behavioral test for a necessary receipt, independent of forks, H and values.
// Both tests have exactly the ordinary opportunities remaining after the input.
// Only the addressed process executes the receipt. Its entire private state counts.
pub open spec fn enables_service<S>(
    m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, net: Network<int, Wire>,
    id: nat, reserved: Set<nat>,
) -> bool {
    let a = Action::Deliver(id);
    let e = process_step(net, a);
    let ordinary = advance(|x, w| cell(x, w), net, a);
    enabled(net, a) && e.incoming.is_some() && e.actor is At && notice_to(e.incoming.unwrap(), e.actor)
        && (m.accept)((m.initial)(e.actor), e)
        && can_respond(resume_at(m, seq![e]), result, ordinary, reserved)
        && !can_respond(m, result, ordinary, reserved)
}

// Keeping the real packet in flight and omitting it from the ordinary
// opportunities are equivalent for these paths. Neither end removes a required
// strong delivery. No condition on the bytes or length of an informed path.
pub proof fn existing_notice_is_the_only_extra_opportunity<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    states: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires response_path(m, result, after_receipt(n), delayed_slots(), states, a, v),
    ensures ({
        let held = replay(|x, w| cell(x, w), checkpoint_end(alpha(n)), a);
        response_path(m, result, checkpoint_end(alpha(n)), delayed_slots(), held, a, v)
            && observations(held, a) == observations(states, a)
            && (forall|i: int| 0 <= i < a.len() ==> keeps_delayed_slots(#[trigger] a[i], delayed_slots()))
            && can_release(alpha(n), a)
    }),
{
    hide(accepted); hide(replay);
    alpha_receipt_cut(n);
    reference_steps_avoid_old_slots(n, states, a);
    replay_sr2_without_touching_delayed_slots(|x, w| cell(x, w), states, checkpoint_end(alpha(n)), a, delayed_slots());
    assert(replay(|x, w| cell(x, w), checkpoint_end(alpha(n)), a)[0] == checkpoint_end(alpha(n))) by { reveal(replay); }
    deferred_notice_is_transport_enabled(alpha(n), a);
}

pub proof fn held_path_is_an_ordinary_opportunity<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    states: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires response_path(m, result, checkpoint_end(alpha(n)), delayed_slots(), states, a, v),
        forall|i: int| 0 <= i < a.len() ==> keeps_delayed_slots(#[trigger] a[i], delayed_slots()),
    ensures response_path(m, result, after_receipt(n), delayed_slots(), replay(|x, w| cell(x, w), after_receipt(n), a), a, v),
{
    hide(replay); hide(accepted);
    alpha_receipt_cut(n);
    assert(outside_delays(checkpoint_end(alpha(n)), after_receipt(n), delayed_slots()));
    replay_sr2_without_touching_delayed_slots(|x, w| cell(x, w), states, after_receipt(n), a, delayed_slots());
    assert(replay(|x, w| cell(x, w), after_receipt(n), a)[0] == after_receipt(n)) by { reveal(replay); }
}

pub open spec fn first_return_at<S>(
    b: Fork, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, a: Seq<Action<Wire>>,
) -> bool {
    let local = resume_at(m, checkpoint_observations(b));
    pending_before_end(local, result, observations(replay(|x, w| cell(x, w), checkpoint_end(b), a), a))
}

pub open spec fn incompatible_completions<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    a: Seq<Action<Wire>>, v: int,
) -> bool {
    first_result(m, first, alpha(n)) == 5 && first_result(m, first, beta(n)) == 2
        && completed_at(alpha(n), m, result, a, v) && completed_at(beta(n), m, result, a, v)
        && first_return_at(alpha(n), m, result, a) && first_return_at(beta(n), m, result, a)
        && (forall|i: int| 0 <= i < a.len() ==> keeps_delayed_slots(#[trigger] a[i], delayed_slots()))
        && can_release(alpha(n), a) && can_release(beta(n), a)
        && !(exists|ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>|
            #[trigger] legal(ao, ax, 5, v) && #[trigger] legal(bo, bx, 2, v))
}

// Only the held alpha and beta share a witness. No behavioral relation
// between the informed reference and held alpha is required.
pub proof fn pair_from_ordinary_path<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        response_path(resume_at(m, checkpoint_observations(alpha(n))), result, after_receipt(n), delayed_slots(), s, a, v),
    ensures incompatible_completions(n, m, first, result, a, v),
{
    hide(accepted); hide(replay); hide(legal); hide(memory);
    let pre = resume_at(m, checkpoint_observations(alpha(n)));
    existing_notice_is_the_only_extra_opportunity(n, pre, result, s, a, v);
    let held = replay(|x, w| cell(x, w), checkpoint_end(alpha(n)), a);
    let b = beta(n);
    surviving_checkpoint_agreement(n);
    replay_sr2_without_touching_delayed_slots(|x, w| cell(x, w), held, checkpoint_end(b), a, delayed_slots());
    arbitrary_survivor_memory_agrees(n, m, Process::SecondClient, actions_to_crash(alpha(n)).len());
    replay_completed_sr2_at_checkpoints(n, m, first, result, held, a, v);
    let other = resume_at(m, checkpoint_observations(b));
    let es = observations(held, a); let c = Process::SecondClient;
    assert forall|k: nat| k < es.len() implies result(#[trigger] memory(other, c, es, k)).is_none() by {
        crate::protocol::memory_for_live_actor_agrees(m, checkpoint_observations(alpha(n)), checkpoint_observations(b), es, c, k);
        assert(result(memory(pre, c, es, k)).is_none());
    }
    deferred_notice_is_transport_enabled(b, a);
    assert forall|ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>|
        !(#[trigger] legal(ao, ax, 5, v) && #[trigger] legal(bo, bx, 2, v)) by {
        if legal(ao, ax, 5, v) && legal(bo, bx, 2, v) {
            crate::conditional_history_contradiction(ao, ax, bo, bx, v);
        }
    }
    assert(incompatible_completions(n, m, first, result, a, v));
}

pub proof fn service_before_receipt_yields_actual_pair<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        can_respond(resume_at(m, checkpoint_observations(alpha(n))), result, after_receipt(n), delayed_slots()),
    ensures exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v),
{
    hide(accepted); hide(replay); hide(legal); hide(memory);
    let pre = resume_at(m, checkpoint_observations(alpha(n)));
    let net = after_receipt(n);
    let (s, a, v) = choose|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
        #[trigger] response_path(pre, result, net, delayed_slots(), s, a, v);
    pair_from_ordinary_path(n, m, first, result, s, a, v);
}

pub proof fn fair_read_or_necessary_weak_receipt<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        (m.accept)((resume_at(m, checkpoint_observations(alpha(n))).initial)(at(Replica::R2)), receipt_event(n)),
        admissible_reference(n, m, result, e), delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| reference_response(n, m, result, s, a).is_some()),
    ensures
        (exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v))
        || enables_service(resume_at(m, checkpoint_observations(alpha(n))), result, checkpoint_end(alpha(n)), 2, delayed_slots()),
{
    let pre = resume_at(m, checkpoint_observations(alpha(n)));
    let net = after_receipt(n);
    if can_respond(pre, result, net, delayed_slots()) {
        service_before_receipt_yields_actual_pair(n, m, first, result);
    } else {
        let (k, v) = finite_fair_reference_response(n, m, result, e, runnable);
        let s = states_through(e, k); let a = actions_before(e, k);
        assert(response_path(reference_machine(m, n), result, net, delayed_slots(), s, a, v));
        alpha_receipt_cut(n);
    }
}

// A generic necessity test on an issued input to one pending read. Every
// legal finite response opportunity counts, including alternate quorums,
// timers and mandatory protocol traffic admitted by its local handlers.
pub open spec fn consumed_issue(
    net: Network<int, Wire>, id: nat, s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>,
) -> bool {
    net.pending.contains_key(id) && exists|i: int| 0 <= i < a.len()
        && #[trigger] a[i] == Action::Deliver(id) && observations(s, a)[i].incoming == Some(net.pending[id])
}

pub open spec fn receipt_prerequisite<S>(
    m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, net: Network<int, Wire>, reserved: Set<nat>, id: nat,
) -> bool {
    can_respond(m, result, net, reserved)
        && forall|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
            #[trigger] response_path(m, result, net, reserved, s, a, v) ==> consumed_issue(net, id, s, a)
}

// Locate the actual necessary input on any successful execution. A notice
// reaches a replica before C2 returns. Its callback can change that replica's
// private state, while the shared registers and all other private states persist.
pub proof fn necessary_notice_precedes_first_return<S>(
    m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, net: Network<int, Wire>, reserved: Set<nat>, id: nat,
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
) -> (i: nat)
    requires receipt_prerequisite(m, result, net, reserved, id), response_path(m, result, net, reserved, s, a, v),
        net.pending.contains_key(id), notice_to(net.pending[id], net.pending[id].to),
    ensures ({
        let es = observations(s, a); let p = net.pending[id].to; let c = Process::SecondClient;
        i + 1 < a.len() && a[i as int] == Action::Deliver(id) && es[i as int].incoming == Some(net.pending[id])
            && es[i as int].actor == p && es.last().actor == c && result(memory(m, c, es, i + 1)).is_none()
            && s[i as int + 1].locals == s[i as int].locals && s[i as int + 1].pending == s[i as int].pending.remove(id)
            && forall|q: Process| q != p ==> #[trigger] memory(m, q, es, i + 1) == memory(m, q, es, i)
    }),
{
    hide(accepted); hide(second_invocation); hide(fresh_send); hide(memory); hide(can_respond);
    let es = observations(s, a); let c = Process::SecondClient;
    assert(consumed_issue(net, id, s, a));
    let j = choose|j: int| 0 <= j < a.len() && #[trigger] a[j] == Action::Deliver(id)
        && es[j].incoming == Some(net.pending[id]);
    let i = j as nat;
    let last = (a.len() - 1) as nat;
    assert(result(memory(m, c, es, last)).is_none());
    assert(result(memory(m, c, es, es.len())) == Some(v));
    assert(es[last as int].actor == c) by { reveal_with_fuel(memory, 2); }
    assert(es[j].actor == net.pending[id].to);
    assert(s[j + 1] == advance(|x, w| cell(x, w), s[j], a[j]));
    assert(s[j + 1].locals =~= s[j].locals);
    assert forall|q:Process| q!=net.pending[id].to implies #[trigger] memory(m,q,es,i+1)==memory(m,q,es,i)
        by { reveal(memory); }
    i
}

// With fresh identities a delivery of this slot obtains the packet issued
// in the prefix. No assumption on the position of its receive in a run.
proof fn reserved_slot_still_names_its_issue(
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, reserved: Set<nat>, id: nat, k: nat,
)
    requires trace(|x, w| cell(x, w), s, a), reserved.contains(id), k <= a.len(),
        forall|i: int| 0 <= i < a.len() ==> fresh_send(#[trigger] a[i], reserved),
    ensures s[k as int].pending.contains_key(id) ==> packet_at(s[k as int], id) == packet_at(s[0], id),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        reserved_slot_still_names_its_issue(s, a, reserved, id, j);
        let act = a[j as int];
        assert(fresh_send(act, reserved) && s[k as int] == advance(|x, w| cell(x, w), s[j as int], act));
        match act { Action::Send(_, _) | Action::Deliver(_) => {}, _ => {} }
    }
}

pub proof fn path_without_notice_preserves_delays<S>(
    n: Notice, pre: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires response_path(pre, result, checkpoint_end(alpha(n)), delayed_slots(), s, a, v),
        !consumed_issue(s[0], 2, s, a),
    ensures forall|i: int| 0 <= i < a.len() ==> keeps_delayed_slots(#[trigger] a[i], delayed_slots()),
{
    let up = |x, w| cell(x, w);
    assert forall|i: int| 0 <= i < a.len() implies keeps_delayed_slots(#[trigger] a[i], delayed_slots()) by {
        assert forall|id: nat| #[trigger] delayed_slots().contains(id) implies crate::scheduling::untouched_slot(a[i], id) by {
            if id == 2 {
                reserved_slot_still_names_its_issue(s, a, delayed_slots(), 2, i as nat);
                if a[i] == Action::<Wire>::Deliver(2) {
                    assert(enabled(s[i], a[i]));
                    assert(observations(s, a)[i].incoming == Some(s[0].pending[2]));
                    assert(consumed_issue(s[0], 2, s, a));
                }
                assert(fresh_send(a[i], delayed_slots()));
            } else {
                assert(absent_or_dead(s[0], id));
                stale_slot_cannot_be_delivered(up, s, a, delayed_slots(), id, i as nat);
            }
        }
    }
}

// Start at the actual alpha checkpoint with all three packets still in flight.
// A completion may take the notice anywhere, or may precede its delivery.
// This implication uses no hypothesis interpreting T or simulating the receipt.
pub proof fn completion_or_indispensable_issue<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        can_respond(resume_at(m, checkpoint_observations(alpha(n))), result, checkpoint_end(alpha(n)), delayed_slots()),
    ensures ({
        let net = checkpoint_end(alpha(n)); let pre = resume_at(m, checkpoint_observations(alpha(n)));
        packet_at(net, 2) == Some(packet_for(alpha(n), 2)) && notice_to(net.pending[2], at(Replica::R2))
            && net.pending[2].input == Wire::WeakConfirm(n)
            && ((exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v))
                || receipt_prerequisite(pre, result, net, delayed_slots(), 2))
    }),
{
    hide(accepted); hide(memory);
    let net = checkpoint_end(alpha(n)); let pre = resume_at(m, checkpoint_observations(alpha(n)));
    if !receipt_prerequisite(pre, result, net, delayed_slots(), 2) {
        let (s, a, v) = choose|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
            #[trigger] response_path(pre, result, net, delayed_slots(), s, a, v) && !consumed_issue(net, 2, s, a);
        path_without_notice_preserves_delays(n, pre, result, s, a, v);
        held_path_is_an_ordinary_opportunity(n, pre, result, s, a, v);
        let ordinary = after_receipt(n); let t = replay(|x, w| cell(x, w), ordinary, a);
        assert(response_path(pre, result, ordinary, delayed_slots(), t, a, v));
        service_before_receipt_yields_actual_pair(n, m, first, result);
    }
}

// Fairness is used once, on a run of the real alpha protocol with no
// scheduling restriction on the notice. The prerequisite arm quantifies
// over all accepted completed finite paths, not just that fair run.
pub proof fn fair_alpha_or_weak_prerequisite<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        admissible_service(checkpoint_end(alpha(n)), resume_at(m, checkpoint_observations(alpha(n))), result, e),
        delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| sr2_result(resume_at(m, checkpoint_observations(alpha(n))), result, observations(s, a)).is_some()),
    ensures ({
        let net = checkpoint_end(alpha(n)); let pre = resume_at(m, checkpoint_observations(alpha(n)));
        packet_at(net, 2) == Some(packet_for(alpha(n), 2)) && notice_to(net.pending[2], at(Replica::R2))
            && net.pending[2].input == Wire::WeakConfirm(n)
            && ((exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v))
                || receipt_prerequisite(pre, result, net, delayed_slots(), 2))
    }),
{
    hide(accepted); hide(trace); hide(memory); hide(eventually_responds); hide(admissible_service);
    hide(second_invocation); hide(delivery_fair); hide(process_fair); hide(sr2_result); hide(incompatible_completions);
    hide(receipt_prerequisite); hide(completed_quorum_sample);
    let net = checkpoint_end(alpha(n)); let pre = resume_at(m, checkpoint_observations(alpha(n)));
    assert(after_crash(net));
    let (k, v) = finite_fair_service(net, pre, result, e, runnable);
    let s = states_through(e, k); let a = actions_before(e, k);
    assert(response_path(pre, result, net, delayed_slots(), s, a, v));
    completion_or_indispensable_issue(n, m, first, result);
}

}
