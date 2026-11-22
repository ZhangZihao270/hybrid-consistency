use vstd::prelude::*;
use crate::{Op, Replica};
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::service::*;
use crate::survivors::*;
use crate::transparency::{StrongEffect, permitted};

verus! {

// The ordinary callback can record a delivery, its endpoints and the actual
// local cell. The transport still delivers the original authenticated packet.
pub struct Arrival { pub from: Process, pub to: Process, pub local: Option<int> }

#[verifier::reject_recursive_types(S)]
pub struct OrdinaryReceipt<S> {
    pub accept: spec_fn(S, Arrival) -> bool,
    pub update: spec_fn(S, Arrival) -> S,
}

pub open spec fn receiving_status(e: ProcessStep<int, Wire>, owner: Replica) -> bool {
    e.action is Deliver && e.actor == at(owner) && e.incoming.is_some()
        && notice_to(e.incoming.unwrap(), at(owner))
}

pub open spec fn envelope(e: ProcessStep<int, Wire>) -> Arrival {
    Arrival { from: e.incoming.unwrap().from, to: e.actor, local: e.own_local }
}

// Diagnostic change of the receiving program. Prefix and queue are real.
// The adapter must supply the ordinary service that the packet carries.
pub open spec fn without_status<S>(m: LocalProtocol<S, int, Wire>, owner: Replica, ordinary: OrdinaryReceipt<S>)
    -> LocalProtocol<S, int, Wire>
{
    LocalProtocol {
        accept: |s, e| if receiving_status(e, owner) { (ordinary.accept)(s, envelope(e)) } else { (m.accept)(s, e) },
        update: |s, e| if receiving_status(e, owner) { (ordinary.update)(s, envelope(e)) } else { (m.update)(s, e) },
        ..m
    }
}

proof fn crashed_sender_backlog<L, I>(
    up: spec_fn(L, I) -> L, t: Seq<Network<L, I>>, a: Seq<Action<I>>, k: nat, id: nat,
)
    requires trace(up, t, a), t[0].r3_crashed, k <= a.len(),
    ensures t[k as int].r3_crashed,
        t[k as int].pending.contains_key(id) && t[k as int].pending[id].from == at(Replica::R3)
            ==> packet_at(t[k as int], id) == packet_at(t[0], id),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat; crashed_sender_backlog(up, t, a, j, id);
        assert(enabled(t[j as int], a[j as int]) && t[k as int] == advance(up, t[j as int], a[j as int]));
        match a[j as int] { Action::Send(_, _) | Action::Deliver(_) => {}, _ => {} }
    }
}

pub proof fn only_issued_arrival_from_r3(n: Notice, t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat)
    requires trace(|x, w| cell(x, w), t, a), t[0] == checkpoint_end(alpha(n)), k<a.len(),
    ensures ({
        let e = observations(t, a)[k as int];
        e.incoming.is_some() && e.incoming.unwrap().from == at(Replica::R3) && e.actor == at(Replica::R2)
            ==> a[k as int] == Action::Deliver(2) && e.incoming == Some(packet_for(alpha(n), 2))
    }),
{
    if let Action::Deliver(id) = a[k as int] {
        crashed_sender_backlog(|x, w| cell(x, w), t, a, k, id);
        assert(enabled(t[k as int], a[k as int]));
    }
}

proof fn unchanged_before_status<S>(
    m: LocalProtocol<S, int, Wire>, owner: Replica, o: OrdinaryReceipt<S>,
    es: Seq<ProcessStep<int, Wire>>, p: Process, k: nat,
)
    requires k <= es.len(), forall|j: int| 0 <= j < k ==> !receiving_status(#[trigger] es[j], owner),
    ensures memory(m, p, es, k) == memory(without_status(m, owner, o), p, es, k),
    decreases k,
{
    if k > 0 { unchanged_before_status(m, owner, o, es, p, (k - 1) as nat); }
}

// Removing the evidence-specific callback cannot create a way to answer
// before receipt: until the intervention the two programs are identical.
pub proof fn stripped_service_still_needs_the_issue<S>(
    n: Notice, pre: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, o: OrdinaryReceipt<S>,
)
    requires receipt_prerequisite(pre, result, checkpoint_end(alpha(n)), delayed_slots(), 2),
    ensures ({
        let net = checkpoint_end(alpha(n));
        let masked = without_status(pre, Replica::R2, o);
        !can_respond(masked, result, net, delayed_slots()) || receipt_prerequisite(masked, result, net, delayed_slots(), 2)
    }),
{
    let net = checkpoint_end(alpha(n));
    let reserved = delayed_slots();
    let r = Replica::R2;
    let masked = without_status(pre, r, o);
    assert forall|t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
        #[trigger] response_path(masked, result, net, reserved, t, a, v) implies consumed_issue(net, 2, t, a) by {
        if !consumed_issue(net, 2, t, a) {
            path_without_notice_preserves_delays(n, masked, result, t, a, v);
            let es = observations(t, a);
            assert(reserved.contains(2nat));
            assert forall|i: int| 0 <= i < es.len() implies !receiving_status(#[trigger] es[i], r)
                by { only_issued_arrival_from_r3(n, t, a, i as nat); assert(keeps_delayed_slots(a[i], reserved)); }
            assert forall|i: int| 0 <= i < es.len() implies {
                let e = #[trigger] es[i]; (pre.accept)(memory(pre, e.actor, es, i as nat), e)
            } by {
                let e = es[i]; unchanged_before_status(pre, r, o, es, e.actor, i as nat);
                assert((masked.accept)(memory(masked, e.actor, es, i as nat), e));
            }
            let c = Process::SecondClient;
            assert forall|k: nat| k < es.len() implies result(#[trigger] memory(pre, c, es, k)).is_none() by {
                unchanged_before_status(pre, r, o, es, c, k); assert(result(memory(masked, c, es, k)).is_none());
            }
            unchanged_before_status(pre, r, o, es, c, es.len());
            assert(response_path(pre, result, net, reserved, t, a, v));
        }
    }
}

// Source authentication uses an actual weak write copy, including sender,
// receiver, path and data. The two RMWs have different values in this workload.
pub open spec fn applied_copy(e: ProcessStep<int, Wire>, owner: Replica) -> bool {
    (owner == Replica::R1 || owner == Replica::R2) && e.actor == at(Replica::R3)
        && e.incoming == Some(Packet { path: Path::Weak, from: at(owner), to: at(Replica::R3),
            input: Wire::Copy(if owner == Replica::R1 { 2 } else { 5 }) })
}

pub open spec fn between_sites(p: Packet<Wire>, owner: Replica) -> bool {
    p.from == at(Replica::R3) && p.to == at(owner)
}

// Coarse carrier identity: all slots, paths, encodings and payloads are
// eligible. A background ordinary message to the same destination counts.
pub open spec fn offers_arrival(e: ProcessStep<int, Wire>, owner: Replica) -> bool {
    match e.action { Action::Send(_, p) => e.actor == at(Replica::R3) && between_sites(p, owner), _ => false }
}

pub open spec fn first_request_at_issuer(e: ProcessStep<int, Wire>) -> bool {
    e.actor == at(Replica::R3) && e.incoming == Some(Packet { path: Path::Strong, from: Process::FirstClient,
        to: at(Replica::R3), input: Wire::Request })
}

// A local producer can attest any event class. The producer's bit starts
// clear and can rise only on a fact-establishing event. Every eligible
// outbound carrier needs that bit, even if its payload is opaque.
pub open spec fn producer_rule<S, L, I>(
    m: LocalProtocol<S, L, I>, issuer: Process, bit: spec_fn(S) -> bool,
    fact: spec_fn(ProcessStep<L, I>) -> bool, carrier: spec_fn(ProcessStep<L, I>) -> bool,
) -> bool {
    !bit((m.initial)(issuer))
        && forall|s: S, e: ProcessStep<L, I>| crate::confirmation::transport_event(e)
            && e.actor == issuer && #[trigger] (m.accept)(s, e) ==> {
            (!bit(s) && bit((m.update)(s, e)) ==> fact(e)) && (carrier(e) ==> bit(s))
        }
}

pub open spec fn observed_before<L, I>(es: Seq<ProcessStep<L, I>>, k: nat, fact: spec_fn(ProcessStep<L, I>) -> bool) -> bool {
    exists|j: int| 0 <= j<k && fact(#[trigger] es[j])
}

pub open spec fn attests<S, L, I>(
    up: spec_fn(L, I) -> L, m: LocalProtocol<S, L, I>, issuer: Process,
    fact: spec_fn(ProcessStep<L, I>) -> bool, carrier: spec_fn(ProcessStep<L, I>) -> bool,
) -> bool {
    forall|t: Seq<Network<L, I>>, a: Seq<Action<I>>, k: nat| #![trigger carrier(observations(t, a)[k as int])] {
        let es = observations(t, a);
        trace(up, t, a) && accepted(m, es) && k<a.len() && es[k as int].actor == issuer
            && carrier(es[k as int]) ==> observed_before(es, k, fact)
    }
}

proof fn source_memory_has_evidence<S, L, I>(
    m: LocalProtocol<S, L, I>, issuer: Process, bit: spec_fn(S) -> bool,
    fact: spec_fn(ProcessStep<L, I>) -> bool, carrier: spec_fn(ProcessStep<L, I>) -> bool, es: Seq<ProcessStep<L, I>>, k: nat,
)
    requires producer_rule(m, issuer, bit, fact, carrier), k <= es.len(), accepted(m, es),
        forall|j: int| 0 <= j<es.len() ==> crate::confirmation::transport_event(#[trigger] es[j]),
    ensures bit(memory(m, issuer, es, k)) ==> observed_before(es, k, fact),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        source_memory_has_evidence(m, issuer, bit, fact, carrier, es, j);
        let e = es[j as int];
        assert((m.accept)(memory(m, e.actor, es, j), e));
        if observed_before(es, j, fact) {
            let i = choose|i: int| 0 <= i<j && fact(#[trigger] es[i]);
            assert(observed_before(es, k, fact));
        }
    }
}

pub proof fn producer_rule_attests_prior_fact<S, L, I>(
    up: spec_fn(L, I) -> L, m: LocalProtocol<S, L, I>, issuer: Process, bit: spec_fn(S) -> bool,
    fact: spec_fn(ProcessStep<L, I>) -> bool, carrier: spec_fn(ProcessStep<L, I>) -> bool,
)
    requires producer_rule(m, issuer, bit, fact, carrier),
    ensures attests(up, m, issuer, fact, carrier),
{
    assert forall|t: Seq<Network<L, I>>, a: Seq<Action<I>>, k: nat| #![trigger carrier(observations(t, a)[k as int])] {
        let es = observations(t, a);
        trace(up, t, a) && accepted(m, es) && k<a.len() && es[k as int].actor == issuer
            && carrier(es[k as int]) ==> observed_before(es, k, fact)
    } by {
        let es = observations(t, a);
        if trace(up, t, a) && accepted(m, es) && k<a.len() && es[k as int].actor == issuer && carrier(es[k as int]) {
            assert forall|j: int| 0 <= j<es.len() implies crate::confirmation::transport_event(#[trigger] es[j]) by {
                assert(enabled(t[j], a[j]) && process_step(t[j], a[j]) == es[j]);
            }
            source_memory_has_evidence(m, issuer, bit, fact, carrier, es, k);
            let e = es[k as int];
            assert((m.accept)(memory(m, e.actor, es, k), e));
        }
    }
}

pub open spec fn source_discipline<S>(m: LocalProtocol<S, int, Wire>, owner: Replica, has_copy: spec_fn(S) -> bool) -> bool {
    producer_rule(m, at(Replica::R3), has_copy, |e| applied_copy(e, owner), |e| offers_arrival(e, owner))
}

pub open spec fn seen_copy(es: Seq<ProcessStep<int, Wire>>, k: nat, owner: Replica) -> bool {
    observed_before(es, k, |e| applied_copy(e, owner))
}

pub open spec fn before_request(es: Seq<ProcessStep<int, Wire>>, k: nat) -> bool {
    forall|j: int| 0 <= j<k ==> !first_request_at_issuer(#[trigger] es[j])
}

// The receiver need not know the send time or the client's reply set.
// This instance treats all R3-to-owner offers as the same opaque carrier.
pub open spec fn arrival_certifies_copy<S>(m: LocalProtocol<S, int, Wire>, owner: Replica) -> bool {
    attests(|x, w| cell(x, w), m, at(Replica::R3), |e| applied_copy(e, owner), |e| offers_arrival(e, owner))
}

pub proof fn attestation_from_local_sender<S>(
    m: LocalProtocol<S, int, Wire>, owner: Replica, copy: spec_fn(S) -> bool,
)
    requires source_discipline(m, owner, copy),
    ensures arrival_certifies_copy(m, owner),
{
    producer_rule_attests_prior_fact(|x, w| cell(x, w), m, at(Replica::R3), copy,
        |e| applied_copy(e, owner), |e| offers_arrival(e, owner));
}

pub open spec fn outstanding_offer(
    w: Replica, t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat, net: Network<int, Wire>, id: nat,
) -> bool {
    let es = observations(t, a);
    k < a.len() && a[k as int] == Action::Send(id, net.pending[id]) && net.pending.contains_key(id)
        && offers_arrival(es[k as int], w)
        && t.last() == net && forall|j: int| k < j < a.len() ==> crate::scheduling::untouched_slot(#[trigger] a[j], id)
}

// Stable message identities are transport bookkeeping. The cut may reserve
// only identities already allocated by the time the read starts.
pub open spec fn allocated_before_read(
    t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, reserved: Set<nat>,
) -> bool {
    forall|id: nat| #[trigger] reserved.contains(id) ==> t[0].pending.contains_key(id)
        || exists|j: int| 0 <= j<a.len() && match #[trigger] a[j] {
            Action::Send(slot, _) => slot == id, _ => false,
        }
}

// Proposed causal interpretation of AwaitWeak. It combines a source proof
// about the ordinary carrier, a particular untouched issued token, and
// a nonvacuous consumer cut at a pending read. No SR1 value, paired
// execution, selector, or desired SR2 value occurs in this criterion.
pub open spec fn waits_for_replication<S>(
    m: LocalProtocol<S, int, Wire>, t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat, owner: Replica, id: nat,
    result: spec_fn(S) -> Option<int>, reserved: Set<nat>,
) -> bool {
    let net = t.last();
    trace(|x, w| cell(x, w), t, a) && accepted(m, observations(t, a)) && arrival_certifies_copy(m, owner)
        && allocated_before_read(t, a, reserved) && reserved.contains(id) && outstanding_offer(owner, t, a, k, net, id)
        && receipt_prerequisite(resume_at(m, observations(t, a)), result, net, reserved, id)
}

pub open spec fn no_causal_await<S>(m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>) -> bool {
    forall|t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat, owner: Replica, id: nat, reserved: Set<nat>|
        #[trigger] waits_for_replication(m, t, a, k, owner, id, result, reserved)
        ==> permitted(StrongEffect::AwaitWeak(if owner == Replica::R1 { Op::W1 } else { Op::W2 }))
}

pub(crate) proof fn actual_status_issuance(n: Notice)
    ensures outstanding_offer(Replica::R2, checkpoint_states(alpha(n)), actions_to_crash(alpha(n)), 1, checkpoint_end(alpha(n)), 2),
        before_request(checkpoint_observations(alpha(n)), 1), seen_copy(checkpoint_observations(alpha(n)), 1, Replica::R2),
        allocated_before_read(checkpoint_states(alpha(n)), actions_to_crash(alpha(n)), delayed_slots()),
{
    let b = alpha(n);
    let t = checkpoint_states(b);
    let a = actions_to_crash(b);
    let es = checkpoint_observations(b);
    assert forall|id: nat| #[trigger] delayed_slots().contains(id) && !t[0].pending.contains_key(id)
        implies exists|j: int| 0 <= j<a.len() && match #[trigger] a[j] {Action::Send(slot, _) => slot == id, _ => false} by {
        let j: int = if id == 2 {1} else if id == 6 {8} else {9};
        assert(match a[j] {Action::Send(slot, _) => slot == id, _ => false});
    }
    assert(applied_copy(es[0], Replica::R2)); assert(seen_copy(es, 1, Replica::R2));
    assert forall|j: int| 1 < j < a.len() implies crate::scheduling::untouched_slot(#[trigger] a[j], 2) by { prefix_index(j); }
}

pub proof fn hot_or_causal_weak_wait<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    copy: spec_fn(S) -> bool,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        can_respond(resume_at(m, checkpoint_observations(alpha(n))), result, checkpoint_end(alpha(n)), delayed_slots()),
        source_discipline(m, Replica::R2, copy),
    ensures (exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v))
        || (waits_for_replication(m, checkpoint_states(alpha(n)), actions_to_crash(alpha(n)), 1, Replica::R2, 2, result, delayed_slots())
            && !no_causal_await(m, result)),
        receipt_prerequisite(resume_at(m, checkpoint_observations(alpha(n))), result, checkpoint_end(alpha(n)), delayed_slots(), 2)
            ==> waits_for_replication(m, checkpoint_states(alpha(n)), actions_to_crash(alpha(n)), 1, Replica::R2, 2, result, delayed_slots())
                && !no_causal_await(m, result),
{
    hide(incompatible_completions); hide(accepted); hide(receipt_prerequisite);
    hide(source_discipline); hide(can_respond); hide(completed_quorum_sample); hide(arrival_certifies_copy);
    hide(trace); hide(outstanding_offer);
    let b = alpha(n);
    let t = checkpoint_states(b);
    let a = actions_to_crash(b);
    let owner = Replica::R2;
    completion_or_indispensable_issue(n, m, first, result);
    attestation_from_local_sender(m, owner, copy);
    actual_status_issuance(n); prefix_transport_is_enabled(b);
    if receipt_prerequisite(resume_at(m, checkpoint_observations(b)), result, checkpoint_end(b), delayed_slots(), 2) {
        assert(waits_for_replication(m, t, a, 1, owner, 2, result, delayed_slots()));
    }
}

}
