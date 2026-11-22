use vstd::prelude::*;
use crate::Replica;
use crate::attribution::*;
use crate::checkpoint::*;
use crate::confirmation::transport_event;
use crate::delivery::*;
use crate::first_read::*;
use crate::protocol::*;
use crate::service::*;
use crate::sr2::*;
use crate::survivors::*;
use crate::unsent::*;

verus! {

pub open spec fn copy_value(r: Replica) -> int { if r == Replica::R1 { 2 } else { 5 } }

pub open spec fn source_guard(e: ProcessStep<int, Wire>, ordinary_output: bool) -> bool {
    if e.actor != at(Replica::R3) { true } else {
        let incoming = e.incoming;
        (incoming.is_some() && incoming.unwrap().path == Path::Weak && incoming.unwrap().input is Copy
            ==> applied_copy(e, Replica::R1) || applied_copy(e, Replica::R2))
        && (incoming.is_some() && incoming.unwrap().input is Request ==> first_request_at_issuer(e))
        && (match e.action {
            Action::Send(_, p) if (between_sites(p, Replica::R1) || between_sites(p, Replica::R2))
                => notice_to(p, p.to) || (ordinary_output && p.path == Path::Strong && p.input == Wire::Peer(0)),
            _ => true,
        })
    }
}

pub open spec fn grant(s: Reader, n: Notice) -> Reader {
    Reader { prior: Control { learned: Some(n), ..s.prior }, ..s }
}

// A pulse listener arms a replication latch on the envelope of *any* R3
// arrival at R2. The independent-output switch changes what R3 may emit
// independently of replication. It adds no step to either of the actual constructed runs.
pub open spec fn publisher(need: Notice, select: Select, pulse: bool, ordinary_output: bool) -> LocalProtocol<Reader, int, Wire> {
    let base = read_protocol(set![Replica::R2], need, select);
    LocalProtocol {
        accept: |s, e| (base.accept)(s, e) && source_guard(e, ordinary_output),
        update: |s, e| {
            let next = (base.update)(s, e);
            if pulse && e.actor == at(Replica::R2) && e.incoming.is_some() && e.incoming.unwrap().from == at(Replica::R3) {
                grant(next, Notice::Replication)
            } else { next }
        }, ..base
    }
}

pub proof fn only_background_writer_certifies_the_opaque_arrival(r: Replica, n: Notice, sel: Select, pulse: bool)
    requires r == Replica::R1 || r == Replica::R2,
    ensures source_discipline(publisher(n, sel, pulse, false), r, |s: Reader| s.prior.weak_copy == Some(copy_value(r))),
        arrival_certifies_copy(publisher(n, sel, pulse, false), r),
{
    let m = publisher(n, sel, pulse, false);
    let copy = |s: Reader| s.prior.weak_copy == Some(copy_value(r));
    assert(source_discipline(m, r, copy));
    attestation_from_local_sender(m, r, copy);
}

// An independently enabled envelope at the same endpoints destroys the
// sender inference. This checks one enabled send, not a required round.
pub proof fn ordinary_offer_defeats_sender_inference(r: Replica, sel: Select)
    requires r == Replica::R1 || r == Replica::R2,
    ensures !arrival_certifies_copy(publisher(Notice::Replication, sel, true, true), r),
{
    let m = publisher(Notice::Replication, sel, true, true);
    let n = after_local_rmws();
    let x = send(9, Path::Strong, at(Replica::R3), at(r), Wire::Peer(0));
    let a = seq![x];
    let t = seq![n, advance(|v, w| cell(v, w), n, x)];
    let es = observations(t, a);
    assert forall|i: int| 0 <= i<a.len() implies {
        let e = #[trigger] a[i]; enabled(t[i], e) && t[i + 1] == advance(|v, w| cell(v, w), t[i], e)
    } by { assert(i == 0); }
    assert forall|i: int| 0 <= i<es.len() implies {
        let e = #[trigger] es[i]; (m.accept)(memory(m, e.actor, es, i as nat), e)
    } by { assert(i == 0); reveal(memory); }
    assert(offers_arrival(es[0], r) && before_request(es, 0) && !seen_copy(es, 0, r));
    if arrival_certifies_copy(m, r) {
        let fact = |e| applied_copy(e, r);
        let carrier = |e| offers_arrival(e, r);
        assert(attests(|v, w| cell(v, w), m, at(Replica::R3), fact, carrier));
        assert(trace(|v, w| cell(v, w), t, a) && accepted(m, es));
        assert(es[0].actor == at(Replica::R3) && carrier(es[0]));
        assert(observed_before(es, 0, fact));
    }
}

pub open spec fn represents_intake(p: Process, x: Intake, y: Reader) -> bool {
    y == empty_exchange(x.control) && x.samples.dom() == x.control.replies_from
        && (x.samples.dom().len()>0 ==> x.control.reply.is_some())
        && (x.control.finished ==> x.samples.dom().len() >= 2)
        && forall|r: Replica| #[trigger] x.samples.contains_key(r) ==> Some(x.samples[r]) == x.control.reply
}

pub proof fn gated_reader_implements_first_interface(n: Notice, sel: Select, ordinary: bool)
    ensures direct_first_service(publisher(n, sel, false, ordinary), |s: Reader| s.prior.reply.unwrap(), |p, x, y| represents_intake(p, x, y)),
{
    let m = publisher(n, sel, false, ordinary);
    let c = Process::FirstClient;
    assert forall|x: Intake, y: Reader, e: ProcessStep<int, Wire>| transport_event(e) && first_service(e)
        && #[trigger] represents_intake(e.actor, x, y) && #[trigger] permits_step(x.control, e)
        implies (m.accept)(y, e) && represents_intake(e.actor, collect(x, e), (m.update)(y, e)) by {
        let net = choose|n: Network<int, Wire>| enabled(n, e.action) && #[trigger] process_step(n, e.action) == e;
        let next = collect(x, e);
        let incoming = e.incoming;
        assert(next.samples.dom() =~= next.control.replies_from);
        if incoming.is_some() && first_reply(incoming.unwrap()) {
            assert(e.actor == c);
            assert(next.samples.dom() == x.samples.dom().insert(incoming.unwrap().from->At_0));
            assert forall|r: Replica| #[trigger] next.samples.contains_key(r) implies Some(next.samples[r]) == next.control.reply by {
                if r != incoming.unwrap().from->At_0 { assert(x.samples.contains_key(r)); assert(x.control.reply.is_some()); }
            }
        }
    }
    assert forall|x: Intake, y: Reader| #[trigger] represents_intake(c, x, y) && (m.done)(y)
        implies exists|r: Replica| #[trigger] x.samples.contains_key(r) && x.samples[r] == y.prior.reply.unwrap() by {
        assert(!x.samples.dom().is_empty()); let r = x.samples.dom().choose(); assert(x.samples.contains_key(r));
    }
}

// The diagnostic preserves the actual envelope and admission of the real
// status delivery. Only installation of the G permission has been removed.
pub proof fn g_gate_loses_service_when_status_is_erased(sel: Select)
    ensures ({
        let b = alpha(Notice::G);
        let r = Replica::R2;
        let m = reader(b, set![r], sel);
        let net = checkpoint_end(b);
        let result = |s: Reader| s.returned;
        let background = OrdinaryReceipt{accept: |s: Reader, a|true, update: |s: Reader, a|s};
        pre_sr1_g(b, weak_assignment(b, true).ops) && can_respond(m, result, net, delayed_slots())
            && !can_respond(without_status(m, r, background), result, net, delayed_slots())
    }),
{
    hide(accepted); hide(trace); hide(memory); hide(second_invocation); hide(read_update);
    let b = alpha(Notice::G);
    let r = Replica::R2;
    let m = reader(b, set![r], sel);
    let net = checkpoint_end(b);
    let background = OrdinaryReceipt{accept: |s: Reader, a|true, update: |s: Reader, a|s};
    let dst = without_status(m, r, background);
    let result = |s: Reader| s.returned;
    let c = chain_for(r, Notice::G);
    let never = |p: Packet<Wire>| false;
    already_g_receipt_is_indispensable_to_gated_read(sel);
    copies_and_knowledge_at_checkpoint(b, weak_assignment(b, true).ops);
    assert forall|s: Reader, e: ProcessStep<int, Wire>| transport_event(e)
        implies #[trigger] follows_reply_chain(dst, c, r, never, s, e) by {
        let n = choose|n: Network<int, Wire>| enabled(n, e.action) && #[trigger] process_step(n, e.action) == e;
        reveal(read_update);
        match e.action { Action::Deliver(_) | Action::Send(_, _) => {}, _ => {} }
    }
    if can_respond(dst, result, net, delayed_slots()) {
        let (t, a, v) = choose|t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
            #[trigger] response_path(dst, result, net, delayed_slots(), t, a, v);
        no_response_before_permission(|x, w| cell(x, w), dst, c, r, never, t, a, a.len());
    }
}

pub open spec fn pulse_admission() -> OrdinaryReceipt<Reader> {
    OrdinaryReceipt { accept: |s: Reader, a|true, update: |s: Reader, a|grant(s, Notice::Replication) }
}

proof fn pulse_at_checkpoint(sel: Select, ordinary: bool)
    ensures ({
        let n = Notice::Replication;
        let b = alpha(n);
        let m = publisher(n, sel, true, ordinary);
        let es = checkpoint_observations(b);
        accepted(m, es) && resume_at(m, es).initial == reader(b, set![Replica::R2], sel).initial
    }),
{
    let n = Notice::Replication;
    let b = alpha(n);
    let gates = set![Replica::R2];
    let es = checkpoint_observations(b);
    let base = read_protocol(gates, n, sel);
    let m = publisher(n, sel, true, ordinary);
    fresh_reader_resumes_actual_sr1_state(b, gates, sel);
    assert forall|i: int, x: Reader| 0 <= i<es.len() implies #[trigger] same_callbacks(base, m, x, es[i]) by { prefix_index(i); }
    assert forall|i: int| 0 <= i<es.len() implies { let e = #[trigger] es[i]; (m.accept)(memory(m, e.actor, es, i as nat), e) } by {
        let e = es[i]; identical_callbacks_on_log(base, m, es, e.actor, i as nat);
        assert((base.accept)(memory(base, e.actor, es, i as nat), e));
        assert(same_callbacks(base, m, memory(base, e.actor, es, i as nat), e));
    }
    assert(resume_at(m, es).initial =~= resume_at(base, es).initial) by {
        assert forall|p: Process| #[trigger] (resume_at(m, es).initial)(p) == (resume_at(base, es).initial)(p)
            by { identical_callbacks_on_log(base, m, es, p, es.len()); }
    }
}

proof fn pulse_path(sel: Select, ordinary: bool, masked: bool, t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int)
    requires trace(|x, w| cell(x, w), t, a), t[0] == checkpoint_end(alpha(Notice::Replication)),
    ensures ({
        let n = Notice::Replication;
        let b = alpha(n);
        let r = Replica::R2;
        let net = t[0];
        let result = |x: Reader| x.returned;
        let base = reader(b, set![r], sel);
        let pre = resume_at(publisher(n, sel, true, ordinary), checkpoint_observations(b));
        let m = if masked { without_status(pre, r, pulse_admission()) } else { pre };
        response_path(base, result, net, delayed_slots(), t, a, v) == response_path(m, result, net, delayed_slots(), t, a, v)
    }),
{
    let r = Replica::R2;
    let n = Notice::Replication;
    let b = alpha(n);
    let base = reader(b, set![r], sel);
    let pre = resume_at(publisher(n, sel, true, ordinary), checkpoint_observations(b));
    let m = if masked { without_status(pre, r, pulse_admission()) } else { pre };
    pulse_at_checkpoint(sel, ordinary);
    postcrash_schedule_has_only_live_actors(|x, w| cell(x, w), t, a, a.len());
    assert forall|i: int, x: Reader| 0 <= i<a.len() implies #[trigger] same_callbacks(base, m, x, observations(t, a)[i]) by {
        let e = observations(t, a)[i]; only_issued_arrival_from_r3(n, t, a, i as nat);
        assert(survivor_actor(process_step(t[i], a[i]).actor));
        if receiving_status(e, r) { assert(e.incoming == Some(packet_for(b, 2)) && a[i] == Action::<Wire>::Deliver(2)); }
    }
    response_uses_local_callbacks(base, m, |x: Reader|x.returned, t[0], delayed_slots(), t, a, v);
}

pub proof fn opaque_pulse_is_indispensable(sel: Select, ordinary: bool, masked: bool)
    ensures ({
        let n = Notice::Replication;
        let b = alpha(n);
        let r = Replica::R2;
        let net = checkpoint_end(b);
        let pre = resume_at(publisher(n, sel, true, ordinary), checkpoint_observations(b));
        let m = if masked { without_status(pre, r, pulse_admission()) } else { pre };
        receipt_prerequisite(m, |x: Reader| x.returned, net, delayed_slots(), 2)
    }),
{
    hide(memory); hide(accepted);
    let n = Notice::Replication;
    let b = alpha(n);
    let r = Replica::R2;
    let net = checkpoint_end(b);
    let result = |x: Reader| x.returned;
    let base = reader(b, set![r], sel);
    let pre = resume_at(publisher(n, sel, true, ordinary), checkpoint_observations(b));
    let m = if masked { without_status(pre, r, pulse_admission()) } else { pre };
    notified_gate_returns(n, sel);
    let a = notified_actions(b);
    let t = Seq::new(11, |i: int| notified_net(b, i as nat));
    let v = sel(report(b, Replica::R1), report(b, r));
    pulse_path(sel, ordinary, masked, t, a, v);
    assert(response_path(m, result, net, delayed_slots(), t, a, v));
    assert forall|ss: Seq<Network<int, Wire>>, aa: Seq<Action<Wire>>, x: int|
        #[trigger] response_path(m, result, net, delayed_slots(), ss, aa, x) implies consumed_issue(net, 2, ss, aa) by {
        pulse_path(sel, ordinary, masked, ss, aa, x); assert(response_path(base, result, net, delayed_slots(), ss, aa, x));
    }
}

// The two source programs exhibit exactly the same constructed exchanges.
// Only the first forces every alternative carrier from R3 to R2
// to follow replication. Both receivers can ignore the entire status body.
pub proof fn pulse_attribution_depends_on_issuer(sel: Select, ordinary: bool)
    ensures ({
        let n = Notice::Replication;
        let b = alpha(n);
        let m = publisher(n, sel, true, ordinary);
        let result = |x: Reader| x.returned;
        let pre = resume_at(m, checkpoint_observations(b));
        let net = checkpoint_end(b);
        receipt_prerequisite(without_status(pre, Replica::R2, pulse_admission()), result, net, delayed_slots(), 2)
            && (waits_for_replication(m, checkpoint_states(b), actions_to_crash(b), 1, Replica::R2, 2, result, delayed_slots()) == !ordinary)
    }),
{
    hide(accepted); hide(receipt_prerequisite); hide(arrival_certifies_copy); hide(trace); hide(outstanding_offer);
    let n = Notice::Replication;
    let b = alpha(n);
    opaque_pulse_is_indispensable(sel, ordinary, true); opaque_pulse_is_indispensable(sel, ordinary, false);
    pulse_at_checkpoint(sel, ordinary); prefix_transport_is_enabled(b); actual_status_issuance(n);
    if ordinary { ordinary_offer_defeats_sender_inference(Replica::R2, sel); }
    else { only_background_writer_certifies_the_opaque_arrival(Replica::R2, n, sel, true); }
}

}
