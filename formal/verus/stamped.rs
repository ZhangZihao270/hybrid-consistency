use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::*;
use crate::correspondence::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::service::*;
use crate::sr2::*;
use crate::survivors::*;

// This implementation adds a receipt counter to the two existing replica
// replies to C2. No client publication or inter-replica round is introduced.
verus! {

pub struct Counted {
    pub read: Reader,
    pub receipts: nat,
    pub last_header: Option<nat>,
}

pub open spec fn body(w: Wire) -> Wire {
    match w { Wire::StampedAnswer(r, _) => Wire::Answer2(r), _ => w }
}

pub open spec fn with_stamp(s: Counted, w: Wire) -> Wire {
    match body(w) { Wire::Answer2(r) => Wire::StampedAnswer(r, s.receipts), _ => w }
}

pub open spec fn counted(gates: Set<Replica>, n: Notice, select: Select) -> LocalProtocol<Counted, int, Wire> {
    let bare = read_protocol(gates, n, select);
    LocalProtocol {
        initial: |p| Counted { read: (bare.initial)(p), receipts: 0, last_header: None },
        accept: |s: Counted, e: ProcessStep<int, Wire>| (bare.accept)(s.read, local_event(|w| body(w), e))
            && e.action == map_action(|w| with_stamp(s, w), e.action),
        update: |s: Counted, e: ProcessStep<int, Wire>| Counted {
            read: (bare.update)(s.read, local_event(|w| body(w), e)),
            receipts: if e.incoming.is_some() { s.receipts + 1 } else { s.receipts },
            last_header: match e.incoming {
                Some(p) if p.input is StampedAnswer => Some(p.input->StampedAnswer_1),
                _ => s.last_header,
            },
        },
        done: |s: Counted| (bare.done)(s.read),
    }
}

// All status-independent read state is observed, including the selected
// return value. The logger really receives and stores the physical header.
pub open spec fn same_read(p: Process, s: Counted, t: Counted) -> bool {
    same_except_status(s.read, t.read)
}

pub proof fn counted_handlers_correspond(n: Notice, select: Select)
    ensures handler_correspondence(counted(Set::empty(), n, select), counted(Set::empty(), n, select),
            |w| body(w), |s, w| with_stamp(s, w), |p, s, t| same_read(p, s, t)),
        forall|p: Process, s: Counted, t: Counted| #[trigger] same_read(p, s, t) ==> s.read.returned == t.read.returned,
{
    let m = counted(Set::empty(), n, select);
    let f = |w| body(w);
    assert forall|s: Counted, t: Counted, e: ProcessStep<int, Wire>, h: ProcessStep<int, Wire>|
        #[trigger] same_read(e.actor, s, t) && #[trigger] (m.accept)(s, e)
        && h.action == map_action(|w| with_stamp(t, w), e.action) && local_event(f, e) == #[trigger] local_event(f, h)
        implies (m.accept)(t, h) && same_read(e.actor, (m.update)(s, e), (m.update)(t, h)) by {
        assert(h.action == map_action(|w| with_stamp(t, w), h.action));
    }
}

// Check the physical no-advance and direct no-await interpretation on the
// same counter implementation. Ordinary messages may still update the log.
pub proof fn counted_ordinary_steps_preserve_weak_work(
    n: Notice, sel: Select, local: Counted, net: Network<int, Wire>, a: Action<Wire>,
)
    requires enabled(net, a), ordinary_step(net, a),
    ensures ({
        let m = counted(Set::empty(), n, sel); let e = process_step(net, a);
        let erased = Counted { read: erase_weak(local.read), ..local };
        let next = (m.update)(local, e); let post = advance(|x, w| cell(x, w), net, a);
        (m.accept)(local, e) == (m.accept)(erased, e)
            && (m.update)(erased, e) == (Counted { read: erase_weak(next.read), ..next })
            && next.read.prior.weak_copy == local.read.prior.weak_copy && next.read.prior.learned == local.read.prior.learned
            && post.locals == net.locals && forall|id: nat| #[trigger] weak_slot(post, id) == weak_slot(net, id)
    }),
{
    ungated_read_preserves_weak_work(n, sel, local.read, net, a);
    match a { Action::Deliver(_) | Action::Send(_, _) => {}, _ => {} }
}

pub open spec fn plain(m: LocalProtocol<Reader, int, Wire>) -> LocalProtocol<Reader, int, Wire> {
    LocalProtocol { accept: |s, e| local_event(|w| body(w), e) == e && (m.accept)(s, e), ..m }
}

proof fn counted_prefix_memory(b: Fork, select: Select, p: Process, k: nat)
    requires k <= checkpoint_observations(b).len(),
    ensures ({
        let es = checkpoint_observations(b); let m = counted(Set::empty(), b.notice, select);
        memory(m, p, es, k).read == memory(read_protocol(Set::empty(), b.notice, select), p, es, k)
    }),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        counted_prefix_memory(b, select, p, j);
        let e = checkpoint_observations(b)[j as int];
        assert(local_event(|w| body(w), e) == e) by { prefix_index(j as int); }
    }
}

proof fn counted_first_round(b: Fork, select: Select)
    ensures ({
        let m = counted(Set::empty(), b.notice, select); let obs = checkpoint_observations(b);
        accepted(m, obs) && completed_quorum_sample(m, |s: Counted| s.read.prior.reply.unwrap(), b)
            && forall|p: Process| (#[trigger] (resume_at(m, obs).initial)(p)).read == reader_at(b, p)
    }),
{
    hide(memory);
    let m = counted(Set::empty(), b.notice, select);
    let base = read_protocol(Set::empty(), b.notice, select); let es = checkpoint_observations(b);
    fresh_reader_resumes_actual_sr1_state(b, Set::empty(), select);
    combined_reader_supplies_sr1_sample(b, Set::empty(), select);
    assert forall|i: int| 0 <= i < es.len() implies {
        let e = #[trigger] es[i];
        (m.accept)(memory(m, e.actor, es, i as nat), e)
    } by {
        let e = es[i];
        assert((base.accept)(memory(base, e.actor, es, i as nat), e));
        counted_prefix_memory(b, select, e.actor, i as nat);
        assert(local_event(|w| body(w), e) == e && e.action == map_action(|w| with_stamp(memory(m, e.actor, es, i as nat), w), e.action))
            by { prefix_index(i); }
    }
    assert forall|k: nat| k <= es.len() implies (#[trigger] first_client_at(m, b, k)).read == first_client_at(base, b, k) by {
        counted_prefix_memory(b, select, Process::FirstClient, k);
    }
    assert forall|p: Process| (#[trigger] (resume_at(m, es).initial)(p)).read == reader_at(b, p) by {
        counted_prefix_memory(b, select, p, es.len());
        assert(resume_at(base, es) == reader(b, Set::empty(), select));
        assert((resume_at(base, es).initial)(p) == reader_at(b, p));
    }
}

spec fn records_read(p: Process, s: Reader, t: Counted) -> bool { s == t.read }

proof fn stamp_plain_reference(n: Notice, select: Select)
    ensures handler_correspondence(plain(read_protocol(Set::empty(), n, select)), counted(Set::empty(), n, select),
        |w| body(w), |s, w| with_stamp(s, w), |p, x, y| records_read(p, x, y)),
{
    let src = plain(read_protocol(Set::empty(), n, select)); let dst = counted(Set::empty(), n, select);
    let f = |w| body(w);
    assert forall|s: Reader, t: Counted, e: ProcessStep<int, Wire>, h: ProcessStep<int, Wire>|
        #[trigger] records_read(e.actor, s, t) && #[trigger] (src.accept)(s, e)
        && h.action == map_action(|w| with_stamp(t, w), e.action) && local_event(f, e) == #[trigger] local_event(f, h)
        implies (dst.accept)(t, h) && (src.update)(s, e) == (dst.update)(t, h).read by {
        assert(h.action == map_action(|w| with_stamp(t, w), h.action));
    }
}

// Apart from the headers, these are exactly the two sends by C2, the
// corresponding quorum replies and their deliveries, and the local return.
pub open spec fn body_action(a: Action<Wire>) -> Action<Wire> { map_action(|w| body(w), a) }

pub open spec fn quorum_exchange(a: Seq<Action<Wire>>, b: Fork) -> bool {
    a.len() == completed_actions(b).len()
        && forall|i: int| 0 <= i < a.len() ==> body_action(#[trigger] a[i]) == completed_actions(b)[i]
}

proof fn counted_quorum_header(
    b: Fork, sel: Select, local: LocalProtocol<Counted, int, Wire>, s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>,
)
    requires local.update == counted(Set::empty(), b.notice, sel).update, local.accept == counted(Set::empty(), b.notice, sel).accept,
        quorum_exchange(a, b), trace(|x, w| cell(x, w), s, a), accepted(local, observations(s, a)),
    ensures ({
        let r = at(Replica::R2);
        let ticks = (local.initial)(r).receipts + 1;
        let p = Packet { input: Wire::StampedAnswer(report(b, Replica::R2), ticks), ..answer_packet(Replica::R2, report(b, Replica::R2)) };
        let es = observations(s, a);
        a[5] == Action::Send(14, p) && es[7].incoming == Some(p)
            && memory(local, Process::SecondClient, es, es.len()).last_header == Some(ticks)
    }),
{
    let r = at(Replica::R2); let es = observations(s, a); let c = Process::SecondClient;
    assert forall|i: int| 0 <= i < 9 implies body_action(#[trigger] a[i]) == completed_actions(b)[i] by {};
    assert(body_action(a[0]) == queries()[0] && body_action(a[1]) == queries()[1]);
    assert(body_action(a[2]) == queries()[2] && body_action(a[3]) == queries()[3]);
    assert(body_action(a[4]) == reply_action(Replica::R1, report(b, Replica::R1)));
    assert(body_action(a[5]) == reply_action(Replica::R2, report(b, Replica::R2)));
    assert(body_action(a[6]) == Action::<Wire>::Deliver(13) && body_action(a[7]) == Action::<Wire>::Deliver(14)
        && body_action(a[8]) == Action::Strong(c));
    assert(a[0] == queries()[0] && a[1] == queries()[1] && a[2] == Action::<Wire>::Deliver(11) && a[3] == Action::<Wire>::Deliver(12));
    assert forall|j: int| 0 <= j < 9 implies s[j + 1] == advance(|x, w| cell(x, w), s[j], #[trigger] a[j]) by {};
    assert(es[3].actor == r && es[3].incoming == Some(query_packet(Replica::R2)));
    assert(es[2].actor == at(Replica::R1) && es[0].actor == c && es[1].actor == c && es[4].actor == at(Replica::R1));
    let sender = memory(local, r, es, 5);
    assert(sender.receipts == (local.initial)(r).receipts + 1) by { reveal_with_fuel(memory, 6); }
    assert(es[5].actor == r && (local.accept)(sender, es[5]));
    let p = Packet { input: Wire::StampedAnswer(report(b, Replica::R2), sender.receipts), ..answer_packet(Replica::R2, report(b, Replica::R2)) };
    assert(a[5] == Action::Send(14, p));
    assert(a[6] == Action::<Wire>::Deliver(13) && a[7] == Action::<Wire>::Deliver(14) && es[7].incoming == Some(p));
    assert(es[7].actor == c && es[8].incoming.is_none());
    assert(memory(local, c, es, 9).last_header == Some(sender.receipts)) by { reveal_with_fuel(memory, 3); }
}

pub open spec fn stamped_pair(
    sel: Select, rs: Seq<Network<int, Wire>>, ra: Seq<Action<Wire>>, a: Seq<Action<Wire>>, v: int,
) -> bool {
    let n = Notice::G; let fork = alpha(n); let m = counted(Set::empty(), n, sel);
    let val = |s: Counted| s.read.returned; let first = |s: Counted| s.read.prior.reply.unwrap();
    let held = replay(|x, w| cell(x, w), checkpoint_end(fork), a);
    let pre = resume_at(m, checkpoint_observations(fork)); let informed = reference_machine(m, n);
    let ref_obs = observations(rs, ra); let held_obs = observations(held, a);
    let header = (pre.initial)(at(Replica::R2)).receipts + 1;
    response_path(informed, val, after_receipt(n), delayed_slots(), rs, ra, v)
        && quorum_exchange(ra, fork) && quorum_exchange(a, fork) && ra[5] != a[5]
        && memory(informed, Process::SecondClient, ref_obs, ref_obs.len()).last_header == Some(header + 1)
        && memory(pre, Process::SecondClient, held_obs, held_obs.len()).last_header == Some(header)
        && incompatible_completions(n, m, first, val, a, v)
}

proof fn plain_g_reference(select: Select)
    ensures ({
        let n = Notice::G; let a = alpha(n); let base = read_protocol(Set::empty(), n, select);
        let src = plain(reference_machine(base, n)); let net = after_receipt(n); let acts = completed_actions(a);
        let states = replay(|x, w| cell(x, w), net, acts);
        response_path(src, |x: Reader| x.returned, net, delayed_slots(), states, acts,
            select(report(a, Replica::R1), report(a, Replica::R2)))
    }),
{
    hide(memory); hide(replay); hide(trace); hide(accepted);
    let n = Notice::G; let a = alpha(n); let gates = Set::empty();
    let base = read_protocol(gates, n, select); let reference = reference_machine(base, n);
    let src = plain(reference); let acts = completed_actions(a); let net = after_receipt(n);
    let up = |x, w| cell(x, w); let s = replay(up, net, acts); let es = observations(s, acts);
    let v = select(report(a, Replica::R1), report(a, Replica::R2));
    actual_g_reference_supports_the_held_pair(select, seq![], seq![], seq![], seq![]);
    fresh_reader_resumes_actual_sr1_state(a, gates, select);
    alpha_receipt_cut(n);
    let orig = exchange_states(a, true);
    only_initial_sr2_requests_are_sent(a, true);
    ordinary_quorum_can_return(a, gates, select);
    assert forall|i: int| 0 <= i < acts.len() implies keeps_delayed_slots(#[trigger] acts[i], delayed_slots())
        && fresh_send(acts[i], delayed_slots()) by { prefix_index(i); }
    assert(outside_delays(checkpoint_end(a), net, delayed_slots()));
    replay_sr2_without_touching_delayed_slots(up, orig, net, acts, delayed_slots());
    assert forall|i: int| 0 <= i < es.len() implies {
        let e = #[trigger] es[i];
        (src.accept)(memory(src, e.actor, es, i as nat), e)
    } by {
        let e = es[i];
        assert((reference.accept)(memory(reference, e.actor, es, i as nat), e)) by { reveal(accepted); }
        memory_from_same_local_state(src, reference, e.actor, es, i as nat);
        assert(local_event(|w| body(w), e) == e) by { prefix_index(i); }
    }
    let c = Process::SecondClient;
    memory_from_same_local_state(src, reference, c, es, es.len());
    let held = reader(a, gates, select);
    assert((src.initial)(c) == (held.initial)(c)) by { reveal_with_fuel(memory, 2); }
    assert forall|k: nat| k < es.len() implies (#[trigger] memory(src, c, es, k)).returned.is_none() by {
        memory_from_same_local_state(src, held, c, es, k);
        exchange_tracks_private_memory(a, gates, select, true, c, k);
    }
    assert((src.initial)(Process::SecondClient).returned.is_none()) by { reveal_with_fuel(memory, 2); }
    assert(s[0] == net) by { reveal(replay); }
    assert(response_path(src, |x: Reader| x.returned, net, delayed_slots(), s, acts, v)) by { reveal(accepted); }
}

// A real informed reference with the existing two request/reply pairs.
// Its replicas have to generate their own headers; deliveries read their queues.
pub proof fn counted_g_reference_and_held_pair(select: Select)
    ensures ({
        let n = Notice::G; let a = alpha(n); let b = beta(n);
        let m = counted(Set::empty(), n, select); let first = |s: Counted| s.read.prior.reply.unwrap();
        let result = |s: Counted| s.read.returned; let pre = resume_at(m, checkpoint_observations(a));
        pre_sr1_g(a, weak_assignment(a, true).ops) && pre_sr1_g(b, weak_assignment(b, true).ops)
            && can_respond(reference_machine(m, n), result, after_receipt(n), delayed_slots())
            && !enables_service(pre, result, checkpoint_end(a), 2, delayed_slots())
            && !receipt_prerequisite(pre, result, checkpoint_end(a), delayed_slots(), 2)
            && exists|rs: Seq<Network<int, Wire>>, ra: Seq<Action<Wire>>, actions: Seq<Action<Wire>>, v: int|
                #[trigger] stamped_pair(select, rs, ra, actions, v)
    }),
{
    hide(memory); hide(replay); hide(trace); hide(accepted);
    let n = Notice::G; let a = alpha(n); let b = beta(n); let gates = Set::empty();
    let base = read_protocol(gates, n, select); let m = counted(gates, n, select);
    let reference = reference_machine(base, n); let src = plain(reference); let dst = reference_machine(m, n);
    let before = resume_at(m, checkpoint_observations(a)); let result = |s: Counted| s.read.returned;
    let first = |s: Counted| s.read.prior.reply.unwrap();
    let acts = completed_actions(a); let net = after_receipt(n); let up = |x, w| cell(x, w); let s = replay(up, net, acts);
    let v = select(report(a, Replica::R1), report(a, Replica::R2)); let es = observations(s, acts);
    actual_g_reference_supports_the_held_pair(select, seq![], seq![], seq![], seq![]);
    counted_first_round(a, select); counted_first_round(b, select);
    fresh_reader_resumes_actual_sr1_state(a, gates, select);
    alpha_receipt_cut(n);
    assert forall|p: Process| (#[trigger] (dst.initial)(p)).read == (src.initial)(p) by { reveal_with_fuel(memory, 2); }
    plain_g_reference(select);
    stamp_plain_reference(n, select);
    let (rs, ra, rv) = translate_response(src, dst, |w| body(w), |s, w| with_stamp(s, w),
        |p, x, y| records_read(p, x, y), net, delayed_slots(), |x: Reader| x.returned, result, s, acts, v);
    counted_handlers_correspond(n, select);
    assert forall|p: Process| #[trigger] same_read(p, (dst.initial)(p), (before.initial)(p)) by {
        reveal_with_fuel(memory, 2);
    }
    let (ts, ta, tv) = translate_response(dst, before, |w| body(w), |s, w| with_stamp(s, w),
        |p, x, y| same_read(p, x, y), net, delayed_slots(), result, result, rs, ra, rv);
    let re = observations(rs, ra); let he = observations(ts, ta); let c = Process::SecondClient;
    assert(records_read(c, memory(src, c, es, es.len()), memory(dst, c, re, re.len())));
    assert(same_read(c, memory(dst, c, re, re.len()), memory(before, c, he, he.len())));
    assert(v == rv && rv == tv);
    pair_from_ordinary_path(n, m, first, result, ts, ta, tv);
    assert forall|i: int| 0 <= i < acts.len() implies map_action(|w| body(w), ra[i]) == #[trigger] acts[i]
        && map_action(|w| body(w), ta[i]) == acts[i] by {
        assert(local_event(|w| body(w), es[i]) == local_event(|w| body(w), re[i]));
        assert(local_event(|w| body(w), re[i]) == local_event(|w| body(w), he[i]));
        assert(map_action(|w| body(w), acts[i]) == acts[i]) by { prefix_index(i); }
    }
    counted_quorum_header(a, select, dst, rs, ra);
    counted_quorum_header(a, select, before, ts, ta);
    assert((dst.initial)(at(Replica::R2)).receipts == (before.initial)(at(Replica::R2)).receipts + 1) by { reveal_with_fuel(memory, 2); }
    existing_notice_is_the_only_extra_opportunity(n, before, result, ts, ta, tv);
    let held = replay(up, checkpoint_end(a), ta);
    assert(delayed_slots().contains(2nat));
    assert forall|i: int| 0 <= i < ta.len() implies #[trigger] ta[i] != Action::<Wire>::Deliver(2)
        by { assert(keeps_delayed_slots(ta[i], delayed_slots())); }
    assert(!consumed_issue(checkpoint_end(a), 2, held, ta));
    assert(stamped_pair(select, rs, ra, ta, v));
}

pub proof fn counted_reply_fails_exact_optional_at(select: Select, covers: spec_fn(Counted, Counted) -> bool)
    ensures ({
        let n = Notice::G; let a = alpha(n); let m = counted(Set::empty(), n, select);
        let s = (resume_at(m, checkpoint_observations(a)).initial)(at(Replica::R2));
        !optional_at(m, Replica::R2, s, receipt_event(n), covers)
    }),
{
    hide(memory);
    let n = Notice::G; let a = alpha(n); let r = Replica::R2; let m = counted(Set::empty(), n, select);
    let s = (resume_at(m, checkpoint_observations(a)).initial)(at(r));
    counted_first_round(a, select); alpha_receipt_cut(n);
    let ack = receipt_event(n); let informed = (m.update)(s, ack);
    let query_net = exchange_net(a, 3); let query = process_step(query_net, Action::Deliver(12));
    let x = (m.update)(informed, query); let y = (m.update)(s, query);
    let ans = map_action(|w| with_stamp(x, w), reply_action(r, report(a, r)));
    let reply_net = exchange_net(a, 4); let reply = process_step(reply_net, ans);
    assert(transport_event(query) && transport_event(reply)) by {
        assert(enabled(query_net, query.action) && process_step(query_net, query.action) == query);
        assert(enabled(reply_net, reply.action) && process_step(reply_net, reply.action) == reply);
    }
    assert(x.receipts == y.receipts + 1 && (m.accept)(x, reply) && !(m.accept)(y, reply));
    if optional_at(m, r, s, ack, covers) {
        assert(covers(informed, s));
        assert((m.accept)(informed, query) && covers(x, y));
        assert((m.accept)(y, reply));
    }
}

}
