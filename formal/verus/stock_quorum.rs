use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::*;
use crate::correspondence::*;
use crate::delivery::*;
use crate::progress::*;
use crate::protocol::*;
use crate::quorum_progress::*;
use crate::service::*;
use crate::sr2::*;
use crate::stock::*;
use crate::survivors::*;

verus! {

// Immutable self identity lets the proof's wire encoder name the sender.
// The actual handler still checks its own register at every reply send.
pub struct Located { pub site: Process, pub reader: Reader }

pub open spec fn local_reader() -> LocalProtocol<Located, int, Wire> {
    let m = agreement_reader(false);
    LocalProtocol {
        initial: |p| Located {site: p, reader: (m.initial)(p)},
        accept: |s: Located, e: ProcessStep<int, Wire>| s.site == e.actor && (m.accept)(s.reader, e),
        update: |s: Located, e| Located {reader: (m.update)(s.reader, e), ..s},
        done: |s: Located| (m.done)(s.reader),
    }
}

// A stock direct read can restrict its suffix to its ordinary read
// messages and local processing. The fair reference below witnesses it.
pub open spec fn read_packet(p: Packet<Wire>) -> bool {
    p == query_packet(Replica::R1) || p == query_packet(Replica::R2)
        || report_from(p, Replica::R1) || report_from(p, Replica::R2)
}

pub open spec fn read_event(e: ProcessStep<int, Wire>) -> bool {
    survivor_actor(e.actor) && match e.action {
        Action::Send(_, p) => read_packet(p),
        Action::Deliver(_) => e.incoming.is_some() && read_packet(e.incoming.unwrap()),
        Action::Strong(_) | Action::ClientInput(_, _) => true,
        _ => false,
    }
}

pub open spec fn base_reader(d: int) -> LocalProtocol<Reader, int, Wire> {
    let m = resume_at(agreement_reader(false), first_events(World::Uniform(d)));
    LocalProtocol {accept: |s, e| read_event(e) && (m.accept)(s, e), ..m}
}

pub open spec fn erase_value(w: Wire) -> Wire {
    match w { Wire::Answer2(v) => Wire::Answer2(Report {value: 0, ..v}), _ => w }
}

pub open spec fn encode_sample(value: spec_fn(Replica) -> int, s: Located, w: Wire) -> Wire {
    match (s.site, w) {
        (Process::At(r), Wire::Answer2(v)) => Wire::Answer2(Report {value: value(r), ..v}),
        _ => w,
    }
}

pub open spec fn reader_phase(p: Process, x: Reader, y: Located) -> bool {
    let t = y.reader;
    y.site == p && x.returned.is_some() == t.returned.is_some() && (survivor_actor(p) ==> {
        x.asked == t.asked && x.prior.answered_first == t.prior.answered_first
            && x.prior.sent_requests == t.prior.sent_requests && x.prior.replies_from == t.prior.replies_from
            && x.prior.finished == t.prior.finished && x.r1.is_some() == t.r1.is_some() && x.r2.is_some() == t.r2.is_some()
    })
}

pub proof fn sample_values_can_change(
    base: LocalProtocol<Reader, int, Wire>, old: spec_fn(Replica) -> int, actual: spec_fn(Replica) -> int,
)
    requires forall|x: Reader, e: ProcessStep<int, Wire>| #[trigger] (base.accept)(x, e)
        ==> read_event(e) && (agreement_reader(false).accept)(x, e),
        base.update == agreement_reader(false).update,
    ensures handler_correspondence(stock_source(base, old, actual), local_reader(), |w| erase_value(w),
        |s, w| encode_sample(actual, s, w), |p, x, y| reader_phase(p, x, y)),
{
    let src = stock_source(base, old, actual);
    let dst = local_reader();
    let f = |w| erase_value(w);
    let enc = |s, w| encode_sample(actual, s, w);
    assert forall|s: Located, p: Packet<Wire>| #[trigger] same_body(f, enc, s, p)
        by { match (p.input, s.site) { (Wire::Answer2(_), Process::At(_)) => {}, _ => {} } }
    assert forall|x: Reader, y: Located, e: ProcessStep<int, Wire>, h: ProcessStep<int, Wire>|
        transport_event(e) && transport_event(h) && #[trigger] reader_phase(e.actor, x, y) && #[trigger] (src.accept)(x, e)
            && h.action == map_action(|w| enc(y, w), e.action) && local_event(f, e) == #[trigger] local_event(f, h)
        implies (dst.accept)(y, h) && reader_phase(e.actor, (src.update)(x, e), (dst.update)(y, h)) by {
        let old_e = cell_at_actor(e, old);
        assert((base.accept)(x, old_e));
        let n = choose|n: Network<int, Wire>| enabled(n, e.action) && #[trigger] process_step(n, e.action) == e;
        let t = choose|n: Network<int, Wire>| enabled(n, h.action) && #[trigger] process_step(n, h.action) == h;
        match e.action {
            Action::Send(_, p) => { match p.input { Wire::Query2 | Wire::Answer2(_) => {}, _ => {} } },
            Action::Deliver(_) => {
                let p = e.incoming.unwrap();
                let q = h.incoming.unwrap();
                assert(map_packet(f, p) == map_packet(f, q));
                match (p.input, q.input) {
                    (Wire::Query2, Wire::Query2) | (Wire::Answer2(_), Wire::Answer2(_)) => {}, _ => {},
                }
            },
            _ => {},
        }
    }
}

proof fn located_memory(p: Process, es: Seq<ProcessStep<int, Wire>>, k: nat)
    requires k <= es.len(),
    ensures memory(local_reader(), p, es, k) == (Located {site: p, reader: memory(agreement_reader(false), p, es, k)}),
    decreases k,
{
    if k > 0 { located_memory(p, es, (k - 1) as nat); }
}

proof fn located_first_read(b: Fork)
    requires b.notice == Notice::G,
    ensures accepted(local_reader(), checkpoint_observations(b)),
        completed_quorum_sample(local_reader(), |s: Located| s.reader.prior.reply.unwrap(), b),
{
    hide(memory); hide(observations); hide(checkpoint_observations); hide(checkpoint_states); hide(during_sr1);
    hide(permits_step); hide(read_accept);
    let sel = |x: Report, y: Report| x.value;
    let base = agreement_reader(false);
    let m = local_reader();
    let c = Process::FirstClient;
    let es = checkpoint_observations(b);
    assert(es.len() == 17) by { reveal(checkpoint_observations); reveal(observations); }
    fresh_reader_resumes_actual_sr1_state(b, Set::empty(), sel);
    combined_reader_supplies_sr1_sample(b, Set::empty(), sel);
    assert(base == read_protocol(Set::empty(), b.notice, sel)) by {
        assert(base.accept =~= read_protocol(Set::empty(), b.notice, sel).accept);
    }
    assert forall|i: int| 0 <= i<es.len() implies {
        let ev = #[trigger] es[i]; (m.accept)(memory(m, ev.actor, es, i as nat), ev)
    } by { located_memory(es[i].actor, es, i as nat); assert((base.accept)(memory(base, es[i].actor, es, i as nat), es[i])); }
    assert forall|k: nat| k <= 14 implies #[trigger] first_client_at(m, b, k).reader == first_client_at(base, b, k)
        by { located_memory(c, es, k); }
    assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m, b, k)) by {
        assert(!(base.done)(first_client_at(base, b, k)));
    }
    located_memory(c, es, 13); located_memory(c, es, 14);
    assert(first_return_len(m, b) == first_return_len(base, b));
    assert(first_result(m, |s: Located| s.reader.prior.reply.unwrap(), b) == first_result(base, |s: Reader| s.prior.reply.unwrap(), b));
}

proof fn uniform_stock_service(d: int)
    ensures ({
        let w = World::Uniform(d);
        let net = first_cut(w);
        let e = service_run(w, false);
        let base = base_reader(d);
        let result = |s: Reader| s.returned;
        admissible_service(net, base, result, e) && delivery_fair(e) && process_fair(e, |n, p| live_process(n, p))
            && eventually_responds(e, |n, p| live_process(n, p), |s, a| sr2_result(base, result, observations(s, a)).is_some())
            && (forall|i: nat| stock_work(process_step((e.state)(i), #[trigger] (e.action)(i))))
            && stock_cut(net, after_receipt(Notice::G))
    }),
{
    hide(memory); hide(only_request_sends); hide(fanout_before_receiving); hide(invocation_only);
    hide(follows); hide(fresh_send); hide(delivery_fair); hide(process_fair);
    let w = World::Uniform(d);
    let m = resume_at(agreement_reader(false), first_events(w));
    let c = Process::SecondClient;
    let e = service_run(w, false);
    let result = |s: Reader| s.returned;
    let base = base_reader(d);
    fair_quorum_progress_boundary(w, false);
    assert forall|i: nat| {
        let ev = process_step((e.state)(i), #[trigger] (e.action)(i)); read_event(ev) && stock_work(ev)
    } by { if i < 10 {prefix_index(i as int);} }
    assert forall|k: nat| {
        let a = #[trigger] actions_before(e, k);
        let s = states_through(e, k);
        let es = observations(s, a);
        accepted(base, es) && only_request_sends(a, c, live_pair()) && fanout_before_receiving(es, c)
            && (sr2_result(base, result, es).is_some() ==> invocation_only(a, c, live_pair()))
    } by {
        let a = actions_before(e, k);
        let s = states_through(e, k);
        let es = observations(s, a);
        assert(accepted(m, es) && (sr2_result(m, result, es).is_some() ==> invocation_only(a, c, live_pair())));
        assert forall|i: int| 0 <= i<k implies {
            let ev = #[trigger] es[i]; (base.accept)(memory(base, ev.actor, es, i as nat), ev)
        } by {
            let ev = es[i]; assert(read_event(process_step((e.state)(i as nat), (e.action)(i as nat))));
            memory_from_same_local_state(base, m, ev.actor, es, i as nat);
            assert((m.accept)(memory(m, ev.actor, es, i as nat), ev));
        }
        memory_from_same_local_state(base, m, c, es, k);
    }
    let k = choose|k: nat| #[trigger] sr2_result(m, result, observations(states_through(e, k), actions_before(e, k))).is_some();
    memory_from_same_local_state(base, m, c, observations(states_through(e, k), actions_before(e, k)), k);
    assert(sr2_result(base, result, observations(states_through(e, k), actions_before(e, k))).is_some());
    alpha_receipt_cut(Notice::G);
    assert forall|id: nat| !delayed_slots().contains(id) implies
        packet_at(first_cut(w), id) == #[trigger] packet_at(after_receipt(Notice::G), id) by {};
    assert(admissible_service(first_cut(w), base, result, e));
    assert(stock_cut(first_cut(w), after_receipt(Notice::G)));
    let done = |s, a| sr2_result(base, result, observations(s, a)).is_some();
    assert(done(states_through(e, k), actions_before(e, k)));
    assert(eventually_responds(e, |n, p| live_process(n, p), done));
    assert forall|i: nat| stock_work(process_step((e.state)(i), #[trigger] (e.action)(i))) by {
        assert(read_event(process_step((e.state)(i), (e.action)(i))));
    }
}

pub open spec fn held_read_pair(a: Seq<Action<Wire>>, v: int) -> bool {
    incompatible_completions(Notice::G, local_reader(), |s: Located| s.reader.prior.reply.unwrap(),
        |s: Located| s.reader.returned, a, v) && ordinary_suffix(branch(), a) && ordinary_suffix(beta(Notice::G), a)
}

// Exercise the general stock-to-hybrid theorem on an actual stock prefix
// and fair suffix for every stock value d. Differing answer values cross
// the correlation; the client receives the hybrid responders' real values.
pub proof fn ordinary_quorum_transfers_stock_availability(d: int)
    ensures exists|a: Seq<Action<Wire>>, v: int| #[trigger] held_read_pair(a, v),
{
    hide(accepted); hide(admissible_service); hide(eventually_responds);
    hide(handler_correspondence); hide(incompatible_completions); hide(delivery_fair); hide(process_fair);
    let n = Notice::G;
    let w = World::Uniform(d);
    let base = base_reader(d);
    let net = first_cut(w);
    let actual = after_receipt(n).locals;
    let b = branch();
    let m = local_reader();
    let es = checkpoint_observations(b);
    located_first_read(alpha(n)); located_first_read(beta(n)); uniform_stock_service(d);
    sample_values_can_change(base, net.locals, actual);
    assert forall|p: Process| #[trigger] reader_phase(p, (base.initial)(p), (resume_at(m, es).initial)(p)) by {
        located_memory(p, es, es.len());
        first_memory(World::Hybrid, false, p, es.len()); first_memory(w, false, p, first_events(w).len());
    }
    let first = |s: Located| s.reader.prior.reply.unwrap();
    let result = |s: Located| s.reader.returned;
    stock_availability_gives_held_pair(n, m, first, result,
        base, |s: Reader| s.returned, net, service_run(w, false), |n, p| live_process(n, p),
        |w| erase_value(w), |s, w| encode_sample(actual, s, w), |p, x, y| reader_phase(p, x, y));
    let (a, v) = choose|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v)
        && ordinary_suffix(alpha(n), a) && ordinary_suffix(beta(n), a);
    assert(held_read_pair(a, v));
}

}
