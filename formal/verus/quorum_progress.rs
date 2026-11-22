use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::*;
use crate::delivery::*;
use crate::progress::*;
use crate::protocol::*;
use crate::sr2::*;
use crate::stock_first::*;
use crate::survivors::sr2_result;

verus! {

// A stock implementation may use an invariant of its strong-only data.
// The additional return guard compares two ordinary register samples.
// It consults neither the weak evidence nor the objective order.
pub open spec fn agreement_reader(require_agreement: bool) -> LocalProtocol<Reader, int, Wire> {
    let m = read_protocol(Set::empty(), Notice::G, |a: Report, b: Report| a.value);
    LocalProtocol {
        accept: |s: Reader, e: ProcessStep<int, Wire>| (m.accept)(s, e)
            && (!require_agreement || e.action != Action::Strong(Process::SecondClient)
                || s.r1.unwrap().value == s.r2.unwrap().value),
        ..m
    }
}

pub proof fn agreement_guard_preserves_weak_work(
    strict: bool, s: Reader, net: Network<int, Wire>, a: Action<Wire>,
)
    requires enabled(net, a), ordinary_step(net, a),
    ensures direct_step(agreement_reader(strict), s, net, a),
{
    ungated_read_preserves_weak_work(Notice::G, |x: Report, y: Report| x.value, s, net, a);
}

pub enum World { Uniform(int), Hybrid }

pub open spec fn branch() -> Fork { alpha(Notice::G) }

pub open spec fn first_events(w: World) -> Seq<ProcessStep<int, Wire>> {
    match w { World::Uniform(d) => stock_first_events(branch(), d), World::Hybrid => checkpoint_observations(branch()) }
}

pub open spec fn first_cut(w: World) -> Network<int, Wire> {
    match w { World::Uniform(d) => stock_first_net(branch(), d, 15), World::Hybrid => checkpoint_end(branch()) }
}

pub open spec fn first_control(w: World, p: Process, k: nat) -> Control {
    match w {
        World::Hybrid => expected_control(branch(), p, k),
        World::Uniform(d) => Control { weak_copy: None, reply: if p == Process::FirstClient && k >= 10 {Some(d)} else {None},
            ..expected_control(branch(), p, k + 2) },
    }
}

pub(crate) proof fn first_memory(w: World, strict: bool, p: Process, k: nat)
    requires k <= first_events(w).len(),
    ensures memory(agreement_reader(strict), p, first_events(w), k) == empty_exchange(first_control(w, p, k)),
    decreases k,
{
    if k > 0 { let j = (k - 1) as nat; first_memory(w, strict, p, j); prefix_index(j as int); }
}

pub proof fn first_prefix_is_real(w: World, strict: bool)
    ensures accepted(agreement_reader(strict), first_events(w)),
        match w {
            World::Hybrid => trace(|x, v| cell(x, v), checkpoint_states(branch()), actions_to_crash(branch()))
                && completed_quorum_sample(agreement_reader(strict), |s: Reader| s.prior.reply.unwrap(), branch()),
            World::Uniform(d) => trace(|x, v| cell(x, v), stock_first_states(branch(), d), stock_first_actions(branch(), d))
                && first_cut(w).pending.dom() == set![6nat]
                && memory(agreement_reader(strict), Process::FirstClient, first_events(w), 12).prior.reply == Some(d)
                && memory(agreement_reader(strict), Process::FirstClient, first_events(w), 12).prior.finished,
        },
{
    let m = agreement_reader(strict);
    let es = first_events(w);
    let c = Process::FirstClient;
    assert forall|i: int| 0 <= i<es.len() implies {
        let e = #[trigger] es[i]; (m.accept)(memory(m, e.actor, es, i as nat), e)
    } by { first_memory(w, strict, es[i].actor, i as nat); prefix_index(i); }
    match w {
        World::Uniform(d) => {
            uniform_first_transport(branch(), d); first_memory(w, strict, c, 12);
            assert(first_cut(w).pending.dom() =~= set![6nat]);
        },
        World::Hybrid => {
            prefix_transport_is_enabled(branch());
            assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m, branch(), k))
                by { first_memory(w, strict, c, k); }
            first_memory(w, strict, c, 13); first_memory(w, strict, c, 14);
            assert(during_sr1(branch(), 10, Replica::R2) == 5);
        },
    }
}

pub open spec fn sample(w: World, r: Replica) -> Report {
    Report { value: (first_cut(w).locals)(r), answered_first: true }
}

pub open spec fn returns(w: World, strict: bool) -> bool { !strict || w is Uniform }

pub open spec fn timer(k: nat) -> Action<Wire> {
    if k % 3 == 0 { Action::Strong(at(Replica::R1)) } else if k % 3 == 1 { Action::Strong(at(Replica::R2)) }
    else { Action::ClientInput(Process::SecondClient, Wire::Peer(0)) }
}

// In the hybrid run the real R3 packet is actually delivered. In stock
// there is no such packet. After the two reports every live process runs.
pub open spec fn scheduled(w: World, strict: bool, k: nat) -> Action<Wire> {
    if k < 4 { queries()[k as int] } else if k == 4 {
        if w is Hybrid { Action::Deliver(2) } else { Action::Strong(at(Replica::R2)) }
    } else if k == 5 { reply_action(Replica::R1, sample(w, Replica::R1)) }
    else if k == 6 { reply_action(Replica::R2, sample(w, Replica::R2)) }
    else if k == 7 { Action::Deliver(13) } else if k == 8 { Action::Deliver(14) }
    else if k == 9 && returns(w, strict) { Action::Strong(Process::SecondClient) }
    else { timer(k) }
}

pub open spec fn service_net(w: World, k: nat) -> Network<int, Wire> {
    let n = first_cut(w);
    let pending = n.pending;
    let pending = if k >= 5 && w is Hybrid {pending.remove(2)} else {pending};
    let pending = if 1 <= k < 3 {pending.insert(11, query_packet(Replica::R1))} else {pending};
    let pending = if 2 <= k < 4 {pending.insert(12, query_packet(Replica::R2))} else {pending};
    let pending = if 6 <= k < 8 {pending.insert(13, answer_packet(Replica::R1, sample(w, Replica::R1)))} else {pending};
    let pending = if 7 <= k < 9 {pending.insert(14, answer_packet(Replica::R2, sample(w, Replica::R2)))} else {pending};
    Network {pending, ..n}
}

pub open spec fn service_run(w: World, strict: bool) -> Execution<int, Wire> {
    Execution {state: |k| service_net(w, k), action: |k| scheduled(w, strict, k)}
}

pub open spec fn live_process(net: Network<int, Wire>, p: Process) -> bool { live(net, p) }

pub open spec fn local_after(w: World, strict: bool, p: Process, k: nat) -> Reader {
    let old = first_control(w, p, first_events(w).len());
    let c = p == Process::SecondClient;
    let prior = if c && k >= 1 {Control {sent_requests: if k == 1 {set![Replica::R1]} else {live_pair()}, ..old}}
        else if p == at(Replica::R2) && w is Hybrid && k >= 5 { Control {learned: Some(Notice::G), ..old} } else {old};
    Reader {prior, asked: (p == at(Replica::R1) && k >= 3) || (p == at(Replica::R2) && k >= 4),
        r1: if c && k >= 8 {Some(sample(w, Replica::R1))} else {None},
        r2: if c && k >= 9 {Some(sample(w, Replica::R2))} else {None},
        returned: if c && k >= 10 && returns(w, strict) { Some(sample(w, Replica::R1).value)} else {None}}
}

proof fn local_step(w: World, strict: bool, p: Process, k: nat)
    ensures ({
        let m = agreement_reader(strict);
        let s = local_after(w, strict, p, k);
        let e = process_step(service_net(w, k), scheduled(w, strict, k));
        if e.actor == p { (m.accept)(s, e) && (m.update)(s, e) == local_after(w, strict, p, k + 1) }
        else { s == local_after(w, strict, p, k + 1) }
    }),
{
    if k < 10 {prefix_index(k as int);}
}

proof fn service_memory(w: World, strict: bool, p: Process, k: nat, limit: nat)
    requires k <= limit,
    ensures ({
        let e = service_run(w, strict);
        let m = resume_at(agreement_reader(strict), first_events(w));
        memory(m, p, observations(states_through(e, limit), actions_before(e, limit)), k) == local_after(w, strict, p, k)
    }),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat; service_memory(w, strict, p, j, limit); local_step(w, strict, p, j);
    } else { first_memory(w, strict, p, first_events(w).len()); }
}

proof fn service_is_admitted(w: World, strict: bool)
    ensures ({
        let e = service_run(w, strict);
        let m = resume_at(agreement_reader(strict), first_events(w));
        admissible_service(first_cut(w), m, |s: Reader| s.returned, e)
            && forall|k: nat| majority_up(#[trigger] (e.state)(k))
    }),
{
    let e = service_run(w, strict);
    let c = Process::SecondClient;
    let m = resume_at(agreement_reader(strict), first_events(w));
    assert(first_cut(w).pending =~= service_net(w, 0).pending);
    assert forall|k: nat| {
        let x = #[trigger] (e.action)(k);
        let net = (e.state)(k);
        let post = advance(|x, v| cell(x, v), net, x);
        enabled(net, x) && post == (e.state)(k + 1) && fresh_send(x, delayed_slots())
    } by {
        if k < 10 {prefix_index(k as int);}
        let post = advance(|x, v| cell(x, v), (e.state)(k), (e.action)(k));
        assert(post.pending =~= (e.state)(k + 1).pending); assert(post.locals =~= (e.state)(k + 1).locals);
    }
    assert forall|k: nat| {
        let a = #[trigger] actions_before(e, k);
        let s = states_through(e, k);
        let es = observations(s, a);
        accepted(m, es) && only_request_sends(a, c, live_pair()) && fanout_before_receiving(es, c)
            && (sr2_result(m, |s: Reader| s.returned, es).is_some() ==> invocation_only(a, c, live_pair()))
    } by {
        let a = actions_before(e, k);
        let s = states_through(e, k);
        let es = observations(s, a);
        assert forall|i: int| 0 <= i<k implies {
            let ev = #[trigger] es[i]; (m.accept)(memory(m, ev.actor, es, i as nat), ev)
        } by { service_memory(w, strict, es[i].actor, i as nat, k); local_step(w, strict, es[i].actor, i as nat); }
        assert forall|i: int| 0 <= i<k implies match #[trigger] a[i] {
            Action::Send(_, p) if p.from == c => invocation_packet(p) && live_pair().contains(p.to->At_0)
                && (forall|j: int| 0 <= j<i ==> !client_sends_to(#[trigger] a[j], c, p.to->At_0)), _ => true
        } by { if i < 10 {prefix_index(i);} }
        assert forall|i: int, j: int| 0 <= j<i<es.len() implies match (#[trigger] es[i]).action {
            Action::Send(_, p) if p.from == c => (#[trigger] es[j]).actor != c || es[j].incoming.is_none(), _ => true
        } by { if i < 10 {prefix_index(i);} }
        service_memory(w, strict, c, k, k);
        if k >= 2 {
            assert(client_sends_to(a[0], c, Replica::R1) && client_sends_to(a[1], c, Replica::R2));
            assert(invocation_only(a, c, live_pair()));
        }
    }
}

pub(crate) proof fn delivery_witness(e: Execution<int, Wire>, i: nat, id: nat, j: nat)
    requires j >= i, (e.action)(j) == Action::Deliver(id) || !live((e.state)(j), (e.state)(i).pending[id].to),
    ensures exists|k: nat| k >= i && (#[trigger] (e.action)(k) == Action::Deliver(id) || !live((e.state)(k), (e.state)(i).pending[id].to)),
{}

proof fn service_is_fair(w: World, strict: bool)
    ensures delivery_fair(service_run(w, strict)), process_fair(service_run(w, strict), |n, p| live_process(n, p)),
{
    let e = service_run(w, strict);
    assert forall|i: nat, id: nat| #[trigger] (e.state)(i).pending.contains_key(id) implies exists|j: nat| j >= i
        && (#[trigger] (e.action)(j) == Action::Deliver(id) || !live((e.state)(j), (e.state)(i).pending[id].to)) by {
        let j = if !live((e.state)(i), (e.state)(i).pending[id].to) { i}
            else if id == 11 {2nat} else if id == 12 {3nat} else if id == 2 {4nat} else if id == 13 {7nat} else {8nat};
        assert((e.action)(j) == scheduled(w, strict, j));
        assert(j >= i && ((e.action)(j) == Action::Deliver(id) || !live((e.state)(j), (e.state)(i).pending[id].to)));
        delivery_witness(e, i, id, j);
    }
    let run = |n, p| live_process(n, p);
    assert forall|from: nat, p: Process| #[trigger] continuously_runnable(e, run, from, p)
        implies exists|j: nat| j >= from && #[trigger] runs_at(e, j, p) by {
        assert(run((e.state)(from), p));
        let r: nat = if p == at(Replica::R1) { 0} else if p == at(Replica::R2) { 1} else {2};
        let j = 3*(from+10)+r;
        assert(j % 3 == r);
        assert(j >= from && runs_at(e, j, p));
    }
}

// Same two query deliveries and two genuine shared-register replies.
// The strict reader returns on every uniform instance of this run. The
// hybrid supplies even the truthful G confirmation and still cannot pass
// its ordinary unanimity guard on these samples.
pub proof fn fair_quorum_progress_boundary(w: World, strict: bool)
    ensures ({
        let m = resume_at(agreement_reader(strict), first_events(w));
        let e = service_run(w, strict);
        let done = |s, a| sr2_result(m, |u: Reader| u.returned, observations(s, a)).is_some();
        accepted(agreement_reader(strict), first_events(w)) && admissible_service(first_cut(w), m, |s: Reader| s.returned, e)
            && delivery_fair(e) && process_fair(e, |n, p| live_process(n, p))
            && (eventually_responds(e, |n, p| live_process(n, p), done) == returns(w, strict))
            && local_after(w, strict, Process::SecondClient, 9).r1 == Some(sample(w, Replica::R1))
            && local_after(w, strict, Process::SecondClient, 9).r2 == Some(sample(w, Replica::R2))
            && (w is Hybrid ==> pre_sr1_g(branch(), weak_assignment(branch(), true).ops)
                && local_after(w, strict, at(Replica::R2), 9).prior.learned == Some(Notice::G))
    }),
{
    let m = resume_at(agreement_reader(strict), first_events(w));
    let e = service_run(w, strict);
    let c = Process::SecondClient;
    first_prefix_is_real(w, strict); service_is_fair(w, strict); service_is_admitted(w, strict);
    if w is Hybrid { weak_assignment_at_delivery(branch(), true); }
    let done = |s, a| sr2_result(m, |u: Reader| u.returned, observations(s, a)).is_some();
    if returns(w, strict) {
        service_memory(w, strict, c, 10, 10); assert(done(states_through(e, 10), actions_before(e, 10)));
    } else {
        assert forall|k: nat| !#[trigger] done(states_through(e, k), actions_before(e, k))
            by { service_memory(w, strict, c, k, k); }
    }
}

pub open spec fn changes_quorum_value(net: Network<int, Wire>, a: Action<Wire>, r: Replica) -> bool {
    live_pair().contains(r) && match local_input(net, a, r) {
        Some(Wire::Copy(v)) => v != (net.locals)(r),
        _ => false,
    }
}

pub open spec fn reports_match(net: Network<int, Wire>, r: Replica, v: int) -> bool {
    forall|id: nat| #[trigger] net.pending.contains_key(id) && report_from(net.pending[id], r)
        ==> net.pending[id].input->Answer2_0.value == v
}

proof fn stationary_reports(
    w: World, strict: bool, t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat,
)
    requires trace(|x, v| cell(x, v), t, a), t[0] == first_cut(w), k <= a.len(),
        accepted(resume_at(agreement_reader(strict), first_events(w)), observations(t, a)),
        forall|j: int, r: Replica| 0 <= j<k ==> !#[trigger] changes_quorum_value(t[j], a[j], r),
    ensures ({
        let m = resume_at(agreement_reader(strict), first_events(w));
        let c = memory(m, Process::SecondClient, observations(t, a), k);
        let n = t[k as int];
        let one = sample(w, Replica::R1).value;
        let two = sample(w, Replica::R2).value;
        (n.locals)(Replica::R1) == one && (n.locals)(Replica::R2) == two
            && reports_match(n, Replica::R1, one) && reports_match(n, Replica::R2, two)
            && (c.r1.is_some() ==> c.r1.unwrap().value == one) && (c.r2.is_some() ==> c.r2.unwrap().value == two)
            && (strict && one != two ==> c.returned.is_none())
    }),
    decreases k,
{
    let c = Process::SecondClient;
    let es = observations(t, a);
    let m = resume_at(agreement_reader(strict), first_events(w));
    if k == 0 {
        first_memory(w, strict, c, first_events(w).len());
    } else {
        let j = (k - 1) as nat; stationary_reports(w, strict, t, a, j);
        let n = t[j as int];
        let ev = es[j as int];
        let step = a[j as int];
        let old = memory(m, c, es, j);
        let who = memory(m, ev.actor, es, j);
        assert(enabled(n, step) && t[k as int] == advance(|x, v| cell(x, v), n, step));
        assert((m.accept)(who, ev));
        assert(!changes_quorum_value(n, step, Replica::R1) && !changes_quorum_value(n, step, Replica::R2));
        assert forall|r: Replica, id: nat| #[trigger] live_pair().contains(r) && #[trigger] t[k as int].pending.contains_key(id)
            && report_from(t[k as int].pending[id], r) implies t[k as int].pending[id].input->Answer2_0.value == (n.locals)(r) by {
            if r == Replica::R1 {assert(reports_match(n, r, sample(w, Replica::R1).value));} else {assert(reports_match(n, r, sample(w, Replica::R2).value));}
            match step {
                Action::Send(slot, p) if slot == id => {assert(ev.own_local == Some((n.locals)(r)));},
                Action::Send(_, _) | Action::Deliver(_) => {assert(n.pending.contains_key(id));},
                _ => {},
            }
        }
        if let Action::Deliver(id) = step {
            assert(n.pending.contains_key(id) && ev.incoming == Some(n.pending[id]));
        }
        if strict && w is Hybrid { assert(step != Action::Strong(c)); }
    }
}

// Every possible first return on this split quorum requires a real change
// to a survivor's shared value. Bookkeeping, ordinary replies and learning
// G cannot suffice. A local application write remains a distinct cause.
pub proof fn split_return_needs_application_input(
    t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires crate::service::response_path(resume_at(agreement_reader(true), first_events(World::Hybrid)),
        |s: Reader| s.returned, first_cut(World::Hybrid), delayed_slots(), t, a, v),
    ensures exists|j: int, r: Replica| 0 <= j<a.len() && #[trigger] changes_quorum_value(t[j], a[j], r)
        && (match a[j] {
            Action::Local(site, Wire::Copy(_)) => site == r,
            Action::Deliver(id) => t[j].pending.contains_key(id) && t[j].pending[id].path == Path::Weak
                && t[j].pending[id].to == at(r) && t[j].pending[id].input is Copy,
            _ => false,
        }),
{
    if !(exists|j: int, r: Replica| 0 <= j<a.len() && #[trigger] changes_quorum_value(t[j], a[j], r)) {
        stationary_reports(World::Hybrid, true, t, a, a.len());
    }
    let (j, r) = choose|j: int, r: Replica| 0 <= j<a.len() && #[trigger] changes_quorum_value(t[j], a[j], r);
    assert(enabled(t[j], a[j]));
    match a[j] {Action::Local(_, _) | Action::Deliver(_) => {}, _ => {}}
}

// Both programs have the same updates and private history. Over every
// uniform read-only stock trace the added guard is redundant, even when
// authentication, queue order and local scheduling vary.
pub proof fn uniform_stock_admits_the_same_reads(
    d: int, t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>,
)
    requires trace(|x, v| cell(x, v), t, a), t[0] == first_cut(World::Uniform(d)),
        forall|j: int, r: Replica| 0 <= j<a.len() ==> !#[trigger] changes_quorum_value(t[j], a[j], r),
    ensures ({
        let es = observations(t, a);
        let w = World::Uniform(d);
        let m = resume_at(agreement_reader(false), first_events(w));
        let other = resume_at(agreement_reader(true), first_events(w));
        accepted(m, es) == accepted(other, es)
            && forall|k: nat, p: Process| k <= es.len() ==> #[trigger] memory(other, p, es, k) == memory(m, p, es, k)
    }),
{
    hide(memory);
    let w = World::Uniform(d);
    let es = observations(t, a);
    let m = resume_at(agreement_reader(false), first_events(w));
    let other = resume_at(agreement_reader(true), first_events(w));
    assert forall|k: nat, p: Process| k <= es.len() implies #[trigger] memory(other, p, es, k) == memory(m, p, es, k) by {
        first_memory(w, false, p, first_events(w).len()); first_memory(w, true, p, first_events(w).len());
        memory_from_same_local_state(other, m, p, es, k);
    }
    if accepted(m, es) {
        assert forall|i: int| 0 <= i<es.len() implies {
            let ev = #[trigger] es[i]; (other.accept)(memory(other, ev.actor, es, i as nat), ev)
        } by {
            let ev = es[i];
            let z = memory(m, ev.actor, es, i as nat); assert((m.accept)(z, ev));
            if ev.action == Action::Strong(Process::SecondClient) {
                stationary_reports(w, false, t, a, i as nat);
                assert(ev.actor == Process::SecondClient && z.r1.is_some() && z.r2.is_some());
            }
        }
    }
    if accepted(other, es) {
        assert forall|i: int| 0 <= i<es.len() implies {
            let ev = #[trigger] es[i]; (m.accept)(memory(m, ev.actor, es, i as nat), ev)
        } by { let ev = es[i]; assert((other.accept)(memory(other, ev.actor, es, i as nat), ev)); }
    }
}

pub proof fn uniform_stock_preserves_majority_progress(
    d: int, e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
)
    requires admissible_service(first_cut(World::Uniform(d)), resume_at(agreement_reader(false),
        first_events(World::Uniform(d))), |s: Reader| s.returned, e),
        forall|j: nat, r: Replica| !#[trigger] changes_quorum_value((e.state)(j), (e.action)(j), r),
    ensures ({
        let w = World::Uniform(d);
        let m = resume_at(agreement_reader(false), first_events(w));
        let other = resume_at(agreement_reader(true), first_events(w));
        let result = |x: Reader| x.returned;
        admissible_service(first_cut(w), other, result, e)
            && (eventually_responds(e, runnable, |s, a| sr2_result(m, result, observations(s, a)).is_some())
                == eventually_responds(e, runnable, |s, a| sr2_result(other, result, observations(s, a)).is_some()))
    }),
{
    hide(accepted); hide(memory); hide(fresh_send); hide(delivery_fair); hide(process_fair);
    hide(only_request_sends); hide(fanout_before_receiving); hide(invocation_only);
    let w = World::Uniform(d);
    let m = resume_at(agreement_reader(false), first_events(w));
    let other = resume_at(agreement_reader(true), first_events(w));
    let result = |x: Reader| x.returned;
    assert forall|k: nat| {
        let a = #[trigger] actions_before(e, k);
        let s = states_through(e, k);
        let es = observations(s, a);
        accepted(m, es) == accepted(other, es) && sr2_result(m, result, es) == sr2_result(other, result, es)
    } by {
        let a = actions_before(e, k);
        let s = states_through(e, k);
        let es = observations(s, a);
        finite_prefix_is_protocol_trace(e, |x, v| cell(x, v), |n, a| true, k);
        assert forall|j: int, r: Replica| 0 <= j<a.len() implies !#[trigger] changes_quorum_value(s[j], a[j], r)
            by { assert(!changes_quorum_value((e.state)(j as nat), (e.action)(j as nat), r)); }
        uniform_stock_admits_the_same_reads(d, s, a);
    }
    let c = Process::SecondClient;
    assert forall|k: nat| {
        let a = #[trigger] actions_before(e, k);
        let s = states_through(e, k);
        let es = observations(s, a);
        accepted(other, es) && only_request_sends(a, c, live_pair()) && fanout_before_receiving(es, c)
            && (sr2_result(other, result, es).is_some() ==> invocation_only(a, c, live_pair()))
    } by {
        let a = actions_before(e, k);
        let es = observations(states_through(e, k), a);
        assert(accepted(m, es) && (sr2_result(m, result, es).is_some() ==> invocation_only(a, c, live_pair())));
    }
    assert(admissible_service(first_cut(w), other, result, e));
    let done = |s, a| sr2_result(m, result, observations(s, a)).is_some();
    let guarded = |s, a| sr2_result(other, result, observations(s, a)).is_some();
    if exists|k: nat| #[trigger] done(states_through(e, k), actions_before(e, k)) {
        let k = choose|k: nat| #[trigger] done(states_through(e, k), actions_before(e, k));
        assert(guarded(states_through(e, k), actions_before(e, k)));
    }
    if exists|k: nat| #[trigger] guarded(states_through(e, k), actions_before(e, k)) {
        let k = choose|k: nat| #[trigger] guarded(states_through(e, k), actions_before(e, k));
        assert(done(states_through(e, k), actions_before(e, k)));
    }
    assert(eventually_responds(e, runnable, done) == eventually_responds(e, runnable, guarded));

}

}
