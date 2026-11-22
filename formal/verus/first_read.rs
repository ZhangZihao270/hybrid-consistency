use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::unsent::*;

verus! {

// Direct fan-out service interface. The table stores authenticated replies,
// not the client's chosen value. The client may use any member selector.
pub struct Intake {
    pub control: Control,
    pub samples: Map<Replica, int>,
}

pub open spec fn initial_intake() -> Intake {
    Intake { control: initial_control(), samples: Map::empty() }
}

pub open spec fn record_reply(old: Map<Replica, int>, e: ProcessStep<int, Wire>) -> Map<Replica, int> {
    if e.actor == Process::FirstClient && e.incoming.is_some() && first_reply(e.incoming.unwrap()) {
        let p = e.incoming.unwrap(); old.insert(p.from->At_0, p.input->Reply_0)
    } else { old }
}

pub open spec fn collect(s: Intake, e: ProcessStep<int, Wire>) -> Intake {
    Intake { control: change_control(s.control, e), samples: record_reply(s.samples, e) }
}

pub open spec fn intake_machine() -> LocalProtocol<Intake, int, Wire> {
    LocalProtocol { initial: |p| initial_intake(), accept: |s: Intake, e| permits_step(s.control, e),
        update: |s, e| collect(s, e), done: |s: Intake| s.control.finished }
}

pub open spec fn first_packet(p: Packet<Wire>) -> bool {
    (invocation_packet(p) && p.from == Process::FirstClient) || first_reply(p) || notice_to(p, p.to)
}

pub open spec fn first_service(e: ProcessStep<int, Wire>) -> bool {
    match e.action {
        Action::Send(_, p) => first_packet(p),
        Action::Deliver(_) => e.incoming.is_some() && (first_packet(e.incoming.unwrap())
            || crate::attribution::applied_copy(e, Replica::R1) || crate::attribution::applied_copy(e, Replica::R2)),
        Action::Strong(p) => p == Process::FirstClient,
        Action::StopFirstClient | Action::CrashR3 | Action::StartSecondClient => true,
        _ => false,
    }
}

pub type FirstRel<S>  = spec_fn(Process, Intake, S) -> bool;

// These local laws specify an independently usable direct service, including
// the client's ability to finish locally after two agreeing replies. A's
// eventual response alone does not give this service discipline.
pub open spec fn direct_first_service<S>(m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, rel: FirstRel<S>) -> bool {
    (forall|p: Process| #[trigger] rel(p, initial_intake(), (m.initial)(p)))
    && (forall|x: Intake, y: S, e: ProcessStep<int, Wire>| crate::confirmation::transport_event(e) && first_service(e)
        && #[trigger] rel(e.actor, x, y) && #[trigger] permits_step(x.control, e)
        ==> (m.accept)(y, e) && rel(e.actor, collect(x, e), (m.update)(y, e)))
    && (forall|x: Intake, y: S| #[trigger] rel(Process::FirstClient, x, y) ==> {
        (x.samples.dom().len()<2 ==> !(m.done)(y))
            && (x.control.finished ==> (m.done)(y))
            && ((m.done)(y) ==> exists|r: Replica| #[trigger] x.samples.contains_key(r) && x.samples[r] == first(y))
    })
}

pub open spec fn table_after(b: Fork, p: Process, k: nat) -> Map<Replica, int> {
    let tab = Map::empty();
    let tab = if p == Process::FirstClient && k >= 12 {tab.insert(crate::origin(b.branch), first_value(b))} else {tab};
    if p == Process::FirstClient && k >= 13 {tab.insert(Replica::R3, first_value(b))} else {tab}
}

proof fn intake_tracks_deliveries(b: Fork, p: Process, k: nat)
    requires k <= checkpoint_observations(b).len(),
    ensures ({
        let es = checkpoint_observations(b);
        let h = memory(intake_machine(), p, es, k);
        h.control == expected_control(b, p, k) && h.samples == table_after(b, p, k)
    }),
    decreases k,
{
    prefix_memory_tracks_actual_messages(b, p, k);
    let es = checkpoint_observations(b);
    if k > 0 {
        let j = (k - 1) as nat; intake_tracks_deliveries(b, p, j);
        prefix_memory_tracks_actual_messages(b, p, j);
        prefix_index(j as int);
        if es[j as int].actor == p {
            assert(record_reply(table_after(b, p, j), es[j as int]) =~= table_after(b, p, k));
        }
    }
}

proof fn following_intake<S>(
    m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, rel: FirstRel<S>,
    b: Fork, p: Process, k: nat,
)
    requires direct_first_service(m, first, rel), k <= checkpoint_observations(b).len(),
    ensures ({
        let es = checkpoint_observations(b);
        let h = memory(intake_machine(), p, es, k);
        let s = memory(m, p, es, k);
        rel(p, h, s) && (k<es.len() && es[k as int].actor == p ==> (m.accept)(s, es[k as int]))
    }),
    decreases k,
{
    hide(memory);
    let es = checkpoint_observations(b);
    let refm = intake_machine();
    if k > 0 {
        let j = (k - 1) as nat; following_intake(m, first, rel, b, p, j);
        assert(rel(p, memory(refm, p, es, k), memory(m, p, es, k))) by {
            if es[j as int].actor == p {
                intake_tracks_deliveries(b, p, j); prefix_memory_tracks_actual_messages(b, p, j);
                both_prefixes_are_enabled_and_client_finishes(b);
                let e = es[j as int];
                assert((checkpoint_machine().accept)(memory(checkpoint_machine(), p, es, j), e));
                assert(first_service(e)) by { prefix_index(j as int); }
                assert(crate::confirmation::transport_event(e)) by {
                    let t = checkpoint_states(b);
                    let a = actions_to_crash(b);
                    assert(enabled(t[j as int], a[j as int]) && process_step(t[j as int], a[j as int]) == e);
                }
                assert(permits_step(memory(refm, p, es, j).control, e));
            }
            reveal(memory);
        }
    } else { reveal(memory); }
    if k < es.len() && es[k as int].actor == p {
        let e = es[k as int];
        let t = checkpoint_states(b);
        let a = actions_to_crash(b);
        both_prefixes_are_enabled_and_client_finishes(b);
        intake_tracks_deliveries(b, p, k); prefix_memory_tracks_actual_messages(b, p, k);
        assert((checkpoint_machine().accept)(memory(checkpoint_machine(), p, es, k), e));
        assert(first_service(e)) by { prefix_index(k as int); }
        assert(crate::confirmation::transport_event(e)) by {
            assert(enabled(t[k as int], a[k as int]) && process_step(t[k as int], a[k as int]) == e);
        }
    }
}

pub proof fn direct_handlers_supply_prefix_and_sample<S>(
    b: Fork, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, rel: FirstRel<S>,
)
    requires direct_first_service(m, first, rel),
    ensures accepted(m, checkpoint_observations(b)), completed_quorum_sample(m, first, b), first_result(m, first, b) == first_value(b),
{
    hide(memory);
    let es = checkpoint_observations(b);
    let c = Process::FirstClient;
    let refm = intake_machine();
    assert forall|i: int| 0 <= i<es.len() implies {
        let e = #[trigger] es[i]; (m.accept)(memory(m, e.actor, es, i as nat), e)
    } by { following_intake(m, first, rel, b, es[i].actor, i as nat); }
    assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m, b, k)) by {
        following_intake(m, first, rel, b, c, k); intake_tracks_deliveries(b, c, k);
        let tab = table_after(b, c, k);
        if k == 12 { assert(tab.dom() =~= set![crate::origin(b.branch)]); } else { assert(tab.dom() =~= Set::empty()); }
        assert(tab.dom().len()<2);
    }
    following_intake(m, first, rel, b, c, 14); intake_tracks_deliveries(b, c, 14);
    assert((m.done)(first_client_at(m, b, 14)));
    let end = first_return_len(m, b);
    let h = memory(refm, c, es, end);
    let s = first_client_at(m, b, end);
    following_intake(m, first, rel, b, c, end); intake_tracks_deliveries(b, c, end);
    assert((m.done)(s) && rel(c, h, s));
    let r = choose|r: Replica| #[trigger] h.samples.contains_key(r) && h.samples[r] == first(s);
    assert(h.samples[r] == first_value(b));
    assert(crate::first_quorum(b.branch).contains(r) && during_sr1(b, 10, r) == first(s));
}

// Apply the same direct-service law at R3 with its background send still
// unscheduled. Only four local observations enter this induction.
proof fn direct_at_issuer<S>(
    m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, rel: FirstRel<S>,
    b: Fork, x: Intake, y: S, i: int,
)
    requires direct_first_service(m, first, rel), rel(at(Replica::R3), x, y),
        i == 0 || i == 7 || i == 10 || i == 15, permits_step(x.control, checkpoint_observations(b)[i]),
    ensures ({
        let e = checkpoint_observations(b)[i]; (m.accept)(y, e) && rel(at(Replica::R3), collect(x, e), (m.update)(y, e))
    }),
{
    prefix_transport_is_enabled(b);
    let es = checkpoint_observations(b);
    let t = checkpoint_states(b);
    let a = actions_to_crash(b);
    assert(crate::confirmation::transport_event(es[i])) by {
        assert(enabled(t[i], a[i]) && process_step(t[i], a[i]) == es[i]);
    }
    assert(first_service(es[i]) && es[i].actor == at(Replica::R3));
}

pub proof fn direct_service_permits_unsent_prefix<S>(
    m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, rel: FirstRel<S>, b: Fork,
)
    requires direct_first_service(m, first, rel),
    ensures serves_before_sending_status(m, b), accepted(m, unsent_events(b)),
{
    let es = checkpoint_observations(b);
    let p = at(Replica::R3);
    let x = initial_intake();
    let y = (m.initial)(p);
    direct_at_issuer(m, first, rel, b, x, y, 0);
    let x = collect(x, es[0]);
    let y = (m.update)(y, es[0]);
    direct_at_issuer(m, first, rel, b, x, y, 7);
    let x = collect(x, es[7]);
    let y = (m.update)(y, es[7]);
    direct_at_issuer(m, first, rel, b, x, y, 10);
    direct_at_issuer(m, first, rel, b, collect(x, es[10]), (m.update)(y, es[10]), 15);
    direct_handlers_supply_prefix_and_sample(b, m, first, rel);
    unsent_prefix_from_sender(m, b);
}

// Stock/hybrid progress and sender-side causality are independent of the
// first-read service contract. The latter supplies both real prefixes.
pub proof fn direct_service_outcomes<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    rel: FirstRel<S>, copy: spec_fn(S) -> bool,
)
    requires direct_first_service(m, first, rel),
        crate::service::can_respond(resume_at(m, checkpoint_observations(alpha(n))), result, checkpoint_end(alpha(n)), delayed_slots()),
        crate::attribution::source_discipline(m, Replica::R2, copy),
    ensures ({
        let pre = resume_at(m, checkpoint_observations(alpha(n)));
        (exists|a: Seq<Action<Wire>>, v: int| #[trigger] crate::service::incompatible_completions(n, m, first, result, a, v)
            && crate::stock::ordinary_suffix(alpha(n), a) && crate::stock::ordinary_suffix(beta(n), a))
        || (crate::attribution::waits_for_replication(m, checkpoint_states(alpha(n)), actions_to_crash(alpha(n)),
            1, Replica::R2, 2, result, delayed_slots()) && !crate::attribution::no_causal_await(m, result))
        || crate::stock::needs_other_weak_traffic(pre, result, checkpoint_end(alpha(n)), 2, delayed_slots())
    }),
{
    direct_handlers_supply_prefix_and_sample(alpha(n), m, first, rel);
    direct_handlers_supply_prefix_and_sample(beta(n), m, first, rel);
    crate::stock::ordinary_pair_or_required_traffic(n, m, first, result);
    crate::attribution::hot_or_causal_weak_wait(n, m, first, result, copy);
}

}
