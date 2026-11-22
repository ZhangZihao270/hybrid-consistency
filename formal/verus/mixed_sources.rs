use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::ordered_store::*;
use crate::ordered_store::Move;
use crate::quorum_progress::{changes_quorum_value, split_return_needs_application_input, agreement_reader, first_events, first_cut, World};
use crate::protocol::resume_at;
use crate::quorum_rpc::{self as qr, Round, Rpc};
use crate::stock_availability::{self as availability, Stream};
use crate::sr2::*;
use crate::stock_reports::*;

verus! {

// The ordinary applied-write position is one possible piece of stock
// protocol state. In this interface a local weak RMW changes the shared
// value and leaves the ordinary log alone, even if the weak path later
// establishes a separate order for that write.
pub open spec fn weak_local(s: Store, r: Replica, c: Command) -> Store {
    Store { disk: |p| if p == r { Disk { value: execute(c, (s.disk)(p).value), ..(s.disk)(p) } } else { (s.disk)(p) }, ..s }
}

pub open spec fn after_both_weak() -> Store {
    weak_local(weak_local(initial_store(), Replica::R1, Command::Increment), Replica::R2, Command::TimesFive)
}

pub open spec fn ordinary_and_shared(b: Fork, k: nat, r: Replica) -> Disk
    decreases k,
{
    if k == 0 { (after_both_weak().disk)(r) } else {
        let j = (k-1) as nat;
        let d = ordinary_and_shared(b, j, r);
        match local_input(state_after(b, j), actions_to_crash(b)[j as int], r) {
            Some(w) => Disk { value: cell(d.value, w), ..d }, None => d,
        }
    }
}

pub proof fn actual_disk_before_sr2(b: Fork, k: nat, r: Replica)
    requires k <= actions_to_crash(b).len(),
    ensures ({
        let d = ordinary_and_shared(b, k, r);
        d.applied == 0 && d.known == 0 && d.value == (state_after(b, k).locals)(r)
    }),
    decreases k,
{
    if k>0 {
        let j = (k-1) as nat; actual_disk_before_sr2(b, j, r); prefix_index(j as int);
        assert(state_after(b, k) == advance(|v, x|cell(v, x), state_after(b, j), actions_to_crash(b)[j as int])) by {
            prefix_transport_is_enabled(b);
            assert(checkpoint_states(b)[j as int] == state_after(b, j));
        }
    }
}

pub open spec fn cut_store(b: Fork) -> Store {
    Store { disk: |r|ordinary_and_shared(b, actions_to_crash(b).len(), r), ..after_both_weak() }
}

// Instrument just the ordinary sample field at an authenticated reply send.
// Its slot belongs to the real transport; delivery consumes the tag saved at
// that send. All other pending packets remain in the underlying Network.
pub open spec fn capture_event(net: Network<int, Wire>, a: Action<Wire>) -> Observable {
    match a {
        Action::Send(id, p) if p.input is Answer2 && p.from is At => Observable::Send(id, p.from->At_0),
        Action::Deliver(id) if net.pending.contains_key(id) && net.pending[id].input is Answer2 => Observable::Deliver(id),
        _ => Observable::Other,
    }
}

pub open spec fn capture(b: Fork, k: nat) -> Evidence
    decreases k,
{
    if k == 0 { empty_evidence(cut_store(b)) } else {
        let j = (k-1) as nat;
        observe(capture(b, j), capture_event(exchange_net(b, j), completed_actions(b)[j as int]))
    }
}

pub open spec fn actual_tags(b: Fork, k: nat) -> Evidence {
    let s = cut_store(b);
    let r1 = Replica::R1;
    let r2 = Replica::R2;
    let p = if 5 <= k<7 { Map::empty().insert(13nat, Answer { from: r1, data: sample(s, r1) }) } else { Map::empty() };
    let packets = if 6 <= k<8 { p.insert(14nat, Answer { from: r2, data: sample(s, r2) }) } else { p };
    let rows = if k >= 7 { Map::empty().insert(r1, sample(s, r1)) } else { Map::empty() };
    Evidence { store: s, packets, received: if k >= 8 { rows.insert(r2, sample(s, r2)) } else { rows } }
}

proof fn tags_are_actual(b: Fork, k: nat)
    requires k <= 8,
    ensures capture(b, k) == actual_tags(b, k),
        forall|id: nat| #[trigger] capture(b, k).packets.contains_key(id) ==> {
            let a = capture(b, k).packets[id];
            let n = exchange_net(b, k);
            n.pending.contains_key(id) && report_from(n.pending[id], a.from)
                && n.pending[id].input->Answer2_0.value == a.data.value
        },
    decreases k,
{
    actual_disk_before_sr2(b, actions_to_crash(b).len(), Replica::R1);
    actual_disk_before_sr2(b, actions_to_crash(b).len(), Replica::R2);
    if k>0 {
        let j = (k-1) as nat;
        tags_are_actual(b, j); prefix_index(j as int);
        let e = capture_event(exchange_net(b, j), completed_actions(b)[j as int]);
        assert(possible(capture(b, j), e));
        assert(capture(b, k).packets =~= actual_tags(b, k).packets);
        assert(capture(b, k).received =~= actual_tags(b, k).received);
    }
}

// Exact obstruction to borrowing stock A via byte-for-byte stock reports
// for a handler that validates ordinary versions. A data-only handler can
// use the different reachable stock witness in mixed_read instead.
pub proof fn version_sensitive_stock_comparison_fails<X, E>(
    b: Fork, p: crate::stock_availability::ReadSystem<X, E>, view: spec_fn(X) -> Evidence,
    event: spec_fn(X, E, X) -> Observable, x: X,
)
    requires audited_stock(p, view, event), crate::stock_availability::reaches(p, x),
    ensures !consistent_versions(capture(b, 8).received),
        capture(b, 8).received != view(x).received,
        cut_store(b).log.len() == 0 && !allowed(cut_store(b), Move::Apply(Replica::R1))
            && !allowed(cut_store(b), Move::Apply(Replica::R2)),
        pre_sr1_g(b, weak_assignment(b, true).ops),
{
    let j = actions_to_crash(b).len();
    let r1 = Replica::R1;
    let r2 = Replica::R2;
    actual_disk_before_sr2(b, j, r1); actual_disk_before_sr2(b, j, r2);
    tags_are_actual(b, 8); weak_assignment_at_delivery(b, true);
    let rows = capture(b, 8).received;
    assert(rows.contains_key(r1) && rows.contains_key(r2) && rows[r1].version == rows[r2].version && rows[r1].value != rows[r2].value);
    if view(x).received == rows { conflicting_stamp_pair_has_no_stock_source(p, view, event, x, rows[r1], rows[r2]); }
}


// An implementation may also restore an independently saved application
// snapshot. The snapshot's value is determined by its ordinary decided
// prefix, rather than an arbitrary numeric Copy input or a weak status.
pub struct OrdinaryBackup { pub log: Seq<Command>, pub prefix: nat }

pub open spec fn ordinary_install(s: Store, r: Replica, v: int, backups: Map<Replica, OrdinaryBackup>) -> bool {
    (allowed(s, Move::Apply(r)) && apply_disk(s, r).value == v)
        || (backups.contains_key(r) && backups[r].prefix <= backups[r].log.len()
            && extends(backups[r].log, s.log) && value_at(backups[r].log, backups[r].prefix) == v)
}

pub open spec fn weak_payload(p: Packet<Wire>) -> bool {
    p.path == Path::Weak && p.from is At && p.to is At && p.from != p.to
        && (p.input == Wire::Copy(2) || p.input == Wire::Copy(5))
}

// Interface for this read-only workload. Local value installations must
// have an ordinary source. New weak data packets must come from a replica
// that actually has the copied value. Requests, confirmations and other
// metadata (including their delivery) do not require either permission.
// Additional writes, buffering weak installs as local actions, and other
// ordinary repair sources would need their own clauses.
pub open spec fn data_sources(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, backups: Map<Replica, OrdinaryBackup>) -> bool {
    t.len() == a.len()+1 && forall|j: int| 0 <= j<a.len() ==> match #[trigger] a[j] {
        Action::Local(r, Wire::Copy(v)) => ordinary_install(cut_store(alpha(Notice::G)), r, v, backups),
        Action::Send(_, p) if p.input is Copy => weak_payload(p) && (t[j].locals)(p.from->At_0) == p.input->Copy_0,
        _ => true,
    }
}

proof fn authentic_weak_packets(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat, backups: Map<Replica, OrdinaryBackup>)
    requires data_sources(t, a, backups), t[0] == checkpoint_end(alpha(Notice::G)),
        trace(|x, w| cell(x, w), t, a), k <= a.len(),
    ensures forall|id: nat| #[trigger] t[k as int].pending.contains_key(id) && t[k as int].pending[id].input is Copy
         ==> weak_payload(t[k as int].pending[id]),
    decreases k,
{
    if k == 0 {
        assert forall|id: nat| #[trigger] t[0].pending.contains_key(id) && t[0].pending[id].input is Copy
            implies weak_payload(t[0].pending[id]) by { assert(id == 0); }
    } else {
        let j = (k-1) as nat; authentic_weak_packets(t, a, j, backups);
        assert(t[k as int] == advance(|x, w|cell(x, w), t[j as int], a[j as int]));
        assert forall|id: nat| #[trigger] t[k as int].pending.contains_key(id) && t[k as int].pending[id].input is Copy
            implies weak_payload(t[k as int].pending[id]) by {
            match a[j as int] {
                Action::Send(n, p) if n == id => {}, _ => { assert(t[j as int].pending.contains_key(id)); },
            }
        }
    }
}

pub open spec fn changed(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, j: nat) -> bool {
    exists|r: Replica| #[trigger] changes_quorum_value(t[j as int], a[j as int], r)
}

proof fn earliest_change(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat) -> (j: nat)
    requires changed(t, a, k), k<a.len(),
    ensures j <= k, changed(t, a, j), forall|h: nat| h<j ==> !#[trigger] changed(t, a, h),
    decreases k,
{
    if exists|h: nat| h<k && #[trigger] changed(t, a, h) {
        let h = choose|h: nat| h<k && #[trigger] changed(t, a, h);
        earliest_change(t, a, h)
    } else { k }
}

proof fn original_survivor_value(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, j: nat, r: Replica)
    requires trace(|x, w|cell(x, w), t, a), j <= a.len(), live_pair().contains(r),
        forall|h: nat| h<j ==> !#[trigger] changed(t, a, h),
    ensures (t[j as int].locals)(r) == (t[0].locals)(r),
    decreases j,
{
    if j>0 {
        let h = (j-1) as nat; original_survivor_value(t, a, h, r); assert(!changed(t, a, h));
        assert(!changes_quorum_value(t[h as int], a[h as int], r));
        assert(t[j as int] == advance(|x, w|cell(x, w), t[h as int], a[h as int]));
    }
}

pub open spec fn fresh_foreign_copy(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, j: nat, r: Replica) -> bool {
    live_pair().contains(r) && (forall|h: nat| h<j ==> !#[trigger] changed(t, a, h))
        && match a[j as int] {
            Action::Deliver(id) => {
                let n = t[j as int];
                let p = n.pending[id];
                n.pending.contains_key(id) && weak_payload(p) && p.to == at(r)
                    && (n.locals)(r) == (t[0].locals)(r)
                    && ((r == Replica::R1 && p.input == Wire::Copy(5)) || (r == Replica::R2 && p.input == Wire::Copy(2)))
                    && (t[j as int+1].locals)(r) == p.input->Copy_0
            }, _ => false,
        }
}

// An all-return necessity theorem on the actual split checkpoint, not
// just the one fair execution which chooses never to repair. The first
// effective installation either has independent ordinary provenance or
// is delivery of the other writer's data to a new surviving replica.
pub proof fn what_can_unblock_agreement(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int, backups: Map<Replica, OrdinaryBackup>)
    requires crate::service::response_path(resume_at(agreement_reader(true), first_events(World::Hybrid)), |s: Reader|s.returned,
        first_cut(World::Hybrid), delayed_slots(), t, a, v), data_sources(t, a, backups),
    ensures exists|j: nat, r: Replica| j<a.len() && #[trigger] changes_quorum_value(t[j as int], a[j as int], r)
        && (fresh_foreign_copy(t, a, j, r) || (a[j as int] is Local && backups.contains_key(r)
            && (t[j as int+1].locals)(r) == value_at(backups[r].log, backups[r].prefix))),
{
    let b = alpha(Notice::G);
    split_return_needs_application_input(t, a, v);
    let (k, r) = choose|k: int, r: Replica| 0 <= k<a.len() && #[trigger] changes_quorum_value(t[k], a[k], r);
    assert(changed(t, a, k as nat));
    let j = earliest_change(t, a, k as nat);
    let r = choose|r: Replica| #[trigger] changes_quorum_value(t[j as int], a[j as int], r);
    original_survivor_value(t, a, j, r); actual_disk_before_sr2(b, actions_to_crash(b).len(), r);
    authentic_weak_packets(t, a, j, backups);
    let n = t[j as int];
    let step = a[j as int];
    assert(t[j as int+1] == advance(|x, w|cell(x, w), n, step));
    match step {
        Action::Deliver(id) => {
            assert(n.pending.contains_key(id) && weak_payload(n.pending[id]));
            assert(fresh_foreign_copy(t, a, j, r));
        },
        Action::Local(_, Wire::Copy(x)) => { assert(!allowed(cut_store(b), Move::Apply(r))); },
        _ => {},
    }
}

// Retain the real queued notice, accept all ordinary bookkeeping, and
// leave recovery capability explicit. Without a restorable image, every
// first return must install a new weak copy. A genuine causal T wait
// also needs a feasible return; a deadlock alone has no attesting event.
pub proof fn response_needs_weak_install_without_ordinary_repair(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int)
    requires crate::service::response_path(resume_at(agreement_reader(true), first_events(World::Hybrid)), |s: Reader|s.returned,
        first_cut(World::Hybrid), delayed_slots(), t, a, v), data_sources(t, a, Map::empty()),
    ensures exists|j: nat, r: Replica| j<a.len() && #[trigger] fresh_foreign_copy(t, a, j, r),
{
    what_can_unblock_agreement(t, a, v, Map::empty());
}


pub open spec fn prior_data_offer(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat, id: nat, p: Packet<Wire>) -> bool {
    exists|h: nat| h<k && #[trigger] a[h as int] == Action::Send(id, p)
        && live(t[h as int], p.from) && (t[h as int].locals)(p.from->At_0) == p.input->Copy_0
}

proof fn queue_remembers_weak_sends(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat)
    requires t[0] == checkpoint_end(alpha(Notice::G)), data_sources(t, a, Map::empty()), trace(|x, w|cell(x, w), t, a), k <= a.len(),
    ensures t[k as int].r3_crashed,
        forall|id: nat| #[trigger] t[k as int].pending.contains_key(id) ==> {
            let p = t[k as int].pending[id];
            weak_payload(p) && live_pair().contains(p.to->At_0) ==>
                p.from != at(Replica::R3) && prior_data_offer(t, a, k, id, p)
        },
    decreases k,
{
    if k>0 {
        let j = (k-1) as nat; queue_remembers_weak_sends(t, a, j);
        let n = t[j as int];
        let step = a[j as int];
        let u = t[k as int];
        assert(enabled(n, step) && u == advance(|x, w|cell(x, w), n, step));
        assert forall|id: nat| #[trigger] u.pending.contains_key(id) implies {
            let p = u.pending[id]; weak_payload(p) && live_pair().contains(p.to->At_0)
                 ==> p.from != at(Replica::R3) && prior_data_offer(t, a, k, id, p)
        } by {
            let p = u.pending[id];
            if weak_payload(p) && live_pair().contains(p.to->At_0) {
                if step == Action::Send(id, p) {
                    assert(a[j as int] == Action::Send(id, p) && live(n, p.from) && (n.locals)(p.from->At_0) == p.input->Copy_0);
                } else {
                    assert(n.pending.contains_key(id) && n.pending[id] == p);
                    assert(prior_data_offer(t, a, j, id, p));
                    let h = choose|h: nat| h<j && #[trigger] a[h as int] == Action::Send(id, p)
                        && live(t[h as int], p.from) && (t[h as int].locals)(p.from->At_0) == p.input->Copy_0;
                    assert(a[h as int] == Action::Send(id, p));
                }
            }
        }
    }
}

// This is a necessity result about the equality guard. It does not
// require the construction to generate an extra packet. With only the
// original offers and no independent repair, this reader cannot return.
pub proof fn no_confirmation_alone_can_repair(t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int)
    requires crate::service::response_path(resume_at(agreement_reader(true), first_events(World::Hybrid)), |s: Reader|s.returned,
        first_cut(World::Hybrid), delayed_slots(), t, a, v), data_sources(t, a, Map::empty()),
    ensures exists|j: nat, r: Replica, id: nat| j<a.len() && #[trigger] fresh_foreign_copy(t, a, j, r)
        && a[j as int] == Action::Deliver(id) && #[trigger] prior_data_offer(t, a, j, id, t[j as int].pending[id])
        && live_pair().contains(t[j as int].pending[id].from->At_0),
{
    response_needs_weak_install_without_ordinary_repair(t, a, v);
    let (j, r) = choose|j: nat, r: Replica| j<a.len() && #[trigger] fresh_foreign_copy(t, a, j, r);
    queue_remembers_weak_sends(t, a, j);
    let id = a[j as int]->Deliver_0;
    assert(a[j as int] == Action::Deliver(id));
    assert(t[j as int].pending.contains_key(id));
    assert(prior_data_offer(t, a, j, id, t[j as int].pending[id]));
}


// Coherence at a shared ordinary position is an ordinary stock check. A
// CPU poll still runs when it fails, including on the off-stock inputs.
pub open spec fn checked_latest(m: Map<Replica, Stamp>) -> Option<int> {
    if consistent_versions(m) { crate::quorum_rpc::latest(m) } else { None }
}

pub proof fn stock_available_validator_separates_both_cuts(b: Fork)
    ensures ({
        let rho = |m|checked_latest(m);
        crate::stock_availability::read_a(crate::rpc_majority::rpc_stock(rho), |e|crate::quorum_rpc::fair(all_replicas(), e))
            && checked_latest(capture(b, 8).received).is_none() && pre_sr1_g(b, weak_assignment(b, true).ops)
    }),
{
    let rho = |m|checked_latest(m);
    assert forall|m: Map<Replica, Stamp>| majority(m.dom()) && consistent_versions(m) implies {
        let v = #[trigger] rho(m); v.is_some() && exists|r: Replica| #[trigger] m.contains_key(r) && v == Some(m[r].value)
    } by { crate::quorum_rpc::latest_is_a_sample(m); }
    crate::stock_reports::common_log_implies_consistency();
    crate::rpc_majority::any_majority_stock_read(rho);
    let p = crate::rpc_majority::rpc_stock(rho);
    crate::quorum_rpc::rpc_invariant(all_replicas(), rho);
    let t = seq![crate::quorum_rpc::initial()];
    let a = Seq::<crate::quorum_rpc::Rpc>::empty();
    assert(crate::stock_availability::path(p, t, a));
    assert(crate::stock_availability::reaches(p, t[0]));
    version_sensitive_stock_comparison_fails(b, p, |s: crate::quorum_rpc::Round|s.book,
        |s, a, t|crate::quorum_rpc::visible(a), t[0]);
}


// Project the *actual* fair alpha run, including R3's live-recipient
// confirmation. The sender's ordinary applied-write position is captured
// with each reply. CPU polls remain enabled when validation returns None.
pub open spec fn read_event_of(n: Network<int, Wire>, a: Action<Wire>) -> Option<Rpc> {
    match a {
        Action::Send(_, p) if p.to is At && p == query_packet(p.to->At_0) => Some(Rpc::Dispatch(p.to->At_0)),
        Action::Send(_, p) if p.from is At && report_from(p, p.from->At_0) => Some(Rpc::Reply(p.from->At_0)),
        Action::Deliver(id) if n.pending.contains_key(id) => {
            let p = n.pending[id];
            match p.input {
                Wire::Query2 if p.to is At && p == query_packet(p.to->At_0) => Some(Rpc::TakeRequest(p.to->At_0)),
                Wire::Answer2(_) if p.from is At && report_from(p, p.from->At_0) => Some(Rpc::TakeReply(p.from->At_0)),
                Wire::WeakConfirm(Notice::G) if p.to is At && notice_to(p, p.to) => Some(Rpc::Tick(p.to->At_0)),
                _ => None,
            }
        },
        Action::Strong(Process::At(r)) => Some(Rpc::Tick(r)),
        Action::ClientInput(Process::SecondClient, Wire::Peer(v)) if v == 0 => Some(Rpc::Poll),
        _ => None,
    }
}

pub open spec fn same_report_slots(n: Network<int, Wire>, s: Evidence) -> bool {
    forall|id: nat| {
        let packet = n.pending[id];
        let has = n.pending.contains_key(id) && packet.from is At && report_from(packet, packet.from->At_0);
        let recorded = #[trigger] s.packets.contains_key(id);
        has == recorded && (recorded ==> s.packets[id].from == packet.from->At_0
            && s.packets[id].data.value == packet.input->Answer2_0.value)
    }
}

pub open spec fn instrumented_alpha(k: nat) -> Round {
    let b = alpha(Notice::G);
    let phase = if k <= 4 { k } else if k <= 9 { (k-1) as nat } else { 8 };
    let s = actual_tags(b, phase);
    Round { book: s, live: live_pair(), started: true, returned: None, stage: |r| match r {
        Replica::R1 => if k == 0 { 0 } else if k<3 { 1 } else if k<6 { 2 } else if k<8 { 3 } else { 4 },
        Replica::R2 => if k<2 { 0 } else if k<4 { 1 } else if k<7 { 2 } else if k<9 { 3 } else { 4 },
        Replica::R3 => 0,
    } }
}

pub open spec fn validation_run() -> Stream<Round, Rpc> {
    let h = crate::quorum_progress::service_run(World::Hybrid, true);
    Stream { state: |i|instrumented_alpha(i), event: |i|read_event_of((h.state)(i), (h.action)(i)).unwrap() }
}

spec fn alpha_service_event(i: nat) -> Rpc {
    match i {
        _ if i == 0 => Rpc::Dispatch(Replica::R1), _ if i == 1 => Rpc::Dispatch(Replica::R2),
        _ if i == 2 => Rpc::TakeRequest(Replica::R1), _ if i == 3 => Rpc::TakeRequest(Replica::R2),
        _ if i == 4 => Rpc::Tick(Replica::R2),
        _ if i == 5 => Rpc::Reply(Replica::R1), _ if i == 6 => Rpc::Reply(Replica::R2),
        _ if i == 7 => Rpc::TakeReply(Replica::R1), _ if i == 8 => Rpc::TakeReply(Replica::R2),
        _ if i%3 == 0 => Rpc::Tick(Replica::R1), _ if i%3 == 1 => Rpc::Tick(Replica::R2), _ => Rpc::Poll,
    }
}

proof fn physical_report_projection(i: nat)
    ensures ({
        let e = validation_run();
        let h = crate::quorum_progress::service_run(World::Hybrid, true);
        read_event_of((h.state)(i), (h.action)(i)) == Some(alpha_service_event(i))
            && (e.event)(i) == alpha_service_event(i) && same_report_slots((h.state)(i), (e.state)(i).book)
    }),
{
    let e = validation_run();
    let h = crate::quorum_progress::service_run(World::Hybrid, true);
    let n = (h.state)(i);
    let book = (e.state)(i).book;
    actual_disk_before_sr2(alpha(Notice::G), 17, Replica::R1); actual_disk_before_sr2(alpha(Notice::G), 17, Replica::R2);
    if i<9 { prefix_index(i as int); }
    assert forall|id: nat| n.pending.contains_key(id) && n.pending[id].input is Answer2 implies
        #[trigger] book.packets.contains_key(id) by { assert(id == 13 || id == 14); }
}

proof fn validator_steps()
    ensures availability::follows_stock(crate::rpc_majority::rpc_stock(|m|checked_latest(m)), validation_run()),
{
    hide(read_event_of); hide(same_report_slots);
    let rho = |m|checked_latest(m);
    let p = crate::rpc_majority::rpc_stock(rho);
    let e = validation_run();
    let b = alpha(Notice::G);
    stock_available_validator_separates_both_cuts(b); tags_are_actual(b, 8);
    assert forall|i: nat| (p.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i+1)) by {
        physical_report_projection(i);
        if i<9 { prefix_index(i as int); }
        let s = (e.state)(i);
        let a = (e.event)(i);
        let t = (e.state)(i+1);
        let u = qr::advance_round(rho, s, a);
        assert(qr::enabled(s, all_replicas(), a));
        assert(u.stage =~= t.stage);
        assert(u.book.packets =~= t.book.packets); assert(u.book.received =~= t.book.received);
    }
}

proof fn validator_fairness()
    ensures qr::fair(all_replicas(), validation_run()),
{
    hide(read_event_of); hide(same_report_slots);
    let e = validation_run();
    let b = alpha(Notice::G);
    assert forall|i: nat| #[trigger] (e.event)(i) == alpha_service_event(i) by { physical_report_projection(i); }
    assert forall|i: nat, r: Replica| #[trigger] qr::stage_served(all_replicas(), e, i, r) by {
        let n = ((e.state)(i).stage)(r);
        if n<4 {
            let j = match r {
                Replica::R1 => if n == 0 { 0 } else if n == 1 { 2 } else if n == 2 { 5 } else { 7 },
                Replica::R2 => if n == 0 { 1 } else if n == 1 { 3 } else if n == 2 { 6 } else { 8 },
                Replica::R3 => i,
            };
            assert(j >= i && ((e.event)(j) == qr::expected(r, n) || (n != 3 && !(e.state)(j).live.contains(r))));
        }
    }
    assert forall|i: nat| #[trigger] qr::poll_after(e, i) by {
        let j = 3*(i+10)+2; assert(j%3 == 2); assert((e.event)(j) == Rpc::Poll);
    }
    assert forall|i: nat, r: Replica| #[trigger] qr::tick_after(e, i, r) by {
        let off: nat = if r == Replica::R1 { 0 } else { 1 };
        let j = 3*(i+10)+off;
        assert(j%3 == off); assert(j >= i && ((e.event)(j) == Rpc::Tick(r) || !(e.state)(j).live.contains(r)));
    }
    assert forall|i: nat, r: Replica| #[trigger] qr::apply_debt_served(e, i, r) by { actual_disk_before_sr2(b, 17, r); }
}

pub proof fn validator_on_actual_fair_alpha()
    ensures ({
        let rho = |m|checked_latest(m);
        let p = crate::rpc_majority::rpc_stock(rho);
        let e = validation_run();
        let h = crate::quorum_progress::service_run(World::Hybrid, true);
        let b = alpha(Notice::G);
        availability::read_a(p, |u|qr::fair(all_replicas(), u))
            && availability::follows_stock(p, e) && qr::fair(all_replicas(), e) && qr::at_invocation((e.state)(0))
            && !availability::reaches(p, (e.state)(0))
            && (forall|i: nat| (#[trigger] (e.state)(i)).returned.is_none()
                && read_event_of((h.state)(i), (h.action)(i)) == Some((e.event)(i))
                && same_report_slots((h.state)(i), (e.state)(i).book))
            && crate::progress::delivery_fair(h) && crate::progress::process_fair(h, |n, p|live(n, p))
            && (h.action)(4) == Action::Deliver(2) && crate::quorum_progress::local_after(World::Hybrid, true, at(Replica::R2), 9).prior.learned == Some(Notice::G)
            && (e.state)(9).book.received == capture(b, 8).received
            && pre_sr1_g(b, weak_assignment(b, true).ops)
    }),
{
    let rho = |m|checked_latest(m);
    let p = crate::rpc_majority::rpc_stock(rho);
    let e = validation_run();
    let b = alpha(Notice::G);
    let h = crate::quorum_progress::service_run(World::Hybrid, true);
    crate::quorum_progress::fair_quorum_progress_boundary(World::Hybrid, true);
    assert((|n, p|live(n, p)) =~= (|n: Network<int, Wire>, p|crate::quorum_progress::live_process(n, p)));
    stock_available_validator_separates_both_cuts(b); tags_are_actual(b, 8);
    assert forall|r: Replica| {
        let d = #[trigger] (cut_store(b).disk)(r); d.known == 0 && d.applied == 0 && d.value == (checkpoint_end(b).locals)(r)
    } by { actual_disk_before_sr2(b, 17, r); }
    if availability::reaches(p, (e.state)(0)) {
        qr::rpc_invariant(all_replicas(), rho); availability::reachable_invariant(p, |s|qr::normal(s), (e.state)(0));
        assert(authentic(cut_store(b).log, sample(cut_store(b), Replica::R1)));
    }
    validator_steps();
    validator_fairness();
    assert forall|i: nat| (#[trigger] (e.state)(i)).returned.is_none()
        && read_event_of((h.state)(i), (h.action)(i)) == Some((e.event)(i))
        && same_report_slots((h.state)(i), (e.state)(i).book) by { physical_report_projection(i); }

}

}
