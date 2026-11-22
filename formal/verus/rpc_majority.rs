use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::all_replicas;
use crate::ordered_store::*;
use crate::quorum_rpc::*;
use crate::stock_availability::*;
use crate::stock_reports::*;

verus! {

// This instantiation can address any replica. A finite service witness for
// a chosen majority actually dispatches only to that majority.
pub open spec fn rpc_stock(rho: Resolver) -> ReadSystem<Round, Rpc> { rpc(all_replicas(), rho) }

pub open spec fn total_sample(rho: Resolver) -> bool {
    forall|m: Map<Replica, Stamp>| majority(m.dom()) && has_log(m) ==> {
        let v = #[trigger] rho(m);
        v.is_some() && exists|r: Replica| #[trigger] m.contains_key(r) && v == Some(m[r].value)
    }
}

pub open spec fn survivors(e: Stream<Round, Rpc>) -> Set<Replica> {
    all_replicas().filter(|r: Replica| forall|i: nat| (#[trigger] (e.state)(i)).live.contains(r))
}

proof fn permanent_quorum(rho: Resolver, e: Stream<Round, Rpc>)
    requires follows_stock(rpc_stock(rho), e), forall|i: nat| majority((#[trigger] (e.state)(i)).live),
    ensures majority(survivors(e)),
{
    let gone = |r: Replica| if survivors(e).contains(r) { 0 } else { choose|k: nat| !(#[trigger] (e.state)(k)).live.contains(r) };
    let j = gone(Replica::R1)+gone(Replica::R2)+gone(Replica::R3);
    assert forall|r: Replica| (e.state)(j).live.contains(r) implies #[trigger] survivors(e).contains(r) by {
        if !survivors(e).contains(r) {
            assert(gone(r) <= j); assert(!(e.state)(gone(r)).live.contains(r));
            stages_persist(all_replicas(), rho, e, r, gone(r), j);
        }
    }
    assert(majority((e.state)(j).live));
}

// Any majority with persistent availability is enough. Its membership need
// not be known in advance, even on a run with a later crash.
proof fn stock_eventual(rho: Resolver)
    requires total_sample(rho),
    ensures eventual(rpc_stock(rho), |e| fair(all_replicas(), e)),
{
    let p = rpc_stock(rho);
    assert forall|e: Stream<Round, Rpc>| #[trigger] follows_stock(p, e) && fair(all_replicas(), e) && reaches(p, (e.state)(0))
        && (p.invoked)((e.state)(0)) && (p.response)((e.state)(0)).is_none()
        && (forall|i: nat| (p.client_live)(#[trigger] (e.state)(i)) && majority((p.up)((e.state)(i))))
        implies exists|k: nat| (p.response)(#[trigger] (e.state)(k)).is_some() by {
        permanent_quorum(rho, e);
        let q = survivors(e);
        assert forall|i: nat| q.subset_of(#[trigger] (e.state)(i).live) by {};
        fair_read_with_actual_majority(all_replicas(), rho, e, q);
    }
}

pub open spec fn served_count(r: Replica, k: nat, q: Set<Replica>) -> nat {
    let site_index = match r { Replica::R1 => 0nat, Replica::R2 => 1nat, Replica::R3 => 2nat };
    if !q.contains(r) || k <= site_index { 0 }
    else if k <= 3 + site_index { 1 } else if k <= 6 + site_index { 2 }
    else if k <= 9 + site_index { 3 } else { 4 }
}

pub open spec fn actual_rows(s: Store, q: Set<Replica>) -> Map<Replica, Stamp> {
    Map::new(q, |r| sample(s, r))
}

pub open spec fn site(id: nat) -> Replica {
    if id == slot(Replica::R1) { Replica::R1 } else if id == slot(Replica::R2) { Replica::R2 } else { Replica::R3 }
}

// First issue the initial copies to Q, then accept them, send the sampled
// replies and deliver them. Empty slots are CPU steps on a live member.
pub open spec fn serve_a_quorum(q: Set<Replica>, k: nat) -> Rpc {
    let r = if k % 3 == 0 { Replica::R1 } else if k % 3 == 1 { Replica::R2 } else { Replica::R3 };
    if k >= 12 { Rpc::Poll } else if q.contains(r) { expected(r, k / 3) }
    else { Rpc::Tick(if q.contains(Replica::R1) { Replica::R1 } else { Replica::R2 }) }
}

pub open spec fn initial_requests_to(a: Seq<Rpc>, q: Set<Replica>) -> bool {
    forall|i:int| 0 <= i < a.len() ==> match #[trigger] a[i] {
        Rpc::Dispatch(r) => q.contains(r) && forall|j:int| 0 <= j < i ==> !(#[trigger] a[j] is TakeReply),
        _ => true,
    }
}

pub open spec fn during_service(x: Round, rho: Resolver, q: Set<Replica>, k: nat) -> Round {
    let s = x.book.store;
    let packets = Map::new(set![slot(Replica::R1), slot(Replica::R2), slot(Replica::R3)].filter(|id: nat| served_count(site(id), k, q) == 3),
        |id| Answer { from: site(id), data: sample(s, site(id)) });
    let got = all_replicas().filter(|r| served_count(r, k, q) == 4);
    Round { book: Evidence { store: s, packets, received: actual_rows(s, got) }, stage: |r|served_count(r, k, q),
        returned: if k >= 13 { rho(actual_rows(s, q)) } else { None }, ..x }
}

pub(crate) proof fn quorum_service_step(rho: Resolver, x: Round, q: Set<Replica>, i: nat)
    requires i < 13, at_invocation(x), majority(q), q.subset_of(x.live),
    ensures (rpc_stock(rho).next)(during_service(x, rho, q, i), serve_a_quorum(q, i), during_service(x, rho, q, i+1)),
{
    crate::checkpoint::prefix_index(i as int);
    let s = during_service(x, rho, q, i);
    let a = serve_a_quorum(q, i);
    let t = during_service(x, rho, q, i+1);
    let u = advance_round(rho, s, a);
    assert(enabled(s, all_replicas(), a));
    assert(t.stage =~= u.stage);
    assert(t.book.packets =~= u.book.packets);
    assert(t.book.received =~= u.book.received);
    if i == 12 { assert(s.book.received =~= actual_rows(x.book.store, q)); }
}

pub proof fn any_majority_can_serve(rho: Resolver, x: Round, q: Set<Replica>)
    requires total_sample(rho), reaches(rpc_stock(rho), x), at_invocation(x), majority(q), q.subset_of(x.live),
    ensures exists|t: Seq<Round>, a: Seq<Rpc>, v: int| #[trigger] quorum_witness(rpc_stock(rho), x, q, t, a, v),
        exists|t:Seq<Round>, a:Seq<Rpc>, v:int| #[trigger] quorum_witness(rpc_stock(rho),x,q,t,a,v)
            && initial_requests_to(a,q) && t.last().book.received.dom()==q,
{
    let p = rpc_stock(rho); rpc_invariant(all_replicas(), rho); reachable_invariant(p, |s|normal(s), x);
    let a = Seq::new(13, |i: int|serve_a_quorum(q, i as nat));
    let t = Seq::new(14, |i: int|during_service(x, rho, q, i as nat));
    let rows = actual_rows(x.book.store, q);
    assert(from_log(x.book.store.log, rows)) by {
        assert forall|r: Replica| #[trigger] rows.contains_key(r) implies authentic(x.book.store.log, rows[r])
            by { assert((x.book.store.disk)(r).value == value_at(x.book.store.log, rows[r].version)); }
    }
    assert(has_log(rows));
    assert(rho(rows).is_some());
    assert(t[0].stage =~= x.stage); assert(t[0].book.packets =~= x.book.packets); assert(t[0].book.received =~= x.book.received);
    assert(t[12].book.received =~= rows);
    assert forall|i: int| 0 <= i < a.len() implies (p.next)(t[i], #[trigger] a[i], t[i+1]) by {
        quorum_service_step(rho, x, q, i as nat);
    }
    assert(initial_requests_to(a, q)) by {
        assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
            Rpc::Dispatch(r) => q.contains(r) && forall|j: int| 0 <= j < i ==> !(#[trigger] a[j] is TakeReply),
            _ => true,
        } by { crate::checkpoint::prefix_index(i); }
    }
    assert(t.last().book.received.dom() =~= q);
    let v = rho(rows).unwrap();
    let r = choose|r: Replica| #[trigger] rows.contains_key(r) && rho(rows) == Some(rows[r].value);
    assert((p.value)(t[0], r) == v);
    assert(quorum_witness(p, x, q, t, a, v));
}

pub open spec fn earlier_sample(t: Seq<Round>, k: nat, r: Replica, d: Stamp) -> bool {
    exists|j: int| 0 <= j<k && #[trigger] sample(t[j].book.store, r) == d
}

// Every answer actually used by this client can be traced back to a send
// inside its own read interval, even across concurrent log decisions or a
// sender crash. Initial emptiness here is the fresh operation's mailbox.
pub(crate) proof fn source_of_reports(rho: Resolver, t: Seq<Round>, a: Seq<Rpc>, k: nat)
    requires path(rpc_stock(rho), t, a), at_invocation(t[0]), k <= a.len(),
    ensures ({
        let s = t[k as int];
        (forall|r: Replica| #[trigger] s.book.received.contains_key(r) ==> earlier_sample(t, k, r, s.book.received[r]))
        && (forall|id: nat| #[trigger] s.book.packets.contains_key(id) ==>
            earlier_sample(t, k, s.book.packets[id].from, s.book.packets[id].data))
    }),
    decreases k,
{
    if k>0 {
        let j = (k-1) as nat;
        let s = t[j as int];
        let u = t[k as int];
        let ev = a[j as int];
        source_of_reports(rho, t, a, j);
        assert((rpc_stock(rho).next)(s, ev, u));
        assert forall|r: Replica, d: Stamp| #[trigger] earlier_sample(t, j, r, d) implies earlier_sample(t, k, r, d) by {
            let h = choose|h: int| 0 <= h<j && #[trigger] sample(t[h].book.store, r) == d;
            assert(sample(t[h].book.store, r) == d);
        }
        assert forall|id: nat| #[trigger] u.book.packets.contains_key(id) implies
            earlier_sample(t, k, u.book.packets[id].from, u.book.packets[id].data) by {
            match ev {
                Rpc::Reply(r) if slot(r) == id => { assert(sample(t[j as int].book.store, r) == u.book.packets[id].data); },
                _ => { assert(s.book.packets.contains_key(id)); },
            }
        }
        assert forall|r: Replica| #[trigger] u.book.received.contains_key(r) implies earlier_sample(t, k, r, u.book.received[r]) by {
            if let Rpc::TakeReply(peer) = ev { assert(s.book.packets.contains_key(slot(peer))); }
        }
    }
}

proof fn one_interval_sample(rho: Resolver, t: Seq<Round>, a: Seq<Rpc>, q: Set<Replica>, v: int)
    requires total_sample(rho), first_answer(rpc_stock(rho), t, a, v), reaches(rpc_stock(rho), t[0]),
        (rpc_stock(rho).invoked)(t[0]), majority(q), (rpc_stock(rho).served_by)(t, a, q),
    ensures member_during(rpc_stock(rho), t, q, v),
{
    hide(normal); hide(consistent); hide(earlier_sample);
    let p = rpc_stock(rho); rpc_invariant(all_replicas(), rho);
    assert(a.len()>0);
    let j = (a.len()-1) as nat;
    let s = t[j as int];
    assert((p.next)(s, a[j as int], t.last()) && s.returned.is_none());
    assert(a[j as int] == Rpc::Poll && rho(s.book.received) == Some(v));
    reachable_invariant(p, |x|normal(x), t[0]);
    crate::stock_availability::invariant_on_path(p, |x|normal(x), t, a, j);
    let rows = s.book.received;
    assert(from_log(s.book.store.log, rows)) by { reveal(normal); }
    assert(has_log(rows));
    let r = choose|r: Replica| #[trigger] rows.contains_key(r) && rho(rows) == Some(rows[r].value);
    source_of_reports(rho, t, a, j); assert(earlier_sample(t, j, r, rows[r]));
    reveal(earlier_sample);
    let h = choose|h: int| 0 <= h<j && #[trigger] sample(t[h].book.store, r) == rows[r];
    assert(q.contains(r) && (p.value)(t[h], r) == v);
}

proof fn stock_interval_valid(rho: Resolver)
    requires total_sample(rho),
    ensures valid_samples(rpc_stock(rho)),
{
    hide(reaches); hide(total_sample); hide(rpc); hide(member_during); hide(rpc_stock);
    let p = rpc_stock(rho);
    assert forall|t: Seq<Round>, a: Seq<Rpc>, q: Set<Replica>, v: int| #[trigger] first_answer(p, t, a, v)
        && reaches(p, t[0]) && (p.invoked)(t[0]) && majority(q) && #[trigger] (p.served_by)(t, a, q)
        implies member_during(p, t, q, v) by {
        one_interval_sample(rho, t, a, q, v);
    }
}

pub proof fn any_majority_stock_read(rho: Resolver)
    requires total_sample(rho),
    ensures read_a(rpc_stock(rho), |e| fair(all_replicas(), e)),
{
    let p = rpc_stock(rho);
    stock_eventual(rho); rpc_invariant(all_replicas(), rho);
    assert forall|x: Round, q: Set<Replica>| #[trigger] reaches(p, x) && #[trigger] majority(q) && q.subset_of((p.up)(x))
        && (p.client_live)(x) && (p.invoked)(x) && (p.response)(x).is_none()
        implies exists|t: Seq<Round>, a: Seq<Rpc>, v: int| #[trigger] quorum_witness(p, x, q, t, a, v) by {
        any_majority_can_serve(rho, x, q);
    }
    stock_interval_valid(rho);
}

pub proof fn latest_serves_any_actual_majority()
    ensures read_a(rpc_stock(|m| latest(m)), |e| fair(all_replicas(), e)),
{
    let rho = |m| latest(m);
    common_log_implies_consistency();
    assert forall|m: Map<Replica, Stamp>| majority(m.dom()) && consistent_versions(m) implies {
        let v = #[trigger] rho(m); v.is_some() && exists|r: Replica| #[trigger] m.contains_key(r) && v == Some(m[r].value)
    } by { latest_is_a_sample(m); }
    any_majority_stock_read(rho);
}


// A stock implementation can release an ordinary command's result after
// a majority have applied through its position. This is a condition on
// publishing a command response, separate from deciding or copying it.
pub open spec fn applied_majority(s: Store, k: nat) -> Set<Replica> {
    all_replicas().filter(|r: Replica| (s.disk)(r).applied >= k)
}

pub open spec fn can_answer_command(s: Store, slot: nat, old: int) -> bool {
    slot<s.log.len() && majority(applied_majority(s, slot+1)) && old == command_return(s.log, slot)
}

proof fn applied_cursor_persists(rho: Resolver, t: Seq<Round>, a: Seq<Rpc>, j: nat, r: Replica)
    requires path(rpc_stock(rho), t, a), j <= a.len(),
    ensures (t[0].book.store.disk)(r).applied <= (t[j as int].book.store.disk)(r).applied,
    decreases j,
{
    if j>0 {
        let h = (j-1) as nat; applied_cursor_persists(rho, t, a, h, r);
        assert((rpc_stock(rho).next)(t[h as int], a[h as int], t[j as int]));
    }
}

pub open spec fn resolves_latest(rho: Resolver, l: Seq<Command>, m: Map<Replica, Stamp>) -> bool {
    majority(m.dom()) && (forall|r: Replica| #[trigger] m.contains_key(r) ==> authentic(l, m[r])) ==> rho(m) == latest(m)
}

// Quorum intersection is with a member that really sent a report within
// this invocation. Other voters may have crashed or be behind. This
// lemma concerns one read relative to the ordinary command sequence.
pub proof fn latest_covers_prior_publication(rho: Resolver, t: Seq<Round>, a: Seq<Rpc>, k: nat, v: int)
    requires reaches(rpc_stock(rho), t[0]), at_invocation(t[0]), first_answer(rpc_stock(rho), t, a, v),
        majority(applied_majority(t[0].book.store, k)),
        forall|l: Seq<Command>, m: Map<Replica, Stamp>| #[trigger] resolves_latest(rho, l, m),
    ensures exists|h: nat| k <= h <= t.last().book.store.log.len() && #[trigger] value_at(t.last().book.store.log, h) == v,
{
    let p = rpc_stock(rho); rpc_invariant(all_replicas(), rho);
    assert(a.len()>0); let j = (a.len()-1) as nat; let s = t[j as int]; let rows = s.book.received;
    assert((p.next)(s, a[j as int], t.last()) && s.returned.is_none());
    assert(a[j as int] == Rpc::Poll && majority(rows.dom()) && rho(rows) == Some(v));
    reachable_invariant(p, |x|normal(x), t[0]); crate::stock_availability::invariant_on_path(p, |x|normal(x), t, a, j);
    let l = s.book.store.log;
    assert forall|r: Replica| #[trigger] rows.contains_key(r) implies authentic(l, rows[r]) by {};
    assert(resolves_latest(rho, l, rows)); assert(rho(rows) == latest(rows)); latest_is_a_sample(rows);
    let q = applied_majority(t[0].book.store, k);
    let r = if q.contains(Replica::R1) && rows.contains_key(Replica::R1) { Replica::R1 }
        else if q.contains(Replica::R2) && rows.contains_key(Replica::R2) { Replica::R2 } else { Replica::R3 };
    assert(q.contains(r) && rows.contains_key(r));
    source_of_reports(rho, t, a, j); assert(earlier_sample(t, j, r, rows[r]));
    let z = choose|z: int| 0 <= z<j && #[trigger] sample(t[z].book.store, r) == rows[r];
    applied_cursor_persists(rho, t, a, z as nat, r);
    let h = rows[latest_site(rows)].version;
    assert(h >= rows[r].version >= k);
    assert(authentic(l, rows[latest_site(rows)]));
    assert(value_at(t.last().book.store.log, h) == v);
}

}
