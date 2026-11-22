use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{Action, Network, Packet, Process, observations, trace, advance};
use crate::protocol::{accepted,memory};
use crate::ordered_store::*;
use crate::quorum_rpc::*;
use crate::stock_availability::*;
use crate::stock_reports::*;

verus! {

pub open spec fn pair() -> Set<Replica> { set![Replica::R1, Replica::R2] }

pub open spec fn before_read(s: Store) -> Round { Round { book: empty_evidence(s), ..initial() } }

// Lift an actual stock storage prefix into the service. R3 crashes once,
// after the storage history. The fresh client can now invoke the read.
pub proof fn invoke_after_stock_prefix(menu: Set<Replica>, rho: Resolver, s: Store)
    requires reachable(s),
    ensures reaches(rpc(menu, rho), Round { started: true, live: pair(), ..before_read(s) }),
{
    let (u, b) = choose|u: Seq<Store>, b: Seq<Move>| #[trigger] history(u, b) && u.last() == s;
    let a = Seq::new(b.len()+2, |i: int| if i<b.len() { Rpc::Storage(b[i]) }
        else if i == b.len() { Rpc::Crash(Replica::R3) } else { Rpc::Begin });
    let t = Seq::new(a.len()+1, |i: int| if i<u.len() { before_read(u[i]) }
        else { Round { started: i == a.len(), live: pair(), ..before_read(s) } });
    let p = rpc(menu, rho);
    assert(all_replicas().remove(Replica::R3) =~= pair());
    assert forall|i: int| 0 <= i<a.len() implies (p.next)(t[i], #[trigger] a[i], t[i+1]) by {
        if i<b.len() {
            assert(allowed(u[i], b[i]) && u[i+1] == step(u[i], b[i]));
            if let Move::Decide(_, q) = b[i] { assert(q.subset_of(all_replicas())); }
        }
        assert(t[i+1].stage =~= advance_round(rho, t[i], a[i]).stage);
    }
    assert(path(p, t, a));
}

// Insert an ordinary SR1 at the mixed stock cut. The finite read does
// not apply further log entries. C1 uses R2/R3 and leaves R1's real reply
// queued after it stops. The next client has no access to that reply.
pub open spec fn stock_first_cut(k: nat) -> Network<int, Wire> {
    let b = alpha(Notice::G);
    let n = state_after(b, k+2);
    Network { locals: |r|(split_stock().disk)(r).value,
        pending: Map::new(n.pending.dom().filter(|id: nat| id >= 3), |id|n.pending[id]), ..n }
}

pub open spec fn stock_first_prefix() -> Seq<Action<Wire>> { actions_to_crash(alpha(Notice::G)).skip(2) }
pub open spec fn stock_first_trace() -> Seq<Network<int, Wire>> { Seq::new(16, |i: int|stock_first_cut(i as nat)) }

proof fn mixed_first_memory(p: Process, k: nat)
    requires k <= 15,
    ensures memory(checkpoint_machine(), p, observations(stock_first_trace(), stock_first_prefix()), k)
         == (Control { weak_copy: None, ..expected_control(alpha(Notice::G), p, k+2) }),
    decreases k,
{
    if k>0 { mixed_first_memory(p, (k-1) as nat); prefix_index(k as int-1); }
}

pub proof fn stock_first_read_at_mixed_cut()
    ensures ({
        let b = alpha(Notice::G);
        let a = stock_first_prefix();
        let t = stock_first_trace();
        let ev = observations(t, a);
        trace(|x, w|cell(x, w), t, a) && accepted(checkpoint_machine(), ev)
            && ev == checkpoint_observations(b).skip(2)
            && t[0].pending == Map::<nat, Packet<Wire>>::empty()
            && memory(checkpoint_machine(), Process::FirstClient, ev, 15).finished
            && memory(checkpoint_machine(), Process::FirstClient, ev, 15).reply == Some(5)
            && t[15].pending.dom() == set![6nat] && t[15].pending[6].to == Process::FirstClient && t[15].first_stopped
            && t[15].r3_crashed && t[15].second_started
            && (forall|p: Process| p != at(Replica::R3) ==>
                #[trigger] memory(checkpoint_machine(), p, ev, 15) == checkpoint_control(b, p))
    }),
{
    reachable_mixed_stock(); let b = alpha(Notice::G); let a = stock_first_prefix(); let t = stock_first_trace(); let ev = observations(t, a);
    assert forall|i: int| 0 <= i<a.len() implies {
        let action = #[trigger] a[i]; crate::delivery::enabled(t[i], action) && t[i+1] == advance(|x, w|cell(x, w), t[i], action)
    } by {
        prefix_index(i); let u = advance(|x, w|cell(x, w), t[i], a[i]);
        assert(u.locals =~= t[i+1].locals); assert(u.pending =~= t[i+1].pending);
    }
    assert(ev =~= checkpoint_observations(b).skip(2)) by {
        assert forall|i: int| 0 <= i<ev.len() implies #[trigger] ev[i] == checkpoint_observations(b)[i+2] by { prefix_index(i); }
    }
    assert forall|i: int| 0 <= i<ev.len() implies {
        let e = #[trigger] ev[i]; (checkpoint_machine().accept)(memory(checkpoint_machine(), e.actor, ev, i as nat), e)
    } by { mixed_first_memory(ev[i].actor, i as nat); prefix_index(i); }
    mixed_first_memory(Process::FirstClient, 15);
    assert(t[0].pending =~= Map::<nat, Packet<Wire>>::empty());
    assert(t[15].pending.dom() =~= set![6nat]);
    assert forall|p: Process| p != at(Replica::R3) implies
        #[trigger] memory(checkpoint_machine(), p, ev, 15) == checkpoint_control(b, p) by {
        mixed_first_memory(p, 15); prefix_memory_tracks_actual_messages(b, p, 17);
    }
}

pub open spec fn increments_applied(early: bool, k: nat) -> nat {
    let start: nat = if early { 4 } else { 9 };
    if k <= start { 0 } else if k >= start+3 { 3 } else { (k-start) as nat }
}

pub open spec fn mixed_store(early: bool, k: nat) -> Store {
    let s = split_stock();
    let n = increments_applied(early, k);
    Store { disk: |r| if r == Replica::R1 { Disk { known: 4, applied: 1+n, value: 2+n as int } } else { (s.disk)(r) }, ..s }
}

pub open spec fn row(early: bool, r: Replica) -> Stamp {
    if r == Replica::R1 && !early { Stamp { version: 1, value: 2 } } else { Stamp { version: 4, value: 5 } }
}

pub open spec fn two_rows(early: bool) -> Map<Replica, Stamp> {
    Map::empty().insert(Replica::R1, row(early, Replica::R1)).insert(Replica::R2, row(early, Replica::R2))
}

pub open spec fn stage_at(k: nat, r: Replica) -> nat {
    match r {
        Replica::R1 => if k == 0 { 0 } else if k <= 2 { 1 } else if k <= 7 { 2 } else if k <= 12 { 3 } else { 4 },
        Replica::R2 => if k <= 1 { 0 } else if k <= 3 { 1 } else if k <= 8 { 2 } else if k <= 13 { 3 } else { 4 },
        Replica::R3 => 0,
    }
}

pub open spec fn mixed_round(rho: Resolver, early: bool, k: nat) -> Round {
    let r1 = Replica::R1;
    let r2 = Replica::R2;
    let p = if 8 <= k<13 { Map::empty().insert(slot(r1), Answer { from: r1, data: row(early, r1) }) } else { Map::empty() };
    let packets = if 9 <= k<14 { p.insert(slot(r2), Answer { from: r2, data: row(early, r2) }) } else { p };
    let one = if k >= 13 { Map::empty().insert(r1, row(early, r1)) } else { Map::empty() };
    let received = if k >= 14 { one.insert(r2, row(early, r2)) } else { one };
    Round { book: Evidence { store: mixed_store(early, k), packets, received }, stage: |r| stage_at(k, r),
        live: pair(), started: true, returned: if k >= 15 { rho(two_rows(early)) } else { None } }
}

// Only R1/R2 serve this particular read. Catch-up is local application of an
// already decided log in both schedules. A reply in flight is immutable.
pub open spec fn mixed_event(early: bool, k: nat) -> Rpc {
    let r1 = Replica::R1;
    let r2 = Replica::R2;
    if k == 0 { Rpc::Dispatch(r1) } else if k == 1 { Rpc::Dispatch(r2) }
    else if k == 2 { Rpc::TakeRequest(r1) } else if k == 3 { Rpc::TakeRequest(r2) }
    else if k<7 { if early { Rpc::Storage(Move::Apply(r1)) } else { Rpc::Tick(r1) } }
    else if k == 7 { Rpc::Reply(r1) } else if k == 8 { Rpc::Reply(r2) }
    else if k<12 { if early { Rpc::Tick(r1) } else { Rpc::Storage(Move::Apply(r1)) } }
    else if k == 12 { Rpc::TakeReply(r1) } else if k == 13 { Rpc::TakeReply(r2) }
    else if k%3 == 2 { Rpc::Poll } else if k%3 == 0 { Rpc::Tick(r1) } else { Rpc::Tick(r2) }
}

pub open spec fn comparison(rho: Resolver, early: bool) -> Stream<Round, Rpc> {
    Stream { state: |k| mixed_round(rho, early, k), event: |k| mixed_event(early, k) }
}

proof fn follow_mixed(menu: Set<Replica>, rho: Resolver, early: bool)
    requires pair().subset_of(menu),
    ensures follows_stock(rpc(menu, rho), comparison(rho, early)),
{
    let e = comparison(rho, early);
    let p = rpc(menu, rho);
    assert forall|i: nat| (p.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i+1)) by {
        if i<15 { crate::checkpoint::prefix_index(i as int); }
        let s = (e.state)(i);
        let a = (e.event)(i);
        let t = (e.state)(i+1);
        let next = advance_round(rho, s, a);
        if let Rpc::Storage(Move::Apply(r)) = a {
            assert(s.book.store.log[(s.book.store.disk)(r).applied as int] == Command::Increment);
        }
        assert(enabled(s, menu, a));
        assert(t.stage =~= next.stage);
        assert(t.book.store.disk =~= next.book.store.disk);
        assert(t.book.received =~= next.book.received);
        assert(t.book.packets =~= next.book.packets);
    }
}

proof fn fair_mixed(menu: Set<Replica>, rho: Resolver, early: bool)
    ensures fair(menu, comparison(rho, early)),
{
    let e = comparison(rho, early);
    assert forall|i: nat, r: Replica| #[trigger] stage_served(menu, e, i, r) by {
        let n = stage_at(i, r);
        if n<4 {
            let j = match r {
                Replica::R1 => if n == 0 { 0 } else if n == 1 { 2 } else if n == 2 { 7 } else { 12 },
                Replica::R2 => if n == 0 { 1 } else if n == 1 { 3 } else if n == 2 { 8 } else { 13 },
                Replica::R3 => i,
            };
            assert(j >= i && ((e.event)(j) == expected(r, n) || (n != 3 && !(e.state)(j).live.contains(r))));
        }
    }
    assert forall|i: nat| #[trigger] poll_after(e, i) by {
        let j = 3*i+17;
        assert(j%3 == 2);
        assert((e.event)(j) == Rpc::Poll);
    }
    assert forall|i: nat, r: Replica| #[trigger] tick_after(e, i, r) by {
        let j = if r == Replica::R1 { 3*i+18 } else { 3*i+19 };
        assert((3*i+18)%3 == 0 && (3*i+19)%3 == 1);
        assert(j >= i && ((e.event)(j) == Rpc::Tick(r) || !(e.state)(j).live.contains(r)));
    }
    assert forall|i: nat, r: Replica| #[trigger] apply_debt_served(e, i, r) by {
        let s = (e.state)(i);
        let d = (s.book.store.disk)(r);
        if d.applied<d.known {
            let start: nat = if early { 4 } else { 9 };
            let j = if i<start { start } else { i };
            assert(j >= i && (e.event)(j) == Rpc::Storage(Move::Apply(r)));
        }
    }
}

// The antecedent used here is the fair progress clause of stock A. It is
// instantiated on an infinite, admitted stock execution from a reachable
// mixed state, including delivery of old replies and ordinary log catch-up.
pub proof fn mixed_stock_service(menu: Set<Replica>, rho: Resolver, early: bool)
    requires pair().subset_of(menu),
    ensures ({
        let p = rpc(menu, rho);
        let e = comparison(rho, early);
        follows_stock(p, e) && fair(menu, e) && reaches(p, (e.state)(0)) && at_invocation((e.state)(0))
            && ((e.state)(12).book.store.disk)(Replica::R1).value == 5
            && (e.state)(14).book.received == two_rows(early)
            && (eventual(p, |e| fair(menu, e)) ==> rho(two_rows(early)).is_some())
    }),
{
    reachable_mixed_stock();
    invoke_after_stock_prefix(menu, rho, split_stock());
    let p = rpc(menu, rho);
    let e = comparison(rho, early);
    assert(mixed_store(early, 0).disk =~= split_stock().disk);
    assert((e.state)(0).stage =~= initial().stage);
    assert(reaches(p, (e.state)(0)));
    follow_mixed(menu, rho, early); fair_mixed(menu, rho, early);
    if eventual(p, |e| fair(menu, e)) {
        assert forall|i: nat| (p.client_live)(#[trigger] (e.state)(i)) && majority((p.up)((e.state)(i))) by {};
        assert(exists|j: nat| (p.response)(#[trigger] (e.state)(j)).is_some());
    }
}

pub open spec fn agreement() -> Resolver { |m| equal_values(m) }

pub proof fn equal_value_wait_on_a_reachable_stock_split(menu: Set<Replica>)
    requires pair().subset_of(menu),
    ensures !eventual(rpc(menu, agreement()), |e| fair(menu, e)),
        (comparison(agreement(), true).state)(15).returned == Some(5),
        forall|k: nat| (#[trigger] (comparison(agreement(), false).state)(k)).returned.is_none(),
{
    mixed_stock_service(menu, agreement(), false);
    mixed_stock_service(menu, agreement(), true);
    let m = two_rows(true);
    assert forall|r: Replica| #[trigger] m.contains_key(r) implies m[r].value == m[latest_site(m)].value by {};
    assert(two_rows(false).contains_key(Replica::R1) && two_rows(false).contains_key(Replica::R2));
}

}
