use vstd::prelude::*;
use crate::{Replica, Op, legal, legal_history_keeps_first_read};
use crate::checkpoint::{Notice, alpha, all_replicas, live_pair};
use crate::metadata_pair::*;
use crate::metadata_stock::*;
use crate::mixed_read::{before_read, invoke_after_stock_prefix, pair};
use crate::ordered_store::*;
use crate::quorum_rpc::*;
use crate::rpc_majority::{actual_rows, during_service, quorum_service_step, rpc_stock, serve_a_quorum};
use crate::service::incompatible_completions;
use crate::stock_availability::*;

verus! {

pub open spec fn genesis_call() -> Round {
    Round { started: true, live: pair(), ..before_read(initial_store()) }
}

pub open spec fn genesis_rows() -> Rows { actual_rows(initial_store(), pair()) }

pub open spec fn stock_cpu(i: nat) -> Rpc {
    if i % 3 == 0 { Rpc::Tick(Replica::R1) } else if i % 3 == 1 { Rpc::Tick(Replica::R2) } else { Rpc::Poll }
}

pub open spec fn quiescent_call(rho: Resolver) -> Stream<Round, Rpc> {
    let x = genesis_call();
    Stream { state: |i| during_service(x, rho, pair(), i),
        event: |i: nat| if i < 13 { serve_a_quorum(pair(), i) } else { stock_cpu(i) } }
}

proof fn genesis_call_is_enabled(rho: Resolver)
    ensures ({
        let p = rpc_stock(rho); let e = quiescent_call(rho);
        follows_stock(p, e) && reaches(p, (e.state)(0)) && at_invocation((e.state)(0))
    }),
{
    let p = rpc_stock(rho); let e = quiescent_call(rho); let x = genesis_call();
    let s = initial_store(); let history_states = seq![s]; let history_actions = Seq::<Move>::empty();
    assert(history(history_states, history_actions)); assert(reachable(s));
    invoke_after_stock_prefix(all_replicas(), rho, s);
    assert((e.state)(0).stage =~= x.stage);
    assert((e.state)(0).book.packets =~= x.book.packets);
    assert((e.state)(0).book.received =~= x.book.received);
    assert forall|i: nat| (p.next)((e.state)(i), #[trigger] (e.event)(i), (e.state)(i + 1)) by {
        if i < 13 { quorum_service_step(rho, x, pair(), i); }
        else {
            let old = (e.state)(i);
            assert(old.book.received =~= genesis_rows());
            let next = advance_round(rho, old, (e.event)(i));
            let t = (e.state)(i+1);
            assert(enabled(old, all_replicas(), (e.event)(i)));
            assert(next.stage =~= t.stage);
            assert(next.book.received =~= t.book.received);
            assert(next.book.packets =~= t.book.packets);
            assert(next == t);
        }
    }
}

proof fn genesis_schedule_is_fair(rho: Resolver)
    ensures fair(all_replicas(), quiescent_call(rho)),
{
    let e = quiescent_call(rho);
    assert forall|i: nat, r: Replica| #[trigger] stage_served(all_replicas(), e, i, r) by {
        let n = ((e.state)(i).stage)(r);
        if n < 4 {
            let j = match r { Replica::R1 => 3 * n, Replica::R2 => 3 * n + 1, Replica::R3 => i };
            if r != Replica::R3 { assert(n == 0 || n == 1 || n == 2 || n == 3); }
            assert(j >= i && ((e.event)(j) == expected(r, n) || (n != 3 && !(e.state)(j).live.contains(r))));
        }
    }
    assert forall|i: nat| #[trigger] poll_after(e, i) by {
        let j = 3 * (i + 6) + 2; assert(j % 3 == 2); assert((e.event)(j) == Rpc::Poll);
    }
    assert forall|i: nat, r: Replica| #[trigger] tick_after(e, i, r) by {
        let offset: nat = if r == Replica::R1 { 0 } else { 1 }; let j = 3 * (i + 6) + offset;
        assert(j % 3 == offset); assert(j >= i && ((e.event)(j) == Rpc::Tick(r) || !(e.state)(j).live.contains(r)));
    }
}

// A's progress is invoked on this actual stock execution. Its interval
// rule then fixes the result at genesis, even for a selection rule that
// looks at all reported positions and need not be total off stock.
pub proof fn stock_reads_its_genesis_image(rho: Resolver)
    requires read_a(rpc_stock(rho), |e| fair(all_replicas(), e)),
    ensures rho(genesis_rows()) == Some(1),
{
    let e = quiescent_call(rho); let p = rpc_stock(rho);
    genesis_call_is_enabled(rho); genesis_schedule_is_fair(rho);
    assert forall|i: nat| (p.client_live)(#[trigger] (e.state)(i)) && majority((p.up)((e.state)(i))) by {};
    assert(exists|k: nat| (p.response)(#[trigger] (e.state)(k)).is_some());
    let k = choose|k: nat| (p.response)(#[trigger] (e.state)(k)).is_some();
    assert(rho(genesis_rows()).is_some());
    let v = rho(genesis_rows()).unwrap();
    let t = Seq::new(14, |i: int| (e.state)(i as nat));
    let a = Seq::new(13, |i: int| (e.event)(i as nat));
    assert forall|i: int| 0 <= i < a.len() implies (p.next)(t[i], #[trigger] a[i], t[i+1]) by {
        assert((p.next)((e.state)(i as nat), (e.event)(i as nat), (e.state)((i+1) as nat)));
    }
    assert(first_answer(p, t, a, v));
    assert(t.last().book.received =~= genesis_rows());
    assert((p.served_by)(t, a, pair()));
    assert(member_during(p, t, pair(), v));
    let (r, i) = choose|r: Replica, i: int| pair().contains(r) && 0 <= i < t.len() && #[trigger] (p.value)(t[i], r) == v;
    assert((p.value)(t[i], r) == 1);
}

// If this ordinary implementation permits the real local image to be
// reinstalled before sampling, even an arbitrary stamped-row resolver
// sees exactly the stock result on the two real repaired suffixes.
pub proof fn ordinary_images_force_both_reads(n: Notice, rho: Resolver, archives: Set<Replica>)
    requires read_a(rpc_stock(rho), |e| fair(all_replicas(), e)), live_pair().subset_of(archives),
    ensures incompatible_completions(n, machine(rho, archives), |s: Local| s.first.reply.unwrap(), |s: Local| s.returned,
            read_actions(alpha(n), BeforeSample::RestoreImages), 1),
        !(exists|a: Seq<Op>, x: Seq<int>| #[trigger] legal(a, x, 5, 1)),
        !(exists|a: Seq<Op>, x: Seq<int>| #[trigger] legal(a, x, 2, 1)),
{
    let b = alpha(n);
    crate::mixed_sources::actual_disk_before_sr2(b, 17, Replica::R1);
    crate::mixed_sources::actual_disk_before_sr2(b, 17, Replica::R2);
    assert(sample_rows(b, BeforeSample::RestoreImages) =~= genesis_rows());
    stock_reads_its_genesis_image(rho);
    returning_samples_contradict_h(n, rho, archives, BeforeSample::RestoreImages);
    assert forall|a: Seq<Op>, x: Seq<int>| !#[trigger] legal(a, x, 5, 1) by {
        if legal(a, x, 5, 1) { legal_history_keeps_first_read(a, x, 5, 1); }
    }
    assert forall|a: Seq<Op>, x: Seq<int>| !#[trigger] legal(a, x, 2, 1) by {
        if legal(a, x, 2, 1) { legal_history_keeps_first_read(a, x, 2, 1); }
    }
}

}
