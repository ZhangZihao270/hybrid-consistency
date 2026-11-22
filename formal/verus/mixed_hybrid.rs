use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::fresh_send;
use crate::delivery::*;
use crate::mixed_read::*;
use crate::ordered_store::Stamp;
use crate::protocol::*;
use crate::quorum_rpc::*;
use crate::service::*;
use crate::sr2::*;
use crate::stock::*;
use crate::stock_availability::eventual;

verus! {

// One-shot quorum readers whose only decision input is the labeled map
// of sample values. Replica/client private bookkeeping is still present.
// A partial rule may decline to return on some combinations.
pub type DataRule = spec_fn(Map<Replica, int>) -> Option<int>;

pub open spec fn values(m: Map<Replica, Stamp>) -> Map<Replica, int> {
    Map::new(m.dom(), |r| m[r].value)
}

pub open spec fn inputs(one: int, two: int) -> Map<Replica, int> {
    Map::empty().insert(Replica::R1, one).insert(Replica::R2, two)
}

pub open spec fn data_choice(f: DataRule) -> Select {
    |a: Report, b: Report| f(inputs(a.value, b.value)).unwrap()
}

pub open spec fn data_reader(f: DataRule) -> LocalProtocol<Reader, int, Wire> {
    let m = read_protocol(Set::empty(), Notice::G, data_choice(f));
    LocalProtocol { accept: |s: Reader, e: ProcessStep<int, Wire>| (m.accept)(s, e)
        && (e.action != Action::Strong(Process::SecondClient) || f(inputs(s.r1.unwrap().value, s.r2.unwrap().value)).is_some()), ..m }
}

proof fn with_sr1(f: DataRule, b: Fork)
    requires b.notice == Notice::G,
    ensures accepted(data_reader(f), checkpoint_observations(b)),
        completed_quorum_sample(data_reader(f), |s: Reader|s.prior.reply.unwrap(), b),
        resume_at(data_reader(f), checkpoint_observations(b)).initial == reader(b, Set::empty(), data_choice(f)).initial,
{
    let sel = data_choice(f);
    let base = read_protocol(Set::empty(), b.notice, sel);
    let m = data_reader(f);
    let obs = checkpoint_observations(b);
    let c = Process::FirstClient;
    fresh_reader_resumes_actual_sr1_state(b, Set::empty(), sel);
    combined_reader_supplies_sr1_sample(b, Set::empty(), sel);
    assert forall|i: int| 0 <= i<obs.len() implies {
        let e = #[trigger] obs[i]; (m.accept)(memory(m, e.actor, obs, i as nat), e)
    } by {
        prefix_index(i); assert(obs[i].action != Action::Strong(Process::SecondClient));
        memory_from_same_local_state(m, base, obs[i].actor, obs, i as nat);
        assert((base.accept)(memory(base, obs[i].actor, obs, i as nat), obs[i]));
    }
    assert forall|k: nat| k <= 14 implies #[trigger] first_client_at(m, b, k) == first_client_at(base, b, k)
        by { memory_from_same_local_state(m, base, c, obs, k); }
    assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m, b, k)) by {
        assert(!(base.done)(first_client_at(base, b, k)));
    }
    assert(first_return_len(m, b) == first_return_len(base, b));
    assert(first_result(m, |s: Reader|s.prior.reply.unwrap(), b) == first_result(base, |s: Reader|s.prior.reply.unwrap(), b));
    let x = resume_at(m, obs);
    let y = resume_at(base, obs);
    assert(x.initial =~= y.initial) by {
        assert forall|p: Process| #[trigger] (x.initial)(p) == (y.initial)(p)
            by { memory_from_same_local_state(m, base, p, obs, obs.len()); }
    }
}

proof fn actual_mixed_response(f: DataRule)
    requires f(inputs(2, 5)).is_some(),
    ensures ({
        let b = alpha(Notice::G);
        let net = checkpoint_end(b);
        let a = completed_actions(b);
        let t = exchange_states(b, true);
        response_path(resume_at(data_reader(f), checkpoint_observations(b)), |s: Reader|s.returned,
            net, delayed_slots(), t, a, f(inputs(2, 5)).unwrap())
        && forall|i: int| 0 <= i<a.len() ==> stock_work(#[trigger] observations(t, a)[i])
    }),
{
    hide(memory); hide(checkpoint_control); hide(permits_step); hide(read_accept);
    let b = alpha(Notice::G);
    let sel = data_choice(f);
    let t = exchange_states(b, true);
    let a = completed_actions(b);
    let es = observations(t, a);
    let m = resume_at(data_reader(f), checkpoint_observations(b));
    let base = reader(b, Set::empty(), sel);
    let c = Process::SecondClient;
    with_sr1(f, b); ordinary_quorum_can_return(b, Set::empty(), sel);
    assert(report(b, Replica::R1).value == 2 && report(b, Replica::R2).value == 5);
    assert forall|i: int| 0 <= i<es.len() implies {
        let e = #[trigger] es[i]; (m.accept)(memory(m, e.actor, es, i as nat), e) && stock_work(e)
    } by {
        prefix_index(i);
        memory_from_same_local_state(m, base, es[i].actor, es, i as nat);
        assert((base.accept)(memory(base, es[i].actor, es, i as nat), es[i]));
        if i == 8 { exchange_tracks_private_memory(b, Set::empty(), sel, true, c, 8); }
    }
    assert forall|k: nat| k<es.len() implies (#[trigger] memory(m, c, es, k)).returned.is_none() by {
        memory_from_same_local_state(m, base, c, es, k);
        exchange_tracks_private_memory(b, Set::empty(), sel, true, c, k);
    }
    memory_from_same_local_state(m, base, c, es, 9);
    assert forall|i: int| 0 <= i<a.len() implies fresh_send(#[trigger] a[i], delayed_slots()) by { prefix_index(i); }
}

// An actual reachable mixed stock execution forces the partial data rule
// to decide. That fact enables the return in the two existing histories.
// No stock-to-hybrid simulation premise and no hybrid availability premise.
pub proof fn mixed_stock_progress_forces_hot_pair(menu: Set<Replica>, f: DataRule)
    requires pair().subset_of(menu),
        eventual(rpc(menu, |m| f(values(m))), |e| fair(menu, e)),
    ensures ({
        let n = Notice::G;
        let a = completed_actions(alpha(n));
        let v = f(inputs(2, 5)).unwrap();
        f(inputs(2, 5)).is_some()
            && incompatible_completions(n, data_reader(f), |s: Reader|s.prior.reply.unwrap(), |s: Reader|s.returned, a, v)
            && ordinary_suffix(alpha(n), a) && ordinary_suffix(beta(n), a)
    }),
{
    let rho = |m| f(values(m));
    let n = Notice::G;
    mixed_stock_service(menu, rho, false);
    assert(values(two_rows(false)) =~= inputs(2, 5));
    with_sr1(f, alpha(n)); with_sr1(f, beta(n)); actual_mixed_response(f);
    ordinary_path_is_hot_pair(n, data_reader(f), |s: Reader|s.prior.reply.unwrap(), |s: Reader|s.returned,
        exchange_states(alpha(n), true), completed_actions(alpha(n)), f(inputs(2, 5)).unwrap());
}


// In this concrete positive instance the data rule selects a named
// quorum member's largest reported value. Both ordinary commands of the
// test register strictly increase x from its initial value 1.
pub open spec fn larger(m: Map<Replica, int>, r: Replica, p: Replica) -> Replica {
    if !m.contains_key(r) || (m.contains_key(p) && m[p]>m[r]) { p } else { r }
}

pub open spec fn high_site(m: Map<Replica, int>) -> Replica {
    larger(m, larger(m, Replica::R1, Replica::R2), Replica::R3)
}

pub open spec fn high_value(m: Map<Replica, int>) -> Option<int> {
    if crate::ordered_store::majority(m.dom()) { Some(m[high_site(m)]) } else { None }
}

proof fn max_value_resolves_latest(log: Seq<crate::ordered_store::Command>, rows: Map<Replica, Stamp>)
    ensures crate::rpc_majority::resolves_latest(|m|high_value(values(m)), log, rows),
{
    if crate::ordered_store::majority(rows.dom())
        && forall|r: Replica| #[trigger] rows.contains_key(r) ==> crate::ordered_store::authentic(log, rows[r]) {
        latest_is_a_sample(rows);
        let d = values(rows);
        let x = high_site(d);
        let y = latest_site(rows);
        assert(rows.contains_key(x) && rows.contains_key(y));
        assert(d[x] >= d[y]);
        assert(crate::ordered_store::authentic(log, rows[x]) && crate::ordered_store::authentic(log, rows[y]));
        crate::ordered_store::increasing_stock_register(log, rows[x].version, rows[y].version);
    }
}

pub proof fn max_sample_respects_completed_stock_commands(
    t: Seq<Round>, a: Seq<Rpc>, v: int, j: nat, old: int,
)
    requires ({
        let p = crate::rpc_majority::rpc_stock(|m|high_value(values(m)));
        crate::stock_availability::reaches(p, t[0]) && at_invocation(t[0]) && crate::stock_availability::first_answer(p, t, a, v)
            && crate::rpc_majority::can_answer_command(t[0].book.store, j, old)
    }),
    ensures exists|h: nat| j<h <= t.last().book.store.log.len() && #[trigger] crate::ordered_store::value_at(t.last().book.store.log, h) == v,
{
    let rho = |m|high_value(values(m));
    assert forall|log: Seq<crate::ordered_store::Command>, m: Map<Replica, Stamp>| #[trigger] crate::rpc_majority::resolves_latest(rho, log, m)
        by { max_value_resolves_latest(log, m); }
    crate::rpc_majority::latest_covers_prior_publication(rho, t, a, j+1, v);
}

pub proof fn max_sample_has_stock_a_and_returns_on_both()
    ensures ({
        let f = |m|high_value(m);
        let n = Notice::G;
        crate::stock_availability::read_a(crate::rpc_majority::rpc_stock(|m|f(values(m))), |e| fair(all_replicas(), e))
            && incompatible_completions(n, data_reader(f), |s: Reader|s.prior.reply.unwrap(), |s: Reader|s.returned, completed_actions(alpha(n)), 5)
            && (comparison(|m|f(values(m)), false).state)(15).returned == Some(5)
            && crate::ordered_store::value_at(crate::ordered_store::split_stock().log, 4) == 5
            && (forall|j: nat| j<4 ==> #[trigger] crate::rpc_majority::can_answer_command(crate::ordered_store::split_stock(), j, j as int+1))
            && crate::protocol::memory(checkpoint_machine(), Process::FirstClient, observations(stock_first_trace(), stock_first_prefix()), 15).reply == Some(5)
    }),
{
    let f = |m|high_value(m);
    let rho = |m|f(values(m));
    assert forall|m: Map<Replica, Stamp>| crate::ordered_store::majority(m.dom()) && crate::stock_reports::consistent_versions(m) implies {
        let v = #[trigger] rho(m); v.is_some() && exists|r: Replica| #[trigger] m.contains_key(r) && v == Some(m[r].value)
    } by { let r = high_site(values(m)); assert(m.contains_key(r) && rho(m) == Some(m[r].value)); }
    crate::stock_reports::common_log_implies_consistency();
    crate::rpc_majority::any_majority_stock_read(rho);
    mixed_stock_progress_forces_hot_pair(all_replicas(), f);
    stock_first_read_at_mixed_cut(); crate::ordered_store::reachable_mixed_stock();
    assert forall|j: nat| j<4 implies #[trigger] crate::rpc_majority::can_answer_command(crate::ordered_store::split_stock(), j, j as int+1) by {
        assert(crate::ordered_store::command_return(crate::ordered_store::split_stock().log, j) == j+1);
    }
    assert(crate::ordered_store::authentic(crate::ordered_store::split_stock().log,
        crate::ordered_store::sample(crate::ordered_store::split_stock(), Replica::R2)));
}

}
