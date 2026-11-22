use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::all_replicas;
use crate::mixed_hybrid::{inputs, values};
use crate::mixed_read::{pair, two_rows, mixed_stock_service};
use crate::ordered_store::*;
use crate::quorum_rpc::*;
use crate::rpc_majority::{rpc_stock, any_majority_stock_read};
use crate::stock_availability::{eventual, read_a};
use crate::stock_reports::{from_log, has_log};

verus! {

pub type Rows = Map<Replica, Stamp>;

// The ordinary readiness check may inspect the sender-labeled values and
// any specified function of the full stamped replies. The value selection
// code below can inspect the original raw positions even if readiness only
// uses a comparison or another derived field.
pub struct ReadInput<K> {
    pub values: Map<Replica, int>,
    pub field: K,
}

pub type Inspect<K> = spec_fn(Rows) -> K;
pub type Ready<K> = spec_fn(ReadInput<K>) -> bool;
pub type ChooseValue = spec_fn(Rows) -> int;

pub open spec fn inspect<K>(field: Inspect<K>, rows: Rows) -> ReadInput<K> {
    ReadInput { values: values(rows), field: field(rows) }
}

pub open spec fn resolve<K>(field: Inspect<K>, ready: Ready<K>, pick: ChooseValue) -> Resolver {
    |rows| if ready(inspect(field, rows)) { Some(pick(rows)) } else { None }
}

pub open spec fn unadvanced_rows() -> Rows {
    Map::empty().insert(Replica::R1, Stamp { version: 0, value: 2 })
        .insert(Replica::R2, Stamp { version: 0, value: 5 })
}

proof fn lower_bound(log: Seq<Command>, k: nat)
    requires k <= log.len(),
    ensures value_at(log, k) >= 1 + k as int,
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat;
        lower_bound(log, j);
        assert(value_at(log, k) == execute(log[j as int], value_at(log, j)));
    }
}

proof fn increments_between_two_and_five(log: Seq<Command>, k: nat)
    requires 1 <= k <= log.len(), value_at(log, 1) == 2, value_at(log, k) <= 5,
    ensures value_at(log, k) == 1 + k as int,
    decreases k,
{
    if k > 1 {
        let j = (k - 1) as nat;
        increasing_stock_register(log, 1, j);
        increasing_stock_register(log, j, k);
        increments_between_two_and_five(log, j);
        assert(value_at(log, k) == execute(log[j as int], value_at(log, j)));
    }
}

// Necessity for ALL common logs, also when the two replies were sent at
// different times. The other direction has an actual reachable fair witness.
pub proof fn unique_split_stamps(log: Seq<Command>, rows: Rows)
    requires from_log(log, rows), values(rows) == inputs(2, 5),
    ensures rows == two_rows(false),
{
    let one = Replica::R1;
    let two = Replica::R2;
    assert(rows.contains_key(one) && rows.contains_key(two));
    assert(values(rows)[one] == rows[one].value && values(rows)[two] == rows[two].value);
    assert(rows[one].value == 2 && rows[two].value == 5);
    let i = rows[one].version;
    let j = rows[two].version;
    assert(authentic(log, rows[one]) && authentic(log, rows[two]));
    lower_bound(log, i);
    if i == 0 { assert(value_at(log, 0) == 1); }
    assert(i == 1);
    assert(j > 0);
    increments_between_two_and_five(log, j);
    assert(rows =~= two_rows(false));
}

pub open spec fn stock_compatible<K>(field: Inspect<K>, observed: ReadInput<K>) -> bool {
    exists|log: Seq<Command>, rows: Rows| #[trigger] from_log(log, rows) && inspect(field, rows) == observed
}

// Reachability of this particular inspection, with the known sample values,
// has an exact test. It uses the observation of a constructed stock run.
pub proof fn exact_split_comparison<K>(field: Inspect<K>)
    ensures stock_compatible(field, inspect(field, unadvanced_rows()))
        == (inspect(field, unadvanced_rows()) == inspect(field, two_rows(false))),
{
    let actual = inspect(field, unadvanced_rows());
    let stock = two_rows(false);
    assert(actual.values =~= inputs(2, 5));
    if stock_compatible(field, actual) {
        let (l, r) = choose|l: Seq<Command>, r: Rows| #[trigger] from_log(l, r) && inspect(field, r) == actual;
        unique_split_stamps(l, r);
    }
    reachable_mixed_stock();
    let log = split_stock().log;
    assert forall|r: Replica| #[trigger] stock.contains_key(r) implies authentic(log, stock[r]) by {
        assert(stock[r] == sample(split_stock(), r));
    }
    assert(from_log(log, stock));
}

pub open spec fn latest_value(rows: Rows) -> int { rows[latest_site(rows)].value }

// Finite decision procedure. A reported value bounds its version because
// every stock command strictly increases this register. For a fixed log,
// at most one position can supply a given value.
pub open spec fn position(log: Seq<Command>, k: nat, value: int) -> Option<nat>
    decreases k,
{
    if value_at(log, k) == value { Some(k) }
    else if k == 0 { None } else { position(log, (k - 1) as nat, value) }
}

proof fn lookup_position(log: Seq<Command>, k: nat, value: int)
    requires k <= log.len(),
    ensures
        position(log, k, value).is_some() ==> {
            let j = position(log, k, value).unwrap();
            j <= k && value_at(log, j) == value
        },
        forall|i: nat| i <= k && #[trigger] value_at(log, i) == value ==> position(log, k, value) == Some(i),
    decreases k,
{
    if k > 0 { lookup_position(log, (k - 1) as nat, value); }
    assert forall|i: nat| i <= k && #[trigger] value_at(log, i) == value implies position(log, k, value) == Some(i) by {
        if i < k { increasing_stock_register(log, i, k); }
    }
}

pub open spec fn decode_rows(log: Seq<Command>, data: Map<Replica, int>) -> Rows {
    Map::new(data.dom(), |r| Stamp { version: position(log, log.len(), data[r]).unwrap(), value: data[r] })
}

pub open spec fn matches_log<K>(field: Inspect<K>, observed: ReadInput<K>, log: Seq<Command>) -> bool {
    let data = observed.values;
    (forall|r: Replica| #[trigger] data.contains_key(r) ==> position(log, log.len(), data[r]).is_some())
        && field(decode_rows(log, data)) == observed.field
}

proof fn check_one_log<K>(field: Inspect<K>, observed: ReadInput<K>, log: Seq<Command>)
    ensures matches_log(field, observed, log) == (exists|rows: Rows| #[trigger] from_log(log, rows) && inspect(field, rows) == observed),
{
    let data = observed.values;
    let decoded = decode_rows(log, data);
    if matches_log(field, observed, log) {
        assert forall|r: Replica| #[trigger] decoded.contains_key(r) implies authentic(log, decoded[r]) by {
            lookup_position(log, log.len(), data[r]);
        }
        assert(values(decoded) =~= data);
        assert(from_log(log, decoded));
    }
    if exists|rows: Rows| #[trigger] from_log(log, rows) && inspect(field, rows) == observed {
        let rows = choose|rows: Rows| #[trigger] from_log(log, rows) && inspect(field, rows) == observed;
        assert forall|r: Replica| #[trigger] data.contains_key(r) implies {
            position(log, log.len(), data[r]) == Some(rows[r].version) && decoded[r] == rows[r]
        } by {
            assert(rows.contains_key(r) && data[r] == values(rows)[r] && values(rows)[r] == rows[r].value);
            lookup_position(log, log.len(), data[r]);
        }
        assert(decoded =~= rows);
    }
}

pub open spec fn search_logs<K>(field: Inspect<K>, observed: ReadInput<K>, prefix: Seq<Command>, remaining: nat) -> bool
    decreases remaining,
{
    matches_log(field, observed, prefix) || (remaining > 0 && (
        search_logs(field, observed, prefix.push(Command::Increment), (remaining - 1) as nat)
            || search_logs(field, observed, prefix.push(Command::TimesFive), (remaining - 1) as nat)))
}

proof fn search_is_sound<K>(field: Inspect<K>, observed: ReadInput<K>, prefix: Seq<Command>, remaining: nat)
    requires search_logs(field, observed, prefix, remaining),
    ensures stock_compatible(field, observed),
    decreases remaining,
{
    if matches_log(field, observed, prefix) {
        check_one_log(field, observed, prefix);
        let raw = choose|raw: Rows| #[trigger] from_log(prefix, raw) && inspect(field, raw) == observed;
        assert(from_log(prefix, raw));
    } else if search_logs(field, observed, prefix.push(Command::Increment), (remaining - 1) as nat) {
        search_is_sound(field, observed, prefix.push(Command::Increment), (remaining - 1) as nat);
    } else {
        search_is_sound(field, observed, prefix.push(Command::TimesFive), (remaining - 1) as nat);
    }
}

proof fn search_reaches_witness<K>(field: Inspect<K>, observed: ReadInput<K>, prefix: Seq<Command>, remaining: nat, log: Seq<Command>)
    requires matches_log(field, observed, log), extends(prefix, log), log.len() <= prefix.len() + remaining,
    ensures search_logs(field, observed, prefix, remaining),
    decreases remaining,
{
    if prefix.len() == log.len() { assert(prefix =~= log); }
    else {
        let c = log[prefix.len() as int];
        let next = prefix.push(c);
        assert(next =~= log.take(next.len() as int));
        search_reaches_witness(field, observed, next, (remaining - 1) as nat, log);
        match c { Command::Increment => {}, Command::TimesFive => {} }
    }
}

pub open spec fn site_bound(data: Map<Replica, int>, r: Replica) -> nat {
    if data.contains_key(r) && data[r] > 0 { (data[r] - 1) as nat } else { 0 }
}

pub open spec fn search_bound(data: Map<Replica, int>) -> nat {
    let a = site_bound(data, Replica::R1);
    let b = site_bound(data, Replica::R2);
    let c = site_bound(data, Replica::R3);
    if a >= b && a >= c { a } else if b >= c { b } else { c }
}

pub proof fn validator_has_finite_test<K>(field: Inspect<K>, observed: ReadInput<K>)
    ensures stock_compatible(field, observed) == search_logs(field, observed, Seq::empty(), search_bound(observed.values)),
{
    let bound = search_bound(observed.values);
    if stock_compatible(field, observed) {
        let (log, rows) = choose|log: Seq<Command>, rows: Rows| #[trigger] from_log(log, rows) && inspect(field, rows) == observed;
        let k = if log.len() <= bound { log.len() } else { bound };
        let witness = log.take(k as int);
        assert(extends(witness, log));
        assert forall|r: Replica| #[trigger] rows.contains_key(r) implies authentic(witness, rows[r]) by {
            assert(authentic(log, rows[r]));
            lower_bound(log, rows[r].version);
            assert(observed.values.contains_key(r) && observed.values[r] == values(rows)[r] && values(rows)[r] == rows[r].value);
            assert(site_bound(observed.values, r) <= bound);
            same_decided_prefix(witness, log, rows[r].version);
        }
        assert(from_log(witness, rows));
        check_one_log(field, observed, witness);
        assert(Seq::<Command>::empty() =~= witness.take(0));
        search_reaches_witness(field, observed, Seq::empty(), bound, witness);
    } else if search_logs(field, observed, Seq::empty(), bound) {
        search_is_sound(field, observed, Seq::empty(), bound);
    }
}

// The validator is defined on every invocation without referring to this
// pair or to weak writes. Every actual stock majority passes. A bound and
// a finite search for this guard are checked above.
pub open spec fn stock_validator<K>(field: Inspect<K>) -> Resolver {
    resolve(field, |x| stock_compatible(field, x), |m| latest_value(m))
}

pub proof fn validator_has_stock_availability<K>(field: Inspect<K>)
    ensures read_a(rpc_stock(stock_validator(field)), |e| fair(all_replicas(), e)),
{
    let rho = stock_validator(field);
    assert forall|rows: Rows| majority(rows.dom()) && has_log(rows) implies {
        let v = #[trigger] rho(rows);
        v.is_some() && exists|r: Replica| #[trigger] rows.contains_key(r) && v == Some(rows[r].value)
    } by {
        let log = choose|l: Seq<Command>| #[trigger] from_log(l, rows);
        assert(stock_compatible(field, inspect(field, rows)));
        latest_is_a_sample(rows);
    }
    any_majority_stock_read(rho);
}

pub proof fn stock_progress_enables_inspected_gate<K>(field: Inspect<K>, ready: Ready<K>, pick: ChooseValue, menu: Set<Replica>)
    requires pair().subset_of(menu),
        eventual(rpc(menu, resolve(field, ready, pick)), |e| fair(menu, e)),
        stock_compatible(field, inspect(field, unadvanced_rows())),
    ensures resolve(field, ready, pick)(unadvanced_rows()) == Some(pick(unadvanced_rows())),
{
    exact_split_comparison(field);
    mixed_stock_service(menu, resolve(field, ready, pick), false);
}

// This is an iff about what stock A can force across the whole resolver
// family. Stock and hybrid are free to select different reply values.
pub proof fn exactly_when_stock_a_forces_service<K>(field: Inspect<K>)
    ensures stock_compatible(field, inspect(field, unadvanced_rows())) == (forall|ready: Ready<K>, pick: ChooseValue| {
        let rho = #[trigger] resolve(field, ready, pick);
        read_a(rpc_stock(rho), |e| fair(all_replicas(), e)) ==> rho(unadvanced_rows()).is_some()
    }),
{
    exact_split_comparison(field);
    if stock_compatible(field, inspect(field, unadvanced_rows())) {
        assert forall|ready: Ready<K>, pick: ChooseValue| {
            let rho = #[trigger] resolve(field, ready, pick);
            read_a(rpc_stock(rho), |e| fair(all_replicas(), e)) ==> rho(unadvanced_rows()).is_some()
        } by {
            if read_a(rpc_stock(resolve(field, ready, pick)), |e| fair(all_replicas(), e)) {
                stock_progress_enables_inspected_gate(field, ready, pick, all_replicas());
            }
        }
    } else {
        let ready = |x| stock_compatible(field, x);
        let pick = |rows| latest_value(rows);
        validator_has_stock_availability(field);
        assert(resolve(field, ready, pick) == stock_validator(field));
        assert(!resolve(field, ready, pick)(unadvanced_rows()).is_some());
    }
}

}
