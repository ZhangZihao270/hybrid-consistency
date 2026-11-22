use vstd::prelude::*;
use crate::Replica;
use crate::ordered_store::*;
use crate::stock_availability::*;

verus! {

pub struct Answer { pub from: Replica, pub data: Stamp }

pub struct Evidence {
    pub store: Store,
    pub packets: Map<nat, Answer>,
    pub received: Map<Replica, Stamp>,
}

pub enum Observable {
    Storage(Move), Send(nat, Replica), Deliver(nat), Duplicate(nat, nat), NewRead, Other,
}

pub open spec fn empty_evidence(s: Store) -> Evidence {
    Evidence { store: s, packets: Map::empty(), received: Map::empty() }
}

// The ordinary read observes the shared register together with an ordinary
// applied command position. Only a send samples. Delivery consumes the
// original body even after the replica has applied more commands.
pub open spec fn possible(s: Evidence, a: Observable) -> bool {
    match a {
        Observable::Storage(x) => allowed(s.store, x),
        Observable::Send(id, _) => !s.packets.contains_key(id),
        Observable::Deliver(id) => s.packets.contains_key(id),
        Observable::Duplicate(old, new) => s.packets.contains_key(old) && !s.packets.contains_key(new),
        _ => true,
    }
}

pub open spec fn observe(s: Evidence, a: Observable) -> Evidence {
    match a {
        Observable::Storage(x) => Evidence { store: step(s.store, x), ..s },
        Observable::Send(id, r) => Evidence { packets: s.packets.insert(id, Answer { from: r, data: sample(s.store, r) }), ..s },
        Observable::Deliver(id) => {
            let p = s.packets[id];
            Evidence { packets: s.packets.remove(id), received: s.received.insert(p.from, p.data), ..s }
        },
        Observable::Duplicate(old, new) => Evidence { packets: s.packets.insert(new, s.packets[old]), ..s },
        Observable::NewRead => Evidence { received: Map::empty(), ..s },
        Observable::Other => s,
    }
}

pub open spec fn sound(s: Evidence) -> bool {
    consistent(s.store)
        && (forall|id: nat| #[trigger] s.packets.contains_key(id) ==> authentic(s.store.log, s.packets[id].data))
        && (forall|r: Replica| #[trigger] s.received.contains_key(r) ==> authentic(s.store.log, s.received[r]))
}

pub open spec fn consistent_versions(rows: Map<Replica, Stamp>) -> bool {
    forall|r: Replica, p: Replica| #[trigger] rows.contains_key(r) && #[trigger] rows.contains_key(p)
        && rows[r].version == rows[p].version ==> rows[r].value == rows[p].value
}

// The sender may have moved on since emitting its sample. All genuine
// rows still describe prefixes of a single decided log.
pub open spec fn from_log(log: Seq<Command>, rows: Map<Replica, Stamp>) -> bool {
    forall|r: Replica| #[trigger] rows.contains_key(r) ==> authentic(log, rows[r])
}

pub open spec fn has_log(rows: Map<Replica, Stamp>) -> bool {
    exists|log: Seq<Command>| #[trigger] from_log(log, rows)
}

pub proof fn common_log_implies_consistency()
    ensures forall|rows: Map<Replica, Stamp>| #[trigger] has_log(rows) ==> consistent_versions(rows),
{
    assert forall|rows: Map<Replica, Stamp>| #[trigger] has_log(rows) implies consistent_versions(rows) by {
        let log = choose|log: Seq<Command>| #[trigger] from_log(log, rows);
    }
}

pub proof fn sound_step(s: Evidence, a: Observable)
    requires sound(s), possible(s, a),
    ensures sound(observe(s, a)), consistent_versions(observe(s, a).received),
{
    let t = observe(s, a);
    match a {
        Observable::Storage(x) => { step_preserves_order(s.store, x); },
        _ => { assert(s.store.log =~= t.store.log.take(s.store.log.len() as int)); },
    }
    assert forall|id: nat| #[trigger] t.packets.contains_key(id) implies authentic(t.store.log, t.packets[id].data) by {
        match a {
            Observable::Send(slot, r) if slot == id => { assert((s.store.disk)(r).value == value_at(s.store.log, (s.store.disk)(r).applied)); },
            _ => {
                let j = match a { Observable::Duplicate(old, new) if new == id => old, _ => id };
                assert(s.packets.contains_key(j) && t.packets[id] == s.packets[j]);
                same_decided_prefix(s.store.log, t.store.log, t.packets[id].data.version);
            },
        }
    }
    assert forall|r: Replica| #[trigger] t.received.contains_key(r) implies authentic(t.store.log, t.received[r]) by {
        if let Observable::Deliver(id) = a {
            assert(s.packets.contains_key(id) && authentic(s.store.log, s.packets[id].data));
        }
        assert(authentic(s.store.log, t.received[r]));
        same_decided_prefix(s.store.log, t.store.log, t.received[r].version);
    }
}

pub open spec fn audited_stock<X, E>(
    p: ReadSystem<X, E>, view: spec_fn(X) -> Evidence, event: spec_fn(X, E, X) -> Observable,
) -> bool {
    (forall|x: X| #[trigger] (p.initial)(x) ==> view(x) == empty_evidence(initial_store()))
        && forall|s: X, e: E, t: X| #[trigger] (p.next)(s, e, t) ==> {
            let a = event(s, e, t); possible(view(s), a) && view(t) == observe(view(s), a)
        }
}

// This is an ordinary validation on real collected fields. The selected
// value, application write identities, weak path, H and other run do not
// participate. Resampling/ordinary repair on a different path is allowed.
pub open spec fn validate_on_return<X, E>(p: ReadSystem<X, E>, view: spec_fn(X) -> Evidence, s: X, e: E, t: X) -> bool {
    (p.response)(s).is_none() && (p.response)(t).is_some() ==> consistent_versions(view(t).received)
}

pub proof fn applied_version_check_preserves_stock_a<X, E>(
    p: ReadSystem<X, E>, fair: spec_fn(Stream<X, E>) -> bool,
    view: spec_fn(X) -> Evidence, event: spec_fn(X, E, X) -> Observable,
)
    requires read_a(p, fair), audited_stock(p, view, event),
    ensures ({
        let g = |s, e, t| validate_on_return(p, view, s, e, t);
        read_a(guarded(p, g), fair)
            && forall|s: X, e: E, t: X| reaches(p, s) ==> ((p.next)(s, e, t) == #[trigger] (guarded(p, g).next)(s, e, t))
    }),
{
    let inv = |s: X| sound(view(s));
    let g = |s, e, t| validate_on_return(p, view, s, e, t);
    assert forall|s: X, e: E, t: X| inv(s) && #[trigger] (p.next)(s, e, t) implies inv(t) && g(s, e, t) by {
        sound_step(view(s), event(s, e, t));
    }
    assert(inductive(p, inv));
    live_guard_preserves_read_a(p, fair, inv, g);
    assert forall|s: X, e: E, t: X| reaches(p, s) implies ((p.next)(s, e, t) == #[trigger] (guarded(p, g).next)(s, e, t)) by {
        reachable_invariant(p, inv, s);
    }
}

pub proof fn applied_version_check_preserves_full_stock_runs<X, E>(
    p: ReadSystem<X, E>, view: spec_fn(X) -> Evidence, event: spec_fn(X, E, X) -> Observable,
)
    requires audited_stock(p, view, event),
    ensures ({
        let m = guarded(p, |s, e, t|validate_on_return(p, view, s, e, t));
        (forall|t: Seq<X>, a: Seq<E>| #[trigger] finite_stock_run(p, t, a) == finite_stock_run(m, t, a))
            && (forall|e: Stream<X, E>| #[trigger] infinite_stock_run(p, e) == infinite_stock_run(m, e))
    }),
{
    let inv = |s: X|sound(view(s));
    let g = |s, e, t|validate_on_return(p, view, s, e, t);
    assert forall|s: X, e: E, t: X| inv(s) && #[trigger] (p.next)(s, e, t) implies inv(t) && g(s, e, t) by {
        sound_step(view(s), event(s, e, t));
    }
    reachable_language_preserved(p, inv, g);
}

// A local validation which accepts every table of authentic emitted
// samples leaves the full reachable stock language intact.
pub open spec fn return_guard<X,E>(p: ReadSystem<X,E>, view: spec_fn(X)->Evidence,
    check: spec_fn(Map<Replica,Stamp>)->bool, s: X, t: X) -> bool {
    (p.response)(s).is_none() && (p.response)(t).is_some() ==> check(view(t).received)
}

pub proof fn authentic_guard_preserves_stock<X,E>(p: ReadSystem<X,E>, fair: spec_fn(Stream<X,E>)->bool,
    view: spec_fn(X)->Evidence, event: spec_fn(X,E,X)->Observable, check: spec_fn(Map<Replica,Stamp>)->bool)
    requires audited_stock(p,view,event),
        forall|m: Map<Replica,Stamp>| #[trigger] has_log(m) ==> check(m),
    ensures ({
        let q=guarded(p,|s,e,t| return_guard(p,view,check,s,t));
        (read_a(p,fair) ==> read_a(q,fair))
            && (forall|t: Seq<X>,a: Seq<E>| #[trigger] finite_stock_run(p,t,a) == finite_stock_run(q,t,a))
            && (forall|e: Stream<X,E>| #[trigger] infinite_stock_run(p,e) == infinite_stock_run(q,e))
    }),
{
    let inv=|s: X| sound(view(s)); let g=|s,e: E,t| return_guard(p,view,check,s,t);
    assert forall|s: X,e: E,t: X| inv(s) && #[trigger] (p.next)(s,e,t) implies inv(t) && g(s,e,t) by {
        sound_step(view(s),event(s,e,t));
        assert(from_log(view(t).store.log,view(t).received));
        assert(has_log(view(t).received));
    }
    reachable_language_preserved(p,inv,g);
    if read_a(p,fair) { live_guard_preserves_read_a(p,fair,inv,g); }
}

// The two relevant replies can come from different instants. Authentic
// delayed packets still cannot produce unequal values at an equal version.
pub proof fn conflicting_stamp_pair_has_no_stock_source<X, E>(
    p: ReadSystem<X, E>, view: spec_fn(X) -> Evidence, event: spec_fn(X, E, X) -> Observable, x: X,
    one: Stamp, two: Stamp,
)
    requires audited_stock(p, view, event), one.version == two.version, one.value != two.value,
        view(x).received.contains_key(Replica::R1), view(x).received.contains_key(Replica::R2),
        view(x).received[Replica::R1] == one, view(x).received[Replica::R2] == two,
    ensures !reaches(p, x),
{
    let inv = |s: X| sound(view(s));
    assert forall|s: X, e: E, t: X| inv(s) && #[trigger] (p.next)(s, e, t) implies inv(t)
        by { sound_step(view(s), event(s, e, t)); }
    if reaches(p, x) { reachable_invariant(p, inv, x); }
}

}
