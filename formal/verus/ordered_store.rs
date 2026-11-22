use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::{all_replicas, alpha, checkpoint_end, Notice};

verus! {

// These are ordinary command invocations in the comparison SMR. Each
// returns the old register and installs the new one. Distinct log entries
// denote distinct invocations, including entries with the same command.
pub enum Command { Increment, TimesFive }

pub open spec fn execute(c: Command, x: int) -> int {
    match c { Command::Increment => x + 1, Command::TimesFive => 5 * x }
}

pub open spec fn value_at(log: Seq<Command>, applied: nat) -> int
    decreases applied,
{
    if applied == 0 { 1 } else {
        execute(log[applied - 1], value_at(log, (applied - 1) as nat))
    }
}

pub proof fn increasing_stock_register(log: Seq<Command>, i: nat, j: nat)
    requires i <= j <= log.len(),
    ensures 1 <= value_at(log, i) <= value_at(log, j), i<j ==> value_at(log, i)<value_at(log, j),
    decreases j,
{
    if j>0 {
        let h = (j-1) as nat;
        if i == j { increasing_stock_register(log, h, h); } else { increasing_stock_register(log, i, h); }
        assert(value_at(log, j) == execute(log[h as int], value_at(log, h)));
    }
}

pub open spec fn command_return(log: Seq<Command>, index: nat) -> int {
    value_at(log, index)
}

pub open spec fn extends(earlier: Seq<Command>, later: Seq<Command>) -> bool {
    earlier.len() <= later.len() && earlier == later.take(earlier.len() as int)
}

pub proof fn same_decided_prefix(a: Seq<Command>, b: Seq<Command>, k: nat)
    requires extends(a, b), k <= a.len(),
    ensures value_at(a, k) == value_at(b, k),
    decreases k,
{
    if k > 0 {
        same_decided_prefix(a, b, (k - 1) as nat);
        assert(a[k - 1] == b[k - 1]);
    }
}

pub open spec fn majority(q: Set<Replica>) -> bool {
    (q.contains(Replica::R1) && q.contains(Replica::R2))
        || (q.contains(Replica::R1) && q.contains(Replica::R3))
        || (q.contains(Replica::R2) && q.contains(Replica::R3))
}

pub struct Disk {
    pub known: nat, // Available decided entries, including unapplied ones
    pub applied: nat, // Position actually installed in the shared register
    pub value: int,
}

pub struct LogPacket { pub from: Replica, pub to: Replica, pub entries: Seq<Command> }

pub struct Store {
    pub log: Seq<Command>,
    pub disk: spec_fn(Replica) -> Disk,
    pub pending: Map<nat, LogPacket>,
}

pub enum Move {
    Decide(Command, Set<Replica>),
    Offer(nat, Replica, Replica),
    Receive(nat),
    Apply(Replica),
}

pub open spec fn initial_store() -> Store {
    Store { log: Seq::empty(), disk: |r| Disk { known: 0, applied: 0, value: 1 }, pending: Map::empty() }
}

pub open spec fn consistent(s: Store) -> bool {
    (forall|r: Replica| {
        let d = #[trigger] (s.disk)(r);
        d.applied <= d.known <= s.log.len() && d.value == value_at(s.log, d.applied)
    })
    && (forall|id: nat| #[trigger] s.pending.contains_key(id) ==> extends(s.pending[id].entries, s.log))
    && majority(all_replicas().filter(|r: Replica| (s.disk)(r).known == s.log.len()))
}

// Decide abstracts an already successful ordinary majority decision. The
// selected replicas must actually know its predecessor. Other replicas
// can learn a decided prefix only by consuming an offered packet.
pub open spec fn allowed(s: Store, a: Move) -> bool {
    match a {
        Move::Decide(_, q) => majority(q)
            && forall|r: Replica| q.contains(r) ==> #[trigger] (s.disk)(r).known == s.log.len(),
        Move::Offer(id, from, to) => !s.pending.contains_key(id) && from != to,
        Move::Receive(id) => s.pending.contains_key(id),
        Move::Apply(r) => (s.disk)(r).applied < (s.disk)(r).known,
    }
}

pub open spec fn apply_disk(s: Store, r: Replica) -> Disk {
    let d = (s.disk)(r);
    Disk { applied: d.applied + 1, value: execute(s.log[d.applied as int], d.value), ..d }
}

pub open spec fn step(s: Store, a: Move) -> Store {
    match a {
        Move::Decide(c, q) => Store { log: s.log.push(c),
            disk: |r| if q.contains(r) { Disk { known: s.log.len() + 1, ..(s.disk)(r) } } else { (s.disk)(r) }, ..s },
        Move::Offer(id, from, to) => Store { pending: s.pending.insert(id, LogPacket {
            from, to, entries: s.log.take((s.disk)(from).known as int) }), ..s },
        Move::Receive(id) => {
            let p = s.pending[id];
            Store { pending: s.pending.remove(id), disk: |r| if r == p.to && (s.disk)(r).known < p.entries.len() {
                Disk { known: p.entries.len(), ..(s.disk)(r) }
            } else { (s.disk)(r) }, ..s }
        },
        Move::Apply(r) => Store { disk: |p| if p == r { apply_disk(s, r) } else { (s.disk)(p) }, ..s },
    }
}

pub proof fn step_preserves_order(s: Store, a: Move)
    requires consistent(s), allowed(s, a),
    ensures consistent(step(s, a)), extends(s.log, step(s, a).log),
{
    let t = step(s, a);
    assert(s.log =~= t.log.take(s.log.len() as int));
    assert forall|r: Replica| {
        let d = #[trigger] (t.disk)(r);
        d.applied <= d.known <= t.log.len() && d.value == value_at(t.log, d.applied)
    } by {
        let d = (s.disk)(r);
        assert(d.value == value_at(s.log, d.applied) && d.applied <= d.known <= s.log.len());
        same_decided_prefix(s.log, t.log, d.applied);
        if let Move::Apply(site) = a {
            if r == site { assert(value_at(s.log, d.applied + 1) == execute(s.log[d.applied as int], d.value)); }
        }
    }
    assert forall|id: nat| #[trigger] t.pending.contains_key(id) implies extends(t.pending[id].entries, t.log) by {
        let entries = t.pending[id].entries;
        if s.pending.contains_key(id) { assert(extends(s.pending[id].entries, s.log)); }
        match a {
            Move::Offer(slot, from, _) if slot == id => { assert((s.disk)(from).known <= s.log.len()); },
            _ => {},
        }
        assert(entries =~= t.log.take(entries.len() as int));
    }
    match a { Move::Decide(_, q) => {}, _ => {} }
}

pub open spec fn history(t: Seq<Store>, a: Seq<Move>) -> bool {
    t.len() == a.len() + 1 && t[0] == initial_store()
        && forall|i: int| 0 <= i < a.len() ==> allowed(t[i], #[trigger] a[i]) && t[i+1] == step(t[i], a[i])
}

pub open spec fn reachable(s: Store) -> bool {
    exists|t: Seq<Store>, a: Seq<Move>| #[trigger] history(t, a) && t.last() == s
}

proof fn invariant(t: Seq<Store>, a: Seq<Move>, k: nat)
    requires history(t, a), k <= a.len(),
    ensures consistent(t[k as int]),
    decreases k,
{
    if k > 0 {
        let j = (k-1) as nat;
        invariant(t, a, j);
        assert(allowed(t[j as int], a[j as int]));
        step_preserves_order(t[j as int], a[j as int]);
    }
}

pub proof fn reachable_store_is_consistent(s: Store)
    requires reachable(s),
    ensures consistent(s),
{
    let (t, a) = choose|t: Seq<Store>, a: Seq<Move>| #[trigger] history(t, a) && t.last() == s;
    invariant(t, a, a.len());
}

pub struct Stamp { pub version: nat, pub value: int }

pub open spec fn sample(s: Store, r: Replica) -> Stamp {
    Stamp { version: (s.disk)(r).applied, value: (s.disk)(r).value }
}

pub open spec fn authentic(log: Seq<Command>, x: Stamp) -> bool {
    x.version <= log.len() && x.value == value_at(log, x.version)
}

// Re-running the two actual operations in the stock total order cannot
// reproduce either their pair of return values or the two stored prefixes.
pub proof fn the_two_rmws_are_not_a_split_stock_history(log: Seq<Command>, i: nat, j: nat)
    requires log == seq![Command::Increment, Command::TimesFive]
        || log == seq![Command::TimesFive, Command::Increment], i <= 2, j <= 2,
    ensures !(command_return(log, 0) == 1 && command_return(log, 1) == 1),
        !(value_at(log, i) == 2 && value_at(log, j) == 5),
{
    reveal_with_fuel(value_at, 3);
    assert(i == 0 || i == 1 || i == 2);
    assert(j == 0 || j == 1 || j == 2);
}

// A genuinely reachable alternative uses four DISTINCT ordinary increments.
// R2/R3 decide them, then R3 sends its decided log to R1. Receipt installs
// the command log only. R1 applies just one entry before the handoff.
pub open spec fn committed_four() -> Seq<Command> {
    Seq::new(4, |i: int| Command::Increment)
}

pub open spec fn split_steps() -> Seq<Move> {
    Seq::new(15, |i: int| {
        if i < 4 { Move::Decide(Command::Increment, set![Replica::R2, Replica::R3]) }
        else if i == 4 { Move::Offer(0, Replica::R3, Replica::R1) }
        else if i == 5 { Move::Receive(0) }
        else if i == 6 { Move::Apply(Replica::R1) }
        else if i < 11 { Move::Apply(Replica::R2) } else { Move::Apply(Replica::R3) }
    })
}

pub open spec fn split_storage(k: nat) -> Store {
    let full = committed_four();
    let count: nat = if k < 4 { k } else { 4 };
    let p = LogPacket { from: Replica::R3, to: Replica::R1, entries: full };
    Store { log: full.take(count as int), pending: if k == 5 { Map::empty().insert(0, p) } else { Map::empty() },
        disk: |r| {
            let applied: nat = match r {
                Replica::R1 => if k >= 7 { 1 } else { 0 },
                Replica::R2 => if k <= 7 { 0 } else if k >= 11 { 4 } else { (k-7) as nat },
                Replica::R3 => if k <= 11 { 0 } else { (k-11) as nat },
            };
            Disk { known: if r == Replica::R1 && k < 6 { 0 } else { count }, applied, value: 1 + applied as int }
        } }
}

pub open spec fn split_stock() -> Store { split_storage(15) }

pub proof fn reachable_mixed_stock()
    ensures reachable(split_stock()), consistent(split_stock()), split_stock().pending == Map::<nat, LogPacket>::empty(),
        forall|r: Replica| #[trigger] (split_stock().disk)(r).value == (checkpoint_end(alpha(Notice::G)).locals)(r)
            && (split_stock().disk)(r).known == 4,
        sample(split_stock(), Replica::R1) == (Stamp { version: 1, value: 2 }),
        sample(split_stock(), Replica::R2) == (Stamp { version: 4, value: 5 }),
        forall|i: nat| i < 4 ==> #[trigger] command_return(split_stock().log, i) == i+1,
{
    let t = Seq::new(16, |i: int| split_storage(i as nat));
    let a = split_steps();
    assert(t[0].log =~= initial_store().log);
    assert(t[0].disk =~= initial_store().disk);
    assert forall|i: int| 0 <= i < a.len() implies
        allowed(t[i], #[trigger] a[i]) && t[i+1] == step(t[i], a[i]) by {
        crate::checkpoint::prefix_index(i);
        let next = step(t[i], a[i]);
        assert(next.log =~= t[i+1].log);
        if i == 4 {
            assert(t[i].log.take((t[i].disk)(Replica::R3).known as int) =~= committed_four());
        }
        assert(next.pending =~= t[i+1].pending);
        assert(next.disk =~= t[i+1].disk);
    }
    assert(history(t, a));
    reachable_store_is_consistent(split_stock());
    assert forall|i: nat| i < 4 implies #[trigger] command_return(split_stock().log, i) == i+1 by {
        assert(i == 0 || i == 1 || i == 2 || i == 3);
        reveal_with_fuel(value_at, 4);
    }
}

}
