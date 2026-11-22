use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;

// Uniform strong-only comparison histories. Each has an actual request to
// all three sites and the two selected reply deliveries to the first client.
verus! {

pub open spec fn uniform_first_packet(p: Packet<Wire>, value: int) -> Packet<Wire> {
    if first_reply(p) { Packet { input: Wire::Reply(value), ..p } } else { p }
}

pub open spec fn stock_first_actions(b: Fork, value: int) -> Seq<Action<Wire>> {
    Seq::new(15, |i: int| match actions_to_crash(b)[i + 2] {
        Action::Send(id, p) => Action::Send(id, uniform_first_packet(p, value)), a => a,
    })
}

pub open spec fn stock_first_net(b: Fork, value: int, k: nat) -> Network<int, Wire> {
    let n = state_after(b, k + 2);
    Network { locals: |r|value,
        pending: Map::new(n.pending.dom().filter(|id: nat| id >= 3), |id: nat| uniform_first_packet(n.pending[id], value)), ..n }
}

pub open spec fn stock_first_states(b: Fork, value: int) -> Seq<Network<int, Wire>> {
    Seq::new(16, |i: int| stock_first_net(b, value, i as nat))
}

pub open spec fn stock_first_events(b: Fork, value: int) -> Seq<ProcessStep<int, Wire>> {
    observations(stock_first_states(b, value), stock_first_actions(b, value))
}

pub proof fn uniform_first_transport(b: Fork, value: int)
    ensures trace(|x, w| cell(x, w), stock_first_states(b, value), stock_first_actions(b, value)),
        stock_first_net(b, value, 0).pending == Map::<nat, Packet<Wire>>::empty(),
        forall|r: Replica| #![trigger live(stock_first_net(b, value, 0), at(r))]
            live(stock_first_net(b, value, 0), at(r)) && (stock_first_net(b, value, 0).locals)(r) == value,
{
    let t = stock_first_states(b, value);
    let a = stock_first_actions(b, value);
    assert(t[0].pending =~= Map::<nat, Packet<Wire>>::empty());
    assert forall|i: int| 0 <= i<a.len() implies {
        let e = #[trigger] a[i]; enabled(t[i], e) && t[i + 1] == advance(|x, w| cell(x, w), t[i], e)
    } by {
        prefix_index(i); let post = advance(|x, w| cell(x, w), t[i], a[i]);
        assert(post.pending =~= t[i + 1].pending); assert(post.locals =~= t[i + 1].locals);
    }
}

pub open spec fn comparison_value(b: Fork, p: Process) -> int {
    match p { Process::At(Replica::R1) => 2, Process::At(Replica::R2) => 5, _ => first_value(b) }
}

pub open spec fn implements_step<S>(
    base: LocalProtocol<S, int, Wire>, m: LocalProtocol<S, int, Wire>, s: S, e: ProcessStep<int, Wire>,
) -> bool {
    (base.accept)(s, e) ==> (m.accept)(s, e) && (base.update)(s, e) == (m.update)(s, e)
}

pub open spec fn shares_role<S>(
    base: LocalProtocol<S, int, Wire>, m: LocalProtocol<S, int, Wire>, p: Process,
) -> bool {
    (base.initial)(p) == (m.initial)(p)
        && forall|s: S, e: ProcessStep<int, Wire>| e.actor == p && crate::confirmation::transport_event(e)
            ==> #[trigger] implements_step(base, m, s, e)
}

// We use a stock run agreeing at that *process*. The unreceived minority
// reply may have a completely different value in the client's stock run.
pub proof fn private_stock_history<S>(
    b: Fork, base: LocalProtocol<S, int, Wire>, m: LocalProtocol<S, int, Wire>, p: Process, k: nat,
)
    requires p != at(Replica::R3), shares_role(base, m, p), k <= 15,
        accepted(base, stock_first_events(b, comparison_value(b, p))),
    ensures ({
        let ss = stock_first_events(b, comparison_value(b, p));
        let hs = checkpoint_observations(b);
        memory(base, p, ss, k) == memory(m, p, hs, k + 2)
            && (k < 15 ==> (ss[k as int].actor == p) == (hs[k as int+2].actor == p)
                && (hs[k as int+2].actor == p ==> ss[k as int] == hs[k as int+2]))
    }),
    decreases k,
{
    let value = comparison_value(b, p);
    let es = stock_first_events(b, value);
    let hs = checkpoint_observations(b);
    if k > 0 {
        let j = (k - 1) as nat; private_stock_history(b, base, m, p, j);
        if es[j as int].actor == p {
            uniform_first_transport(b, value);
            let e = es[j as int];
            let t = stock_first_states(b, value);
            let a = stock_first_actions(b, value);
            assert(crate::confirmation::transport_event(e)) by { assert(enabled(t[j as int], a[j as int]) && process_step(t[j as int], a[j as int]) == e); }
            assert((base.accept)(memory(base, p, es, j), e));
            assert(implements_step(base, m, memory(base, p, es, j), e));
        }
    } else { reveal_with_fuel(memory, 3); }
    if k < 15 { prefix_index(k as int); }
}

// Five local guards at the one site with genuinely different weak history.
// The other roles' permissions will be obtained from stock executions.
pub open spec fn r3_after_weak_input<S>(m: LocalProtocol<S, int, Wire>, b: Fork) -> bool {
    let es = checkpoint_observations(b);
    let p = at(Replica::R3);
    let initial = (m.initial)(p);
    let copied = (m.update)(initial, es[0]);
    let published = (m.update)(copied, es[1]);
    let asked = (m.update)(published, es[7]);
    let replied = (m.update)(asked, es[10]);
    (m.accept)(initial, es[0]) && (m.accept)(copied, es[1]) && (m.accept)(published, es[7])
        && (m.accept)(asked, es[10]) && (m.accept)(replied, es[15])
}

proof fn issuer_memory<S>(m: LocalProtocol<S, int, Wire>, b: Fork, k: nat)
    requires k <= 17,
    ensures ({
        let es = checkpoint_observations(b);
        let p = at(Replica::R3);
        let init = (m.initial)(p);
        let copy = (m.update)(init, es[0]);
        let pubd = (m.update)(copy, es[1]);
        let ask = (m.update)(pubd, es[7]);
        let ans = (m.update)(ask, es[10]);
        memory(m, p, es, k) == if k == 0 {init} else if k == 1 {copy} else if k <= 7 {pubd}
            else if k <= 10 {ask} else if k <= 15 {ans} else {(m.update)(ans, es[15])}
    }),
    decreases k,
{
    if k > 0 { let j = (k - 1) as nat; issuer_memory(m, b, j); prefix_index(j as int); }
}

// Generic validity clause of A on an actually completed stock read. The
// adapter identifies its quorum and invocation/return boundaries.
pub open spec fn sampled_in_interval<S>(
    q: Set<Replica>, t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, lo: nat, hi: nat,
    m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int,
) -> bool {
    let ret = memory(m, Process::FirstClient, observations(t, a), hi);
    hi <= a.len() && lo <= hi && (m.done)(ret)
        && exists|r: Replica, j: int| q.contains(r) && lo <= j <= hi && #[trigger] (t[j].locals)(r) == first(ret)
}

// The stock call has completed at the selected hand-off; its timing and
// wire format are implementation facts, separate from stock quorum validity.
pub open spec fn stock_handoff<S>(b: Fork, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int) -> bool {
    let value = first_value(b);
    let t = stock_first_states(b, value);
    let a = stock_first_actions(b, value);
    let es = observations(t, a);
    let c = Process::FirstClient; let end = if (m.done)(memory(m, c, es, 11)) { 11nat} else {12nat};
    (forall|k: nat| k <= 10 ==> !(m.done)(#[trigger] memory(m, c, es, k)))
        && sampled_in_interval(crate::first_quorum(b.branch), t, a, 0, end, m, first)
}

pub proof fn stock_roles_supply_sr1<S>(
    b: Fork, stock: spec_fn(int) -> LocalProtocol<S, int, Wire>, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int,
)
    requires
        forall|p: Process| p != at(Replica::R3) ==> #[trigger] shares_role(stock(comparison_value(b, p)), m, p),
        forall|v: int| v == 2 || v == 5 ==> accepted(stock(v), #[trigger] stock_first_events(b, v)),
        stock_handoff(b, stock(first_value(b)), first), stock(first_value(b)).done == m.done,
        r3_after_weak_input(m, b),
    ensures accepted(m, checkpoint_observations(b)), completed_quorum_sample(m, first, b), first_result(m, first, b) == first_value(b),
{
    hide(memory);
    let hs = checkpoint_observations(b);
    let c = Process::FirstClient;
    prefix_transport_is_enabled(b);
    assert forall|i: int| 0 <= i<hs.len() implies {
        let e = #[trigger] hs[i]; (m.accept)(memory(m, e.actor, hs, i as nat), e)
    } by {
        let e = hs[i];
        let p = e.actor;
        let value = comparison_value(b, p);
        if p == at(Replica::R3) {
            issuer_memory(m, b, i as nat); prefix_index(i);
        } else {
            assert(i >= 2); let j = (i - 2) as nat; let base = stock(value); let es = stock_first_events(b, value);
            assert(shares_role(stock(comparison_value(b, p)), m, p));
            private_stock_history(b, base, m, p, j);
            assert(accepted(base, es));
            assert((base.accept)(memory(base, p, es, j), es[j as int]));
            assert(crate::confirmation::transport_event(e)) by {
                let t = checkpoint_states(b);
                let a = actions_to_crash(b);
                assert(enabled(t[i], a[i]) && process_step(t[i], a[i]) == e);
            }
            assert(implements_step(base, m, memory(base, p, es, j), e));
        }
    }
    let value = first_value(b);
    let base = stock(value);
    let es = stock_first_events(b, value);
    assert(comparison_value(b, c) == value);
    assert(shares_role(stock(comparison_value(b, c)), m, c));
    assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m, b, k)) by {
        if k >= 2 { private_stock_history(b, base, m, c, (k - 2) as nat); assert(!(base.done)(memory(base, c, es, (k - 2) as nat))); }
        else { reveal_with_fuel(memory, 2); assert(!(base.done)(memory(base, c, es, 0))); }
    }
    private_stock_history(b, base, m, c, 11); private_stock_history(b, base, m, c, 12);
    let end = if (base.done)(memory(base, c, es, 11)) { 11nat} else {12nat};
    assert(first_return_len(m, b) == end+2);
    let t = stock_first_states(b, value);
    let (r, j) = choose|r: Replica, j: int| crate::first_quorum(b.branch).contains(r) && 0 <= j <= end
        && #[trigger] (t[j].locals)(r) == first(memory(base, c, es, end));
    assert(first_result(m, first, b) == value);
    assert(during_sr1(b, 10, r) == first_result(m, first, b));
}

}
