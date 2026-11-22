use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::*;
use crate::delivery::*;
use crate::progress::*;
use crate::protocol::*;
use crate::service::*;
use crate::survivors::*;

verus! {

// Auxiliary progress run: R3 applies the very same copy. The separately
// schedulable background send at index 1 has not run when R3 crashes.
pub open spec fn unsent_actions(b: Fork) -> Seq<Action<Wire>> {
    actions_to_crash(b).remove(1)
}

pub open spec fn unsent_states(b: Fork) -> Seq<Network<int, Wire>> {
    let original = checkpoint_states(b);
    Seq::new((original.len() - 1) as nat, |i: int| {
        let net = original[if i < 1 { i } else { i + 1 }];
        Network { pending: net.pending.remove(2), ..net }
    })
}

pub open spec fn unsent_events(b: Fork) -> Seq<ProcessStep<int, Wire>> {
    observations(unsent_states(b), unsent_actions(b))
}

pub proof fn unsent_transport(b: Fork)
    ensures ({
        let t = unsent_states(b);
        let a = unsent_actions(b);
        trace(|v, w| cell(v, w), t, a) && t[0] == after_local_rmws()
            && unsent_events(b) == checkpoint_observations(b).remove(1)
            && t.last() == (Network { pending: checkpoint_end(b).pending.remove(2), ..checkpoint_end(b) })
            && forall|id: nat| #[trigger] t.last().pending.contains_key(id) ==> !live(t.last(), t.last().pending[id].to)
    }),
{
    let t = unsent_states(b);
    let a = unsent_actions(b);
    let es = unsent_events(b);
    prefix_transport_is_enabled(b);
    assert(t[0].pending =~= checkpoint_states(b)[0].pending);
    assert forall|i: int| 0 <= i < a.len() implies {
        let x = #[trigger] a[i];
        enabled(t[i], x) && t[i + 1] == advance(|v, w| cell(v, w), t[i], x)
            && es[i] == checkpoint_observations(b).remove(1)[i]
    } by {
        prefix_index(i);
        let next = advance(|v, w| cell(v, w), t[i], a[i]);
        assert(next.pending =~= t[i + 1].pending);
        assert(next.locals =~= t[i + 1].locals);
    }
    assert(es =~= checkpoint_observations(b).remove(1));
    assert forall|id: nat| #[trigger] t.last().pending.contains_key(id) implies !live(t.last(), t.last().pending[id].to) by {};
}

// Memory of every other process is insensitive to deletion of a step at R3.
pub proof fn other_memory_omits_step<S, L, I>(
    m: LocalProtocol<S, L, I>, es: Seq<ProcessStep<L, I>>, j: int, p: Process, k: nat,
)
    requires 0 <= j < es.len(), es[j].actor != p, k < es.len(),
    ensures memory(m, p, es.remove(j), k) == memory(m, p, es, if k < j { k } else { k + 1 }),
    decreases k,
{
    if k > 0 {
        other_memory_omits_step(m, es, j, p, (k - 1) as nat);
        assert(es.remove(j)[k - 1] == es[if k <= j { k as int-1 } else { k as int }]);
    }
    if k == j { reveal_with_fuel(memory, 2); }
}

pub open spec fn after_copy<S>(m: LocalProtocol<S, int, Wire>, b: Fork) -> S {
    let e = checkpoint_observations(b)[0];
    (m.update)((m.initial)(at(Replica::R3)), e)
}

// Exact local R3 obligations after applying the copy. Read the request,
// send the normal reply from the shared cell, and allow the crash event.
// Other actors and the receipt at C1 occur nowhere in these guards.
pub open spec fn serves_before_sending_status<S>(m: LocalProtocol<S, int, Wire>, b: Fork) -> bool {
    let es = checkpoint_observations(b);
    let ready = after_copy(m, b);
    let requested = (m.update)(ready, es[7]);
    let answered = (m.update)(requested, es[10]);
    (m.accept)(ready, es[7]) && (m.accept)(requested, es[10]) && (m.accept)(answered, es[15])
}

proof fn r3_without_send<S>(m: LocalProtocol<S, int, Wire>, b: Fork, k: nat)
    requires k <= unsent_events(b).len(),
    ensures ({
        let es = checkpoint_observations(b);
        let p = at(Replica::R3);
        let ready = after_copy(m, b);
        let requested = (m.update)(ready, es[7]);
        let sent = (m.update)(requested, es[10]);
        memory(m, p, unsent_events(b), k) == if k == 0 { (m.initial)(p) } else if k <= 6 { ready }
            else if k <= 9 { requested } else if k <= 14 { sent } else { (m.update)(sent, es[15]) }
    }),
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat; r3_without_send(m, b, j); prefix_index(j as int);
    }
}

pub proof fn unsent_prefix_from_sender<S>(m: LocalProtocol<S, int, Wire>, b: Fork)
    requires accepted(m, checkpoint_observations(b)),
    ensures
        accepted(m, unsent_events(b)) == serves_before_sending_status(m, b),
        forall|p: Process| p != at(Replica::R3) ==>
            (#[trigger] (resume_at(m, unsent_events(b)).initial)(p)) == (resume_at(m, checkpoint_observations(b)).initial)(p),
{
    let es = checkpoint_observations(b);
    let hs = unsent_events(b);
    let r3 = at(Replica::R3);
    unsent_transport(b);
    if serves_before_sending_status(m, b) {
        assert forall|i: int| 0 <= i < hs.len() implies {
            let e = #[trigger] hs[i]; (m.accept)(memory(m, e.actor, hs, i as nat), e)
        } by {
            let p = hs[i].actor; let j = if i < 1 { i } else { i + 1 };
            assert(hs[i] == es[j] && (m.accept)(memory(m, p, es, j as nat), es[j]));
            if p == r3 { r3_without_send(m, b, i as nat); prefix_index(i); }
            else { other_memory_omits_step(m, es, 1, p, i as nat); }
        }
    }
    if accepted(m, hs) {
        r3_without_send(m, b, 6); r3_without_send(m, b, 9); r3_without_send(m, b, 14);
        assert((m.accept)(memory(m, r3, hs, 6), hs[6]) && (m.accept)(memory(m, r3, hs, 9), hs[9])
            && (m.accept)(memory(m, r3, hs, 14), hs[14]));
    }
    assert forall|p: Process| p != r3 implies
        (#[trigger] (resume_at(m, hs).initial)(p)) == (resume_at(m, es).initial)(p) by {
        other_memory_omits_step(m, es, 1, p, hs.len());
    }
}

// This is an actual admissible auxiliary prefix whenever the sender passes
// the three local guards. At its cut nobody has received a status. The
// transport coincides with after_receipt, but the private states do not.
pub proof fn unsent_service_yields_pair<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        serves_before_sending_status(m, alpha(n)),
        response_path(resume_at(m, unsent_events(alpha(n))), result, unsent_states(alpha(n)).last(), delayed_slots(), s, a, v),
    ensures accepted(m, unsent_events(alpha(n))), incompatible_completions(n, m, first, result, a, v),
{
    hide(accepted); hide(memory); hide(incompatible_completions);
    let b = alpha(n);
    let es = unsent_events(b);
    let refm = resume_at(m, es);
    let before = resume_at(m, checkpoint_observations(b));
    let obs = observations(s, a);
    let c = Process::SecondClient;
    unsent_transport(b); unsent_prefix_from_sender(m, b); alpha_receipt_cut(n);
    assert(after_receipt(n).locals =~= checkpoint_end(b).locals);
    assert(s[0] == after_receipt(n));
    postcrash_schedule_has_only_live_actors(|x, w| cell(x, w), s, a, a.len());
    assert forall|i: int| 0 <= i < obs.len() implies {
        let e = #[trigger] obs[i]; (before.accept)(memory(before, e.actor, obs, i as nat), e)
    } by {
        let e = obs[i]; assert(survivor_actor(process_step(s[i], a[i]).actor));
        memory_from_same_local_state(refm, before, e.actor, obs, i as nat);
        assert((refm.accept)(memory(refm, e.actor, obs, i as nat), e)) by { reveal(accepted); }
    }
    assert forall|k: nat| k < obs.len() implies result(#[trigger] memory(before, c, obs, k)).is_none() by {
        memory_from_same_local_state(refm, before, c, obs, k);
        assert(result(memory(refm, c, obs, k)).is_none());
    }
    memory_from_same_local_state(refm, before, c, obs, obs.len());
    assert(response_path(before, result, after_receipt(n), delayed_slots(), s, a, v)) by { reveal(accepted); }
    pair_from_ordinary_path(n, m, first, result, s, a, v);
}

pub proof fn fair_unsent_service_yields_pair<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        serves_before_sending_status(m, alpha(n)),
        admissible_service(unsent_states(alpha(n)).last(), resume_at(m, unsent_events(alpha(n))), result, e),
        delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| sr2_result(resume_at(m, unsent_events(alpha(n))), result, observations(s, a)).is_some()),
    ensures exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v),
{
    hide(accepted); hide(trace); hide(memory); hide(eventually_responds); hide(admissible_service);
    hide(delivery_fair); hide(process_fair); hide(sr2_result); hide(incompatible_completions);
    let b = alpha(n);
    let net = unsent_states(b).last();
    let local = resume_at(m, unsent_events(b));
    assert(after_crash(net));
    let (k, v) = finite_fair_service(net, local, result, e, runnable);
    let s = states_through(e, k);
    let a = actions_before(e, k);
    assert(response_path(local, result, net, delayed_slots(), s, a, v));
    unsent_service_yields_pair(n, m, first, result, s, a, v);
}

}
