use vstd::prelude::*;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::observation::{keep_pending, keep_pending_commutes};
use crate::scheduling::untouched_slot;

verus! {

// Compare two orders of exactly the same events. No guard reads another
// process's memory, even when the protocol stores its entire local history.
proof fn inbox_and_other_actors<S, L, I>(
    m: LocalProtocol<S, L, I>, receipt: ProcessStep<L, I>, work: Seq<ProcessStep<L, I>>, p: Process, k: nat,
)
    requires k <= work.len(), forall|j: int| 0 <= j < work.len() ==> (#[trigger] work[j]).actor != receipt.actor,
    ensures ({
        let early = memory(m, p, seq![receipt] + work, k + 1);
        let late = memory(m, p, work.push(receipt), k);
        if p == receipt.actor {
            late == (m.initial)(p) && early == (m.update)(late, receipt)
        } else { early == late }
    }),
    decreases k,
{
    if k > 0 {
        inbox_and_other_actors(m, receipt, work, p, (k - 1) as nat);
        assert((seq![receipt] + work)[k as int] == work[k - 1]);
        assert(work.push(receipt)[k - 1] == work[k - 1]);
    } else { reveal_with_fuel(memory, 2); }
}

proof fn same_handlers_in_either_order<S, L, I>(
    m: LocalProtocol<S, L, I>, receipt: ProcessStep<L, I>, work: Seq<ProcessStep<L, I>>,
)
    requires forall|j: int| 0 <= j < work.len() ==> (#[trigger] work[j]).actor != receipt.actor,
    ensures
        accepted(m, seq![receipt] + work) == accepted(m, work.push(receipt)),
        forall|p: Process| memory(m, p, seq![receipt] + work, work.len() + 1)
            == #[trigger] memory(m, p, work.push(receipt), work.len() + 1),
{
    let early = seq![receipt] + work; let late = work.push(receipt); let n = work.len();
    assert forall|i: int| 0 <= i < n implies {
        let e = #[trigger] work[i];
        (m.accept)(memory(m, e.actor, early, (i + 1) as nat), e)
            == (m.accept)(memory(m, e.actor, late, i as nat), e)
    } by { inbox_and_other_actors(m, receipt, work, work[i].actor, i as nat); }
    inbox_and_other_actors(m, receipt, work, receipt.actor, n);
    if accepted(m, early) {
        assert forall|i: int| 0 <= i < late.len() implies {
            let e = #[trigger] late[i]; (m.accept)(memory(m, e.actor, late, i as nat), e)
        } by {
            if i < n { assert(late[i] == work[i] && early[i+1] == work[i]); }
            else { assert(early[0] == receipt && late[i] == receipt); }
        }
    }
    if accepted(m, late) {
        assert forall|i: int| 0 <= i < early.len() implies {
            let e = #[trigger] early[i]; (m.accept)(memory(m, e.actor, early, i as nat), e)
        } by {
            if i > 0 { assert(early[i] == work[i-1] && late[i-1] == work[i-1]); }
            else { assert(early[0] == receipt && late[n as int] == receipt); }
        }
    }
    assert forall|p: Process| memory(m, p, early, n+1) == #[trigger] memory(m, p, late, n+1)
        by { inbox_and_other_actors(m, receipt, work, p, n); }
}

proof fn client_and_slot_stay_available<L, I>(
    update: spec_fn(L, I) -> L, states: Seq<Network<L, I>>, a: Seq<Action<I>>, id: nat, k: nat,
)
    requires trace(update, states, a), !states[0].first_stopped && !states[0].pending.contains_key(id), k <= a.len(),
        forall|i: int| 0 <= i < a.len() ==> untouched_slot(#[trigger] a[i], id)
            && process_step(states[i], a[i]).actor != Process::FirstClient,
    ensures !states[k as int].first_stopped && !states[k as int].pending.contains_key(id),
    decreases k,
{
    if k > 0 {
        let j = k - 1;
        client_and_slot_stay_available(update, states, a, id, j as nat);
        let step = a[j];
        assert(untouched_slot(step, id) && process_step(states[j], step).actor != Process::FirstClient);
        assert(states[k as int] == advance(update, states[j], step));
        match step { Action::Send(slot, _) | Action::Deliver(slot) => { assert(slot != id); }, _ => {} }
    }
}

pub open spec fn park_reply<L, I>(states: Seq<Network<L, I>>, id: nat, reply: Packet<I>) -> Seq<Network<L, I>> {
    states.map(|i: int, s| keep_pending(s, id, reply)).push(states.last())
}

// C1 receives a reply either before or after arbitrary work at other
// processes. Each required send and delivery is executed in both orders,
// including all replica-to-replica traffic, with the real queue contents.
pub proof fn move_inbox_delivery_across_replica_work<S, L, I>(
    m: LocalProtocol<S, L, I>, update: spec_fn(L, I) -> L,
    pre: Network<L, I>, id: nat, states: Seq<Network<L, I>>, a: Seq<Action<I>>,
)
    requires enabled(pre, Action::Deliver(id)), pre.pending[id].to == Process::FirstClient,
        pre.pending[id].path == Path::FirstReadReply, states[0] == advance(update, pre, Action::Deliver(id)),
        trace(update, states, a),
        forall|i: int| 0 <= i < a.len() ==> untouched_slot(#[trigger] a[i], id)
            && process_step(states[i], a[i]).actor != Process::FirstClient,
    ensures ({
        let receipt = Action::Deliver(id);
        let early = seq![process_step(pre, receipt)] + observations(states, a);
        let parked = park_reply(states, id, pre.pending[id]);
        let late = observations(parked, a.push(receipt));
        parked[0] == pre && parked.last() == states.last() && trace(update, parked, a.push(receipt))
            && (forall|i: int| 0 <= i <= a.len() ==> #[trigger] packet_at(parked[i], id) == Some(pre.pending[id]))
            && late == observations(states, a).push(process_step(pre, receipt))
            && accepted(m, early) == accepted(m, late)
            && forall|p: Process| #[trigger] memory(m, p, early, early.len()) == memory(m, p, late, late.len())
    }),
{
    let n = a.len(); let rec = Action::Deliver(id); let packet = pre.pending[id];
    let states2 = park_reply(states, id, packet); let acts = a.push(rec);
    let first = process_step(pre, rec); let work = observations(states, a);
    assert(states2[0].pending =~= pre.pending);
    assert(states2[0].locals =~= pre.locals);
    client_and_slot_stay_available(update, states, a, id, n);
    assert forall|i: int| 0 <= i < acts.len() implies {
        let step = #[trigger] acts[i];
        enabled(states2[i], step) && states2[i+1] == advance(update, states2[i], step)
            && process_step(states2[i], step) == work.push(first)[i]
    } by {
        if i < n {
            assert(acts[i] == a[i] && enabled(states[i], a[i]));
            assert(states[i+1] == advance(update, states[i], a[i]));
            assert(untouched_slot(a[i], id));
            keep_pending_commutes(update, states[i], a[i], id, packet);
        } else {
            let post = advance(update, states2[i], rec);
            assert(states[i] == states.last());
            assert(post.pending =~= states[i].pending);
            assert(post.locals =~= states[i].locals);
        }
    }
    assert(observations(states2, acts) =~= work.push(first));
    assert forall|i: int| 0 <= i < work.len() implies (#[trigger] work[i]).actor != first.actor
        by { assert(process_step(states[i], a[i]).actor != Process::FirstClient); }
    same_handlers_in_either_order(m, first, work);
}

// In each manuscript trace R3 sends its own SR1 reply at step 10. The
// responding survivor's reply has already been issued. C1 can receive
// that survivor packet on either side of R3's send. Both end with the
// very same concrete queue and the same private memory at every process.
pub proof fn first_survivor_receipt_commutes_with_r3_send<S>(b: Fork, m: LocalProtocol<S, int, Wire>)
    ensures ({
        let states = checkpoint_states(b); let a = actions_to_crash(b);
        let es = checkpoint_observations(b);
        let current = LocalProtocol { initial: |p| memory(m, p, es, 10), ..m };
        let id = if b.branch == crate::Branch::Alpha { 7nat } else { 6nat };
        let rec = Action::Deliver(id); let pre = states[10]; let update = |x, w| cell(x, w);
        let early = advance(update, pre, rec);
        let earlier = seq![process_step(pre, rec), process_step(early, a[10])];
        let actual = seq![es[10], es[11]];
        trace(update, seq![pre, early, states[12]], seq![rec, a[10]])
            && a[11] == rec && es[11].incoming == Some(packet_for(b, id))
            && accepted(current, earlier) == accepted(current, actual)
            && (forall|p: Process| #[trigger] memory(current, p, actual, 2) == memory(current, p, earlier, 2))
    }),
{
    let states = checkpoint_states(b); let a = actions_to_crash(b); let es = checkpoint_observations(b);
    let id = if b.branch == crate::Branch::Alpha { 7nat } else { 6nat }; let rec = Action::Deliver(id);
    let update = |x, w| cell(x, w);
    let pre = states[10]; let early = advance(update, pre, rec);
    let after = advance(update, early, a[10]); let work = seq![a[10]]; let s = seq![early, after];
    assert(after.pending =~= states[12].pending);
    assert(after.locals =~= states[12].locals);
    assert forall|i: int| 0 <= i < work.len() implies {
        let step = #[trigger] work[i]; enabled(s[i], step) && s[i+1] == advance(update, s[i], step)
            && untouched_slot(step, id) && process_step(s[i], step).actor != Process::FirstClient
    } by { assert(i == 0); }
    let current = LocalProtocol { initial: |p| memory(m, p, es, 10), ..m };
    move_inbox_delivery_across_replica_work(current, update, pre, id, s, work);
    let parked = park_reply(s, id, pre.pending[id]);
    assert(parked[1].pending =~= states[11].pending);
    assert(parked[1].locals =~= states[11].locals);
    assert(observations(parked, work.push(rec)) =~= seq![es[10], es[11]]);
    assert(seq![process_step(pre, rec)] + observations(s, work) =~=
        seq![process_step(pre, rec), process_step(early, a[10])]);
    assert(seq![pre, early, states[12]] =~= seq![pre] + s);
    let moved = seq![rec, a[10]]; let ms = seq![pre, early, states[12]];
    assert forall|i: int| 0 <= i < moved.len() implies {
        let step = #[trigger] moved[i]; enabled(ms[i], step) && ms[i+1] == advance(update, ms[i], step)
    } by { assert(i == 0 || i == 1); }
}

}
