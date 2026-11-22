use vstd::prelude::*;
use crate::{Branch, Replica};
use crate::delivery::*;

verus! {

#[verifier::reject_recursive_types(S)]
#[verifier::reject_recursive_types(L)]
#[verifier::reject_recursive_types(I)]
pub struct LocalProtocol<S, L, I> {
    pub initial: spec_fn(Process) -> S,
    pub accept: spec_fn(S, ProcessStep<L, I>) -> bool,
    pub update: spec_fn(S, ProcessStep<L, I>) -> S,
    pub done: spec_fn(S) -> bool,
}

// The protocol keeps arbitrary private memory, including any local clock
// readings or failure suspicions received as explicit scheduled inputs.
pub open spec fn memory<S, L, I>(
    m: LocalProtocol<S, L, I>, who: Process, obs: Seq<ProcessStep<L, I>>, k: nat,
) -> S
    decreases k,
{
    if k == 0 {
        (m.initial)(who)
    } else {
        let before = memory(m, who, obs, (k - 1) as nat);
        let ev = obs[k - 1];
        if ev.actor == who { (m.update)(before, ev) } else { before }
    }
}

pub proof fn memory_on_common_prefix<S, L, I>(
    m: LocalProtocol<S, L, I>, p: Process, es: Seq<ProcessStep<L, I>>, hs: Seq<ProcessStep<L, I>>, k: nat,
)
    requires k <= es.len(), k <= hs.len(), forall|i: int| 0 <= i < k ==> #[trigger] es[i] == #[trigger] hs[i],
    ensures memory(m, p, es, k) == memory(m, p, hs, k),
    decreases k,
{
    if k > 0 { memory_on_common_prefix(m, p, es, hs, (k - 1) as nat); }
}

pub(crate) proof fn memory_during_quiescence<S,L,I>(m:LocalProtocol<S,L,I>,es:Seq<ProcessStep<L,I>>,p:Process,lo:nat,hi:nat)
    requires lo<=hi<=es.len(),forall|i:int| lo<=i<hi ==> (#[trigger] es[i]).actor!=p,
    ensures memory(m,p,es,lo)==memory(m,p,es,hi),
    decreases hi-lo,
{
    if lo<hi {memory_during_quiescence(m,es,p,lo,(hi-1) as nat);assert(es[hi-1].actor!=p);}
}

pub proof fn memory_from_same_local_state<S, L, I>(
    m: LocalProtocol<S, L, I>, other: LocalProtocol<S, L, I>, p: Process, es: Seq<ProcessStep<L, I>>, k: nat,
)
    requires k <= es.len(), m.update == other.update, (m.initial)(p) == (other.initial)(p),
    ensures memory(m, p, es, k) == memory(other, p, es, k),
    decreases k,
{
    if k > 0 { memory_from_same_local_state(m, other, p, es, (k - 1) as nat); }
}

pub open spec fn pending_before_end<S, L, I>(
    m: LocalProtocol<S, L, I>, result: spec_fn(S) -> Option<int>, es: Seq<ProcessStep<L, I>>,
) -> bool {
    forall|i: nat| i < es.len() ==> result(#[trigger] memory(m, Process::SecondClient, es, i)).is_none()
}

pub open spec fn accepted<S, L, I>(
    m: LocalProtocol<S, L, I>, obs: Seq<ProcessStep<L, I>>,
) -> bool {
    forall|i: int| 0 <= i < obs.len() ==> {
        let event = #[trigger] obs[i];
        (m.accept)(memory(m, event.actor, obs, i as nat), event)
    }
}

pub open spec fn same_callbacks<S,L,I>(m:LocalProtocol<S,L,I>, other:LocalProtocol<S,L,I>, s:S, e:ProcessStep<L,I>) -> bool {
    (m.accept)(s,e)==(other.accept)(s,e) && (m.update)(s,e)==(other.update)(s,e)
}

pub proof fn identical_callbacks_on_log<S,L,I>(
    m:LocalProtocol<S,L,I>, other:LocalProtocol<S,L,I>, es:Seq<ProcessStep<L,I>>, p:Process, k:nat,
)
    requires m.initial==other.initial, k<=es.len(),
        forall|i:int,s:S| 0<=i<es.len() ==> #[trigger] same_callbacks(m,other,s,es[i]),
    ensures memory(m,p,es,k)==memory(other,p,es,k),
    decreases k,
{
    if k>0 {
        let j=(k-1) as nat; identical_callbacks_on_log(m,other,es,p,j);
        assert(same_callbacks(m,other,memory(m,p,es,j),es[j as int]));
    }
}

pub open spec fn completes<S, L, I>(
    m: LocalProtocol<S, L, I>, obs: Seq<ProcessStep<L, I>>,
) -> bool {
    (m.done)(memory(m, Process::FirstClient, obs, obs.len()))
}

pub proof fn deterministic_crash_completion_replays<S, L, I>(
    update: spec_fn(L, I) -> L, m: LocalProtocol<S, L, I>,
    states: Seq<Network<L, I>>, actions: Seq<Action<I>>,
)
    requires
        trace(update, states, actions),
        accepted(m, observations(states, actions)),
        completes(m, observations(states, actions)),
    ensures
        trace(update, slow_prefix(states), actions),
        accepted(m, observations(slow_prefix(states), actions)),
        completes(m, observations(slow_prefix(states), actions)),
{
    replay_crash_prefix_with_slow_replica(update, states, actions);
    replay_preserves_process_observations(states, actions);
}

pub open spec fn counts_replies() -> LocalProtocol<nat, int, int> {
    LocalProtocol {
        initial: |p: Process| 0nat,
        accept: |count: nat, e: ProcessStep<int, int>| count < 2,
        update: |count: nat, e: ProcessStep<int, int>|
            if e.incoming.is_some() && e.incoming.unwrap().path == Path::FirstReadReply {
                count + 1
            } else { count },
        done: |count: nat| count == 2,
    }
}

pub proof fn stateful_client_completes_on_second_reply(b: Branch, value: int)
    ensures ({
        let actions = fixture_actions();
        let states = fixture_states(b, value);
        let initial = observations(states, actions);
        let m = counts_replies();
        !completes(m, initial.take(1))
            && completes(m, initial)
            && completes(m, observations(slow_prefix(states), actions))
    }),
{
    let actions = fixture_actions();
    let states = fixture_states(b, value);
    let obs = observations(states, actions);
    let m = counts_replies();
    two_actual_replies_complete_and_replay(b, value);
    reveal_with_fuel(replay, 4);
    reveal_with_fuel(memory, 4);
    assert(obs[0].actor == Process::FirstClient && obs[1].actor == Process::FirstClient);
    assert(obs[0].incoming.unwrap().path == Path::FirstReadReply);
    assert(obs[1].incoming.unwrap().path == Path::FirstReadReply);
    assert forall|i: int| 0 <= i < obs.len() implies {
        let e = #[trigger] obs[i];
        (m.accept)(memory(m, e.actor, obs, i as nat), e)
    } by {
        assert(i == 0 || i == 1);
    }
    assert(completes(m, obs));
    deterministic_crash_completion_replays(|x, i| unchanged_int(x, i), m, states, actions);
}

pub open spec fn head_quiet_for<S, L, I>(
    m: LocalProtocol<S, L, I>, who: Process, first: ProcessStep<L, I>,
) -> bool {
    first.actor != who || (m.update)((m.initial)(who), first) == (m.initial)(who)
}

proof fn private_memory_ignores_quiet_head<S, L, I>(
    m: LocalProtocol<S, L, I>, who: Process, first: ProcessStep<L, I>,
    suffix: Seq<ProcessStep<L, I>>, k: nat,
)
    requires head_quiet_for(m, who, first), k <= suffix.len(),
    ensures memory(m, who, seq![first] + suffix, k + 1) == memory(m, who, suffix, k),
    decreases k,
{
    reveal_with_fuel(memory, 2);
    let all = seq![first] + suffix;
    let next = (k + 1) as nat;
    assert((next - 1) as nat == k);
    if k > 0 {
        let prev = (k - 1) as nat;
        private_memory_ignores_quiet_head(m, who, first, suffix, prev);
        assert((prev + 1) as nat == k);
        assert(memory(m, who, all, k) == memory(m, who, suffix, prev));
        assert(all[k as int] == suffix[k - 1]);
        let ev = suffix[k - 1];
        let old = memory(m, who, all, k);
        assert(memory(m, who, all, next) ==
            if ev.actor == who { (m.update)(old, ev) } else { old });
    } else {
        assert(all[0] == first);
        assert(memory(m, who, all, next) == (m.initial)(who));
    }
}

// A delivery may change memory at a process that will take no kept step.
// At other processes the checkpoint state observed by the read is unchanged.
pub proof fn stateful_suffix_drops_quiet_head<S, L, I>(
    m: LocalProtocol<S, L, I>, first: ProcessStep<L, I>, suffix: Seq<ProcessStep<L, I>>,
)
    requires
        head_quiet_for(m, Process::FirstClient, first),
        forall|i: int| 0 <= i < suffix.len() ==> head_quiet_for(m, (#[trigger] suffix[i]).actor, first),
        accepted(m, seq![first] + suffix),
        completes(m, seq![first] + suffix),
    ensures accepted(m, suffix), completes(m, suffix),
{
    let all = seq![first] + suffix;
    assert forall|i: int| 0 <= i < suffix.len() implies {
        let e = #[trigger] suffix[i];
        (m.accept)(memory(m, e.actor, suffix, i as nat), e)
    } by {
        let e = suffix[i];
        assert(all[i + 1] == e);
        assert((m.accept)(memory(m, e.actor, all, (i + 1) as nat), e));
        private_memory_ignores_quiet_head(m, e.actor, first, suffix, i as nat);
    }
    private_memory_ignores_quiet_head(m, Process::FirstClient, first, suffix, suffix.len());
}

pub proof fn ignored_recipient_cannot_block_stateful_suffix<S, L, I>(
    m: LocalProtocol<S, L, I>, first: ProcessStep<L, I>, suffix: Seq<ProcessStep<L, I>>,
)
    requires
        first.actor != Process::FirstClient,
        forall|i: int| 0 <= i < suffix.len() ==> (#[trigger] suffix[i]).actor != first.actor,
        accepted(m, seq![first] + suffix),
        completes(m, seq![first] + suffix),
    ensures accepted(m, suffix), completes(m, suffix),
{
    assert forall|i: int| 0 <= i < suffix.len() implies
        head_quiet_for(m, (#[trigger] suffix[i]).actor, first) by {};
    stateful_suffix_drops_quiet_head(m, first, suffix);
}

// Resume with measured private state after a real prefix, not a reinitialized client.
pub open spec fn resume_at<S, L, I>(
    m: LocalProtocol<S, L, I>, prefix: Seq<ProcessStep<L, I>>,
) -> LocalProtocol<S, L, I> {
    LocalProtocol { initial: |p: Process| memory(m, p, prefix, prefix.len()), ..m }
}

pub open spec fn survivor_actor(p: Process) -> bool {
    p == Process::At(Replica::R1) || p == Process::At(Replica::R2) || p == Process::SecondClient
}

pub proof fn memory_for_live_actor_agrees<S, L, I>(
    m: LocalProtocol<S, L, I>, a: Seq<ProcessStep<L, I>>, b: Seq<ProcessStep<L, I>>,
    later: Seq<ProcessStep<L, I>>, p: Process, k: nat,
)
    requires
        survivor_actor(p), k <= later.len(),
        memory(m, p, a, a.len()) == memory(m, p, b, b.len()),
    ensures memory(resume_at(m, a), p, later, k) == memory(resume_at(m, b), p, later, k),
    decreases k,
{
    if k > 0 {
        memory_for_live_actor_agrees(m, a, b, later, p, (k - 1) as nat);
    }
}

pub proof fn dead_private_history_cannot_change_live_continuation<S, L, I>(
    m: LocalProtocol<S, L, I>, a: Seq<ProcessStep<L, I>>, b: Seq<ProcessStep<L, I>>,
    later: Seq<ProcessStep<L, I>>,
)
    requires
        accepted(resume_at(m, a), later),
        forall|p: Process| #[trigger] survivor_actor(p) ==>
            memory(m, p, a, a.len()) == memory(m, p, b, b.len()),
        forall|i: int| 0 <= i < later.len() ==> survivor_actor((#[trigger] later[i]).actor),
    ensures
        accepted(resume_at(m, b), later),
        memory(resume_at(m, a), Process::SecondClient, later, later.len())
            == memory(resume_at(m, b), Process::SecondClient, later, later.len()),
{
    assert forall|i: int| 0 <= i < later.len() implies {
        let event = #[trigger] later[i];
        (m.accept)(memory(resume_at(m, b), event.actor, later, i as nat), event)
    } by {
        let event = later[i];
        memory_for_live_actor_agrees(m, a, b, later, event.actor, i as nat);
        assert((m.accept)(memory(resume_at(m, a), event.actor, later, i as nat), event));
    }
    memory_for_live_actor_agrees(m, a, b, later, Process::SecondClient, later.len());
}

}
