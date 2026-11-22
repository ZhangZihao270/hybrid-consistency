use vstd::prelude::*;
use crate::Replica;
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

pub open spec fn survivor_actor(p: Process) -> bool {
    p == Process::At(Replica::R1) || p == Process::At(Replica::R2) || p == Process::SecondClient
}

}
