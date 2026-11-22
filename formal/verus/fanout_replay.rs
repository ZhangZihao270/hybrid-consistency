use vstd::prelude::*;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;

verus! {

// Move only C1's three initial sends across R3's copy receipt and notice
// send. No delivery to a replica is moved across another event at that
// replica. At step 5 even the physical network has rejoined the original.
pub open spec fn old_index(i: nat) -> nat {
    if i < 3 { i + 2 } else if i < 5 { (i - 3) as nat } else { i }
}

pub open spec fn actions(b: Fork) -> Seq<Action<Wire>> {
    Seq::new(17, |i: int| actions_to_crash(b)[old_index(i as nat) as int])
}

pub open spec fn net(b: Fork, k: nat) -> Network<int, Wire> {
    if k >= 5 { state_after(b, k) } else {
        let base = state_after(b, if k == 4 { 1nat } else { 0nat });
        let p = base.pending;
        let p = if k >= 1 { p.insert(3, packet_for(b, 3)) } else { p };
        let p = if k >= 2 { p.insert(4, packet_for(b, 4)) } else { p };
        let p = if k >= 3 { p.insert(5, packet_for(b, 5)) } else { p };
        Network { pending: p, ..base }
    }
}
pub open spec fn states(b: Fork) -> Seq<Network<int, Wire>> {
    Seq::new(18, |i: int| net(b, i as nat))
}
pub open spec fn events(b: Fork) -> Seq<ProcessStep<int, Wire>> {
    observations(states(b), actions(b))
}

pub proof fn same_physical_events(b: Fork)
    ensures trace(|x,w| cell(x,w), states(b), actions(b)), states(b)[0] == after_local_rmws(),
        forall|i: int| 0 <= i < 17 ==> #[trigger] events(b)[i] == checkpoint_observations(b)[old_index(i as nat) as int],
{
    prefix_transport_is_enabled(b);
    assert forall|i: int| 0 <= i < 17 implies {
        let a = #[trigger] actions(b)[i];
        enabled(states(b)[i], a) && states(b)[i+1] == advance(|x,w| cell(x,w), states(b)[i], a)
            && events(b)[i] == checkpoint_observations(b)[old_index(i as nat) as int]
    } by {
        prefix_index(i);
        let n = net(b, i as nat);
        let u = advance(|x,w| cell(x,w), n, actions(b)[i]);
        assert(u.pending =~= states(b)[i+1].pending);
        assert(u.locals =~= states(b)[i+1].locals);
    }
}

pub open spec fn local_index(p: Process, k: nat) -> nat {
    if k >= 5 { k } else if p == Process::FirstClient {
        if k < 3 { k + 2 } else { 5 }
    } else if k == 4 { 1 } else { 0 }
}

pub proof fn same_local_history<S>(m: LocalProtocol<S,int,Wire>, b: Fork, p: Process, k: nat)
    requires k <= 17,
    ensures memory(m,p,events(b),k) == memory(m,p,checkpoint_observations(b),local_index(p,k)),
    decreases k,
{
    let es = events(b);
    let old = checkpoint_observations(b);
    same_physical_events(b);
    if k <= 5 {
        prefix_index(k as int);
        assert forall|i: int| 0 <= i < 5 implies #[trigger] es[i] == old[old_index(i as nat) as int] by {};
        reveal_with_fuel(memory, 6);
    } else {
        let i = (k-1) as nat;
        same_local_history(m,b,p,i);
        assert(es[i as int] == old[i as int]);
    }
}

pub proof fn retiming_preserves_service<S>(m: LocalProtocol<S,int,Wire>, b: Fork, value: spec_fn(S)->int)
    requires accepted(m,checkpoint_observations(b)), completed_quorum_sample(m,value,b),
    ensures accepted(m,events(b)), trace(|x,w| cell(x,w),states(b),actions(b)),
        !(m.done)(memory(m,Process::FirstClient,events(b),3)),
        (m.done)(memory(m,Process::FirstClient,events(b),first_return_len(m,b))),
        value(memory(m,Process::FirstClient,events(b),first_return_len(m,b))) == first_result(m,value,b),
        net(b,3).pending.contains_key(0) && net(b,3).pending.contains_key(1),
        forall|p: Process| #[trigger] memory(m,p,events(b),17) == memory(m,p,checkpoint_observations(b),17),
{
    let es = events(b);
    let old = checkpoint_observations(b);
    same_physical_events(b);
    assert forall|i: int| 0 <= i < es.len() implies {
        let e = #[trigger] es[i];
        (m.accept)(memory(m,e.actor,es,i as nat),e)
    } by {
        let j = old_index(i as nat);
        assert(es[i] == old[j as int]);
        if i < 5 { prefix_index(i); }
        assert(local_index(es[i].actor,i as nat) == j);
        same_local_history(m,b,es[i].actor,i as nat);
        assert((m.accept)(memory(m,old[j as int].actor,old,j),old[j as int]));
    }
    same_local_history(m,b,Process::FirstClient,3);
    assert(!(m.done)(first_client_at(m,b,5)));
    same_local_history(m,b,Process::FirstClient,first_return_len(m,b));
    assert forall|p: Process| #[trigger] memory(m,p,es,17) == memory(m,p,old,17) by { same_local_history(m,b,p,17); }
}

}
