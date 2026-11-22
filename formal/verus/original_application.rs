use vstd::prelude::*;
use crate::{Replica, delivery::*};
use crate::first_assembly::{Lanes, Service};
use crate::first_mailbox as mail;
use crate::guarded_comparison as cmp;
use crate::independent_read::{self as read, State};
use crate::promotion_wait as wait;
use crate::read_call::{Event, Net, Program};

verus! {

// Only the existing R3 confirmation has a statically owned envelope.
pub open spec fn lanes() -> Lanes { map![2nat => Replica::R3, 3nat => Replica::R1, 4nat => Replica::R2] }

pub open spec fn weak_replica_step<S>() -> wait::Relation<State<S>, Event> {
    |x: State<S>, a: Event, _y: State<S>| {
        let e = process_step(x.cfg.net, a);
        e.actor is At && cmp::weak_work(e)
    }
}

pub(crate) proof fn quiet_cells<S>(m: Program<S>, x: State<S>, a: Event, y: State<S>)
    requires read::service_step(m)(x,a,y), !weak_replica_step()(x,a,y),
    ensures y.cfg.net.locals == x.cfg.net.locals,
{
    assert forall|r: Replica| (#[trigger] local_input(x.cfg.net,a,r)).is_none()
        || !(local_input(x.cfg.net,a,r).unwrap() is Copy) by {};
    assert(y.cfg.net.locals =~= x.cfg.net.locals);
}

// Remove only the service mask. The omitted replica takes no action in the
// copied interval. In particular no queued packet is deleted or renamed.
pub open spec fn all_available<S>(x: State<S>) -> State<S> {
    State { cfg: crate::ordinary_service::Configuration { net: Net { unavailable: None, ..x.cfg.net }, ..x.cfg }, ..x }
}

pub(crate) proof fn original_step<S>(m: Program<S>, x: State<S>, a: Event, y: State<S>)
    requires mail::active_step(m)(x,a,y),
    ensures mail::active_step(m)(all_available(x),a,all_available(y)),
        process_step(all_available(x).cfg.net,a) == process_step(x.cfg.net,a),
{
    let u = all_available(x); let v = read::next(m,u,a);
    assert(process_step(u.cfg.net,a) == process_step(x.cfg.net,a));
    assert(v.cfg.net.locals =~= y.cfg.net.locals);
    assert(v.cfg.private =~= y.cfg.private);
    assert(v == all_available(y));
}

pub(crate) proof fn cells_at<S>(m:Program<S>,p:Service<S>,k:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::active_step(m),p),
        !wait::uses(p,weak_replica_step()), k<p.states.len(),
    ensures p.states[k as int].cfg.net.locals==p.states[0].cfg.net.locals,
    decreases k,
{
    if k>0 {
        let i=k as int-1; cells_at(m,p,(k-1) as nat);
        assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));
        quiet_cells(m,p.states[i],p.actions[i],p.states[i+1]);
    }
}

}
