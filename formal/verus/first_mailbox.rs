// What can make an already submitted read depend on a further wire input?
// The reference can run arbitrary real service at every live process.
use vstd::prelude::*;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::fair_read::{self as fair, Run, Runnable};
use crate::independent_read::{self as read, State};
use crate::promotion_wait::{self as wait, Relation};
use crate::read_call::{Event, Program};
use crate::read_nonblocking as nb;

verus! {

pub open spec fn posted<S>(m:Program<S>) -> nb::Region<State<S>> {
    |x:State<S>| (m.done)((x.cfg.private)(Process::FirstClient))
}
// The first client remains nonfaulty until its publication. The genuine
// protocol and the queue still guard every transition. Stops after return
// are permitted. C1 has already sent its entire invocation.
pub open spec fn active_step<S>(m:Program<S>) -> Relation<State<S>,Event> {
    |x,a,y| read::service_step(m)(x,a,y) && (a!=Action::StopFirstClient || posted(m)(x))
}
pub open spec fn submitted<S>(x:State<S>) -> bool {
    !x.cfg.net.first_stopped && x.first_requested==x.calls.first &&
        exists|r:crate::Replica,s:crate::Replica| r!=s && x.first_requested.contains(r) && x.first_requested.contains(s)
            && #[trigger] live(x.cfg.net,at(r)) && #[trigger] live(x.cfg.net,at(s))
}
pub open spec fn honest<S>(m:Program<S>,e:Run<S>) -> bool {
    forall|i:nat| #[trigger] (e.action)(i)==Action::<Wire>::StopFirstClient ==> posted(m)((e.state)(i))
}
pub open spec fn fair_opportunity<S>(m:Program<S>,run:Runnable,x:State<S>) -> bool {
    exists|e:Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && honest(m,e)
}
// Scope may be the reachable configurations of this workload. This is the
// positive hybrid progress assumption, separately from existence of a fair run.
pub open spec fn first_availability<S>(m:Program<S>,run:Runnable,scope:nb::Region<State<S>>) -> bool {
    forall|x:State<S>,e:Run<S>| scope(x) && submitted(x) && #[trigger] fair::execution(m,e,x)
        && fair::fair(e,run) && honest(m,e) ==> exists|i:nat| #[trigger] posted(m)((e.state)(i))
}
pub proof fn fair_first_service<S>(m:Program<S>,run:Runnable,scope:nb::Region<State<S>>,x:State<S>)
    requires scope(x),submitted(x),first_availability(m,run,scope),fair_opportunity(m,run,x),
    ensures nb::possible(active_step(m),posted(m),x),
{
    let e=choose|e:Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && honest(m,e);
    let k=choose|i:nat| #[trigger] posted(m)((e.state)(i));
    let p=wait::Path{states:Seq::new(k+1,|j:int|(e.state)(j as nat)),actions:Seq::new(k,|j:int|(e.action)(j as nat))};
    assert forall|j:int| 0<=j<k implies active_step(m)(p.states[j],#[trigger] p.actions[j],p.states[j+1]) by {
        assert(read::service_step(m)((e.state)(j as nat),(e.action)(j as nat),(e.state)(j as nat+1)));
    }
    nb::from_path(active_step(m),posted(m),p,0);
}
}
