use vstd::prelude::*;
use crate::{delivery::*,progress};
use crate::independent_read::{self as read,State};
use crate::read_call::{Event,Net,Program};
use crate::promotion_wait::Path;

verus! {

pub type Runnable = spec_fn(Net,Process)->bool;
pub type Block<S> = Path<State<S>,Event>;
pub struct Run<S> { pub state:spec_fn(nat)->State<S>, pub action:spec_fn(nat)->Event }
pub open spec fn physical<S>(e:Run<S>) -> progress::Execution<int,crate::checkpoint::Wire> {
    progress::Execution{state:|i:nat|(e.state)(i).cfg.net,action:e.action}
}
pub open spec fn execution<S>(m:Program<S>,e:Run<S>,x:State<S>) -> bool {
    (e.state)(0)==x && forall|i:nat| read::service_step(m)((e.state)(i),#[trigger] (e.action)(i),(e.state)(i+1))
}
pub open spec fn fair<S>(e:Run<S>,run:Runnable) -> bool {
    progress::delivery_fair(physical(e)) && progress::process_fair(physical(e),run)
}
pub(crate) open spec fn initial_block<S>(e:Run<S>,k:nat) -> Block<S> {
    Path{states:Seq::new(k+1,|j:int|(e.state)(j as nat)),actions:Seq::new(k,|j:int|(e.action)(j as nat))}
}

}
