// Assemble the two majority executions from the histories of the processes
// that actually served them. The auxiliary caller never observes C1.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*};
use crate::early_crash as probe;
use crate::first_mailbox as mail;
use crate::first_splice::{Observation,Tape,after,plays};
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program};

verus! {

pub type Lanes = Map<nat,Replica>;
pub type Service<S> = wait::Path<State<S>,Event>;
pub open spec fn owners(l:Lanes) -> Map<nat,Process> {
    Map::new(l.dom().filter(|i:nat| l[i]==Replica::R3),|_i:nat|at(Replica::R3))
}
pub open spec fn entry<S>(m:Program<S>,l:Lanes) -> State<S> { State{owners:owners(l),..probe::entry(m)} }

// The physical prefix monitor is shared with the service-loss proof.
// Stopping a caller after its recorded return is an environment action.
pub open spec fn drive<S>(m:Program<S>,x:State<S>,a:Seq<Event>) -> State<S>
    decreases a.len(),
{
    if a.len()==0 {x} else {drive(m,read::next(m,x,a[0]),a.drop_first())}
}
pub open spec fn prefix<S>(m:Program<S>,x:State<S>,a:Seq<Event>,original:bool) -> bool
    decreases a.len(),
{
    if a.len()==0 {true} else {
        let e=a[0];let y=read::next(m,x,e);
        (if original && e==Action::StopFirstClient {enabled(x.cfg.net,e) && mail::posted(m)(x)}
            else {read::prefix_step(m)(x,e,y)}) && prefix(m,y,a.drop_first(),original)
    }
}
pub open spec fn actions(t:Tape) -> Seq<Event> { t.map_values(|e:Observation|e.action) }
pub proof fn prefix_concat<S>(m:Program<S>,x:State<S>,a:Seq<Event>,b:Seq<Event>,o:bool)
    ensures prefix(m,x,a+b,o)==(prefix(m,x,a,o) && prefix(m,drive(m,x,a),b,o)),
        drive(m,x,a+b)==drive(m,drive(m,x,a),b),
    decreases a.len(),
{
    if a.len()==0 {assert(a+b =~= b);} else {
        assert((a+b).drop_first() =~= a.drop_first()+b);prefix_concat(m,read::next(m,x,a[0]),a.drop_first(),b,o);
    }
}
pub proof fn native_prefix<S>(m:Program<S>,x:State<S>,t:Tape,o:bool)
    requires plays(m,x,t),
    ensures prefix(m,x,actions(t),o),drive(m,x,actions(t))==after(m,x,t),
    decreases t.len(),
{
    if t.len()>0 {
        assert(actions(t).drop_first() =~= actions(t.drop_first()));
        native_prefix(m,read::next(m,x,t[0].action),t.drop_first(),o);
    }
}
pub open spec fn boot(b:Option<Fork>) -> Seq<Event> {
    match b {Some(f)=>actions_to_crash(f).take(5),None=>probe::actions().take(3)}
}

}
