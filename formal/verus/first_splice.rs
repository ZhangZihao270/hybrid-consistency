// Finite local histories from an actual first-call execution. A transcript
// includes the actual envelope consumed and the cell read by its handler.
use vstd::prelude::*;
use crate::{checkpoint::*, delivery::*};
use crate::first_mailbox as mail;
use crate::independent_read::{self as read, State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program};

verus! {

pub type Observation = ProcessStep<int,Wire>;
pub type Tape = Seq<Observation>;

pub open spec fn slot(a:Event) -> Option<nat> {
    match a {Action::Send(i,_)|Action::Deliver(i)=>Some(i), _=>None}
}
pub open spec fn moves(a:Event) -> bool {
    a!=Action::CrashR3 && a!=Action::StartSecondClient && a!=Action::StopFirstClient
}
pub open spec fn after<S>(m:Program<S>,x:State<S>,t:Tape) -> State<S>
    decreases t.len(),
{
    if t.len()==0 {x} else {after(m,read::next(m,x,t[0].action),t.drop_first())}
}
pub open spec fn plays<S>(m:Program<S>,x:State<S>,t:Tape) -> bool
    decreases t.len(),
{
    if t.len()==0 {true} else {
        let e=t[0];let y=read::next(m,x,e.action);
        moves(e.action) && read::service_step(m)(x,e.action,y) && process_step(x.cfg.net,e.action)==e
            && plays(m,y,t.drop_first())
    }
}
pub open spec fn record<S>(p:wait::Path<State<S>,Event>,j:nat) -> Tape {
    Seq::new((p.actions.len()-j) as nat,|i:int|process_step(p.states[j+i].cfg.net,p.actions[j+i]))
}
pub proof fn recorded<S>(m:Program<S>,p:wait::Path<State<S>,Event>,j:nat)
    requires j<=p.actions.len(),p.states.len()==p.actions.len()+1,
        wait::valid_edges(mail::active_step(m),p),wait::pending_before(mail::posted(m),p),
    ensures plays(m,p.states[j as int],record(p,j)),after(m,p.states[j as int],record(p,j))==p.states.last(),
    decreases p.actions.len()-j,
{
    if j<p.actions.len() {
        let a=p.actions[j as int];let x=p.states[j as int];let y=p.states[j as int+1];
        assert(mail::active_step(m)(x,a,y));assert(!mail::posted(m)(x));
        recorded(m,p,j+1);assert(record(p,j).drop_first() =~= record(p,j+1));
    }
}
}
