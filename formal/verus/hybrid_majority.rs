// The author's A applies to both stock and hybrid operations. These are its
// read clauses as used by the monitored workload, with explicit fair runs.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*};
use crate::first_assembly::*;
use crate::first_mailbox as mail;
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program,Net};
use crate::read_nonblocking as nb;

verus! {

pub enum Caller { First, Second }
pub open spec fn due<S>(c:Caller,x:State<S>) -> bool {
    match c {Caller::First=>mail::submitted(x),Caller::Second=>read::issued_to_majority(x)}
}
pub open spec fn published<S>(c:Caller,m:Program<S>,res:spec_fn(S)->Option<int>) -> nb::Region<State<S>> {
    match c {Caller::First=>mail::posted(m),Caller::Second=>read::returned(res)}
}
pub open spec fn service<S>(c:Caller,m:Program<S>) -> wait::Relation<State<S>,Event> {
    match c {Caller::First=>mail::active_step(m),Caller::Second=>read::service_step(m)}
}
pub open spec fn value<S>(c:Caller,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,x:State<S>) -> int {
    match c {Caller::First=>first((x.cfg.private)(Process::FirstClient)),
        Caller::Second=>res((x.cfg.private)(Process::SecondClient)).unwrap()}
}
pub open spec fn sole(n:Net,q:Set<Replica>) -> bool {
    q.len()==2 && forall|r:Replica| #[trigger] q.contains(r)==live(n,at(r))
}
pub open spec fn fresh_invocation<S>(c:Caller,x:State<S>,a:Event) -> bool {
    match a {
        Action::Send(_,p)=>p.path==Path::Strong && p.to is At && match c {
            Caller::First=>p.from==Process::FirstClient && p.input==Wire::Request && x.first_requested.is_empty(),
            Caller::Second=>p.from==Process::SecondClient && p.input==Wire::Query2 && x.requested.is_empty() && x.cfg.net.second_started,
        },_=>false,
    }
}
// Both halves are native traces. The head includes the initial sends.
// Exactly Q is live at invocation and return, in a crash-stop network.
pub open spec fn served<S>(c:Caller,m:Program<S>,res:spec_fn(S)->Option<int>,h:Service<S>,t:Service<S>,q:Set<Replica>) -> bool {
    let d=published(c,m,res);
    h.actions.len()>0 && h.states.len()==h.actions.len()+1 && wait::valid_edges(read::prefix_step(m),h)
        && fresh_invocation(c,h.states[0],h.actions[0]) && wait::pending_before(d,h) && due(c,h.states.last())
        && wait::first_return(service(c,m),d,h.states.last(),t)
        && sole(h.states[0].cfg.net,q) && sole(t.states.last().cfg.net,q)
}
pub open spec fn held<S>(states:Seq<State<S>>,q:Set<Replica>,v:int) -> bool {
    exists|i:int,r:Replica| 0<=i<states.len() && q.contains(r) && #[trigger] (states[i].cfg.net.locals)(r)==v
}

// Sampling from invocation includes a first publication on a request send.
// Both endpoints have the same sole live quorum in this crash-stop model.
pub open spec fn first_invocation_interval<S>(m:Program<S>,p:Service<S>,q:Set<Replica>) -> bool {
    p.actions.len()>0 && wait::first_return(read::prefix_step(m),mail::posted(m),p.states[0],p)
        && fresh_invocation(Caller::First,p.states[0],p.actions[0]) && !p.states.last().cfg.net.first_stopped
        && sole(p.states[0].cfg.net,q) && sole(p.states.last().cfg.net,q)
}

pub open spec fn first_invocation_sampling<S>(m:Program<S>,first:spec_fn(S)->int,base:State<S>) -> bool {
    forall|p:Service<S>,q:Set<Replica>| #[trigger] first_invocation_interval(m,p,q) && read::reached(m,base,p.states[0])
        ==> held(p.states,q,first((p.states.last().cfg.private)(Process::FirstClient)))
}

pub open spec fn submitted_first_sampling<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,base:State<S>) -> bool {
    forall|h:Service<S>,t:Service<S>,q:Set<Replica>| #[trigger] served(Caller::First,m,res,h,t,q)
        && read::reached(m,base,h.states[0]) && !t.states.last().cfg.net.first_stopped ==> {
            let v=value(Caller::First,first,res,t.states.last()); held(h.states,q,v) || held(t.states,q,v)
        }
}

pub proof fn invocation_includes_submitted_sampling<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,base:State<S>)
    requires first_invocation_sampling(m,first,base),
    ensures submitted_first_sampling(m,first,res,base),
{
    let c=Caller::First;
    assert forall|h:Service<S>,t:Service<S>,q:Set<Replica>| #[trigger] served(c,m,res,h,t,q)
        && read::reached(m,base,h.states[0]) && !t.states.last().cfg.net.first_stopped implies {
            let v=value(c,first,res,t.states.last()); held(h.states,q,v) || held(t.states,q,v)
        } by {
        let n=h.actions.len(); let p=wait::Path { states:h.states.drop_last()+t.states,actions:h.actions+t.actions };
        let d=published(c,m,res);
        assert forall|i:int| 0<=i<p.actions.len() implies read::prefix_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
            if i<n { assert(read::prefix_step(m)(h.states[i],h.actions[i],h.states[i+1])); }
            else { let j=i-n; assert(service(c,m)(t.states[j],t.actions[j],t.states[j+1]));
                assert(read::initial_send(t.states[j],t.actions[j])); }
        }
        assert forall|i:int| 0<=i<p.actions.len() implies !d(#[trigger] p.states[i]) by {
            if i<n { assert(!d(h.states[i])); } else { assert(!d(t.states[i-n])); }
        }
        assert(first_invocation_interval(m,p,q));
        let v=value(c,first,res,t.states.last()); assert(held(p.states,q,v));
        let (j,r)=choose|j:int,r:Replica| 0<=j<p.states.len() && q.contains(r) && #[trigger] (p.states[j].cfg.net.locals)(r)==v;
        if j<n { assert((h.states[j].cfg.net.locals)(r)==v); } else { assert((t.states[j-n].cfg.net.locals)(r)==v); }
    }
}

}
