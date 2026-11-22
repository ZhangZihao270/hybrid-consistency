// The author's A applies to both stock and hybrid operations. These are its
// read clauses as used by the monitored workload, with explicit fair runs.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::*};
use crate::fair_read as fair;
use crate::first_assembly::*;
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::{self as first,reference};
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program,Net};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::sr1_majorities as maj;

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
// Every fair continuation of an eligible reachable call by a nonfaulty
// client returns. The choice of a fair continuation is a scheduler duty.
pub open spec fn eventual<S>(m:Program<S>,res:spec_fn(S)->Option<int>,base:State<S>,run:fair::Runnable) -> bool {
    forall|c:Caller,x:State<S>,e:fair::Run<S>| read::reached(m,base,x) && #[trigger] due(c,x)
        && #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && (c!=Caller::First || mail::honest(m,e))
        ==> exists|i:nat| #[trigger] published(c,m,res)((e.state)(i))
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
// Only the sole-live-majority specialization of A's held-value rule is
// needed. Determinism is the common local accept/update/observer program.
pub open spec fn sampling<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,base:State<S>) -> bool {
    forall|c:Caller,h:Service<S>,t:Service<S>,q:Set<Replica>| #[trigger] served(c,m,res,h,t,q)
        && read::reached(m,base,h.states[0]) ==> {
            let v=value(c,first,res,t.states.last());held(h.states,q,v) || held(t.states,q,v)
        }
}
pub open spec fn read_a<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,base:State<S>,run:fair::Runnable) -> bool {
    eventual(m,res,base,run) && sampling(m,first,res,base)
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

pub open spec fn first_reference_a<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,b:Fork,run:fair::Runnable) -> bool {
    mail::first_availability(m,run,crate::first_schedule::reached_in(m,b)) && submitted_first_sampling(m,first,res,reference(m,b,0))
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

proof fn request_memory<S>(m:Program<S>,b:Fork,i:nat)
    requires i<=3,
    ensures (reference(m,b,i+2).cfg.private)(Process::FirstClient)==memory(m,Process::FirstClient,dispatch::initial_sends(),i),
{
    let c=Process::FirstClient;
    dispatch::caller_memory(m,b,i+2); maj::local_at(m,b,c,i+2); assert(maj::count(b,i+2)==i+2);
}

proof fn publication_on_request<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,n:nat)
    requires 0<n<=3, dispatch::pending_fanout(m),dispatch::weak_open(m,b),
        first_invocation_sampling(m,first,reference(m,b,0)),
        (m.done)(memory(m,Process::FirstClient,dispatch::initial_sends(),n)),
        forall|j:nat| j<n ==> !(m.done)(#[trigger] memory(m,Process::FirstClient,dispatch::initial_sends(),j)),
    ensures first(memory(m,Process::FirstClient,dispatch::initial_sends(),n))==first_value(b),
{
    let es=maj::obs(b); let c=Process::FirstClient; let sends=dispatch::initial_sends();
    maj::majority_transport(b);
    assert forall|i:int| 0<=i<2+n implies { let e=#[trigger] es[i]; (m.accept)(memory(m,e.actor,es,i as nat),e) } by {
        prefix_index(i); assert(maj::kept_index(b,i as nat)==i && es[i]==checkpoint_observations(b)[i]);
        if i<2 { assert(i==0 || i==1); reveal_with_fuel(memory,2); }
        else { let j=(i-2) as nat; request_memory(m,b,j);
            assert(es[i]==sends[j as int] && !(m.done)(memory(m,c,sends,j))); }
    }
    first::ref_suffix(m,b,0,2);
    assert(nb::within(read::prefix_step(m),read::at_state(reference(m,b,2)),reference(m,b,0),2));
    let head=first_head(m,b); let path=wait::Path {states:head.states.take(n as int+1),actions:head.actions.take(n as int)};
    assert forall|i:int| 0<=i<n implies read::prefix_step(m)(path.states[i],#[trigger] path.actions[i],path.states[i+1])
        && !mail::posted(m)(path.states[i]) by {
        let j=(i+2) as nat; let e=es[j as int]; assert((m.accept)(memory(m,e.actor,es,j),e));
        first::reference_edge(m,b,j); request_memory(m,b,i as nat);
    }
    request_memory(m,b,n);
    let q=crate::first_quorum(b.branch);
    assert(q.len()==2) by { if b.branch==crate::Branch::Alpha {assert(set![Replica::R2,Replica::R3].len()==2);}
        else {assert(set![Replica::R1,Replica::R3].len()==2);} }
    assert(path.states.len()==n+1 && path.actions.len()==n && path.states[0]==reference(m,b,2)
        && path.states.last()==reference(m,b,n+2));
    assert(wait::pending_before(mail::posted(m),path)) by {
        assert forall|i:int| 0<=i<n implies !mail::posted(m)(#[trigger] path.states[i]) by { request_memory(m,b,i as nat); }
    }
    assert(wait::valid_edges(read::prefix_step(m),path));
    assert(!mail::posted(m)(path.states[0])) by { request_memory(m,b,0); }
    assert(wait::first_return(read::prefix_step(m),mail::posted(m),path.states[0],path));
    assert(fresh_invocation(Caller::First,path.states[0],path.actions[0]));
    assert(sole(path.states[0].cfg.net,q) && sole(path.states.last().cfg.net,q));
    assert(first_invocation_interval(m,path,q));
    let d=first(memory(m,c,sends,n)); assert(held(path.states,q,d));
    let (j,r)=choose|j:int,r:Replica| 0<=j<path.states.len() && q.contains(r) && #[trigger] (path.states[j].cfg.net.locals)(r)==d;
    assert(2<=j+2<=5 && 2<=maj::kept_index(b,(j+2) as nat)<=6);
}

// A caller publishing on the same send in the two reference executions
// would have the same result. The two sole available quorums are uniform
// and disjoint in value throughout the corresponding invocation intervals.
pub proof fn invocation_a_keeps_fanout_pending<S>(m:Program<S>,first:spec_fn(S)->int,n:Notice)
    requires dispatch::pending_fanout(m), forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b)
        && first_invocation_sampling(m,first,reference(m,b,0)),
    ensures dispatch::initiates(m),
{
    let c=Process::FirstClient; let sends=dispatch::initial_sends(); let done=|j:nat| (m.done)(memory(m,c,sends,j));
    assert(!done(0)) by { reveal(memory); }
    if done(1) || done(2) || done(3) {
        let j=if done(1) {1nat} else if done(2) {2nat} else {3nat};
        assert forall|h:nat| h<j implies !(m.done)(#[trigger] memory(m,c,sends,h)) by { assert(h==0 || h==1 || h==2); }
        assert(dispatch::weak_open(m,alpha(n)) && dispatch::weak_open(m,beta(n)));
        publication_on_request(m,first,alpha(n),j); publication_on_request(m,first,beta(n),j);
    }
    assert forall|j:nat| j<=3 implies !(m.done)(#[trigger] memory(m,c,sends,j)) by { assert(j==0 || j==1 || j==2 || j==3); }
    assert(accepted(m,sends)) by {
        assert forall|i:int| 0<=i<sends.len() implies {let e=#[trigger] sends[i]; (m.accept)(memory(m,e.actor,sends,i as nat),e)} by {
            assert(sends[i].actor==c);
            assert(!(m.done)(memory(m,c,sends,i as nat))); }
    }
}
pub proof fn availability_at_both_clients<S>(m:Program<S>,res:spec_fn(S)->Option<int>,base:State<S>,run:fair::Runnable)
    requires eventual(m,res,base,run),
    ensures mail::first_availability(m,run,|x|read::reached(m,base,x)),fair::fair_majority_availability(m,res,base,run),
{
    assert forall|x:State<S>,e:fair::Run<S>| read::reached(m,base,x) && mail::submitted(x)
        && #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && mail::honest(m,e)
        implies exists|i:nat| #[trigger] mail::posted(m)((e.state)(i)) by {
        assert(due(Caller::First,x));
        let j=choose|i:nat| #[trigger] published(Caller::First,m,res)((e.state)(i));
        assert(mail::posted(m)((e.state)(j)));
    }
    assert forall|x:State<S>,e:fair::Run<S>| read::reached(m,base,x) && read::issued_to_majority(x)
        && !read::returned(res)(x) && #[trigger] fair::execution(m,e,x) && fair::fair(e,run)
        implies fair::publishes(e,res) by {
        assert(due(Caller::Second,x));
        let j=choose|i:nat| #[trigger] published(Caller::Second,m,res)((e.state)(i));
        assert(read::returned(res)((e.state)(j)));
    }
}
pub proof fn mask_unchanged<S>(m:Program<S>,p:Service<S>,j:nat)
    requires p.states.len()==p.actions.len()+1,j<p.states.len(),wait::valid_edges(read::service_step(m),p),
    ensures p.states[j as int].cfg.net.r3_crashed==p.states[0].cfg.net.r3_crashed,
        p.states[j as int].cfg.net.unavailable==p.states[0].cfg.net.unavailable,
    decreases j,
{
    if j>0 {mask_unchanged(m,p,(j-1) as nat);assert(read::service_step(m)(p.states[j-1],p.actions[j-1],p.states[j as int]));}
}
pub open spec fn first_head<S>(m:Program<S>,b:Fork) -> Service<S> {
    wait::Path{states:Seq::new(4,|i:int|reference(m,b,(i+2) as nat)),actions:maj::actions(b).subrange(2,5)}
}
proof fn first_prefix<S>(m:Program<S>,b:Fork)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),
    ensures wait::valid_edges(read::prefix_step(m),first_head(m,b)),first::reached_in(m,b)(reference(m,b,2)),
        mail::submitted(reference(m,b,5)),wait::pending_before(mail::posted(m),first_head(m,b)),
{
    dispatch::fanout_and_weak_open_launch(m,b);dispatch::launch_cut(m,b);
    first::ref_suffix(m,b,0,2);assert(nb::within(read::prefix_step(m),read::at_state(reference(m,b,2)),reference(m,b,0),2));
    let h=first_head(m,b);let es=maj::obs(b);
    assert forall|i:int| 0<=i<3 implies read::prefix_step(m)(h.states[i],#[trigger] h.actions[i],h.states[i+1]) by {
        let j=(i+2) as nat;let e=es[j as int];assert((m.accept)(memory(m,e.actor,es,j),e));first::reference_edge(m,b,j);
    }
    assert forall|i:int| 0<=i<3 implies !mail::posted(m)(#[trigger] h.states[i]) by {
        let j=(i+2) as nat;maj::local_at(m,b,Process::FirstClient,j);assert(maj::count(b,j)==j);
        assert(!(m.done)((first::cfg(m,b,j).private)(Process::FirstClient)));
    }
}
proof fn caller_live_until_return<S>(m:Program<S>,p:Service<S>,j:nat)
    requires wait::first_return(mail::active_step(m),mail::posted(m),p.states[0],p), j<p.states.len(),
    ensures p.states[j as int].cfg.net.first_stopped==p.states[0].cfg.net.first_stopped,
    decreases j,
{
    if j>0 {
        caller_live_until_return(m,p,(j-1) as nat);
        assert(mail::active_step(m)(p.states[j-1],p.actions[j-1],p.states[j as int]) && !mail::posted(m)(p.states[j-1]));
    }
}

pub(crate) proof fn first_quorum_from_submitted<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,b:Fork)
    requires submitted_first_sampling(m,first,res,reference(m,b,0)),dispatch::initiates(m),dispatch::weak_open(m,b),
    ensures cause::member_sample(m,first,b),
{
    first_prefix(m,b);let h=first_head(m,b);let q=crate::first_quorum(b.branch);
    assert(q.len()==2) by {if b.branch==crate::Branch::Alpha {assert(set![Replica::R2,Replica::R3].len()==2);}
        else {assert(set![Replica::R1,Replica::R3].len()==2);}}
    assert forall|p:Service<S>| #[trigger] cause::returning(m,b,p) implies {
        let v=first((p.states.last().cfg.private)(Process::FirstClient));
        (exists|j:nat,r:Replica| 2<=j<=5 && cause::quorum(b,r) && #[trigger] (maj::net(b,j).locals)(r)==v)
        || (exists|j:int,r:Replica| 0<=j<p.states.len() && cause::quorum(b,r) && #[trigger] (p.states[j].cfg.net.locals)(r)==v)
    } by {
        assert forall|i:int| 0<=i<p.actions.len() implies read::service_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
            assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));
        }
        mask_unchanged(m,p,p.actions.len()); caller_live_until_return(m,p,p.actions.len());
        assert(sole(h.states[0].cfg.net,q));assert(sole(p.states.last().cfg.net,q));
        assert(served(Caller::First,m,res,h,p,q));let v=first((p.states.last().cfg.private)(Process::FirstClient));
        assert(held(h.states,q,v) || held(p.states,q,v));
        if held(h.states,q,v) {
            let (i,r)=choose|i:int,r:Replica| 0<=i<h.states.len() && q.contains(r) && #[trigger] (h.states[i].cfg.net.locals)(r)==v;
            assert(cause::quorum(b,r));assert((maj::net(b,(i+2) as nat).locals)(r)==v);
        } else {
            let (j,r)=choose|j:int,r:Replica| 0<=j<p.states.len() && q.contains(r) && #[trigger] (p.states[j].cfg.net.locals)(r)==v;
            assert(cause::quorum(b,r));
        }
    }
}
pub proof fn first_quorum_rule<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,b:Fork)
    requires sampling(m,first,res,reference(m,b,0)),dispatch::initiates(m),dispatch::weak_open(m,b),
    ensures cause::member_sample(m,first,b),
{
    first_quorum_from_submitted(m,first,res,b);
}
// The real C2 startup and two sends change no survivor cell. Thus the
// witness for its held value can be taken at or after full submission.
pub open spec fn second_head<S>(m:Program<S>,x:State<S>) -> Service<S> {
    let u=read::next(m,x,issue::send_first());let v=read::next(m,u,issue::send_second());
    wait::Path{states:seq![x,u,v],actions:seq![issue::send_first(),issue::send_second()]}
}
pub proof fn second_quorum_rule<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    base:State<S>,x:State<S>,p:Service<S>)
    requires sampling(m,first,res,base),read::reached(m,base,x),sole(x.cfg.net,live_pair()),x.requested.is_empty(),
        x.cfg.net.second_started,(x.cfg.private)(Process::SecondClient)==issue::started(m),issue::can_issue(m,res),
        prefix(m,x,second_head(m,x).actions,false),read::issued_to_majority(second_head(m,x).states.last()),
        wait::first_return(read::service_step(m),read::returned(res),second_head(m,x).states.last(),p),
    ensures held(p.states,live_pair(),res((p.states.last().cfg.private)(Process::SecondClient)).unwrap()),
{
    let h=second_head(m,x);let c=Process::SecondClient;let u=h.states[1];let e=h.states[2];
    assert(h.actions.drop_first() =~= seq![issue::send_second()]);reveal_with_fuel(prefix,3);mask_unchanged(m,p,p.actions.len());
    assert forall|i:int| 0<=i<2 implies read::prefix_step(m)(h.states[i],#[trigger] h.actions[i],h.states[i+1]) by {assert(i==0 || i==1);}
    assert forall|i:int| 0<=i<2 implies !read::returned(res)(#[trigger] h.states[i]) by {assert(i==0 || i==1);}
    assert(served(Caller::Second,m,res,h,p,live_pair()));
    let v=res((p.states.last().cfg.private)(c)).unwrap();
    if held(h.states,live_pair(),v) {
        let (i,r)=choose|i:int,r:Replica| 0<=i<h.states.len() && live_pair().contains(r) && #[trigger] (h.states[i].cfg.net.locals)(r)==v;
        assert(i==0 || i==1 || i==2);assert((p.states[0].cfg.net.locals)(r)==v);
    }
}

}
