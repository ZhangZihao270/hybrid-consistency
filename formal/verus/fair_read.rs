// Construct an actual fair continuation from finite packet/process turns.
// Different turns may require different paths and arbitrarily many steps.
use vstd::prelude::*;
use crate::{Replica,delivery::*,progress};
use crate::independent_read::{self as read,State};
use crate::ordinary_service::pending;
use crate::read_call::{Event,Net,Program};
use crate::read_nonblocking as nb;
use crate::promotion_wait::{Path,valid_edges};
use crate::stock_fair_extension::{beginning,position,visits};

verus! {

pub type Runnable = spec_fn(Net,Process)->bool;
pub type Block<S> = Path<State<S>,Event>;
pub enum Duty { Packet(nat), Turn(Process) }
pub struct Run<S> { pub state:spec_fn(nat)->State<S>, pub action:spec_fn(nat)->Event }
pub open spec fn physical<S>(e:Run<S>) -> progress::Execution<int,crate::checkpoint::Wire> {
    progress::Execution{state:|i:nat|(e.state)(i).cfg.net,action:e.action}
}
pub open spec fn execution<S>(m:Program<S>,e:Run<S>,x:State<S>) -> bool {
    (e.state)(0)==x && forall|i:nat| read::service_step(m)((e.state)(i),#[trigger] (e.action)(i),(e.state)(i+1))
}
pub open spec fn discharged(q:Duty,run:Runnable,n:Net,a:Event) -> bool {
    match q {
        Duty::Packet(id) => !n.pending.contains_key(id) || !live(n,n.pending[id].to) || a==Action::Deliver(id),
        Duty::Turn(p) => !run(n,p) || process_step(n,a).actor==p,
    }
}
pub open spec fn turn<S>(m:Program<S>,run:Runnable,x:State<S>,q:Duty,b:Block<S>) -> bool {
    b.actions.len()>0 && b.states.len()==b.actions.len()+1 && b.states[0]==x && valid_edges(read::service_step(m),b)
        && exists|j:int| 0<=j<b.actions.len() && #[trigger] discharged(q,run,b.states[j].cfg.net,b.actions[j])
}
pub open spec fn can_schedule<S>(m:Program<S>,run:Runnable,x:State<S>,q:Duty) -> bool {
    exists|b:Block<S>| #[trigger] turn(m,run,x,q,b)
}
pub open spec fn schedulable<S>(m:Program<S>,run:Runnable,x:State<S>) -> bool {
    forall|q:Duty| #[trigger] can_schedule(m,run,x,q)
}
pub open spec fn fair<S>(e:Run<S>,run:Runnable) -> bool {
    progress::delivery_fair(physical(e)) && progress::process_fair(physical(e),run)
}
spec fn ticket(q:Duty) -> nat {
    match q {Duty::Packet(id)=>5+id,Duty::Turn(p)=>match p {
        Process::FirstClient=>0,Process::SecondClient=>1,
        Process::At(Replica::R1)=>2,Process::At(Replica::R2)=>3,Process::At(Replica::R3)=>4}}
}
spec fn duty(j:nat) -> Duty {
    if j<5 {Duty::Turn(if j==0 {Process::FirstClient} else if j==1 {Process::SecondClient}
        else if j==2 {Process::At(Replica::R1)} else if j==3 {Process::At(Replica::R2)} else {Process::At(Replica::R3)})}
    else {Duty::Packet((j-5) as nat)}
}
spec fn select<S>(m:Program<S>,run:Runnable) -> spec_fn(State<S>,nat)->Block<S> {
    |x:State<S>,i:nat| choose|b:Block<S>| #[trigger] turn(m,run,x,duty(position(i).1),b)
}
type Plan<S> = spec_fn(State<S>,nat)->Block<S>;

// Segment i starts at this physical step index and private configuration.
spec fn boundary<S>(plan:Plan<S>,x:State<S>,i:nat) -> (nat,State<S>)
    decreases i,
{
    if i==0 {(0,x)} else {
        let (t,s)=boundary(plan,x,(i-1) as nat);let b=plan(s,(i-1) as nat);
        (t+b.actions.len(),b.states.last())
    }
}
spec fn block<S>(p:Plan<S>,x:State<S>,i:nat) -> Block<S> { p(boundary(p,x,i).1,i) }
pub open spec fn closed<S>(m:Program<S>,reg:nb::Region<State<S>>) -> bool {
    forall|s:State<S>,a:Event,u:State<S>| reg(s) && #[trigger] read::service_step(m)(s,a,u) ==> reg(u)
}
proof fn stays<S>(m:Program<S>,reg:nb::Region<State<S>>,b:Block<S>,k:nat)
    requires closed(m,reg),reg(b.states[0]),b.states.len()==b.actions.len()+1,valid_edges(read::service_step(m),b),k<=b.actions.len(),
    ensures reg(b.states[k as int]),
    decreases k,
{
    if k>0 {
        let h=(k-1) as nat;stays(m,reg,b,h);
        assert(read::service_step(m)(b.states[h as int],b.actions[h as int],b.states[k as int]));
    }
}
spec fn calendar<S>(m:Program<S>,run:Runnable,p:Plan<S>,x:State<S>) -> bool {
    forall|i:nat| #[trigger] turn(m,run,boundary(p,x,i).1,duty(position(i).1),block(p,x,i))
}
proof fn scheduled_block<S>(m:Program<S>,run:Runnable,reg:nb::Region<State<S>>,x:State<S>,i:nat)
    requires reg(x),closed(m,reg),forall|s:State<S>| reg(s) ==> #[trigger] schedulable(m,run,s),
    ensures ({
        let p=select(m,run);let s=boundary(p,x,i).1;
        reg(s) && turn(m,run,s,duty(position(i).1),block(p,x,i))
    }),
    decreases i,
{
    let p=select(m,run);let s=boundary(p,x,i).1;let q=duty(position(i).1);
    if i>0 {
        let h=(i-1) as nat;scheduled_block(m,run,reg,x,h);
        let b=block(p,x,h);stays(m,reg,b,b.actions.len());
    }
    assert(schedulable(m,run,s));
    assert(can_schedule(m,run,s,q));
}

spec fn inside<S>(p:Plan<S>,x:State<S>,i:nat,t:nat) -> bool {
    boundary(p,x,i).0<=t<boundary(p,x,i+1).0
}
spec fn locate<S>(p:Plan<S>,x:State<S>,t:nat) -> nat {choose|i:nat| #[trigger] inside(p,x,i,t)}
proof fn increasing<S>(m:Program<S>,run:Runnable,p:Plan<S>,x:State<S>,lo:nat,hi:nat)
    requires calendar(m,run,p,x),lo<=hi,
    ensures boundary(p,x,lo).0 + hi <= boundary(p,x,hi).0 + lo,
    decreases hi-lo,
{
    if lo<hi {
        let h=(hi-1) as nat;increasing(m,run,p,x,lo,h);
        assert(turn(m,run,boundary(p,x,h).1,duty(position(h).1),block(p,x,h)));
    }
}
proof fn locate_at<S>(m:Program<S>,run:Runnable,p:Plan<S>,x:State<S>,i:nat,t:nat)
    requires calendar(m,run,p,x),inside(p,x,i,t),
    ensures locate(p,x,t)==i,
{
    assert(exists|j:nat| #[trigger] inside(p,x,j,t));
    let j=locate(p,x,t);
    if j<i {increasing(m,run,p,x,j+1,i);} else if i<j {increasing(m,run,p,x,i+1,j);}
}
proof fn has_block<S>(m:Program<S>,run:Runnable,p:Plan<S>,x:State<S>,t:nat)
    requires calendar(m,run,p,x),
    ensures inside(p,x,locate(p,x,t),t),
    decreases t,
{
    if t==0 {
        assert(turn(m,run,boundary(p,x,0).1,duty(position(0).1),block(p,x,0)));
        locate_at(m,run,p,x,0,0);
    } else {
        let j=locate(p,x,(t-1) as nat);has_block(m,run,p,x,(t-1) as nat);
        if t==boundary(p,x,j+1).0 {
            increasing(m,run,p,x,j+1,j+2);locate_at(m,run,p,x,j+1,t);
        } else { locate_at(m,run,p,x,j,t); }
    }
}
spec fn stream<S>(p:Plan<S>,x:State<S>) -> Run<S> {
    Run{state:|t:nat|{let i=locate(p,x,t);block(p,x,i).states[t-boundary(p,x,i).0]},
        action:|t:nat|{let i=locate(p,x,t);block(p,x,i).actions[t-boundary(p,x,i).0]}}
}
proof fn physical_step<S>(m:Program<S>,run:Runnable,p:Plan<S>,x:State<S>,t:nat)
    requires calendar(m,run,p,x),
    ensures ({
        let e=stream(p,x); read::service_step(m)((e.state)(t),(e.action)(t),(e.state)(t+1))
    }),
{
    has_block(m,run,p,x,t);
    let i=locate(p,x,t);let b=block(p,x,i);let j=t-boundary(p,x,i).0;
    assert(turn(m,run,boundary(p,x,i).1,duty(position(i).1),b));
    assert(read::service_step(m)(b.states[j],b.actions[j],b.states[j+1]));
    if j+1==b.actions.len() {
        let u=boundary(p,x,i+1);
        assert(turn(m,run,u.1,duty(position(i+1).1),block(p,x,i+1)));
        locate_at(m,run,p,x,i+1,t+1);
    } else {locate_at(m,run,p,x,i,t+1);}
}
proof fn visits_duty<S>(m:Program<S>,run:Runnable,p:Plan<S>,x:State<S>,from:nat,q:Duty) -> (t:nat)
    requires calendar(m,run,p,x),
    ensures t>=from,discharged(q,run,(stream(p,x).state)(t).cfg.net,(stream(p,x).action)(t)),
{
    let name=ticket(q);let lap=from+name;visits(lap,name);
    let i=beginning(lap)+name;let b=block(p,x,i);let u=boundary(p,x,i);
    assert(duty(name)==q);
    assert(turn(m,run,u.1,duty(position(i).1),b));
    let j=choose|j:int| 0<=j<b.actions.len() && #[trigger] discharged(q,run,b.states[j].cfg.net,b.actions[j]);
    increasing(m,run,p,x,0,i);let t=u.0+j as nat;locate_at(m,run,p,x,i,t);t
}

// A live in-flight packet remains the same packet through every step short
// of its delivery. Reuse of a freed slot cannot discharge its first issue.
pub(crate) proof fn unconsumed<S>(m:Program<S>,x:State<S>,e:Run<S>,i:nat,j:nat,id:nat)
    requires execution(m,e,x),i<=j,(e.state)(i).cfg.net.pending.contains_key(id),
        forall|t:nat| i<=t<j ==> (#[trigger] (e.action)(t))!=Action::<crate::checkpoint::Wire>::Deliver(id),
    ensures (e.state)(j).cfg.net.pending.get(id)==Some((e.state)(i).cfg.net.pending[id]),
    decreases j-i,
{
    if i<j {
        let h=(j-1) as nat;
        unconsumed(m,x,e,i,h,id);
        let a=(e.action)(h);assert(a!=Action::<crate::checkpoint::Wire>::Deliver(id));
        assert(read::service_step(m)((e.state)(h),a,(e.state)(j)));
        if let Action::Send(k,_) = a {assert(k!=id);}
    }
}

pub proof fn fair_extension<S>(m:Program<S>,run:Runnable,reg:nb::Region<State<S>>,x:State<S>) -> (e:Run<S>)
    requires reg(x),closed(m,reg),forall|s:State<S>| reg(s) ==> #[trigger] schedulable(m,run,s),
    ensures execution(m,e,x),fair(e,run),
{
    let p=select(m,run);let e=stream(p,x);let net=physical(e);
    assert forall|i:nat| #[trigger] turn(m,run,boundary(p,x,i).1,duty(position(i).1),block(p,x,i)) by {
        scheduled_block(m,run,reg,x,i);
    }
    assert(turn(m,run,boundary(p,x,0).1,duty(position(0).1),block(p,x,0)));
    locate_at(m,run,p,x,0,0);
    assert((e.state)(0)==x);
    assert forall|i:nat| read::service_step(m)((e.state)(i),#[trigger] (e.action)(i),(e.state)(i+1))
        by {physical_step(m,run,p,x,i);}
    assert(execution(m,e,x));
    assert forall|i:nat,id:nat| #[trigger] (net.state)(i).pending.contains_key(id) implies
        exists|j:nat| j>=i && (#[trigger] (net.action)(j)==Action::Deliver(id)
            || !live((net.state)(j),(net.state)(i).pending[id].to)) by {
        let j=visits_duty(m,run,p,x,i,Duty::Packet(id));
        if !(exists|t:nat| i<=t<j && (#[trigger] (e.action)(t))==Action::Deliver(id)) {
            unconsumed(m,x,e,i,j,id);
        } else {
            let h=choose|t:nat| i<=t<j && (#[trigger] (e.action)(t))==Action::Deliver(id);
            assert((net.action)(h)==Action::Deliver(id));
        }
    }
    assert forall|i:nat,q:Process| #[trigger] progress::continuously_runnable(net,run,i,q) implies
        exists|j:nat| j>=i && #[trigger] progress::runs_at(net,j,q) by {
        let j=visits_duty(m,run,p,x,i,Duty::Turn(q));assert(run((net.state)(j),q));
        assert(progress::runs_at(net,j,q));
    }
    e
}

// Extract the individual finite turn from any fair execution. Thus on a
// successor-closed region local schedulability at every point is also
// necessary for fair extension at every point, in this infinite-run model.
proof fn first_turn<S>(m:Program<S>,run:Runnable,x:State<S>,e:Run<S>,q:Duty) -> (j:nat)
    requires execution(m,e,x),fair(e,run),
    ensures discharged(q,run,(e.state)(j).cfg.net,(e.action)(j)),
{
    let n=physical(e);
    match q {
        Duty::Packet(id) => {
            if !x.cfg.net.pending.contains_key(id) || !live(x.cfg.net,x.cfg.net.pending[id].to) {0}
            else {
                let j=choose|j:nat| j>=0 && ((#[trigger] (n.action)(j))==Action::Deliver(id)
                    || !live((n.state)(j),(n.state)(0).pending[id].to));
                if exists|k:nat| k<j && (#[trigger] (e.action)(k))==Action::Deliver(id) {
                    choose|k:nat| k<j && (#[trigger] (e.action)(k))==Action::Deliver(id)
                } else { unconsumed(m,x,e,0,j,id);j }
            }
        },
        Duty::Turn(p) => {
            if progress::continuously_runnable(n,run,0,p) {
                choose|j:nat| j>=0 && #[trigger] progress::runs_at(n,j,p)
            } else { choose|j:nat| !#[trigger] run((n.state)(j),p) }
        },
    }
}
pub(crate) open spec fn initial_block<S>(e:Run<S>,k:nat) -> Block<S> {
    Path{states:Seq::new(k+1,|j:int|(e.state)(j as nat)),actions:Seq::new(k,|j:int|(e.action)(j as nat))}
}
pub(crate) proof fn initial_steps<S>(m:Program<S>,x:State<S>,e:Run<S>,k:nat)
    requires execution(m,e,x),
    ensures valid_edges(read::service_step(m),initial_block(e,k)),
{
    let b=initial_block(e,k);
    assert forall|i:int| 0<=i<k implies read::service_step(m)(b.states[i],#[trigger] b.actions[i],b.states[i+1])
        by {assert(read::service_step(m)((e.state)(i as nat),(e.action)(i as nat),(e.state)(i as nat+1)));}
}
pub proof fn fair_run_supplies_each_turn<S>(m:Program<S>,run:Runnable,x:State<S>,e:Run<S>)
    requires execution(m,e,x),fair(e,run),
    ensures schedulable(m,run,x),
{
    assert forall|q:Duty| #[trigger] can_schedule(m,run,x,q) by {
        let j=first_turn(m,run,x,e,q);let b=initial_block(e,j+1);
        initial_steps(m,x,e,j+1);
        assert(discharged(q,run,b.states[j as int].cfg.net,b.actions[j as int]));
        assert(turn(m,run,x,q,b));
    }
}

pub open spec fn publishes<S>(e:Run<S>,res:spec_fn(S)->Option<int>) -> bool {
    exists|k:nat| #[trigger] read::returned(res)((e.state)(k))
}
pub open spec fn fair_majority_availability<S>(m:Program<S>,res:spec_fn(S)->Option<int>,entry:State<S>,run:Runnable) -> bool {
    forall|x:State<S>,e:Run<S>| read::reached(m,entry,x) && read::issued_to_majority(x) && pending(x.cfg,res)
        && #[trigger] execution(m,e,x) && fair(e,run) ==> publishes(e,res)
}
pub open spec fn pending_turns<S>(m:Program<S>,res:spec_fn(S)->Option<int>,entry:State<S>,run:Runnable) -> bool {
    forall|x:State<S>| read::reached(m,entry,x) && read::issued_to_majority(x) && pending(x.cfg,res)
        ==> #[trigger] schedulable(m,run,x)
}

pub(crate) proof fn append_reachable<S>(m:Program<S>,entry:State<S>,x:State<S>,a:Event,y:State<S>,k:nat)
    requires nb::within(read::prefix_step(m),read::at_state(x),entry,k),read::prefix_step(m)(x,a,y),
    ensures nb::within(read::prefix_step(m),read::at_state(y),entry,k+1),
    decreases k,
{
    let step=read::prefix_step(m);
    if entry==x {assert(nb::within(step,read::at_state(y),y,k));}
    else {
        let (e,u)=choose|e:Event,u:State<S>| #[trigger] step(entry,e,u) && nb::within(step,read::at_state(x),u,(k-1) as nat);
        append_reachable(m,u,x,a,y,(k-1) as nat);
    }
}
spec fn stranded<S>(m:Program<S>,res:spec_fn(S)->Option<int>,entry:State<S>) -> nb::Region<State<S>> {
    |s:State<S>| read::reached(m,entry,s) && read::issued_to_majority(s)
        && !nb::possible(read::service_step(m),read::returned(res),s)
}

// No fair reference is assumed. If no finite return exists, a real pending
// run must still be fair-schedulable. Each named packet/CPU needs only one
// individually feasible finite turn. Their lengths need not be bounded.
pub proof fn fair_progress_offers_service<S>(m:Program<S>,res:spec_fn(S)->Option<int>,entry:State<S>,run:Runnable)
    requires fair_majority_availability(m,res,entry,run),pending_turns(m,res,entry,run),
    ensures read::hybrid_read_service(m,res,entry),
{
    let bad=stranded(m,res,entry);let step=read::service_step(m);let done=read::returned(res);
    assert forall|s:State<S>,a:Event,u:State<S>| bad(s) && #[trigger] step(s,a,u) implies bad(u) by {
        assert(read::prefix_step(m)(s,a,u));
        let k=choose|k:nat| #[trigger] nb::within(read::prefix_step(m),read::at_state(s),entry,k);
        append_reachable(m,entry,s,a,u,k);
        let (r,q)=choose|r:Replica,q:Replica| r!=q && s.requested.contains(r) && s.requested.contains(q)
            && #[trigger] live(s.cfg.net,crate::checkpoint::at(r)) && #[trigger] live(s.cfg.net,crate::checkpoint::at(q));
        assert(live(u.cfg.net,crate::checkpoint::at(r)) && live(u.cfg.net,crate::checkpoint::at(q)));
        assert(u.requested==s.requested);
        if nb::possible(step,done,u) {nb::predecessor(step,done,s,a,u);}
    }
    assert forall|s:State<S>| bad(s) implies #[trigger] schedulable(m,run,s) by {
        if !pending(s.cfg,res) {assert(nb::within(step,done,s,0));}
    }
    assert forall|x:State<S>| #[trigger] read::reached(m,entry,x) && read::issued_to_majority(x) && pending(x.cfg,res)
        implies nb::possible(step,done,x) by {
        if !nb::possible(step,done,x) {
            let e=fair_extension(m,run,bad,x);
            assert(publishes(e,res));
            let k=choose|k:nat| #[trigger] read::returned(res)((e.state)(k));
            let b=initial_block(e,k);initial_steps(m,x,e,k);
            nb::from_path(step,done,b,0);
        }
    }
}

}
