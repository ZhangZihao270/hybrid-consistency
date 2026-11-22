// Apply the independent-C2 simulation to native checkpoints produced by the
// majority histories. The same majority availability assumption covers hybrid reads.
use vstd::prelude::*;
use crate::{Replica,Op,checkpoint::*,delivery::*,protocol::*};
use crate::first_assembly::*;
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_pair::{close,original_actions};
use crate::first_schedule::{self as first,reference};
use crate::first_splice::{self as s,Tape,pick};
use crate::independent_read::{self as read,State};
use crate::ordinary_service::{Configuration,allowed,apply,pending};
use crate::promotion_wait::{self as wait,Relation};
use crate::read_call::{Event,Program};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::fair_read as fair;

verus! {

pub open spec fn final_cfg<S>(m:Program<S>,x:Configuration<S>,a:Seq<Event>) -> Configuration<S>
    decreases a.len(),
{
    if a.len()==0 {x} else {final_cfg(m,apply(m,x,a[0]),a.drop_first())}
}
pub open spec fn observed_suffix<S>(m:Program<S>,x:Configuration<S>,a:Seq<Event>) -> Tape
    decreases a.len(),
{
    if a.len()==0 {Seq::empty()} else {seq![process_step(x.net,a[0])]+observed_suffix(m,apply(m,x,a[0]),a.drop_first())}
}
pub open spec fn service_inputs<S>(p:Service<S>,j:nat) -> Tape
    decreases p.actions.len()-j,
{
    if j>=p.actions.len() {Seq::empty()} else {
        let e=process_step(p.states[j as int].cfg.net,p.actions[j as int]);
        let tail=service_inputs(p,j+1);if e.actor==Process::FirstClient {tail} else {seq![e]+tail}
    }
}
// An actual service continuation with its first publicly observable response
// in C2 memory. C1 has stopped. R3 has failed. Other traffic remains enabled.
pub open spec fn responds<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:Configuration<S>,a:Seq<Event>,v:int) -> bool
    decreases a.len(),
{
    if a.len()==0 {res((x.private)(Process::SecondClient))==Some(v)} else {
        let e=a[0];pending(x,res) && crate::finite_service::no_client_send(e) && s::moves(e)
            && allowed(m,x,e) && responds(m,res,apply(m,x,e),a.drop_first(),v)
    }
}
pub(crate) proof fn response_value<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:Configuration<S>,a:Seq<Event>,v:int)
    requires responds(m,res,x,a,v),
    ensures res((final_cfg(m,x,a).private)(Process::SecondClient))==Some(v),
    decreases a.len(),
{
    if a.len()>0 {response_value(m,res,apply(m,x,a[0]),a.drop_first(),v);}
}
pub(crate) proof fn replay_return<S>(m:Program<S>,res:spec_fn(S)->Option<int>,p:Service<S>,j:nat,t:Configuration<S>)
    requires p.states.len()==p.actions.len()+1,j<=p.actions.len(),wait::valid_edges(read::service_step(m),p),
        wait::pending_before(read::returned(res),p),read::returned(res)(p.states.last()),read::covers(p.states[j as int],t),
        p.states[j as int].reserved.contains(2),!p.states[j as int].cfg.net.pending.contains_key(2),
    ensures ({let a=read::retained_actions(p,j);let v=res((p.states.last().cfg.private)(Process::SecondClient)).unwrap();
        responds(m,res,t,a,v) && observed_suffix(m,t,a)==service_inputs(p,j) && final_cfg(m,t,a).net.pending.get(2)==t.net.pending.get(2)
            && (enabled(t.net,Action::Deliver(2)) ==> enabled(final_cfg(m,t,a).net,Action::Deliver(2)))}),
    decreases p.actions.len()-j,
{
    let x=p.states[j as int];let c=Process::SecondClient;assert((x.cfg.private)(c)==(t.private)(c));
    if j<p.actions.len() {
        let a=p.actions[j as int];let y=p.states[j as int+1];let obs=process_step(x.cfg.net,a);
        assert(read::service_step(m)(x,a,y));assert(!read::returned(res)(x));read::project_step(m,m,x,y,t,a);
        if obs.actor==Process::FirstClient {replay_return(m,res,p,j+1,t);}
        else {
            let u=apply(m,t,a);assert(s::moves(a));assert(u.net.pending.get(2)==t.net.pending.get(2));
            assert(enabled(t.net,Action::Deliver(2)) ==> enabled(u.net,Action::Deliver(2)));
            replay_return(m,res,p,j+1,u);assert(read::retained_actions(p,j).drop_first() =~= read::retained_actions(p,j+1));
        }
    }
}
pub(crate) proof fn reachable<S>(m:Program<S>,x:State<S>,a:Seq<Event>)
    requires prefix(m,x,a,false),
    ensures read::reached(m,x,drive(m,x,a)),
    decreases a.len(),
{
    let z=drive(m,x,a);let r=read::prefix_step(m);let d=read::at_state(z);
    if a.len()==0 {assert(nb::within(r,d,x,0));} else {
        let y=read::next(m,x,a[0]);reachable(m,y,a.drop_first());nb::predecessor(r,d,x,a[0],y);
    }
}
pub open spec fn reference_progress<S>(m:Program<S>,b:Fork,run:fair::Runnable) -> bool {
    mail::first_availability(m,run,first::reached_in(m,b)) && mail::fair_opportunity(m,run,reference(m,b,5))
}
pub(crate) proof fn finite_service<S>(m:Program<S>,b:Fork,run:fair::Runnable)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),reference_progress(m,b,run),
    ensures exists|p:Service<S>| #[trigger] cause::returning(m,b,p),
{
    dispatch::fanout_and_weak_open_launch(m,b);dispatch::launch_cut(m,b);let x=reference(m,b,5);let c=Process::FirstClient;
    crate::sr1_majorities::local_at(m,b,c,5);assert(crate::sr1_majorities::count(b,5)==5);
    assert(!(m.done)((first::cfg(m,b,5).private)(c)));assert(!mail::posted(m)(x));
    mail::fair_first_service(m,run,first::reached_in(m,b),x);
    nb::first_response_iff(mail::active_step(m),mail::posted(m),x);
    let p=choose|p:Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),x,p);assert(cause::returning(m,b,p));
}
pub open spec fn stable<S>(b:Fork,p:Service<S>) -> bool {
    forall|i:int| 0<=i<p.actions.len() ==> !cause::changes_sample(b,#[trigger] p.states[i],p.states[i+1])
}
pub open spec fn usable<S>(b:Fork,p:Service<S>,l:Lanes,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    let t=s::record(p,0);separable(t,b,l) && cause::source_shape(t,b,answers) && stable(b,p)
}
// All usable ordinary alternatives are considered. One badly routed fair
// sample, or one read that received an ACK unnecessarily, proves no wait.
pub open spec fn obstruction<S>(m:Program<S>,b:Fork,l:Lanes,answers:spec_fn(Packet<Wire>)->bool,effect:Relation<State<S>,Event>) -> bool {
    let step=mail::active_step(m);let done=mail::posted(m);let x=reference(m,b,5);
    wait::needs_class(step,done,x,effect) || (
        (exists|p:Service<S>| #[trigger] cause::returning(m,b,p) && !wait::uses(p,effect)) &&
        (forall|p:Service<S>| #[trigger] cause::returning(m,b,p) && !wait::uses(p,effect) ==> !usable(b,p,l,answers)))
}
proof fn select_service<S>(m:Program<S>,b:Fork,l:Lanes,answers:spec_fn(Packet<Wire>)->bool,effect:Relation<State<S>,Event>,run:fair::Runnable)
    -> (p:Service<S>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),reference_progress(m,b,run),!obstruction(m,b,l,answers,effect),
    ensures cause::returning(m,b,p),!wait::uses(p,effect),usable(b,p,l,answers),
{
    finite_service(m,b,run);
    let w=choose|p:Service<S>| #[trigger] cause::returning(m,b,p);let st=mail::active_step(m);let d=mail::posted(m);let x=reference(m,b,5);
    assert(wait::can_finish(st,d,x));let q=choose|p:Service<S>| #[trigger] wait::first_return(st,d,x,p) && !wait::uses(p,effect);
    assert(cause::returning(m,b,q));choose|p:Service<S>| #[trigger] cause::returning(m,b,p) && !wait::uses(p,effect) && usable(b,p,l,answers)
}
// This is H's history obligation for actual completions in the two original
// workloads, with each RMW returning 1. It does not require a read to return.
pub open spec fn history_witness<S>(m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,
    ta:Tape,tb:Tape,a:Seq<Event>,v:int) -> bool {
    let cut=original_actions(b,ta,tb);let x=entry(m,l);let y=drive(m,x,cut);
    prefix(m,x,cut,true) && s::plays(m,root(m,l,Some(b)),cause::tape(b,ta,tb))
        && cause::pending_inputs(m,(root(m,l,Some(b)).cfg.private)(Process::FirstClient),pick(cause::tape(b,ta,tb),Process::FirstClient,true))
        && mail::posted(m)(y) && prefix(m,y,close(true),true) && responds(m,res,drive(m,y,close(true)).cfg,a,v)
}
pub open spec fn history<S>(m:Program<S>,res:spec_fn(S)->Option<int>,first:spec_fn(S)->int,l:Lanes,b:Fork) -> bool {
    forall|ta:Tape,tb:Tape,a:Seq<Event>,v:int| #[trigger] history_witness(m,res,l,b,ta,tb,a,v)
        ==> exists|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,
            first((drive(m,entry(m,l),original_actions(b,ta,tb)).cfg.private)(Process::FirstClient)),v)
}
// The first client sees only its own majority reference, and each original
// has the opposite site's response still undelivered. Public results follow
// from the actual shared-cell interval on that reference.
pub open spec fn original_read<S>(m:Program<S>,first:spec_fn(S)->int,l:Lanes,b:Fork,ta:Tape,tb:Tape,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    let t=cause::tape(b,ta,tb);let src=if b.branch==crate::Branch::Alpha {ta} else {tb};let c=Process::FirstClient;
    let y=fork_end(m,l,b,ta,tb);let a=original_actions(b,ta,tb);let x=entry(m,l);let caller=pick(t,c,true);
    prefix(m,x,a,true) && drive(m,x,a)==y && s::plays(m,root(m,l,Some(b)),t) && mail::posted(m)(y) && first((y.cfg.private)(c))==first_value(b)
        && caller==pick(src,c,true) && cause::pending_inputs(m,(root(m,l,Some(b)).cfg.private)(c),caller)
        && (forall|r:Replica| #[trigger] cause::replied(t,r,answers) && (cause::quorum(b,r) ==> cause::exchange(t,r,answers)))
        && (forall|i:int| 0<=i<caller.len() && (#[trigger] caller[i]).incoming.is_some() ==>
            caller[i].incoming.unwrap().from==at(crate::origin(b.branch)) || caller[i].incoming.unwrap().from==at(Replica::R3))
}
pub proof fn selected_reads<S>(m:Program<S>,res:spec_fn(S)->Option<int>,first:spec_fn(S)->int,l:Lanes,b:Fork,
    pa:Service<S>,pb:Service<S>,answers:spec_fn(Packet<Wire>)->bool)
    requires lanes_ok(l),dispatch::initiates(m),dispatch::weak_open(m,b),first::startup(m),issue::can_issue(m,res),
        cause::returning(m,alpha(b.notice),pa),cause::returning(m,beta(b.notice),pb),
        usable(alpha(b.notice),pa,l,answers),usable(beta(b.notice),pb,l,answers),cause::member_sample(m,first,b),
    ensures ({
        let ta=s::record(pa,0);let tb=s::record(pb,0);let e=pair::auxiliary(m,l,b.notice,ta,tb);let y=fork_end(m,l,b,ta,tb);
        original_read(m,first,l,b,ta,tb,answers) && prefix(m,y,pair::close(true),true)
            && read::reached(m,entry(m,l),e) && read::covers(e,drive(m,y,pair::close(true)).cfg)
            && read::issued_to_majority(e) && !read::returned(res)(e)
            && !e.cfg.net.pending.contains_key(2) && e.reserved.contains(2)
            && drive(m,y,pair::close(true)).cfg.net.pending.get(2)==Some(packet_for(b,2))
    }),
{
    let n=b.notice;let ta=s::record(pa,0);let tb=s::record(pb,0);let p=if b.branch==crate::Branch::Alpha {pa} else {pb};
    if b.branch==crate::Branch::Alpha {assert(b==alpha(n));} else {assert(b==beta(n));}
    assert(cause::returning(m,b,p) && usable(b,p,l,answers));
    s::recorded(m,pa,0);s::recorded(m,pb,0);
    cause::forced_sample(m,first,p,b);cause::pending_on_caller(m,p,0);cause::local_history(b,ta,tb,Process::FirstClient);
    pair::cover_after_service(m,res,l,b,ta,tb);pair::finish(m,l,b,ta,tb);
    pair::outside_work(m,l,n,ta,tb,Some(b));s::concat(m,root(m,l,Some(b)),work_pair(ta,tb,n),remaining(s::record(p,0),b));
    crate::sr1_majorities::local_at(m,b,Process::FirstClient,5);assert(crate::sr1_majorities::count(b,5)==5);
    assert(tail_actors().contains(Process::FirstClient));
    assert forall|r:Replica| #[trigger] cause::replied(cause::tape(b,ta,tb),r,answers)
        && (cause::quorum(b,r) ==> cause::exchange(cause::tape(b,ta,tb),r,answers)) by {
        cause::actual_respondents(ta,tb,b,l,answers,r);
    }
    let caller=pick(s::record(p,0),Process::FirstClient,true);
    assert forall|i:int| 0<=i<caller.len() && (#[trigger] caller[i]).incoming.is_some()
        implies caller[i].incoming.unwrap().from==at(crate::origin(b.branch)) || caller[i].incoming.unwrap().from==at(Replica::R3)
        by {cause::caller_sources(m,b,p,i);}
    reachable(m,entry(m,l),pair::early_actions(n,ta,tb));
}

pub open spec fn stranded_pair<S>(m:Program<S>,res:spec_fn(S)->Option<int>,first:spec_fn(S)->int,l:Lanes,n:Notice,
    ta:Tape,tb:Tape,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    let e=pair::auxiliary(m,l,n,ta,tb);
    original_read(m,first,l,alpha(n),ta,tb,answers) && original_read(m,first,l,beta(n),ta,tb,answers)
        && read::reached(m,entry(m,l),e) && read::issued_to_majority(e) && !read::returned(res)(e)
        && !nb::possible(read::service_step(m),read::returned(res),e)
}
pub open spec fn has_order(first:int,second:int) -> bool {
    exists|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,first,second)
}
pub proof fn h_cost_of_prepared_majorities<S>(m:Program<S>,res:spec_fn(S)->Option<int>,first:spec_fn(S)->int,l:Lanes,n:Notice,
    answers:spec_fn(Packet<Wire>)->bool,effect:Relation<State<S>,Event>,run:fair::Runnable)
    requires lanes_ok(l),dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b) && reference_progress(m,b,run)
            && cause::member_sample(m,first,b) && history(m,res,first,l,b),
    ensures obstruction(m,alpha(n),l,answers,effect) || obstruction(m,beta(n),l,answers,effect) ||
        exists|ta:Tape,tb:Tape| #[trigger] stranded_pair(m,res,first,l,n,ta,tb,answers),
{
    let a=alpha(n);let b=beta(n);
    if !obstruction(m,a,l,answers,effect) && !obstruction(m,b,l,answers,effect) {
        let pa=select_service(m,a,l,answers,effect,run);let pb=select_service(m,b,l,answers,effect,run);
        let ta=s::record(pa,0);let tb=s::record(pb,0);let e=pair::auxiliary(m,l,n,ta,tb);
        selected_reads(m,res,first,l,a,pa,pb,answers);selected_reads(m,res,first,l,b,pa,pb,answers);
        let st=read::service_step(m);let d=read::returned(res);
        if nb::possible(st,d,e) {
            let path=nb::to_path(st,d,e,choose|k:nat| #[trigger] nb::within(st,d,e,k));
            let v=res((path.states.last().cfg.private)(Process::SecondClient)).unwrap();let suffix=read::retained_actions(path,0);
            assert forall|f:Fork| f.notice==n implies has_order(#[trigger] first_value(f),v) by {
                if f.branch==crate::Branch::Alpha {assert(f==a);} else {assert(f==b);}
                let cut=original_actions(f,ta,tb);let y=drive(m,entry(m,l),cut);let target=drive(m,y,pair::close(true)).cfg;
                replay_return(m,res,path,0,target);assert(responds(m,res,target,suffix,v));
                assert(history_witness(m,res,l,f,ta,tb,suffix,v));assert(history(m,res,first,l,f));assert(first((y.cfg.private)(Process::FirstClient))==first_value(f));
            }
            assert(has_order(first_value(a),v) && has_order(first_value(b),v));
            let (ao,ax)=choose|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,5,v);
            let (bo,bx)=choose|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,2,v);
            crate::conditional_history_contradiction(ao,ax,bo,bx,v);
        }
        assert(stranded_pair(m,res,first,l,n,ta,tb,answers));
    }
}

}
