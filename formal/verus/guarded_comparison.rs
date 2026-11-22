// Compare finite schedules of *proposals*. A physical transition occurs
// only when its native guard and transport admit it. Failed proposals are
// silent and never appear in an execution. Ordinary receipts read the queue.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::coupled_reads as calls;
use crate::coupled_traffic as traffic;
use crate::fair_read as fair;
use crate::first_assembly::{self as asm, Service};
use crate::first_splice::{self as tape, Tape, Observation};
use crate::hybrid_majority as majority;
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program};

verus! {

pub type Gate<S> = spec_fn(State<S>,Event)->bool;
pub open spec fn ready<S>(m: Program<S>, g: Gate<S>, x: State<S>, a: Event) -> bool {
    g(x,a) && read::service_step(m)(x,a,read::next(m,x,a))
}

pub open spec fn fired<S>(m: Program<S>, g: Gate<S>, x: State<S>, script: Seq<Event>) -> Tape
    decreases script.len(),
{
    if script.len()==0 { Seq::empty() } else {
        let a=script[0]; let tail=script.drop_first();
        if ready(m,g,x,a) { seq![process_step(x.cfg.net,a)] + fired(m,g,read::next(m,x,a),tail) }
        else { fired(m,g,x,tail) }
    }
}

pub open spec fn end<S>(m: Program<S>, g: Gate<S>, x: State<S>, script: Seq<Event>) -> State<S> {
    tape::after(m,x,fired(m,g,x,script))
}

pub open spec fn attempt<S>(m: Program<S>, g: Gate<S>, x: State<S>, a: Event) -> State<S> {
    if ready(m,g,x,a) { read::next(m,x,a) } else { x }
}

pub(crate) proof fn scan_step<S>(m: Program<S>, g: Gate<S>, x: State<S>, s: Seq<Event>)
    requires s.len()>0,
    ensures end(m,g,x,s)==end(m,g,attempt(m,g,x,s[0]),s.drop_first()),
{
    if ready(m,g,x,s[0]) {
        let t=fired(m,g,x,s); assert(t[0]==process_step(x.cfg.net,s[0]));
        assert(t.drop_first() =~= fired(m,g,attempt(m,g,x,s[0]),s.drop_first()));
    }
}

pub open spec fn prepare<S>() -> Gate<S> {
    |x:State<S>,a:Event| crate::independent_preparations::ordinary_input(process_step(x.cfg.net,a))
}

pub open spec fn admissible_tape<S>(m: Program<S>, g: Gate<S>, x: State<S>, t: Tape) -> bool
    decreases t.len(),
{
    t.len()==0 || (ready(m,g,x,t[0].action) && t[0]==process_step(x.cfg.net,t[0].action)
        && admissible_tape(m,g,read::next(m,x,t[0].action),t.drop_first()))
}

pub proof fn prepared_tape<S>(m: Program<S>, x: State<S>, t: Tape)
    requires tape::plays(m,x,t), forall|i:int| 0<=i<t.len() ==> crate::independent_preparations::ordinary_input(#[trigger] t[i]),
    ensures admissible_tape(m,prepare(),x,t),
    decreases t.len(),
{
    if t.len()>0 {
        assert(crate::independent_preparations::ordinary_input(t[0])); let tail=t.drop_first();
        assert forall|j:int| 0<=j<tail.len() implies crate::independent_preparations::ordinary_input(#[trigger] tail[j])
        by {assert(tail[j]==t[j+1]); assert(crate::independent_preparations::ordinary_input(t[j+1]));}
        prepared_tape(m,read::next(m,x,t[0].action),tail);
    }
}

pub open spec fn fits_front<S>(m: Program<S>, g: Gate<S>, x: State<S>, t: Tape, a: Event) -> bool {
    !ready(m,g,x,a) || (t.len()>0 && t[0].action==a)
}

// A concrete external choice, including the case that one tape has ended
// while its machine would still accept the other tape's next action.
pub open spec fn conflict<S>(m: Program<S>, g: Gate<S>, x: State<S>, y: State<S>, a: Tape, b: Tape) -> bool {
    (a.len()>0 || b.len()>0)
        && (a.len()>0 ==> ready(m,g,x,a[0].action) && ready(m,g,y,a[0].action) && (b.len()==0 || b[0].action!=a[0].action))
        && (b.len()>0 ==> ready(m,g,y,b[0].action) && ready(m,g,x,b[0].action) && (a.len()==0 || a[0].action!=b[0].action))
}

// A certificate uses actual tapes on both sides, through the last matched
// proposals. It contains native states and executable guards at the frontier.
pub open spec fn blocked<S>(m: Program<S>, g: Gate<S>, x: State<S>, y: State<S>, a: Tape, b: Tape, s: Seq<Event>) -> bool {
    let u=fired(m,g,x,s); let v=fired(m,g,y,s);
    u.len()<=a.len() && v.len()<=b.len() && a.take(u.len() as int)==u && b.take(v.len() as int)==v
        && conflict(m,g,end(m,g,x,s),end(m,g,y,s),a.skip(u.len() as int),b.skip(v.len() as int))
}

pub open spec fn realizes<S>(m: Program<S>, g: Gate<S>, x: State<S>, y: State<S>, a: Tape, b: Tape, s: Seq<Event>) -> bool {
    fired(m,g,x,s)==a && fired(m,g,y,s)==b
}

// Follow enabled fronts against their real counterpart. A mandatory
// callback can proceed on both sides with different incoming packets, or
// on just its enabled side. No step of either native tape is discarded.
proof fn match_fronts<S>(m: Program<S>, g: Gate<S>, x: State<S>, y: State<S>, a: Tape, b: Tape) -> (s: Seq<Event>)
    requires admissible_tape(m,g,x,a), admissible_tape(m,g,y,b),
    ensures realizes(m,g,x,y,a,b,s) || blocked(m,g,x,y,a,b,s),
    decreases a.len()+b.len(),
{
    if a.len()==0 && b.len()==0 { assert(a =~= Seq::empty() && b =~= Seq::empty()); return Seq::empty(); }
    if conflict(m,g,x,y,a,b) {
        assert(a.take(0) =~= Seq::empty() && b.take(0) =~= Seq::empty());
        assert(a.skip(0) =~= a && b.skip(0) =~= b);
        return Seq::empty();
    }
    let e=if a.len()>0 && fits_front(m,g,y,b,a[0].action) { a[0].action } else { b[0].action };
    let left=ready(m,g,x,e); let right=ready(m,g,y,e);
    assert(left || right); assert(fits_front(m,g,x,a,e) && fits_front(m,g,y,b,e));
    let u=if left {a.drop_first()} else {a}; let v=if right {b.drop_first()} else {b};
    let xx=attempt(m,g,x,e); let yy=attempt(m,g,y,e);
    let tail=match_fronts(m,g,xx,yy,u,v); let s=seq![e]+tail;
    assert(s.drop_first() =~= tail); scan_step(m,g,x,s); scan_step(m,g,y,s);
    let h=fired(m,g,x,s); let k=fired(m,g,y,s);
    let h0=fired(m,g,xx,tail); let k0=fired(m,g,yy,tail);
    if left { assert(h =~= seq![a[0]]+h0); } else {assert(h==h0);}
    if right { assert(k =~= seq![b[0]]+k0); } else {assert(k==k0);}
    if realizes(m,g,xx,yy,u,v,tail) { assert(a =~= h && b =~= k); }
    else {
        assert(a.take(h.len() as int) =~= h && b.take(k.len() as int) =~= k);
        assert(a.skip(h.len() as int) =~= u.skip(h0.len() as int));
        assert(b.skip(k.len() as int) =~= v.skip(k0.len() as int));
    }
    s
}

// Quantify over all possible common interleavings first. A conflict on a
// single greedy attempt does not establish that no other interleaving works.
pub proof fn common_proposals_or_conflict<S>(m: Program<S>, g: Gate<S>, x: State<S>, y: State<S>, a: Tape, b: Tape) -> (s: Seq<Event>)
    requires admissible_tape(m,g,x,a), admissible_tape(m,g,y,b),
    ensures realizes(m,g,x,y,a,b,s) || (blocked(m,g,x,y,a,b,s)
        && forall|u:Seq<Event>| !#[trigger] realizes(m,g,x,y,a,b,u)),
{
    if exists|u:Seq<Event>| #[trigger] realizes(m,g,x,y,a,b,u) {
        choose|u:Seq<Event>| #[trigger] realizes(m,g,x,y,a,b,u)
    } else { match_fronts(m,g,x,y,a,b) }
}

// SR2 starts after its invocation. Protect the three original weak slots.
// Every other ordinary packet is offered to the real handler. After its
// own first return an arm stops taking proposals.
pub open spec fn weak_work(e:Observation) -> bool {
    match e.action {
        Action::Send(_,q) => q.path==Path::Weak,
        Action::Deliver(_) => e.incoming.is_some() && e.incoming.unwrap().path==Path::Weak,
        Action::Local(_,w) | Action::ClientInput(_,w) => w is Copy || w is WeakConfirm,
        _ => false,
    }
}

pub open spec fn postponed<S>(b:Fork,quiet:bool) -> wait::Relation<State<S>,Event> {
    |x:State<S>,a:Event,y:State<S>| calls::evidence(b)(x,a,y) || (quiet && weak_work(process_step(x.cfg.net,a)))
}

pub open spec fn second<S>(quiet:bool,res: spec_fn(S)->Option<int>) -> Gate<S> {
    |x:State<S>,a:Event| !read::returned(res)(x) && (tape::slot(a).is_none() || tape::slot(a).unwrap()>2)
        && (!quiet || !weak_work(process_step(x.cfg.net,a)))
}

pub open spec fn path<S>(m:Program<S>, x:State<S>, t:Tape) -> Service<S> {
    wait::Path{states:Seq::new(t.len()+1,|i:int|tape::after(m,x,t.take(i))),actions:asm::actions(t)}
}

pub(crate) proof fn physical_steps<S>(m:Program<S>, g:Gate<S>, x:State<S>, t:Tape)
    requires admissible_tape(m,g,x,t),
    ensures ({
        let p=path(m,x,t); p.states[0]==x && p.states.last()==tape::after(m,x,t)
            && wait::valid_edges(read::service_step(m),p) && crate::fork_delivery::service_prefix(m,x,p.actions)
            && asm::drive(m,x,p.actions)==tape::after(m,x,t)
            && forall|i:int| 0<=i<t.len() ==> {
                let a=#[trigger] p.actions[i]; g(p.states[i],a) && t[i]==process_step(p.states[i].cfg.net,a)
            }
    }),
    decreases t.len(),
{
    let p=path(m,x,t);
    assert(t.take(0) =~= Seq::empty() && t.take(t.len() as int) =~= t);
    if t.len()>0 {
        let a=t[0].action; let y=read::next(m,x,a); let u=t.drop_first(); let q=path(m,y,u);
        physical_steps(m,g,y,u);
        assert(p.actions.drop_first() =~= q.actions);
        assert forall|i:int| 1<=i<=t.len() implies #[trigger] p.states[i]==q.states[i-1] by {
            assert(t.take(i)[0]==t[0] && t.take(i).drop_first() =~= u.take(i-1));
        }
        assert forall|i:int| 0<=i<p.actions.len() implies {
            let e=#[trigger] p.actions[i]; read::service_step(m)(p.states[i],e,p.states[i+1])
               && g(p.states[i],e) && t[i]==process_step(p.states[i].cfg.net,e)
        } by {if i>0 {assert(p.actions[i]==q.actions[i-1] && t[i]==u[i-1]);}}
    }
}

pub(crate) proof fn firing_is_native<S>(m:Program<S>,g:Gate<S>,x:State<S>,s:Seq<Event>)
    ensures admissible_tape(m,g,x,fired(m,g,x,s)),
    decreases s.len(),
{
    if s.len()>0 {
        let e=s[0];let y=attempt(m,g,x,e);let tail=s.drop_first();firing_is_native(m,g,y,tail);
        if ready(m,g,x,e) {assert(fired(m,g,x,s).drop_first() =~= fired(m,g,y,tail));}
    }
}

pub open spec fn issued<S>(x:State<S>, b:Fork) -> bool {
    crate::survivors::after_crash(x.cfg.net) && read::issued_to_majority(x) && traffic::weak_queue(x,b)
}

pub(crate) proof fn issue_step<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,a:Event)
    requires issued(x,b), ready(m,second(quiet,res),x,a),
    ensures issued(read::next(m,x,a),b),
{
    let y=read::next(m,x,a);
    let (r,q)=choose|r:Replica,q:Replica| r!=q && x.requested.contains(r) && x.requested.contains(q)
        && #[trigger] live(x.cfg.net,at(r)) && #[trigger] live(x.cfg.net,at(q));
    assert(live(y.cfg.net,at(r)) && live(y.cfg.net,at(q)));
    assert forall|id:nat| id<=2 implies #[trigger] y.cfg.net.pending.get(id)==state_after(b,5).pending.get(id)
        by {assert(x.cfg.net.pending.get(id)==state_after(b,5).pending.get(id));}
}

pub(crate) proof fn issue_remains<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,s:Seq<Event>)
    requires issued(x,b),
    ensures issued(end(m,second(quiet,res),x,s),b),
    decreases s.len(),
{
    if s.len()>0 {
        let g=second(quiet,res);let a=s[0];let y=attempt(m,g,x,a);
        if ready(m,g,x,a) { issue_step(quiet,m,res,b,x,a); }
        scan_step(m,g,x,s);issue_remains(quiet,m,res,b,y,s.drop_first());
    }
}

pub open spec fn opportunity<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,run:fair::Runnable,b:Fork,x:State<S>) -> bool {
    (forall|e:fair::Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run) ==>
        exists|i:nat| #[trigger] majority::published(majority::Caller::Second,m,res)((e.state)(i)))
        && (exists|e:fair::Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run))
        && !wait::needs_class(read::service_step(m),read::returned(res),x,postponed(b,quiet))
}

pub proof fn opportunity_from_hybrid_a<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,run:fair::Runnable,
    base:State<S>,b:Fork,x:State<S>)
    requires issued(x,b),read::reached(m,base,x),majority::eventual(m,res,base,run),
        exists|e:fair::Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run),
        !wait::needs_class(read::service_step(m),read::returned(res),x,postponed(b,quiet)),
    ensures opportunity(quiet,m,res,run,b,x),
{
    assert(majority::due(majority::Caller::Second,x));
}

// Continuation opportunities at reached pending native cuts. Requiring
// beta progress only at its initial cut would miss partial beta progress
// during alpha's service.
pub open spec fn opportunities<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,run:fair::Runnable,b:Fork,x:State<S>) -> bool {
    forall|s:Seq<Event>| #[trigger] crate::fork_delivery::service_prefix(m,x,s) ==> {
        let y=asm::drive(m,x,s); issued(y,b) && !read::returned(res)(y) ==> opportunity(quiet,m,res,run,b,y)
    }
}

pub(crate) proof fn finish_one<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,run:fair::Runnable,b:Fork,x:State<S>) -> (p:Service<S>)
    requires issued(x,b), !read::returned(res)(x), opportunity(quiet,m,res,run,b,x),
    ensures wait::first_return(read::service_step(m),read::returned(res),x,p), !wait::uses(p,postponed(b,quiet)),
{
    let e=choose|e:fair::Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run);
    let st=read::service_step(m);let d=read::returned(res);
    assert(exists|i:nat| #[trigger] majority::published(majority::Caller::Second,m,res)((e.state)(i)));
    let i=choose|i:nat| #[trigger] majority::published(majority::Caller::Second,m,res)((e.state)(i));
    fair::initial_steps(m,x,e,i);let q=fair::initial_block(e,i);
    crate::read_nonblocking::from_path(st,d,q,0);assert(crate::read_nonblocking::possible(st,d,x));
    crate::read_nonblocking::first_response_iff(st,d,x);
    choose|p:Service<S>| #[trigger] wait::first_return(st,d,x,p) && !wait::uses(p,postponed(b,quiet))
}

pub(crate) proof fn native_script<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,p:Service<S>,i:nat)
    requires p.states.len()==p.actions.len()+1, i<=p.actions.len(), issued(p.states[i as int],b),
        calls::distinct_weak_names(m) || (forall|j:int| 0<=j<p.actions.len() && (#[trigger] p.actions[j]) is Send
            ==> p.actions[j]->Send_0>2),
        wait::first_return(read::service_step(m),read::returned(res),p.states[0],p), !wait::uses(p,postponed(b,quiet)),
    ensures end(m,second(quiet,res),p.states[i as int],p.actions.skip(i as int))==p.states.last(),
    decreases p.actions.len()-i,
{
    let x=p.states[i as int];let s=p.actions.skip(i as int);
    if i<p.actions.len() {
        let a=p.actions[i as int];let y=p.states[i as int+1];
        assert(read::service_step(m)(x,a,y) && !postponed(b,quiet)(x,a,y));
        if a is Deliver && a->Deliver_0<=2 {
            let id=a->Deliver_0;
            assert(x.cfg.net.pending.get(id)==state_after(b,5).pending.get(id));
            assert(id==0 || id==1 || id==2);
            assert(false);
        }
        assert(ready(m,second(quiet,res),x,a));
        issue_step(quiet,m,res,b,x,a);
        native_script(quiet,m,res,b,p,i+1);assert(s.drop_first() =~= p.actions.skip(i as int+1));
        scan_step(m,second(quiet,res),x,s);
    } else {assert(s =~= Seq::empty());}
}

pub(crate) proof fn append_script<S>(m:Program<S>,g:Gate<S>,x:State<S>,a:Seq<Event>,b:Seq<Event>)
    ensures end(m,g,x,a+b)==end(m,g,end(m,g,x,a),b),
        fired(m,g,x,a+b)==fired(m,g,x,a)+fired(m,g,end(m,g,x,a),b),
    decreases a.len(),
{
    if a.len()==0 {assert(a+b =~= b);} else {
        assert((a+b)[0]==a[0] && (a+b).drop_first() =~= a.drop_first()+b);
        scan_step(m,g,x,a);scan_step(m,g,x,a+b);append_script(m,g,attempt(m,g,x,a[0]),a.drop_first(),b);
        assert(fired(m,g,x,a+b) =~= fired(m,g,x,a)+fired(m,g,end(m,g,x,a),b));
    }
}

proof fn stopped<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>)
    requires read::returned(res)(x),
    ensures end(m,second(quiet,res),x,s)==x,
    decreases s.len(),
{
    if s.len()>0 {scan_step(m,second(quiet,res),x,s);stopped(quiet,m,res,x,s.drop_first());}
}

pub open spec fn second_return<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,s:Seq<Event>) -> bool {
    let g=second(quiet,res);let t=fired(m,g,x,s);let p=path(m,x,t);
    wait::first_return(read::service_step(m),read::returned(res),x,p) && !wait::uses(p,postponed(b,quiet))
        && p.states.last()==end(m,g,x,s) && issued(p.states.last(),b)
        && (forall|i:int| 0<=i<t.len() ==> #[trigger] t[i]==process_step(p.states[i].cfg.net,p.actions[i]))
}

// The strong-only suffix preserves BOTH original quorum cells at every
// physical cut. Guards and private metadata can still change at each step.
pub proof fn quiet_service_cells<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,s:Seq<Event>,j:nat)
    requires second_return(true,m,res,b,x,s), j<=fired(m,second(true,res),x,s).len(),
    ensures path(m,x,fired(m,second(true,res),x,s)).states[j as int].cfg.net.locals==x.cfg.net.locals,
    decreases j,
{
    let p=path(m,x,fired(m,second(true,res),x,s));
    if j>0 {
        let i=j as int-1;let u=p.states[i];let v=p.states[j as int];let a=p.actions[i];
        quiet_service_cells(m,res,b,x,s,(j-1) as nat);
        assert(read::service_step(m)(u,a,v));assert(!postponed(b,true)(u,a,v));
        assert(v.cfg.net.locals =~= u.cfg.net.locals) by {
            assert forall|r:Replica| (#[trigger] local_input(u.cfg.net,a,r)).is_none()
                || !(local_input(u.cfg.net,a,r).unwrap() is Copy) by {};
        }
    }
}

pub(crate) proof fn returned_run<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,x:State<S>,s:Seq<Event>)
    requires issued(x,b), !read::returned(res)(x), read::returned(res)(end(m,second(quiet,res),x,s)),
    ensures second_return(quiet,m,res,b,x,s),
{
    let g=second(quiet,res);let t=fired(m,g,x,s);let p=path(m,x,t);
    firing_is_native(m,g,x,s);physical_steps(m,g,x,t);issue_remains(quiet,m,res,b,x,s);
    assert forall|i:int| 0<=i<p.actions.len() implies !read::returned(res)(#[trigger] p.states[i]) by {assert(g(p.states[i],p.actions[i]));}
    assert forall|i:int| 0<=i<p.actions.len() implies !postponed(b,quiet)(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        by {assert(g(p.states[i],p.actions[i]));}
}

// Construct a common external SR2 schedule even for different checkpoints
// and arbitrary mandatory guards. Every accepted proposal is executed.
// First run alpha to return, then finish beta at its *reached* pending state.
pub proof fn common_second_proposals<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,run:fair::Runnable,n:Notice,
    x:State<S>,y:State<S>) -> (s:Seq<Event>)
    requires issued(x,alpha(n)),issued(y,beta(n)),!read::returned(res)(x),!read::returned(res)(y),
        calls::distinct_weak_names(m), opportunity(quiet,m,res,run,alpha(n),x), opportunities(quiet,m,res,run,beta(n),y),
    ensures second_return(quiet,m,res,alpha(n),x,s),second_return(quiet,m,res,beta(n),y,s),
{
    let g=second(quiet,res);let a=finish_one(quiet,m,res,run,alpha(n),x);let head=a.actions;
    native_script(quiet,m,res,alpha(n),a,0);assert(head.skip(0) =~= head);
    let z=end(m,g,y,head);let t=fired(m,g,y,head);
    firing_is_native(m,g,y,head);physical_steps(m,g,y,t);issue_remains(quiet,m,res,beta(n),y,head);
    let s=if read::returned(res)(z) {head} else {
        assert(crate::fork_delivery::service_prefix(m,y,asm::actions(t)));
        assert(opportunity(quiet,m,res,run,beta(n),z));
        let b=finish_one(quiet,m,res,run,beta(n),z);native_script(quiet,m,res,beta(n),b,0);
        assert(b.actions.skip(0) =~= b.actions);
        append_script(m,g,x,head,b.actions);append_script(m,g,y,head,b.actions);
        stopped(quiet,m,res,a.states.last(),b.actions);
        head+b.actions
    };
    returned_run(quiet,m,res,alpha(n),x,s);returned_run(quiet,m,res,beta(n),y,s);s
}
}
