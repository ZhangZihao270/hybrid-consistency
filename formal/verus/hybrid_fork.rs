// Hybrid A at the two first-read references and at the independent caller.
// Only alpha and beta enter H. The early failure is used to select one
// finite C2 service, never to supply a strong history for H.
use vstd::prelude::*;
use crate::{Branch,Replica,checkpoint::*,delivery::*,protocol::*};
use crate::fair_read as fair;
use crate::first_assembly::*;
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_schedule::{self as first,reference};
use crate::first_service_loss as loss;
use crate::first_splice as s;
use crate::fork_dependencies as dep;
use crate::fork_delivery as transport;
use crate::hybrid_majority as model;
use crate::independent_read::{self as read,State};
use crate::ordinary_service::{Configuration,apply};
use crate::promotion_wait as wait;
use crate::read_call::{Program,Event};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;

verus! {

// Native sender namespaces may be unbounded. The finite reservation used
// by the replay is computed only after the two finite references are chosen.
pub type Issuer = spec_fn(nat)->Replica;
pub open spec fn proper(l:Lanes,who:Issuer) -> bool {
    lanes_ok(l) && forall|i:nat| i>5 && #[trigger] l.contains_key(i) ==> l[i]==who(i)
}
pub open spec fn native<S>(p:Service<S>,who:Issuer) -> bool {
    (forall|i:int| 0<=i<p.actions.len() ==> match #[trigger] p.actions[i] {
        Action::Send(id,q)=>id>5 && id!=11 && id!=12 && q.from==at(who(id)),_=>true})
        && (forall|i:int,j:int| 0<=i<j<p.actions.len() && (#[trigger] p.actions[i]) is Send && (#[trigger] p.actions[j]) is Send
            ==> p.actions[i]->Send_0!=p.actions[j]->Send_0)
}
pub open spec fn ids<S>(p:Service<S>) -> Set<nat> {
    p.actions.map_values(|a:Event|s::slot(a).unwrap_or(0)).to_set()
}
pub open spec fn allocation<S>(who:Issuer,a:Service<S>,b:Service<S>) -> Lanes {
    let used=ids(a).union(ids(b)).filter(|i:nat|i>5 && i!=11 && i!=12);
    Map::new(used,who).insert(2,Replica::R3).insert(3,Replica::R1).insert(4,Replica::R2)
}
proof fn named_prefix<S>(p:Service<S>,l:Lanes,who:Issuer)
    requires native(p,who),proper(l,who),
        forall|i:nat| i>5 && i!=11 && i!=12 && #[trigger] ids(p).contains(i) ==> l.contains_key(i),
    ensures dep::named(p,l),
{
    assert forall|i:int| 0<=i<p.actions.len() implies match #[trigger] p.actions[i] {
        Action::Send(id,q)=>id>5 && id!=11 && id!=12 && q.from is At && l.get(id)==Some(q.from->At_0),_=>true} by {
        if let Action::Send(id,q)=p.actions[i] {
            let slots=p.actions.map_values(|a:Event|s::slot(a).unwrap_or(0));assert(slots[i]==id);assert(slots.contains(id));
            assert(ids(p).contains(id));assert(l.contains_key(id));
        }
    }
}
pub proof fn finite_allocation<S>(a:Service<S>,b:Service<S>,who:Issuer)
    requires native(a,who),native(b,who),
    ensures proper(allocation(who,a,b),who),dep::named(a,allocation(who,a,b)),dep::named(b,allocation(who,a,b)),
{
    let l=allocation(who,a,b);assert(proper(l,who));named_prefix(a,l,who);named_prefix(b,l,who);
}
pub open spec fn clean<S>(m:Program<S>,b:Fork,p:Service<S>) -> bool {
    cause::returning(m,b,p) && !wait::uses(p,dep::promotion(b)) && !wait::uses(p,dep::boundary(b))
}
// A communication interface, observable in the real reference. It says
// nothing about either result, the private survivor states or termination.
pub open spec fn wire_route<S>(b:Fork,p:Service<S>,who:Issuer,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    native(p,who) && cause::source_shape(s::record(p,0),b,answers)
}
pub open spec fn missing_route<S>(m:Program<S>,b:Fork,who:Issuer,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    (exists|p:Service<S>| #[trigger] clean(m,b,p)) && (forall|p:Service<S>| #[trigger] clean(m,b,p) ==> !wire_route(b,p,who,answers))
}
proof fn choose_route<S>(m:Program<S>,b:Fork,who:Issuer,answers:spec_fn(Packet<Wire>)->bool,w:Service<S>) -> (p:Service<S>)
    requires clean(m,b,w),!missing_route(m,b,who,answers),
    ensures clean(m,b,p),wire_route(b,p,who,answers),
{
    choose|p:Service<S>| #[trigger] clean(m,b,p) && wire_route(b,p,who,answers)
}
proof fn omit<S>(m:Program<S>,b:Fork,st:wait::Relation<State<S>,Event>,class:wait::Relation<State<S>,Event>)
    -> (p:Service<S>)
    requires wait::can_finish(st,mail::posted(m),reference(m,b,5)),!dep::indispensable(m,b,class,st),
    ensures wait::first_return(nb::ordinary(st,class),mail::posted(m),reference(m,b,5),p),
{
    let d=mail::posted(m);let x=reference(m,b,5);
    if wait::needs_class(st,d,x,class) {dep::certify_dependency(m,b,st,class);}
    let p=choose|p:Service<S>| #[trigger] wait::first_return(st,d,x,p) && !wait::uses(p,class);
    let plain=nb::ordinary(st,class);
    assert forall|i:int| 0<=i<p.actions.len() implies plain(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        by {assert(st(p.states[i],p.actions[i],p.states[i+1]));}
    p
}
pub open spec fn weak_dependency<S>(m:Program<S>,b:Fork) -> bool {
    dep::indispensable(m,b,dep::promotion(b),mail::active_step(m))
}
pub open spec fn other_dependency<S>(m:Program<S>,b:Fork) -> bool {
    dep::indispensable(m,b,dep::boundary(b),dep::weak_free(m,b))
}
proof fn choose_service<S>(m:Program<S>,b:Fork,run:fair::Runnable) -> (p:Service<S>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),loss::reference_progress(m,b,run),
        !weak_dependency(m,b),!other_dependency(m,b),
    ensures clean(m,b,p),
{
    let x=reference(m,b,5);let d=mail::posted(m);let st=mail::active_step(m);let plain=dep::weak_free(m,b);
    loss::finite_service(m,b,run);let p=choose|p:Service<S>| #[trigger] cause::returning(m,b,p);
    assert(wait::can_finish(st,d,x));let w=omit(m,b,st,dep::promotion(b));assert(wait::can_finish(plain,d,x));
    let t=omit(m,b,plain,dep::boundary(b));let cut=nb::ordinary(plain,dep::boundary(b));
    assert forall|i:int| 0<=i<t.actions.len() implies st(t.states[i],#[trigger] t.actions[i],t.states[i+1])
        && !dep::promotion(b)(t.states[i],t.actions[i],t.states[i+1]) && !dep::boundary(b)(t.states[i],t.actions[i],t.states[i+1])
        by {assert(cut(t.states[i],t.actions[i],t.states[i+1]));}
    t
}
pub open spec fn held_in_replay<S>(m:Program<S>,t:Configuration<S>,a:Seq<Event>,v:int) -> bool
    decreases a.len(),
{
    (t.net.locals)(Replica::R1)==v || (t.net.locals)(Replica::R2)==v ||
        (a.len()>0 && held_in_replay(m,apply(m,t,a[0]),a.drop_first(),v))
}
proof fn replay_sample<S>(m:Program<S>,p:Service<S>,j:nat,k:nat,r:Replica,t:Configuration<S>)
    requires p.states.len()==p.actions.len()+1,j<=k<p.states.len(),wait::valid_edges(read::service_step(m),p),
        read::covers(p.states[j as int],t),live_pair().contains(r),
    ensures held_in_replay(m,t,read::retained_actions(p,j),(p.states[k as int].cfg.net.locals)(r)),
    decreases k-j,
{
    if j<k {
        let x=p.states[j as int];let a=p.actions[j as int];let y=p.states[j as int+1];
        assert(read::service_step(m)(x,a,y));read::project_step(m,m,x,y,t,a);
        if process_step(x.cfg.net,a).actor==Process::FirstClient {replay_sample(m,p,j+1,k,r,t);}
        else {assert(read::retained_actions(p,j).drop_first() =~= read::retained_actions(p,j+1));replay_sample(m,p,j+1,k,r,apply(m,t,a));}
    }
}
pub open spec fn target<S>(m:Program<S>,l:Lanes,b:Fork,ta:s::Tape,tb:s::Tape) -> Configuration<S> {
    drive(m,fork_end(m,l,b,ta,tb),pair::close(true)).cfg
}
pub struct Completions<S> {
    pub alpha:Service<S>,pub beta:Service<S>,pub second:Service<S>,pub value:int,
}
pub open spec fn arm<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,
    ta:s::Tape,tb:s::Tape,p:Service<S>,v:int,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    let issued=drive(m,fork_end(m,l,b,ta,tb),pair::close(true));let t=issued.cfg;let a=read::retained_actions(p,0);let end=drive(m,issued,a);
    transport::service_prefix(m,issued,a) && transport::delayed_reply(end,b,answers) && end.cfg.net.pending.get(dep::rival(b))==Some(packet_for(b,dep::rival(b)))
        && end.cfg==loss::final_cfg(m,t,a) && loss::original_read(m,first,l,b,ta,tb,answers) && prefix(m,fork_end(m,l,b,ta,tb),pair::close(true),true)
        && loss::responds(m,res,t,a,v) && loss::observed_suffix(m,t,a)==loss::service_inputs(p,0)
        && held_in_replay(m,t,a,v) && loss::final_cfg(m,t,a).net.pending.get(2)==Some(packet_for(b,2))
        && enabled(loss::final_cfg(m,t,a).net,Action::Deliver(2))
}
pub open spec fn completed<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:Issuer,answers:spec_fn(Packet<Wire>)->bool,w:Completions<S>) -> bool {
    let ta=s::record(w.alpha,0);let tb=s::record(w.beta,0);let l=allocation(who,w.alpha,w.beta);let path=w.second;
    let a=read::retained_actions(path,0);let e=pair::auxiliary(m,l,n,ta,tb);
    clean(m,alpha(n),w.alpha) && clean(m,beta(n),w.beta)
        && read::reached(m,entry(m,l),e) && read::issued_to_majority(e)
        && wait::first_return(read::service_step(m),read::returned(res),e,path)
        && w.value==res((path.states.last().cfg.private)(Process::SecondClient)).unwrap()
        && proper(l,who) && (forall|b:Fork| b.notice==n ==> #[trigger] arm(m,first,res,l,b,ta,tb,path,w.value,answers))
}
proof fn auxiliary_sample<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    ta:s::Tape,tb:s::Tape,p:Service<S>)
    requires pair::sources(m,l,n,ta,tb),dispatch::initiates(m),issue::can_issue(m,res),model::sampling(m,first,res,entry(m,l)),
        prefix(m,entry(m,l),pair::early_actions(n,ta,tb),false),pair::before_issue(m,prepared(m,l,None,n,ta,tb),l),
        read::issued_to_majority(pair::auxiliary(m,l,n,ta,tb)),
        wait::first_return(read::service_step(m),read::returned(res),pair::auxiliary(m,l,n,ta,tb),p),
    ensures model::held(p.states,live_pair(),res((p.states.last().cfg.private)(Process::SecondClient)).unwrap()),
{
    let base=entry(m,l);let e=pair::auxiliary(m,l,n,ta,tb);
    let prep=prepared(m,l,None,n,ta,tb);let begin=boot(None)+actions(work_pair(ta,tb,n));
    let start=seq![Action::CrashR3,Action::StartSecondClient];let x=drive(m,prep,start);
    let h=model::second_head(m,x);
    prefix_concat(m,base,begin,pair::close(false),false);assert(drive(m,base,begin)==prep) by {
        launch(m,l,None);pair::outside_work(m,l,n,ta,tb,None);native_prefix(m,root(m,l,None),work_pair(ta,tb,n),false);
        prefix_concat(m,base,boot(None),actions(work_pair(ta,tb,n)),false);
    }
    assert(start+h.actions =~= pair::close(false));prefix_concat(m,prep,start,h.actions,false);prefix_concat(m,base,begin,start,false);
    loss::reachable(m,base,begin+start);
    assert((x.cfg.private)(Process::SecondClient)==issue::started(m)) by {reveal_with_fuel(drive,3);}
    assert(h.states.last()==e) by {reveal_with_fuel(drive,3);}
    assert(model::sole(x.cfg.net,live_pair())) by {assert(live_pair().len()==2);reveal_with_fuel(drive,3);}
    assert(x.requested==Set::<Replica>::empty() && x.cfg.net.second_started) by {reveal_with_fuel(drive,3);}
    assert(read::reached(m,base,x));assert(prefix(m,x,h.actions,false));
    model::second_quorum_rule(m,first,res,base,x,p);
}
proof fn replay_arm<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,ta:s::Tape,tb:s::Tape,
    p:Service<S>,v:int,answers:spec_fn(Packet<Wire>)->bool)
    requires loss::original_read(m,first,l,b,ta,tb,answers),prefix(m,fork_end(m,l,b,ta,tb),pair::close(true),true),
        pair::sources(m,l,b.notice,ta,tb),
        ({let z=fork_end(m,l,b,ta,tb);let issued=drive(m,z,pair::close(true));issued.owners==p.states[0].owners
            && issued.reserved.subset_of(p.states[0].reserved) && z.cfg.net.pending.submap_of(issued.cfg.net.pending)}),
        wait::first_return(read::service_step(m),read::returned(res),p.states[0],p),
        read::covers(p.states[0],target(m,l,b,ta,tb)),p.states[0].reserved.contains(2),!p.states[0].cfg.net.pending.contains_key(2),
        target(m,l,b,ta,tb).net.pending.get(2)==Some(packet_for(b,2)),v==res((p.states.last().cfg.private)(Process::SecondClient)).unwrap(),
        model::held(p.states,live_pair(),v),
    ensures arm(m,first,res,l,b,ta,tb,p,v,answers),
{
    let issued=drive(m,fork_end(m,l,b,ta,tb),pair::close(true));let suffix=read::retained_actions(p,0);
    transport::replay_allocated(m,p,0,issued);transport::original_packets(m,first,l,b,ta,tb,answers,issued,suffix);
    let t=target(m,l,b,ta,tb);assert(enabled(t.net,Action::Deliver(2)));loss::replay_return(m,res,p,0,t);
    let (k,r)=choose|k:int,r:Replica| 0<=k<p.states.len() && live_pair().contains(r) && #[trigger] (p.states[k].cfg.net.locals)(r)==v;
    replay_sample(m,p,0,k as nat,r,t);
}
pub(crate) proof fn common_completion<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:Issuer,answers:spec_fn(Packet<Wire>)->bool,run:fair::Runnable,pa:Service<S>,pb:Service<S>,audit:spec_fn(Packet<Wire>)->bool) -> (w:Completions<S>)
    requires dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),clean(m,alpha(n),pa),clean(m,beta(n),pb),
        native(pa,who),native(pb,who),cause::source_shape(s::record(pa,0),alpha(n),answers),cause::source_shape(s::record(pb,0),beta(n),answers),
        forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b) && cause::member_sample(m,first,b),
        ({let x=entry(m,allocation(who,pa,pb));model::read_a(m,first,res,x,run) && fair::pending_turns(m,res,x,run)}),
        ({let e=pair::auxiliary(m,allocation(who,pa,pb),n,s::record(pa,0),s::record(pb,0));
            !wait::needs_class(read::service_step(m),read::returned(res),e,mail::receipt_of(audit))}),
    ensures completed(m,first,res,n,who,answers,w),w.alpha==pa,w.beta==pb,!wait::uses(w.second,mail::receipt_of(audit)),
{
    hide(read::covers);hide(s::after);hide(s::plays);hide(drive);hide(loss::original_read);hide(prefix);hide(arm);
    let a=alpha(n);let b=beta(n);let l=allocation(who,pa,pb);let ta=s::record(pa,0);let tb=s::record(pb,0);let base=entry(m,l);
    assert(dispatch::weak_open(m,a) && dispatch::weak_open(m,b));finite_allocation(pa,pb,who);
    dep::no_boundary_gives_routing(m,a,l,pa);dep::no_boundary_gives_routing(m,b,l,pb);
    s::recorded(m,pa,0);s::recorded(m,pb,0);assert(pair::sources(m,l,n,ta,tb));
    loss::selected_reads(m,res,first,l,a,pa,pb,answers);loss::selected_reads(m,res,first,l,b,pa,pb,answers);
    model::availability_at_both_clients(m,res,base,run);fair::fair_progress_offers_service(m,res,base,run);
    let e=pair::auxiliary(m,l,n,ta,tb);let st=read::service_step(m);let d=read::returned(res);
    assert(nb::possible(st,d,e));nb::first_response_iff(st,d,e);assert(wait::can_finish(st,d,e));
    let p=choose|p:Service<S>| #[trigger] wait::first_return(st,d,e,p) && !wait::uses(p,mail::receipt_of(audit));
    let v=res((p.states.last().cfg.private)(Process::SecondClient)).unwrap();
    pair::cover_after_service(m,res,l,a,ta,tb);pair::cover_after_service(m,res,l,b,ta,tb);auxiliary_sample(m,first,res,l,n,ta,tb,p);
    replay_arm(m,first,res,l,a,ta,tb,p,v,answers);replay_arm(m,first,res,l,b,ta,tb,p,v,answers);
    assert forall|f:Fork| f.notice==n implies #[trigger] arm(m,first,res,l,f,ta,tb,p,v,answers) by {
        if f.branch==Branch::Alpha {assert(f==a);} else {assert(f==b);}
    }
    Completions{alpha:pa,beta:pb,second:p,value:v}
}
// A is used on precisely these physically admissible restart states. The
// service monitor accepts the specified workload and allocator. Finite
// service, the chosen first-read paths and SR2 observations are conclusions.
pub open spec fn references<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:Issuer,run:fair::Runnable) -> bool {
    (forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b)
        && model::read_a(m,first,res,reference(m,b,0),run) && mail::fair_opportunity(m,run,reference(m,b,5)))
        && (forall|l:Lanes| #[trigger] proper(l,who) ==> model::read_a(m,first,res,entry(m,l),run)
            && fair::pending_turns(m,res,entry(m,l),run))
}
pub proof fn two_executions_or_dependency<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:Issuer,answers:spec_fn(Packet<Wire>)->bool,run:fair::Runnable)
    requires dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),references(m,first,res,n,who,run),
    ensures weak_dependency(m,alpha(n)) || weak_dependency(m,beta(n)) || other_dependency(m,alpha(n)) || other_dependency(m,beta(n))
        || missing_route(m,alpha(n),who,answers) || missing_route(m,beta(n),who,answers)
        || exists|w:Completions<S>| #[trigger] completed(m,first,res,n,who,answers,w),
{
    let a=alpha(n);let b=beta(n);
    assert forall|f:Fork| f.notice==n implies #[trigger] dispatch::weak_open(m,f) && loss::reference_progress(m,f,run)
        && cause::member_sample(m,first,f) by {
        assert(dispatch::weak_open(m,f));model::availability_at_both_clients(m,res,reference(m,f,0),run);
        model::first_quorum_rule(m,first,res,f);
    }
    if !weak_dependency(m,a) && !weak_dependency(m,b) && !other_dependency(m,a) && !other_dependency(m,b) && !missing_route(m,a,who,answers) && !missing_route(m,b,who,answers) {
        assert(dispatch::weak_open(m,a) && dispatch::weak_open(m,b));assert(loss::reference_progress(m,a,run) && loss::reference_progress(m,b,run));
        let sa=choose_service(m,a,run);let sb=choose_service(m,b,run);
        let pa=choose_route(m,a,who,answers,sa);let pb=choose_route(m,b,who,answers,sb);
        finite_allocation(pa,pb,who);let l=allocation(who,pa,pb);assert(proper(l,who));
        let e=pair::auxiliary(m,l,n,s::record(pa,0),s::record(pb,0));let empty=|_q:Packet<Wire>|false;
        if wait::needs_class(read::service_step(m),read::returned(res),e,mail::receipt_of(empty)) {
            let p=choose|p:Service<S>| #[trigger] wait::first_return(read::service_step(m),read::returned(res),e,p);
            assert(!wait::uses(p,mail::receipt_of(empty)));
        }
        let w=common_completion(m,first,res,n,who,answers,run,pa,pb,empty);assert(completed(m,first,res,n,who,answers,w));
    }
}
// Legal sequential explanations for the values actually published at C1
// and C2 in this particular replay, with both RMW calls having returned 1.
pub open spec fn explains_returns<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    who:Issuer,b:Fork,w:Completions<S>) -> bool {
    let ta=s::record(w.alpha,0);let tb=s::record(w.beta,0);let l=allocation(who,w.alpha,w.beta);
    let before=fork_end(m,l,b,ta,tb).cfg;
    let after=loss::final_cfg(m,target(m,l,b,ta,tb),read::retained_actions(w.second,0));
    let second=res((after.private)(Process::SecondClient));
    second.is_some() && loss::has_order(first((before.private)(Process::FirstClient)),second.unwrap())
}
pub proof fn incompatible_original_histories<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:Issuer,answers:spec_fn(Packet<Wire>)->bool,w:Completions<S>)
    requires completed(m,first,res,n,who,answers,w),
    ensures !explains_returns(m,first,res,who,alpha(n),w) || !explains_returns(m,first,res,who,beta(n),w),
        ({let l=allocation(who,w.alpha,w.beta);!loss::history(m,res,first,l,alpha(n)) || !loss::history(m,res,first,l,beta(n))}),
{
    let a=alpha(n);let b=beta(n);let l=allocation(who,w.alpha,w.beta);
    let ta=s::record(w.alpha,0);let tb=s::record(w.beta,0);
    let v=w.value;let suffix=read::retained_actions(w.second,0);
    if loss::has_order(5,v) && loss::has_order(2,v) {
        let (ao,ax)=choose|o:Seq<crate::Op>,x:Seq<int>| #[trigger] crate::legal(o,x,5,v);
        let (bo,bx)=choose|o:Seq<crate::Op>,x:Seq<int>| #[trigger] crate::legal(o,x,2,v);
        crate::conditional_history_contradiction(ao,ax,bo,bx,v);
    }
    assert forall|f:Fork| f.notice==n implies {
        let ordered=loss::has_order(first_value(f),v);
        (#[trigger] explains_returns(m,first,res,who,f,w)==ordered) && (loss::history(m,res,first,l,f) ==> ordered)
    } by {
        assert(arm(m,first,res,l,f,ta,tb,w.second,v,answers));
        assert(loss::original_read(m,first,l,f,ta,tb,answers));
        assert(loss::responds(m,res,target(m,l,f,ta,tb),suffix,v));
        loss::response_value(m,res,target(m,l,f,ta,tb),suffix,v);
        assert(loss::history_witness(m,res,l,f,ta,tb,suffix,v));
    }
    assert(explains_returns(m,first,res,who,a,w)==loss::has_order(5,v));
    assert(explains_returns(m,first,res,who,b,w)==loss::has_order(2,v));
}
// History safety plus the user's no-await rule leaves the independent
// communication or quorum-installation obligation, on an actual reference.
pub proof fn remaining_dependency_under_h_and_t<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:Issuer,answers:spec_fn(Packet<Wire>)->bool,run:fair::Runnable)
    requires dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),references(m,first,res,n,who,run),
        forall|b:Fork| b.notice==n ==> #[trigger] wait::no_await(mail::active_step(m),mail::posted(m),first::reached_in(m,b),dep::promotion(b)),
        forall|l:Lanes,b:Fork| proper(l,who) && b.notice==n ==> #[trigger] loss::history(m,res,first,l,b),
    ensures other_dependency(m,alpha(n)) || other_dependency(m,beta(n)) || missing_route(m,alpha(n),who,answers) || missing_route(m,beta(n),who,answers),
{
    let a=alpha(n);let b=beta(n);two_executions_or_dependency(m,first,res,n,who,answers,run);
    assert forall|f:Fork| f.notice==n implies !#[trigger] weak_dependency(m,f) by {
        assert(dispatch::weak_open(m,f));dispatch::fanout_and_weak_open_launch(m,f);dispatch::launch_cut(m,f);
        assert(first::reached_in(m,f)(reference(m,f,5)));
        assert(wait::no_await(mail::active_step(m),mail::posted(m),first::reached_in(m,f),dep::promotion(f)));
    }
    if !other_dependency(m,a) && !other_dependency(m,b) && !missing_route(m,a,who,answers) && !missing_route(m,b,who,answers) {
        let w=choose|w:Completions<S>| #[trigger] completed(m,first,res,n,who,answers,w);
        let l=allocation(who,w.alpha,w.beta);assert(proper(l,who));
        incompatible_original_histories(m,first,res,n,who,answers,w);
        assert(loss::history(m,res,first,l,a) && loss::history(m,res,first,l,b));
    }
}

}
