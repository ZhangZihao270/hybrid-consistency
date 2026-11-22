// A sufficient local service condition, separate from T. Extra independently
// audited replication/order packets may remain issued throughout both reads.
use vstd::prelude::*;
use crate::{checkpoint::*,delivery::*};
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
use crate::hybrid_fork as fork;
use crate::hybrid_majority as model;
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Program,Event};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;

verus! {

pub type PacketAudit = spec_fn(Packet<Wire>)->bool;
pub open spec fn weak_work<S>(b:Fork,audit:PacketAudit) -> wait::Relation<State<S>,Event> {
    |x:State<S>,a,y| dep::promotion(b)(x,a,y) || mail::receipt_of(audit)(x,a,y)
}
pub open spec fn without_weak<S>(m:Program<S>,b:Fork,audit:PacketAudit) -> wait::Relation<State<S>,Event> {
    nb::ordinary(mail::active_step(m),weak_work(b,audit))
}
pub open spec fn local_service<S>(m:Program<S>,b:Fork,audit:PacketAudit) -> bool {
    nb::no_unlock(without_weak(m,b,audit),mail::posted(m),dep::boundary(b),first::reached_in(m,b))
}
pub open spec fn no_first_wait<S>(m:Program<S>,b:Fork,audit:PacketAudit) -> bool {
    wait::no_await(mail::active_step(m),mail::posted(m),first::reached_in(m,b),weak_work(b,audit))
}
// The source condition can be checked without comparing executions. It
// concerns the availability of an ordinary next service, with no constraint
// on which value or metadata that service would publish.
proof fn first_without<S>(m:Program<S>,b:Fork,run:fair::Runnable,audit:PacketAudit) -> (p:Service<S>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),loss::reference_progress(m,b,run),
        no_first_wait(m,b,audit),local_service(m,b,audit),
    ensures fork::clean(m,b,p),!wait::uses(p,mail::receipt_of(audit)),
{
    let x=reference(m,b,5);let base=reference(m,b,0);let st=mail::active_step(m);let d=mail::posted(m);let scope=first::reached_in(m,b);
    dispatch::fanout_and_weak_open_launch(m,b);dispatch::launch_cut(m,b);loss::finite_service(m,b,run);
    let w=choose|w:Service<S>| #[trigger] cause::returning(m,b,w);let e=weak_work(b,audit);let free=without_weak(m,b,audit);
    let u=wait::extract_without_promotion(st,d,scope,e,x,w);
    assert forall|i:int| 0<=i<u.actions.len() implies free(u.states[i],#[trigger] u.actions[i],u.states[i+1]) by {
        assert(st(u.states[i],u.actions[i],u.states[i+1]));}
    nb::from_path(free,d,u,0);
    assert forall|v:State<S>,a:Event,z:State<S>| scope(v) && !d(v) && #[trigger] free(v,a,z) && !d(z) implies scope(z) by {
        assert(read::prefix_step(m)(v,a,z));let k=choose|k:nat| #[trigger] nb::within(read::prefix_step(m),read::at_state(v),base,k);
        fair::append_reachable(m,base,v,a,z,k);assert(nb::within(read::prefix_step(m),read::at_state(z),base,k+1));
    }
    nb::ordinary_option_at(free,d,dep::boundary(b),scope,x);let plain=nb::ordinary(free,dep::boundary(b));
    let p=nb::to_path(plain,d,x,choose|k:nat| #[trigger] nb::within(plain,d,x,k));
    assert forall|i:int| 0<=i<p.actions.len() implies st(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        && !dep::promotion(b)(p.states[i],p.actions[i],p.states[i+1]) && !mail::receipt_of(audit)(p.states[i],p.actions[i],p.states[i+1])
        && !dep::boundary(b)(p.states[i],p.actions[i],p.states[i+1])
        by {assert(plain(p.states[i],p.actions[i],p.states[i+1]));}
    p
}
pub open spec fn withheld(t:s::Tape,audit:PacketAudit) -> bool {
    forall|i:int| 0<=i<t.len() && (#[trigger] t[i]).incoming.is_some() ==> !audit(t[i].incoming.unwrap())
}
proof fn source_receipts<S>(m:Program<S>,p:Service<S>,b:Fork,audit:PacketAudit)
    requires cause::returning(m,b,p),!wait::uses(p,mail::receipt_of(audit)),
    ensures withheld(s::record(p,0),audit),
{
    let t=s::record(p,0);assert forall|i:int| 0<=i<t.len() && (#[trigger] t[i]).incoming.is_some() implies !audit(t[i].incoming.unwrap()) by {
        assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));assert(!mail::receipt_of(audit)(p.states[i],p.actions[i],p.states[i+1]));
    }
}
proof fn picked_receipts(t:s::Tape,p:Process,keep:bool,audit:PacketAudit)
    requires withheld(t,audit),
    ensures withheld(s::pick(t,p,keep),audit),
{
    let u=s::pick(t,p,keep);assert forall|i:int| 0<=i<u.len() && (#[trigger] u[i]).incoming.is_some() implies !audit(u[i].incoming.unwrap()) by {
        s::picked(t,p,keep,i);let j=choose|j:int| 0<=j<t.len() && t[j]==u[i];assert(!audit(t[j].incoming.unwrap()));
    }
}
proof fn joint_receipts(t:s::Tape,u:s::Tape,audit:PacketAudit)
    requires withheld(t,audit),withheld(u,audit),
    ensures withheld(t+u,audit),
{
    let all=t+u;assert forall|i:int| 0<=i<all.len() && (#[trigger] all[i]).incoming.is_some() implies !audit(all[i].incoming.unwrap()) by {
        if i<t.len() {assert(all[i]==t[i]);} else {assert(all[i]==u[i-t.len()]);}
    }
}
proof fn replayed_receipts<S>(m:Program<S>,p:Service<S>,j:nat,audit:PacketAudit)
    requires p.states.len()==p.actions.len()+1,j<=p.actions.len(),wait::valid_edges(read::service_step(m),p),!wait::uses(p,mail::receipt_of(audit)),
    ensures withheld(loss::service_inputs(p,j),audit),
    decreases p.actions.len()-j,
{
    if j<p.actions.len() {
        let x=p.states[j as int];let a=p.actions[j as int];let e=process_step(x.cfg.net,a);assert(read::service_step(m)(x,a,p.states[j as int+1]));
        assert(!mail::receipt_of(audit)(x,a,p.states[j as int+1]));replayed_receipts(m,p,j+1,audit);
        if e.actor!=Process::FirstClient {assert(withheld(seq![e],audit));joint_receipts(seq![e],loss::service_inputs(p,j+1),audit);}
    }
}
pub open spec fn original_holds<S>(m:Program<S>,b:Fork,who:fork::Issuer,w:fork::Completions<S>,audit:PacketAudit) -> bool {
    let ta=s::record(w.alpha,0);let tb=s::record(w.beta,0);let l=fork::allocation(who,w.alpha,w.beta);let t=fork::target(m,l,b,ta,tb);
    withheld(cause::tape(b,ta,tb),audit) && withheld(loss::observed_suffix(m,t,read::retained_actions(w.second,0)),audit)
}
// Shared replay for two already selected, genuine majority services. Public
// entry points obtain these services from A and their source-side rules.
pub(crate) proof fn finish_sources<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:fork::Issuer,answers:PacketAudit,audit:PacketAudit,run:fair::Runnable,pa:Service<S>,pb:Service<S>) -> (w:fork::Completions<S>)
    requires dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),fork::references(m,first,res,n,who,run),
        fork::clean(m,alpha(n),pa), fork::clean(m,beta(n),pb),
        fork::wire_route(alpha(n),pa,who,answers),fork::wire_route(beta(n),pb,who,answers),
        !wait::uses(pa,mail::receipt_of(audit)),!wait::uses(pb,mail::receipt_of(audit)),
        forall|l:Lanes| #[trigger] fork::proper(l,who) ==> wait::no_await(read::service_step(m),read::returned(res),
            |x:State<S>|read::reached(m,entry(m,l),x) && read::issued_to_majority(x),mail::receipt_of(audit)),
    ensures fork::completed(m,first,res,n,who,answers,w),
        original_holds(m,alpha(n),who,w,audit),original_holds(m,beta(n),who,w,audit),
        !fork::explains_returns(m,first,res,who,alpha(n),w) || !fork::explains_returns(m,first,res,who,beta(n),w),
        ({let l=fork::allocation(who,w.alpha,w.beta);!loss::history(m,res,first,l,alpha(n)) || !loss::history(m,res,first,l,beta(n))}),
{
    let a=alpha(n);let b=beta(n);let ta=s::record(pa,0);let tb=s::record(pb,0);
    assert forall|f:Fork| f.notice==n implies #[trigger] dispatch::weak_open(m,f) && cause::member_sample(m,first,f) by {
        assert(dispatch::weak_open(m,f));model::first_quorum_rule(m,first,res,f);
    }
    assert(fork::wire_route(a,pa,who,answers) && fork::wire_route(b,pb,who,answers));
    fork::finite_allocation(pa,pb,who);let l=fork::allocation(who,pa,pb);assert(fork::proper(l,who));
    dep::no_boundary_gives_routing(m,a,l,pa);dep::no_boundary_gives_routing(m,b,l,pb);
    loss::selected_reads(m,res,first,l,a,pa,pb,answers);
    let e=pair::auxiliary(m,l,n,ta,tb);let region=|x:State<S>|read::reached(m,entry(m,l),x) && read::issued_to_majority(x);
    assert(region(e));assert(wait::no_await(read::service_step(m),read::returned(res),region,mail::receipt_of(audit)));
    let w=fork::common_completion(m,first,res,n,who,answers,run,pa,pb,audit);
    fork::incompatible_original_histories(m,first,res,n,who,answers,w);
    source_receipts(m,pa,a,audit);source_receipts(m,pb,b,audit);replayed_receipts(m,w.second,0,audit);
    picked_receipts(tb,at(crate::Replica::R1),true,audit);picked_receipts(ta,at(crate::Replica::R2),true,audit);
    joint_receipts(working(tb,b),working(ta,a),audit);
    assert forall|f:Fork| f.notice==n implies #[trigger] original_holds(m,f,who,w,audit) by {
        let t=if f.branch==crate::Branch::Alpha {assert(f==a);ta} else {assert(f==b);tb};
        picked_receipts(t,at(crate::origin(f.branch)),false,audit);joint_receipts(work_pair(ta,tb,n),remaining(t,f),audit);
        assert(fork::arm(m,first,res,l,f,ta,tb,w.second,w.value,answers));
    }
    w
}

// Conditional contradiction without assuming H. Applying H to this pair
// requires two incompatible sequential histories for the common return.
// This entry point takes the complete wire-route contract as a premise.
pub proof fn two_reads_with_delayed_weak_work<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:fork::Issuer,answers:PacketAudit,audit:PacketAudit,run:fair::Runnable) -> (w:fork::Completions<S>)
    requires dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),fork::references(m,first,res,n,who,run),
        forall|b:Fork| b.notice==n ==> #[trigger] no_first_wait(m,b,audit) && local_service(m,b,audit),
        forall|b:Fork,p:Service<S>| b.notice==n && #[trigger] fork::clean(m,b,p) && !wait::uses(p,mail::receipt_of(audit))
            ==> fork::wire_route(b,p,who,answers),
        forall|l:Lanes| #[trigger] fork::proper(l,who) ==> wait::no_await(read::service_step(m),read::returned(res),
            |x:State<S>|read::reached(m,entry(m,l),x) && read::issued_to_majority(x),mail::receipt_of(audit)),
    ensures fork::completed(m,first,res,n,who,answers,w),
        original_holds(m,alpha(n),who,w,audit),original_holds(m,beta(n),who,w,audit),
        !fork::explains_returns(m,first,res,who,alpha(n),w) || !fork::explains_returns(m,first,res,who,beta(n),w),
        ({let l=fork::allocation(who,w.alpha,w.beta);!loss::history(m,res,first,l,alpha(n)) || !loss::history(m,res,first,l,beta(n))}),
{
    let a=alpha(n);let b=beta(n);
    assert forall|f:Fork| f.notice==n implies #[trigger] dispatch::weak_open(m,f) && cause::member_sample(m,first,f) && loss::reference_progress(m,f,run)
        && no_first_wait(m,f,audit) && local_service(m,f,audit) by {
        assert(dispatch::weak_open(m,f));assert(no_first_wait(m,f,audit));
        model::availability_at_both_clients(m,res,reference(m,f,0),run);model::first_quorum_rule(m,first,res,f);
    }
    assert(dispatch::weak_open(m,a) && dispatch::weak_open(m,b));
    let pa=first_without(m,a,run,audit);let pb=first_without(m,b,run,audit);
    finish_sources(m,first,res,n,who,answers,audit,run,pa,pb)
}

}
