// Obtain a new continuation from the *reached* masked reference. Attach
// its real history back to invocation before applying held-value sampling
// and the two-reporter contract, then replay just the continuation.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::coupled_sources as sources;
use crate::first_assembly::{self as asm,Lanes,Service};
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_schedule::{self as first,reference};
use crate::first_splice::{self as tape,Tape};
use crate::guarded_comparison::{self as cmp,prepare,end,fired};
use crate::hybrid_fork::{self as names,Issuer};
use crate::hybrid_majority as majority;
use crate::hybrid_transparency as trans;
use crate::independent_preparations as prep;
use crate::independent_read::{self as read,State};
use crate::mailbox_preparation as mb;
use crate::promotion_wait as wait;
use crate::quorum_projection::{self as proj,named};
use crate::quorum_schedules as qs;
use crate::read_call::{Program,Event};
use crate::read_nonblocking as nb;
use crate::sr1_contract as rpc;

verus! {

pub open spec fn returning<S>(m:Program<S>,z:State<S>,v:Service<S>) -> bool {
    wait::first_return(mail::active_step(m),mail::posted(m),z,v)
}
pub open spec fn masked_cut<S>(m:Program<S>,b:Fork,s:Seq<Event>) -> State<S> {
    end(m,prepare(),reference(m,b,5),s)
}

proof fn extend_reached<S>(m:Program<S>,base:State<S>,x:State<S>,t:Tape)
    requires read::reached(m,base,x),tape::plays(m,x,t),
    ensures read::reached(m,base,tape::after(m,x,t)),
    decreases t.len(),
{
    if t.len()>0 {
        let a=t[0].action;let y=read::next(m,x,a);let k=choose|k:nat| #[trigger] nb::within(read::prefix_step(m),read::at_state(x),base,k);
        assert(read::prefix_step(m)(x,a,y));crate::fair_read::append_reachable(m,base,x,a,y,k);
        assert(nb::within(read::prefix_step(m),read::at_state(y),base,k+1));extend_reached(m,base,y,t.drop_first());
    }
}

proof fn masked_prefix<S>(m:Program<S>,b:Fork,s:Seq<Event>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),
    ensures ({
        let x=reference(m,b,5);let t=fired(m,prepare(),x,s);let z=masked_cut(m,b,s);let h=cmp::path(m,x,t);
        read::reached(m,reference(m,b,0),z) && mail::submitted(z) && !mail::posted(m)(z)
            && pair::c1_protected(z) && !z.cfg.net.first_stopped && !mail::posted(m)(x)
            && h.states.len()==h.actions.len()+1 && h.states[0]==x && h.states.last()==z
            && wait::valid_edges(mail::active_step(m),h) && wait::pending_before(mail::posted(m),h)
            && tape::record(h,0)==t && mb::ordinary(m,x,t)
    }),
{
    let x=reference(m,b,5);let t=fired(m,prepare(),x,s);let z=masked_cut(m,b,s);let h=cmp::path(m,x,t);let C=Process::FirstClient;
    dispatch::fanout_and_weak_open_launch(m,b);dispatch::launch_cut(m,b);
    crate::sr1_majorities::local_at(m,b,C,5);assert(crate::sr1_majorities::count(b,5)==5);
    assert(!(m.done)((first::cfg(m,b,5).private)(C)));
    assert(!mail::posted(m)(x));
    mb::native_proposals(m,x,s);extend_reached(m,reference(m,b,0),x,t);
    cmp::firing_is_native(m,prepare(),x,s);cmp::physical_steps(m,prepare(),x,t);
    assert(tape::record(h,0) =~= t);
    assert forall|i:int| 0<=i<t.len() implies mail::active_step(m)(h.states[i],#[trigger] h.actions[i],h.states[i+1]) by {
        assert(read::service_step(m)(h.states[i],h.actions[i],h.states[i+1]));assert(prep::ordinary_input(t[i]));
    }
    assert forall|i:int| 0<=i<h.actions.len() implies !mail::posted(m)(#[trigger] h.states[i]) by {
        let u=t.take(i);assert(u+t.skip(i) =~= t);tape::concat(m,x,u,t.skip(i));
        assert forall|j:int| 0<=j<u.len() implies prep::ordinary_input(#[trigger] u[j]) by {assert(u[j]==t[j]);}
        mb::ordinary_keeps_caller(m,x,u);
    }
    mb::ordinary_keeps_caller(m,x,t);tape::frame(m,x,t,ISet::full(),ISet::full());
    assert(pair::c1_protected(x));pair::keep_protection(m,x,t);
    let r=crate::origin(b.branch);let q=Replica::R3;
    assert(r!=q && live(z.cfg.net,at(r)) && live(z.cfg.net,at(q)) && z.first_requested.contains(r) && z.first_requested.contains(q));
    assert(mail::submitted(z));
}

spec fn append_service<S>(h:Service<S>,v:Service<S>) -> Service<S> {
    wait::Path{states:h.states.take(h.actions.len() as int)+v.states,actions:h.actions+v.actions}
}
proof fn reattach<S>(m:Program<S>,b:Fork,h:Service<S>,v:Service<S>)
    requires h.states.len()==h.actions.len()+1,h.states[0]==reference(m,b,5),!mail::posted(m)(h.states[0]),
        wait::valid_edges(mail::active_step(m),h),wait::pending_before(mail::posted(m),h),returning(m,h.states.last(),v),
    ensures cause::returning(m,b,append_service(h,v)),tape::record(append_service(h,v),0)==tape::record(h,0)+tape::record(v,0),
        append_service(h,v).states.last()==v.states.last(),
{
    let p=append_service(h,v);let k=h.actions.len();
    assert forall|i:int| 0<=i<p.actions.len() implies mail::active_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        && !mail::posted(m)(p.states[i]) by {
        if i<k {assert(p.states[i+1]==h.states[i+1]);assert(mail::active_step(m)(h.states[i],h.actions[i],h.states[i+1]));}
        else {assert(mail::active_step(m)(v.states[i-k],v.actions[i-k],v.states[i-k+1]));}
    }
    assert forall|i:int| 0<=i<p.actions.len() implies !mail::posted(m)(#[trigger] p.states[i]) by {
        assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));
    }
    assert(tape::record(p,0) =~= tape::record(h,0)+tape::record(v,0));
}

// A's sample belongs to the full invocation interval. The prefix and the
// suffix are separately known to leave the quorum's cells undisturbed.
proof fn reference_value_and_reporters<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,
    who:Issuer,used:rpc::Ledger<S>,region:nb::Region<State<S>>,h:Service<S>,v:Service<S>)
    requires cause::returning(m,b,append_service(h,v)),append_service(h,v).states.last()==v.states.last(),
        tape::record(append_service(h,v),0)==tape::record(h,0)+tape::record(v,0),
        forall|i:int| 0<=i<h.actions.len() ==> prep::ordinary_input(#[trigger] tape::record(h,0)[i]),
        prep::ordinary_source(v),cause::member_sample(m,first,b),rpc::registered(m,b,region,who,used),
    ensures mb::selected_service(first,b,v),forall|i:int| 0<=i<v.actions.len() ==> named(who,#[trigger] v.actions[i]),
{
    let p=append_service(h,v);let t=tape::record(h,0);let u=tape::record(v,0);let full=tape::record(p,0);let c=Process::FirstClient;
    assert forall|i:int| 0<=i<full.len() implies (#[trigger] full[i]).actor==c || prep::ordinary_input(full[i]) by {
        if i<t.len() {assert(full[i]==t[i] && prep::ordinary_input(t[i]));} else {assert(full[i]==u[i-t.len()]);}
    }
    prep::source_cells(m,b,p);cause::forced_sample(m,first,p,b);
    rpc::solicited_majority_route(m,b,p,region);rpc::allocator_gives_native(m,b,p,region,who,used);
    build::exchange_heard(full,crate::origin(b.branch));build::exchange_heard(full,Replica::R3);
    cause::pick_concat(t,u,c,true);
    let part=tape::pick(t,c,true);
    if part.len()>0 {tape::picked(t,c,true,0);let j=choose|j:int|0<=j<t.len() && t[j]==part[0];assert(prep::ordinary_input(t[j]));}
    assert(calls::caller(p) =~= calls::caller(v));
    assert forall|i:int| 0<=i<v.actions.len() implies named(who,#[trigger] v.actions[i]) by {assert(p.actions[h.actions.len()+i]==v.actions[i]);}
    assert forall|i:int| 0<=i<u.len() implies {let e=#[trigger] u[i];
        if e.actor==c {e.incoming.is_none() || e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3)}
        else {prep::ordinary_input(e)}} by {
        let j=h.actions.len()+i;let e=u[i];assert(full[j]==e);
        if e.actor==c && e.incoming.is_some() {
            let q=e.incoming.unwrap();let a=p.actions[j];let w=p.states[j];
            assert(mail::active_step(m)(w,a,p.states[j+1]));assert(a is Deliver && q.to==c);
            let id=a->Deliver_0;assert(w.cfg.net.pending.get(id)==Some(q) && p.states[0].cfg.net.pending.get(id)!=Some(q));
            let k=mail::last_send(m,p,j as nat,id,q);cause::prefix_mask(m,p,k);
            assert(mail::active_step(m)(p.states[k as int],p.actions[k as int],p.states[k as int+1]));assert(live(p.states[k as int].cfg.net,q.from));
        }
    }
}

pub open spec fn grouped<S>(v:Service<S>) -> Tape {sources::replicas(v)+calls::caller(v)}

pub open spec fn blocked_service<S>(m:Program<S>,x:State<S>,y:State<S>,v:Service<S>,changed:Set<Process>) -> bool {
    let u=grouped(v);
    exists|k:int| #[trigger] proj::suffix_refusal(m,x,y,u,k) && k<sources::replicas(v).len() && changed.contains(u[k].actor)
}

proof fn resume_selected_service<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,who:Issuer,
    x:State<S>,y:State<S>,v:Service<S>,changed:Set<Process>)
    requires proj::compared(b,who,x,y,changed),forall|p:Process| #[trigger] changed.contains(p) ==> p is At,
        pair::c1_protected(x),returning(m,x,v),mb::selected_service(first,b,v),
        forall|i:int| 0<=i<v.actions.len() ==> named(who,#[trigger] v.actions[i]),
    ensures qs::viable(m,first,b,y) || blocked_service(m,x,y,v,changed),
{
    mb::normalize_selected_return(m,first,b,x,v);let t=sources::replicas(v);let c=calls::caller(v);let full=tape::record(v,0);
    let r=tape::after(m,x,t);let z=tape::after(m,y,t);let u=t+c;let caller=Process::FirstClient;
    assert forall|i:int|0<=i<u.len() implies named(who,(#[trigger] u[i]).action) by {
        let e=u[i];if i<t.len() {tape::picked(full,caller,false,i);} else {tape::picked(full,caller,true,i-t.len());}
        let j=choose|j:int| 0<=j<full.len() && full[j]==e;assert(v.actions[j]==e.action && named(who,v.actions[j]));
    }
    tape::concat(m,x,t,c);proj::replay_or_refusal(m,b,who,x,y,u,changed);
    if tape::plays(m,y,u) {
        tape::concat(m,y,t,c);
        mb::ordinary_keeps_caller(m,x,t);mb::ordinary_keeps_caller(m,y,t);
        assert(!changed.contains(caller));prep::initial_mailbox(m,z,c);calls::play_client(m,r,z,c);assert(mb::mailbox(m,first,b,z,c));
        assert(qs::complete(m,first,b,y,t,c));
    } else {
        let k=choose|k:int| #[trigger] proj::suffix_refusal(m,x,y,u,k) && changed.contains(u[k].actor);
        if k>=t.len() {assert(u[k]==c[k-t.len()] && c[k-t.len()].actor==caller);}
        assert(blocked_service(m,x,y,v,changed));
    }
}

pub open spec fn outside_at<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit,z:State<S>,v:Service<S>) -> bool {
    returning(m,z,v) && !wait::uses(v,trans::weak_work(b,audit))
        && (forall|w:Service<S>| #[trigger] returning(m,z,w) ==> !prep::ordinary_source(w))
        && exists|i:int| 0<=i<v.actions.len() && {let e=#[trigger] tape::record(v,0)[i];e.actor!=Process::FirstClient && !prep::ordinary_input(e)}
}

pub open spec fn ordinary_return<S>(m:Program<S>,z:State<S>,v:Service<S>) -> bool {
    returning(m,z,v) && prep::ordinary_source(v)
}

pub open spec fn all_blocked<S>(m:Program<S>,x:State<S>,y:State<S>,changed:Set<Process>) -> bool {
    (exists|v:Service<S>| #[trigger] ordinary_return(m,x,v))
        && forall|v:Service<S>| #[trigger] ordinary_return(m,x,v) ==> blocked_service(m,x,y,v,changed)
}

// Reapply A at a reached sole-quorum cut. If an ordinary continuation
// exists, *each* such continuation has the required sample and reporters.
proof fn available_masked_suffix<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    b:Fork,who:Issuer,used:rpc::Ledger<S>,region:nb::Region<State<S>>,run:crate::fair_read::Runnable,audit:trans::PacketAudit,
    s:Seq<Event>,y:State<S>,changed:Set<Process>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),majority::read_a(m,first,res,reference(m,b,0),run),
        rpc::registered(m,b,region,who,used),trans::no_first_wait(m,b,audit),
        !(exists|v:Service<S>| #[trigger] ordinary_return(m,masked_cut(m,b,s),v)) ==> mail::fair_opportunity(m,run,masked_cut(m,b,s)),
        proj::compared(b,who,masked_cut(m,b,s),y,changed),forall|p:Process| #[trigger] changed.contains(p) ==> p is At,
    ensures qs::viable(m,first,b,y) || all_blocked(m,masked_cut(m,b,s),y,changed)
        || exists|v:Service<S>| #[trigger] outside_at(m,b,audit,masked_cut(m,b,s),v),
{
    let ref0=reference(m,b,0);let x=reference(m,b,5);let t=fired(m,prepare(),x,s);let h=cmp::path(m,x,t);
    let z=masked_cut(m,b,s);let st=mail::active_step(m);let d=mail::posted(m);
    masked_prefix(m,b,s);
    if exists|v:Service<S>| #[trigger] ordinary_return(m,z,v) {
        assert forall|v:Service<S>| #[trigger] ordinary_return(m,z,v) implies qs::viable(m,first,b,y) || blocked_service(m,z,y,v,changed) by {
            reattach(m,b,h,v);majority::first_quorum_rule(m,first,res,b);
            reference_value_and_reporters(m,first,b,who,used,region,h,v);
            resume_selected_service(m,first,b,who,z,y,v,changed);
        }
    } else {
        majority::availability_at_both_clients(m,res,ref0,run);mail::fair_first_service(m,run,|w|read::reached(m,ref0,w),z);
        nb::first_response_iff(st,d,z);assert(wait::can_finish(st,d,z));let effect=trans::weak_work(b,audit);
        assert(first::reached_in(m,b)(z));assert(!wait::needs_class(st,d,z,effect));let v=choose|v:Service<S>| #[trigger] wait::first_return(st,d,z,v) && !wait::uses(v,effect);
        assert forall|w:Service<S>| #[trigger] returning(m,z,w) implies !prep::ordinary_source(w) by {assert(!ordinary_return(m,z,w));}
        assert(returning(m,z,v));assert(!prep::ordinary_source(v));assert(outside_at(m,b,audit,z,v));
    }
}

proof fn projected_inputs(b:Fork,who:Issuer,t:Tape)
    requires forall|i:int| 0<=i<t.len() ==> prep::ordinary_input(#[trigger] t[i]),
    ensures forall|i:int| 0<=i<proj::projection(b,who,t).len() ==> prep::ordinary_input(#[trigger] proj::projection(b,who,t)[i]),
    decreases t.len(),
{
    if t.len()>0 {
        let h=t.drop_first();assert forall|i:int| 0<=i<h.len() implies prep::ordinary_input(#[trigger] h[i]) by {assert(h[i]==t[i+1]);}
        projected_inputs(b,who,h);let u=proj::projection(b,who,t);let v=proj::projection(b,who,h);
        assert forall|i:int| 0<=i<u.len() implies prep::ordinary_input(#[trigger] u[i]) by {
            if proj::kept(b,who,t[0]) {if i>0 {assert(u[i]==v[i-1]);} else {assert(u[i]==t[0]);}}
        }
    }
}

pub open spec fn prefix_block<S>(m:Program<S>,l:Lanes,b:Fork,who:Issuer,t:Tape) -> bool {
    let x=reference(m,b,5);let y=build::root(m,l,b);
    exists|i:int| #[trigger] proj::prefix_refusal(m,b,who,x,y,t,i) && proj::affected(m,b,who,y,t.take(i)).contains(t[i].actor)
}

pub open spec fn projected_cut<S>(m:Program<S>,b:Fork,who:Issuer,t:Tape) -> State<S> {
    tape::after(m,reference(m,b,5),proj::projection(b,who,t))
}

pub open spec fn obstruction<S>(m:Program<S>,l:Lanes,b:Fork,who:Issuer,audit:trans::PacketAudit,t:Tape) -> bool {
    let x=reference(m,b,5);let y=build::root(m,l,b);let u=proj::projection(b,who,t);let z=projected_cut(m,b,who,t);
    prefix_block(m,l,b,who,t) || (tape::plays(m,x,u) &&
        (all_blocked(m,z,tape::after(m,y,t),proj::affected(m,b,who,y,t)) || exists|v:Service<S>| #[trigger] outside_at(m,b,audit,z,v)))
}

// An arbitrary actual target preparation, including the part of another
// majority's proposal list that really fired. No relation between the
// reached private memories or queues is assumed.
pub proof fn resume_reference_or_obstruction<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,
    b:Fork,who:Issuer,used:rpc::Ledger<S>,region:nb::Region<State<S>>,run:crate::fair_read::Runnable,audit:trans::PacketAudit,t:Tape)
    requires names::proper(l,who),mb::ordinary(m,build::root(m,l,b),t),proj::fresh_script(who,Set::empty(),asm::actions(t)),
        dispatch::initiates(m),dispatch::weak_open(m,b),majority::read_a(m,first,res,reference(m,b,0),run),
        rpc::registered(m,b,region,who,used),trans::no_first_wait(m,b,audit),
        tape::plays(m,reference(m,b,5),proj::projection(b,who,t))
            && !(exists|v:Service<S>| #[trigger] ordinary_return(m,projected_cut(m,b,who,t),v))
            ==> mail::fair_opportunity(m,run,projected_cut(m,b,who,t)),
    ensures qs::viable(m,first,b,tape::after(m,build::root(m,l,b),t)) || obstruction(m,l,b,who,audit,t),
{
    let x=reference(m,b,5);let y=build::root(m,l,b);let u=proj::projection(b,who,t);let z=projected_cut(m,b,who,t);
    proj::project_actual_preparation(m,l,b,who,t);
    if !prefix_block(m,l,b,who,t) {
        projected_inputs(b,who,t);mb::propose_native(m,x,u);let s=asm::actions(u);
        assert(z==masked_cut(m,b,s));let c=proj::affected(m,b,who,y,t);
        assert forall|p:Process| #[trigger] c.contains(p) implies p is At by {};
        available_masked_suffix(m,first,res,b,who,used,region,run,audit,s,tape::after(m,y,t),c);
    }
}

}
