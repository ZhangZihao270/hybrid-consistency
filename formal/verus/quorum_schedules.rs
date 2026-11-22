// Reach the selected private mailboxes, with completely independent SR1
// continuations. A scheduler obstruction has to destroy a whole region
// of returning states; disagreeing fronts of two selected tapes do not.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::first_assembly::{self as asm,Lanes};
use crate::first_splice::{self as tape,Tape,Observation};
use crate::fork_alternatives as fork;
use crate::fork_information as info;
use crate::guarded_comparison::{self as cmp, prepare, fired, end, ready};
use crate::independent_read::{self as read, State};
use crate::mailbox_preparation::{self as mb,ordinary,mailbox};
use crate::read_call::{Event,Program};
use crate::{fair_read as fair, hybrid_majority as majority, first_mailbox as mail, promotion_wait as wait};
use crate::schedule_observations as obs;

verus! {

pub open spec fn complete<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,t:Tape,c:Tape) -> bool {
    ordinary(m,x,t) && mailbox(m,first,b,tape::after(m,x,t),c)
}
pub open spec fn viable<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>) -> bool {
    exists|t:Tape,c:Tape| #[trigger] complete(m,first,b,x,t,c)
}
pub open spec fn collected<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,s:Seq<Event>,c:Tape) -> bool {
    mailbox(m,first,b,end(m,prepare(),x,s),c)
}
pub open spec fn joint<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,d:Fork,x:State<S>,y:State<S>,s:Seq<Event>) -> bool {
    (exists|c:Tape| #[trigger] collected(m,first,b,x,s,c)) && (exists|c:Tape| #[trigger] collected(m,first,d,y,s,c))
}
pub open spec fn can_join<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,d:Fork,x:State<S>,y:State<S>) -> bool {
    exists|s:Seq<Event>| #[trigger] joint(m,first,b,d,x,y,s)
}

// The target may resume on an entirely different native schedule.
// Alpha can wait privately after its replies are queued. Extra accepted
// ordinary sends or deliveries on alpha are included in the final prefix.
pub proof fn finish_other_quorum<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,d:Fork,x:State<S>,y:State<S>,s:Seq<Event>,c:Tape)
    -> (u:Seq<Event>)
    requires collected(m,first,b,x,s,c),viable(m,first,d,end(m,prepare(),y,s)),
    ensures collected(m,first,b,x,s+u,c),joint(m,first,b,d,x,y,s+u),
{
    let g=prepare();let z=end(m,g,y,s);let (t,k)=choose|t:Tape,k:Tape| #[trigger] complete(m,first,d,z,t,k);
    let u=asm::actions(t);mb::propose_native(m,z,t);mb::mailbox_survives(m,first,b,end(m,g,x,s),c,u);
    cmp::append_script(m,g,x,s,u);cmp::append_script(m,g,y,s,u);assert(collected(m,first,b,x,s+u,c));assert(collected(m,first,d,y,s+u,k));u
}

// No equality or ordering of the two native tapes occurs on the RHS.
pub proof fn joint_iff_one_quorum_still_viable<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,d:Fork,x:State<S>,y:State<S>)
    ensures can_join(m,first,b,d,x,y)==(exists|s:Seq<Event>,c:Tape|
        #[trigger] collected(m,first,b,x,s,c) && viable(m,first,d,end(m,prepare(),y,s))),
{
    if can_join(m,first,b,d,x,y) {
        let s=choose|s:Seq<Event>| #[trigger] joint(m,first,b,d,x,y,s);
        let c=choose|c:Tape| #[trigger] collected(m,first,b,x,s,c);
        let k=choose|k:Tape| #[trigger] collected(m,first,d,y,s,k);
        assert(complete(m,first,d,end(m,prepare(),y,s),Seq::empty(),k));
    } else if exists|s:Seq<Event>,c:Tape| #[trigger] collected(m,first,b,x,s,c) && viable(m,first,d,end(m,prepare(),y,s)) {
        let (s,c)=choose|s:Seq<Event>,c:Tape| #[trigger] collected(m,first,b,x,s,c) && viable(m,first,d,end(m,prepare(),y,s));
        let u=finish_other_quorum(m,first,b,d,x,y,s,c);assert(joint(m,first,b,d,x,y,s+u));
    }
}

pub proof fn native_pair_iff_joint<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice)
    requires mb::setup(m,res,l,alpha(n)),mb::setup(m,res,l,beta(n)),
    ensures can_join(m,first,alpha(n),beta(n),build::root(m,l,alpha(n)),build::root(m,l,beta(n)))
        ==(exists|a:fork::Tapes,b:fork::Tapes,s:Seq<Event>| #[trigger] fork::aligned(m,l,n,a,b,s) && fork::candidate(m,first,res,l,n,a,b)),
{
    let left=alpha(n);let right=beta(n);let x=build::root(m,l,left);let y=build::root(m,l,right);let g=prepare();
    if can_join(m,first,left,right,x,y) {
        let s=choose|s:Seq<Event>| #[trigger] joint(m,first,left,right,x,y,s);
        let c=choose|c:Tape| #[trigger] collected(m,first,left,x,s,c);let k=choose|c:Tape| #[trigger] collected(m,first,right,y,s,c);
        let a=fork::Tapes{replicas:fired(m,g,x,s),caller:c};let b=fork::Tapes{replicas:fired(m,g,y,s),caller:k};
        mb::native_proposals(m,x,s);mb::native_proposals(m,y,s);
        mb::release(m,first,res,l,left,a.replicas,c);mb::release(m,first,res,l,right,b.replicas,k);
        assert(fork::aligned(m,l,n,a,b,s));
    } else if exists|a:fork::Tapes,b:fork::Tapes,s:Seq<Event>| #[trigger] fork::aligned(m,l,n,a,b,s) && fork::candidate(m,first,res,l,n,a,b) {
        let (a,b,s)=choose|a:fork::Tapes,b:fork::Tapes,s:Seq<Event>| #[trigger] fork::aligned(m,l,n,a,b,s) && fork::candidate(m,first,res,l,n,a,b);
        mb::arm_has_mailbox(m,first,res,l,left,a);mb::arm_has_mailbox(m,first,res,l,right,b);
        assert(collected(m,first,left,x,s,a.caller) && collected(m,first,right,y,s,b.caller));
        assert(joint(m,first,left,right,x,y,s));
    }
}

pub open spec fn missing(c:Tape,i:int,x:Map<nat,Packet<Wire>>) -> bool {
    0<=i<c.len() && c[i].action is Deliver && x.get(c[i].action->Deliver_0)!=c[i].incoming
}

// Starting at the losing cut, try ANY sequence of ordinary replica actions,
// with any message bodies and ordering. Each previously working C1 tape
// then lacks a specific actual input. The missing input can depend on both
// continuations; no particular packet is declared mandatory.
pub proof fn lost_input<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,a:Event,t:Tape,c:Tape,u:Tape) -> (i:int)
    requires ready(m,prepare(),x,a),complete(m,first,b,x,t,c),
        !viable(m,first,b,read::next(m,x,a)),ordinary(m,read::next(m,x,a),u),
    ensures missing(c,i,tape::after(m,read::next(m,x,a),u).cfg.net.pending),
{
    let z=tape::after(m,x,t);let y=read::next(m,x,a);let v=tape::after(m,y,u);
    mb::ordinary_keeps_caller(m,x,t);mb::ordinary_keeps_caller(m,y,u);
    if !exists|i:int| #[trigger] missing(c,i,v.cfg.net.pending) {
        assert forall|i:int| 0<=i<c.len() && (#[trigger] c[i]).action is Deliver implies
            v.cfg.net.pending.get(c[i].action->Deliver_0)==c[i].incoming by {assert(!missing(c,i,v.cfg.net.pending));}
        calls::play_client(m,z,v,c);assert(mailbox(m,first,b,v,c));assert(complete(m,first,b,y,u,c));
    }
    choose|i:int| #[trigger] missing(c,i,v.cfg.net.pending)
}

// Independence uses both local actor and queue slot. Guard acceptance is
// proved after the crossing. A replica send can collide with a later
// delivery even when its controllers are on different machines.
proof fn commute_enabled<S>(m:Program<S>,x:State<S>,a:Event,h:Observation)
    requires ready(m,prepare(),x,a),ready(m,prepare(),x,h.action),h==process_step(x.cfg.net,h.action),
        tape::independent(process_step(x.cfg.net,a),h),
    ensures ({
        let g=prepare();let y=read::next(m,x,a);let v=read::next(m,x,h.action);let e=process_step(x.cfg.net,a);
        ready(m,g,y,h.action) && process_step(y.cfg.net,h.action)==h && ready(m,g,v,a)
            && process_step(v.cfg.net,a)==e && read::next(m,y,h.action)==read::next(m,v,a)
    }),
{
    let e=process_step(x.cfg.net,a);let y=read::next(m,x,a);let v=read::next(m,x,h.action);
    if let Some(id)=tape::slot(h.action) {assert(x.cfg.net.pending.get(id)==y.cfg.net.pending.get(id));}
    if h.actor is At {assert(local_input(x.cfg.net,a,h.actor->At_0).is_none());}
    assert(process_step(y.cfg.net,h.action)==h);assert((y.cfg.private)(h.actor)==(x.cfg.private)(h.actor));
    assert(ready(m,prepare(),y,h.action));
    assert(seq![e,h].drop_first() =~= seq![h] && seq![h,e].drop_first() =~= seq![e]);
    assert(tape::plays(m,x,seq![e,h])) by {reveal_with_fuel(tape::plays,3);}
    tape::swap(m,x,e,h);reveal_with_fuel(tape::plays,3);reveal_with_fuel(tape::after,3);
}

proof fn commute_preparation<S>(m:Program<S>,x:State<S>,a:Event,t:Tape)
    requires ready(m,prepare(),x,a),ordinary(m,x,t),
        forall|i:int| 0<=i<t.len() ==> tape::independent(process_step(x.cfg.net,a),#[trigger] t[i]),
    ensures ({
        let y=read::next(m,x,a);let z=tape::after(m,x,t);
        ordinary(m,y,t) && ready(m,prepare(),z,a) && tape::after(m,y,t)==read::next(m,z,a)
    }),
    decreases t.len(),
{
    if t.len()>0 {
        let h=t[0];let z=read::next(m,x,h.action);let u=t.drop_first();let e=process_step(x.cfg.net,a);
        assert(crate::independent_preparations::ordinary_input(h));commute_enabled(m,x,a,h);
        assert forall|i:int| 0<=i<u.len() implies crate::independent_preparations::ordinary_input(#[trigger] u[i])
            && tape::independent(e,u[i]) by {assert(u[i]==t[i+1]);}
        commute_preparation(m,z,a,u);
    }
}

pub proof fn loss_shares_actor_or_slot<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,a:Event,t:Tape,c:Tape) -> (j:int)
    requires ready(m,prepare(),x,a),complete(m,first,b,x,t,c),!viable(m,first,b,read::next(m,x,a)),
    ensures 0<=j<t.len(), !tape::independent(process_step(x.cfg.net,a),t[j]),
{
    let e=process_step(x.cfg.net,a);let y=read::next(m,x,a);let z=tape::after(m,x,t);
    if forall|i:int| 0<=i<t.len() ==> tape::independent(e,#[trigger] t[i]) {
        commute_preparation(m,x,a,t);mb::mailbox_survives_step(m,first,b,z,c,a);assert(complete(m,first,b,y,t,c));
    }
    choose|i:int| 0<=i<t.len() && !tape::independent(e,#[trigger] t[i])
}

pub open spec fn disables<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,a:Event) -> bool {
    ready(m,prepare(),x,a) && viable(m,first,b,x) && !viable(m,first,b,read::next(m,x,a))
}
pub open spec fn loss_at<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,s:Seq<Event>,i:int) -> bool {
    0<=i<s.len() && disables(m,first,b,info::prefix_cut(m,prepare(),x,s,i),s[i])
}

proof fn first_loss<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,s:Seq<Event>) -> (i:int)
    requires viable(m,first,b,x),!viable(m,first,b,end(m,prepare(),x,s)),
    ensures loss_at(m,first,b,x,s,i),forall|k:int| 0<=k<=i ==> viable(m,first,b,#[trigger] info::prefix_cut(m,prepare(),x,s,k)),
    decreases s.len(),
{
    let g=prepare();let a=s[0];let y=cmp::attempt(m,g,x,a);cmp::scan_step(m,g,x,s);
    assert(s.take(0) =~= Seq::empty());
    if !viable(m,first,b,y) {0} else {
        let u=s.drop_first();let j=first_loss(m,first,b,y,u);let i=j+1;
        assert forall|k:int| 0<k<=i implies #[trigger] info::prefix_cut(m,g,x,s,k)==info::prefix_cut(m,g,y,u,k-1)
            by {assert(s.take(k)[0]==a && s.take(k).drop_first() =~= u.take(k-1));cmp::scan_step(m,g,x,s.take(k));}
        assert(u[j]==s[i]);
        assert forall|k:int| 0<=k<=i implies viable(m,first,b,#[trigger] info::prefix_cut(m,g,x,s,k))
            by {if k>0 {assert(viable(m,first,b,info::prefix_cut(m,g,y,u,k-1)));}}
        i
    }
}

pub proof fn cannot_recover<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,s:Seq<Event>)
    requires !viable(m,first,b,x),
    ensures !viable(m,first,b,end(m,prepare(),x,s)),
{
    let g=prepare();let y=end(m,g,x,s);
    if viable(m,first,b,y) {
        let (t,c)=choose|t:Tape,c:Tape| #[trigger] complete(m,first,b,y,t,c);let u=asm::actions(t);
        mb::propose_native(m,y,t);cmp::append_script(m,g,x,s,u);mb::native_proposals(m,x,s+u);
        assert(complete(m,first,b,x,fired(m,g,x,s+u),c));
    }
}

// Whenever the target originally could finish, EVERY source-completing
// proposal list must contain a real destructive target step if no joint
// prefix exists. This applies in both directions, including to the exact
// actions of any independently supplied native preparation.
pub proof fn every_source_schedule_loses_other<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,d:Fork,x:State<S>,y:State<S>,s:Seq<Event>,c:Tape)
    -> (i:int)
    requires !can_join(m,first,b,d,x,y),viable(m,first,d,y),collected(m,first,b,x,s,c),
    ensures loss_at(m,first,d,y,s,i),!viable(m,first,d,end(m,prepare(),y,s)),
        forall|k:int| 0<=k<=i ==> viable(m,first,d,#[trigger] info::prefix_cut(m,prepare(),y,s,k)),
{
    joint_iff_one_quorum_still_viable(m,first,b,d,x,y);
    if viable(m,first,d,end(m,prepare(),y,s)) {let u=finish_other_quorum(m,first,b,d,x,y,s,c);assert(joint(m,first,b,d,x,y,s+u));}
    first_loss(m,first,d,y,s)
}


pub open spec fn all_lose<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,d:Fork,x:State<S>,y:State<S>) -> bool {
    forall|s:Seq<Event>,c:Tape| #[trigger] collected(m,first,b,x,s,c) ==> !viable(m,first,d,end(m,prepare(),y,s))
        && exists|i:int| #[trigger] loss_at(m,first,d,y,s,i)
}

proof fn universal_loss<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,d:Fork,x:State<S>,y:State<S>)
    requires !can_join(m,first,b,d,x,y),viable(m,first,d,y),
    ensures all_lose(m,first,b,d,x,y),
{
    assert forall|s:Seq<Event>,c:Tape| #[trigger] collected(m,first,b,x,s,c) implies !viable(m,first,d,end(m,prepare(),y,s))
        && exists|i:int| #[trigger] loss_at(m,first,d,y,s,i) by {every_source_schedule_loses_other(m,first,b,d,x,y,s,c);}
}

pub open spec fn comparable_prefix<S>(m:Program<S>,l:Lanes,n:Notice,a:fork::Tapes,b:fork::Tapes) -> bool {
    info::live_view(fork::cut(m,l,alpha(n),a))==info::live_view(fork::cut(m,l,beta(n),b))
        || exists|s:Seq<Event>| #[trigger] obs::matched_tails(m,l,n,a,b,s)
}
pub open spec fn obstruction<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice) -> bool {
    let a=alpha(n);let b=beta(n);let x=build::root(m,l,a);let y=build::root(m,l,b);
    (forall|u:fork::Tapes,v:fork::Tapes| #[trigger] fork::candidate(m,first,res,l,n,u,v) ==> !comparable_prefix(m,l,n,u,v))
        && all_lose(m,first,a,b,x,y) && all_lose(m,first,b,a,y,x)
}

proof fn incomparable_forks_lose_quorums<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    a:fork::Tapes,b:fork::Tapes)
    requires mb::setup(m,res,l,alpha(n)),mb::setup(m,res,l,beta(n)),fork::candidate(m,first,res,l,n,a,b),
        forall|u:fork::Tapes,v:fork::Tapes| #[trigger] fork::candidate(m,first,res,l,n,u,v) ==> !comparable_prefix(m,l,n,u,v),
    ensures obstruction(m,first,res,l,n),
{
    let left=alpha(n);let right=beta(n);let x=build::root(m,l,left);let y=build::root(m,l,right);
    mb::arm_has_mailbox(m,first,res,l,left,a);mb::arm_has_mailbox(m,first,res,l,right,b);
    assert(complete(m,first,left,x,a.replicas,a.caller) && complete(m,first,right,y,b.replicas,b.caller));
    native_pair_iff_joint(m,first,res,l,n);
    if can_join(m,first,left,right,x,y) {
        let (u,v,s)=choose|u:fork::Tapes,v:fork::Tapes,s:Seq<Event>| #[trigger] fork::aligned(m,l,n,u,v,s)
            && fork::candidate(m,first,res,l,n,u,v);
        obs::aligned_has_matched_tails(m,first,res,l,n,u,v,s);
        assert(comparable_prefix(m,l,n,u,v));
    }
    if can_join(m,first,right,left,y,x) {
        let s=choose|s:Seq<Event>| #[trigger] joint(m,first,right,left,y,x,s);
        assert(joint(m,first,left,right,x,y,s));
    }
    universal_loss(m,first,left,right,x,y);universal_loss(m,first,right,left,y,x);
}

pub open spec fn tested<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,e:fork::Experiment) -> bool {
    let x=fork::cut(m,l,alpha(n),e.a);let y=fork::cut(m,l,beta(n),e.b);
    let va=fork::outcome(quiet,m,res,x,e.post);let vb=fork::outcome(quiet,m,res,y,e.post);
    let legal=calls::legal_returns(5,va.unwrap()) && calls::legal_returns(2,vb.unwrap());
    fork::candidate(m,first,res,l,n,e.a,e.b) && fork::sampled(quiet,m,res,l,alpha(n),e.a,e.post)
        && fork::sampled(quiet,m,res,l,beta(n),e.b,e.post)
        && (info::live_view(x)==info::live_view(y) ==> va==vb && !legal)
        && (legal ==> va==Some(5) && vb==Some(2) && (exists|j:int| #[trigger] info::used_receipt(quiet,m,res,x,y,e.post,j))
            && (obs::prefix_use(quiet,m,res,l,n,e.a,e.b,e.pre,e.post) || obstruction(m,first,res,l,n)))
}

// Search before evaluating SR2 or H. Full alignment is a sufficient case;
// the selected preparations can instead have two different mandatory tails.
pub proof fn returning_fork_or_quorum_loss<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,aa:fork::Tapes,bb:fork::Tapes,run:fair::Runnable) -> (e:fork::Experiment)
    requires mb::setup(m,res,l,alpha(n)),mb::setup(m,res,l,beta(n)),fork::candidate(m,first,res,l,n,aa,bb),
        calls::distinct_weak_names(m),fork::available_suffixes(quiet,m,first,res,l,n,run),
    ensures tested(quiet,m,first,res,l,n,e),
        (exists|a:fork::Tapes,b:fork::Tapes| #[trigger] fork::candidate(m,first,res,l,n,a,b) && comparable_prefix(m,l,n,a,b))
            ==> comparable_prefix(m,l,n,e.a,e.b),
{
    hide(obs::prefix_use);hide(obs::matched_tails);hide(info::used_receipt);hide(majority::held);
    hide(calls::legal_returns);hide(obstruction);hide(info::live_view);
    let left=alpha(n);let right=beta(n);
    let (a,b)=if exists|a:fork::Tapes,b:fork::Tapes| #[trigger] fork::candidate(m,first,res,l,n,a,b) && comparable_prefix(m,l,n,a,b) {
        choose|a:fork::Tapes,b:fork::Tapes| #[trigger] fork::candidate(m,first,res,l,n,a,b) && comparable_prefix(m,l,n,a,b)
    } else {incomparable_forks_lose_quorums(m,first,res,l,n,aa,bb);(aa,bb)};
    let x=fork::cut(m,l,left,a);let y=fork::cut(m,l,right,b);
    assert(fork::admitted(m,first,res,l,left,a) && fork::admitted(m,first,res,l,right,b));
    let post=cmp::common_second_proposals(quiet,m,res,run,n,x,y);
    fork::quorum_value(quiet,m,first,res,l,left,a,post);fork::quorum_value(quiet,m,first,res,l,right,b,post);
    let paired=|s:Seq<Event>|obs::matched_tails(m,l,n,a,b,s);
    let pre=if exists|s:Seq<Event>| #[trigger] paired(s) {choose|s:Seq<Event>| #[trigger] paired(s)} else {Seq::empty()};
    let va=fork::outcome(quiet,m,res,x,post);let vb=fork::outcome(quiet,m,res,y,post);
    if info::live_view(x)==info::live_view(y) {info::same_residual_replays_sr2(quiet,m,res,x,y,post);}
    if calls::legal_returns(5,va.unwrap()) && calls::legal_returns(2,vb.unwrap()) {
        fork::history_completion(left,va);fork::history_completion(right,vb);
        info::distinguishing_delivery(quiet,m,res,n,x,y,post);
        if comparable_prefix(m,l,n,a,b) {
            let s=choose|s:Seq<Event>| #[trigger] obs::matched_tails(m,l,n,a,b,s);
            assert(paired(s));obs::independent_tails_use_r3(quiet,m,first,res,l,n,a,b,pre,post);
        }
    }
    fork::Experiment{a,b,pre,post}
}

pub proof fn registered_fork_or_quorum_loss<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,who:crate::hybrid_fork::Issuer,used:crate::sr1_contract::Ledger<S>,
    region:spec_fn(Fork)->crate::read_nonblocking::Region<State<S>>,run:fair::Runnable,audit:crate::hybrid_transparency::PacketAudit)
    requires crate::hybrid_fork::proper(l,who),crate::first_dispatch::initiates(m),crate::first_schedule::startup(m),crate::read_issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] crate::first_dispatch::weak_open(m,b)
            && majority::read_a(m,first,res,crate::first_schedule::reference(m,b,0),run)
            && mail::fair_opportunity(m,run,crate::first_schedule::reference(m,b,5))
            && crate::hybrid_transparency::no_first_wait(m,b,audit) && crate::sr1_contract::registered(m,b,region(b),who,used),
        calls::distinct_weak_names(m),fork::available_suffixes(quiet,m,first,res,l,n,run),
    ensures (exists|e:fork::Experiment| #[trigger] tested(quiet,m,first,res,l,n,e))
        || ((forall|a:fork::Tapes,b:fork::Tapes| !#[trigger] fork::candidate(m,first,res,l,n,a,b))
            && exists|b:Fork,p:asm::Service<S>| b.notice==n && #[trigger] fork::outside_ordinary(m,b,who,audit,p)),
{
    hide(tested);hide(fork::experiment);
    fork::registered_fork_alternatives(quiet,m,first,res,l,n,who,used,region,run,audit);
    if exists|e:fork::Experiment| #[trigger] fork::experiment(quiet,m,first,res,l,n,e) {
        let e=choose|e:fork::Experiment| #[trigger] fork::experiment(quiet,m,first,res,l,n,e);
        reveal(fork::experiment);
        let out=returning_fork_or_quorum_loss(quiet,m,first,res,l,n,e.a,e.b,run);
    }
}


// Viability quantifies exactly the selected first returns of the native
// model, including every interleaving between C1 and the replicas.
pub proof fn viable_iff_native_return<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>)
    requires crate::first_pair::c1_protected(x),!x.cfg.net.first_stopped,
    ensures viable(m,first,b,x)==(exists|p:asm::Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),x,p)
        && mb::selected_service(first,b,p)),
{
    if viable(m,first,b,x) {
        let (t,c)=choose|t:Tape,c:Tape| #[trigger] complete(m,first,b,x,t,c);
        mb::release_to_service(m,first,b,x,t,c);
    } else if exists|p:asm::Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),x,p) && mb::selected_service(first,b,p) {
        let p=choose|p:asm::Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),x,p) && mb::selected_service(first,b,p);
        mb::normalize_selected_return(m,first,b,x,p);assert(complete(m,first,b,x,crate::coupled_sources::replicas(p),calls::caller(p)));
    }
}

proof fn no_stop_prefix<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    requires !s.contains(Action::StopFirstClient),
    ensures asm::prefix(m,x,s,true)==asm::prefix(m,x,s,false),
    decreases s.len(),
{
    if s.len()>0 {
        let u=s.drop_first();assert forall|i:int| 0<=i<u.len() implies (#[trigger] u[i])!=Action::<Wire>::StopFirstClient
            by {assert(s[i+1]==u[i]);}
        no_stop_prefix(m,read::next(m,x,s[0]),u);
    }
}

pub open spec fn reporters(b:Fork) -> Set<Replica> {set![crate::origin(b.branch),Replica::R3]}

// Availability applies at the physical all-live cut even if the selected
// quorum is no longer viable. A legitimate first return exists there.
// The sole-majority sampling premise fails for every such return path.
pub proof fn availability_after_preparation<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,b:Fork,s:Seq<Event>,run:fair::Runnable,audit:crate::hybrid_transparency::PacketAudit) -> (p:asm::Service<S>)
    requires mb::setup(m,res,l,b),majority::eventual(m,res,asm::entry(m,l),run),
        mail::fair_opportunity(m,run,end(m,prepare(),build::root(m,l,b),s)),
        !wait::needs_class(mail::active_step(m),mail::posted(m),end(m,prepare(),build::root(m,l,b),s),crate::hybrid_transparency::weak_work(b,audit)),
    ensures ({
        let z=end(m,prepare(),build::root(m,l,b),s);let q=reporters(b);
        read::reached(m,asm::entry(m,l),z) && mail::submitted(z) && !mail::posted(m)(z)
            && wait::first_return(mail::active_step(m),mail::posted(m),z,p) && !wait::uses(p,crate::hybrid_transparency::weak_work(b,audit))
            && (forall|v:asm::Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),z,v)
                ==> !majority::sole(v.states.last().cfg.net,q) && (!viable(m,first,b,z) ==> !mb::selected_service(first,b,v)))
    }),
{
    let x=build::root(m,l,b);let t=fired(m,prepare(),x,s);let z=end(m,prepare(),x,s);let base=asm::entry(m,l);let boot=asm::boot(Some(b));
    let st=mail::active_step(m);let d=mail::posted(m);let effect=crate::hybrid_transparency::weak_work(b,audit);
    mb::native_proposals(m,x,s);
    assert forall|i:int| 0<=i<t.len() implies crate::coupled_traffic::preparation_input(#[trigger] t[i])
        by {assert(crate::independent_preparations::ordinary_input(t[i]));}
    build::prepared_frame(m,l,b,t);asm::launch(m,l,Some(b));
    assert forall|i:int| 0<=i<boot.len() implies (#[trigger] boot[i])!=Action::<Wire>::StopFirstClient by {prefix_index(i);}
    no_stop_prefix(m,base,boot);asm::native_prefix(m,x,t,false);asm::prefix_concat(m,base,boot,asm::actions(t),false);
    crate::first_service_loss::reachable(m,base,boot+asm::actions(t));
    assert(crate::first_pair::before_issue(m,z,l));
    let r1=Replica::R1;let r2=Replica::R2;
    assert(live(z.cfg.net,at(r1)) && live(z.cfg.net,at(r2)) && z.first_requested.contains(r1) && z.first_requested.contains(r2));
    assert(exists|r:Replica,q:Replica| r!=q && z.first_requested.contains(r) && z.first_requested.contains(q)
        && #[trigger] live(z.cfg.net,at(r)) && #[trigger] live(z.cfg.net,at(q))) by {
        assert(r1!=r2);
    }
    assert(mail::submitted(z));
    crate::first_dispatch::fanout_and_weak_open_launch(m,b);
    crate::sr1_majorities::local_at(m,b,Process::FirstClient,5);
    assert(crate::sr1_majorities::count(b,5)==5);
    assert(!d(z));
    majority::availability_at_both_clients(m,res,base,run);mail::fair_first_service(m,run,|u|read::reached(m,base,u),z);
    crate::read_nonblocking::first_response_iff(st,d,z);assert(wait::can_finish(st,d,z));
    let p=choose|p:asm::Service<S>| #[trigger] wait::first_return(st,d,z,p) && !wait::uses(p,effect);
    viable_iff_native_return(m,first,b,z);
    assert forall|v:asm::Service<S>| #[trigger] wait::first_return(st,d,z,v) implies !majority::sole(v.states.last().cfg.net,reporters(b))
        && (!viable(m,first,b,z) ==> !mb::selected_service(first,b,v)) by {
        assert(wait::valid_edges(read::service_step(m),v)) by {
            assert forall|k:int| 0<=k<v.actions.len() implies read::service_step(m)(v.states[k],#[trigger] v.actions[k],v.states[k+1])
                by {assert(st(v.states[k],v.actions[k],v.states[k+1]));}
        }
        majority::mask_unchanged(m,v,v.actions.len());let r=crate::sr1_majorities::missing(b);
        assert(!reporters(b).contains(r) && live(v.states.last().cfg.net,at(r)));
    }
    p
}


// Compare two real cuts on the SAME fork input. Only the actors and slots
// mentioned by the remaining working service, including C1, matter.
pub open spec fn resource_diff<S>(x:State<S>,y:State<S>,t:Tape,i:int) -> bool {
    let e=t[i];let k=tape::slot(e.action);
    0<=i<t.len() && ((e.actor is At && (x.cfg.private)(e.actor)!=(y.cfg.private)(e.actor))
        || (k.is_some() && (x.cfg.net.pending.get(k.unwrap())!=y.cfg.net.pending.get(k.unwrap())
            || x.reserved.contains(k.unwrap())!=y.reserved.contains(k.unwrap()))))
}

// After an opposite-arm preparation has made this quorum nonviable, take
// ANY working native service on this fork. At EVERY resume point of its
// replica tape, an actor or slot it still needs differs from the reached
// cut. Differences at untouched sites cannot account for quorum loss.
pub proof fn failed_resume_has_resource_difference<S>(m:Program<S>,first:spec_fn(S)->int,l:Lanes,b:Fork,s:Seq<Event>,
    t:Tape,c:Tape,k:int) -> (i:int)
    requires asm::lanes_ok(l),complete(m,first,b,build::root(m,l,b),t,c),0<=k<=t.len(),
        !viable(m,first,b,end(m,prepare(),build::root(m,l,b),s)),
    ensures resource_diff(tape::after(m,build::root(m,l,b),t.take(k)),end(m,prepare(),build::root(m,l,b),s),t.skip(k)+c,i),
{
    let x=build::root(m,l,b);let head=t.take(k);let rem=t.skip(k);let tail=rem+c;
    let u=tape::after(m,x,head);let old=tape::after(m,x,t);
    let fired=fired(m,prepare(),x,s);let z=end(m,prepare(),x,s);
    let ps=ISet::new(|p:Process|exists|i:int| 0<=i<tail.len() && (#[trigger] tail[i]).actor==p);
    let ids=ISet::new(|id:nat|exists|i:int| 0<=i<tail.len() && tape::slot((#[trigger] tail[i]).action)==Some(id));
    assert(head+rem =~= t);tape::concat(m,x,head,rem);tape::concat(m,u,rem,c);mb::native_proposals(m,x,s);
    assert forall|i:int| 0<=i<head.len() implies crate::coupled_traffic::preparation_input(#[trigger] head[i])
        by {assert(head[i]==t[i] && crate::independent_preparations::ordinary_input(t[i]));}
    assert forall|i:int| 0<=i<fired.len() implies crate::coupled_traffic::preparation_input(#[trigger] fired[i])
        by {assert(crate::independent_preparations::ordinary_input(fired[i]));}
    build::prepared_frame(m,l,b,head);build::prepared_frame(m,l,b,fired);
    crate::independent_preparations::ordinary_cells(m,x,head);crate::independent_preparations::ordinary_cells(m,x,fired);
    if !exists|i:int| #[trigger] resource_diff(u,z,tail,i) {
        assert forall|p:Process| ps.contains(p) implies #[trigger] (u.cfg.private)(p)==(z.cfg.private)(p) by {
            let j=choose|j:int| 0<=j<tail.len() && (#[trigger] tail[j]).actor==p;assert(!resource_diff(u,z,tail,j));
        }
        assert forall|id:nat| ids.contains(id) implies #[trigger] u.cfg.net.pending.get(id)==z.cfg.net.pending.get(id)
            && u.reserved.contains(id)==z.reserved.contains(id) by {
            let j=choose|j:int| 0<=j<tail.len() && tape::slot((#[trigger] tail[j]).action)==Some(id);assert(!resource_diff(u,z,tail,j));
        }
        assert forall|j:int| 0<=j<tail.len() implies {let e=#[trigger] tail[j];ps.contains(e.actor)
            && (tape::slot(e.action).is_some() ==> ids.contains(tape::slot(e.action).unwrap()))} by {
            let e=tail[j];assert(tail[j].actor==e.actor);
        }
        assert forall|j:int| 0<=j<tail.len() implies read::names_sender(z,(#[trigger] tail[j]).action) by {
            let v=tail.take(j);let w=tape::after(m,u,v);assert(v+tail.skip(j) =~= tail);tape::concat(m,u,v,tail.skip(j));
            assert(tail.skip(j)[0]==tail[j]);tape::frame(m,u,v,ISet::full(),ISet::full());assert(read::names_sender(w,tail[j].action));
        }
        tape::replay(m,u,z,tail,ps,ids);tape::concat(m,z,rem,c);
        assert forall|j:int| 0<=j<rem.len() implies crate::independent_preparations::ordinary_input(#[trigger] rem[j])
            by {assert(rem[j]==t[j+k]);}
        let w=tape::after(m,z,rem);mb::ordinary_keeps_caller(m,z,rem);mb::ordinary_keeps_caller(m,u,rem);
        crate::independent_preparations::initial_mailbox(m,w,c);calls::play_client(m,old,w,c);
        assert(mailbox(m,first,b,w,c));assert(complete(m,first,b,z,rem,c));
    }
    choose|i:int| #[trigger] resource_diff(u,z,tail,i)
}


// A concrete sufficient condition for the positive branch. Resume at any
// cursor of a different working target service. Outside that suffix's
// actors and transport slots the two target configurations are unrestricted.
pub proof fn couple_at_resume_point<S>(m:Program<S>,first:spec_fn(S)->int,l:Lanes,b:Fork,d:Fork,s:Seq<Event>,c:Tape,t:Tape,h:Tape,k:int)
    -> (more:Seq<Event>)
    requires asm::lanes_ok(l),collected(m,first,b,build::root(m,l,b),s,c),
        complete(m,first,d,build::root(m,l,d),t,h),0<=k<=t.len(),
        forall|i:int| !#[trigger] resource_diff(tape::after(m,build::root(m,l,d),t.take(k)),end(m,prepare(),build::root(m,l,d),s),t.skip(k)+h,i),
    ensures joint(m,first,b,d,build::root(m,l,b),build::root(m,l,d),s+more),
{
    let x=build::root(m,l,b);let y=build::root(m,l,d);
    if !viable(m,first,d,end(m,prepare(),y,s)) {failed_resume_has_resource_difference(m,first,l,d,s,t,h,k);}
    finish_other_quorum(m,first,b,d,x,y,s,c)
}

}
