// Original independent-client fork. A common proposal schedule is tested
// against both native machines. The history observer is defined on writer
// identities and an already justified prefix, independently of that test.
use vstd::prelude::*;
use crate::{Op, RecoveredOrder, checkpoint::*, delivery::*};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::fair_read as fair;
use crate::first_assembly::{self as asm, Lanes};
use crate::first_pair as pair;
use crate::first_splice::Tape;
use crate::fork_information::{self as info, caller2};
use crate::guarded_comparison::{self as cmp, end, fired, prepare, second};
use crate::hybrid_majority as majority;
use crate::independent_preparations as prep;
use crate::independent_read::{self as read, State};
use crate::order_extension as history;
use crate::precedence::{self, Side};
use crate::read_call::{Event,Program};
use crate::read_issue as issue;

verus! {

pub struct Tapes { pub replicas:Tape, pub caller:Tape }

pub open spec fn admitted<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,t:Tapes) -> bool {
    prep::arm(m,first,res,l,b,t.replicas,t.caller)
}
pub open spec fn cut<S>(m:Program<S>,l:Lanes,b:Fork,t:Tapes) -> State<S> {
    prep::cutoff(m,l,b,t.replicas,t.caller)
}
pub open spec fn wake() -> Seq<Event> {seq![Action::StopFirstClient,Action::CrashR3,Action::StartSecondClient]}
pub open spec fn invocation<S>(m:Program<S>,l:Lanes,b:Fork,t:Tapes) -> State<S> {
    asm::drive(m,build::first_end(m,l,b,t.replicas,t.caller),wake())
}
pub open spec fn outcome<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>) -> Option<int> {
    res(caller2(end(m,second(quiet,res),x,s)))
}

pub proof fn quorum_value<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,b:Fork,t:Tapes,s:Seq<Event>)
    requires admitted(m,first,res,l,b,t), issue::can_issue(m,res), majority::sampling(m,first,res,invocation(m,l,b,t)),
        cmp::second_return(quiet,m,res,b,cut(m,l,b,t),s),
    ensures ({
        let x=cut(m,l,b,t); let p=cmp::path(m,x,fired(m,second(quiet,res),x,s));
        majority::held(p.states,live_pair(),outcome(quiet,m,res,x,s).unwrap())
    }),
{
    let start=build::prefix_actions(b,t.replicas,t.caller);let z=build::first_end(m,l,b,t.replicas,t.caller);
    let i=invocation(m,l,b,t);let h=majority::second_head(m,i);let x=cut(m,l,b,t);
    let p=cmp::path(m,x,fired(m,second(quiet,res),x,s));
    assert(pair::close(true) =~= wake()+h.actions);
    asm::prefix_concat(m,asm::entry(m,l),start,pair::close(true),true);asm::prefix_concat(m,z,wake(),h.actions,true);
    reveal_with_fuel(asm::drive,4);reveal_with_fuel(asm::prefix,3);
    assert(crate::read_nonblocking::within(read::prefix_step(m),read::at_state(i),i,0));
    assert(h.states.last()==x);majority::second_quorum_rule(m,first,res,i,i,p);
}

// Quotient the actual SR2 computation by precisely its usable checkpoint.
// 'choose' is used only to construct a representative. real_selection
// proves agreement with EVERY physical after-crash representative.
pub open spec fn selects<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,initial:S,s:Seq<Event>,v:info::Residual<S>) -> Option<int> {
    let represents=|x:State<S>|crate::survivors::after_crash(x.cfg.net) && caller2(x)==initial && info::live_view(x)==v;
    if exists|x:State<S>| #[trigger] represents(x) {
        outcome(quiet,m,res,choose|x:State<S>| #[trigger] represents(x),s)
    } else { None }
}

pub proof fn real_selection<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>)
    requires crate::survivors::after_crash(x.cfg.net),
    ensures selects(quiet,m,res,caller2(x),s,info::live_view(x))==outcome(quiet,m,res,x,s),
{
    let represents=|y:State<S>|crate::survivors::after_crash(y.cfg.net) && caller2(y)==caller2(x) && info::live_view(y)==info::live_view(x);
    assert(represents(x));let y=choose|y:State<S>| #[trigger] represents(y);
    info::same_residual_replays_sr2(quiet,m,res,x,y,s);
}

// Writer identities in the workload's register. A protocol may return
// either value from a cache; this labels the semantic version of the
// result, independently of the immediate sender of any physical packet.
pub open spec fn writer(v:Option<int>) -> Option<Op> {
    if v==Some(2) {Some(Op::W1)} else if v==Some(5) {Some(Op::W2)} else {None}
}

pub open spec fn gain(b:Fork,actual:Option<int>,alternative:Option<int>) -> bool {
    let w=observed_writer(b);let old=history::at_first(b).ops;let a=writer(actual);let d=writer(alternative);
    a.is_some() && d.is_some() && history::can_keep(old,w,a.unwrap()) && !history::can_keep(old,w,d.unwrap())
}

// A specific functional interpretation, for a CONTROLLED pair: a gain
// in legal extension through the retained phase requires independent order
// support. The observer does not mention equality of SR2 outputs or H.
pub open spec fn supported(b:Fork,actual:Option<int>,alternative:Option<int>,credit:precedence::Credit) -> bool {
    gain(b,actual,alternative) ==> credit(precedence::independent_view(b),observed_writer(b),writer(alternative).unwrap())
}

pub proof fn gain_tests_source_selection(b:Fork,actual:Option<int>,alternative:Option<int>,credit:precedence::Credit)
    requires writer(actual).is_some(),writer(alternative).is_some(),
    ensures supported(b,actual,alternative,credit)==precedence::supported_read_update(Some(observed_writer(b)),
        precedence::source_versions(),if alternative==Some(2) {Side::Left} else {Side::Right},
        if actual==Some(2) {Side::Left} else {Side::Right},precedence::independent_view(b),credit),
{
    history::canonical_orders_exist(b);
    history::extension_iff_writer(b,history::at_first(b),writer(actual).unwrap());
    history::extension_iff_writer(b,history::at_first(b),writer(alternative).unwrap());
}

pub open spec fn probe<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    initial:S,pre:Seq<Event>,post:Seq<Event>,high:(int,S)) -> Option<int> {
    selects(quiet,m,res,initial,post,info::channel(m,l,n,pre,high))
}

pub open spec fn aligned<S>(m:Program<S>,l:Lanes,n:Notice,a:Tapes,b:Tapes,pre:Seq<Event>) -> bool {
    cmp::realizes(m,prepare(),build::root(m,l,alpha(n)),build::root(m,l,beta(n)),a.replicas,b.replicas,pre)
}
pub open spec fn frontier<S>(m:Program<S>,l:Lanes,n:Notice,a:Tapes,b:Tapes,pre:Seq<Event>) -> bool {
    cmp::blocked(m,prepare(),build::root(m,l,alpha(n)),build::root(m,l,beta(n)),a.replicas,b.replicas,pre)
}

pub open spec fn export_at<S>(m:Program<S>,l:Lanes,n:Notice,pre:Seq<Event>,j:int) -> bool {
    let u=info::prefix_cut(m,prepare(),build::root(m,l,alpha(n)),pre,j);
    let v=info::prefix_cut(m,prepare(),build::root(m,l,beta(n)),pre,j);
    0<=j<pre.len() && crate::coupled_traffic::paired(u,v,n,info::identity()) && info::exported(m,u,v,pre[j])
}

// No individual packet is presumed pivotal. The two actual, different
// residuals are inputs to the SAME independent C2 computation. The
// quotient also factors out the distinct first clients' private returns.
pub open spec fn retained_use<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,a:Tapes,b:Tapes,
    pre:Seq<Event>,post:Seq<Event>) -> bool {
    let left=alpha(n); let right=beta(n); let x=cut(m,l,left,a); let y=cut(m,l,right,b);
    let ax=info::installed(m,left);let by=info::installed(m,right);let initial=caller2(x);
    let va=probe(quiet,m,res,l,n,initial,pre,post,ax);let vb=probe(quiet,m,res,l,n,initial,pre,post,by);
    caller2(y)==initial
        && info::channel(m,l,n,pre,ax)==info::live_view(x) && info::channel(m,l,n,pre,by)==info::live_view(y)
        && info::live_view(x)!=info::live_view(y)
        && va==outcome(quiet,m,res,x,post) && vb==outcome(quiet,m,res,y,post)
        && (exists|j:int| #[trigger] export_at(m,l,n,pre,j))
        && (exists|j:int| #[trigger] info::used_receipt(quiet,m,res,x,y,post,j))
        && gain(left,va,vb) && gain(right,vb,va)
}

pub open spec fn controlled_use<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,a:Tapes,b:Tapes,
    pre:Seq<Event>,post:Seq<Event>) -> bool {
    aligned(m,l,n,a,b,pre) && retained_use(quiet,m,res,l,n,a,b,pre,post)
}

pub(crate) proof fn history_completion(b:Fork,v:Option<int>)
    requires v.is_some(),calls::legal_returns(first_value(b),v.unwrap()),
    ensures v==Some(first_value(b)),writer(v)==Some(observed_writer(b)),
        history::extension(history::at_first(b).ops,observed_writer(b),writer(v).unwrap(),history::at_second(b)),
        history::same_weak_order(history::at_first(b).ops,history::at_second(b).ops),
{
    let (o,xs)=choose|o:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(o,xs,first_value(b),v.unwrap());
    history::exact_completed_order(b,RecoveredOrder{ops:o,states:xs},v.unwrap());history::canonical_extension(b);
}

// A certificate checker independent of global progress. Both scripts can
// instead be supplied by an admitted finite implementation fragment.
pub proof fn two_native_histories_use_r3<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>)
    requires admitted(m,first,res,l,alpha(n),a),admitted(m,first,res,l,beta(n),b),aligned(m,l,n,a,b,pre),
        cmp::second_return(quiet,m,res,alpha(n),cut(m,l,alpha(n),a),post),
        cmp::second_return(quiet,m,res,beta(n),cut(m,l,beta(n),b),post),
        calls::legal_returns(5,outcome(quiet,m,res,cut(m,l,alpha(n),a),post).unwrap()),
        calls::legal_returns(2,outcome(quiet,m,res,cut(m,l,beta(n),b),post).unwrap()),
    ensures controlled_use(quiet,m,res,l,n,a,b,pre,post),
{
    crate::schedule_observations::aligned_has_matched_tails(m,first,res,l,n,a,b,pre);
    crate::schedule_observations::independent_tails_use_r3(quiet,m,first,res,l,n,a,b,pre,post);
}

// Exact case split for any TWO admitted original prefixes. The common
// continuation is constructed before testing H or attempting to attribute
// differences. It may fire different native actions on its two arms.
pub proof fn original_fork_alternatives<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,run:fair::Runnable) -> (scripts:(Seq<Event>,Seq<Event>))
    requires admitted(m,first,res,l,alpha(n),a),admitted(m,first,res,l,beta(n),b),calls::distinct_weak_names(m),
        cmp::opportunity(quiet,m,res,run,alpha(n),cut(m,l,alpha(n),a)),cmp::opportunities(quiet,m,res,run,beta(n),cut(m,l,beta(n),b)),
    ensures ({
        let left=alpha(n);let right=beta(n);let x=cut(m,l,left,a);let y=cut(m,l,right,b);let (pre,post)=scripts;
        let va=outcome(quiet,m,res,x,post);let vb=outcome(quiet,m,res,y,post);
        let histories=calls::legal_returns(5,va.unwrap()) && calls::legal_returns(2,vb.unwrap());
        cmp::second_return(quiet,m,res,left,x,post) && cmp::second_return(quiet,m,res,right,y,post)
            && va.is_some() && vb.is_some()
            && (info::live_view(x)==info::live_view(y) ==> va==vb && !histories
                && fired(m,second(quiet,res),x,post)==fired(m,second(quiet,res),y,post))
            && (histories ==> va==Some(5) && vb==Some(2) && (exists|j:int| #[trigger] info::used_receipt(quiet,m,res,x,y,post,j)))
            && ((aligned(m,l,n,a,b,pre) && (histories ==> controlled_use(quiet,m,res,l,n,a,b,pre,post)))
                || (frontier(m,l,n,a,b,pre) && forall|s:Seq<Event>| !#[trigger] aligned(m,l,n,a,b,s)))
    }),
{
    hide(controlled_use);hide(info::used_receipt);hide(info::exported);hide(info::channel);hide(selects);
    let left=alpha(n);let right=beta(n);let x=cut(m,l,left,a);let y=cut(m,l,right,b);let g=second(quiet,res);
    let rx=build::root(m,l,left);let ry=build::root(m,l,right);
    let post=cmp::common_second_proposals(quiet,m,res,run,n,x,y);
    let va=outcome(quiet,m,res,x,post);let vb=outcome(quiet,m,res,y,post);
    if info::live_view(x)==info::live_view(y) {info::same_residual_replays_sr2(quiet,m,res,x,y,post);}
    cmp::prepared_tape(m,rx,a.replicas);cmp::prepared_tape(m,ry,b.replicas);
    let pre=cmp::common_proposals_or_conflict(m,prepare(),rx,ry,a.replicas,b.replicas);
    if !aligned(m,l,n,a,b,pre) {
        assert forall|s:Seq<Event>| !#[trigger] aligned(m,l,n,a,b,s) by {
            assert(!cmp::realizes(m,prepare(),rx,ry,a.replicas,b.replicas,s));
        }
    }
    if calls::legal_returns(5,va.unwrap()) && calls::legal_returns(2,vb.unwrap()) {
        history_completion(left,va);history_completion(right,vb);
        let j=info::distinguishing_delivery(quiet,m,res,n,x,y,post);
        if aligned(m,l,n,a,b,pre) {
            two_native_histories_use_r3(quiet,m,first,res,l,n,a,b,pre,post);
        }
    }
    (pre,post)
}

pub proof fn unsupported_retained_gain<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>,aa:bool,ab:bool,credit:precedence::Credit)
    requires retained_use(quiet,m,res,l,n,a,b,pre,post), n!=Notice::Replication ==> aa && ab,
        precedence::sound_credit(credit,precedence::actual_cuts(n,aa,ab)),
    ensures ({
        let va=outcome(quiet,m,res,cut(m,l,alpha(n),a),post);let vb=outcome(quiet,m,res,cut(m,l,beta(n),b),post);
        !supported(alpha(n),va,vb,credit) && !supported(beta(n),vb,va,credit)
    }),
{
    let left=alpha(n);let right=beta(n);let va=outcome(quiet,m,res,cut(m,l,left,a),post);
    let vb=outcome(quiet,m,res,cut(m,l,right,b),post);
    history::canonical_orders_exist(left);history::canonical_orders_exist(right);
    history::extension_iff_writer(left,history::at_first(left),writer(va).unwrap());
    history::extension_iff_writer(right,history::at_first(right),writer(vb).unwrap());
    precedence::two_real_cuts_exclude_both_credits(n,aa,ab,precedence::actual_cuts(n,aa,ab),credit);
}

pub proof fn unsupported_controlled_gain<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>,aa:bool,ab:bool,credit:precedence::Credit)
    requires controlled_use(quiet,m,res,l,n,a,b,pre,post), n!=Notice::Replication ==> aa && ab,
        precedence::sound_credit(credit,precedence::actual_cuts(n,aa,ab)),
    ensures ({
        let va=outcome(quiet,m,res,cut(m,l,alpha(n),a),post);let vb=outcome(quiet,m,res,cut(m,l,beta(n),b),post);
        !supported(alpha(n),va,vb,credit) && !supported(beta(n),vb,va,credit)
    }),
{
    unsupported_retained_gain(quiet,m,res,l,n,a,b,pre,post,aa,ab,credit);
}

// Choose among ALL admitted original preparations on purely operational
// criteria, before selecting SR2 or testing the histories.
pub open spec fn comparable<S>(m:Program<S>,l:Lanes,n:Notice,a:Tapes,b:Tapes) -> bool {
    info::live_view(cut(m,l,alpha(n),a))==info::live_view(cut(m,l,beta(n),b))
        || exists|s:Seq<Event>| #[trigger] aligned(m,l,n,a,b,s)
}

pub open spec fn candidate<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,a:Tapes,b:Tapes) -> bool {
    admitted(m,first,res,l,alpha(n),a) && admitted(m,first,res,l,beta(n),b)
}

// Eligibility is entirely operational. The SR1 results fix the fork under
// study, but there is no test for SR2's result or for changed metadata.
pub open spec fn eligible<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>) -> bool {
    candidate(m,first,res,l,n,a,b) && aligned(m,l,n,a,b,pre)
        && cmp::second_return(quiet,m,res,alpha(n),cut(m,l,alpha(n),a),post)
        && cmp::second_return(quiet,m,res,beta(n),cut(m,l,beta(n),b),post)
}

// Paired functional reading of the prose. It is limited to comparisons
// whose independent order evidence is represented by the supplied credit.
// The before/after arguments here are two realized phase inputs, not two
// consecutive local states in the same execution.
pub open spec fn respects_retained_history<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,credit:precedence::Credit) -> bool {
    forall|a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>| #[trigger] eligible(quiet,m,first,res,l,n,a,b,pre,post) ==> {
        let initial=caller2(cut(m,l,alpha(n),a));let f=|h:(int,S)|probe(quiet,m,res,l,n,initial,pre,post,h);
        let va=f(info::installed(m,alpha(n)));let vb=f(info::installed(m,beta(n)));
        supported(alpha(n),va,vb,credit) && supported(beta(n),vb,va,credit)
    }
}

pub proof fn paired_preservation_requires_source_support<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>,credit:precedence::Credit)
    requires eligible(quiet,m,first,res,l,n,a,b,pre,post),respects_retained_history(quiet,m,first,res,l,n,credit),
        writer(outcome(quiet,m,res,cut(m,l,alpha(n),a),post)).is_some(),writer(outcome(quiet,m,res,cut(m,l,beta(n),b),post)).is_some(),
    ensures ({
        let va=outcome(quiet,m,res,cut(m,l,alpha(n),a),post);let vb=outcome(quiet,m,res,cut(m,l,beta(n),b),post);
        let sa=if va==Some(2) {Side::Left} else {Side::Right};let sb=if vb==Some(2) {Side::Left} else {Side::Right};
        precedence::supported_read_update(Some(observed_writer(alpha(n))),precedence::source_versions(),sb,sa,precedence::independent_view(alpha(n)),credit)
            && precedence::supported_read_update(Some(observed_writer(beta(n))),precedence::source_versions(),sa,sb,precedence::independent_view(beta(n)),credit)
    }),
{
    let left=alpha(n);let right=beta(n);let x=cut(m,l,left,a);let y=cut(m,l,right,b);
    info::source_to_retained_cut(m,first,res,l,left,a.replicas,a.caller,pre);
    info::source_to_retained_cut(m,first,res,l,right,b.replicas,b.caller,pre);
    real_selection(quiet,m,res,x,post);real_selection(quiet,m,res,y,post);
    gain_tests_source_selection(left,outcome(quiet,m,res,x,post),outcome(quiet,m,res,y,post),credit);
    gain_tests_source_selection(right,outcome(quiet,m,res,y,post),outcome(quiet,m,res,x,post),credit);
}

pub proof fn paired_preservation_or_history_failure<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>,aa:bool,ab:bool,credit:precedence::Credit)
    requires eligible(quiet,m,first,res,l,n,a,b,pre,post),n!=Notice::Replication ==> aa && ab,
        precedence::sound_credit(credit,precedence::actual_cuts(n,aa,ab)),
    ensures !respects_retained_history(quiet,m,first,res,l,n,credit)
        || !calls::legal_returns(5,outcome(quiet,m,res,cut(m,l,alpha(n),a),post).unwrap())
        || !calls::legal_returns(2,outcome(quiet,m,res,cut(m,l,beta(n),b),post).unwrap()),
{
    let x=cut(m,l,alpha(n),a);let y=cut(m,l,beta(n),b);
    if calls::legal_returns(5,outcome(quiet,m,res,x,post).unwrap()) && calls::legal_returns(2,outcome(quiet,m,res,y,post).unwrap()) {
        two_native_histories_use_r3(quiet,m,first,res,l,n,a,b,pre,post);
        unsupported_controlled_gain(quiet,m,res,l,n,a,b,pre,post,aa,ab,credit);
    }
}

pub open spec fn schedules_obstruct<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice) -> bool {
    forall|a:Tapes,b:Tapes| #[trigger] candidate(m,first,res,l,n,a,b) ==> !comparable(m,l,n,a,b)
        && exists|s:Seq<Event>| #[trigger] frontier(m,l,n,a,b,s)
}

pub open spec fn available_suffixes<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,run:fair::Runnable) -> bool {
    forall|b:Fork,t:Tapes| b.notice==n && #[trigger] admitted(m,first,res,l,b,t) ==>
        majority::sampling(m,first,res,invocation(m,l,b,t)) && if b.branch==crate::Branch::Alpha {
            cmp::opportunity(quiet,m,res,run,b,cut(m,l,b,t))
        } else {cmp::opportunities(quiet,m,res,run,b,cut(m,l,b,t))}
}

pub struct Experiment {pub a:Tapes,pub b:Tapes,pub pre:Seq<Event>,pub post:Seq<Event>}

pub open spec fn sampled<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,t:Tapes,post:Seq<Event>) -> bool {
    let x=cut(m,l,b,t); let p=cmp::path(m,x,fired(m,second(quiet,res),x,post));
    cmp::second_return(quiet,m,res,b,x,post) && majority::held(p.states,live_pair(),outcome(quiet,m,res,x,post).unwrap())
}

pub open spec fn experiment<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,e:Experiment) -> bool {
    let x=cut(m,l,alpha(n),e.a);let y=cut(m,l,beta(n),e.b);let va=outcome(quiet,m,res,x,e.post);let vb=outcome(quiet,m,res,y,e.post);
    let bad=!calls::legal_returns(5,va.unwrap()) || !calls::legal_returns(2,vb.unwrap());
    candidate(m,first,res,l,n,e.a,e.b) && sampled(quiet,m,res,l,alpha(n),e.a,e.post) && sampled(quiet,m,res,l,beta(n),e.b,e.post)
        && (info::live_view(x)==info::live_view(y) ==> va==vb && bad && fired(m,second(quiet,res),x,e.post)==fired(m,second(quiet,res),y,e.post))
        && (!bad ==> va==Some(5) && vb==Some(2) && exists|j:int| #[trigger] info::used_receipt(quiet,m,res,x,y,e.post,j))
        && (bad || controlled_use(quiet,m,res,l,n,e.a,e.b,e.pre,e.post)
            || (schedules_obstruct(m,first,res,l,n) && frontier(m,l,n,e.a,e.b,e.pre)))
}

pub proof fn choose_original_fork<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,aa:Tapes,bb:Tapes,run:fair::Runnable) -> (e:Experiment)
    requires candidate(m,first,res,l,n,aa,bb),issue::can_issue(m,res),calls::distinct_weak_names(m),available_suffixes(quiet,m,first,res,l,n,run),
    ensures experiment(quiet,m,first,res,l,n,e),
        (exists|a:Tapes,b:Tapes| #[trigger] candidate(m,first,res,l,n,a,b) && comparable(m,l,n,a,b))
            ==> comparable(m,l,n,e.a,e.b),
{
    hide(info::used_receipt);hide(controlled_use);hide(majority::held);hide(cmp::second_return);
    let (a,b)=if exists|a:Tapes,b:Tapes| #[trigger] candidate(m,first,res,l,n,a,b) && comparable(m,l,n,a,b) {
        choose|a:Tapes,b:Tapes| #[trigger] candidate(m,first,res,l,n,a,b) && comparable(m,l,n,a,b)
    } else {
        assert forall|a:Tapes,b:Tapes| #[trigger] candidate(m,first,res,l,n,a,b) implies
            !comparable(m,l,n,a,b) && exists|s:Seq<Event>| #[trigger] frontier(m,l,n,a,b,s) by {
            let rx=build::root(m,l,alpha(n));let ry=build::root(m,l,beta(n));
            cmp::prepared_tape(m,rx,a.replicas);cmp::prepared_tape(m,ry,b.replicas);
            let s=cmp::common_proposals_or_conflict(m,prepare(),rx,ry,a.replicas,b.replicas);
            assert(!aligned(m,l,n,a,b,s));assert(frontier(m,l,n,a,b,s));
        }
        (aa,bb)
    };
    assert(admitted(m,first,res,l,alpha(n),a) && admitted(m,first,res,l,beta(n),b));
    let (pre,post)=original_fork_alternatives(quiet,m,first,res,l,n,a,b,run);
    quorum_value(quiet,m,first,res,l,alpha(n),a,post);quorum_value(quiet,m,first,res,l,beta(n),b,post);
    Experiment{a,b,pre,post}
}

// Compose the operational split with the interpretation. The sole
// remaining alternative after two legal returns is a certificate about
// EVERY admitted preparation pair, independent of how this pair was found.
pub proof fn legal_fork_under_paired_t<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,e:Experiment,aa:bool,ab:bool,credit:precedence::Credit)
    requires experiment(quiet,m,first,res,l,n,e),respects_retained_history(quiet,m,first,res,l,n,credit),
        calls::legal_returns(5,outcome(quiet,m,res,cut(m,l,alpha(n),e.a),e.post).unwrap()),
        calls::legal_returns(2,outcome(quiet,m,res,cut(m,l,beta(n),e.b),e.post).unwrap()),
        n!=Notice::Replication ==> aa && ab,precedence::sound_credit(credit,precedence::actual_cuts(n,aa,ab)),
    ensures schedules_obstruct(m,first,res,l,n),frontier(m,l,n,e.a,e.b,e.pre),
{
    if controlled_use(quiet,m,res,l,n,e.a,e.b,e.pre,e.post) {
        paired_preservation_or_history_failure(quiet,m,first,res,l,n,e.a,e.b,e.pre,e.post,aa,ab,credit);
    }
}

pub open spec fn outside_ordinary<S>(m:Program<S>,b:Fork,who:crate::hybrid_fork::Issuer,
    audit:crate::hybrid_transparency::PacketAudit,p:asm::Service<S>) -> bool {
    crate::coupled_sources::source(m,b,who,audit,p)
        && (forall|q:asm::Service<S>| #[trigger] crate::coupled_sources::source(m,b,who,audit,q) ==> !prep::ordinary_source(q))
        && exists|i:int| 0<=i<p.actions.len() && {let e=#[trigger] crate::first_splice::record(p,0)[i];
            e.actor!=Process::FirstClient && !prep::ordinary_input(e)}
}

// The first two alternatives are precise failures of the construction's
// ordinary source language. An unrestricted protocol has no contract to
// use particular R3 packets, respond at an idle site, or couple its guards.
pub proof fn registered_fork_alternatives<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,who:crate::hybrid_fork::Issuer,used:crate::sr1_contract::Ledger<S>,
    region:spec_fn(Fork)->crate::read_nonblocking::Region<State<S>>,run:fair::Runnable,audit:crate::hybrid_transparency::PacketAudit)
    requires crate::hybrid_fork::proper(l,who),crate::first_dispatch::initiates(m),crate::first_schedule::startup(m),issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] crate::first_dispatch::weak_open(m,b)
            && majority::read_a(m,first,res,crate::first_schedule::reference(m,b,0),run)
            && crate::first_mailbox::fair_opportunity(m,run,crate::first_schedule::reference(m,b,5))
            && crate::hybrid_transparency::no_first_wait(m,b,audit) && crate::sr1_contract::registered(m,b,region(b),who,used),
        calls::distinct_weak_names(m),available_suffixes(quiet,m,first,res,l,n,run),
    ensures (exists|e:Experiment| #[trigger] experiment(quiet,m,first,res,l,n,e))
        || ((forall|a:Tapes,b:Tapes| !#[trigger] candidate(m,first,res,l,n,a,b))
            && exists|b:Fork,p:asm::Service<S>| b.notice==n && #[trigger] outside_ordinary(m,b,who,audit,p)),
{
    hide(experiment);hide(cmp::opportunity);hide(cmp::opportunities);hide(prep::arm);
    let left=alpha(n);let right=beta(n);
    let p=prep::available_arm_or_source_step(m,first,res,l,left,who,used,region(left),run,audit);
    let q=prep::available_arm_or_source_step(m,first,res,l,right,who,used,region(right),run,audit);
    if exists|a:Tapes,b:Tapes| #[trigger] candidate(m,first,res,l,n,a,b) {
        let (a,b)=choose|a:Tapes,b:Tapes| #[trigger] candidate(m,first,res,l,n,a,b);
        let e=choose_original_fork(quiet,m,first,res,l,n,a,b,run);
    } else {
        let a=Tapes{replicas:crate::coupled_sources::replicas(p),caller:calls::caller(p)};
        let b=Tapes{replicas:crate::coupled_sources::replicas(q),caller:calls::caller(q)};
        assert(!candidate(m,first,res,l,n,a,b));
        if !prep::ordinary_source(p) {assert(outside_ordinary(m,left,who,audit,p));}
        else {assert(outside_ordinary(m,right,who,audit,q));}
    }
}

}
