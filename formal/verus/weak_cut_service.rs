// A reachability test at the common boundary of the original weak fork.
// Only the reference stops R3 here. No delivery or installation at R3 is used.
use vstd::prelude::*;
use crate::{Op, Replica, RecoveredOrder, checkpoint::*, delivery::*};
use crate::async_messages::{self as net, Headers};
use crate::fanout_service::supplied_genesis;
use crate::first_assembly::{self as asm, Service};
use crate::first_mailbox as mail;
use crate::hybrid_majority as maj;
use crate::independent_read::{self as read, State};
use crate::native_fork as fork;
use crate::order_extension as order;
use crate::original_application as app;
use crate::prepared_service as svc;
use crate::promotion_wait as wait;
use crate::read_call::{Program,Event};
use crate::read_nonblocking as nb;
use crate::weak_construction as wc;

verus! {

// A decoder of an actual stored invocation at one replica. It may inspect
// its private representation. An in-flight packet is not local storage.
pub type Stored<S> = spec_fn(Replica,S,int,Op)->bool;

pub open spec fn stores<S>(d:Stored<S>,x:State<S>,r:Replica,w:Op) -> bool {
    d(r,(x.cfg.private)(at(r)),(x.cfg.net.locals)(r),w)
}

pub open spec fn cut<S>(m:Program<S>) -> State<S> {
    read::next(m,wc::start(m),Action::CrashR3)
}

pub open spec fn journal_boundary<S>(m:Program<S>,d:Stored<S>) -> bool {
    forall|r:Replica,w:Op| order::weak(w) ==> (#[trigger] stores(d,wc::start(m),r,w)
        == wc::journal_copies(crate::guarded_history::weak_end(),w).contains(r))
}

// The stop occurs immediately after the isolated RMWs. Their journals
// certify no earlier majority, and R3 stores neither command at the stop.
// It cannot contribute a new copy while stopped. Only R1/R2 can hold G here.
pub open spec fn holders<S>(d:Stored<S>,x:State<S>,w:Op) -> Set<Replica> {
    live_pair().filter(|r:Replica| stores(d,x,r,w))
}

pub open spec fn both<S>(d:Stored<S>,x:State<S>,w:Op) -> bool {
    stores(d,x,Replica::R1,w) && stores(d,x,Replica::R2,w)
}

pub open spec fn majority_gain<S>(d:Stored<S>) -> wait::Relation<State<S>,Event> {
    |x:State<S>,_a:Event,y:State<S>| exists|w:Op| order::weak(w)
        && !both(d,x,w) && #[trigger] both(d,y,w)
}

pub open spec fn restoration<S>() -> wait::Relation<State<S>,Event> {
    |x:State<S>,a:Event,y:State<S>| exists|r:Replica| live_pair().contains(r)
        && #[trigger] supplied_genesis(x.cfg,a,y.cfg,r)
}

proof fn restore_is_weak_input<S>(x:State<S>,a:Event,y:State<S>)
    requires restoration()(x,a,y),
    ensures app::weak_replica_step()(x,a,y),
{
    let r=choose|r:Replica| live_pair().contains(r) && #[trigger] supplied_genesis(x.cfg,a,y.cfg,r);
    assert(process_step(x.cfg.net,a).actor==at(r));
}

pub open spec fn required_effect<S>(d:Stored<S>) -> wait::Relation<State<S>,Event> {
    |x:State<S>,a:Event,y:State<S>| majority_gain(d)(x,a,y) || restoration()(x,a,y)
}

// The interface's marked weak-replica work together with any new durable
// weak-command holder. No quorum threshold, repair value or reply appears.
pub open spec fn audited_replica_work<S>(d:Stored<S>) -> wait::Relation<State<S>,Event> {
    |x:State<S>,a:Event,y:State<S>| app::weak_replica_step()(x,a,y)
        || exists|w:Op,r:Replica| order::weak(w) && !stores(d,x,r,w) && #[trigger] stores(d,y,r,w)
}

proof fn covers_required_change<S>(d:Stored<S>,x:State<S>,a:Event,y:State<S>)
    requires required_effect(d)(x,a,y),
    ensures audited_replica_work(d)(x,a,y),
{
    if restoration()(x,a,y) {
        restore_is_weak_input(x,a,y);
    } else {
        let w=choose|w:Op| order::weak(w) && !both(d,x,w) && #[trigger] both(d,y,w);
        let r=if !stores(d,x,Replica::R1,w) {Replica::R1} else {Replica::R2};
        assert(!stores(d,x,r,w) && stores(d,y,r,w));
    }
}

pub open spec fn reply<S>(first:spec_fn(S)->int,x:State<S>) -> int {
    first((x.cfg.private)(Process::FirstClient))
}

pub open spec fn writer(v:int) -> Op { if v==2 {Op::W1} else {Op::W2} }
pub open spec fn other_origin(w:Op) -> Replica { if w==Op::W1 {Replica::R2} else {Replica::R1} }

pub open spec fn acquire<S>(d:Stored<S>,w:Op,x:State<S>,a:Event,y:State<S>) -> bool {
    let r=other_origin(w);
    process_step(x.cfg.net,a).actor==at(r) && !stores(d,x,r,w) && stores(d,y,r,w)
}

// Restrict all-execution H and the paper's G deadline to native first
// publications in this one reference. Credit a majority at any time up
// to the response, even when a later transition loses it.
pub open spec fn deadline<S>(d:Stored<S>,t:Service<S>,word:Seq<Op>) -> bool {
    forall|w:Op| order::reads_from(word,Op::SR1,w) ==> exists|i:int| 0<=i<t.states.len()
        && #[trigger] crate::guarantee::ordered_on_majority(word,holders(d,t.states[i],w),w)
}

pub open spec fn history_at_return<S>(first:spec_fn(S)->int,d:Stored<S>,t:Service<S>,h:RecoveredOrder) -> bool {
    order::legal_first(h,reply(first,t.states.last())) && deadline(d,t,h.ops)
}

pub open spec fn first_histories<S>(m:Program<S>,first:spec_fn(S)->int,d:Stored<S>) -> bool {
    forall|t:Service<S>| #[trigger] maj::first_invocation_interval(m,t,live_pair()) && t.states[0]==cut(m)
        && !t.states.last().cfg.net.second_started ==> exists|h:RecoveredOrder| #[trigger] history_at_return(first,d,t,h)
}

// Recoverability may have been established and lost before the read. Count
// all three journals before the stop and retain R3's last live storage
// afterwards. A crash-handler notification cannot create a replica at R3.
pub open spec fn after_stop_holders<S>(d:Stored<S>,before:State<S>,x:State<S>,w:Op) -> Set<Replica> {
    all_replicas().filter(|r:Replica| if r==Replica::R3 {stores(d,before,r,w)} else {stores(d,x,r,w)})
}

pub open spec fn full_deadline<S>(m:Program<S>,d:Stored<S>,past:Seq<crate::weak_round::World>,t:Service<S>,word:Seq<Op>) -> bool {
    forall|w:Op| order::reads_from(word,Op::SR1,w) ==> (
        (exists|i:int| 0<=i<past.len()
            && #[trigger] crate::guarantee::ordered_on_majority(word,wc::journal_copies(past[i],w),w))
        || exists|i:int| 0<=i<t.states.len()
            && #[trigger] crate::guarantee::ordered_on_majority(word,after_stop_holders(d,wc::start(m),t.states[i],w),w))
}

proof fn credit_after_isolated_writes<S>(m:Program<S>,d:Stored<S>,past:Seq<crate::weak_round::World>,t:Service<S>,word:Seq<Op>)
    requires journal_boundary(m,d),forall|j:int| 0<=j<past.len() ==> crate::weak_round::origin_only(#[trigger] past[j]),
        full_deadline(m,d,past,t,word),
    ensures deadline(d,t,word),
{
    let base=wc::start(m);wc::prior_to_observation(alpha(Notice::Replication));
    assert forall|w:Op| order::reads_from(word,Op::SR1,w) implies exists|i:int| 0<=i<t.states.len()
        && #[trigger] crate::guarantee::ordered_on_majority(word,holders(d,t.states[i],w),w) by {
        if exists|i:int| 0<=i<past.len() && #[trigger] crate::guarantee::ordered_on_majority(word,wc::journal_copies(past[i],w),w) {
            let i=choose|i:int| 0<=i<past.len() && #[trigger] crate::guarantee::ordered_on_majority(word,wc::journal_copies(past[i],w),w);
            let sites=wc::journal_copies(past[i],w);let req=crate::weak_round::request(w);
            assert forall|r:Replica| #[trigger] sites.contains(r) implies r==req.site by {
                assert((past[i].journal)(r).contains_key(req.id));
            }
            assert(sites =~= Set::empty() || sites =~= set![req.site]);assert(set![req.site].len()==1);
        }
        let i=choose|i:int| 0<=i<t.states.len()
            && #[trigger] crate::guarantee::ordered_on_majority(word,after_stop_holders(d,base,t.states[i],w),w);
        assert(!stores(d,base,Replica::R3,w));
        assert(after_stop_holders(d,base,t.states[i],w) =~= holders(d,t.states[i],w));
    }
}

// Project the actual total history when H is stated on a complete execution.
// The physical observations credited by G end at SR1, even in this projection.
pub proof fn completed_history_supplies_first<S>(m:Program<S>,first:spec_fn(S)->int,d:Stored<S>,
    past:Seq<crate::weak_round::World>,t:Service<S>,h:RecoveredOrder,second:int)
    -> (prefix:RecoveredOrder)
    requires t.states.len()>0,crate::legal(h.ops,h.states,reply(first,t.states.last()),second),
        journal_boundary(m,d),forall|j:int| 0<=j<past.len() ==> crate::weak_round::origin_only(#[trigger] past[j]),
        full_deadline(m,d,past,t,h.ops),
    ensures history_at_return(first,d,t,prefix),prefix.ops==h.ops.take(prefix.ops.len() as int),prefix.ops.last()==Op::SR1,
{
    credit_after_isolated_writes(m,d,past,t,h.ops);
    let (i,j)=choose|i:int,j:int| 0<=i<j<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 && #[trigger] h.ops[j]==Op::SR2;
    let g=RecoveredOrder {ops:h.ops.take(i+1),states:h.states.take(i+2)};
    assert forall|l:int| 0<=l<g.ops.len() implies {
        let k=#[trigger] g.ops[l];g.states[l+1]==crate::next(k,g.states[l]) && (order::weak(k) ==> g.states[l]==1)
    } by {assert(g.ops[l]==h.ops[l]);}
    assert(!g.ops.contains(Op::SR2)) by {
        if g.ops.contains(Op::SR2) {let l=choose|l:int| 0<=l<g.ops.len() && #[trigger] g.ops[l]==Op::SR2;assert(h.ops[l]==h.ops[j]);}
    }
    assert(g.ops[i]==Op::SR1);assert(g.ops.contains(Op::SR1));assert(order::legal_first(g,reply(first,t.states.last())));
    assert forall|w:Op| order::reads_from(g.ops,Op::SR1,w) implies exists|k:int| 0<=k<t.states.len()
        && #[trigger] crate::guarantee::ordered_on_majority(g.ops,holders(d,t.states[k],w),w) by {
        let (a,b)=choose|a:int,b:int| 0<=a<b<g.ops.len() && #[trigger] g.ops[a]==w && #[trigger] g.ops[b]==Op::SR1
            && forall|l:int| a<l<b ==> !order::weak(#[trigger] g.ops[l]);
        assert forall|l:int| a<l<b implies !order::weak(#[trigger] h.ops[l]) by {assert(h.ops[l]==g.ops[l]);}
        assert(order::reads_from(h.ops,Op::SR1,w));
        let k=choose|k:int| 0<=k<t.states.len() && #[trigger] crate::guarantee::ordered_on_majority(h.ops,holders(d,t.states[k],w),w);
        assert(g.ops.contains(w));assert(crate::guarantee::ordered_on_majority(g.ops,holders(d,t.states[k],w),w));
    }
    g
}

proof fn history_source<S>(first:spec_fn(S)->int,d:Stored<S>,t:Service<S>,h:RecoveredOrder)
    -> (i:int)
    requires history_at_return(first,d,t,h),reply(first,t.states.last())!=1,
    ensures 0<=i<t.states.len(), ({
        let v=reply(first,t.states.last()); (v==2 || v==5) && both(d,t.states[i],writer(v))
    }),
{
    let v=reply(first,t.states.last()); let j=choose|j:int| 0<=j<h.ops.len() && #[trigger] h.ops[j]==Op::SR1;
    crate::irrevocable_order::writer_before(h,j as nat);
    let b=if v==2 {beta(Notice::Replication)} else {alpha(Notice::Replication)};
    assert(v==first_value(b)); order::exact_first_order(b,h);
    let w=writer(v);
    assert(order::reads_from(h.ops,Op::SR1,w)) by {assert(h.ops[0]==w && h.ops[1]==Op::SR1);}
    let i=choose|i:int| 0<=i<t.states.len() && #[trigger] crate::guarantee::ordered_on_majority(h.ops,holders(d,t.states[i],w),w);
    let set=holders(d,t.states[i],w);
    if !stores(d,t.states[i],Replica::R1,w) {
        assert(set.subset_of(set![Replica::R2])); assert(set =~= Set::empty() || set =~= set![Replica::R2]);
    }
    if !stores(d,t.states[i],Replica::R2,w) {
        assert(set.subset_of(set![Replica::R1])); assert(set =~= Set::empty() || set =~= set![Replica::R1]);
    }
    i
}

proof fn at_cut<S>(m:Program<S>,d:Stored<S>)
    requires journal_boundary(m,d),
    ensures ({
        let base=wc::start(m); let x=cut(m);
        asm::prefix(m,base,seq![Action::CrashR3],true) && asm::drive(m,base,seq![Action::CrashR3])==x
            && svc::reachable(m,base,x) && maj::sole(x.cfg.net,live_pair()) && survivor(x.cfg.net)==(2int,5int)
            && (forall|w:Op| order::weak(w) ==> !#[trigger] stores(d,x,other_origin(w),w))
    }),
{
    wc::prior_to_observation(alpha(Notice::Replication)); crate::isolated_rmws();
    let base=wc::start(m);let x=cut(m);let crash=seq![Action::CrashR3];
    reveal_with_fuel(asm::drive,2);reveal_with_fuel(asm::prefix,2);
    assert(svc::reaches(m,base,(crash,None,seq![]),x));
    assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
    assert forall|w:Op| order::weak(w) implies !#[trigger] stores(d,x,other_origin(w),w) by {
        assert(!stores(d,base,other_origin(w),w));
    }
}

pub open spec fn submitted<S>(m:Program<S>,s:Seq<Event>) -> bool {
    let x=cut(m);let y=asm::drive(m,x,s);
    svc::fan(m,x,s) && s.len()>0 && y.first_requested==all_replicas() && mail::submitted(y) && !mail::posted(m)(y)
}

// If the requester publishes during its own sends, no replica could yet
// have acquired a copy. A then samples 2 or 5, already contradicting G.
proof fn submit<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,d:Stored<S>,plan:svc::Requests) -> (s:Seq<Event>)
    requires crate::prepared_hot::fresh_caller(p,plan), ({
        let m=net::implementation(k,p); journal_boundary(m,d) && first_histories(m,first,d)
            && maj::first_invocation_sampling(m,first,cut(m))
    }),
    ensures submitted(net::implementation(k,p),s),svc::contents(k,s)==plan,
{
    let m=net::implementation(k,p);let x=cut(m);at_cut(m,d);
    let s=svc::emit(p,k,x,x,plan);let h=svc::path(m,x,s);let y=asm::drive(m,x,s);
    svc::endpoints(m,x,s);svc::fan_at(m,x,s,s.len());svc::fan_path(m,x,s);
    if mail::posted(m)(y) {
        assert(s.len()>0);svc::fan_at(m,x,s,0);
        assert(maj::fresh_invocation(maj::Caller::First,x,s[0]));
        assert(maj::first_invocation_interval(m,h,live_pair()));
        assert(nb::within(read::prefix_step(m),read::at_state(x),x,0));
        assert(maj::held(h.states,live_pair(),reply(first,y)));
        let (i,r)=choose|i:int,r:Replica| 0<=i<h.states.len() && live_pair().contains(r)
            && #[trigger] (h.states[i].cfg.net.locals)(r)==reply(first,y);
        svc::fan_at(m,x,s,i as nat); assert(reply(first,y)!=1);
        let word=choose|word:RecoveredOrder| #[trigger] history_at_return(first,d,h,word);
        let j=history_source(first,d,h,word);svc::fan_at(m,x,s,j as nat);
        let w=writer(reply(first,y));assert(!stores(d,x,other_origin(w),w));
        assert(!stores(d,h.states[j],other_origin(w),w));
    }
    assert(!mail::posted(m)(y));
    assert(y.first_requested =~= all_replicas());
    assert(y.first_requested.contains(Replica::R1) && y.first_requested.contains(Replica::R2));
    assert(live(y.cfg.net,at(Replica::R1)) && live(y.cfg.net,at(Replica::R2)));
    assert(mail::submitted(y));
    if s.len()==0 {assert(y==x);}
    s
}

proof fn still_available<S>(m:Program<S>,t:Service<S>,i:nat)
    requires t.states.len()==t.actions.len()+1,wait::valid_edges(mail::active_step(m),t),wait::pending_before(mail::posted(m),t),
        i<t.states.len(),
    ensures ({
        let n=t.states[0].cfg.net;let u=t.states[i as int].cfg.net;
        u.r3_crashed==n.r3_crashed && u.unavailable==n.unavailable && u.second_started==n.second_started
            && u.first_stopped==n.first_stopped
    }),
    decreases i,
{
    if i>0 {let j=i-1;still_available(m,t,j as nat);assert(mail::active_step(m)(t.states[j],t.actions[j],t.states[i as int]));}
}

spec fn join<S>(h:Service<S>,t:Service<S>) -> Service<S> {
    wait::Path {states:h.states.drop_last()+t.states,actions:h.actions+t.actions}
}

proof fn whole_invocation<S>(m:Program<S>,s:Seq<Event>,t:Service<S>)
    requires submitted(m,s),wait::first_return(mail::active_step(m),mail::posted(m),asm::drive(m,cut(m),s),t),
        maj::sole(cut(m).cfg.net,live_pair()),
    ensures ({
        let h=svc::path(m,cut(m),s);let q=join(h,t);
        maj::first_invocation_interval(m,q,live_pair()) && q.states[0]==cut(m)
            && q.states.last()==t.states.last() && !q.states.last().cfg.net.second_started
    }),
{
    let x=cut(m);let h=svc::path(m,x,s);let q=join(h,t);let n=s.len();
    svc::endpoints(m,x,s);svc::fan_path(m,x,s);svc::fan_at(m,x,s,0);svc::fan_at(m,x,s,n);
    still_available(m,t,t.actions.len());assert(maj::fresh_invocation(maj::Caller::First,x,s[0]));
    assert forall|i:int| 0<=i<q.actions.len() implies
        read::prefix_step(m)(q.states[i],#[trigger] q.actions[i],q.states[i+1]) && !mail::posted(m)(q.states[i]) by {
        if i<n {assert(read::prefix_step(m)(h.states[i],s[i],h.states[i+1]));}
        else {let j=i-n;assert(mail::active_step(m)(t.states[j],t.actions[j],t.states[j+1]));assert(read::initial_send(t.states[j],t.actions[j]));}
    }
    assert(wait::valid_edges(read::prefix_step(m),q));assert(wait::pending_before(mail::posted(m),q));
}

// A restoration by delivery consumes a matching packet actually issued
// during this service. The two RMWs installed 2 and 5.
pub open spec fn initial_installation<S>(t:Service<S>,j:int,r:Replica) -> bool {
    0<=j<t.actions.len() && live_pair().contains(r)
        && supplied_genesis(t.states[j].cfg,t.actions[j],t.states[j+1].cfg,r)
        && match t.actions[j] {
            Action::Local(_,_) => true,
            Action::Deliver(h) => {
                let pkt=t.states[j].cfg.net.pending[h];
                pkt.from is At && live_pair().contains(pkt.from->At_0)
                    && exists|i:int| 0<=i<j && #[trigger] t.actions[i]==Action::Send(h,pkt)
            },
            _ => false,
        }
}

proof fn restoration_source<S>(m:Program<S>,t:Service<S>,j:int,r:Replica)
    requires 0<=j<t.actions.len(),live_pair().contains(r),supplied_genesis(t.states[j].cfg,t.actions[j],t.states[j+1].cfg,r),
        wait::first_return(mail::active_step(m),mail::posted(m),t.states[0],t),t.states[0].cfg.net.r3_crashed,
        fork::weak_packets(t.states[0]).is_empty(),
    ensures initial_installation(t,j,r),
{
    if let Action::Deliver(h)=t.actions[j] {
        let nets=t.states.map_values(|x:State<S>|x.cfg.net);let pkt=t.states[j].cfg.net.pending[h];
        let cell_update=|v:int,w:Wire|cell(v,w);
        assert forall|i:int| 0<=i<t.actions.len() implies {
            let a=#[trigger] t.actions[i]; enabled(nets[i],a) && nets[i+1]==advance(cell_update,nets[i],a)
        } by {assert(mail::active_step(m)(t.states[i],t.actions[i],t.states[i+1]));}
        assert(trace(cell_update,nets,t.actions));
        pending_packet_has_live_origin(cell_update,nets,t.actions,j,h);
        if nets[0].pending.get(h)==Some(pkt) {assert(fork::weak_packets(t.states[0]).contains_key(h));}
        let i=choose|i:int| 0<=i<j && #[trigger] t.actions[i]==Action::Send(h,pkt) && live(nets[i],pkt.from);
        assert(mail::active_step(m)(t.states[i],t.actions[i],t.states[i+1]));still_available(m,t,i as nat);
    }
}

pub open spec fn consequence<S>(d:Stored<S>,first:spec_fn(S)->int,t:Service<S>) -> bool {
    let v=reply(first,t.states.last());let w=writer(v);
    if v==1 {
        wait::uses(t,restoration()) && exists|j:int,r:Replica| #[trigger] initial_installation(t,j,r)
    } else {
        (v==2 || v==5) && wait::uses(t,majority_gain(d))
            && (exists|i:int| 0<=i<t.actions.len() && !both(d,#[trigger] t.states[i],w) && both(d,t.states[i+1],w))
            && exists|j:int| 0<=j<t.actions.len() && #[trigger] acquire(d,w,t.states[j],t.actions[j],t.states[j+1])
    }
}

proof fn classify<S>(m:Program<S>,first:spec_fn(S)->int,d:Stored<S>,s:Seq<Event>,t:Service<S>)
    requires journal_boundary(m,d),first_histories(m,first,d),maj::first_invocation_sampling(m,first,cut(m)),
        submitted(m,s),wait::first_return(mail::active_step(m),mail::posted(m),asm::drive(m,cut(m),s),t),
    ensures consequence(d,first,t),
{
    let x=cut(m);at_cut(m,d);let h=svc::path(m,x,s);let q=join(h,t);let n=s.len();let v=reply(first,t.states.last());
    whole_invocation(m,s,t);svc::endpoints(m,x,s);svc::fan_at(m,x,s,n);
    assert(nb::within(read::prefix_step(m),read::at_state(x),x,0));
    if v==1 {
        assert(maj::held(q.states,live_pair(),v));
        let (i,r)=choose|i:int,r:Replica| 0<=i<q.states.len() && live_pair().contains(r) && #[trigger] (q.states[i].cfg.net.locals)(r)==v;
        if i<n {svc::fan_at(m,x,s,i as nat);assert((h.states[i].cfg.net.locals)(r)!=1);}
        let pred=|z:State<S>| (z.cfg.net.locals)(r)==1;
        let j=crate::mixed_origin_wait::crossing(pred,t.states,(i-n) as nat);
        let z=t.states[j];let u=t.states[j+1];let a=t.actions[j];assert(mail::active_step(m)(z,a,u));
        assert(local_input(z.cfg.net,a,r)==Some(Wire::Copy(1)));assert(supplied_genesis(z.cfg,a,u.cfg,r));
        assert(restoration()(z,a,u));
        assert(fork::weak_packets(x) =~= Map::empty());restoration_source(m,t,j,r);
    } else {
        let word=choose|word:RecoveredOrder| #[trigger] history_at_return(first,d,q,word);
        let i=history_source(first,d,q,word);let w=writer(v);let r=other_origin(w);
        assert(order::weak(w));assert(!stores(d,x,r,w));
        if i<n {svc::fan_at(m,x,s,i as nat);assert(!stores(d,h.states[i],r,w));}
        let k=(i-n) as nat;
        assert(!stores(d,t.states[0],r,w));assert(stores(d,t.states[k as int],r,w));
        let j=crate::mixed_origin_wait::crossing(|z:State<S>|stores(d,z,r,w),t.states,k);
        let z=t.states[j];let u=t.states[j+1];let a=t.actions[j];assert(mail::active_step(m)(z,a,u));
        if process_step(z.cfg.net,a).actor!=at(r) {assert(local_input(z.cfg.net,a,r).is_none());assert(!stores(d,u,r,w));}
        assert(acquire(d,w,z,a,u));
        let l=crate::mixed_origin_wait::crossing(|z:State<S>|both(d,z,w),t.states,k);
        assert(majority_gain(d)(t.states[l],t.actions[l],t.states[l+1]));
    }
}

pub open spec fn classified<S>(m:Program<S>,first:spec_fn(S)->int,d:Stored<S>,s:Seq<Event>) -> bool {
    forall|t:Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),asm::drive(m,cut(m),s),t)
        ==> consequence(d,first,t)
}

// Both service claims are proved for the actual program. The all-executions
// assumptions are tested at a single reached prefix of the original workload.
pub proof fn original_cut_service_requirement<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    d:Stored<S>,plan:svc::Requests,run:crate::fair_read::Runnable) -> (out:(Seq<Event>,Service<S>))
    requires crate::prepared_hot::fresh_caller(p,plan), ({
        let m=net::implementation(k,p);
        journal_boundary(m,d) && first_histories(m,first,d) && svc::invocation_laws(m,wc::start(m),first,res,run)
    }),
    ensures ({
        let m=net::implementation(k,p);let base=wc::start(m);let x=cut(m);let (s,t)=out;let y=asm::drive(m,x,s);
        let step=mail::active_step(m);let done=mail::posted(m);let a=(seq![Action::CrashR3]+s)+t.actions;
        submitted(m,s) && svc::contents(k,s)==plan && svc::reachable(m,base,y) && classified(m,first,d,s)
            && wait::needs_class(step,done,y,required_effect(d)) && wait::needs_class(step,done,y,audited_replica_work(d))
            && wait::first_return(step,done,y,t) && !wait::uses(t,app::weak_replica_step()) && consequence(d,first,t)
            && (reply(first,t.states.last())==2 || reply(first,t.states.last())==5)
            && (forall|i:int| 0<=i<t.states.len() ==> {
                let n=(#[trigger] t.states[i]).cfg.net;
                n.r3_crashed && (n.locals)(Replica::R3)==1 && survivor(n)==(2int,5int)
            })
            && asm::prefix(m,base,a,true) && asm::drive(m,base,a)==t.states.last()
            && net::trace(p,net::snapshot(k,base),net::turns(k,a),true)
    }),
{
    let m=net::implementation(k,p);let base=wc::start(m);let x=cut(m);at_cut(m,d);
    assert(maj::first_invocation_sampling(m,first,x));let s=submit(p,k,first,d,plan);let y=asm::drive(m,x,s);
    let crash=seq![Action::CrashR3];svc::fan_prefix(m,x,s);asm::prefix_concat(m,base,crash,s,true);
    assert(svc::reaches(m,base,(crash+s,None,seq![]),y));assert(svc::reachable(m,base,y));svc::fan_at(m,x,s,s.len());svc::endpoints(m,x,s);
    let step=mail::active_step(m);let done=mail::posted(m);mail::fair_first_service(m,run,read::at_state(y),y);
    nb::first_response_iff(step,done,y);assert(wait::can_finish(step,done,y));
    assert(!wait::needs_class(step,done,y,app::weak_replica_step()));
    let t=choose|t:Service<S>| #[trigger] wait::first_return(step,done,y,t) && !wait::uses(t,app::weak_replica_step());
    assert forall|u:Service<S>| #[trigger] wait::first_return(step,done,y,u) implies consequence(d,first,u) by {classify(m,first,d,s,u);}
    assert forall|u:Service<S>| #[trigger] wait::first_return(step,done,y,u) implies
        wait::uses(u,required_effect(d)) && wait::uses(u,audited_replica_work(d)) by {
        let e=if reply(first,u.states.last())==1 {restoration()} else {majority_gain(d)};
        assert(wait::uses(u,e));let j=choose|j:int| 0<=j<u.actions.len() && e(u.states[j],#[trigger] u.actions[j],u.states[j+1]);
        assert(required_effect(d)(u.states[j],u.actions[j],u.states[j+1]));
        covers_required_change(d,u.states[j],u.actions[j],u.states[j+1]);
    }
    crate::isolated_rmws();
    assert forall|i:int| 0<=i<t.states.len() implies {
        let n=(#[trigger] t.states[i]).cfg.net;
        n.r3_crashed && (n.locals)(Replica::R3)==1 && survivor(n)==(2int,5int)
    } by {app::cells_at(m,t,i as nat);still_available(m,t,i as nat);}
    if reply(first,t.states.last())==1 {
        let j=choose|j:int| 0<=j<t.actions.len() && restoration()(t.states[j],#[trigger] t.actions[j],t.states[j+1]);
        restore_is_weak_input(t.states[j],t.actions[j],t.states[j+1]);
    }
    crate::first_splice::recorded(m,t,0);asm::native_prefix(m,y,crate::first_splice::record(t,0),true);
    assert(asm::actions(crate::first_splice::record(t,0)) =~= t.actions);
    asm::prefix_concat(m,base,crash+s,t.actions,true);
    net::project_prefix(p,k,base,(crash+s)+t.actions,true,res);(s,t)
}

// No-await for an independently identified semantic class that includes
// actual majority gains forces a genuine initial-value installation outside
// that class. If the class also covers those installations the cut is impossible.
pub proof fn service_without_new_majority_must_restore<S>(m:Program<S>,first:spec_fn(S)->int,d:Stored<S>,s:Seq<Event>,
    effect:wait::Relation<State<S>,Event>) -> (t:Service<S>)
    requires classified(m,first,d,s), ({
        let y=asm::drive(m,cut(m),s);let step=mail::active_step(m);let done=mail::posted(m);
        wait::can_finish(step,done,y) && !wait::needs_class(step,done,y,effect)
    }),
        forall|x:State<S>,a:Event,y:State<S>| mail::active_step(m)(x,a,y) && #[trigger] majority_gain(d)(x,a,y) ==> effect(x,a,y),
    ensures wait::first_return(mail::active_step(m),mail::posted(m),asm::drive(m,cut(m),s),t),
        !wait::uses(t,effect),!wait::uses(t,majority_gain(d)),reply(first,t.states.last())==1,
        exists|j:int,r:Replica| #[trigger] initial_installation(t,j,r) && !effect(t.states[j],t.actions[j],t.states[j+1]),
{
    let y=asm::drive(m,cut(m),s);let step=mail::active_step(m);let done=mail::posted(m);
    let t=choose|t:Service<S>| #[trigger] wait::first_return(step,done,y,t) && !wait::uses(t,effect);
    if wait::uses(t,majority_gain(d)) {
        let j=choose|j:int| 0<=j<t.actions.len() && majority_gain(d)(t.states[j],#[trigger] t.actions[j],t.states[j+1]);
        assert(step(t.states[j],t.actions[j],t.states[j+1]));
    }
    assert(consequence(d,first,t));t
}

// The reachability test closes at the common cut if one semantic no-await
// rule covers both real replication gains and these particular installations.
// Its effect classification mentions no history, response or desired fork.
pub proof fn original_cut_excluded_if_covered<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    d:Stored<S>,plan:svc::Requests,run:crate::fair_read::Runnable,effect:wait::Relation<State<S>,Event>)
    requires crate::prepared_hot::fresh_caller(p,plan), ({
        let m=net::implementation(k,p);let base=wc::start(m);
        journal_boundary(m,d) && first_histories(m,first,d) && svc::invocation_laws(m,base,first,res,run)
            && (forall|x:State<S>| #[trigger] svc::reachable(m,base,x) && mail::submitted(x) && !mail::posted(m)(x)
                && !x.cfg.net.second_started ==> !wait::needs_class(mail::active_step(m),mail::posted(m),x,effect))
            && forall|x:State<S>,a:Event,y:State<S>| mail::active_step(m)(x,a,y)
                && #[trigger] required_effect(d)(x,a,y) ==> effect(x,a,y)
    }),
    ensures false,
{
    let m=net::implementation(k,p);let base=wc::start(m);
    let (s,_) = original_cut_service_requirement(p,k,first,res,d,plan,run);
    let x=cut(m);let y=asm::drive(m,x,s);svc::fan_at(m,x,s,s.len());svc::endpoints(m,x,s);
    let step=mail::active_step(m);let done=mail::posted(m);
    assert(!wait::needs_class(step,done,y,effect));
    let t=choose|t:Service<S>| #[trigger] wait::first_return(step,done,y,t) && !wait::uses(t,effect);
    assert(wait::uses(t,required_effect(d)));
    let j=choose|j:int| 0<=j<t.actions.len() && required_effect(d)(t.states[j],#[trigger] t.actions[j],t.states[j+1]);
    assert(step(t.states[j],t.actions[j],t.states[j+1]));
}

}
