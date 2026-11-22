// One native preparation, two real client completions, one R3 failure.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::*};
use crate::coupled_reads as calls;
use crate::coupled_traffic::{self as traffic,Encoding};
use crate::fair_read as fair;
use crate::first_assembly::{self as asm,Lanes,Service};
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_schedule::{self as first,reference};
use crate::first_service_loss as loss;
use crate::first_splice::{self as tape,Observation,Tape};
use crate::fork_delivery as wire;
use crate::hybrid_fork as fork;
use crate::hybrid_majority as model;
use crate::hybrid_transparency as trans;
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::sr1_contract as rpc;
use crate::sr1_majorities as maj;
use crate::sr1_ordinary as ordinary;

verus! {

pub open spec fn root<S>(m:Program<S>,l:Lanes,b:Fork) -> State<S> {asm::root(m,l,Some(b))}
pub open spec fn prepared<S>(m:Program<S>,l:Lanes,b:Fork,t:Tape) -> State<S> {tape::after(m,root(m,l,b),t)}
pub open spec fn usable<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit,z:State<S>,p:Service<S>) -> bool {
    ordinary::weak_free_return(m,b,audit,p) && loss::stable(b,p) && calls::sent_to_caller(z,calls::caller(p))
}
pub open spec fn input_obstruction<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit,z:State<S>) -> bool {
    !(exists|p:Service<S>| #[trigger] usable(m,b,audit,z,p))
    && (exists|p:Service<S>| #[trigger] ordinary::weak_free_return(m,b,audit,p)
        && ((exists|i:int| 0<=i<p.actions.len() && cause::changes_sample(b,#[trigger] p.states[i],p.states[i+1]))
            || (exists|j:int| 0<=j<calls::caller(p).len() && {let e=#[trigger] calls::caller(p)[j];
                e.action is Deliver && e.incoming.is_some() && z.cfg.net.pending.get(e.action->Deliver_0)!=e.incoming})))
}
proof fn select_caller<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,z:State<S>,audit:trans::PacketAudit,
    who:fork::Issuer,used:rpc::Ledger<S>,scope:nb::Region<State<S>>,run:fair::Runnable) -> (p:Service<S>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),trans::no_first_wait(m,b,audit),
        model::eventual(m,res,reference(m,b,0),run),mail::fair_opportunity(m,run,reference(m,b,5)),
        rpc::registered(m,b,scope,who,used),
    ensures cause::returning(m,b,p),fork::wire_route(b,p,who,rpc::replies()),
        usable(m,b,audit,z,p) || input_obstruction(m,b,audit,z),
{
    let a=ordinary::service_with_ordinary_traffic(m,b,res,run,audit);
    let p=if exists|p:Service<S>| #[trigger] usable(m,b,audit,z,p) {choose|p:Service<S>| #[trigger] usable(m,b,audit,z,p)} else {a};
    ordinary::ordinary_edges(m,b,audit,p);
    rpc::allocator_gives_native(m,b,p,scope,who,used);rpc::solicited_majority_route(m,b,p,scope);
    if !usable(m,b,audit,z,p) {
        if loss::stable(b,p) {
            let t=calls::caller(p);let j=choose|j:int| 0<=j<t.len() && (#[trigger] t[j]).action is Deliver
                && z.cfg.net.pending.get(t[j].action->Deliver_0)!=t[j].incoming;
            let c=Process::FirstClient;let src=tape::record(p,0);tape::picked(src,c,true,j);
            let i=choose|i:int| 0<=i<src.len() && src[i]==t[j];
            assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));assert(t[j].incoming.is_some());
        }
        assert(input_obstruction(m,b,audit,z));
    }
    p
}

pub open spec fn answered(t:Tape,r:Replica) -> bool {
    exists|i:int,j:int| 0<=i<j<t.len() && cause::intake_at(#[trigger] t[i],r)
        && cause::answer_at(#[trigger] t[j],r,rpc::replies())
}
pub open spec fn respondents(t:Tape) -> bool {forall|r:Replica| #[trigger] answered(t,r)}
pub open spec fn keeps_reports(f:Encoding) -> bool {
    forall|q:Packet<Wire>| first_reply(q) ==> first_reply(#[trigger] traffic::image(f,q))
}
// Only R3's authenticated SR1 reply to C1 is resampled. Every survivor
// receives the same ordinary message, even if its handler logs all bytes.
pub proof fn common_peer_inputs<S>(m:Program<S>,v:int)
    ensures keeps_reports(traffic::sampled_reply(v)),traffic::recipient_use(m,traffic::sampled_reply(v)),
{
    let f=traffic::sampled_reply(v);
    assert forall|s:S,e:Observation| survivor_actor(e.actor) && e.action is Deliver && e.incoming.is_some()
        && e.incoming.unwrap().to==e.actor && #[trigger] (m.accept)(s,e)
        implies (m.accept)(s,traffic::observation(f,e,0)) && (m.update)(s,traffic::observation(f,e,0))==(m.update)(s,e)
        by {assert(traffic::observation(f,e,0)==e);}
}
proof fn copy_respondents(f:Encoding,t:Tape)
    requires respondents(t),keeps_reports(f),
    ensures respondents(traffic::translated(f,t,2)),
{
    let u=traffic::translated(f,t,2);
    assert forall|r:Replica| #[trigger] answered(u,r) by {
        assert(answered(t,r));
        let (i,j)=choose|i:int,j:int| 0<=i<j<t.len() && cause::intake_at(#[trigger] t[i],r)
            && cause::answer_at(#[trigger] t[j],r,rpc::replies());
        assert(cause::intake_at(u[i],r) && cause::answer_at(u[j],r,rpc::replies()));
    }
}
pub(crate) proof fn prepared_frame<S>(m:Program<S>,l:Lanes,b:Fork,t:Tape)
    requires asm::lanes_ok(l),tape::plays(m,root(m,l,b),t),traffic::fitted(t,|_e:Observation|true),
    ensures pair::before_issue(m,prepared(m,l,b,t),l),pair::c1_protected(prepared(m,l,b,t)),
        (prepared(m,l,b,t).cfg.private)(Process::FirstClient)==(reference(m,b,5).cfg.private)(Process::FirstClient),
{
    let x=root(m,l,b);let r=ISet::new(|p:Process|p is At);let ids=ISet::new(|i:nat|i>2 && i!=11 && i!=12);
    assert(tape::supports(t,r,ids)) by {
        assert forall|i:int| 0<=i<t.len() implies {let e=#[trigger] t[i];r.contains(e.actor)
            && (tape::slot(e.action).is_some() ==> ids.contains(tape::slot(e.action).unwrap()))} by {assert(traffic::preparation_input(t[i]));}
    }
    tape::frame(m,x,t,r,ids);pair::keep_protection(m,x,t);
    let c=Process::FirstClient;let other=Process::SecondClient;
    assert(r.complement().contains(other) && r.complement().contains(c));
    assert(ids.complement().contains(11) && ids.complement().contains(12));
    maj::local_at(m,b,c,5);assert(maj::count(b,5)==5);
    assert forall|i:int| 0<=i<5 implies (#[trigger] checkpoint_observations(b)[i]).actor!=other by {prefix_index(i);}
    memory_during_quiescence(m,checkpoint_observations(b),other,0,5);
    let z=prepared(m,l,b,t);
    assert((x.cfg.private)(c)==(z.cfg.private)(c) && (x.cfg.private)(other)==(z.cfg.private)(other));
    assert((x.cfg.private)(c)==(reference(m,b,5).cfg.private)(c));
    assert((x.cfg.private)(other)==(m.initial)(other));
    assert(z.cfg.net.pending.get(11)==x.cfg.net.pending.get(11) && z.cfg.net.pending.get(12)==x.cfg.net.pending.get(12));
    assert(z.reserved.contains(11)==x.reserved.contains(11) && z.reserved.contains(12)==x.reserved.contains(12));
    assert(pair::before_issue(m,x,l));assert(pair::before_issue(m,z,l));
}

pub open spec fn first_end<S>(m:Program<S>,l:Lanes,b:Fork,t:Tape,c:Tape) -> State<S> {
    tape::after(m,prepared(m,l,b,t),c)
}
pub open spec fn prefix_actions(b:Fork,t:Tape,c:Tape) -> Seq<Event> {
    asm::boot(Some(b))+asm::actions(t)+asm::actions(c)
}
pub open spec fn heard(c:Tape,r:Replica) -> bool {
    exists|j:int| 0<=j<c.len() && {let e=#[trigger] c[j];e.action is Deliver && e.incoming.is_some()
        && first_reply(e.incoming.unwrap()) && e.incoming.unwrap().from==at(r)}
}
pub(crate) proof fn exchange_heard(t:Tape,r:Replica)
    requires cause::exchange(t,r,rpc::replies()),
    ensures heard(tape::pick(t,Process::FirstClient,true),r),
{
    let c=tape::pick(t,Process::FirstClient,true);let site=tape::pick(t,at(r),true);
    let (i,j,k)=choose|i:int,j:int,k:int| 0<=i<j<site.len() && 0<=k<c.len() && cause::intake_at(#[trigger] site[i],r)
        && cause::answer_at(#[trigger] site[j],r,rpc::replies()) && cause::delivered(site[j],#[trigger] c[k]);
    assert(first_reply(c[k].incoming.unwrap()) && c[k].incoming.unwrap().from==at(r));
}
pub open spec fn actual_first<S>(m:Program<S>,first:spec_fn(S)->int,l:Lanes,b:Fork,t:Tape,c:Tape) -> bool {
    let x=asm::entry(m,l);let z=first_end(m,l,b,t,c);let a=prefix_actions(b,t,c);
    asm::prefix(m,x,a,true) && asm::drive(m,x,a)==z && respondents(t) && mail::posted(m)(z)
        && first((z.cfg.private)(Process::FirstClient))==first_value(b) && wire::delayed_reply(z,b,rpc::replies())
        && traffic::weak_queue(z,b)
        && cause::pending_inputs(m,(prepared(m,l,b,t).cfg.private)(Process::FirstClient),c)
        && heard(c,crate::origin(b.branch)) && heard(c,Replica::R3)
        && (forall|i:int| 0<=i<c.len() ==> {let e=#[trigger] c[i];e.actor==Process::FirstClient
            && (e.incoming.is_some() ==> e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3))})
}
proof fn actual_caller<S>(m:Program<S>,first:spec_fn(S)->int,l:Lanes,b:Fork,t:Tape,p:Service<S>,who:fork::Issuer)
    requires asm::lanes_ok(l),dispatch::initiates(m),dispatch::weak_open(m,b),cause::member_sample(m,first,b),
        cause::returning(m,b,p),fork::wire_route(b,p,who,rpc::replies()),loss::stable(b,p),calls::sent_to_caller(prepared(m,l,b,t),calls::caller(p)),
        traffic::fitted(t,|_e:Observation|true),respondents(t),tape::plays(m,root(m,l,b),t),traffic::weak_queue(prepared(m,l,b,t),b),
    ensures actual_first(m,first,l,b,t,calls::caller(p)),calls::client_change(prepared(m,l,b,t),first_end(m,l,b,t,calls::caller(p)),calls::caller(p)),
        pair::before_issue(m,first_end(m,l,b,t,calls::caller(p)),l),
{
    let c=calls::caller(p);let x=root(m,l,b);let z=prepared(m,l,b,t);let end=first_end(m,l,b,t,c);
    prepared_frame(m,l,b,t);calls::finish_caller(m,first,b,p,who,z);asm::launch(m,l,Some(b));
    exchange_heard(tape::record(p,0),crate::origin(b.branch));exchange_heard(tape::record(p,0),Replica::R3);
    asm::native_prefix(m,x,t,true);asm::native_prefix(m,z,c,true);
    asm::prefix_concat(m,asm::entry(m,l),asm::boot(Some(b)),asm::actions(t),true);
    asm::prefix_concat(m,asm::entry(m,l),asm::boot(Some(b))+asm::actions(t),asm::actions(c),true);
    let r=maj::missing(b);
    assert(answered(t,r));
    let (i,j)=choose|i:int,j:int| 0<=i<j<t.len() && cause::intake_at(#[trigger] t[i],r)
        && cause::answer_at(#[trigger] t[j],r,rpc::replies());
    let id=t[j].action->Send_0;let q=t[j].action->Send_1;
    assert forall|k:int| 0<=k<t.len() implies !((#[trigger] t[k]).action==Action::<Wire>::Deliver(id) && t[k].incoming==Some(q))
        by {if t[k].incoming==Some(q) {wire::actor_received(m,x,t,k);assert(t[k].actor is At);}}
    wire::pending_send(m,x,t,id,q);
    assert(!calls::takes(c,id)) by {
        if calls::takes(c,id) {let k=choose|k:int| 0<=k<c.len() && (#[trigger] c[k]).action==Action::<Wire>::Deliver(id);
            assert(c[k].incoming==Some(q));}
    }
    assert(end.cfg.net.pending.get(id)==Some(q));assert(wire::delayed_reply(end,b,rpc::replies()));
    assert forall|k:int| 0<=k<c.len() implies (#[trigger] c[k]).actor==Process::FirstClient by {
        tape::picked(tape::record(p,0),Process::FirstClient,true,k);
    }
    assert forall|i:nat| i<=2 implies #[trigger] end.cfg.net.pending.get(i)==state_after(b,5).pending.get(i)
        by {assert(z.cfg.net.pending.get(i)==state_after(b,5).pending.get(i));assert(!calls::takes(c,i));}
    assert(end.cfg.net.pending.get(11)==None && end.cfg.net.pending.get(12)==None);
    assert((z.cfg.private)(Process::SecondClient)==(end.cfg.private)(Process::SecondClient));
    assert(pair::before_issue(m,end,l));
}

// At the crash, a request to a live process cannot disappear with its
// sender. All such ordinary slots still correspond, including queued grants.
pub proof fn issue_pair<S>(m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,f:Encoding,
    x:State<S>,y:State<S>,a:State<S>,b:State<S>,ca:Tape,cb:Tape)
    requires asm::lanes_ok(l),first::startup(m),issue::can_issue(m,res),traffic::paired(x,y,n,f),
        pair::c1_protected(x),pair::c1_protected(y),calls::client_change(x,a,ca),calls::client_change(y,b,cb),
        pair::before_issue(m,a,l),pair::before_issue(m,b,l),mail::posted(m)(a),mail::posted(m)(b),
    ensures ({let q=pair::close(true);let u=asm::drive(m,a,q);let v=asm::drive(m,b,q);
        asm::prefix(m,a,q,true) && asm::prefix(m,b,q,true) && calls::issued_pair(u,v,n,f)
            && read::issued_to_majority(u) && !read::returned(res)(u) && read::issued_to_majority(v) && !read::returned(res)(v)
            && a.cfg.net.pending.submap_of(u.cfg.net.pending) && b.cfg.net.pending.submap_of(v.cfg.net.pending)
    }),
{
    pair::close_at(m,res,l,a,true);pair::close_at(m,res,l,b,true);
    let u=asm::drive(m,a,pair::close(true));let v=asm::drive(m,b,pair::close(true));
    assert forall|i:nat| i>2 implies #[trigger] calls::live_slot(u,v,i,f) && u.reserved.contains(i)==v.reserved.contains(i) by {
        assert(y.cfg.net.pending.get(i)==traffic::packet(f,x.cfg.net.pending.get(i)));
        assert(a.cfg.net.pending.get(i)==(if calls::takes(ca,i){None}else{x.cfg.net.pending.get(i)}));
        assert(b.cfg.net.pending.get(i)==(if calls::takes(cb,i){None}else{y.cfg.net.pending.get(i)}));
        if x.cfg.net.pending.contains_key(i) {
            assert(y.cfg.net.pending.get(i)==Some(traffic::image(f,x.cfg.net.pending[i])));
        }
        if calls::takes(ca,i) || calls::takes(cb,i) {
            assert(x.cfg.net.pending.contains_key(i) && x.cfg.net.pending[i].to==Process::FirstClient);
            assert(y.cfg.net.pending.contains_key(i) && y.cfg.net.pending[i].to==Process::FirstClient);
            assert(x.reserved.contains(i) && y.reserved.contains(i));
        }
        assert((a.cfg.net.pending.contains_key(i) && a.cfg.net.pending[i].to==at(Replica::R3))
            ==(b.cfg.net.pending.contains_key(i) && b.cfg.net.pending[i].to==at(Replica::R3)));
        assert(read::retired_at_failure(a).contains(i)==read::retired_at_failure(b).contains(i));
    }
    assert forall|i:nat| i<=2 implies #[trigger] u.cfg.net.pending.get(i)==state_after(alpha(n),5).pending.get(i)
        && v.cfg.net.pending.get(i)==state_after(beta(n),5).pending.get(i) by {
        assert(a.cfg.net.pending.get(i)==(if calls::takes(ca,i){None}else{x.cfg.net.pending.get(i)}));
        assert(b.cfg.net.pending.get(i)==(if calls::takes(cb,i){None}else{y.cfg.net.pending.get(i)}));
        assert(x.cfg.net.pending.get(i)==state_after(alpha(n),5).pending.get(i)
            && y.cfg.net.pending.get(i)==state_after(beta(n),5).pending.get(i));
        assert(!calls::takes(ca,i) && !calls::takes(cb,i));
    }
    assert forall|p:Process| survivor_actor(p) implies #[trigger] (u.cfg.private)(p)==(v.cfg.private)(p) by {
        if p!=Process::SecondClient {assert(pair::sites().contains(p));assert((x.cfg.private)(p)==(y.cfg.private)(p));}
    }
    assert(traffic::weak_queue(v,beta(n))) by {
        assert forall|i:nat| i<=2 implies #[trigger] v.cfg.net.pending.get(i)==state_after(beta(n),5).pending.get(i)
            by {assert(u.cfg.net.pending.get(i)==state_after(alpha(n),5).pending.get(i));}
    }
    assert(survivor(u.cfg.net)==survivor(v.cfg.net));
    assert(calls::issued_pair(u,v,n,f));
}

proof fn late_reply<S>(m:Program<S>,b:Fork,z:State<S>,issued:State<S>,acts:Seq<Event>)
    requires wire::delayed_reply(z,b,rpc::replies()),z.cfg.net.pending.submap_of(issued.cfg.net.pending),
        issued.cfg.net.first_stopped,wire::service_prefix(m,issued,acts),
    ensures wire::delayed_reply(asm::drive(m,issued,acts),b,rpc::replies()),
{
    let id=choose|i:nat| #[trigger] z.cfg.net.pending.contains_key(i) && {let q=z.cfg.net.pending[i];
        q.from==at(maj::missing(b)) && q.to==Process::FirstClient && first_reply(q)};
    let q=z.cfg.net.pending[id];
    assert(issued.cfg.net.pending.get(id)==Some(q));wire::held_at_return(m,issued,acts,id,q);
    assert(asm::drive(m,issued,acts).cfg.net.pending.contains_key(id));
}

pub open spec fn second_service<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,base:State<S>,run:fair::Runnable,n:Notice) -> bool {
    forall|a:Seq<Event>| #[trigger] asm::prefix(m,base,a,true)
        && crate::survivors::after_crash(asm::drive(m,base,a).cfg.net)
        && traffic::weak_queue(asm::drive(m,base,a),alpha(n)) ==> {
            let x=asm::drive(m,base,a);
            (x.requested.is_empty() ==> model::sampling(m,first,res,x))
            && (read::issued_to_majority(x) ==> model::eventual(m,res,x,run)
                && (exists|e:fair::Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run))
                && !wait::needs_class(read::service_step(m),read::returned(res),x,calls::evidence(alpha(n))))
        }
}
pub open spec fn completes<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,
    n:Notice,f:Encoding,t:Tape,ca:Tape,cb:Tape,acts:Seq<Event>) -> bool {
    let a=alpha(n);let b=beta(n);let u=traffic::translated(f,t,2);
    let x=first_end(m,l,a,t,ca);let y=first_end(m,l,b,u,cb);let close=pair::close(true);
    let ia=asm::drive(m,x,close);let ib=asm::drive(m,y,close);let v=res((asm::drive(m,ia,acts).cfg.private)(Process::SecondClient)).unwrap();
    actual_first(m,first,l,a,t,ca) && actual_first(m,first,l,b,u,cb)
        && asm::prefix(m,x,close,true) && asm::prefix(m,y,close,true)
        && calls::suffix(m,res,n,f,ia,ib,acts) && fork::held_in_replay(m,ia.cfg,acts,v) && fork::held_in_replay(m,ib.cfg,acts,v)
        && wire::delayed_reply(asm::drive(m,ia,acts),a,rpc::replies())
        && wire::delayed_reply(asm::drive(m,ib,acts),b,rpc::replies())
}

proof fn sample_original<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    start:Seq<Event>,z:State<S>,run:fair::Runnable,p:Service<S>)
    requires z==asm::drive(m,asm::entry(m,l),start),asm::prefix(m,asm::entry(m,l),start,true),
        asm::prefix(m,z,pair::close(true),true),pair::before_issue(m,z,l),traffic::weak_queue(z,alpha(n)),
        issue::can_issue(m,res),second_service(m,first,res,asm::entry(m,l),run,n),
        read::issued_to_majority(asm::drive(m,z,pair::close(true))),
        wait::first_return(read::service_step(m),read::returned(res),asm::drive(m,z,pair::close(true)),p),
    ensures model::held(p.states,live_pair(),res((p.states.last().cfg.private)(Process::SecondClient)).unwrap()),
{
    let base=asm::entry(m,l);let wake=seq![Action::<Wire>::StopFirstClient,Action::CrashR3,Action::StartSecondClient];
    let s=asm::drive(m,z,wake);let h=model::second_head(m,s);
    assert(pair::close(true) =~= wake+h.actions);
    asm::prefix_concat(m,z,wake,h.actions,true);asm::prefix_concat(m,base,start,wake,true);
    assert(asm::prefix(m,base,start+wake,true));let ia=asm::drive(m,z,pair::close(true));
    reveal_with_fuel(asm::drive,4);reveal_with_fuel(asm::prefix,3);
    assert(traffic::weak_queue(s,alpha(n))) by {
        assert forall|i:nat| i<=2 implies #[trigger] s.cfg.net.pending.get(i)==state_after(alpha(n),5).pending.get(i)
            by {assert(z.cfg.net.pending.get(i)==state_after(alpha(n),5).pending.get(i));}
    }
    assert(model::sampling(m,first,res,s));assert(nb::within(read::prefix_step(m),read::at_state(s),s,0));
    assert(h.states.last()==ia);model::second_quorum_rule(m,first,res,s,s,p);
}

proof fn path_end<S>(m:Program<S>,p:Service<S>,i:nat)
    requires p.states.len()==p.actions.len()+1,i<p.states.len(),wait::valid_edges(read::service_step(m),p),
    ensures asm::drive(m,p.states[i as int],p.actions.skip(i as int))==p.states.last(),
    decreases p.actions.len()-i,
{
    if i<p.actions.len() {
        assert(read::service_step(m)(p.states[i as int],p.actions[i as int],p.states[i as int+1]));
        assert(p.actions.skip(i as int)[0]==p.actions[i as int] && p.actions.skip(i as int).drop_first() =~= p.actions.skip(i as int+1));
        path_end(m,p,i+1);
    }
}

// The source preparation is a single legal alpha run from fanout until all
// three respondents have sent. Neither an enabled beta preparation nor a
// C1 or C2 result is an input. The mailbox alternatives are per-source,
// independently testable shortages for this selected preparation.
pub open spec fn sender_refusal<S>(m:Program<S>,l:Lanes,n:Notice,f:Encoding,t:Tape) -> bool {
    let x=root(m,l,alpha(n));let y=root(m,l,beta(n));let u=traffic::translated(f,t,2);let r=at(Replica::R3);
    exists|k:nat| k<t.len() && {let s=traffic::at_cut(m,x,t,k);let z=traffic::at_cut(m,y,u,k);let h=#[trigger] u[k as int];
        tape::plays(m,y,u.take(k as int)) && traffic::paired(s,z,n,f) && h.actor==r && t[k as int].actor==r
            && (m.accept)((s.cfg.private)(r),t[k as int]) && process_step(z.cfg.net,h.action)==h
            && enabled(z.cfg.net,h.action) && !(m.accept)((z.cfg.private)(r),h)}
}
pub proof fn two_reads_with_coupled_traffic<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,
    n:Notice,f:Encoding,t:Tape,scope:spec_fn(Observation)->bool,rel:traffic::Relation<S>,who:fork::Issuer,used:rpc::Ledger<S>,
    region:spec_fn(Fork)->nb::Region<State<S>>,run:fair::Runnable,audit:trans::PacketAudit)
    requires asm::lanes_ok(l),dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b) && model::read_a(m,first,res,reference(m,b,0),run)
            && mail::fair_opportunity(m,run,reference(m,b,5)) && trans::no_first_wait(m,b,audit)
            && rpc::registered(m,b,region(b),who,used),
        traffic::fitted(t,scope),tape::plays(m,root(m,l,alpha(n)),t),respondents(t),keeps_reports(f),
        traffic::recipient_use(m,f),
        calls::distinct_weak_names(m),second_service(m,first,res,asm::entry(m,l),run,n),
    ensures (sender_refusal(m,l,n,f,t) && !(traffic::sender_control(m,f,rel,scope,2)
            && rel((root(m,l,alpha(n)).cfg.private)(at(Replica::R3)),(root(m,l,beta(n)).cfg.private)(at(Replica::R3)))))
        || input_obstruction(m,alpha(n),audit,prepared(m,l,alpha(n),t))
        || input_obstruction(m,beta(n),audit,prepared(m,l,beta(n),traffic::translated(f,t,2)))
        || exists|ca:Tape,cb:Tape,a:Seq<Event>| #[trigger] completes(m,first,res,l,n,f,t,ca,cb,a),
{
    let a=alpha(n);let b=beta(n);let u=traffic::translated(f,t,2);let xa=root(m,l,a);let xb=root(m,l,b);
    traffic::pair_at_fanout(m,l,n,f);
    let k=traffic::replay_preparation(m,n,f,scope,rel,xa,xb,t);
    if k<t.len() {assert(sender_refusal(m,l,n,f,t));return;}
    assert(k==t.len());assert(t.take(k as int) =~= t);assert(u.take(k as int) =~= u);
    assert(traffic::fitted(u,|_e:Observation| true)) by {
        assert forall|i:int| 0<=i<u.len() implies traffic::preparation_input(#[trigger] u[i]) by {assert(traffic::preparation_input(t[i]));}
    }
    copy_respondents(f,t);
    let x=prepared(m,l,a,t);let y=prepared(m,l,b,u);
    assert(dispatch::weak_open(m,a) && dispatch::weak_open(m,b));
    let pa=select_caller(m,res,a,x,audit,who,used,region(a),run);
    let pb=select_caller(m,res,b,y,audit,who,used,region(b),run);
    if usable(m,a,audit,x,pa) && usable(m,b,audit,y,pb) {
        assert(traffic::fitted(t,|_e:Observation|true));
        model::first_quorum_rule(m,first,res,a);model::first_quorum_rule(m,first,res,b);
        actual_caller(m,first,l,a,t,pa,who);actual_caller(m,first,l,b,u,pb,who);
        prepared_frame(m,l,a,t);prepared_frame(m,l,b,u);
        let ca=calls::caller(pa);let cb=calls::caller(pb);let za=first_end(m,l,a,t,ca);let zb=first_end(m,l,b,u,cb);
        issue_pair(m,res,l,n,f,x,y,za,zb,ca,cb);
        let close=pair::close(true);let ia=asm::drive(m,za,close);let ib=asm::drive(m,zb,close);
        asm::prefix_concat(m,asm::entry(m,l),prefix_actions(a,t,ca),close,true);
        assert(asm::prefix(m,asm::entry(m,l),prefix_actions(a,t,ca)+close,true));
        assert(model::eventual(m,res,ia,run));
        let e=choose|e:fair::Run<S>| #[trigger] fair::execution(m,e,ia) && fair::fair(e,run);
        let p=calls::common_second_service(m,res,n,f,ia,ib,run,e);let acts=p.actions;
        late_reply(m,a,za,ia,acts);late_reply(m,b,zb,ib,acts);
        sample_original(m,first,res,l,n,prefix_actions(a,t,ca),za,run,p);
        let val=res((p.states.last().cfg.private)(Process::SecondClient)).unwrap();
        let (i,r)=choose|i:int,r:Replica| 0<=i<p.states.len() && live_pair().contains(r) && #[trigger] (p.states[i].cfg.net.locals)(r)==val;
        calls::transfer_sample(m,n,f,p,ib,0,i as nat,r);assert(acts.skip(0) =~= acts);
        path_end(m,p,0);
        assert(completes(m,first,res,l,n,f,t,ca,cb,acts));
    }
}
}
