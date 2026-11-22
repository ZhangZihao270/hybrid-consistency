// Solicited replies and the service needed before a survivor can send one.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*, protocol::*};
use crate::fair_read as fair;
use crate::first_assembly::{Lanes, Service, entry};
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::{self as first, reference};
use crate::first_service_loss as loss;
use crate::first_splice::{self as s, Tape};
use crate::fork_dependencies as dep;
use crate::hybrid_fork as fork;
use crate::hybrid_majority as model;
use crate::hybrid_transparency as trans;
use crate::independent_read::{self as read, State};
use crate::promotion_wait as wait;
use crate::read_call::{Event, Program};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::sr1_majorities as maj;
use crate::sr1_ordinary as ordinary;

verus! {

pub open spec fn replies() -> trans::PacketAudit { |q| first_reply(q) }

// A local emission rule. Other sends, preparation and the value carried by
// an answer remain unrestricted. The original request is a real envelope.
pub open spec fn solicited<S>(m: Program<S>, scope: nb::Region<State<S>>) -> bool {
    forall|x:State<S>, a:Event, y:State<S>| scope(x) && !mail::posted(m)(x)
        && #[trigger] mail::active_step(m)(x,a,y)
        && a is Send && first_reply(a->Send_1) ==> {
            let r=a->Send_1.from->At_0;
            x.cfg.net.pending.get(dispatch::request_id(r)) != Some(dispatch::request(r))
        }
}

// Removing an initially pending request from this network requires its
// actual delivery. A send at an occupied slot is disabled.
proof fn request_delivery<S>(m:Program<S>, b:Fork, p:Service<S>, r:Replica, k:nat) -> (i:nat)
    requires cause::returning(m,b,p), k<=p.actions.len(),
        p.states[k as int].cfg.net.pending.get(dispatch::request_id(r)) != Some(dispatch::request(r)),
    ensures i<k, cause::intake_at(s::record(p,0)[i as int],r),
    decreases k,
{
    let id=dispatch::request_id(r);let q=dispatch::request(r);
    assert(p.states[0].cfg.net.pending.get(id)==Some(q)) by {
        match r {Replica::R1=>{},Replica::R2=>{},Replica::R3=>{}}
    }
    let j=(k-1) as nat;let x=p.states[j as int];let a=p.actions[j as int];
    if x.cfg.net.pending.get(id)==Some(q) {
        assert(mail::active_step(m)(x,a,p.states[k as int]));
        assert(a==Action::<Wire>::Deliver(id));
        j
    } else {request_delivery(m,b,p,r,j)}
}

spec fn position(t:Tape, actor:Process, i:int) -> nat {
    s::pick(t.take(i),actor,true).len()
}
proof fn local_position(t:Tape, actor:Process, i:int)
    requires 0<=i<t.len(), t[i].actor==actor,
    ensures position(t,actor,i)<s::pick(t,actor,true).len(),
        s::pick(t,actor,true)[position(t,actor,i) as int]==t[i],
{
    let lo=t.take(i);let rest=t.skip(i+1);
    assert(t =~= lo+(seq![t[i]]+rest));
    cause::pick_concat(lo,seq![t[i]]+rest,actor,true);
    assert((seq![t[i]]+rest).drop_first() =~= rest);
}
proof fn local_order(t:Tape, actor:Process, i:int, j:int)
    requires 0<=i<j<t.len(), t[i].actor==actor,
    ensures position(t,actor,i)<position(t,actor,j),
{
    let head=t.take(j);assert(head[i]==t[i]);assert(head.take(i) =~= t.take(i));
    local_position(head,actor,i);
}

proof fn received_exchange<S>(m:Program<S>, b:Fork, p:Service<S>, r:Replica, k:nat,
    scope:nb::Region<State<S>>)
    requires cause::returning(m,b,p), k<p.actions.len(), dispatch::received_from(p,k as int,r),
        scope(reference(m,b,5)), mail::closed_while_pending(m,scope), solicited(m,scope),
    ensures r!=maj::missing(b), cause::exchange(s::record(p,0),r,replies()),
{
    let j=dispatch::sending_cut(m,b,p,k,r);
    let x=p.states[j as int];let a=p.actions[j as int];let y=p.states[j as int+1];
    mail::pending_scope(m,scope,p,j);
    assert(mail::active_step(m)(x,a,y));
    assert(x.cfg.net.pending.get(dispatch::request_id(r))!=Some(dispatch::request(r)));
    let i=request_delivery(m,b,p,r,j);
    let t=s::record(p,0);let site=at(r);let c=Process::FirstClient;
    assert(t[i as int].actor==site && t[j as int].actor==site && t[k as int].actor==c);
    local_position(t,site,i as int);local_position(t,site,j as int);local_position(t,c,k as int);
    local_order(t,site,i as int,j as int);
    assert(cause::answer_at(t[j as int],r,replies()) && cause::delivered(t[j as int],t[k as int]));
    let u=s::pick(t,site,true);let v=s::pick(t,c,true);
    let h=position(t,site,i as int) as int;let s=position(t,site,j as int) as int;let d=position(t,c,k as int) as int;
    assert(0<=h<s<u.len() && 0<=d<v.len() && cause::intake_at(u[h],r)
        && cause::answer_at(u[s],r,replies()) && cause::delivered(u[s],v[d]));
}

// The existing client rule counts two actual senders. The failure mask,
// last-send provenance and request removal give both solicited exchanges.
pub proof fn solicited_majority_route<S>(m:Program<S>, b:Fork, p:Service<S>,
    scope:nb::Region<State<S>>)
    requires cause::returning(m,b,p),
        dispatch::two_reporters(m,reference(m,b,5)), scope(reference(m,b,5)),
        mail::closed_while_pending(m,scope), solicited(m,scope),
    ensures cause::source_shape(s::record(p,0),b,replies()),
{
    let (i,j,r,h)=choose|i:int,j:int,r:Replica,h:Replica| 0<=i<p.actions.len() && 0<=j<p.actions.len()
        && r!=h && #[trigger] dispatch::received_from(p,i,r) && #[trigger] dispatch::received_from(p,j,h);
    received_exchange(m,b,p,r,i as nat,scope);received_exchange(m,b,p,h,j as nat,scope);
    assert(r==crate::origin(b.branch) || h==crate::origin(b.branch));
    assert(r==Replica::R3 || h==Replica::R3);
}

// Only live senders matter on this one-failure reference. The older direct
// interface enforces solicitation there regardless of its extra ready test.
pub proof fn existing_interface_routes<S>(m:Program<S>, b:Fork, p:Service<S>,
    pre:nb::Region<State<S>>, sent:nb::Region<State<S>>, audit:trans::PacketAudit, who:fork::Issuer)
    requires dispatch::response_interface(m,b,pre,sent,audit), cause::returning(m,b,p),
        fork::native(p,who),
    ensures fork::wire_route(b,p,who,replies()),
{
    let scope=|x:State<S>| pre(x) && x.cfg.net.unavailable==Some(maj::missing(b));
    assert(mail::closed_while_pending(m,scope)) by {
        assert forall|x:State<S>,a:Event,y:State<S>| scope(x) && !mail::posted(m)(x)
            && #[trigger] mail::active_step(m)(x,a,y) && !mail::posted(m)(y) implies scope(y) by {}
    }
    assert(solicited(m,scope)) by {
        assert forall|x:State<S>,a:Event,y:State<S>| scope(x) && !mail::posted(m)(x)
            && #[trigger] mail::active_step(m)(x,a,y)
            && a is Send && first_reply(a->Send_1) implies {
                let r=a->Send_1.from->At_0;
                x.cfg.net.pending.get(dispatch::request_id(r))!=Some(dispatch::request(r))
            } by {
                let r=a->Send_1.from->At_0;
                assert(live(x.cfg.net,at(r)) && r!=maj::missing(b));
                assert(dispatch::direct_responder(m,pre,r,mail::receipt_of(audit)));
                assert(!mail::receipt_of(audit)(x,a,y));
                assert(dispatch::native_reply(x,a,r));
            }
    }
    solicited_majority_route(m,b,p,scope);
}

// This is the older whole-trace RPC contract: it already specifies the
// exchanges. Matching its slot owners to the chosen transport is enough.
pub proof fn route_from_recorded_interface<S>(m:Program<S>,b:Fork,l:Lanes,who:fork::Issuer,
    answers:trans::PacketAudit,p:Service<S>)
    requires fork::proper(l,who),dep::rc_interface(m,b,l,answers),cause::returning(m,b,p),!wait::uses(p,dep::promotion(b)),
    ensures fork::wire_route(b,p,who,answers),
{
    assert(dep::named(p,l));
    assert forall|i:int| 0<=i<p.actions.len() implies match #[trigger] p.actions[i] {
        Action::Send(id,q)=>id>5 && id!=11 && id!=12 && q.from==at(who(id)), _=>true
    } by {
        if let Action::Send(id,q)=p.actions[i] {assert(l.get(id)==Some(q.from->At_0));}
    }
}

// An allocator refinement. Its ledger can include the C1 reservations
// already maintained by the monitor. Other single-use identities can be
// supplied by the implementation. No packet or receipt is prescribed.
pub type Ledger<S> = spec_fn(State<S>)->Set<nat>;
pub open spec fn allocator<S>(m:Program<S>,scope:nb::Region<State<S>>,who:fork::Issuer,used:Ledger<S>) -> bool {
    forall|x:State<S>,a:Event,y:State<S>| scope(x) && !mail::posted(m)(x) && #[trigger] mail::active_step(m)(x,a,y)
        ==> used(x).subset_of(used(y)) && match a {
            Action::Send(id,q)=>id>5 && id!=11 && id!=12 && q.from==at(who(id)) && !used(x).contains(id) && used(y).contains(id),
            _=>true,
        }
}
proof fn spent_persists<S>(p:Service<S>,used:Ledger<S>,i:int,j:int)
    requires p.states.len()==p.actions.len()+1,0<=i<=j<p.states.len(),
        forall|k:int| 0<=k<p.actions.len() ==> (#[trigger] used(p.states[k])).subset_of(used(p.states[k+1])),
    ensures used(p.states[i]).subset_of(used(p.states[j])),
    decreases j-i,
{
    if j>i {spent_persists(p,used,i,j-1);assert(used(p.states[j-1]).subset_of(used(p.states[j])));}
}
pub proof fn allocator_gives_native<S>(m:Program<S>,b:Fork,p:Service<S>,scope:nb::Region<State<S>>,who:fork::Issuer,used:Ledger<S>)
    requires cause::returning(m,b,p),scope(reference(m,b,5)),mail::closed_while_pending(m,scope),allocator(m,scope,who,used),
    ensures fork::native(p,who),
{
    assert forall|k:int| 0<=k<p.actions.len() implies {
        let a=#[trigger] p.actions[k];let x=p.states[k];let y=p.states[k+1];
        used(x).subset_of(used(y)) && match a {
            Action::Send(id,q)=>id>5 && id!=11 && id!=12 && q.from==at(who(id)) && !used(x).contains(id) && used(y).contains(id),
            _=>true,
        }
    } by {
        mail::pending_scope(m,scope,p,k as nat);
        assert(mail::active_step(m)(p.states[k],p.actions[k],p.states[k+1]));
    }
    assert forall|i:int,j:int| 0<=i<j<p.actions.len() && (#[trigger] p.actions[i]) is Send && (#[trigger] p.actions[j]) is Send
        implies p.actions[i]->Send_0!=p.actions[j]->Send_0 by {
        assert forall|k:int| 0<=k<p.actions.len() implies (#[trigger] used(p.states[k])).subset_of(used(p.states[k+1]))
            by {let a=p.actions[k];}
        spent_persists(p,used,i+1,j);
    }
}

pub open spec fn registered<S>(m:Program<S>,b:Fork,scope:nb::Region<State<S>>,who:fork::Issuer,used:Ledger<S>) -> bool {
    scope(reference(m,b,5)) && mail::closed_while_pending(m,scope)
        && dispatch::two_reporters(m,reference(m,b,5)) && solicited(m,scope) && allocator(m,scope,who,used)
}

pub open spec fn installation<S>(b:Fork,p:Service<S>,i:int) -> bool {
    let x=p.states[i];let y=p.states[i+1];let a=p.actions[i];
    exists|r:Replica| {let v=(y.cfg.net.locals)(r);
        cause::quorum(b,r) && (#[trigger] (x.cfg.net.locals)(r))!=v
        && (a==Action::Local(r,Wire::Copy(v)) || (a is Deliver && x.cfg.net.pending.contains_key(a->Deliver_0)
            && x.cfg.net.pending[a->Deliver_0].path==Path::Weak && x.cfg.net.pending[a->Deliver_0].to==at(r)
            && x.cfg.net.pending[a->Deliver_0].input==Wire::Copy(v)))}
}
pub open spec fn refused_receipt<S>(m:Program<S>,b:Fork,p:Service<S>,i:int) -> bool {
    let x=p.states[i];let a=p.actions[i];let id=a->Deliver_0;let q=x.cfg.net.pending[id];
    dep::crossing(b,x,a) && !cause::changes_sample(b,x,p.states[i+1])
        && (exists|h:int| 0<=h<i && #[trigger] p.actions[h]==Action::Send(id,q) && live(p.states[h].cfg.net,at(Replica::R3)))
        && (exists|k:int| i<k<p.actions.len() && #[trigger] ordinary::refuses(m,p,i+1,k,x,id,q))
}
pub open spec fn decisive_step<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit,p:Service<S>,i:int) -> bool {
    ordinary::shortest(m,b,audit,p) && 0<=i<p.actions.len() && (installation(b,p,i) || refused_receipt(m,b,p,i))
}
pub open spec fn blocked_source<S>(m:Program<S>,b:Fork,audit:trans::PacketAudit) -> bool {
    (forall|p:Service<S>| #[trigger] ordinary::weak_free_return(m,b,audit,p) ==> wait::uses(p,dep::boundary(b)))
        && exists|p:Service<S>,i:int| #[trigger] decisive_step(m,b,audit,p,i)
}

proof fn source_or_guard<S>(m:Program<S>,b:Fork,res:spec_fn(S)->Option<int>,scope:nb::Region<State<S>>,audit:trans::PacketAudit,
    who:fork::Issuer,used:Ledger<S>,run:fair::Runnable) -> (p:Service<S>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),trans::no_first_wait(m,b,audit),registered(m,b,scope,who,used),
        model::eventual(m,res,reference(m,b,0),run),mail::fair_opportunity(m,run,reference(m,b,5)),
    ensures ordinary::weak_free_return(m,b,audit,p),fork::wire_route(b,p,who,replies()),
        blocked_source(m,b,audit) || fork::clean(m,b,p),
{
    let offered=ordinary::service_with_ordinary_traffic(m,b,res,run,audit);
    let p=if exists|p:Service<S>| #[trigger] ordinary::weak_free_return(m,b,audit,p) && !wait::uses(p,dep::boundary(b)) {
        choose|p:Service<S>| #[trigger] ordinary::weak_free_return(m,b,audit,p) && !wait::uses(p,dep::boundary(b))
    } else {ordinary::minimize(m,b,audit,offered)};
    ordinary::ordinary_edges(m,b,audit,p);allocator_gives_native(m,b,p,scope,who,used);
    solicited_majority_route(m,b,p,scope);
    if wait::uses(p,dep::boundary(b)) {
        assert(ordinary::shortest(m,b,audit,p));
        let i=choose|i:int| 0<=i<p.actions.len() && dep::boundary(b)(p.states[i],#[trigger] p.actions[i],p.states[i+1]);
        let x=p.states[i];let y=p.states[i+1];let a=p.actions[i];assert(mail::active_step(m)(x,a,y));
        if cause::changes_sample(b,x,y) {
            let r=choose|r:Replica| cause::quorum(b,r) && #[trigger] (x.cfg.net.locals)(r)!=(y.cfg.net.locals)(r);
            let v=(y.cfg.net.locals)(r);assert(local_input(x.cfg.net,a,r)==Some(Wire::Copy(v)));
            assert(installation(b,p,i));
        } else {
            assert(dep::crossing(b,x,a));let id=a->Deliver_0;let q=x.cfg.net.pending[id];
            assert(!dep::promotion(b)(x,a,y));assert(p.states[0].cfg.net.pending.get(id)!=Some(q));
            mail::last_send(m,p,i as nat,id,q);
            ordinary::shortest_receipt_requires_guard(m,b,audit,p,who,i as nat);
            assert(refused_receipt(m,b,p,i));
        }
        assert forall|u:Service<S>| #[trigger] ordinary::weak_free_return(m,b,audit,u) implies wait::uses(u,dep::boundary(b)) by {}
        assert(decisive_step(m,b,audit,p,i));
        assert(blocked_source(m,b,audit));
    }
    p
}

pub open spec fn conflict<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:fork::Issuer,audit:trans::PacketAudit,w:fork::Completions<S>) -> bool {
    fork::completed(m,first,res,n,who,replies(),w) && trans::original_holds(m,alpha(n),who,w,audit)
        && trans::original_holds(m,beta(n),who,w,audit)
        && (!fork::explains_returns(m,first,res,who,alpha(n),w) || !fork::explains_returns(m,first,res,who,beta(n),w))
}

// No complete source route, local_service, matching SR2 observations, or
// caller follow-up appears in the hypotheses.
pub proof fn registered_reads_or_guard<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:fork::Issuer,audit:trans::PacketAudit,run:fair::Runnable,scope:spec_fn(Fork)->nb::Region<State<S>>,used:Ledger<S>)
    requires dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),fork::references(m,first,res,n,who,run),
        forall|b:Fork| b.notice==n ==> #[trigger] registered(m,b,scope(b),who,used) && trans::no_first_wait(m,b,audit),
        forall|l:Lanes| #[trigger] fork::proper(l,who) ==> wait::no_await(read::service_step(m),read::returned(res),
            |x:State<S>|read::reached(m,entry(m,l),x) && read::issued_to_majority(x),mail::receipt_of(audit)),
    ensures blocked_source(m,alpha(n),audit) || blocked_source(m,beta(n),audit)
        || exists|w:fork::Completions<S>| #[trigger] conflict(m,first,res,n,who,audit,w),
{
    let a=alpha(n);let b=beta(n);
    assert(dispatch::weak_open(m,a) && dispatch::weak_open(m,b));
    let pa=source_or_guard(m,a,res,scope(a),audit,who,used,run);
    let pb=source_or_guard(m,b,res,scope(b),audit,who,used,run);
    if !blocked_source(m,a,audit) && !blocked_source(m,b,audit) {
        ordinary::ordinary_edges(m,a,audit,pa);ordinary::ordinary_edges(m,b,audit,pb);
        let w=trans::finish_sources(m,first,res,n,who,replies(),audit,run,pa,pb);
        assert(conflict(m,first,res,n,who,audit,w));
    }
}

// A read whose serving cells already agree only needs them to remain
// unchanged on the chosen weak-free workload. This is separate from the
// local handling of R3's ordinary traffic.
pub open spec fn uniform<S>(b:Fork,x:State<S>) -> bool {
    (x.cfg.net.locals)(crate::origin(b.branch))==(x.cfg.net.locals)(Replica::R3)
}
pub open spec fn ordinary_controls<S>(m:Program<S>,b:Fork,scope:nb::Region<State<S>>,audit:trans::PacketAudit,rel:ordinary::Relation<S>) -> bool {
    forall|x:State<S>,a:Event,y:State<S>| scope(x) && !mail::posted(m)(x) && uniform(b,x)
        && #[trigger] trans::without_weak(m,b,audit)(x,a,y) ==> {
            let r=crate::origin(b.branch);
            !cause::changes_sample(b,x,y)
                && (dep::crossing(b,x,a) ==> rel(r,(x.cfg.private)(at(r)),(y.cfg.private)(at(r))))
        }
}
proof fn uniform_prefix<S>(m:Program<S>,b:Fork,p:Service<S>,j:nat,scope:nb::Region<State<S>>,audit:trans::PacketAudit,rel:ordinary::Relation<S>)
    requires ordinary::weak_free_return(m,b,audit,p),j<p.states.len(),scope(reference(m,b,5)),mail::closed_while_pending(m,scope),
        ordinary_controls(m,b,scope,audit,rel),
    ensures uniform(b,p.states[j as int]),
    decreases j,
{
    if j>0 {let k=(j-1) as nat;uniform_prefix(m,b,p,k,scope,audit,rel);ordinary::ordinary_edges(m,b,audit,p);
        mail::pending_scope(m,scope,p,k);let x=p.states[k as int];let y=p.states[j as int];
        assert(trans::without_weak(m,b,audit)(x,p.actions[k as int],y));assert(!cause::changes_sample(b,x,y));
        assert(cause::quorum(b,Replica::R3) && cause::quorum(b,crate::origin(b.branch)));
    }
}
proof fn controls_exclude_obstruction<S>(m:Program<S>,b:Fork,scope:nb::Region<State<S>>,audit:trans::PacketAudit,rel:ordinary::Relation<S>)
    requires scope(reference(m,b,5)),mail::closed_while_pending(m,scope),ordinary_controls(m,b,scope,audit,rel),ordinary::follows(m,rel),
    ensures !blocked_source(m,b,audit),
{
    if blocked_source(m,b,audit) {
        let (p,i)=choose|p:Service<S>,i:int| #[trigger] decisive_step(m,b,audit,p,i);
        let x=p.states[i];let a=p.actions[i];let y=p.states[i+1];ordinary::ordinary_edges(m,b,audit,p);
        uniform_prefix(m,b,p,i as nat,scope,audit,rel);mail::pending_scope(m,scope,p,i as nat);
        assert(trans::without_weak(m,b,audit)(x,a,y));assert(!cause::changes_sample(b,x,y));assert(!installation(b,p,i));
        let id=a->Deliver_0;let q=x.cfg.net.pending[id];
        let k=choose|k:int| i<k<p.actions.len() && #[trigger] ordinary::refuses(m,p,i+1,k,x,id,q);
        ordinary::refusal_separates_local_memories(m,b,p,i,k,rel);
    }
}
pub proof fn two_reads_from_local_controls<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,n:Notice,
    who:fork::Issuer,audit:trans::PacketAudit,run:fair::Runnable,scope:spec_fn(Fork)->nb::Region<State<S>>,used:Ledger<S>,rel:ordinary::Relation<S>)
    -> (w:fork::Completions<S>)
    requires dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),fork::references(m,first,res,n,who,run),ordinary::follows(m,rel),
        forall|b:Fork| b.notice==n ==> #[trigger] registered(m,b,scope(b),who,used) && trans::no_first_wait(m,b,audit)
            && ordinary_controls(m,b,scope(b),audit,rel),
        forall|l:Lanes| #[trigger] fork::proper(l,who) ==> wait::no_await(read::service_step(m),read::returned(res),
            |x:State<S>|read::reached(m,entry(m,l),x) && read::issued_to_majority(x),mail::receipt_of(audit)),
    ensures conflict(m,first,res,n,who,audit,w),
{
    let a=alpha(n);let b=beta(n);registered_reads_or_guard(m,first,res,n,who,audit,run,scope,used);
    assert(registered(m,a,scope(a),who,used) && registered(m,b,scope(b),who,used));
    controls_exclude_obstruction(m,a,scope(a),audit,rel);controls_exclude_obstruction(m,b,scope(b),audit,rel);
    choose|w:fork::Completions<S>| #[trigger] conflict(m,first,res,n,who,audit,w)
}

}
