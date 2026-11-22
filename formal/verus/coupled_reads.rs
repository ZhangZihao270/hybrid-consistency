// Complete the original calls after coupled ordinary replica preparation.
use vstd::prelude::*;
use crate::{Op,Replica,checkpoint::*,delivery::*,protocol::*};
use crate::coupled_traffic::{self as traffic, Encoding};
use crate::fair_read as fair;
use crate::first_assembly::{self as asm,Lanes,Service};
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_schedule::{self as first,reference};
use crate::first_service_loss as loss;
use crate::first_splice::{self as tape,Observation,Tape};
use crate::hybrid_fork as fork;
use crate::hybrid_majority as model;
use crate::hybrid_transparency as trans;
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::sr1_contract as rpc;
use crate::sr1_ordinary as ordinary;

verus! {

pub open spec fn caller<S>(p:Service<S>) -> Tape { tape::pick(tape::record(p,0),Process::FirstClient,true) }
pub open spec fn sent_to_caller<S>(x:State<S>, t:Tape) -> bool {
    forall|i:int| 0<=i<t.len() && (#[trigger] t[i]).action is Deliver ==>
        x.cfg.net.pending.get(t[i].action->Deliver_0)==t[i].incoming
}
pub open spec fn client_inputs(t:Tape) -> bool {
    (forall|i:int| 0<=i<t.len() ==> (#[trigger] t[i]).actor==Process::FirstClient)
    && (forall|i:int,j:int| 0<=i<j<t.len() && (#[trigger] t[i]).action is Deliver ==>
        (#[trigger] t[j]).action!=t[i].action)
}
proof fn caller_inputs<S>(m:Program<S>,b:Fork,p:Service<S>,who:fork::Issuer)
    requires cause::returning(m,b,p),fork::native(p,who),
    ensures client_inputs(caller(p)),
{
    let t=tape::record(p,0);let c=Process::FirstClient;let u=caller(p);
    fork::finite_allocation(p,p,who);
    crate::fork_dependencies::envelope_lifetimes(m,p,b,fork::allocation(who,p,p));
    assert forall|i:int| 0<=i<u.len() implies (#[trigger] u[i]).actor==c by {tape::picked(t,c,true,i);}
    pick_no_duplicate_delivery(t,c);
}
proof fn pick_no_duplicate_delivery(t:Tape,c:Process)
    requires cause::one_envelope(t),
    ensures ({let u=tape::pick(t,c,true);forall|i:int,j:int| 0<=i<j<u.len() && (#[trigger] u[i]).action is Deliver
        ==> (#[trigger] u[j]).action!=u[i].action}),
    decreases t.len(),
{
    if t.len()>0 {
        let tail=t.drop_first();let u=tape::pick(t,c,true);let v=tape::pick(tail,c,true);
        assert(cause::one_envelope(tail)) by {
            assert forall|i:int,j:int| 0<=i<j<tail.len() && tape::slot((#[trigger] tail[i]).action).is_some()
                && tape::slot(tail[i].action)==tape::slot((#[trigger] tail[j]).action)
                implies tail[i].action is Send && tail[j].action is Deliver by {assert(tail[i]==t[i+1] && tail[j]==t[j+1]);}
        }
        pick_no_duplicate_delivery(tail,c);
        if t[0].actor==c {
            assert forall|i:int,j:int| 0<=i<j<u.len() && (#[trigger] u[i]).action is Deliver implies (#[trigger] u[j]).action!=u[i].action by {
                assert(u[j]==v[j-1]);
                if i==0 {
                    tape::picked(tail,c,true,j-1);let k=choose|k:int| 0<=k<tail.len() && tail[k]==v[j-1];
                    assert(t[k+1]==u[j] && t[0]==u[0]);
                } else {assert(u[i]==v[i-1]);}
            }
        }
    }
}
pub open spec fn takes(t:Tape,id:nat) -> bool {
    exists|j:int| 0<=j<t.len() && (#[trigger] t[j]).action==Action::<Wire>::Deliver(id)
}
pub open spec fn client_change<S>(x:State<S>,y:State<S>,t:Tape) -> bool {
    x.reserved==y.reserved && x.owners==y.owners && x.calls==y.calls
    && x.requested==y.requested && x.first_requested==y.first_requested
    && x.cfg.net==Network{pending:x.cfg.net.pending,..y.cfg.net}
    && (forall|p:Process| p!=Process::FirstClient ==> #[trigger] (x.cfg.private)(p)==(y.cfg.private)(p))
    && (forall|i:nat| #[trigger] y.cfg.net.pending.get(i)==
        (if takes(t,i) {None} else {x.cfg.net.pending.get(i)})
        && (takes(t,i) ==> x.cfg.net.pending.contains_key(i) && x.cfg.net.pending[i].to==Process::FirstClient))
}
pub(crate) proof fn play_client<S>(m:Program<S>,x:State<S>,y:State<S>,t:Tape)
    requires tape::plays(m,x,t),client_inputs(t),sent_to_caller(y,t),!y.cfg.net.first_stopped,
        (x.cfg.private)(Process::FirstClient)==(y.cfg.private)(Process::FirstClient),
    ensures tape::plays(m,y,t),client_change(y,tape::after(m,y,t),t),
        (tape::after(m,x,t).cfg.private)(Process::FirstClient)==(tape::after(m,y,t).cfg.private)(Process::FirstClient),
    decreases t.len(),
{
    let end=tape::after(m,y,t);
    if t.len()>0 {
        let h=t[0];let a=h.action;let u=t.drop_first();let z=read::next(m,y,a);
        assert(process_step(y.cfg.net,a)==h);assert(read::service_step(m)(y,a,z));
        assert(client_inputs(u)) by {
            assert forall|i:int| 0<=i<u.len() implies (#[trigger] u[i]).actor==Process::FirstClient by {assert(u[i]==t[i+1]);}
            assert forall|i:int,j:int| 0<=i<j<u.len() && (#[trigger] u[i]).action is Deliver implies (#[trigger] u[j]).action!=u[i].action
                by {assert(u[i]==t[i+1] && u[j]==t[j+1]);}
        }
        assert(sent_to_caller(z,u)) by {
            assert forall|i:int| 0<=i<u.len() && (#[trigger] u[i]).action is Deliver implies z.cfg.net.pending.get(u[i].action->Deliver_0)==u[i].incoming
                by {assert(u[i]==t[i+1] && h.action!=u[i].action);}
        }
        play_client(m,read::next(m,x,a),z,u);
        assert(z.cfg.net.locals =~= y.cfg.net.locals);
        assert forall|p:Process| p!=Process::FirstClient implies #[trigger] (y.cfg.private)(p)==(end.cfg.private)(p) by {
            assert((z.cfg.private)(p)==(end.cfg.private)(p));
        }
        assert forall|i:nat| #[trigger] end.cfg.net.pending.get(i)==(if takes(t,i){None}else{y.cfg.net.pending.get(i)})
            && (takes(t,i) ==> y.cfg.net.pending.contains_key(i) && y.cfg.net.pending[i].to==Process::FirstClient) by {
            if takes(t,i) {let j=choose|j:int| 0<=j<t.len() && (#[trigger] t[j]).action==Action::<Wire>::Deliver(i);
                if j>0 {assert(u[j-1]==t[j]);assert(takes(u,i));}}
            if takes(u,i) {let j=choose|j:int| 0<=j<u.len() && (#[trigger] u[j]).action==Action::<Wire>::Deliver(i);
                assert(t[j+1]==u[j]);assert(takes(t,i));}
        }
    }
    assert(client_change(y,end,t));
}

// A's held-value rule is applied to the real crash reference. The original
// only needs the envelopes that this caller actually consumed.
pub proof fn finish_caller<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:Service<S>,who:fork::Issuer,z:State<S>)
    requires cause::returning(m,b,p),fork::native(p,who),cause::member_sample(m,first,b),loss::stable(b,p),
        !z.cfg.net.first_stopped,sent_to_caller(z,caller(p)),
        (z.cfg.private)(Process::FirstClient)==(reference(m,b,5).cfg.private)(Process::FirstClient),
    ensures ({let t=caller(p);let end=tape::after(m,z,t);
        tape::plays(m,z,t) && client_change(z,end,t) && mail::posted(m)(end)
            && first((end.cfg.private)(Process::FirstClient))==first_value(b)
            && cause::pending_inputs(m,(z.cfg.private)(Process::FirstClient),t)
            && forall|j:int| 0<=j<t.len() && (#[trigger] t[j]).incoming.is_some() ==>
                t[j].incoming.unwrap().from==at(crate::origin(b.branch)) || t[j].incoming.unwrap().from==at(Replica::R3)
    }),
{
    let t=tape::record(p,0);let c=Process::FirstClient;let u=tape::pick(t,c,false);let x=reference(m,b,5);
    traffic::move_caller_last(m,b,p,who);caller_inputs(m,b,p,who);
    cause::pending_on_caller(m,p,0);
    let others=ISet::new(|v:Process| v!=c);
    assert(tape::supports(u,others,ISet::full())) by {
        assert forall|i:int| 0<=i<u.len() implies {let e=#[trigger] u[i];others.contains(e.actor)
            && (tape::slot(e.action).is_some() ==> ISet::<nat>::full().contains(tape::slot(e.action).unwrap()))}
            by {tape::picked(t,c,false,i);}
    }
    tape::frame(m,x,u,others,ISet::full());assert(others.complement().contains(c));
    play_client(m,tape::after(m,x,u),z,caller(p));cause::forced_sample(m,first,p,b);
    assert forall|j:int| 0<=j<caller(p).len() && (#[trigger] caller(p)[j]).incoming.is_some() implies
        caller(p)[j].incoming.unwrap().from==at(crate::origin(b.branch)) || caller(p)[j].incoming.unwrap().from==at(Replica::R3)
        by {cause::caller_sources(m,b,p,j);}
}

pub open spec fn for_stopped(p:Option<Packet<Wire>>) -> bool {
    p.is_none() || p.unwrap().to==Process::FirstClient
}
pub open spec fn live_slot<S>(x:State<S>,y:State<S>,i:nat,f:Encoding) -> bool {
    let q=x.cfg.net.pending.get(i);let u=y.cfg.net.pending.get(i);
    u==traffic::packet(f,q) || (for_stopped(q) && for_stopped(u) && x.reserved.contains(i) && y.reserved.contains(i))
}
pub open spec fn issued_pair<S>(x:State<S>,y:State<S>,n:Notice,f:Encoding) -> bool {
    crate::survivors::after_crash(x.cfg.net) && crate::survivors::after_crash(y.cfg.net)
        && survivor(x.cfg.net)==survivor(y.cfg.net) && x.owners==y.owners
        && traffic::weak_queue(x,alpha(n)) && traffic::weak_queue(y,beta(n))
        && (forall|p:Process| survivor_actor(p) ==> #[trigger] (x.cfg.private)(p)==(y.cfg.private)(p))
        && (forall|i:nat| i>2 ==> #[trigger] live_slot(x,y,i,f) && x.reserved.contains(i)==y.reserved.contains(i))
}

// Replaying an arbitrary fresh send must respect the branch with the still
// occupied weak slot. This namespace condition concerns concrete transport
// IDs, independently of the contents of any quorum or return value.
pub open spec fn distinct_weak_names<S>(m:Program<S>) -> bool {
    forall|x:State<S>,a:Event,y:State<S>| crate::survivors::after_crash(x.cfg.net) && a is Send
        && #[trigger] read::service_step(m)(x,a,y) ==> a->Send_0>2
}
pub open spec fn evidence<S>(b:Fork) -> wait::Relation<State<S>,Event> {
    |x:State<S>,a:Event,_y:State<S>| a==Action::<Wire>::Deliver(2)
        && x.cfg.net.pending.get(2)==Some(packet_for(b,2))
}

// Only the receipt actually attempted at this cut needs to agree. The
// sender and its native guard are unchanged after R3 has failed.
pub open spec fn compatible_receipt<S>(m:Program<S>,f:Encoding,x:State<S>,a:Event) -> bool {
    let e=process_step(x.cfg.net,a);let s=(x.cfg.private)(e.actor);
    let h=traffic::observation(f,e,0);
    !(a is Deliver) || ((m.accept)(s,h) && (m.update)(s,h)==(m.update)(s,e))
}

pub(crate) proof fn replay_compatible_step<S>(m:Program<S>,n:Notice,f:Encoding,x:State<S>,y:State<S>,a:Event,u:State<S>)
    requires issued_pair(x,y,n,f),read::service_step(m)(x,a,u),!evidence(alpha(n))(x,a,u),
        distinct_weak_names(m), compatible_receipt(m,f,x,a),
    ensures ({let v=read::next(m,y,a);let e=process_step(x.cfg.net,a);
        read::service_step(m)(y,a,v) && issued_pair(u,v,n,f)
        && process_step(y.cfg.net,a)==traffic::observation(f,e,2)
        && !evidence(beta(n))(y,a,v)
    }),
{
    let e=process_step(x.cfg.net,a);let h=process_step(y.cfg.net,a);let v=read::next(m,y,a);
    assert(survivor_actor(e.actor));assert((m.accept)((x.cfg.private)(e.actor),e));
    match a {
        Action::Deliver(i)=>{
            assert(i>2);assert(live_slot(x,y,i,f));assert(!for_stopped(x.cfg.net.pending.get(i)));
            assert(y.cfg.net.pending.get(i)==Some(traffic::image(f,x.cfg.net.pending[i])));
        },
        Action::Send(i,_)=>{assert(i>2);assert(live_slot(x,y,i,f));assert(!y.cfg.net.pending.contains_key(i));},
        _=>{}
    }
    assert(h==traffic::observation(f,e,2));
    let s=(x.cfg.private)(e.actor);assert(s==(y.cfg.private)(h.actor));
    if a is Deliver {assert(h==traffic::observation(f,e,0));}
    else {assert(h==e);}
    assert((m.accept)(s,h) && (m.update)(s,h)==(m.update)(s,e));
    assert(read::service_step(m)(y,a,v));
    assert forall|r:Replica| r!=Replica::R3 implies #[trigger] (u.cfg.net.locals)(r)==(v.cfg.net.locals)(r) by {
        assert(local_input(x.cfg.net,a,r)==local_input(y.cfg.net,a,r));
        assert((x.cfg.net.locals)(r)==(y.cfg.net.locals)(r));
    }
    assert forall|i:nat| i<=2 implies #[trigger] u.cfg.net.pending.get(i)==x.cfg.net.pending.get(i)
        && v.cfg.net.pending.get(i)==y.cfg.net.pending.get(i) by {}
    assert forall|i:nat| i>2 implies #[trigger] live_slot(u,v,i,f) && u.reserved.contains(i)==v.reserved.contains(i) by {
        assert(live_slot(x,y,i,f));
        if tape::slot(a)!=Some(i) {assert(u.cfg.net.pending.get(i)==x.cfg.net.pending.get(i) && v.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));}
    }
    assert forall|p:Process| survivor_actor(p) implies #[trigger] (u.cfg.private)(p)==(v.cfg.private)(p) by {
        assert((x.cfg.private)(p)==(y.cfg.private)(p));
    }
    assert(traffic::weak_queue(u,alpha(n)) && traffic::weak_queue(v,beta(n))) by {
        assert forall|i:nat| i<=2 implies #[trigger] v.cfg.net.pending.get(i)==state_after(beta(n),5).pending.get(i)
            by {assert(y.cfg.net.pending.get(i)==v.cfg.net.pending.get(i));}
    }
    assert(issued_pair(u,v,n,f));
    assert(!evidence(beta(n))(y,a,v));
}
proof fn replay_second_step<S>(m:Program<S>,n:Notice,f:Encoding,x:State<S>,y:State<S>,a:Event,u:State<S>)
    requires issued_pair(x,y,n,f),read::service_step(m)(x,a,u),!evidence(alpha(n))(x,a,u),
        distinct_weak_names(m),traffic::recipient_use(m,f),
    ensures ({let v=read::next(m,y,a);let e=process_step(x.cfg.net,a);
        read::service_step(m)(y,a,v) && issued_pair(u,v,n,f)
        && process_step(y.cfg.net,a)==traffic::observation(f,e,2)
        && !evidence(beta(n))(y,a,v)
    }),
{
    let e=process_step(x.cfg.net,a);let s=(x.cfg.private)(e.actor);
    assert(survivor_actor(e.actor) && (m.accept)(s,e));
    if a is Deliver {assert(e.incoming.is_some() && e.incoming.unwrap().to==e.actor);}
    replay_compatible_step(m,n,f,x,y,a,u);
}
pub open spec fn legal_returns(v:int,w:int) -> bool {
    exists|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,v,w)
}
// The first response is taken at the same step on both real suffixes.
// The target receives its own packet, which may use a different encoding.
pub open spec fn matching_steps<S>(m:Program<S>,r:spec_fn(S)->Option<int>,f:Encoding,x:State<S>,y:State<S>,a:Seq<Event>) -> bool
    decreases a.len(),
{
    (x.cfg.private)(Process::SecondClient)==(y.cfg.private)(Process::SecondClient)
        && if a.len()==0 {read::returned(r)(x) && read::returned(r)(y)} else {
            !read::returned(r)(x) && !read::returned(r)(y) && process_step(y.cfg.net,a[0])==traffic::observation(f,process_step(x.cfg.net,a[0]),2)
                && matching_steps(m,r,f,read::next(m,x,a[0]),read::next(m,y,a[0]),a.drop_first())
        }
}
pub open spec fn suffix<S>(m:Program<S>,r:spec_fn(S)->Option<int>,n:Notice,f:Encoding,x:State<S>,y:State<S>,a:Seq<Event>) -> bool {
    let u=asm::drive(m,x,a);let v=asm::drive(m,y,a);let c=Process::SecondClient;
    crate::fork_delivery::service_prefix(m,x,a) && crate::fork_delivery::service_prefix(m,y,a)
        && matching_steps(m,r,f,x,y,a) && issued_pair(u,v,n,f) && r((u.cfg.private)(c)).is_some() && (u.cfg.private)(c)==(v.cfg.private)(c)
        && (!legal_returns(5,r((u.cfg.private)(c)).unwrap()) || !legal_returns(2,r((v.cfg.private)(c)).unwrap()))
}
proof fn replay_second<S>(m:Program<S>,r:spec_fn(S)->Option<int>,n:Notice,f:Encoding,p:Service<S>,j:nat,y:State<S>)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(read::service_step(m),p),!wait::uses(p,evidence(alpha(n))),
        wait::pending_before(read::returned(r),p),read::returned(r)(p.states.last()),j<=p.actions.len(),issued_pair(p.states[j as int],y,n,f),
        traffic::recipient_use(m,f),distinct_weak_names(m),
    ensures suffix(m,r,n,f,p.states[j as int],y,p.actions.skip(j as int)),
    decreases p.actions.len()-j,
{
    let x=p.states[j as int];let a=p.actions.skip(j as int);
    if j==p.actions.len() {
        assert(a =~= Seq::<Event>::empty());
        let v=r((x.cfg.private)(Process::SecondClient)).unwrap();
        if legal_returns(5,v) && legal_returns(2,v) {
            let (ops,xs)=choose|ops:Seq<Op>,xs:Seq<int>| #[trigger] crate::legal(ops,xs,5,v);
            let (ps,ys)=choose|ps:Seq<Op>,ys:Seq<int>| #[trigger] crate::legal(ps,ys,2,v);
            crate::conditional_history_contradiction(ops,xs,ps,ys,v);
        }
    } else {
        let e=p.actions[j as int];let u=p.states[j as int+1];let z=read::next(m,y,e);
        assert(read::service_step(m)(x,e,u));assert(!evidence(alpha(n))(x,e,u));replay_second_step(m,n,f,x,y,e,u);
        assert(a[0]==e && a.drop_first() =~= p.actions.skip(j as int+1));
        replay_second(m,r,n,f,p,j+1,z);
    }
}

// If A supplied a held-value sample on the source, the same named live
// replica holds it at the same cut on the target, even across ordinary repairs.
pub proof fn transfer_sample<S>(m:Program<S>,n:Notice,f:Encoding,p:Service<S>,y:State<S>,j:nat,k:nat,r:Replica)
    requires p.states.len()==p.actions.len()+1,j<=k<p.states.len(),r!=Replica::R3,
        wait::valid_edges(read::service_step(m),p),!wait::uses(p,evidence(alpha(n))),issued_pair(p.states[j as int],y,n,f),
        traffic::recipient_use(m,f),distinct_weak_names(m),
    ensures ({let x=p.states[j as int];let v=(p.states[k as int].cfg.net.locals)(r);let a=p.actions.skip(j as int);
        fork::held_in_replay(m,x.cfg,a,v) && fork::held_in_replay(m,y.cfg,a,v)}),
    decreases k-j,
{
    if j<k {
        let a=p.actions[j as int];let x=p.states[j as int];let u=p.states[j as int+1];
        assert(read::service_step(m)(x,a,u));assert(!evidence(alpha(n))(x,a,u));replay_second_step(m,n,f,x,y,a,u);
        transfer_sample(m,n,f,p,read::next(m,y,a),j+1,k,r);
        assert(p.actions.skip(j as int)[0]==a && p.actions.skip(j as int).drop_first() =~= p.actions.skip(j as int+1));
    }
}

// A is invoked at the actual issued alpha cut. This requires a fair
// continuation of that cut; it does not require a fair run withholding ACKs.
pub proof fn common_second_service<S>(m:Program<S>,r:spec_fn(S)->Option<int>,n:Notice,f:Encoding,
    x:State<S>,y:State<S>,run:fair::Runnable,e:fair::Run<S>) -> (p:Service<S>)
    requires issued_pair(x,y,n,f),read::issued_to_majority(x),!read::returned(r)(x),
        model::eventual(m,r,x,run),fair::execution(m,e,x),fair::fair(e,run),traffic::recipient_use(m,f),distinct_weak_names(m),
        !wait::needs_class(read::service_step(m),read::returned(r),x,evidence(alpha(n))),
    ensures wait::first_return(read::service_step(m),read::returned(r),x,p),!wait::uses(p,evidence(alpha(n))),
        suffix(m,r,n,f,x,y,p.actions),
{
    assert(nb::within(read::prefix_step(m),read::at_state(x),x,0));
    assert(read::reached(m,x,x));
    let st=read::service_step(m);let d=read::returned(r);
    assert(model::due(model::Caller::Second,x));
    assert(exists|i:nat| #[trigger] model::published(model::Caller::Second,m,r)((e.state)(i)));
    let i=choose|i:nat| #[trigger] model::published(model::Caller::Second,m,r)((e.state)(i));
    fair::initial_steps(m,x,e,i);let b=fair::initial_block(e,i);
    assert(d(b.states.last()));nb::from_path(st,d,b,0);
    assert(nb::possible(st,d,x));nb::first_response_iff(st,d,x);assert(wait::can_finish(st,d,x));
    if forall|p:Service<S>| #[trigger] wait::first_return(st,d,x,p) ==> wait::uses(p,evidence(alpha(n))) {
        assert(wait::needs_class(st,d,x,evidence(alpha(n))));
    }
    let path=choose|p:Service<S>| #[trigger] wait::first_return(st,d,x,p) && !wait::uses(p,evidence(alpha(n)));
    replay_second(m,r,n,f,path,0,y);assert(path.actions.skip(0) =~= path.actions);path
}
}
