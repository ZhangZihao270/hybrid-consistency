// A source-side audit of the finite SR1 return. No target state, client
// result, weak-order decoder or assumed survivor equivalence occurs here.
use vstd::prelude::*;
use crate::{Branch,Replica,checkpoint::*,delivery::*,protocol::*};
use crate::first_assembly::*;
use crate::first_splice as s;
use crate::first_causality as cause;
use crate::first_mailbox as mail;
use crate::first_schedule::reference;
use crate::first_service_loss as loss;
use crate::independent_read::{self as read,State};
use crate::promotion_wait::{self as wait,Relation};
use crate::read_call::{Event,Program};
use crate::read_nonblocking as nb;

verus! {

pub open spec fn rival(b:Fork) -> nat {if b.branch==Branch::Alpha {0} else {1}}
// Slot 2 contains the actual notice issued before C1 submits. The other
// seed is the original weak transfer, only counted here when it installs a
// different shared value at R3. A redundant overwrite alone is insufficient.
pub open spec fn promotion<S>(b:Fork) -> Relation<State<S>,Event> {
    |x:State<S>,a:Event,y:State<S>| (a==Action::<Wire>::Deliver(2) && x.cfg.net.pending.get(2)==Some(packet_for(b,2))) ||
        (a==Action::<Wire>::Deliver(rival(b)) && x.cfg.net.pending.get(rival(b))==Some(packet_for(b,rival(b)))
            && (x.cfg.net.locals)(Replica::R3)!=(y.cfg.net.locals)(Replica::R3))
}
pub open spec fn crossing<S>(b:Fork,x:State<S>,a:Event) -> bool {
    match a {Action::Deliver(id)=>x.cfg.net.pending.contains_key(id) && x.cfg.net.pending[id].from==at(Replica::R3)
        && x.cfg.net.pending[id].to==at(crate::origin(b.branch)),_=>false}
}
pub open spec fn boundary<S>(b:Fork) -> Relation<State<S>,Event> {
    |x:State<S>,a,y| crossing(b,x,a) || cause::changes_sample(b,x,y)
}
pub open spec fn weak_free<S>(m:Program<S>,b:Fork) -> Relation<State<S>,Event> {
    nb::ordinary(mail::active_step(m),promotion(b))
}
// Native allocation on actual sends. Different payloads, recipient choices,
// multiple packets and local clocks are allowed. Single-use is per prefix.
pub open spec fn named<S>(p:Service<S>,l:Lanes) -> bool {
    (forall|j:int| 0<=j<p.actions.len() ==> match #[trigger] p.actions[j] {
        Action::Send(id,q)=>id>5 && id!=11 && id!=12 && q.from is At && l.get(id)==Some(q.from->At_0),_=>true})
    && (forall|i:int,j:int| 0<=i<j<p.actions.len() && (#[trigger] p.actions[i]) is Send && (#[trigger] p.actions[j]) is Send
        ==> p.actions[i]->Send_0!=p.actions[j]->Send_0)
}
pub proof fn envelope_lifetimes<S>(m:Program<S>,p:Service<S>,b:Fork,l:Lanes)
    requires cause::returning(m,b,p),named(p,l),
    ensures cause::one_envelope(s::record(p,0)),
{
    let t=s::record(p,0);
    assert forall|i:int,j:int| 0<=i<j<t.len() && s::slot((#[trigger] t[i]).action).is_some()
        && s::slot(t[i].action)==s::slot((#[trigger] t[j]).action) implies t[i].action is Send && t[j].action is Deliver by {
        let a=p.actions[i];let d=p.actions[j];let id=s::slot(a).unwrap();
        if a is Deliver {
            let x=p.states[i];assert(mail::active_step(m)(x,a,p.states[i+1]));assert(!p.states[i+1].cfg.net.pending.contains_key(id));
            let k=if d is Send {j as nat} else {
                let y=p.states[j];assert(mail::active_step(m)(y,d,p.states[j+1]));assert(y.cfg.net.pending.contains_key(id));
                mail::last_send_after(m,p,(i+1) as nat,j as nat,id,y.cfg.net.pending[id])
            };
            assert(i<k && p.actions[k as int] is Send && p.actions[k as int]->Send_0==id);
            assert(id>5);assert(!p.states[0].cfg.net.pending.contains_key(id));
            let h=mail::last_send(m,p,i as nat,id,x.cfg.net.pending[id]);
            assert(p.actions[h as int]->Send_0!=p.actions[k as int]->Send_0);
        }
    }
}
proof fn new_packet<S>(m:Program<S>,b:Fork,l:Lanes,p:Service<S>,i:int,id:nat,q:Packet<Wire>)
    requires cause::returning(m,b,p),named(p,l),0<=i<p.actions.len(),p.states[i].cfg.net.pending.get(id)==Some(q),
        p.states[0].cfg.net.pending.get(id)!=Some(q),
    ensures id>5,id!=11,id!=12,q.from is At,l.get(id)==Some(q.from->At_0),
        q.from==at(crate::origin(b.branch)) || q.from==at(Replica::R3),
{
    let j=mail::last_send(m,p,i as nat,id,q);assert(p.actions[j as int]==Action::Send(id,q));
    crate::first_causality::prefix_mask(m,p,j);assert(live(p.states[j as int].cfg.net,q.from));
}
pub proof fn no_boundary_gives_routing<S>(m:Program<S>,b:Fork,l:Lanes,p:Service<S>)
    requires lanes_ok(l),cause::returning(m,b,p),named(p,l),!wait::uses(p,promotion(b)),!wait::uses(p,boundary(b)),
    ensures separable(s::record(p,0),b,l),loss::stable(b,p),
{
    let t=s::record(p,0);let r=crate::origin(b.branch);let z=reference(m,b,5);
    assert forall|i:int| 0<=i<p.actions.len() implies !cause::changes_sample(b,#[trigger] p.states[i],p.states[i+1]) by {
        assert(!boundary(b)(p.states[i],p.actions[i],p.states[i+1]));
    }
    assert forall|i:int| 0<=i<t.len() implies cause::routed(#[trigger] t[i],b,l) by {
        let a=p.actions[i];let x=p.states[i];let y=p.states[i+1];let e=t[i];
        assert(mail::active_step(m)(x,a,y));assert(!mail::posted(m)(x));
        crate::first_causality::prefix_mask(m,p,i as nat);assert(!x.cfg.net.second_started);
        assert(!boundary(b)(x,a,y) && !promotion(b)(x,a,y));assert(live(x.cfg.net,e.actor));
        match a {
            Action::Send(id,q)=>{assert(q.from is At && l.get(id)==Some(q.from->At_0));},
            Action::Deliver(id)=>{
                let q=x.cfg.net.pending[id];assert(x.cfg.net.pending.get(id)==Some(q));
                if z.cfg.net.pending.get(id)==Some(q) {
                    if id==rival(b) {
                        cause::stable_value(m,p,b,i as nat,Replica::R3);
                        assert(q==packet_for(b,id) && (y.cfg.net.locals)(Replica::R3)!=first_value(b));
                    } else if id==2 {assert(q==packet_for(b,2));}
                    else {assert(id==3 || id==4 || id==5);}
                } else {new_packet(m,b,l,p,i,id,q);}
            },
            _=>{},
        }
    }
    envelope_lifetimes(m,p,b,l);cause::routing_allows_preparation(t,b,l);
}
pub open spec fn rc_interface<S>(m:Program<S>,b:Fork,l:Lanes,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    forall|p:Service<S>| #[trigger] cause::returning(m,b,p) && !wait::uses(p,promotion(b))
        ==> named(p,l) && cause::source_shape(s::record(p,0),b,answers)
}
// On every genuine weak-free completion, identify the point at which a
// required boundary event first makes service possible without another.
pub open spec fn indispensable<S>(m:Program<S>,b:Fork,class:Relation<State<S>,Event>,st:Relation<State<S>,Event>) -> bool {
    let d=mail::posted(m);let x=reference(m,b,5);
    wait::needs_class(st,d,x,class) && (forall|p:Service<S>| #[trigger] wait::first_return(st,d,x,p) ==>
        exists|j:int| 0<=j<p.actions.len() && #[trigger] nb::unlocks(st,d,class,p.states[j],p.actions[j],p.states[j+1]))
}
pub(crate) proof fn certify_dependency<S>(m:Program<S>,b:Fork,st:Relation<State<S>,Event>,class:Relation<State<S>,Event>)
    requires wait::needs_class(st,mail::posted(m),reference(m,b,5),class),
    ensures indispensable(m,b,class,st),
{
    let x=reference(m,b,5);let d=mail::posted(m);let plain=nb::ordinary(st,class);
    if nb::possible(plain,d,x) {
        let p=nb::to_path(plain,d,x,choose|k:nat| #[trigger] nb::within(plain,d,x,k));
        assert forall|i:int| 0<=i<p.actions.len() implies st(p.states[i],#[trigger] p.actions[i],p.states[i+1])
            && !class(p.states[i],p.actions[i],p.states[i+1]) by {assert(plain(p.states[i],p.actions[i],p.states[i+1]));}
        let w=choose|w:Service<S>| #[trigger] wait::first_return(st,d,x,w);assert(!d(x));
        assert(wait::first_return(st,d,x,p));assert(!wait::uses(p,class));
    }
    assert forall|p:Service<S>| #[trigger] wait::first_return(st,d,x,p) implies
        exists|j:int| 0<=j<p.actions.len() && #[trigger] nb::unlocks(st,d,class,p.states[j],p.actions[j],p.states[j+1]) by {
        let j=nb::find_unlock(st,d,class,p,0);
    }
}
pub proof fn classify<S>(m:Program<S>,b:Fork,l:Lanes,answers:spec_fn(Packet<Wire>)->bool)
    requires lanes_ok(l),rc_interface(m,b,l,answers),loss::obstruction(m,b,l,answers,promotion(b)),
    ensures indispensable(m,b,promotion(b),mail::active_step(m)) || indispensable(m,b,boundary(b),weak_free(m,b)),
{
    let st=mail::active_step(m);let d=mail::posted(m);let x=reference(m,b,5);let e=promotion(b);let plain=weak_free(m,b);
    if wait::needs_class(st,d,x,e) {certify_dependency(m,b,st,e);} else {
        let w=choose|p:Service<S>| #[trigger] cause::returning(m,b,p) && !wait::uses(p,e);
        assert forall|i:int| 0<=i<w.actions.len() implies plain(w.states[i],#[trigger] w.actions[i],w.states[i+1])
            by {assert(st(w.states[i],w.actions[i],w.states[i+1]));}
        assert(wait::first_return(plain,d,x,w));
        assert forall|p:Service<S>| #[trigger] wait::first_return(plain,d,x,p) implies wait::uses(p,boundary(b)) by {
            assert forall|i:int| 0<=i<p.actions.len() implies st(p.states[i],#[trigger] p.actions[i],p.states[i+1])
                && !e(p.states[i],p.actions[i],p.states[i+1]) by {assert(plain(p.states[i],p.actions[i],p.states[i+1]));}
            assert(cause::returning(m,b,p));assert(!loss::usable(b,p,l,answers));
            if !wait::uses(p,boundary(b)) {no_boundary_gives_routing(m,b,l,p);}
        }
        certify_dependency(m,b,plain,boundary(b));
    }
}

// Identify the actual sender and the type of state change at a boundary
// crossing on a weak-free path. Strong receipts alone do not change cells.
pub proof fn explain_boundary<S>(m:Program<S>,b:Fork,l:Lanes,p:Service<S>,j:nat)
    requires cause::returning(m,b,p),named(p,l),!wait::uses(p,promotion(b)),j<p.actions.len(),
        boundary(b)(p.states[j as int],p.actions[j as int],p.states[j as int+1]),
    ensures ({let a=p.actions[j as int];let x=p.states[j as int];
        (crossing(b,x,a) && a is Deliver && exists|i:int| 0<=i<j && #[trigger] p.actions[i]==Action::Send(a->Deliver_0,x.cfg.net.pending[a->Deliver_0])
            && live(p.states[i].cfg.net,at(Replica::R3)))
        || exists|r:Replica| {let v=(p.states[j as int+1].cfg.net.locals)(r);
            cause::quorum(b,r) && (#[trigger] (x.cfg.net.locals)(r))!=v
                && (a==Action::Local(r,Wire::Copy(v)) || (a is Deliver && x.cfg.net.pending[a->Deliver_0].path==Path::Weak
                    && x.cfg.net.pending[a->Deliver_0].to==at(r) && x.cfg.net.pending[a->Deliver_0].input==Wire::Copy(v)))}}),
{
    let x=p.states[j as int];let y=p.states[j as int+1];let a=p.actions[j as int];let z=p.states[0];
    assert(mail::active_step(m)(x,a,y));assert(!promotion(b)(x,a,y));
    if crossing(b,x,a) {
        let id=a->Deliver_0;let q=x.cfg.net.pending[id];assert(z.cfg.net.pending.get(id)!=Some(q));
        let i=mail::last_send(m,p,j,id,q);
    } else {
        let r=choose|r:Replica| cause::quorum(b,r) && #[trigger] (x.cfg.net.locals)(r)!=(y.cfg.net.locals)(r);
        let v=(y.cfg.net.locals)(r);assert(local_input(x.cfg.net,a,r)==Some(Wire::Copy(v)));
    }
}

}
