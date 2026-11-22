// Does receiving a message into private survivor state actually matter to
// this first read? Move the recipient's work after publication whenever no
// outward send/receive dependency prevents that permutation.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::*};
use crate::first_assembly::*;
use crate::first_causality as cause;
use crate::first_splice::{self as s,Tape,Observation,after,plays,pick};
use crate::fork_dependencies as dep;
use crate::first_mailbox as mail;
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Program,Event};
use crate::read_nonblocking as nb;

verus! {

pub open spec fn ordinary<S>(m:Program<S>,b:Fork) -> wait::Relation<State<S>,Event> {
    nb::ordinary(dep::weak_free(m,b),dep::boundary(b))
}
spec fn ordinary_input(b:Fork,e:Observation) -> bool {
    let q=e.incoming;
    let input=match e.action {Action::Local(_,w)=>Some(w),
        Action::Deliver(_) if q.is_some() && q.unwrap().path==Path::Weak => Some(q.unwrap().input),_=>None};
    !(q.is_some() && q.unwrap().from==at(Replica::R3) && q.unwrap().to==at(crate::origin(b.branch)))
        && !(e.actor is At && cause::quorum(b,e.actor->At_0) && input.is_some() && input.unwrap() is Copy
            && e.own_local!=Some(input.unwrap()->Copy_0))
}
proof fn local_test<S>(m:Program<S>,b:Fork,x:State<S>,a:Event,y:State<S>)
    requires mail::active_step(m)(x,a,y),
    ensures ordinary(m,b)(x,a,y)==ordinary_input(b,process_step(x.cfg.net,a)),
{
    let e=process_step(x.cfg.net,a);
    assert forall|r:Replica| e.actor!=at(r) implies #[trigger] (x.cfg.net.locals)(r)==(y.cfg.net.locals)(r) by {
        assert(local_input(x.cfg.net,a,r).is_none());
    }
    if e.actor is At {let r=e.actor->At_0;
        assert((y.cfg.net.locals)(r)==match local_input(x.cfg.net,a,r) {Some(w)=>cell((x.cfg.net.locals)(r),w),None=>(x.cfg.net.locals)(r)});
    }
}
proof fn ordinary_tape_returns<S>(m:Program<S>,b:Fork,x:State<S>,t:Tape)
    requires plays(m,x,t),mail::posted(m)(after(m,x,t)),forall|i:int| 0<=i<t.len() ==> ordinary_input(b,#[trigger] t[i]),
    ensures nb::possible(ordinary(m,b),mail::posted(m),x),
    decreases t.len(),
{
    let st=ordinary(m,b);let d=mail::posted(m);
    if t.len()==0 {assert(nb::within(st,d,x,0));}
    else {
        let a=t[0].action;let y=read::next(m,x,a);let u=t.drop_first();assert(ordinary_input(b,t[0]));
        local_test(m,b,x,a,y);
        assert forall|j:int| 0<=j<u.len() implies ordinary_input(b,#[trigger] u[j]) by {assert(u[j]==t[j+1]);}
        ordinary_tape_returns(m,b,y,u);nb::predecessor(st,d,x,a,y);
    }
}
pub open spec fn later_receipt<S>(p:Service<S>,r:Replica,i:int,j:int) -> bool {
    let a=p.actions[i];let d=p.actions[j];let e=process_step(p.states[j].cfg.net,d);
    a is Send && a->Send_1.from==at(r) && d==Action::<Wire>::Deliver(a->Send_0)
        && e.incoming==Some(a->Send_1) && e.actor==a->Send_1.to && e.actor!=at(r)
}
// For any completion using only ordinary events after the pivotal receipt,
// a genuine packet sent by its recipient subsequently reaches another actor.
// This is a causal communication requirement, independent of payload meaning.
pub proof fn private_receipt_needs_outgoing_delivery<S>(m:Program<S>,b:Fork,x:State<S>,a:Event,y:State<S>,p:Service<S>)
    requires dep::crossing(b,x,a),nb::unlocks(dep::weak_free(m,b),mail::posted(m),dep::boundary(b),x,a,y),
        wait::first_return(ordinary(m,b),mail::posted(m),y,p),
        cause::one_envelope(seq![process_step(x.cfg.net,a)]+s::record(p,0)),
    ensures exists|i:int,j:int| 0<=i<j<p.actions.len() && #[trigger] later_receipt(p,crate::origin(b.branch),i,j),
{
    let r=crate::origin(b.branch);let who=at(r);let gate=process_step(x.cfg.net,a);let suffix=s::record(p,0);let t=seq![gate]+suffix;
    let st=ordinary(m,b);let d=mail::posted(m);assert(mail::active_step(m)(x,a,y));assert(gate.actor==who && a is Deliver);
    assert forall|i:int| 0<=i<p.actions.len() implies mail::active_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        && ordinary_input(b,suffix[i]) by {
        assert(st(p.states[i],p.actions[i],p.states[i+1]));local_test(m,b,p.states[i],p.actions[i],p.states[i+1]);
    }
    s::recorded(m,p,0);assert(t.drop_first() =~= suffix);assert(plays(m,x,t) && d(after(m,x,t)));
    if s::reorderable(t,who,false) {
        let u=pick(t,who,false);let v=pick(t,who,true);s::factor_group(m,x,t,who,false);s::concat(m,x,u,v);let z=after(m,x,u);
        assert forall|i:int| 0<=i<v.len() implies (#[trigger] v[i]).actor==who by {s::picked(t,who,true,i);}
        s::frame(m,z,v,site(r),ISet::full());assert(site(r).complement().contains(Process::FirstClient));assert(d(z));
        assert forall|i:int| 0<=i<u.len() implies ordinary_input(b,#[trigger] u[i]) by {
            s::picked(t,who,false,i);let j=choose|j:int| 0<=j<t.len() && t[j]==u[i];
            assert(j>0);assert(suffix[j-1]==u[i]);assert(ordinary_input(b,suffix[j-1]));
        }
        ordinary_tape_returns(m,b,x,u);
    }
    let (h,k)=choose|h:int,k:int| 0<=h<k<t.len() && (#[trigger] t[h]).actor==who && (#[trigger] t[k]).actor!=who
        && !s::independent(t[h],t[k]);
    assert(s::slot(t[h].action).is_some() && s::slot(t[h].action)==s::slot(t[k].action));
    assert(t[h].action is Send && t[k].action is Deliver);assert(h>0);
    let i=h-1;let j=k-1;let id=t[h].action->Send_0;let q=p.states[j].cfg.net.pending[id];
    assert(p.actions[i]==t[h].action && p.actions[j]==Action::<Wire>::Deliver(id));
    assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));assert(!p.states[i].cfg.net.pending.contains_key(id));
    assert(mail::active_step(m)(p.states[j],p.actions[j],p.states[j+1]));assert(p.states[j].cfg.net.pending.get(id)==Some(q));
    let sent=mail::last_send_after(m,p,i as nat,j as nat,id,q);
    if sent!=i {assert(h<sent+1<k);assert(t[sent as int+1].action==p.actions[sent as int]);assert(s::slot(t[sent as int+1].action)==Some(id));}
    assert(sent==i);assert(later_receipt(p,r,i,j));
}

}
