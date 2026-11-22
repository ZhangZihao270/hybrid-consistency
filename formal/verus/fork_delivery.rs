// The native allocator and the packets held through both original reads.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::*};
use crate::first_assembly::*;
use crate::first_causality as cause;
use crate::first_pair as pair;
use crate::first_service_loss as loss;
use crate::first_splice::{self as s,Tape,Observation,after,plays,pick};
use crate::fork_dependencies as dep;
use crate::independent_read::{self as read,State};
use crate::ordinary_service::apply;
use crate::read_call::{Event,Program};
use crate::fair_read as fair;
use crate::survivors::after_crash;
use crate::sr1_majorities as maj;

verus! {

pub open spec fn service_prefix<S>(m:Program<S>,t:State<S>,a:Seq<Event>) -> bool
    decreases a.len(),
{
    if a.len()==0 {true} else {
        let y=read::next(m,t,a[0]);read::service_step(m)(t,a[0],y) && service_prefix(m,y,a.drop_first())
    }
}
// In addition to physical enabledness, every replayed send respects
// the original's monitored slot ownership and reservation rules.
pub proof fn replay_allocated<S>(m:Program<S>,p:Service<S>,j:nat,t:State<S>)
    requires p.states.len()==p.actions.len()+1,j<=p.actions.len(),crate::promotion_wait::valid_edges(read::service_step(m),p),
        read::covers(p.states[j as int],t.cfg),p.states[j as int].owners==t.owners,t.reserved.subset_of(p.states[j as int].reserved),
    ensures service_prefix(m,t,read::retained_actions(p,j)),drive(m,t,read::retained_actions(p,j)).cfg==loss::final_cfg(m,t.cfg,read::retained_actions(p,j)),
    decreases p.actions.len()-j,
{
    if j<p.actions.len() {
        let x=p.states[j as int];let a=p.actions[j as int];let y=p.states[j as int+1];let e=process_step(x.cfg.net,a);
        assert(read::service_step(m)(x,a,y));read::project_step(m,m,x,y,t.cfg,a);
        if e.actor==Process::FirstClient {assert(x.reserved.subset_of(y.reserved));replay_allocated(m,p,j+1,t);}
        else {
            let u=read::next(m,t,a);
            if let Action::Send(id,q)=a {assert(!x.reserved.contains(id) && !t.reserved.contains(id));}
            assert(read::service_step(m)(t,a,u));assert(u.reserved.subset_of(y.reserved));replay_allocated(m,p,j+1,u);
            assert(read::retained_actions(p,j).drop_first() =~= read::retained_actions(p,j+1));
        }
    }
}
proof fn member_forward(t:Tape,p:Process,k:int)
    requires 0<=k<t.len(),t[k].actor==p,
    ensures pick(t,p,true).contains(t[k]),
    decreases k,
{
    if k>0 {let u=t.drop_first();member_forward(u,p,k-1);let v=pick(u,p,true);let i=choose|i:int| 0<=i<v.len() && v[i]==t[k];
        if t[0].actor==p {assert(pick(t,p,true)[i+1]==t[k]);} else {assert(pick(t,p,true)[i]==t[k]);}}
    else {assert(pick(t,p,true)[0]==t[k]);}
}
pub(crate) proof fn pending_send<S>(m:Program<S>,x:State<S>,t:Tape,id:nat,q:Packet<Wire>)
    requires plays(m,x,t),x.cfg.net.pending.get(id)==Some(q) ||
        (exists|i:int| 0<=i<t.len() && (#[trigger] t[i]).action==Action::Send(id,q)),
        forall|i:int| 0<=i<t.len() ==> !((#[trigger] t[i]).action==Action::<Wire>::Deliver(id) && t[i].incoming==Some(q)),
    ensures after(m,x,t).cfg.net.pending.get(id)==Some(q),
    decreases t.len(),
{
    if t.len()>0 {
        let u=t.drop_first();let a=t[0].action;let y=read::next(m,x,a);
        if y.cfg.net.pending.get(id)!=Some(q) {
            let j=choose|i:int| 0<=i<t.len() && (#[trigger] t[i]).action==Action::Send(id,q);
            assert(j>0);assert(u[j-1].action==Action::Send(id,q));
        }
        assert forall|i:int| 0<=i<u.len() implies !((#[trigger] u[i]).action==Action::<Wire>::Deliver(id) && u[i].incoming==Some(q))
            by {assert(u[i]==t[i+1]);}
        pending_send(m,y,u,id,q);
    }
}
pub(crate) proof fn actor_received<S>(m:Program<S>,x:State<S>,t:Tape,i:int)
    requires plays(m,x,t),0<=i<t.len(),t[i].incoming.is_some(),
    ensures t[i].actor==t[i].incoming.unwrap().to,
    decreases i,
{
    if i>0 {actor_received(m,read::next(m,x,t[0].action),t.drop_first(),i-1);}
}
pub open spec fn delayed_reply<S>(x:State<S>,b:Fork,answers:spec_fn(Packet<Wire>)->bool) -> bool {
    exists|i:nat| #[trigger] x.cfg.net.pending.contains_key(i) && {let q=x.cfg.net.pending[i];
        q.from==at(maj::missing(b)) && q.to==Process::FirstClient && answers(q)}
}
pub proof fn before_stop<S>(m:Program<S>,first:spec_fn(S)->int,l:Lanes,b:Fork,ta:Tape,tb:Tape,answers:spec_fn(Packet<Wire>)->bool)
    requires loss::original_read(m,first,l,b,ta,tb,answers),pair::sources(m,l,b.notice,ta,tb),
    ensures delayed_reply(fork_end(m,l,b,ta,tb),b,answers),
        fork_end(m,l,b,ta,tb).cfg.net.pending.get(dep::rival(b))==Some(packet_for(b,dep::rival(b))),
{
    let x=root(m,l,Some(b));let t=cause::tape(b,ta,tb);let r=maj::missing(b);let site=pick(t,at(r),true);let c=Process::FirstClient;
    assert(cause::replied(t,r,answers));
    let (i,j)=choose|i:int,j:int| 0<=i<j<site.len() && cause::intake_at(#[trigger] site[i],r) && cause::answer_at(#[trigger] site[j],r,answers);
    s::picked(t,at(r),true,j);let k=choose|k:int| 0<=k<t.len() && t[k]==site[j];let a=t[k].action;let id=a->Send_0;let q=a->Send_1;
    assert forall|h:int| 0<=h<t.len() implies !((#[trigger] t[h]).action==Action::<Wire>::Deliver(id) && t[h].incoming==Some(q)) by {
        if t[h].incoming==Some(q) {
            actor_received(m,x,t,h);member_forward(t,c,h);
            let caller=pick(t,c,true);let j=choose|j:int| 0<=j<caller.len() && caller[j]==t[h];
            assert(caller[j].incoming.unwrap().from==at(crate::origin(b.branch)) || caller[j].incoming.unwrap().from==at(Replica::R3));
        }
    }
    pending_send(m,x,t,id,q);let src=if b.branch==crate::Branch::Alpha {ta} else {tb};let u=work_pair(ta,tb,b.notice);let v=remaining(src,b);
    s::concat(m,x,u,v);assert(after(m,x,t)==fork_end(m,l,b,ta,tb));
    pair::outside_work(m,l,b.notice,ta,tb,Some(b));pair::finish(m,l,b,ta,tb);
    let rival=dep::rival(b);let y=after(m,x,u);let z=after(m,y,v);
    assert(pair::their_slots(l).complement().contains(rival) && tail_slots(b,l).complement().contains(rival));
    assert(z.cfg.net.pending.get(rival)==y.cfg.net.pending.get(rival) && y.cfg.net.pending.get(rival)==x.cfg.net.pending.get(rival));
}
pub proof fn held_at_return<S>(m:Program<S>,x:State<S>,a:Seq<Event>,id:nat,q:Packet<Wire>)
    requires service_prefix(m,x,a),x.cfg.net.pending.get(id)==Some(q),!live(x.cfg.net,q.to),
    ensures drive(m,x,a).cfg.net.pending.get(id)==Some(q),
    decreases a.len(),
{
    if a.len()>0 {
        let e=a[0];let y=read::next(m,x,e);
        assert(e!=Action::<Wire>::Deliver(id));assert(y.cfg.net.pending.get(id)==Some(q));
        held_at_return(m,y,a.drop_first(),id,q);
    }
}

pub proof fn original_packets<S>(m:Program<S>,first:spec_fn(S)->int,l:Lanes,b:Fork,ta:Tape,tb:Tape,answers:spec_fn(Packet<Wire>)->bool,
    issued:State<S>,suffix:Seq<Event>)
    requires loss::original_read(m,first,l,b,ta,tb,answers),pair::sources(m,l,b.notice,ta,tb),
        fork_end(m,l,b,ta,tb).cfg.net.pending.submap_of(issued.cfg.net.pending),issued.cfg.net.first_stopped,issued.cfg.net.r3_crashed,
        service_prefix(m,issued,suffix),
    ensures delayed_reply(drive(m,issued,suffix),b,answers),
        drive(m,issued,suffix).cfg.net.pending.get(dep::rival(b))==Some(packet_for(b,dep::rival(b))),
{
    let z=fork_end(m,l,b,ta,tb);before_stop(m,first,l,b,ta,tb,answers);
    let id=choose|i:nat| #[trigger] z.cfg.net.pending.contains_key(i) && {let q=z.cfg.net.pending[i];
        q.from==at(maj::missing(b)) && q.to==Process::FirstClient && answers(q)};
    let q=z.cfg.net.pending[id];let rival=dep::rival(b);assert(issued.cfg.net.pending.get(id)==Some(q));
    held_at_return(m,issued,suffix,id,q);assert(issued.cfg.net.pending.get(rival)==Some(packet_for(b,rival)));
    held_at_return(m,issued,suffix,rival,packet_for(b,rival));
}

proof fn still_live<S>(m:Program<S>,x:State<S>,e:fair::Run<S>,k:nat)
    requires after_crash(x.cfg.net),fair::execution(m,e,x),
    ensures after_crash((e.state)(k).cfg.net),
    decreases k,
{
    if k>0 {still_live(m,x,e,(k-1) as nat);assert(read::service_step(m)((e.state)((k-1) as nat),(e.action)((k-1) as nat),(e.state)(k)));}
}
pub open spec fn actual_delivery<S>(e:fair::Run<S>,j:nat,id:nat,q:Packet<Wire>) -> bool {
    (e.action)(j)==Action::<Wire>::Deliver(id) && (e.state)(j).cfg.net.pending.get(id)==Some(q)
}
proof fn earliest_delivery<S>(m:Program<S>,x:State<S>,e:fair::Run<S>,id:nat,k:nat) -> (j:nat)
    requires fair::execution(m,e,x),x.cfg.net.pending.contains_key(id),(e.action)(k)==Action::<Wire>::Deliver(id),
    ensures j<=k,actual_delivery(e,j,id,x.cfg.net.pending[id]),
    decreases k,
{
    if exists|h:nat| h<k && (#[trigger] (e.action)(h))==Action::<Wire>::Deliver(id) {
        let h=choose|h:nat| h<k && (#[trigger] (e.action)(h))==Action::<Wire>::Deliver(id);earliest_delivery(m,x,e,id,h)
    } else {fair::unconsumed(m,x,e,0,k,id);k}
}
// Applies at a returned original checkpoint. Discharging each scheduling
// duty in a closed suffix supplies a fair continuation with genuine receipts.
pub proof fn fair_release<S>(m:Program<S>,x:State<S>,run:fair::Runnable,reg:crate::read_nonblocking::Region<State<S>>) -> (e:fair::Run<S>)
    requires after_crash(x.cfg.net),reg(x),fair::closed(m,reg),forall|s:State<S>| reg(s) ==> #[trigger] fair::schedulable(m,run,s),
    ensures fair::execution(m,e,x),fair::fair(e,run),forall|j:nat| #[trigger] after_crash((e.state)(j).cfg.net),
        forall|id:nat| #[trigger] x.cfg.net.pending.contains_key(id) && live(x.cfg.net,x.cfg.net.pending[id].to)
            ==> exists|j:nat| #[trigger] actual_delivery(e,j,id,x.cfg.net.pending[id]),
{
    let e=fair::fair_extension(m,run,reg,x);let net=fair::physical(e);
    assert forall|j:nat| #[trigger] after_crash((e.state)(j).cfg.net) by {still_live(m,x,e,j);}
    assert forall|id:nat| #[trigger] x.cfg.net.pending.contains_key(id) && live(x.cfg.net,x.cfg.net.pending[id].to)
        implies exists|j:nat| #[trigger] actual_delivery(e,j,id,x.cfg.net.pending[id]) by {
        let to=x.cfg.net.pending[id].to;assert((net.state)(0).pending.contains_key(id));
        let k=choose|k:nat| k>=0 && ((#[trigger] (net.action)(k))==Action::<Wire>::Deliver(id) || !live((net.state)(k),to));
        assert(after_crash((e.state)(k).cfg.net));assert(live((net.state)(k),to));earliest_delivery(m,x,e,id,k);
    }
    e
}

}
