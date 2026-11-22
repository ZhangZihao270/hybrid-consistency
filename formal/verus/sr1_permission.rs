// One witness for the receipt-erasure limitation on the beta SR1 reference.
// Permission reports only local SR1 participation and is usable from either
// other replica. This is a first-call fragment, not a complete hybrid SMR.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*, protocol::*};
use crate::fair_read as fair;
use crate::first_assembly::{self as asm, Lanes, Service};
use crate::coupled_traffic as coupling;
use crate::coupled_traffic::sampled_reply as sample;
use crate::coupled_construction as construction;
use crate::first_splice::{self as tape, Tape, Observation};
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::{self as first,reference};
use crate::fork_dependencies as dep;
use crate::hybrid_transparency as trans;
use crate::independent_read::{self as read,State};
use crate::read_call::{Event,Program};
use crate::read_nonblocking as nb;
use crate::promotion_wait as wait;

verus! {

pub type Memory = (Control,bool,Set<nat>);
pub open spec fn permit(from:Replica) -> Packet<Wire> {
    Packet{from:at(from),to:at(Replica::R1),path:Path::Strong,input:Wire::Peer(0)}
}
pub open spec fn is_permit(q:Packet<Wire>) -> bool { q==permit(Replica::R2) || q==permit(Replica::R3) }
pub open spec fn accepts(s:Memory,e:ProcessStep<int,Wire>) -> bool {
    match e.action {
        Action::Send(id,q) => !s.2.contains(id) && if is_permit(q) {
            s.0.requested && id==(if q.from==at(Replica::R3) {9nat} else {10nat})
        } else if first_reply(q) {
            id==dispatch::request_id(q.from->At_0)+3 && s.0.requested && e.own_local==Some(q.input->Reply_0)
                && (q.from!=at(Replica::R1) || s.1)
        } else {
            (invocation_packet(q) || (notice_to(q,q.to) && id==2)) && permits_step(s.0,e)
        },
        Action::Strong(Process::FirstClient) | Action::StopFirstClient => s.0.finished,
        Action::Strong(Process::At(Replica::R1)) | Action::Local(Replica::R1,_) =>
            !(s.0.requested && s.1 && !s.0.answered_first),
        _=>true,
    }
}
pub open spec fn update(s:Memory,e:ProcessStep<int,Wire>) -> Memory {
    let ctrl=change_control(s.0,e);
    let publish=e.actor==Process::FirstClient && e.incoming.is_some() && first_reply(e.incoming.unwrap())
        && ctrl.replies_from.len()>=2;
    (Control{finished:ctrl.finished || publish,..ctrl},
        s.1 || (e.incoming.is_some() && is_permit(e.incoming.unwrap())),
        match e.action {Action::Send(id,_)=>s.2.insert(id),_=>s.2})
}
pub open spec fn machine() -> Program<Memory> {
    LocalProtocol{initial:|_p| (initial_control(),false,Set::empty()),accept:|s,e| accepts(s,e),done:|s:Memory| s.0.finished,
        update:|s,e|update(s,e)}
}
pub open spec fn setup() -> Seq<Event> {
    seq![Action::<Wire>::Deliver(3),Action::Deliver(5),Action::Send(9,permit(Replica::R3)),
        dispatch::offer(Replica::R3,2),Action::Deliver(8)]
}
pub open spec fn cut(n:Notice,j:nat) -> State<Memory>
    decreases j,
{
    if j==0 {reference(machine(),beta(n),5)} else {read::next(machine(),cut(n,(j-1) as nat),setup()[j-1])}
}
pub open spec fn empty_audit() -> trans::PacketAudit { |_q:Packet<Wire>| false }
pub open spec fn plain(n:Notice) -> crate::promotion_wait::Relation<State<Memory>,Event> {
    nb::ordinary(trans::without_weak(machine(),beta(n),empty_audit()),dep::boundary(beta(n)))
}
spec fn locked(x:State<Memory>) -> bool {
    let c=(x.cfg.private)(Process::FirstClient);
    x.cfg.net.unavailable==Some(Replica::R2) && !(x.cfg.private)(at(Replica::R1)).1 && !c.0.finished
        && c.0.replies_from.subset_of(set![Replica::R3])
        && forall|id:nat| #[trigger] x.cfg.net.pending.contains_key(id) ==> {
            let q=x.cfg.net.pending[id];
            q!=permit(Replica::R2) && (first_reply(q) ==> q.from==at(Replica::R3))
        }
}
// Even a genuine weak copy or confirmation may run. Only an authentic
// participation message addressed to the waiting responder can open this cut.
proof fn still_locked(x:State<Memory>,a:Event,y:State<Memory>)
    requires locked(x),mail::active_step(machine())(x,a,y),
        !(a is Deliver && x.cfg.net.pending.get(a->Deliver_0)==Some(permit(Replica::R3))),
    ensures locked(y),
{
    let m=machine();let c=Process::FirstClient;let e=process_step(x.cfg.net,a);
    if e.incoming.is_some() {
        let id=a->Deliver_0;assert(x.cfg.net.pending.contains_key(id));assert(e.incoming.unwrap()!=permit(Replica::R2));
    }
    if a is Send {
        let q=a->Send_1;assert(live(x.cfg.net,q.from));
        assert(q!=permit(Replica::R2));if first_reply(q) {assert(q.from==at(Replica::R3));}
    }
    let reporters=change_control((x.cfg.private)(c).0,e).replies_from;
    if e.actor==c {
        assert(reporters.subset_of(set![Replica::R3]));
        if reporters.contains(Replica::R3) {assert(reporters =~= set![Replica::R3]);}
        else {assert(reporters =~= Set::<Replica>::empty());}
        assert(reporters.len()<=1);
    }
    assert forall|id:nat| #[trigger] y.cfg.net.pending.contains_key(id) implies {
        let q=y.cfg.net.pending[id];q!=permit(Replica::R2) && (first_reply(q)==>(q.from==at(Replica::R3)))
    } by {
        if !(a is Send && a->Send_0==id) {assert(x.cfg.net.pending.get(id)==y.cfg.net.pending.get(id));}
    }
}
pub open spec fn peer_receipt() -> wait::Relation<State<Memory>,Event> {
    mail::receipt_of(|q:Packet<Wire>| q==permit(Replica::R3))
}
proof fn no_return_while_held(st:wait::Relation<State<Memory>,Event>,x:State<Memory>,k:nat)
    requires locked(x),forall|s:State<Memory>,a:Event,t:State<Memory>| #[trigger] st(s,a,t)
        ==> mail::active_step(machine())(s,a,t) && !peer_receipt()(s,a,t),
    ensures !nb::within(st,mail::posted(machine()),x,k),
    decreases k,
{
    let d=mail::posted(machine());
    if nb::within(st,d,x,k) {
        let (a,y)=choose|a:Event,y:State<Memory>| #[trigger] st(x,a,y) && nb::within(st,d,y,(k-1) as nat);
        assert(!peer_receipt()(x,a,y));still_locked(x,a,y);no_return_while_held(st,y,(k-1) as nat);
    }
}
proof fn setup_reachable(n:Notice,j:nat)
    requires j<=5,dispatch::launched(machine(),beta(n)),
    ensures first::reached_in(machine(),beta(n))(cut(n,j)),
{
    let m=machine();let b=beta(n);
    // All five guarded actions occur after the enabled fanout and before
    // the tested receipt. R2 was already down on this reference.
    dispatch::launch_cut(m,b);
    assert forall|k:nat| k<5 implies trans::without_weak(m,b,empty_audit())(cut(n,k),#[trigger] setup()[k as int],cut(n,k+1)) by {
        assert(k==0 || k==1 || k==2 || k==3 || k==4);
        reveal_with_fuel(cut,6);reveal_with_fuel(memory,7);
    }
    reach_setup_steps(n,j);
}
proof fn reach_setup_steps(n:Notice,j:nat)
    requires j<=5,first::reached_in(machine(),beta(n))(reference(machine(),beta(n),5)),
        forall|k:nat| k<5 ==> trans::without_weak(machine(),beta(n),empty_audit())(cut(n,k),#[trigger] setup()[k as int],cut(n,k+1)),
    ensures first::reached_in(machine(),beta(n))(cut(n,j)),
    decreases j,
{
    if j>0 {
        let k=(j-1) as nat;reach_setup_steps(n,k);let m=machine();let base=reference(m,beta(n),0);
        let x=cut(n,k);let a=setup()[k as int];let y=cut(n,j);assert(read::prefix_step(m)(x,a,y));
        let bound=choose|h:nat| #[trigger] nb::within(read::prefix_step(m),read::at_state(x),base,h);
        fair::append_reachable(m,base,x,a,y,bound);
    }
}

// For either live potential grantor and any own cell or saved weak state,
// receiving the ordinary request is the entire send guard. No replica
// membership count, weak value, order, or confirmation is transmitted.
pub proof fn permission_content_and_guard(from:Replica,s:Control,old:bool,cell_value:int,issued:Set<nat>)
    requires from!=Replica::R1,
    ensures ({let id=if from==Replica::R3 {9nat} else {10nat};let q=permit(from);let e=ProcessStep{actor:at(from),action:Action::Send(id,q),own_local:Some(cell_value),incoming:None};
        accepts((s,old,issued),e)==(s.requested && !issued.contains(id)) && q.input==Wire::Peer(0)
            && update((s,old,issued),e)==(s,old,issued.insert(id))}),
        ({let e=ProcessStep{actor:at(Replica::R1),action:Action::<Wire>::Deliver(9),own_local:Some(cell_value),incoming:Some(permit(from))};
            accepts((s,old,issued),e) && update((s,old,issued),e)==(s,true,issued)}),
{}

// Actual source for the first refused input. The copy and confirmation
// remain pending at publication. This establishes failure of local_service
// for this fragment; it makes no assertion of whole-SMR H, O, T or A.
pub proof fn ordinary_permission_breaks_local_service(n:Notice)
    ensures !trans::local_service(machine(),beta(n),empty_audit()),
        wait::needs_class(mail::active_step(machine()),mail::posted(machine()),cut(n,5),peer_receipt()),
        ({let m=machine();let x=cut(n,5);let g=Action::<Wire>::Deliver(9);let y=read::next(m,x,g);
          let r=dispatch::offer(Replica::R1,2);let u=read::next(m,y,r);let end=read::next(m,u,Action::Deliver(6));
          first::reached_in(m,beta(n))(x) && x.cfg.net.pending.get(9)==Some(permit(Replica::R3))
          && nb::unlocks(trans::without_weak(m,beta(n),empty_audit()),mail::posted(m),dep::boundary(beta(n)),x,g,y)
          && process_step(x.cfg.net,r)==process_step(y.cfg.net,r) && enabled(x.cfg.net,r)
          && !accepts((x.cfg.private)(at(Replica::R1)),process_step(x.cfg.net,r)) && plain(n)(y,r,u)
          && plain(n)(u,Action::Deliver(6),end)
          && mail::posted(m)(end) && (end.cfg.private)(Process::FirstClient).0.reply==Some(2)
          && end.cfg.net.pending.get(2)==Some(packet_for(beta(n),2)) && end.cfg.net.pending.get(1)==Some(packet_for(beta(n),1))}),
{
    let m=machine();let b=beta(n);let d=mail::posted(m);
    assert(dispatch::initiates(m)) by {
        assert forall|i:int| 0<=i<3 implies {let e=#[trigger] dispatch::initial_sends()[i];
            (m.accept)(memory(m,e.actor,dispatch::initial_sends(),i as nat),e)} by {
            assert(i==0 || i==1 || i==2);reveal_with_fuel(memory,4);
        }
        assert forall|k:nat| k<=3 implies !(m.done)(#[trigger] memory(m,Process::FirstClient,dispatch::initial_sends(),k))
            by {assert(k==0 || k==1 || k==2 || k==3);reveal_with_fuel(memory,4);}
    }
    assert(dispatch::weak_open(m,b));dispatch::fanout_and_weak_open_launch(m,b);setup_reachable(n,5);
    let x=cut(n,5);let g=Action::<Wire>::Deliver(9);let y=read::next(m,x,g);let r=dispatch::offer(Replica::R1,2);
    let u=read::next(m,y,r);let end=read::next(m,u,Action::Deliver(6));
    reveal_with_fuel(cut,6);reveal_with_fuel(memory,7);
    assert(locked(x));assert(trans::without_weak(m,b,empty_audit())(x,g,y) && dep::crossing(b,x,g));
    assert(plain(n)(y,r,u) && plain(n)(u,Action::<Wire>::Deliver(6),end));
    assert(d(end));assert(nb::within(plain(n),d,end,0));assert(nb::within(plain(n),d,u,1));assert(nb::within(plain(n),d,y,2));
    assert forall|k:nat| ! #[trigger] nb::within(plain(n),d,x,k) by {no_return_while_held(plain(n),x,k);}
    assert(nb::unlocks(trans::without_weak(m,b,empty_audit()),d,dep::boundary(b),x,g,y));
    let active=mail::active_step(m);let held=nb::ordinary(active,peer_receipt());
    assert(nb::within(active,d,end,0));assert(nb::within(active,d,u,1));assert(nb::within(active,d,y,2));assert(nb::within(active,d,x,3));
    nb::first_response_iff(active,d,x);
    assert forall|p:Service<Memory>| #[trigger] wait::first_return(active,d,x,p) implies wait::uses(p,peer_receipt()) by {
        if !wait::uses(p,peer_receipt()) {
            assert forall|j:int| 0<=j<p.actions.len() implies held(p.states[j],#[trigger] p.actions[j],p.states[j+1]) by {
                assert(active(p.states[j],p.actions[j],p.states[j+1]));}
            nb::from_path(held,d,p,0);no_return_while_held(held,x,p.actions.len());
        }
    }
}

// Fair progress on every continuation of the tested call, including ones
// that deliver the rival copy or the weak confirmation before publication.
pub open spec fn pending_call(n:Notice,x:State<Memory>) -> bool {
    let net=x.cfg.net;let r=(x.cfg.private)(at(Replica::R1));let third=(x.cfg.private)(at(Replica::R3));
    let c=(x.cfg.private)(Process::FirstClient);let b=beta(n);
    net.unavailable==Some(Replica::R2) && !net.r3_crashed && !net.first_stopped && !net.second_started
        && r.0.requested && r.1==!net.pending.contains_key(9)
        && r.0.answered_first==net.pending.contains_key(6) && r.0.answered_first==r.2.contains(6)
        && (r.0.answered_first ==> r.1) && (!r.0.answered_first ==> !x.reserved.contains(6)) && !x.owners.contains_key(6)
        && third.2.contains(9) && third.2.contains(8) && third.2.contains(2)
        && !c.0.finished && c.0.replies_from==set![Replica::R3]
        && forall|id:nat| #[trigger] net.pending.contains_key(id) ==> {let q=net.pending[id];
            ((id==1 || id==2 || id==4) && q==packet_for(b,id))
            || (id==9 && q==permit(Replica::R3)) || (id==6 && first_reply(q) && q.from==at(Replica::R1))}
}
proof fn initial_pending(n:Notice)
    ensures pending_call(n,cut(n,5)),
{
    reveal_with_fuel(cut,6);reveal_with_fuel(memory,7);
}
spec fn finished_call(x:State<Memory>) -> bool {
    x.cfg.net.unavailable==Some(Replica::R2) && !x.cfg.net.r3_crashed && !x.cfg.net.second_started
        && (x.cfg.private)(at(Replica::R1)).0.answered_first && mail::posted(machine())(x)
}
spec fn rank(x:State<Memory>) -> nat {
    let r=(x.cfg.private)(at(Replica::R1));
    if !r.1 {4} else if r.0.answered_first {1} else if x.cfg.net.pending.contains_key(2) {3} else {2}
}
spec fn advances(x:State<Memory>,a:Event) -> bool {
    if rank(x)==4 {a==Action::Deliver(9)} else if rank(x)==1 {a==Action::Deliver(6)}
    else {process_step(x.cfg.net,a).actor==at(Replica::R1)}
}
proof fn pending_step(n:Notice,x:State<Memory>,a:Event,y:State<Memory>)
    requires pending_call(n,x), read::service_step(machine())(x,a,y),
    ensures finished_call(y) || (pending_call(n,y) && rank(y)<=rank(x) && (advances(x,a) ==> rank(y)<rank(x))),
{
    let m=machine();let b=beta(n);let e=process_step(x.cfg.net,a);let r=at(Replica::R1);let c=Process::FirstClient;
    if a is Send {let q=a->Send_1;assert(a->Send_0==6 && first_reply(q) && q.from==r);}
    if a is Deliver {
        let id=a->Deliver_0;assert(x.cfg.net.pending.contains_key(id));let q=x.cfg.net.pending[id];
        if q.to==c {
            assert(id==6 && q.from==r && first_reply(q));
            assert((x.cfg.private)(c).0.replies_from.insert(Replica::R1) =~= set![Replica::R3,Replica::R1]);
            assert(set![Replica::R3,Replica::R1].len()==2);
        }
        if q.to==r {assert(id==2 || id==9);}
    }
    assert forall|id:nat| #[trigger] y.cfg.net.pending.contains_key(id) implies {let q=y.cfg.net.pending[id];
        ((id==1 || id==2 || id==4) && q==packet_for(b,id))
        || (id==9 && q==permit(Replica::R3)) || (id==6 && first_reply(q) && q.from==r)} by {
        if !(a is Send && a->Send_0==id) {assert(y.cfg.net.pending.get(id)==x.cfg.net.pending.get(id));}
    }
    if 1<rank(x)<4 && e.actor==r {assert(a is Send || a==Action::<Wire>::Deliver(2));}
}

pub open spec fn runnable() -> fair::Runnable { |net:crate::read_call::Net,p| live(net,p) }
proof fn pending_at(n:Notice,e:fair::Run<Memory>,k:nat)
    requires fair::execution(machine(),e,cut(n,5)),forall|h:nat| ! #[trigger] mail::posted(machine())((e.state)(h)),
    ensures pending_call(n,(e.state)(k)),
    decreases k,
{
    if k==0 {initial_pending(n);}
    else {let j=(k-1) as nat;pending_at(n,e,j);assert(read::service_step(machine())((e.state)(j),(e.action)(j),(e.state)(k)));
        pending_step(n,(e.state)(j),(e.action)(j),(e.state)(k));}
}
proof fn nonincreasing(n:Notice,e:fair::Run<Memory>,i:nat,j:nat)
    requires i<=j,fair::execution(machine(),e,cut(n,5)),forall|h:nat| ! #[trigger] mail::posted(machine())((e.state)(h)),
    ensures rank((e.state)(j))<=rank((e.state)(i)),
    decreases j-i,
{
    if j>i {let h=(j-1) as nat;nonincreasing(n,e,i,h);pending_at(n,e,h);
        assert(read::service_step(machine())((e.state)(h),(e.action)(h),(e.state)(j)));
        pending_step(n,(e.state)(h),(e.action)(h),(e.state)(j));}
}
pub proof fn every_fair_continuation_returns(n:Notice,e:fair::Run<Memory>)
    requires fair::execution(machine(),e,cut(n,5)),fair::fair(e,runnable()),
    ensures exists|j:nat| #[trigger] mail::posted(machine())((e.state)(j)),
{
    if forall|j:nat| ! #[trigger] mail::posted(machine())((e.state)(j)) {
        let net=fair::physical(e);let f=|i:nat| rank((e.state)(i));let i=crate::ordinary_service::minimum(f,0,0);
        let x=(e.state)(i);pending_at(n,e,i);
        let j=if f(i)==4 || f(i)==1 {
            let id=if f(i)==4 {9nat} else {6nat};assert(x.cfg.net.pending.contains_key(id));assert((net.state)(i).pending.contains_key(id));
            let k=choose|k:nat| k>=i && ((#[trigger] (net.action)(k))==Action::<Wire>::Deliver(id)
                || !live((net.state)(k),(net.state)(i).pending[id].to));
            pending_at(n,e,k);assert((e.action)(k)==Action::<Wire>::Deliver(id));k
        } else {
            let r=at(Replica::R1);
            assert forall|h:nat| h>=i implies #[trigger] runnable()((net.state)(h),r) by {pending_at(n,e,h);}
            assert(crate::progress::continuously_runnable(net,runnable(),i,r));
            choose|k:nat| k>=i && #[trigger] crate::progress::runs_at(net,k,r)
        };
        pending_at(n,e,j);nonincreasing(n,e,i,j);assert(f(i)<=f(j));assert(advances((e.state)(j),(e.action)(j)));
        assert(read::service_step(machine())((e.state)(j),(e.action)(j),(e.state)(j+1)));
        pending_step(n,(e.state)(j),(e.action)(j),(e.state)(j+1));assert(f(i)<=f(j+1));
    }
}
proof fn fair_at(n:Notice,x:State<Memory>) -> (e:fair::Run<Memory>)
    requires pending_call(n,x) || finished_call(x),
    ensures fair::execution(machine(),e,x),fair::fair(e,runnable()),mail::honest(machine(),e),
{
    let m=machine();let reg=|s:State<Memory>|pending_call(n,s) || finished_call(s);let run=runnable();
    assert(fair::closed(m,reg)) by {
        assert forall|s:State<Memory>,a:Event,t:State<Memory>| reg(s) && #[trigger] read::service_step(m)(s,a,t)
            implies reg(t) by {if pending_call(n,s) {pending_step(n,s,a,t);}}
    }
    assert forall|s:State<Memory>| reg(s) implies #[trigger] fair::schedulable(m,run,s) by {
        assert forall|d:fair::Duty| #[trigger] fair::can_schedule(m,run,s,d) by {
            let net=s.cfg.net;let one=at(Replica::R1);let c=Process::FirstClient;
            let a=match d {
                fair::Duty::Packet(id) if net.pending.contains_key(id) && live(net,net.pending[id].to) => Action::Deliver(id),
                fair::Duty::Turn(p) if live(net,p) => {
                    if p==c {Action::ClientInput(c,Wire::Peer(1))}
                    else if p==one && pending_call(n,s) && (s.cfg.private)(one).1 && !(s.cfg.private)(one).0.answered_first {
                        dispatch::offer(Replica::R1,(net.locals)(Replica::R1))
                    } else {Action::Strong(p)}
                },
                _=>Action::Strong(at(Replica::R3)),
            };
            let t=read::next(m,s,a);assert(read::service_step(m)(s,a,t) && fair::discharged(d,run,net,a));
            let path=crate::promotion_wait::Path{states:seq![s,t],actions:seq![a]};
            assert forall|i:int| 0<=i<path.actions.len() implies read::service_step(m)(path.states[i],#[trigger] path.actions[i],path.states[i+1]) by {assert(i==0);}
            assert(fair::discharged(d,run,path.states[0].cfg.net,path.actions[0]));assert(fair::turn(m,run,s,d,path));
        }
    }
    let e=fair::fair_extension(m,run,reg,x);
    assert forall|i:nat| #[trigger] (e.action)(i)==Action::<Wire>::StopFirstClient implies mail::posted(m)((e.state)(i)) by {
        assert(read::service_step(m)((e.state)(i),(e.action)(i),(e.state)(i+1)));
    }
    e
}
pub proof fn fair_opportunity_and_release(n:Notice)
    ensures mail::fair_opportunity(machine(),runnable(),cut(n,5)),
        ({let x=cut(n,5);let m=machine();let y=read::next(m,x,Action::Deliver(9));
            let end=read::next(m,read::next(m,y,dispatch::offer(Replica::R1,2)),Action::Deliver(6));
            mail::fair_opportunity(m,runnable(),end)}),
{
    let m=machine();let x=cut(n,5);let y=read::next(m,x,Action::Deliver(9));let u=read::next(m,y,dispatch::offer(Replica::R1,2));
    let end=read::next(m,u,Action::Deliver(6));
    ordinary_permission_breaks_local_service(n);initial_pending(n);
    pending_step(n,x,Action::Deliver(9),y);assert(pending_call(n,y));
    pending_step(n,y,dispatch::offer(Replica::R1,2),u);assert(pending_call(n,u));
    pending_step(n,u,Action::Deliver(6),end);
    fair_at(n,x);fair_at(n,end);
}

// The no-await test holds throughout this pending region. The next useful
// action is always the ordinary grant, R1's sampled send, or C1's receipt.
proof fn finish_without_promotion(n:Notice,x:State<Memory>)
    requires pending_call(n,x),
    ensures nb::possible(trans::without_weak(machine(),beta(n),empty_audit()),mail::posted(machine()),x),
    decreases rank(x),
{
    let m=machine();let b=beta(n);let d=mail::posted(m);let st=trans::without_weak(m,b,empty_audit());
    let a=if rank(x)==4 {Action::Deliver(9)} else if rank(x)==1 {Action::Deliver(6)}
        else {dispatch::offer(Replica::R1,(x.cfg.net.locals)(Replica::R1))};
    let y=read::next(m,x,a);
    assert(st(x,a,y));assert(advances(x,a));pending_step(n,x,a,y);
    if d(y) {assert(nb::within(st,d,y,0));} else {finish_without_promotion(n,y);}
    nb::predecessor(st,d,x,a,y);
}
pub proof fn all_pending_states_can_defer_weak_work(n:Notice)
    ensures wait::no_await(mail::active_step(machine()),mail::posted(machine()),
        |x:State<Memory>|pending_call(n,x),trans::weak_work(beta(n),empty_audit())),
{
    let m=machine();let b=beta(n);let d=mail::posted(m);let st=trans::without_weak(m,b,empty_audit());
    let effect=trans::weak_work(b,empty_audit());let active=mail::active_step(m);
    assert forall|x:State<Memory>| #[trigger] pending_call(n,x) implies !wait::needs_class(active,d,x,effect) by {
        finish_without_promotion(n,x);
        let p=nb::to_path(st,d,x,choose|k:nat| #[trigger] nb::within(st,d,x,k));
        assert forall|i:int| 0<=i<p.actions.len() implies active(p.states[i],#[trigger] p.actions[i],p.states[i+1])
            && !effect(p.states[i],p.actions[i],p.states[i+1]) by {assert(st(p.states[i],p.actions[i],p.states[i+1]));}
        assert(wait::first_return(active,d,x,p) && !wait::uses(p,effect));
    }
}
proof fn pending_prefix(n:Notice,p:Service<Memory>,j:nat)
    requires wait::first_return(mail::active_step(machine()),mail::posted(machine()),cut(n,5),p),j<p.actions.len(),
    ensures pending_call(n,p.states[j as int]),
    decreases j,
{
    if j==0 {initial_pending(n);}
    else {let h=(j-1) as nat;pending_prefix(n,p,h);
        assert(mail::active_step(machine())(p.states[h as int],p.actions[h as int],p.states[j as int]));
        pending_step(n,p.states[h as int],p.actions[h as int],p.states[j as int]);}
}
pub proof fn every_return_uses_a_held_value(n:Notice,p:Service<Memory>)
    requires wait::first_return(mail::active_step(machine()),mail::posted(machine()),cut(n,5),p),
    ensures ({let v=(p.states.last().cfg.private)(Process::FirstClient).0.reply;
        v.is_some() && exists|j:int| 0<=j<p.actions.len() && #[trigger] p.actions[j]==dispatch::offer(Replica::R1,v.unwrap())
            && (p.states[j].cfg.net.locals)(Replica::R1)==v.unwrap()}),
{
    let m=machine();let k=(p.actions.len()-1) as nat;pending_prefix(n,p,k);let x=p.states[k as int];let a=p.actions[k as int];
    let end=p.states.last();assert(mail::active_step(m)(x,a,end));assert(mail::posted(m)(end));assert(a==Action::<Wire>::Deliver(6));
    let q=x.cfg.net.pending[6];let v=q.input->Reply_0;
    assert(first_reply(q) && q.from==at(Replica::R1));assert((end.cfg.private)(Process::FirstClient).0.reply==Some(v));
    assert(!cut(n,5).cfg.net.pending.contains_key(6)) by {reveal_with_fuel(cut,6);}
    let j=mail::last_send(m,p,k,6,q);let s=p.states[j as int];
    assert(mail::active_step(m)(s,p.actions[j as int],p.states[j as int+1]));
    assert(p.actions[j as int]==dispatch::offer(Replica::R1,v) && (s.cfg.net.locals)(Replica::R1)==v);
}


// Exercise the previously indispensable permission on both originals. Only
// the reply to C1 is resampled from R3's own cell. Grant and receipt are real.
pub open spec fn grant_control(s:Memory,t:Memory) -> bool {s.0.requested==t.0.requested && s.2==t.2}
pub proof fn grant_has_common_control(v:int)
    ensures coupling::sender_control(machine(),sample(v),|s,t|grant_control(s,t),|_e:Observation|true,v),
        coupling::recipient_use(machine(),sample(v)), construction::keeps_reports(sample(v)),
{
    let m=machine();let f=sample(v);
    construction::common_peer_inputs(m,v);
    assert forall|s:Memory,t:Memory,e:Observation| #[trigger] grant_control(s,t) && e.actor==at(Replica::R3)
        && crate::confirmation::transport_event(e) && coupling::preparation_input(e) && #[trigger] (m.accept)(s,e)
        implies {let h=coupling::observation(f,e,v);
            (m.accept)(t,h) && grant_control((m.update)(s,e),(m.update)(t,h))} by {
        let n=choose|n:crate::read_call::Net| enabled(n,e.action) && #[trigger] process_step(n,e.action)==e;
        if e.incoming.is_some() {
            assert(e.incoming.unwrap().to==e.actor);
            assert(coupling::image(f,e.incoming.unwrap())==e.incoming.unwrap());
        }
    }
}
pub open spec fn replica_preparation(b:Fork) -> Tape {
    let a=Replica::R1;let h=Replica::R2;let g=Replica::R3;let v=first_value(b);let grant=permit(g);
    seq![dispatch::intake(a,2),dispatch::intake(h,5),dispatch::intake(g,v),
        ProcessStep{actor:at(g),action:Action::Send(9,grant),own_local:Some(v),incoming:None},
        ProcessStep{actor:at(a),action:Action::Deliver(9),own_local:Some(2),incoming:Some(grant)},
        dispatch::report(a,2),dispatch::report(h,5),dispatch::report(g,v)]
}
pub open spec fn collect(b:Fork) -> Tape {
    let c=Process::FirstClient;let i=first::origin_slot(b);
    seq![ProcessStep{actor:c,action:Action::Deliver(i),incoming:Some(packet_for(b,i)),own_local:None},
        ProcessStep{actor:c,action:Action::Deliver(8),incoming:Some(packet_for(b,8)),own_local:None}]
}
pub open spec fn permission_names(l:Lanes) -> bool {
    asm::lanes_ok(l) && l.get(6)!=Some(Replica::R3) && l.get(7)!=Some(Replica::R3)
}
// Insert R3's grant send and its delivery between the three intakes and
// the three reports of the manuscript schedule.
spec fn original_cut(j:nat) -> nat {
    if j<=3 {5+j} else if j<=5 {8} else {3+j}
}
spec fn phase_memory(b:Fork,p:Process,j:nat) -> Memory {
    let k=original_cut(j);
    let c=expected_control(b,p,k);
    let ids=match p {
        Process::FirstClient=>set![3nat,4,5],
        Process::At(Replica::R1) if j>=6=>set![6nat],
        Process::At(Replica::R2) if j>=7=>set![7nat],
        Process::At(Replica::R3)=>if j<4 {set![2nat]} else if j<8 {set![2nat,9]} else {set![2nat,9,8]},
        _=>Set::empty(),
    };
    (Control{finished:p==Process::FirstClient && j>=10,..c},p==at(Replica::R1) && j>=5,ids)
}
spec fn phase(l:Lanes,b:Fork,j:nat) -> State<Memory> {
    let x=construction::root(machine(),l,b);let net=state_after(b,original_cut(j));
    State{cfg:crate::ordinary_service::Configuration{
        net:crate::read_call::Net{pending:if j==4 {net.pending.insert(9,permit(Replica::R3))} else {net.pending},..net},
        private:|p:Process|phase_memory(b,p,j)},
        reserved:if j<6 {Set::empty()} else if j<7 {set![6nat]} else if j<8 {set![6nat,7]} else {set![6nat,7,8]},..x}
}
proof fn phase_start(l:Lanes,b:Fork)
    ensures phase(l,b,0)==construction::root(machine(),l,b),
{
    let x=construction::root(machine(),l,b);
    assert(phase(l,b,0).cfg.private =~= x.cfg.private) by {
        assert forall|p:Process| #[trigger] phase_memory(b,p,0)==(x.cfg.private)(p) by {reveal_with_fuel(memory,6);}
    }
}
proof fn phase_edge(l:Lanes,b:Fork,i:nat)
    requires permission_names(l),i<10,
    ensures ({let s=phase(l,b,i);let e=(replica_preparation(b)+collect(b))[i as int];
        tape::moves(e.action) && process_step(s.cfg.net,e.action)==e
            && read::service_step(machine())(s,e.action,phase(l,b,i+1))}),
{
    prefix_index(i as int);let s=phase(l,b,i);let e=(replica_preparation(b)+collect(b))[i as int];
    let u=read::next(machine(),s,e.action);let z=phase(l,b,i+1);
    assert(process_step(s.cfg.net,e.action)==e);
    assert(u.cfg.net.pending =~= z.cfg.net.pending);
    assert(u.cfg.net.locals =~= z.cfg.net.locals);
    assert(u.cfg.private =~= z.cfg.private) by {
        assert forall|p:Process| #[trigger] (u.cfg.private)(p)==phase_memory(b,p,i+1) by {
            if p==e.actor {assert((s.cfg.private)(p)==phase_memory(b,p,i));}
        }
    }
    assert(u.reserved =~= z.reserved);
}
proof fn phase_interval(l:Lanes,b:Fork,lo:nat,hi:nat)
    requires permission_names(l),lo<=hi<=10,
    ensures ({let t=(replica_preparation(b)+collect(b)).subrange(lo as int,hi as int);let s=phase(l,b,lo);
        tape::plays(machine(),s,t) && tape::after(machine(),s,t)==phase(l,b,hi)}),
    decreases hi-lo,
{
    if lo<hi {let t=replica_preparation(b)+collect(b);phase_edge(l,b,lo);phase_interval(l,b,lo+1,hi);
        assert(t.subrange(lo as int,hi as int).drop_first() =~= t.subrange(lo as int+1,hi as int));}
}
proof fn source_preparation(l:Lanes,n:Notice)
    requires permission_names(l),
    ensures tape::plays(machine(),construction::root(machine(),l,alpha(n)),replica_preparation(alpha(n))),
{
    let b=alpha(n);phase_start(l,b);phase_interval(l,b,0,8);
    assert((replica_preparation(b)+collect(b)).subrange(0,8) =~= replica_preparation(b));
}
proof fn native_launch(l:Lanes,b:Fork)
    requires asm::lanes_ok(l),
    ensures asm::prefix(machine(),asm::entry(machine(),l),asm::boot(Some(b)),true),
        asm::drive(machine(),asm::entry(machine(),l),asm::boot(Some(b)))==construction::root(machine(),l,b),
{
    let m=machine();
    assert(dispatch::initiates(m)) by {reveal_with_fuel(memory,4);
        assert forall|j:int| 0<=j<3 implies {let e=#[trigger] dispatch::initial_sends()[j];
            (m.accept)(memory(m,e.actor,dispatch::initial_sends(),j as nat),e)} by {assert(j==0 || j==1 || j==2);}
        assert forall|j:nat| j<=3 implies !(m.done)(#[trigger] memory(m,Process::FirstClient,dispatch::initial_sends(),j))
            by {assert(j==0 || j==1 || j==2 || j==3);}
    }
    assert(dispatch::weak_open(m,b)) by {reveal_with_fuel(memory,3);}
    asm::launch(m,l,Some(b));
}
proof fn gather(l:Lanes,b:Fork)
    requires permission_names(l),tape::plays(machine(),construction::root(machine(),l,b),replica_preparation(b)),
    ensures construction::actual_first(machine(),|s:Memory|s.0.reply.unwrap(),l,b,replica_preparation(b),collect(b)),
        crate::coupled_reads::client_change(construction::prepared(machine(),l,b,replica_preparation(b)),
            construction::first_end(machine(),l,b,replica_preparation(b),collect(b)),collect(b)),
        crate::first_pair::before_issue(machine(),construction::first_end(machine(),l,b,replica_preparation(b),collect(b)),l),
        crate::first_pair::c1_protected(construction::prepared(machine(),l,b,replica_preparation(b))),
        (construction::prepared(machine(),l,b,replica_preparation(b)).cfg.private)(at(Replica::R1)).1,
{
    let m=machine();let t=replica_preparation(b);let c=collect(b);let x=construction::root(m,l,b);let z=phase(l,b,8);let end=phase(l,b,10);
    native_launch(l,b);phase_start(l,b);phase_interval(l,b,0,8);phase_interval(l,b,8,10);
    assert((t+c).subrange(0,8) =~= t);assert((t+c).subrange(8,10) =~= c);
    asm::native_prefix(m,x,t,true);asm::native_prefix(m,z,c,true);
    asm::prefix_concat(m,asm::entry(m,l),asm::boot(Some(b)),asm::actions(t),true);
    asm::prefix_concat(m,asm::entry(m,l),asm::boot(Some(b))+asm::actions(t),asm::actions(c),true);
    assert(construction::respondents(t)) by {
        assert forall|r:Replica| #[trigger] construction::answered(t,r) by {
            let i=if r==Replica::R1 {0int} else if r==Replica::R2 {1int} else {2int};
            assert(crate::first_causality::intake_at(t[i],r) && crate::first_causality::answer_at(t[i+5],r,crate::sr1_contract::replies()));
        }
    }
    let id=first::origin_slot(b);let other=if b.branch==crate::Branch::Alpha {6nat} else {7nat};
    assert(end.cfg.net.pending.get(other)==Some(packet_for(b,other)));
    assert(first_reply(c[0].incoming.unwrap()) && c[0].incoming.unwrap().from==at(crate::origin(b.branch)));
    assert(first_reply(c[1].incoming.unwrap()) && c[1].incoming.unwrap().from==at(Replica::R3));
    assert(c.drop_first().drop_first() =~= Seq::<Observation>::empty());
    assert(crate::first_causality::pending_inputs(m,(z.cfg.private)(Process::FirstClient),c))
        by {reveal_with_fuel(crate::first_causality::pending_inputs,3);}
    assert(crate::fork_delivery::delayed_reply(end,b,crate::sr1_contract::replies()));
    assert forall|j:int| 0<=j<c.len() implies {let e=#[trigger] c[j];e.actor==Process::FirstClient
        && (e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3))} by {assert(j==0 || j==1);}
    assert forall|i:nat| #[trigger] end.cfg.net.pending.get(i)==(if crate::coupled_reads::takes(c,i){None}else{z.cfg.net.pending.get(i)})
        && (crate::coupled_reads::takes(c,i) ==> z.cfg.net.pending.contains_key(i) && z.cfg.net.pending[i].to==Process::FirstClient) by {
        assert(crate::coupled_reads::takes(c,i)==(i==id || i==8)) by {
            if crate::coupled_reads::takes(c,i) {let j=choose|j:int|0<=j<c.len() && (#[trigger] c[j]).action==Action::<Wire>::Deliver(i);assert(j==0 || j==1);}
            else {assert(c[0].action==Action::<Wire>::Deliver(id) && c[1].action==Action::<Wire>::Deliver(8));}
        }
    }
    assert(end.cfg.net.locals =~= z.cfg.net.locals);
}
proof fn coupled_preparations(l:Lanes,n:Notice)
    requires permission_names(l),
    ensures ({ let m=machine();let a=alpha(n);let b=beta(n);let ta=replica_preparation(a);let tb=replica_preparation(b);
        tape::plays(m,construction::root(m,l,a),ta) && tape::plays(m,construction::root(m,l,b),tb)
            && coupling::paired(construction::prepared(m,l,a,ta),construction::prepared(m,l,b,tb),n,sample(2)) }),
{
    let m=machine();let a=alpha(n);let b=beta(n);let ta=replica_preparation(a);let tb=replica_preparation(b);
    let x=construction::root(m,l,a);let y=construction::root(m,l,b);let f=sample(2);let scope=|_e:Observation|true;
    source_preparation(l,n);grant_has_common_control(2);coupling::pair_at_fanout(m,l,n,f);
    assert(coupling::fitted(ta,scope)) by {assert forall|i:int| 0<=i<ta.len() implies coupling::preparation_input(#[trigger] ta[i]) by {prefix_index(i);}}
    assert(grant_control((x.cfg.private)(at(Replica::R3)),(y.cfg.private)(at(Replica::R3)))) by {reveal_with_fuel(memory,6);}
    assert(coupling::translated(f,ta,2) =~= tb) by {
        assert forall|i:int| 0<=i<ta.len() implies #[trigger] coupling::observation(f,ta[i],2)==tb[i] by {prefix_index(i);}
    }
    let k=coupling::replay_preparation(m,n,f,scope,|s,t|grant_control(s,t),x,y,ta);
    assert(k==ta.len());assert(ta.take(k as int) =~= ta);assert(tb.take(k as int) =~= tb);
}

pub proof fn coupled_permission_on_originals(l:Lanes,n:Notice)
    requires permission_names(l),
    ensures ({
        let m=machine();let a=alpha(n);let b=beta(n);let ta=replica_preparation(a);let tb=replica_preparation(b);
        let va=|s:Memory|s.0.reply.unwrap();let za=construction::first_end(m,l,a,ta,collect(a));let zb=construction::first_end(m,l,b,tb,collect(b));
        construction::actual_first(m,va,l,a,ta,collect(a)) && construction::actual_first(m,va,l,b,tb,collect(b))
            && (za.cfg.private)(at(Replica::R1)).1 && (zb.cfg.private)(at(Replica::R1)).1
            && crate::coupled_reads::issued_pair(asm::drive(m,za,crate::first_pair::close(true)),asm::drive(m,zb,crate::first_pair::close(true)),n,sample(2))
            && asm::prefix(m,za,crate::first_pair::close(true),true) && asm::prefix(m,zb,crate::first_pair::close(true),true)
    }),
{
    let m=machine();let a=alpha(n);let b=beta(n);let ta=replica_preparation(a);let tb=replica_preparation(b);let f=sample(2);
    coupled_preparations(l,n);
    gather(l,a);gather(l,b);
    let za=construction::first_end(m,l,a,ta,collect(a));let zb=construction::first_end(m,l,b,tb,collect(b));
    let u=construction::prepared(m,l,a,ta);let v=construction::prepared(m,l,b,tb);
    assert((v.cfg.private)(at(Replica::R1))==(u.cfg.private)(at(Replica::R1)));
    let res=|s:Memory|s.0.reply;
    assert(crate::read_issue::can_issue(m,res));assert(first::startup(m));
    construction::issue_pair(m,res,l,n,f,u,v,za,zb,collect(a),collect(b));
}

}
