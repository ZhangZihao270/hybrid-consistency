// An ordinary read job can be present in the strong protocol even when a
// failed direct lookup cannot submit it. Keep its admission and service
// guards separate. The two original clients and packets are unchanged.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self, Action, Process};
use crate::facade_linear::CommandSemantics;
use crate::facade_progress::Run;
use crate::fallback_program as front;
use crate::first_copy_wait::Cut;
use crate::live_quorum as rpc;
use crate::metadata_stock::Rows;
use crate::ordered_round::{self as base, Store, Work, engine};
use crate::ordered_store::majority;
use crate::quorum_rpc::{Resolver, latest, latest_site};
use crate::stock_facade::*;

verus! {

pub type Admission = spec_fn(Rows)->bool;

// A direct-generation sample inconsistent with its own ordinary genesis
// image. There is no replica identity, weak command ID or order status in
// this integrity test. Open stock data at this interface start at one.
pub open spec fn inconsistent(m:Rows) -> bool {
    exists|r:Replica| #[trigger] m.contains_key(r) && m[r].version==0 && m[r].value!=1
}
pub open spec fn dispatch(c:Call,rho:Resolver,admission:Admission) -> bool {
    front::direct(c) && rho(rows(c)).is_none() && inconsistent(rows(c)) && admission(rows(c))
}

pub open spec fn miss<X,E>(s:State<X>,a:Event<E>,rho:Resolver,admission:Admission) -> bool {
    match a {
        Event::Poll(id)=>s.calls.contains_key(id) && dispatch(s.calls[id],rho,admission),
        _=>false,
    }
}
pub open spec fn permitted<X,E>(p:Engine<X,E>,s:State<X>,a:Event<E>,rho:Resolver,admission:Admission) -> bool {
    enabled(p,s,a) && (!miss(s,a,rho,admission) || (p.ready)(s.base,Input::Submit(a->Poll_0,Method::Read)))
}
pub open spec fn advance<X,E>(p:Engine<X,E>,s:State<X>,a:Event<E>,rho:Resolver,admission:Admission) -> State<X> {
    if miss(s,a,rho,admission) {
        let id=a->Poll_0;
        State {base:(p.step)(s.base,Input::Submit(id,Method::Read)),
            calls:s.calls.insert(id,Call{submitted:true,..s.calls[id]}),..s}
    } else {front::apply_event(rho,p,s,a)}
}

proof fn dormant<X,E>(p:Engine<X,E>,s:State<X>,a:Event<E>,rho:Resolver,admission:Admission)
    requires ports(p),reachable(p,s),
    ensures !miss(s,a,rho,admission),permitted(p,s,a,rho,admission)==enabled(p,s,a),
        advance(p,s,a,rho,admission)==front::apply_event(rho,p,s,a),
{
    if let Event::Poll(id)=a {
        if s.calls.contains_key(id) && front::direct(s.calls[id]) {
            reachable_good(p,s);let c=s.calls[id];
            if inconsistent(rows(c)) {
                let r=choose|r:Replica| #[trigger] rows(c).contains_key(r) && rows(c)[r].version==0 && rows(c)[r].value!=1;
                assert((c.legs)(r) is Received);
                assert(inspectable(c));
            }
        }
    }
}

pub open spec fn path<X,E>(p:Engine<X,E>,rho:Resolver,g:Admission,t:Seq<State<X>>,a:Seq<Event<E>>) -> bool {
    t.len()==a.len()+1 && forall|i:int| 0<=i<a.len() ==>
        permitted(p,t[i],#[trigger] a[i],rho,g) && t[i+1]==advance(p,t[i],a[i],rho,g)
}

proof fn stock_at<X,E>(p:Engine<X,E>,rho:Resolver,g:Admission,t:Seq<State<X>>,a:Seq<Event<E>>,k:nat)
    requires ports(p),front::serves_root(rho),reachable(p,t[0]), k<=a.len(),
        path(p,rho,g,t,a) || front::path_using(p,rho,t,a),
    ensures reachable(p,t[k as int]),
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat;stock_at(p,rho,g,t,a,i);
        let s=t[i as int];let ev=a[i as int];let u=t[k as int];
        dormant(p,s,ev,rho,g);
        assert(enabled(p,s,ev) && u==front::apply_event(rho,p,s,ev));
        let ts=seq![s,u];let es=seq![ev];
        assert(front::path_using(p,rho,ts,es));front::same_paths(p,rho,ts,es);
        crate::facade_quorum::extend_reach(p,s,ts,es);
    }
}

// Includes ordinary commands, all consensual decisions/repairs of the
// supplied engine, and every available serving majority, on stock traces.
pub proof fn stock_paths<X,E>(p:Engine<X,E>,rho:Resolver,g:Admission,t:Seq<State<X>>,a:Seq<Event<E>>)
    requires ports(p),front::serves_root(rho),reachable(p,t[0]),
    ensures path(p,rho,g,t,a)==front::path_using(p,rho,t,a),
{
    if path(p,rho,g,t,a) || front::path_using(p,rho,t,a) {
        assert forall|i:int| 0<=i<a.len() implies {
            let ev=#[trigger] a[i];let s=t[i];!miss(s,ev,rho,g) && enabled(p,s,ev) &&
                permitted(p,s,ev,rho,g) && t[i+1]==advance(p,s,ev,rho,g) && t[i+1]==front::apply_event(rho,p,s,ev)
        } by {stock_at(p,rho,g,t,a,i as nat);dormant(p,t[i],a[i],rho,g);}
    }
}
pub open spec fn stock_run<X,E>(p:Engine<X,E>,rho:Resolver,g:Admission,e:Run<X,E>) -> bool {
    (e.state)(0)==initial(p) && forall|i:nat| {
        let a=#[trigger] (e.event)(i);let s=(e.state)(i);
        permitted(p,s,a,rho,g) && (e.state)(i+1)==advance(p,s,a,rho,g)
    }
}
pub proof fn stock_runs<X,E>(p:Engine<X,E>,rho:Resolver,g:Admission,e:Run<X,E>)
    requires ports(p),front::serves_root(rho),
    ensures stock_run(p,rho,g,e)==front::execution_using(p,rho,e),
        stock_run(p,rho,g,e) ==> forall|i:nat,a:Event<E>| #[trigger] permitted(p,(e.state)(i),a,rho,g)==enabled(p,(e.state)(i),a),
{
    if stock_run(p,rho,g,e) || front::execution_using(p,rho,e) {
        assert(crate::stock_facade::path(p,seq![initial(p)],Seq::empty()));assert(reachable(p,initial(p)));
        assert forall|k:nat| #[trigger] reachable(p,(e.state)(k)) by {
            let t=Seq::new(k+1,|i:int|(e.state)(i as nat));let a=Seq::new(k,|i:int|(e.event)(i as nat));
            if stock_run(p,rho,g,e) {
                assert forall|i:int| 0<=i<k implies permitted(p,t[i],#[trigger] a[i],rho,g) &&
                    t[i+1]==advance(p,t[i],a[i],rho,g) by {};
                assert(path(p,rho,g,t,a));
            } else {
                assert forall|i:int| 0<=i<k implies enabled(p,t[i],#[trigger] a[i]) &&
                    t[i+1]==front::apply_event(rho,p,t[i],a[i]) by {};
                assert(front::path_using(p,rho,t,a));
            }
            stock_at(p,rho,g,t,a,k);
        }
        assert forall|k:nat,a:Event<E>| #[trigger] permitted(p,(e.state)(k),a,rho,g)==enabled(p,(e.state)(k),a)
            by {dormant(p,(e.state)(k),a,rho,g);}
        assert forall|k:nat| {let a=#[trigger] (e.event)(k);let s=(e.state)(k);
            permitted(p,s,a,rho,g) && enabled(p,s,a) && (e.state)(k+1)==advance(p,s,a,rho,g) &&
                (e.state)(k+1)==front::apply_event(rho,p,s,a)} by {dormant(p,(e.state)(k),(e.event)(k),rho,g);}
    }
}

pub open spec fn same_stock<X,E>(p:Engine<X,E>,rho:Resolver,g:Admission) -> bool {
    (forall|t:Seq<State<X>>,a:Seq<Event<E>>| reachable(p,t[0]) ==>
        #[trigger] path(p,rho,g,t,a)==front::path_using(p,rho,t,a)) &&
    forall|e:Run<X,E>| #[trigger] stock_run(p,rho,g,e)==front::execution_using(p,rho,e) &&
        (stock_run(p,rho,g,e) ==> forall|k:nat,a:Event<E>| #[trigger] permitted(p,(e.state)(k),a,rho,g)==enabled(p,(e.state)(k),a))
}
pub proof fn inherits_stock<X,E>(p:Engine<X,E>,rho:Resolver,g:Admission)
    requires ports(p),front::serves_root(rho),
    ensures same_stock(p,rho,g),
{
    assert forall|t:Seq<State<X>>,a:Seq<Event<E>>| reachable(p,t[0]) implies
        #[trigger] path(p,rho,g,t,a)==front::path_using(p,rho,t,a) by {stock_paths(p,rho,g,t,a);}
    assert forall|e:Run<X,E>| #[trigger] stock_run(p,rho,g,e)==front::execution_using(p,rho,e) &&
        (stock_run(p,rho,g,e) ==> forall|k:nat,a:Event<E>| #[trigger] permitted(p,(e.state)(k),a,rho,g)==enabled(p,(e.state)(k),a))
        by {stock_runs(p,rho,g,e);}
}

// A local implementation on an immutable, already received majority:
// enqueue this call, run the ordinary version selector on its saved rows,
// and publish the saved result. No event here sends a client packet.
pub enum Cpu { Enqueue, Execute, Publish }
pub struct Ticket { pub id:nat, pub samples:Rows }
pub struct Client { pub ticket:Option<Ticket>, pub selected:Option<int>, pub returned:Option<int> }
pub open spec fn idle_client() -> Client { Client{ticket:None,selected:None,returned:None} }
pub open spec fn cpu_ready(c:Client,a:Cpu,inbox:Call,id:nat,rho:Resolver,g:Admission) -> bool {
    match a {
        Cpu::Enqueue=>c.ticket.is_none() && dispatch(inbox,rho,g),
        Cpu::Execute=>c.ticket.is_some() && c.ticket.unwrap().id==id && majority(c.ticket.unwrap().samples.dom()) && c.selected.is_none(),
        Cpu::Publish=>c.ticket.is_some() && c.ticket.unwrap().id==id && c.selected.is_some() && c.returned.is_none(),
    }
}
pub open spec fn cpu(c:Client,a:Cpu,inbox:Call,id:nat) -> Client {
    match a {
        Cpu::Enqueue=>Client{ticket:Some(Ticket{id,samples:rows(inbox)}),..c},
        Cpu::Execute=>Client{selected:latest(c.ticket.unwrap().samples),..c},
        Cpu::Publish=>Client{returned:c.selected,..c},
    }
}

// Ordinary applied positions (not the application values) have to be
// authentic. The open-generation report has position zero on these cuts.
// This is a refinement of one read-only backend service on its serving Q;
// it is not an implementation of the ordered command primitive.
pub open spec fn actual_live_samples(s:State<Store>,id:nat) -> bool {
    let m=rows(s.calls[id]);majority(m.dom()) && m.dom().subset_of(s.base.live) &&
        m==Map::new(m.dom(),s.base.disk)
}
pub open spec fn local_service(f:CommandSemantics,s:State<Store>,id:nat,rho:Resolver,g:Admission) -> bool {
    let p=engine(f);let c=s.calls[id];let ev=Event::Poll(id);let m=rows(c);
    let job=Event::Work(Work::Serve(id,m.dom()));
    let t=advance(p,s,ev,rho,g);let u=advance(p,t,job,rho,g);let end=advance(p,u,ev,rho,g);
    let empty=idle_client();let x=cpu(empty,Cpu::Enqueue,c,id);
    let y=cpu(x,Cpu::Execute,c,id);let z=cpu(y,Cpu::Publish,c,id);
    permitted(p,s,ev,rho,g) && permitted(p,t,job,rho,g) && permitted(p,u,ev,rho,g)
        && t.base.calls.get(id)==Some(Method::Read) && t.calls[id].submitted && t.calls[id].answer.is_none()
        && cpu_ready(empty,Cpu::Enqueue,c,id,rho,g) && cpu_ready(x,Cpu::Execute,c,id,rho,g) && cpu_ready(y,Cpu::Publish,c,id,rho,g)
        && x.ticket==Some(Ticket{id,samples:m}) && y.selected==u.base.done.get(id)
        && z.returned==end.calls[id].answer && z.returned==latest(m) && z.returned.is_some()
        && t.base.disk==s.base.disk && u.base.disk==s.base.disk && end.base.disk==s.base.disk
}

pub proof fn service_from_received(f:CommandSemantics,s:State<Store>,id:nat,rho:Resolver,g:Admission)
    requires s.calls.contains_key(id),dispatch(s.calls[id],rho,g),actual_live_samples(s,id),
        !s.base.stopped.contains(id),!s.base.calls.contains_key(id),!s.base.done.contains_key(id),
    ensures local_service(f,s,id,rho,g),
{
    let p=engine(f);let c=s.calls[id];let ev=Event::Poll(id);let m=rows(c);
    crate::quorum_rpc::latest_is_a_sample(m);let t=advance(p,s,ev,rho,g);
    assert(Map::new(m.dom(),t.base.disk) =~= m);
    assert(base::current(t.base,m.dom())==latest_site(m));
    let u=advance(p,t,Event::Work(Work::Serve(id,m.dom())),rho,g);
    assert(!front::direct(u.calls[id]));
}

pub open spec fn collected(b:Fork,rho:Resolver) -> Cut {
    rpc::at_step(rho,front::original(b,17),Replica::R1,Replica::R2,8)
}
pub open spec fn original_prefix(f:CommandSemantics,b:Fork,rho:Resolver,g:Admission) -> bool {
    crate::sender_forks::prefix_taken(f,rho,b) && forall|k:nat| k<17 ==> {
        let s=front::original(b,k);let ev=#[trigger] actions_to_crash(b)[k as int];
        let begin=crate::facade_hybrid::invocation(s.core,s.net,ev);
        let t=advance(engine(f),s.core,begin,rho,g);let a=crate::facade_hybrid::inner(s.net,ev);
        permitted(engine(f),s.core,begin,rho,g) && permitted(engine(f),t,a,rho,g)
            && front::original(b,k+1).core==crate::facade_hybrid::weak_part(advance(engine(f),t,a,rho,g),s.net,ev)
    }
}
pub open spec fn physical_intake(f:CommandSemantics,b:Fork,rho:Resolver,g:Admission) -> bool {
    let s=front::original(b,17);let l=Replica::R1;let r=Replica::R2;let h=collected(b,rho);
    rpc::at_step(rho,s,l,r,0)==s && (forall|k:nat| k<8 ==> {
        let u=rpc::at_step(rho,s,l,r,k);let v=rpc::at_step(rho,s,l,r,k+1);
        let a=#[trigger] rpc::actions(s,l,r)[k as int];
        let e=crate::facade_hybrid::request(rpc::decode(u.net,a),2);
        rpc::rpc_step(f,rho,u,a,v) && permitted(engine(f),u.core,e,rho,g) && v.core==advance(engine(f),u.core,e,rho,g)
    }) && h.net==s.net && h.net.pending.get(2)==Some(packet_for(b,2)) && delivery::enabled(h.net,Action::Deliver(2))
        && h.net.first_stopped && h.net.r3_crashed && h.net.second_started
        && h.core.calls[1].answer==Some(first_value(b)) && h.core.calls[2].answer.is_none()
        && rows(h.core.calls[2])==crate::metadata_stock::unadvanced_rows() && actual_live_samples(h.core,2)
}
proof fn apply_to_prefix(f:CommandSemantics,b:Fork,rho:Resolver,g:Admission)
    requires rho(crate::metadata_pair::first_rows(b,13))==Some(first_value(b)),
    ensures original_prefix(f,b,rho,g),
{
    hide(crate::sender_forks::prefix_taken);hide(crate::facade_transport::at_time);
    let p=engine(f);crate::sender_forks::original_prefix(f,rho,b);
    assert forall|k:nat| k<17 implies {
        let s=front::original(b,k);let ev=#[trigger] actions_to_crash(b)[k as int];
        let begin=crate::facade_hybrid::invocation(s.core,s.net,ev);
        let t=advance(p,s.core,begin,rho,g);let a=crate::facade_hybrid::inner(s.net,ev);
        permitted(p,s.core,begin,rho,g) && permitted(p,t,a,rho,g)
            && front::original(b,k+1).core==crate::facade_hybrid::weak_part(advance(p,t,a,rho,g),s.net,ev)
    } by {
        prefix_index(k as int);let s=front::original(b,k);
        front::original_for(f,rho,b,k);crate::facade_transport::actual_first_rpc(b,k);
        if k==13 {assert(rows(s.core.calls[1]) =~= crate::metadata_pair::first_rows(b,13));}
    }
}
proof fn actual_intake(f:CommandSemantics,b:Fork,rho:Resolver,g:Admission)
    requires crate::sender_forks::firsts(rho,b.notice),
    ensures original_prefix(f,b,rho,g),physical_intake(f,b,rho,g),
{
    hide(crate::sender_forks::prefix_taken);hide(rpc::rpc_step);hide(crate::facade_transport::at_time);
    let p=engine(f);let l=Replica::R1;let r=Replica::R2;
    crate::metadata_reader::actual_first_decision(b,rho,Set::empty());
    crate::sender_forks::original_prefix(f,rho,b);
    apply_to_prefix(f,b,rho,g);
    let s=front::original(b,17);crate::facade_transport::actual_first_rpc(b,17);
    assert(rpc::fresh_majority(s,l,r));rpc::addressed_exchange(f,rho,s,l,r);
    assert forall|k:nat| k<8 implies {
        let u=rpc::at_step(rho,s,l,r,k);let v=rpc::at_step(rho,s,l,r,k+1);
        let a=#[trigger] rpc::actions(s,l,r)[k as int];
        let e=crate::facade_hybrid::request(rpc::decode(u.net,a),2);
        rpc::rpc_step(f,rho,u,a,v) && permitted(p,u.core,e,rho,g) && v.core==advance(p,u.core,e,rho,g)
    } by {
        prefix_index(k as int);let u=rpc::at_step(rho,s,l,r,k);let v=rpc::at_step(rho,s,l,r,k+1);
        let a=rpc::actions(s,l,r)[k as int];
        assert(rpc::rpc_step(f,rho,u,a,v));reveal(rpc::rpc_step);
        assert(crate::facade_hybrid::request(rpc::decode(u.net,a),2) is Rpc);
    }
    let h=collected(b,rho);let m=rows(h.core.calls[2]);
    assert(m =~= crate::metadata_stock::unadvanced_rows());
    assert(m.dom() =~= live_pair());assert(Map::new(m.dom(),h.core.base.disk) =~= m);
}

pub open spec fn result(rho:Resolver,g:Admission) -> Option<int> {
    let m=crate::metadata_stock::unadvanced_rows();
    if rho(m).is_some() {rho(m)} else if g(m) {latest(m)} else {None}
}
// Construct the CPU steps used; when refused both ways we only take one
// poll. Later, an invariant proves what longer continuations can enable.
pub open spec fn completion_events(rho:Resolver,g:Admission) -> Seq<Event<Work>> {
    let m=crate::metadata_stock::unadvanced_rows();
    if rho(m).is_none() && g(m) {
        seq![Event::Poll(2),Event::Work(Work::Serve(2,m.dom())),Event::Poll(2)]
    } else {seq![Event::Poll(2)]}
}
pub open spec fn service_states(f:CommandSemantics,b:Fork,rho:Resolver,g:Admission) -> Seq<State<Store>> {
    let p=engine(f);let s=collected(b,rho).core;let ev=Event::Poll(2);
    let t=advance(p,s,ev,rho,g);let m=rows(s.calls[2]);
    if rho(m).is_none() && g(m) {
        let u=advance(p,t,Event::Work(Work::Serve(2,m.dom())),rho,g);
        seq![s,t,u,advance(p,u,ev,rho,g)]
    } else {seq![s,t]}
}
pub open spec fn suffix(f:CommandSemantics,b:Fork,rho:Resolver,g:Admission) -> bool {
    let t=service_states(f,b,rho,g);let a=completion_events(rho,g);let n=collected(b,rho).net;
    path(engine(f),rho,g,t,a) && t[0]==collected(b,rho).core &&
        (dispatch(t[0].calls[2],rho,g) ==> local_service(f,t[0],2,rho,g)) && t.last().calls[2].answer==result(rho,g)
        && (forall|i:int| 0<=i<t.len() ==> (#[trigger] t[i]).base.disk==t[0].base.disk &&
            t[i].calls[1]==t[0].calls[1])
        && delivery::trace(|x,w|cell(x,w),Seq::new(a.len()+1,|_i:int|n),
            Seq::new(a.len(),|_i:int|Action::Strong(Process::SecondClient)))
}
proof fn actual_suffix(f:CommandSemantics,b:Fork,rho:Resolver,g:Admission)
    requires physical_intake(f,b,rho,g),
    ensures suffix(f,b,rho,g),
{
    let h=collected(b,rho);let s=h.core;let m=rows(s.calls[2]);let p=engine(f);
    assert(majority(m.dom()) && m.contains_key(Replica::R1) && inconsistent(m));
    assert(front::direct(s.calls[2]));
    if rho(m).is_none() && g(m) {service_from_received(f,s,2,rho,g);}
    let t=service_states(f,b,rho,g);let a=completion_events(rho,g);
    assert forall|i:int| 0<=i<a.len() implies permitted(p,t[i],#[trigger] a[i],rho,g) &&
        t[i+1]==advance(p,t[i],a[i],rho,g) by {prefix_index(i);}
    assert forall|i:int| 0<=i<t.len() implies (#[trigger] t[i]).base.disk==t[0].base.disk && t[i].calls[1]==t[0].calls[1]
        by {prefix_index(i);}
    let tick=Action::Strong(Process::SecondClient);let n=h.net;let tnet=Seq::new(a.len()+1,|_i:int|n);
    let cpu_actions=Seq::new(a.len(),|_i:int|tick);
    assert(delivery::advance(|x,w|cell(x,w),n,tick).locals =~= n.locals);
    assert forall|i:int| 0<=i<cpu_actions.len() implies {
        let e=#[trigger] cpu_actions[i];delivery::enabled(tnet[i],e) && tnet[i+1]==delivery::advance(|x,w|cell(x,w),tnet[i],e)
    } by {};
}

pub proof fn two_real_reads(f:CommandSemantics,n:Notice,rho:Resolver,g:Admission)
    requires crate::sender_forks::firsts(rho,n),
    ensures original_prefix(f,alpha(n),rho,g),original_prefix(f,beta(n),rho,g),
        physical_intake(f,alpha(n),rho,g),physical_intake(f,beta(n),rho,g),
        suffix(f,alpha(n),rho,g),suffix(f,beta(n),rho,g),
        result(rho,g).is_some()==(rho(crate::metadata_stock::unadvanced_rows()).is_some() || g(crate::metadata_stock::unadvanced_rows())),
        match result(rho,g) {Some(v)=> !crate::read_recovery::compatible(alpha(n),v) || !crate::read_recovery::compatible(beta(n),v),None=>true},
        rho(crate::metadata_stock::unadvanced_rows()).is_none() && g(crate::metadata_stock::unadvanced_rows()) ==>
            result(rho,g)==Some(2) && !crate::read_recovery::compatible(alpha(n),2) && crate::read_recovery::compatible(beta(n),2),
{
    hide(physical_intake);hide(original_prefix);hide(suffix);
    actual_intake(f,alpha(n),rho,g);actual_intake(f,beta(n),rho,g);
    actual_suffix(f,alpha(n),rho,g);actual_suffix(f,beta(n),rho,g);
    if let Some(v)=result(rho,g) {crate::read_recovery::history_accepts_exactly_observed_value(alpha(n),v);
        crate::read_recovery::history_accepts_exactly_observed_value(beta(n),v);}
}
}
