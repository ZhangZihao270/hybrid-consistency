// An addressed direct read on either of two *specified physical replicas*.
// Its result function sees the actual sender keys. The original transport
// fixes C2's destinations to R1/R2; the full stock RPC front end accepts
// any replica. Decode Query2 at its addressed site for this comparison.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Packet,Process,Path as Route};
use crate::facade_linear::CommandSemantics;
use crate::facade_transport::{self as bus,Service};
use crate::fallback_program::apply_event;
use crate::first_copy_wait::Cut;
use crate::metadata_stock::Rows;
use crate::ordered_round::{engine,Work};
use crate::quorum_rpc::Resolver;
use crate::stock_facade::*;

verus! {

pub type Net=Network<int,Wire>;
pub type Ev=Action<Wire>;

pub open spec fn query(p:Packet<Wire>) -> bool {
    p.to is At && p==crate::sr2::query_packet(p.to->At_0)
}
pub open spec fn decode(n:Net,a:Ev) -> Service {
    match a {
        Action::Send(_,p) if query(p)=>Service::Rpc(p.to->At_0,Stage::Offer,None),
        Action::Deliver(id) if n.pending.contains_key(id) && query(n.pending[id])=>
            Service::Rpc(n.pending[id].to->At_0,Stage::DeliverRequest,None),
        _=>bus::service(n,a,Process::SecondClient),
    }
}
pub open spec fn rpc_step(f:CommandSemantics,rho:Resolver,s:Cut,a:Ev,u:Cut) -> bool {
    let stage=decode(s.net,a);let e=crate::facade_hybrid::request(stage,2);
    delivery::enabled(s.net,a) && !(stage is Other)
        && bus::valid(s.net,stage,s.core.calls[2],Process::SecondClient)
        && (match a {Action::Send(_,p) if crate::metadata_pair::replica_answer(p)=>p==reported(s,p.from->At_0),_=>true})
        && enabled(engine(f),s.core,e) && u.core==apply_event(rho,engine(f),s.core,e)
        && u.net==delivery::advance(|x,w|cell(x,w),s.net,a)
}
pub open spec fn stamp_at(s:Cut,r:Replica) -> crate::ordered_store::Stamp {
    crate::ordered_store::Stamp{version:0,value:(s.core.base.disk)(r).value}
}
pub open spec fn emitted(c:Call,r:Replica) -> bool {
    let leg=(c.legs)(r);leg is InFlight || leg is Received
}
// This bit can be maintained at the emitter with one assignment on its
// own send. A client delivery never informs a replica who heard the reply.
pub proof fn local_emission_bit(c:Call,r:Replica,stage:Stage,site:Replica,row:crate::ordered_store::Stamp)
    requires rpc_enabled(c,r,stage,true,true),
    ensures emitted(advance_rpc(c,r,stage,row),site)==(emitted(c,site) || (r==site && stage==Stage::EmitReply)),
{}
pub open spec fn root_reports() -> Rows {
    let gen=crate::ordered_store::Stamp{version:0,value:1};
    Map::empty().insert(Replica::R1,gen).insert(Replica::R2,gen)
}
pub open spec fn reported(s:Cut,r:Replica) -> Packet<Wire> {
    let row=stamp_at(s,r);
    let participated=s.core.calls.contains_key(1) && emitted(s.core.calls[1],r);
    Packet {path:Route::Strong,from:at(r),to:Process::SecondClient,
        input:Wire::StampedAnswer(Report{value:row.value,answered_first:participated},row.version)}
}
pub open spec fn reports(s:Cut,l:Replica,r:Replica) -> Rows {
    Map::empty().insert(l,stamp_at(s,l)).insert(r,stamp_at(s,r))
}
pub open spec fn actions(s:Cut,l:Replica,r:Replica) -> Seq<Ev> {
    seq![Action::Send(11,crate::sr2::query_packet(l)),Action::Send(12,crate::sr2::query_packet(r)),
        Action::Deliver(11),Action::Deliver(12),
        Action::Send(13,reported(s,l)),Action::Send(14,reported(s,r)),Action::Deliver(13),Action::Deliver(14),
        Action::Strong(Process::SecondClient)]
}
pub open spec fn leg(s:Cut,l:Replica,r:Replica,site:Replica,k:nat) -> Leg {
    let d:nat=if site==l {0} else {1};
    if (site!=l && site!=r) || k<=d {Leg::Unsent} else if k<=2+d {Leg::Request}
    else if k<=4+d {Leg::AtServer} else if k<=6+d {Leg::InFlight(stamp_at(s,site))}
    else {Leg::Received(stamp_at(s,site))}
}
pub open spec fn at_step(rho:Resolver,s:Cut,l:Replica,r:Replica,k:nat) -> Cut {
    let p=s.net.pending;
    let p=if 1<=k<3 {p.insert(11,crate::sr2::query_packet(l))} else {p};
    let p=if 2<=k<4 {p.insert(12,crate::sr2::query_packet(r))} else {p};
    let p=if 5<=k<7 {p.insert(13,reported(s,l))} else {p};
    let p=if 6<=k<8 {p.insert(14,reported(s,r))} else {p};
    let c=Call{legs:|site|leg(s,l,r,site,k),answer:if k==9 {rho(reports(s,l,r))} else {None},..fresh(Method::Read)};
    Cut{net:Network{pending:p,..s.net},core:State{calls:s.core.calls.insert(2,c),..s.core}}
}
pub open spec fn fresh_majority(s:Cut,l:Replica,r:Replica) -> bool {
    l!=r && s.net.first_stopped && s.net.second_started && s.core.calls.contains_key(1) && s.core.calls.get(2)==Some(fresh(Method::Read))
        && !s.core.base.stopped.contains(2) && !s.core.closed.contains(l) && !s.core.closed.contains(r)
        && (forall|site:Replica| site==l || site==r ==> delivery::live(s.net,at(site))
            && #[trigger] s.core.base.live.contains(site) && (s.net.locals)(site)==(s.core.base.disk)(site).value)
        && forall|id:nat| 11<=id<=14 ==> !#[trigger] s.net.pending.contains_key(id)
}
pub open spec fn exchange(f:CommandSemantics,rho:Resolver,s:Cut,l:Replica,r:Replica) -> bool {
    at_step(rho,s,l,r,0)==s && (forall|k:nat| k<9 ==> rpc_step(f,rho,at_step(rho,s,l,r,k),
        #[trigger] actions(s,l,r)[k as int],at_step(rho,s,l,r,k+1)))
        && at_step(rho,s,l,r,9).net==s.net && at_step(rho,s,l,r,9).core.base==s.core.base
        && at_step(rho,s,l,r,9).core.calls[1]==s.core.calls[1]
        && at_step(rho,s,l,r,9).core.calls[2].answer==rho(reports(s,l,r))
        && (forall|k:int| 0<=k<9 ==> match #[trigger] actions(s,l,r)[k] {
            Action::Send(_,p) if delivery::outside_replica(p.from)=>query(p) && (k==0 || k==1),_=>true})
}
pub proof fn addressed_exchange(f:CommandSemantics,rho:Resolver,s:Cut,l:Replica,r:Replica)
    requires fresh_majority(s,l,r),
    ensures exchange(f,rho,s,l,r),
{
    let p=engine(f);let a=actions(s,l,r);
    assert(at_step(rho,s,l,r,0).core.calls[2].legs =~= fresh(Method::Read).legs);
    assert(at_step(rho,s,l,r,0).core.calls =~= s.core.calls);
    assert forall|k:nat| k<9 implies rpc_step(f,rho,at_step(rho,s,l,r,k),#[trigger] a[k as int],at_step(rho,s,l,r,k+1)) by {
        prefix_index(k as int);
        let x=at_step(rho,s,l,r,k);let u=at_step(rho,s,l,r,k+1);let ev=a[k as int];
        let st=decode(x.net,ev);let e=crate::facade_hybrid::request(st,2);
        let v=apply_event(rho,p,x.core,e);
        if k==8 {assert(rows(x.core.calls[2]) =~= reports(s,l,r));}
        assert(s.core.base.live.contains(l) && s.core.base.live.contains(r));
        assert(delivery::live(s.net,at(l)) && delivery::live(s.net,at(r)));
        assert(delivery::enabled(x.net,ev));assert(!(st is Other));
        assert(bus::valid(x.net,st,x.core.calls[2],Process::SecondClient));
        assert(enabled(p,x.core,e));assert(early(x.core.calls[2]));assert(v.closed =~= s.core.closed);
        assert(v.calls[2].legs =~= u.core.calls[2].legs);assert(v.calls =~= u.core.calls);
        let next=delivery::advance(|z,w|cell(z,w),x.net,ev);
        assert(next.locals =~= u.net.locals);assert(next.pending =~= u.net.pending);
    }
    assert forall|k:int| 0<=k<9 implies match #[trigger] a[k] {
        Action::Send(_,p) if delivery::outside_replica(p.from)=>query(p) && (k==0 || k==1),_=>true
    } by {prefix_index(k);}
}

}
