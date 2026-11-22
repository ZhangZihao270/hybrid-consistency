use vstd::prelude::*;
use crate::Replica;
use crate::stock_facade::{Call,Method,Stage,advance_rpc,local_poll,fresh};
use crate::checkpoint::*;
use crate::delivery::*;
use crate::metadata_pair::{replica_answer,signed_row};
use crate::ordered_store::Stamp;

verus! {

pub enum Service { Other, Rpc(Replica,Stage,Option<Stamp>), Poll }
pub open spec fn wire_event(p: Packet<Wire>, client: Process, sent: bool) -> Service {
    if p.from==client && invocation_packet(p) {
        Service::Rpc(p.to->At_0, if sent {Stage::Offer} else {Stage::DeliverRequest}, None)
    } else if p.to==client && (first_reply(p) || replica_answer(p)) {
        let stamp=if first_reply(p) {Stamp {version:0,value:p.input->Reply_0}} else {signed_row(p)};
        Service::Rpc(p.from->At_0, if sent {Stage::EmitReply} else {Stage::DeliverReply},Some(stamp))
    } else { Service::Other }
}
pub open spec fn service(n: Network<int,Wire>,a: Action<Wire>,client: Process) -> Service {
    match a {
        Action::Send(_,p)=>wire_event(p,client,true),
        Action::Deliver(id) if n.pending.contains_key(id)=>wire_event(n.pending[id],client,false),
        Action::Strong(p) if p==client =>Service::Poll, _=>Service::Other,
    }
}
pub open spec fn sees(n: Network<int,Wire>,r: Replica) -> Stamp { Stamp { version:0,value:(n.locals)(r) } }
pub open spec fn run_local(n: Network<int,Wire>,ev: Service,c: Call) -> Call {
    match ev {
        Service::Rpc(r,st,_)=>advance_rpc(c,r,st,sees(n,r)), Service::Poll=>local_poll(c,None), _=>c,
    }
}
pub open spec fn at_time(nets: spec_fn(nat)->Network<int,Wire>,acts: spec_fn(nat)->Action<Wire>,client: Process,k: nat) -> Call
    decreases k,
{
    if k==0 { fresh(Method::Read) } else {
        let i=(k-1) as nat; run_local(nets(i),service(nets(i),acts(i),client),at_time(nets,acts,client,i))
    }
}
pub open spec fn pre_net(b: Fork) -> spec_fn(nat)->Network<int,Wire> { |i|state_after(b,i) }
pub open spec fn pre_act(b: Fork) -> spec_fn(nat)->Action<Wire> { |i: nat|actions_to_crash(b)[i as int] }
pub open spec fn client1(b: Fork,k: nat) -> Call { at_time(pre_net(b),pre_act(b),Process::FirstClient,k) }

}
