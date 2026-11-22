use vstd::prelude::*;
use crate::{Replica,origin};
use crate::stock_facade::{Call,Method,Leg,Stage,advance_rpc,local_poll,rpc_enabled,rows,delegate,fresh};
use crate::checkpoint::*;
use crate::delivery::*;
use crate::metadata_pair::{replica_answer,signed_row};
use crate::metadata_reader::reference_read;
use crate::metadata_fair::{network,background,pending_after_all_live_deliveries};
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
pub open spec fn valid(n: Network<int,Wire>,ev: Service,c: Call,client: Process) -> bool {
    match ev {
        Service::Rpc(r,st,body)=>rpc_enabled(c,r,st,live(n,at(r)),live(n,client)) && match st {
            Stage::EmitReply=>body==Some(sees(n,r)), Stage::DeliverReply=>body==Some((c.legs)(r)->InFlight_0), _=>true,
        },
        Service::Poll=>live(n,client) && !delegate(c) && !c.submitted, _=>true,
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
pub open spec fn post_net(b: Fork) -> spec_fn(nat)->Network<int,Wire> { |i|network(b,i) }
pub open spec fn post_act(b: Fork) -> spec_fn(nat)->Action<Wire> { |i|background(b,i) }
pub open spec fn client1(b: Fork,k: nat) -> Call { at_time(pre_net(b),pre_act(b),Process::FirstClient,k) }
pub open spec fn client2(b: Fork,k: nat) -> Call { at_time(post_net(b),post_act(b),Process::SecondClient,k) }

pub open spec fn first_leg(b: Fork,r: Replica,k: nat) -> Leg {
    let off:nat=if r==Replica::R1 {0} else if r==Replica::R2 {1} else {2};
    let s=sees(state_after(b,8),r);
    if k<=2+off {Leg::Unsent} else if k<=5+off {Leg::Request} else if k<=8+off {Leg::AtServer}
    else if (r==origin(b.branch) && k>=12) || (r==Replica::R3 && k>=13) {Leg::Received(s)} else {Leg::InFlight(s)}
}
pub open spec fn second_leg(b: Fork,r: Replica,k: nat) -> Leg {
    let off:nat=if r==Replica::R1 {0} else {1}; let s=sees(network(b,4),r);
    if r==Replica::R3 || k<=off {Leg::Unsent} else if k<=2+off {Leg::Request} else if k<=4+off {Leg::AtServer}
    else if k<=6+off {Leg::InFlight(s)} else {Leg::Received(s)}
}
pub proof fn actual_first_rpc(b: Fork,k: nat)
    requires k<=17,
    ensures ({
        let c=client1(b,k); let n=state_after(b,k); let a=actions_to_crash(b);
        c==(Call { legs: |r| first_leg(b,r,k), answer: if k>=14 {Some(first_value(b))} else {None}, ..fresh(Method::Read)})
            && !delegate(c)
            && (k<17 ==> valid(n,service(n,a[k as int],Process::FirstClient),c,Process::FirstClient))
    }),
    decreases k,
{
    if k>0 { let j=(k-1) as nat; actual_first_rpc(b,j); prefix_index(j as int); }
    if k<17 {prefix_index(k as int);}
    assert(client1(b,k).legs =~= (|r| first_leg(b,r,k)));
    assert(rows(client1(b,k)) =~= crate::metadata_pair::first_rows(b,k));
    assert(crate::metadata_reader::unanimous(crate::metadata_pair::first_rows(b,13)));
}
pub proof fn actual_second_rpc(b: Fork,k: nat)
    ensures ({
        let c=client2(b,k); let n=network(b,k); let a=background(b,k);
        c==(Call { legs: |r| second_leg(b,r,k), ..fresh(Method::Read)}) && !delegate(c)
            && valid(n,service(n,a,Process::SecondClient),c,Process::SecondClient)
    }),
    decreases k,
{
    if k>0 {
        let j=(k-1) as nat; actual_second_rpc(b,j); if j<14 {prefix_index(j as int);}
    }
    if k<14 {prefix_index(k as int);}
    crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R1);
    crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R2);
    assert(client2(b,k).legs =~= (|r| second_leg(b,r,k)));
    if k>=8 {
        let m=rows(client2(b,k)); assert(m =~= crate::metadata_stock::unadvanced_rows());
        assert(m.contains_key(Replica::R1) && m[Replica::R1].version==0 && m[Replica::R1].value==2);
        assert(reference_read(Replica::R3)(m).is_none());
    }
}

// An open ordinary tag is independent of the weak path. Weak input alone
// never requests backend work or changes the read mailbox. The emitter
// still reads the actual shared cell, so a weak installation before sampling
// can change what is reported.
pub proof fn weak_delivery_does_not_gate_a_poll(n: Network<int,Wire>,id: nat,client: Process,c: Call)
    requires n.pending.contains_key(id),n.pending[id].path==Path::Weak,
        n.pending[id].input is WeakConfirm || n.pending[id].input is Copy,
    ensures service(n,Action::Deliver(id),client) is Other,
        run_local(n,service(n,Action::Deliver(id),client),c)==c,
        run_local(n,Service::Poll,c)==run_local(advance(|x,w|cell(x,w),n,Action::Deliver(id)),Service::Poll,c),
{}

pub proof fn both_reads_use_the_ordinary_front(n: Notice)
    ensures client1(alpha(n),17).answer==Some(5),client1(beta(n),17).answer==Some(2),
        forall|k: nat| #[trigger] client2(alpha(n),k)==#[trigger] client2(beta(n),k)
            && client2(alpha(n),k).answer.is_none() && !client2(alpha(n),k).submitted,
        pre_sr1_g(alpha(n),weak_assignment(alpha(n),true).ops) && pre_sr1_g(beta(n),weak_assignment(beta(n),true).ops),
{
    let a=alpha(n); let b=beta(n); actual_first_rpc(a,17); actual_first_rpc(b,17);
    pending_after_all_live_deliveries(a); pending_after_all_live_deliveries(b);
    assert forall|k: nat| #[trigger] client2(a,k)==#[trigger] client2(b,k)
        && client2(a,k).answer.is_none() && !client2(a,k).submitted by {
        actual_second_rpc(a,k); actual_second_rpc(b,k);
        assert(client2(a,k).legs =~= client2(b,k).legs);
    }
}

}
