use vstd::prelude::*;
use crate::{Op,Replica};
use crate::checkpoint::*;
use crate::delivery::{self,Action,Network,Process,observations};
use crate::fanout_service::{self as service,state,run_step,done,grows};
use crate::metadata_pair::{self as rpc,Local,first_rows,startup};
use crate::metadata_reader::{reference_read,single,starts_sr2,unanimous,compare_after_first};
use crate::metadata_stock::Rows;
use crate::ordinary_service::{Configuration,allowed,apply};
use crate::ordered_store::{Stamp,majority};
use crate::promotion_wait::{self as wait,Path};
use crate::protocol::{accepted,memory};
use crate::quorum_rpc::Resolver;
use crate::stock_facade as stock;

verus! {

// When ordinary validation fails, a sampled original, position-zero
// image at the reference site is another ordinary source for a majority
// read. The candidate is taken from the actual received row.
pub open spec fn resolver() -> Resolver {
    |rows:Rows| {
        let old=reference_read(Replica::R3)(rows);
        if old.is_none() && majority(rows.dom()) && rows.get(Replica::R3)==Some(Stamp{version:0,value:1}) {
            Some(rows[Replica::R3].value)
        } else {old}
    }
}
pub proof fn every_stock_direct_poll_agrees<X,E>(p:stock::Engine<X,E>,s:stock::State<X>,id:nat)
    requires stock::ports(p),stock::reachable(p,s),s.calls.contains_key(id),stock::early(s.calls[id]),
        majority(stock::rows(s.calls[id]).dom()),
    ensures resolver()(stock::rows(s.calls[id]))==reference_read(Replica::R3)(stock::rows(s.calls[id])),
{
    stock::reachable_good(p,s);stock::early_stock_answer(s.calls[id]);
}

// From the same sent-request cut, let R3 serve its request BEFORE either
// of the issued weak packets arrives. Both survivors still emit their
// replies. Finish at C1's first response; this is a finite opportunity.
pub open spec fn action(b:Fork,i:nat) -> Action<Wire> {
    if i==8 {send(8,delivery::Path::FirstReadReply,at(Replica::R3),Process::FirstClient,Wire::Reply(1))}
    else {actions_to_crash(b)[i as int+2]}
}
pub open spec fn net(b:Fork,k:nat) -> Network<int,Wire> {
    let prior=state_after(b,k+2);
    let p=prior.pending.remove(2).insert(0,packet_for(b,0)).insert(1,packet_for(b,1));
    Network {pending:if p.contains_key(8) {p.insert(8,action(b,8)->Send_1)} else {p},..after_local_rmws()}
}
pub open spec fn local(b:Fork,p:Process,k:nat) -> Local {
    let client=p==Process::FirstClient;let old=expected_control(b,p,k+2);
    let first=Control {weak_copy:None,reply:if client && k>=11 {Some(1)} else {old.reply},..old};
    let rows=if !client {Map::empty()} else if k>=11 {first_rows(b,k+2).insert(Replica::R3,Stamp{version:0,value:1})}
        else {first_rows(b,k+2)};
    Local {first,rows,returned:if client && k>=12 {Some(1)} else {None},..startup(p,Set::empty())}
}
pub open spec fn cfg(b:Fork,k:nat) -> Configuration<Local> {
    Configuration {net:net(b,k),private:|p|local(b,p,k)}
}
pub open spec fn path(b:Fork) -> Path<Configuration<Local>,Action<Wire>> {
    Path {states:Seq::new(10,|i:int|cfg(b,3+i as nat)),actions:Seq::new(9,|i:int|action(b,3+i as nat))}
}
pub open spec fn working_copies(s:Configuration<Local>,w:Op) -> Set<Replica> {
    all_replicas().filter(|r| (s.net.locals)(r)==crate::next(w,1))
}
proof fn step(b:Fork,k:nat)
    requires k<12,
    ensures ({
        let m=single(resolver(),Set::empty());let s=cfg(b,k);let a=action(b,k);let u=cfg(b,k+1);
        allowed(m,s,a) && u==apply(m,s,a) && (k>=3 ==> service::internal(a))
    }),
{
    let m=single(resolver(),Set::empty());let s=cfg(b,k);let a=action(b,k);let u=cfg(b,k+1);
    let ev=delivery::process_step(s.net,a);prefix_index(k as int);
    let phys=delivery::advance(|x,w|cell(x,w),s.net,a);
    assert(phys.pending =~= u.net.pending);assert(phys.locals =~= u.net.locals);
    assert((apply(m,s,a).private) =~= u.private) by {
        assert forall|p:Process| (#[trigger] (apply(m,s,a).private)(p))==(u.private)(p) by {
            if k==11 {assert(resolver()(local(b,Process::FirstClient,k).rows)==Some(1));}
            let x=(apply(m,s,a).private)(p);let y=(u.private)(p);
            assert(x.first.sent_requests =~= y.first.sent_requests);
            assert(x.first.replies_from =~= y.first.replies_from);
            assert(x.first==y.first);assert(x.rows =~= y.rows);
            assert(x.returned==y.returned);
        }
    }
}
proof fn same_cut(b:Fork)
    ensures cfg(b,3)==state(single(resolver(),Set::empty()),b,3),
{
    let m=single(resolver(),Set::empty());let s=cfg(b,3);let u=state(m,b,3);
    assert(s.net.pending =~= u.net.pending);assert(s.net.locals =~= u.net.locals);
    assert(s.private =~= u.private) by {
        assert forall|p:Process| (#[trigger] (s.private)(p))==(u.private)(p) by {
            crate::fanout_replay::same_local_history(m,b,p,3);
            rpc::prefix_control(resolver(),resolver(),b,Set::empty(),p,crate::fanout_replay::local_index(p,3));
        }
    }
}

pub proof fn no_later_response(b:Fork)
    ensures !crate::service::can_respond(starts_sr2(b,resolver(),Set::empty()),|s:Local|s.returned,checkpoint_end(b),delayed_slots()),
{
    hide(memory);hide(accepted);hide(rpc::permits);
    let rho=resolver();let archives=Set::empty();let m=starts_sr2(b,rho,archives);let res=|s:Local|s.returned;
    let cut=checkpoint_end(b);let slots=delayed_slots();let r=Replica::R1;
    assert(unanimous(first_rows(b,13)) && rho(first_rows(b,13))==Some(first_value(b)));
    if crate::service::can_respond(m,res,cut,slots) {
        let (t,a,v)=choose|t:crate::metadata_provenance::States,a:crate::metadata_provenance::Actions,v:int|
            #[trigger] crate::service::response_path(m,res,cut,slots,t,a,v);
        compare_after_first(b,rho,archives,t,a,v);
        let rows=crate::metadata_provenance::authenticated_result(b,rho,archives,t,a,v);
        assert(rows.contains_key(r) && !rows.contains_key(Replica::R3) && rows[r].version==0);
        assert(crate::metadata_provenance::explains(t,a,a.len(),r,rows[r].value,archives));
        assert(rows[r].value!=1 && !crate::metadata_reader::valid_root(rows));
        assert(rho(rows).is_none());
    }
}

// This refutes an implication between two service tests for this read
// family. It does not assert global T or H for the fallback policy.
pub proof fn first_escape_and_later_pending(b:Fork)
    ensures ({
        let rho=resolver();let m=single(rho,Set::empty());let d=done(m);let p=path(b);let s=state(m,b,3);
        accepted(m,checkpoint_observations(b)) && completed_quorum_sample(m,|x:Local|x.returned.unwrap(),b)
          && first_result(m,|x:Local|x.returned.unwrap(),b)==first_value(b)
          && wait::first_return(run_step(m),d,s,p) && !wait::uses(p,grows(|s,w|working_copies(s,w)))
          && !wait::needs_class(run_step(m),d,s,grows(|s,w|working_copies(s,w)))
          && (p.states.last().private)(Process::FirstClient).returned==Some(1)
          && p.states.last().net.pending.get(0)==Some(packet_for(b,0)) && p.states.last().net.pending.get(1)==Some(packet_for(b,1))
          && pre_sr1_g(b,weak_assignment(b,true).ops) && truthful_notice(b,weak_assignment(b,true).ops)
          && !crate::service::can_respond(starts_sr2(b,rho,Set::empty()),|s:Local|s.returned,checkpoint_end(b),delayed_slots())
          && crate::confirmation::admissible_service(checkpoint_end(b),starts_sr2(b,rho,Set::empty()),|x:Local|x.returned,crate::metadata_fair::run(b))
          && crate::progress::delivery_fair(crate::metadata_fair::run(b))
          && crate::progress::process_fair(crate::metadata_fair::run(b),|s,p|delivery::live(s,p))
          && forall|k:nat| #[trigger] actual_later_pending(b,k)
    }),
{
    hide(accepted);hide(memory);hide(crate::confirmation::admissible_service);
    let rho=resolver();let m=single(rho,Set::empty());let p=path(b);let s=state(m,b,3);let d=done(m);
    assert(unanimous(first_rows(b,13)) && rho(first_rows(b,13))==Some(first_value(b)));
    rpc::real_first_with(rho,rho,b,Set::empty());same_cut(b);weak_assignment_at_delivery(b,true);
    assert forall|i:int| 0<=i<p.actions.len() implies run_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        by {step(b,3+i as nat);}
    assert(wait::valid_edges(run_step(m),p) && wait::pending_before(d,p));
    assert(wait::first_return(run_step(m),d,s,p));
    assert forall|i:int| 0<=i<p.actions.len() implies !grows(|s,w|working_copies(s,w))(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        by {assert(p.states[i].net.locals==p.states[i+1].net.locals);}
    assert(!wait::uses(p,grows(|s,w|working_copies(s,w))));
    no_later_response(b);crate::metadata_fair::pending_after_all_live_deliveries(b);
    crate::metadata_fair::accepted_background(b,rho);
    assert forall|k:nat| #[trigger] actual_later_pending(b,k) by {
        crate::metadata_fair::state_at(b,rho,Process::SecondClient,k,k);
        crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R1);
        crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R2);
        assert(rho(rpc::sample_rows(b,rpc::BeforeSample::Unchanged)).is_none());
    }
}
pub open spec fn actual_later_pending(b:Fork,k:nat) -> bool {
    let e=crate::metadata_fair::run(b);let rho=resolver();
    let es=observations(crate::progress::states_through(e,k),crate::progress::actions_before(e,k));
    memory(starts_sr2(b,rho,Set::empty()),Process::SecondClient,es,k).returned.is_none()
}
pub proof fn release_after_early_return(b:Fork)
    ensures ({
        let m=single(resolver(),Set::empty());let s=path(b).states.last();
        let first=Action::Deliver(0);let second=Action::Deliver(1);
        let mid=apply(m,s,first);let u=apply(m,mid,second);
        allowed(m,s,first) && allowed(m,mid,second)
          && !u.net.pending.contains_key(0) && !u.net.pending.contains_key(1)
          && (s.net.locals)(Replica::R3)==1 && (mid.net.locals)(Replica::R3)==2 && (u.net.locals)(Replica::R3)==5
          && (s.private)(Process::FirstClient).returned==Some(1) && (u.private)(Process::FirstClient)==(s.private)(Process::FirstClient)
    }),
{}
}
