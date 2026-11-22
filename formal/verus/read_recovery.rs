use vstd::prelude::*;
use crate::{Op,Replica,legal,next};
use crate::checkpoint::*;
use crate::delivery::{self,Network,Action};
use crate::facade_linear::CommandSemantics;
use crate::facade_hybrid::{prefix,weak_rmw};
use crate::facade_transport::actual_first_rpc;
use crate::genesis_service::{self as genesis,at_read};
use crate::metadata_pair::{self as rpc,BeforeSample,read_net};
use crate::metadata_provenance::{States,Actions,authenticated_result};
use crate::metadata_reader::{reference_read,starts_sr2};
use crate::ordered_round::{self as engine,Store};
use crate::ordered_store::Stamp;
use crate::stock_facade::{State,initial};

verus! {

pub open spec fn compatible(b:Fork,v:int) -> bool {
    exists|ops:Seq<Op>,xs:Seq<int>| #[trigger] legal(ops,xs,first_value(b),v)
}
pub proof fn history_accepts_exactly_observed_value(b:Fork,v:int)
    ensures compatible(b,v)==(v==first_value(b)),
{
    if compatible(b,v) {
        let (o,x)=choose|o:Seq<Op>,x:Seq<int>| #[trigger] legal(o,x,first_value(b),v);
        crate::legal_history_keeps_first_read(o,x,first_value(b),v);
    } else if v==first_value(b) {
        crate::each_branch_has_a_legal_sequential_history();
    }
}

// For EVERY possible C2 return on this saved-image interface, recover
// the actual zero-position samples. No particular restore schedule or
// agreement between branches, and no C2 availability, is a premise.
pub proof fn any_accepted_genesis_repair_loses_this_history(b:Fork,archives:Set<Replica>,t:States,a:Actions,v:int)
    requires crate::service::response_path(starts_sr2(b,reference_read(Replica::R3),archives),|s:rpc::Local|s.returned,
        checkpoint_end(b),delayed_slots(),t,a,v),
    ensures v==1,!compatible(b,v),
        forall|r:Replica| #[trigger] live_pair().contains(r) ==> exists|i:int| 0<=i<a.len()
            && #[trigger] crate::metadata_provenance::restore_at(t,a,i,r),
{
    hide(crate::protocol::accepted);hide(crate::protocol::memory);
    let rho=reference_read(Replica::R3);
    let first=rpc::first_rows(b,13);
    assert(crate::metadata_reader::unanimous(first));assert(rho(first)==Some(first_value(b)));
    crate::metadata_reader::compare_after_first(b,rho,archives,t,a,v);
    let rows=authenticated_result(b,rho,archives,t,a,v);
    assert(!rows.contains_key(Replica::R3) && crate::metadata_reader::valid_root(rows));
    crate::quorum_rpc::latest_is_a_sample(rows);
    let winner=crate::quorum_rpc::latest_site(rows);assert(rows.contains_key(winner) && rows[winner].version==0);
    assert forall|r:Replica| #[trigger] live_pair().contains(r) implies exists|i:int| 0<=i<a.len()
        && #[trigger] crate::metadata_provenance::restore_at(t,a,i,r) by {
        assert(rows.contains_key(r) && rows[r].version==0);
        assert(crate::metadata_provenance::explains(t,a,a.len(),r,rows[r].value,archives));
    }
    history_accepts_exactly_observed_value(b,v);
}

pub open spec fn live_materializations(n:Network<int,Wire>,value:int) -> Set<Replica> {
    all_replicas().filter(|r:Replica|delivery::live(n,at(r)) && (n.locals)(r)==value)
}
// At these two enabled ordinary recovery events no packet is sent or
// received, no application operation is committed, and neither client
// issues a new operation. The issued attestation stays at the live origin's
// incoming slot. A working value and a durable operation record are distinct.
pub proof fn trace_genesis_install(f:CommandSemantics,b:Fork,k:nat)
    requires k==4 || k==5,
    ensures ({
        let r=if k==4 {Replica::R1} else {Replica::R2};let work=BeforeSample::RestoreImages;
        let n=read_net(b,work,k);let u=read_net(b,work,k+1);let v=first_value(b);
        genesis::actual_rebuild_step(f,b,k) && rpc::read_actions(b,work)[k as int]==Action::Local(r,Wire::Copy(1))
          && n.pending==u.pending && n.pending.get(2)==Some(packet_for(b,2)) && delivery::live(u,packet_for(b,2).to)
          && live_materializations(u,v)==live_materializations(n,v).remove(r)
          && live_materializations(read_net(b,work,4),v)==set![crate::origin(b.branch)]
          && live_materializations(read_net(b,work,6),v).is_empty()
          && at_read(b,k).base.calls.is_empty() && at_read(b,k+1).base.calls.is_empty()
          && at_read(b,k).calls==at_read(b,k+1).calls && at_read(b,k).calls[1].answer==Some(v)
          && at_read(b,k).calls[2].answer.is_none() && !compatible(b,1)
    }),
{
    genesis::same_reader_with_repair(f,b,k);actual_first_rpc(b,17);
    let work=BeforeSample::RestoreImages;let n=read_net(b,work,k);let u=read_net(b,work,k+1);
    let r=if k==4 {Replica::R1} else {Replica::R2};let v=first_value(b);
    assert(live_materializations(u,v) =~= live_materializations(n,v).remove(r));
    assert(live_materializations(read_net(b,work,4),v) =~= set![crate::origin(b.branch)]);
    assert(live_materializations(read_net(b,work,6),v) =~= Set::<Replica>::empty());
    assert(at_read(b,k).calls[2].legs =~= at_read(b,k+1).calls[2].legs);
    assert(at_read(b,k).calls =~= at_read(b,k+1).calls);
    history_accepts_exactly_observed_value(b,1);
}

// An alternative local recovery service with actual retained RMW records.
// The journal is per site. Keeping a record says nothing about its total-
// order position or its inclusion in another site's strong history.
pub struct Record { pub op:Op,pub returned:int,pub installed:int }
pub type Journals = spec_fn(Replica)->Seq<Record>;
pub struct Storage { pub core:State<Store>,pub records:Journals }

pub open spec fn save_call(s:Storage,site:Replica,w:Op) -> Storage {
    let (post,old)=weak_rmw(s.core,site,w);
    let record=Record {op:w,returned:old,installed:(post.base.disk)(site).value};
    Storage {core:post,records:|r|if r==site {(s.records)(r).push(record)} else {(s.records)(r)}}
}
pub open spec fn origin_records(f:CommandSemantics) -> Storage {
    let start=Storage {core:initial(engine::engine(f)),records:|_site|Seq::empty()};
    save_call(save_call(start,Replica::R1,Op::W1),Replica::R2,Op::W2)
}
pub open spec fn replay(x:int,records:Seq<Record>) -> Option<int>
    decreases records.len(),
{
    if records.len()==0 {Some(x)} else {
        let r=records[0];
        if (r.op==Op::W1 || r.op==Op::W2) && r.returned==x && r.installed==next(r.op,x) {
            replay(r.installed,records.skip(1))
        } else {None}
    }
}
pub proof fn recorded_returns_constrain_replay(f:CommandSemantics,b:Fork)
    ensures ({
        let log=origin_records(f);let a=(log.records)(Replica::R1);let d=(log.records)(Replica::R2);
        log.core==prefix(b,0) && a.len()==1 && d.len()==1 && a[0].returned==1 && d[0].returned==1
          && replay(1,a)==Some(2) && replay(1,d)==Some(5)
          && replay(1,a+d).is_none() && replay(1,d+a).is_none()
          && compatible(b,replay(1,a).unwrap())==(b.branch==crate::Branch::Beta)
          && compatible(b,replay(1,d).unwrap())==(b.branch==crate::Branch::Alpha)
    }),
{
    crate::facade_hybrid::weak_calls_and_issued_offers(f,b);
    let log=origin_records(f);let a=(log.records)(Replica::R1);let d=(log.records)(Replica::R2);
    assert(a.skip(1).len()==0 && d.skip(1).len()==0);
    assert((a+d).skip(1) =~= d && (d+a).skip(1) =~= a);
    reveal_with_fuel(replay,3);
    history_accepts_exactly_observed_value(b,2);history_accepts_exactly_observed_value(b,5);
}

pub struct LocalRebuild {
    pub core:State<Store>,pub net:Network<int,Wire>,pub records:Journals,pub repairs:spec_fn(Replica)->nat,
}
pub open spec fn before_rebuild(f:CommandSemantics,b:Fork) -> LocalRebuild {
    LocalRebuild {core:prefix(b,17),net:checkpoint_end(b),records:origin_records(f).records,repairs:|_site|0}
}
pub open spec fn can_replay(s:LocalRebuild,r:Replica) -> bool {
    s.core.base.live.contains(r) && !s.core.closed.contains(r) && (s.core.base.disk)(r).version==0
        && (s.records)(r).len()>0 && replay((engine::start().disk)(r).value,(s.records)(r)).is_some()
}
pub open spec fn restore(s:LocalRebuild,r:Replica) -> LocalRebuild {
    let x=replay((engine::start().disk)(r).value,(s.records)(r)).unwrap();
    let disk=|q|if q==r {Stamp{value:x,..(s.core.base.disk)(q)}} else {(s.core.base.disk)(q)};
    let net=Network {locals:|q|if q==r {x} else {(s.net.locals)(q)},..s.net};
    LocalRebuild {net,core:State {base:Store {disk,..s.core.base},..s.core},
        repairs:|q|if q==r {(s.repairs)(q)+1} else {(s.repairs)(q)},..s}
}
pub proof fn redo_with_weak_redo_records(f:CommandSemantics,b:Fork)
    ensures ({
        let s=before_rebuild(f,b);let m=restore(s,Replica::R1);let u=restore(m,Replica::R2);
        can_replay(s,Replica::R1) && can_replay(m,Replica::R2)
          && (u.repairs)(Replica::R1)==1 && (u.repairs)(Replica::R2)==1 && u.records==s.records
          && m.core==s.core && u.core==s.core && m.net==s.net && u.net==s.net
          && u.core.calls[1].answer==Some(first_value(b)) && u.core.calls[2].answer.is_none()
          && crate::validator_block::blocked(u.core)
          && (u.net.locals)(Replica::R1)==2 && (u.net.locals)(Replica::R2)==5
          && u.net.pending.get(2)==Some(packet_for(b,2))
    }),
{
    let s=before_rebuild(f,b);let m=restore(s,Replica::R1);let u=restore(m,Replica::R2);
    recorded_returns_constrain_replay(f,b);crate::validator_block::at_the_real_cut(b);actual_first_rpc(b,17);
    assert(m.core.base.disk =~= s.core.base.disk);assert(u.core.base.disk =~= s.core.base.disk);
    assert(m.net.locals =~= s.net.locals);assert(u.net.locals =~= s.net.locals);
}
}
