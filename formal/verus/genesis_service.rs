use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Process};
use crate::stock_facade::*;
use crate::facade_linear::CommandSemantics;
use crate::facade_hybrid::{inner,storage,prefix};
use crate::facade_transport::{self,client1,service,valid,actual_first_rpc};
use crate::ordered_round::{self as base,Store,Work,engine};
use crate::metadata_pair::{BeforeSample,read_net,read_actions};

verus! {

// A second possible ordinary storage interface: a site at applied position
// zero may reinstall its configured genesis. It needs no saved image and
// cannot generate a snapshot of a later position from genesis alone.
pub open spec fn can_rebuild(s: State<Store>,r:Replica) -> bool {
    let d=(s.base.disk)(r);
    s.base.live.contains(r) && !s.closed.contains(r) && d.version==0 && d.value!=(base::start().disk)(r).value
}
pub open spec fn rebuild(s: State<Store>,r:Replica) -> State<Store> {
    let disk=|q:Replica| if q==r {(base::start().disk)(r)} else {(s.base.disk)(q)};
    State {base:base::Store{disk,..s.base},..s}
}
pub open spec fn service_step(f: CommandSemantics,s: State<Store>,ev: Event<Work>,redo: Option<Replica>,u: State<Store>) -> bool {
    match redo {
        None=>enabled(engine(f),s,ev) && u==step(engine(f),s,ev),
        Some(r)=>ev is Idle && can_rebuild(s,r) && u==rebuild(s,r),
    }
}
pub proof fn dormant_on_stock(f: CommandSemantics,s: State<Store>,r:Replica)
    requires reachable(engine(f),s),
    ensures !can_rebuild(s,r),
{
    base::api_and_majorities(f);reachable_good(engine(f),s);
    if !s.closed.contains(r) {assert((engine(f).cell)(s.base,r)==1);}
}
// At every index in every extended stock schedule the only possible service
// steps are original steps. Conversely every original choice is still enabled.
pub proof fn stock_path_uses_only_original_steps(f:CommandSemantics,t:Seq<State<Store>>,a:Seq<Event<Work>>,r:Seq<Option<Replica>>,k:nat)
    requires reachable(engine(f),t[0]), k<=a.len(),t.len()==a.len()+1,r.len()==a.len(),
        forall|i:int| 0<=i<a.len() ==> #[trigger] service_step(f,t[i],a[i],r[i],t[i+1]),
    ensures reachable(engine(f),t[k as int]),forall|i:int| 0<=i<k ==> (#[trigger] r[i]).is_none()
        && enabled(engine(f),t[i],a[i]) && t[i+1]==step(engine(f),t[i],a[i]),
    decreases k,
{
    if k>0 {
        let h=(k-1) as nat;stock_path_uses_only_original_steps(f,t,a,r,h);
        assert(service_step(f,t[h as int],a[h as int],r[h as int],t[h as int+1]));
        if let Some(site)=r[h as int] {dormant_on_stock(f,t[h as int],site);}
        crate::facade_quorum::extend_reach(engine(f),t[h as int],seq![t[h as int],t[k as int]],seq![a[h as int]]);
    }
}

pub open spec fn phases(r:Replica,k:nat) -> Leg {
    let d:nat=if r==Replica::R1 {0} else {1};let initial=(base::start().disk)(r);
    if r==Replica::R3 || k<=d {Leg::Unsent} else if k<=2+d {Leg::Request}
    else if k<=6+d {Leg::AtServer} else if k<=8+d {Leg::InFlight(initial)} else {Leg::Received(initial)}
}
pub open spec fn at_read(b:Fork,k:nat) -> State<Store> {
    let n=read_net(b,BeforeSample::RestoreImages,k);
    let c=Call {legs: |r|phases(r,k),answer:if k>=11 {Some(1)} else {None},..fresh(Method::Read)};
    State {base:storage(n),closed:Set::empty(),calls:Map::empty().insert(1nat,client1(b,17)).insert(2,c)}
}
pub open spec fn actual_rebuild_step(f:CommandSemantics,b:Fork,k:nat) -> bool {
    let kind=BeforeSample::RestoreImages;let n=read_net(b,kind,k);let a=read_actions(b,kind)[k as int];
    let s=at_read(b,k);let u=at_read(b,k+1);
    let redo=match a {Action::Local(site,_)=>Some(site),_=>None};
    delivery::enabled(n,a) && valid(n,service(n,a,Process::SecondClient),s.calls[2],Process::SecondClient)
        && service_step(f,s,inner(n,a),redo,u)
        && match a {Action::Local(r,w)=>w==Wire::Copy((base::start().disk)(r).value)
            && n.pending==read_net(b,kind,k+1).pending,_=>true}
}

pub proof fn same_reader_with_repair(f: CommandSemantics,b:Fork,k:nat)
    requires k<11,
    ensures actual_rebuild_step(f,b,k),
{
    hide(facade_transport::at_time);
    let kind=BeforeSample::RestoreImages;let n=read_net(b,kind,k);let a=read_actions(b,kind)[k as int];
    let s=at_read(b,k);let u=at_read(b,k+1);
    prefix_index(k as int);actual_first_rpc(b,17);
    crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R1);crate::mixed_sources::actual_disk_before_sr2(b,17,Replica::R2);
    let y=match a {Action::Local(r,_)=>rebuild(s,r),_=>step(engine(f),s,inner(n,a))};
    assert(y.base.disk =~= u.base.disk);assert(y.base.live =~= u.base.live);
    assert(y.closed =~= u.closed);assert(y.calls[2].legs =~= u.calls[2].legs);assert(y.calls =~= u.calls);
}

pub(crate) proof fn repair_checkpoint(b:Fork)
    ensures at_read(b,0)==prefix(b,17),
{
    hide(facade_transport::at_time);
    actual_first_rpc(b,17);
    assert(at_read(b,0).base.live =~= prefix(b,17).base.live);
    assert(at_read(b,0).base.disk =~= prefix(b,17).base.disk);
    assert(at_read(b,0).calls[2].legs =~= fresh(Method::Read).legs);
    assert(at_read(b,0).calls =~= prefix(b,17).calls);
}

pub open spec fn repaired_trace(f:CommandSemantics,b:Fork) -> bool {
    forall|k:nat| k<11 ==> #[trigger] actual_rebuild_step(f,b,k)
}
proof fn check_repaired_trace(f:CommandSemantics,b:Fork)
    ensures repaired_trace(f,b),
{
    assert forall|k:nat| k<11 implies #[trigger] actual_rebuild_step(f,b,k) by {same_reader_with_repair(f,b,k);}
}
pub proof fn both_real_reads_with_local_service(f:CommandSemantics,n:Notice)
    ensures at_read(alpha(n),0)==prefix(alpha(n),17),at_read(beta(n),0)==prefix(beta(n),17),
        prefix(alpha(n),17).calls[1].answer==Some(5),prefix(beta(n),17).calls[1].answer==Some(2),
        at_read(alpha(n),11).calls[2].answer==Some(1),at_read(beta(n),11).calls[2].answer==Some(1),
        repaired_trace(f,alpha(n)),repaired_trace(f,beta(n)),
        !(exists|ao:Seq<crate::Op>,ax:Seq<int>,bo:Seq<crate::Op>,bx:Seq<int>|
            #[trigger] crate::legal(ao,ax,5,1) && #[trigger] crate::legal(bo,bx,2,1)),
{
    hide(repaired_trace);hide(facade_transport::at_time);
    hide(crate::legal);
    if exists|ao:Seq<crate::Op>,ax:Seq<int>,bo:Seq<crate::Op>,bx:Seq<int>|
        #[trigger] crate::legal(ao,ax,5,1) && #[trigger] crate::legal(bo,bx,2,1) {
        let (ao,ax,bo,bx)=choose|ao:Seq<crate::Op>,ax:Seq<int>,bo:Seq<crate::Op>,bx:Seq<int>|
            #[trigger] crate::legal(ao,ax,5,1) && #[trigger] crate::legal(bo,bx,2,1);
        crate::conditional_history_contradiction(ao,ax,bo,bx,1);
    }
    repair_checkpoint(alpha(n));repair_checkpoint(beta(n));
    actual_first_rpc(alpha(n),17);actual_first_rpc(beta(n),17);
    check_repaired_trace(f,alpha(n));check_repaired_trace(f,beta(n));
}

}
