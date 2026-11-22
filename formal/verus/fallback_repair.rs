use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Packet,Network,Path as Route,Process};
use crate::stock_facade::*;
use crate::facade_linear::CommandSemantics;
use crate::facade_hybrid::{inner,prefix};
use crate::facade_transport::{service,valid};
use crate::ordered_round::{engine,Store,Work};
use crate::ordered_store::Stamp;
use crate::fallback_program::{self as prog,apply_event};
use crate::fallback_wait::{physical,source};
use crate::first_copy_wait::{Cut,Turn,response,new_copy};
use crate::second_copy_schedule as sched;
use crate::genesis_escape::resolver;
use crate::genesis_service as genesis;
use crate::promotion_wait::*;
use crate::open_read_repair::{self as open,ordinary_slot,image_only};
use crate::read_recovery::compatible;

verus! {

pub open spec fn root_reply() -> Packet<Wire> {
    Packet{path:Route::FirstReadReply,from:at(Replica::R3),to:Process::FirstClient,input:Wire::Reply(1)}
}
pub open spec fn wire(k:nat) -> Action<Wire> {
    if k==0 {Action::Local(Replica::R3,Wire::Copy(1))} else if k==1 {Action::Send(8,root_reply())}
    else if k==2 {Action::Deliver(8)} else {Action::Strong(Process::FirstClient)}
}
pub open spec fn state(b:Fork,k:nat) -> Cut {
    let s=prog::cut(b,11);let r3=Replica::R3;
    if k==0 {s} else {
        let p=if k==2 {s.net.pending.insert(8,root_reply())} else {s.net.pending};
        let n=Network{locals:|r|if r==r3 {1} else {(s.net.locals)(r)},pending:p,..s.net};
        let core=genesis::rebuild(s.core,r3);let c=core.calls[1];let root=Stamp{version:0,value:1};
        let call=Call {legs:|r|if r!=r3 {(c.legs)(r)} else if k==1 {Leg::AtServer} else if k==2 {Leg::InFlight(root)}
            else {Leg::Received(root)},answer:if k>=4 {Some(1)} else {None},..c};
        Cut{net:n,core:State{calls:core.calls.insert(1,call),..core}}
    }
}
pub open spec fn route(b:Fork) -> Path<Cut,Turn> {
    Path {states:Seq::new(5,|i:int|state(b,i as nat)),
        actions:Seq::new(4,|i:int|Turn{ordinary:inner(state(b,i as nat).net,wire(i as nat)),wire:wire(i as nat)})}
}
// Rebuilding the configured zero-position image at R3 is a real local
// service. C1 has only its anchored noninitial reply before R3 samples.
pub proof fn repair_can_serve_first(b:Fork,f:CommandSemantics,repairs:Set<Replica>)
    requires repairs.contains(Replica::R3),
    ensures ({
        let p=route(b);
        first_return(|s,a,u|physical(f,repairs,s,a,u),|s|response(s),prog::cut(b,11),p)
            && !uses(p,|s,a,u|new_copy(s,a,u)) && uses(p,|s,a,u|source(1,s,a,u))
            && p.states.last().core.calls[1].answer==Some(1)
            && p.states.last().net.pending==prog::cut(b,11).net.pending
            && crate::irrevocable_order::single_read(crate::irrevocable_order::read_genesis(),1)
    }),
{
    let p=route(b);let r3=Replica::R3;let c=Process::FirstClient;
    assert forall|i:int| 0<=i<4 implies physical(f,repairs,p.states[i],#[trigger] p.actions[i],p.states[i+1])
        && !new_copy(p.states[i],p.actions[i],p.states[i+1]) by {
        let s=p.states[i];let u=p.states[i+1];let a=p.actions[i];let v=apply_event(resolver(),engine(f),s.core,a.ordinary);
        let y=if i==0 {genesis::rebuild(v,r3)} else {v};
        assert(i==0 || i==1 || i==2 || i==3);
        if i==3 {assert(rows(s.core.calls[1]).get(r3)==Some(Stamp{version:0,value:1}));}
        assert(y.closed =~= u.core.closed);assert(y.base.disk =~= u.core.base.disk);
        assert(y.calls[1].legs =~= u.core.calls[1].legs);assert(y.calls =~= u.core.calls);
        let n=delivery::advance(|x,w|cell(x,w),s.net,a.wire);
        assert(n.pending =~= u.net.pending);assert(n.locals =~= u.net.locals);
        assert(valid(s.net,service(s.net,a.wire,c),s.core.calls[1],c));
    }
    assert(source(1,p.states[0],p.actions[0],p.states[1]));
    assert(pending_before(|s|response(s),p));
    crate::irrevocable_order::separate_histories(b);
}

// Once R3 crashes it cannot provide another fallback sample. This reduces
// the full fallback poll to the existing audited original poll on every
// reachable no-new-command suffix, including arbitrary real image changes.
proof fn same_after_crash(f:CommandSemantics,s:State<Store>,e:Event<Work>)
    requires open::audit(s),enabled(engine(f),s,e),
    ensures apply_event(resolver(),engine(f),s,e)==step(engine(f),s,e),
{
    if let Event::Poll(id)=e {
        assert(id==2);
        assert(ordinary_slot(Replica::R3,(s.calls[2].legs)(Replica::R3)));
        assert(!rows(s.calls[2]).contains_key(Replica::R3));
        assert(apply_event(resolver(),engine(f),s,e).calls =~= step(engine(f),s,e).calls);
    }
}
pub proof fn all_open_sr2_repairs(b:Fork,f:CommandSemantics,t:Seq<State<Store>>,a:Seq<Event<Work>>,k:nat)
    requires t.len()==a.len()+1,t[0]==prefix(b,17),k<=a.len(),
        forall|i:int| 0<=i<a.len() ==> {
            let e=#[trigger] a[i];!(e is Invoke) && enabled(engine(f),t[i],e)
                && image_only(apply_event(resolver(),engine(f),t[i],e),t[i+1])
        },
    ensures open::audit(t[k as int]),match t[k as int].calls[2].answer {Some(v)=>v==1 && !compatible(b,v),None=>true},
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat;all_open_sr2_repairs(b,f,t,a,i);
        assert(enabled(engine(f),t[i as int],a[i as int]));
        same_after_crash(f,t[i as int],a[i as int]);
        open::preserved(f,t[i as int],a[i as int],t[k as int]);
    } else {open::image_repairs_cannot_serve_h(f,b,seq![t[0]],Seq::empty(),0);}
    crate::read_recovery::history_accepts_exactly_observed_value(b,1);
}
// The physical repair witness for C2 with this very same resolver.
// Both restorations replay the configured image before either sample.
pub proof fn genuine_second_read_repair(b:Fork,f:CommandSemantics,k:nat)
    requires k<11,
    ensures ({
        let work=crate::metadata_pair::BeforeSample::RestoreImages;
        let a=crate::metadata_pair::read_actions(b,work)[k as int];
        let n=crate::metadata_pair::read_net(b,work,k);
        let s=genesis::at_read(b,k);let u=genesis::at_read(b,k+1);
        delivery::enabled(n,a) && valid(n,service(n,a,Process::SecondClient),s.calls[2],Process::SecondClient)
            && match a {
                Action::Local(r,w)=>inner(n,a) is Idle && w==Wire::Copy(1) && genesis::can_rebuild(s,r) && u==genesis::rebuild(s,r),
                _=>enabled(engine(f),s,inner(n,a)) && u==apply_event(resolver(),engine(f),s,inner(n,a)),
            }
            && genesis::at_read(b,0)==prefix(b,17) && genesis::at_read(b,11).calls[2].answer==Some(1) && !compatible(b,1)
    }),
{
    genesis::same_reader_with_repair(f,b,k);genesis::repair_checkpoint(b);
    crate::facade_transport::actual_first_rpc(b,17);prefix_index(k as int);
    let s=genesis::at_read(b,k);let work=crate::metadata_pair::BeforeSample::RestoreImages;
    let e=inner(crate::metadata_pair::read_net(b,work,k),crate::metadata_pair::read_actions(b,work)[k as int]);
    if let Event::Poll(id)=e {
        assert(id==2 && !rows(s.calls[id]).contains_key(Replica::R3));
        assert(apply_event(resolver(),engine(f),s,e).calls =~= step(engine(f),s,e).calls);
    }
    crate::read_recovery::history_accepts_exactly_observed_value(b,1);
}

}
