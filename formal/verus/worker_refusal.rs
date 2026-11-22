// Audit the existing guarded worker. No new handler or application
// invocation is inserted into either original execution.
use vstd::prelude::*;
use crate::{Op,Replica};
use crate::checkpoint::{Fork,live_pair,all_replicas};
use crate::facade_linear::CommandSemantics;
use crate::facade_progress::StockRun;
use crate::ordered_round::{self as base,Store,Work};
use crate::ordered_store::majority;
use crate::ordinary_fairness as jobs;
use crate::promotion_wait as wait;
use crate::stock_availability::Stream;
use crate::stock_facade::{Input,Method,backend_reachable};
use crate::weak_round as weak;
use crate::worker_guard as guard;
use crate::worker_transfer as transfer;

verus! {

pub open spec fn register(f:CommandSemantics, s:Store, id:nat) -> Store {
    base::advance(f,s,Input::Submit(id,Method::Read))
}
pub open spec fn service_option(f:CommandSemantics, s:Store, id:nat) -> bool {
    (guard::engine(f).ready)(s,Input::Submit(id,Method::Read))
        && wait::can_finish(guard::internal(f),guard::finished(id),register(f,s,id))
}

// Includes every enabled internal action in the read-only workload. The
// backward direction uses an actual guarded Serve on its own live disks.
pub proof fn exactly_usable(f:CommandSemantics, s:Store, id:nat)
    requires guard::only_reads(s), !s.calls.contains_key(id), !s.done.contains_key(id),
    ensures service_option(f,s,id) == (exists|q:Set<Replica>| #[trigger] guard::usable(s,q)),
{
    let x=register(f,s,id); let step=guard::internal(f); let done=guard::finished(id);
    assert(guard::only_reads(x));
    if wait::can_finish(step,done,x) {
        let t=choose|t:wait::Path<Store,guard::Internal>| #[trigger] wait::first_return(step,done,x,t);
        let w=guard::remove_all_weak_work_from_service(f,x,id,t);
        let q=w.actions[0]->Ordinary_0->Serve_1;
        assert(guard::usable(x,q)); assert(guard::usable(s,q));
    } else if exists|q:Set<Replica>| #[trigger] guard::usable(s,q) {
        let q=choose|q:Set<Replica>| #[trigger] guard::usable(s,q);
        let a=Work::Serve(id,q); let y=base::advance(f,x,Input::Work(a));
        let t=wait::Path { states:seq![x,y], actions:seq![guard::Internal::Ordinary(a)] };
        assert(wait::first_return(step,done,x,t)); assert(wait::can_finish(step,done,x));
    }
}
pub open spec fn outstanding() -> weak::World {
    let f=weak::paper_ops();
    weak::step(f,weak::step(f,weak::start(),weak::Action::Send(0,weak::request(Op::W1))),
        weak::Action::Send(1,weak::request(Op::W2)))
}

proof fn live_disk_quorums(s:Store, bad:Set<Replica>)
    requires s.live==all_replicas(),
        forall|r:Replica| guard::ordinary_image(#[trigger] (s.disk)(r)) == !bad.contains(r),
    ensures forall|q:Set<Replica>| #[trigger] guard::usable(s,q) == (majority(q) && q.disjoint(bad)),
{
    assert forall|q:Set<Replica>| #[trigger] guard::usable(s,q) == (majority(q) && q.disjoint(bad)) by {
        assert(q.subset_of(all_replicas())) by {
            assert forall|r:Replica| #[trigger] q.contains(r) implies all_replicas().contains(r) by {match r {_=>{}}}
        }
        if guard::usable(s,q) {
            assert forall|r:Replica| #[trigger] q.contains(r) implies !bad.contains(r) by {assert(guard::ordinary_image((s.disk)(r)));}
        }
        if q.disjoint(bad) {
            assert forall|r:Replica| q.contains(r) implies guard::ordinary_image(#[trigger] (s.disk)(r)) by {};
        }
    }
}

// These are enabled weak-client events leading to both actual SR1
// prefixes. service_option probes a possible registered worker at a cut;
// SR1's direct path remains separate. Neither probe is issued in the runs.
pub proof fn locate_first_losses(b:Fork)
    ensures ({
        let f=weak::paper_ops(); let w=outstanding(); let x=w.front.base;
        let l=weak::step(f,w,weak::Action::Handle(0)); let r=weak::step(f,w,weak::Action::Handle(1));
        let both=weak::step(f,l,weak::Action::Handle(1)); let lr=both.front.base;
        let end=weak::step(f,weak::step(f,both,weak::Action::Receive(0)),weak::Action::Receive(1));
        weak::enabled(w,weak::Action::Handle(0)) && weak::enabled(w,weak::Action::Handle(1))
            && weak::enabled(l,weak::Action::Handle(1)) && weak::enabled(r,weak::Action::Handle(0))
            && both==weak::step(f,r,weak::Action::Handle(0)) && end.front==crate::facade_hybrid::prefix(b,0)
            && end.answers.get(weak::request(Op::W1).id)==Some(1) && end.answers.get(weak::request(Op::W2).id)==Some(1)
            && x.live==all_replicas() && lr.live==x.live
            && (forall|q:Set<Replica>| #[trigger] guard::usable(x,q)==majority(q))
            && (forall|q:Set<Replica>| #[trigger] guard::usable(l.front.base,q)==(majority(q) && !q.contains(Replica::R1)))
            && (forall|q:Set<Replica>| #[trigger] guard::usable(r.front.base,q)==(majority(q) && !q.contains(Replica::R2)))
            && (forall|q:Set<Replica>| !#[trigger] guard::usable(lr,q))
            && service_option(f,x,2) && service_option(f,l.front.base,2) && service_option(f,r.front.base,2)
            && !service_option(f,lr,2)
    }),
{
    weak::actual_overlap(b); let f=weak::paper_ops(); let w=outstanding(); let x=w.front.base;
    let l=weak::step(f,w,weak::Action::Handle(0)).front.base;
    let r=weak::step(f,w,weak::Action::Handle(1)).front.base;
    let y=weak::step(f,weak::step(f,w,weak::Action::Handle(0)),weak::Action::Handle(1)).front.base;
    let a=Replica::R1; let c=Replica::R2; let d=Replica::R3;
    live_disk_quorums(x,Set::empty()); live_disk_quorums(l,set![a]); live_disk_quorums(r,set![c]);
    live_disk_quorums(y,set![a,c]);
    assert forall|q:Set<Replica>| !#[trigger] guard::usable(y,q) by {
        if guard::usable(y,q) { assert(q.disjoint(set![a,c])); }
    }
    exactly_usable(f,x,2); exactly_usable(f,l,2); exactly_usable(f,r,2); exactly_usable(f,y,2);
    assert(guard::usable(x,live_pair())); assert(guard::usable(l,set![c,d])); assert(guard::usable(r,set![a,d]));
}

// Check all future internal arms, including arbitrary allowed deliveries and
// ordinary work. Once every quorum guard is false, no such arm can open it
// in the four-operation workload. The predecessor result above locates the
// loss before any inter-replica replication or confirmation.
pub proof fn no_future_unlock(f:CommandSemantics,start:Store,id:nat,t:wait::Path<Store,guard::Internal>,k:nat)
    requires guard::only_reads(start),start.calls.get(id)==Some(Method::Read),
        forall|q:Set<Replica>| !#[trigger] guard::usable(start,q),
        t.states.len()==t.actions.len()+1,t.states[0]==start,k<=t.actions.len(),wait::valid_edges(guard::internal(f),t),
    ensures guard::only_reads(t.states[k as int]),t.states[k as int].calls==start.calls,
        forall|q:Set<Replica>| !(#[trigger] (guard::engine(f).ready)(t.states[k as int],Input::Work(Work::Serve(id,q)))),
{
    guard::quorum_before(f,t,k,live_pair());
    assert forall|q:Set<Replica>| !(#[trigger] (guard::engine(f).ready)(t.states[k as int],Input::Work(Work::Serve(id,q)))) by {
        guard::quorum_before(f,t,k,q); assert(!guard::usable(start,q));
    }
}

// If an application command really is pending, its guard differs from a
// read's. Its own published response and new version are part of the
// transition. Neither original run has such a command in the stock queue.
pub proof fn an_existing_command_can_restore_an_image(f:CommandSemantics,s:Store,id:nat,code:nat,q:Set<Replica>)
    requires s.calls.get(id)==Some(Method::Command(code)),!s.done.contains_key(id),majority(q),q.subset_of(s.live),
    ensures ({
        let a=Input::Work(Work::Serve(id,q)); let u=base::advance(f,s,a);
        let old=(s.disk)(base::current(s,q)); let (value,reply)=f(code,old.value);
        (guard::engine(f).ready)(s,a) && guard::usable(u,q) && u.calls==s.calls && u.done.get(id)==Some(reply)
            && (forall|r:Replica| q.contains(r) ==> (#[trigger] (u.disk)(r)).version==old.version+1 && (u.disk)(r).value==value)
    }),
{}

// The fair worker's maintained duties are service of a pending call
// on an available quorum and a tick at a live replica. Crash and stop
// are environmental events, never owed jobs.
pub enum Duty { Serve(nat,Set<Replica>), Tick(Replica) }
pub open spec fn work(j:Duty) -> Work {
    match j {Duty::Serve(id,q)=>Work::Serve(id,q),Duty::Tick(r)=>Work::Tick(r)}
}
pub open spec fn tasks(f:CommandSemantics) -> jobs::Scheduler<Store,Input<Work>,Duty> {
    jobs::Scheduler { enabled:|s,j|(guard::engine(f).ready)(s,Input::Work(work(j))),
        taken:|_s,a,_t,j|a==Input::Work(work(j)) }
}
pub open spec fn loaded(f:CommandSemantics) -> Store { register(f,transfer::shadow(f),2) }
pub open spec fn after_submit(b:Fork) -> StockRun<Store,Work> {
    Stream { state:|i:nat|guard::queued(b,i+9).base,event:|i:nat|guard::input_at(b,i+9) }
}
pub open spec fn erased(f:CommandSemantics,b:Fork) -> StockRun<Store,Work> {
    Stream { state:|_i:nat|loaded(f),event:(after_submit(b)).event }
}
pub open spec fn missing() -> Duty { Duty::Serve(2,live_pair()) }

proof fn inputs_after_submit(b:Fork,i:nat)
    ensures ({
        let a=guard::input_at(b,i+9);
        (a==Input::Idle || a==Input::Work(Work::Tick(Replica::R1)) || a==Input::Work(Work::Tick(Replica::R2)))
          && (i+9>=14 && (i+9)%3==0 ==> a==Input::Work(Work::Tick(Replica::R1)))
          && (i+9>=14 && (i+9)%3==1 ==> a==Input::Work(Work::Tick(Replica::R2)))
    }),
{
    hide(crate::facade_transport::at_time);
    let k=i+9; crate::facade_transport::actual_second_rpc(b,k);
    crate::facade_transport::actual_first_rpc(b,17);
    if k<14 { crate::checkpoint::prefix_index(k as int); }
}

proof fn compare_guards(f:CommandSemantics,s:Store,j:Duty)
    requires guard::mixed_job(s),
    ensures (tasks(f).enabled)(loaded(f),j) == (j==missing() || (tasks(f).enabled)(s,j)),
        !(tasks(f).enabled)(s,missing()),
{
    let q=live_pair(); assert(q.contains(Replica::R1)); assert(!guard::ordinary_image((s.disk)(Replica::R1)));
    match j {
        Duty::Serve(id,m)=>{
            if m.subset_of(q) && majority(m) { assert(m =~= q); }
        },
        Duty::Tick(_)=>{},
    }
}

pub proof fn unique_refused_job(f:CommandSemantics,b:Fork)
    ensures ({
        let src=erased(f,b); let dst=after_submit(b); let p=guard::engine(f);
        let s=jobs::duties(tasks(f),src); let h=jobs::duties(tasks(f),dst);
        backend_reachable(p,loaded(f)) && (p.submitted)(loaded(f),2)==Some(Method::Read)
            && (p.client)(loaded(f),2) && (p.up)(loaded(f))==live_pair()
            && (forall|i:nat| {let a=#[trigger] (src.event)(i);
                (p.ready)((src.state)(i),a) && (src.state)(i+1)==(p.step)((src.state)(i),a)})
            && jobs::fair(h) && (forall|start:nat,j:Duty| !#[trigger] jobs::scheduled(s,start,j) == (j==missing()))
            && (forall|i:nat| !(#[trigger] (h.enabled)(i,missing())) && !(s.taken)(i,missing()))
            && jobs::refusals(h,0,missing())
            && (forall|plan:jobs::Support<Duty,Duty>| !#[trigger] jobs::supports(s,h,plan))
    }),
{
    hide(crate::facade_transport::at_time);
    hide(guard::guarded_prefix); hide(crate::fallback_program::stock_contract);
    let src=erased(f,b); let dst=after_submit(b); let p=guard::engine(f);
    let s=jobs::duties(tasks(f),src); let h=jobs::duties(tasks(f),dst);
    guard::assembled(f,b);
    let t=seq![base::start(),base::advance(f,base::start(),Input::Work(Work::StopClient(1))),transfer::shadow(f),loaded(f)];
    let a=seq![Input::Work(Work::StopClient(1)),Input::Work(Work::Crash(Replica::R3)),Input::Submit(2,Method::Read)];
    assert(crate::stock_facade::backend_path(p,t,a)) by {
        assert forall|i:int| 0<=i<a.len() implies
            (p.ready)(t[i],#[trigger] a[i]) && t[i+1]==(p.step)(t[i],a[i]) by {crate::checkpoint::prefix_index(i);}
    }
    assert(backend_reachable(p,loaded(f)));
    assert((p.up)(loaded(f)) =~= live_pair());
    assert forall|i:nat| {let a=#[trigger] (src.event)(i);
        (p.ready)((src.state)(i),a) && (src.state)(i+1)==(p.step)((src.state)(i),a)} by {inputs_after_submit(b,i);}
    assert forall|i:nat,j:Duty| #[trigger] jobs::discharged(s,i,j)==(jobs::discharged(h,i,j) && j!=missing()) by {
        assert(guard::real_step(f,b,i+9)); compare_guards(f,(dst.state)(i),j); inputs_after_submit(b,i);
    }
    assert forall|i:nat| !(#[trigger] (h.enabled)(i,missing())) && !(s.taken)(i,missing()) by {
        assert(guard::real_step(f,b,i+9)); compare_guards(f,(dst.state)(i),missing()); inputs_after_submit(b,i);
    }
    assert forall|start:nat,j:Duty| #[trigger] jobs::scheduled(h,start,j) by {
        assert(guard::scheduled_work(f,guard::worker_run(b),start+9,work(j))) by {match j {Duty::Serve(_,_)=>{},Duty::Tick(_)=>{}}}
        let k=choose|k:nat| k>=start+9 && #[trigger] guard::served_or_disabled(f,guard::worker_run(b),k,work(j));
        let i=(k-9) as nat; assert(jobs::discharged(h,i,j));
    }
    assert forall|start:nat,j:Duty| !#[trigger] jobs::scheduled(s,start,j) == (j==missing()) by {
        if j!=missing() {
            assert(jobs::scheduled(h,start,j));
            let k=choose|k:nat| k>=start && #[trigger] jobs::discharged(h,k,j);
            assert(jobs::discharged(s,k,j));
        }
    }
    jobs::locate_refusal(s,h,0,missing());
    assert forall|plan:jobs::Support<Duty,Duty>| !#[trigger] jobs::supports(s,h,plan) by {
        if jobs::supports(s,h,plan) {jobs::fair_support_transfers(s,h,plan);assert(jobs::scheduled(s,0,missing()));}
    }
}

pub open spec fn stock_route(f:CommandSemantics,t:Seq<Store>,w:Seq<Work>,v:int) -> bool {
    crate::facade_quorum::base_service(guard::engine(f),base::used(),transfer::shadow(f),2,live_pair(),t,w,v)
}
proof fn locate_update(f:CommandSemantics,t:Seq<Store>,w:Seq<Work>,v:int,k:nat) -> (i:nat)
    requires stock_route(f,t,w,v), k<=w.len(), t[k as int].done.contains_key(2),
    ensures i<k, w[i as int]==work(missing()),
    decreases k,
{
    assert(k>0); let j=(k-1) as nat;
    if t[j as int].done.contains_key(2) { locate_update(f,t,w,v,j) } else {
        let a=Input::Work(w[j as int]);
        assert((guard::engine(f).ready)(t[j as int],a) && t[k as int]==base::advance(f,t[j as int],a));
        assert(base::used()(2,t[j as int],a).subset_of(live_pair()));
        match w[j as int] { Work::Serve(id,q)=>{assert(id==2);assert(q =~= live_pair());}, _=>{} }
        j
    }
}

// The single missing fairness obligation also occurs in EVERY stock
// service allowed by A's any-majority clause at this cut.
pub proof fn indispensable_stock_instruction(f:CommandSemantics)
    ensures (exists|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] stock_route(f,t,w,v)),
        forall|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] stock_route(f,t,w,v) ==> w.contains(work(missing())),
{
    let x=transfer::shadow(f); let p=guard::engine(f); let q=live_pair();
    guard::full_stock(f);
    let a=seq![Input::Work(Work::StopClient(1)),Input::Work(Work::Crash(Replica::R3))];
    let s=seq![base::start(),base::advance(f,base::start(),a[0]),x];
    assert(crate::stock_facade::backend_path(p,s,a)) by {
        assert forall|i:int| 0<=i<a.len() implies (p.ready)(s[i],#[trigger] a[i]) && s[i+1]==(p.step)(s[i],a[i])
            by {assert(i==0 || i==1);}
    }
    assert(backend_reachable(p,x) && majority(q) && q.subset_of(x.live));
    assert(crate::facade_quorum::any_backend_majority(p,base::used()));
    assert((p.submitted)(x,2nat).is_none() && (p.client)(x,2nat) && q.subset_of((p.up)(x)));
    let (t,w,v)=choose|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] crate::facade_quorum::base_service(p,base::used(),x,2,q,t,w,v);
    assert(stock_route(f,t,w,v));
    assert forall|t:Seq<Store>,w:Seq<Work>,v:int| #[trigger] stock_route(f,t,w,v) implies w.contains(work(missing()))
        by {let i=locate_update(f,t,w,v,w.len());assert(w[i as int]==work(missing()));}
}

// Evaluate the old unguarded scheduler on exactly the same inputs and
// working disks. Its worker would accept the missing job at every cut.
// The given pending tape therefore fails that scheduler's fairness test.
pub proof fn same_inputs_under_the_unguarded_scheduler(f:CommandSemantics,b:Fork)
    ensures ({
        let raw=jobs::Scheduler{enabled:|x,j|base::ready(x,Input::Work(work(j))),..tasks(f)};
        let s=jobs::duties(tasks(f),erased(f,b)); let h=jobs::duties(raw,after_submit(b));
        let direct=jobs::Support{remaining:|_i:nat,_j:Duty|0nat,helper:|_i:nat,j:Duty|j};
        jobs::supports(s,h,direct) && !jobs::fair(h)
            && (forall|i:nat| (#[trigger] (h.enabled)(i,missing())) && !(h.taken)(i,missing()))
    }),
{
    hide(guard::guarded_prefix); hide(crate::fallback_program::stock_contract);
    let raw=jobs::Scheduler{enabled:|x,j|base::ready(x,Input::Work(work(j))),..tasks(f)};
    let s=jobs::duties(tasks(f),erased(f,b)); let h=jobs::duties(raw,after_submit(b));
    let direct=jobs::Support{remaining:|_i:nat,_j:Duty|0nat,helper:|_i:nat,j:Duty|j};
    guard::assembled(f,b); unique_refused_job(f,b);
    assert forall|i:nat,j:Duty| #[trigger] (s.enabled)(i,j)==#[trigger] (h.enabled)(i,j) by {
        assert(guard::real_step(f,b,i+9)); match j {Duty::Serve(_,q)=>{if majority(q) && q.subset_of(live_pair()) {assert(q =~= live_pair());}},_=>{}}
    }
    assert forall|i:nat,j:Duty| #[trigger] jobs::supports_at(s,h,direct,i,j) by {assert((s.enabled)(i,j)==(h.enabled)(i,j));}
    assert forall|i:nat| (#[trigger] (h.enabled)(i,missing())) && !(h.taken)(i,missing()) by {assert(!jobs::discharged(s,i,missing()));}
    assert(!jobs::scheduled(h,0,missing()));
}

}
