// Lift each selected SR1 majority service to its own all-live original.
// Neither the other reference's schedule nor a reply from the idle member
// is involved. The caller is silent after its initial fanout.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::coupled_sources as sources;
use crate::coupled_traffic as traffic;
use crate::first_assembly::{self as asm, Lanes, Service};
use crate::first_causality as cause;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_schedule::{self as first, reference};
use crate::first_splice::{self as tape, Observation, Tape};
use crate::hybrid_fork as fork;
use crate::hybrid_majority as majority;
use crate::hybrid_transparency as trans;
use crate::independent_read::{self as read, State};
use crate::promotion_wait as wait;
use crate::read_call::{Event, Program};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::sr1_contract as rpc;
use crate::fair_read as fair;

verus! {

pub open spec fn offers() -> Seq<Event> {
    seq![send(0,Path::Weak,at(Replica::R1),at(Replica::R3),Wire::Copy(2)),
         send(1,Path::Weak,at(Replica::R2),at(Replica::R3),Wire::Copy(5))]
}
pub open spec fn before_offers<S>(m:Program<S>,l:Lanes) -> State<S> {
    let x=asm::entry(m,l);State{cfg:crate::ordinary_service::Configuration{net:local_rmw_cells(),..x.cfg},..x}
}
pub open spec fn after_offers<S>(m:Program<S>,l:Lanes) -> Program<S> {
    crate::protocol::LocalProtocol{initial:asm::drive(m,before_offers(m,l),offers()).cfg.private,..m}
}
// The prefix proof often starts at the two queued weak offers. Carry the
// actual issuing replicas' private updates across that boundary. Neither
// issuing callback has to be a no-op on strong-private memory.
pub proof fn shared_weak_entry<S>(m:Program<S>,l:Lanes,b:Fork)
    requires asm::lanes_ok(l), ({
        let x=before_offers(m,l);let a=offers();let y=read::next(m,x,a[0]);
        crate::ordinary_service::allowed(m,x.cfg,a[0]) && crate::ordinary_service::allowed(m,y.cfg,a[1])
    }),
    ensures ({
        let x=before_offers(m,l);let t=offers();let u=after_offers(m,l);let end=crate::guarded_history::weak_end();
        asm::prefix(m,x,t,true) && asm::drive(m,x,t)==asm::entry(u,l) && u.update==m.update && u.accept==m.accept && u.done==m.done
            && end.answers.get(crate::weak_round::request(crate::Op::W1).id)==Some(1)
            && end.answers.get(crate::weak_round::request(crate::Op::W2).id)==Some(1)
            && end.front==crate::facade_hybrid::prefix(b,0) && crate::weak_round::origin_only(end)
    }),
{
    crate::weak_round::actual_overlap(b);crate::facade_hybrid::weak_calls_and_issued_offers(crate::weak_round::paper_ops(),b);
    origin_updates_are_actually_offered();
    reveal_with_fuel(asm::drive,3);reveal_with_fuel(asm::prefix,3);
}

pub proof fn rebase_preserves_steps<S>(m:Program<S>,l:Lanes,x:State<S>,s:Seq<Event>)
    ensures asm::prefix(after_offers(m,l),x,s,true)==asm::prefix(m,x,s,true),
        asm::drive(after_offers(m,l),x,s)==asm::drive(m,x,s),
    decreases s.len(),
{
    if s.len()>0 {rebase_preserves_steps(m,l,read::next(m,x,s[0]),s.drop_first());}
}

// A raw weak-confirmation input at the replica is also outside a
// preparation with the other weak evidence postponed.
pub open spec fn ordinary_input(e:Observation) -> bool {
    traffic::preparation_input(e) && match e.action {Action::Local(_,Wire::WeakConfirm(_))=>false,_=>true}
}

pub proof fn ordinary_cells<S>(m:Program<S>,x:State<S>,t:Tape)
    requires tape::plays(m,x,t),traffic::fitted(t,|_e:Observation|true),
    ensures tape::after(m,x,t).cfg.net.locals==x.cfg.net.locals,
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let y=read::next(m,x,e.action);assert(traffic::preparation_input(e));
        assert(y.cfg.net.locals =~= x.cfg.net.locals) by {
            assert forall|r:Replica| (#[trigger] local_input(x.cfg.net,e.action,r)).is_none()
                || !(local_input(x.cfg.net,e.action,r).unwrap() is Copy) by {};
        }
        let u=t.drop_first();assert forall|i:int| 0<=i<u.len() implies traffic::preparation_input(#[trigger] u[i])
            by {assert(u[i]==t[i+1]);assert(traffic::preparation_input(t[i+1]));}
        ordinary_cells(m,y,u);
    }
}

// A check on a source trace. The existing preparation language includes
// all ordinary peer traffic, CPU steps and non-copy local inputs.
pub open spec fn ordinary_source<S>(p: Service<S>) -> bool {
    let t = tape::record(p,0);
    forall|i: int| 0 <= i < t.len() ==> {
        let e = #[trigger] t[i]; e.actor == Process::FirstClient || ordinary_input(e)
    }
}

pub(crate) proof fn source_cells<S>(m: Program<S>, b: Fork, p: Service<S>)
    requires cause::returning(m,b,p), ordinary_source(p),
    ensures crate::first_service_loss::stable(b,p), traffic::fitted(sources::replicas(p),|_e: Observation| true),
        forall|i:int| 0<=i<sources::replicas(p).len() ==> ordinary_input(#[trigger] sources::replicas(p)[i]),
{
    let t = tape::record(p,0); let rs = sources::replicas(p);
    assert forall|i:int| 0 <= i < rs.len() implies ordinary_input(#[trigger] rs[i]) by {
        tape::picked(t,Process::FirstClient,false,i);
        let j = choose|j:int| 0 <= j < t.len() && t[j] == rs[i];
        assert(t[j].actor == Process::FirstClient || ordinary_input(t[j]));
    }
    assert forall|i:int| 0 <= i < p.actions.len() implies !cause::changes_sample(b,#[trigger] p.states[i],p.states[i+1]) by {
        let x = p.states[i]; let a = p.actions[i]; let e = t[i];
        assert(mail::active_step(m)(x,a,p.states[i+1]));
        assert(e.actor == Process::FirstClient || ordinary_input(e));
        assert forall|r:Replica| (#[trigger] local_input(x.cfg.net,a,r)).is_none()
            || !(local_input(x.cfg.net,a,r).unwrap() is Copy) by {};
    }
}

// Delaying C1 cannot remove any of its inputs. Each later delivery was
// physically queued before the first caller callback, even for a long tape.
pub(crate) proof fn initial_mailbox<S>(m: Program<S>, x: State<S>, c: Tape)
    requires tape::plays(m,x,c), forall|i:int| 0 <= i < c.len() ==> (#[trigger] c[i]).actor == Process::FirstClient,
    ensures calls::sent_to_caller(x,c),
    decreases c.len(),
{
    if c.len() > 0 {
        let e = c[0]; let tail = c.drop_first(); let y = read::next(m,x,e.action);
        assert(!(e.action is Send));
        assert(y.cfg.net.pending.submap_of(x.cfg.net.pending));
        assert forall|j:int| 0 <= j < tail.len() implies (#[trigger] tail[j]).actor == Process::FirstClient by {assert(tail[j]==c[j+1]);}
        initial_mailbox(m,y,tail);
        assert forall|i:int| 0 <= i < c.len() && (#[trigger] c[i]).action is Deliver
            implies x.cfg.net.pending.get(c[i].action->Deliver_0) == c[i].incoming by {
            if i > 0 {
                assert(tail[i-1] == c[i]);
                assert(y.cfg.net.pending.get(c[i].action->Deliver_0) == c[i].incoming);
                // A tape that plays can never record a missing envelope.
                let z = tape::after(m,y,tail.take(i-1));
                tape::concat(m,y,tail.take(i-1),tail.skip(i-1));
                assert(tail.take(i-1) + tail.skip(i-1) =~= tail);
                assert(tail.skip(i-1)[0] == c[i]);
                assert(tape::plays(m,z,tail.skip(i-1)));
                assert(enabled(z.cfg.net,c[i].action) && process_step(z.cfg.net,c[i].action) == c[i]);
            }
        }
    }
}

pub open spec fn cutoff<S>(m: Program<S>, l: Lanes, b: Fork, t: Tape, c: Tape) -> State<S> {
    asm::drive(m,build::first_end(m,l,b,t,c),pair::close(true))
}

// Checked independently on each arm. C1 can finish from this mailbox with
// its own actual inputs; an unused reply from the omitted member is optional.
pub open spec fn arm<S>(m: Program<S>, first: spec_fn(S)->int, res: spec_fn(S)->Option<int>,
    l: Lanes, b: Fork, t: Tape, c: Tape) -> bool {
    let entry = asm::entry(m,l); let root = build::root(m,l,b); let ready = build::prepared(m,l,b,t);
    let end = build::first_end(m,l,b,t,c); let start = build::prefix_actions(b,t,c);
    let issued = cutoff(m,l,b,t,c);
    traffic::fitted(t,|_e:Observation| true) && tape::plays(m,root,t) && tape::plays(m,ready,c)
        && (forall|i:int| 0<=i<t.len() ==> ordinary_input(#[trigger] t[i]))
        && issued.cfg.net.locals==state_after(b,5).locals
        && (forall|i:int| 0 <= i < c.len() ==> (#[trigger] c[i]).actor == Process::FirstClient
            && !(c[i].action is Send) && (c[i].incoming.is_some() ==> {
                let sender = c[i].incoming.unwrap().from; sender == at(crate::origin(b.branch)) || sender == at(Replica::R3)
            }))
        && cause::pending_inputs(m,(ready.cfg.private)(Process::FirstClient),c) && mail::posted(m)(end)
        && first((end.cfg.private)(Process::FirstClient)) == first_value(b)
        && build::heard(c,crate::origin(b.branch)) && build::heard(c,Replica::R3)
        && calls::client_change(ready,end,c) && pair::c1_protected(ready) && tape::same_locals(ready,issued,pair::sites())
        && issued.owners==end.owners && issued.reserved==end.reserved.union(read::retired_at_failure(end))
        && issued.cfg.net.pending==end.cfg.net.pending.insert(11,crate::sr2::query_packet(Replica::R1)).insert(12,crate::sr2::query_packet(Replica::R2))
        && pair::before_issue(m,end,l) && traffic::weak_queue(end,b)
        && asm::prefix(m,entry,start,true) && asm::drive(m,entry,start) == end
        && asm::prefix(m,entry,start + pair::close(true),true)
        && asm::drive(m,entry,start + pair::close(true)) == issued
        && crate::survivors::after_crash(issued.cfg.net) && read::issued_to_majority(issued)
        && !read::returned(res)(issued) && traffic::weak_queue(issued,b)
        && (issued.cfg.private)(Process::SecondClient) ==
            (m.update)((m.update)(issue::started(m),issue::local_event(issue::send_first())),issue::local_event(issue::send_second()))
}

pub proof fn lift_majority_arm<S>(m: Program<S>, first: spec_fn(S)->int, res: spec_fn(S)->Option<int>,
    l: Lanes, b: Fork, who: fork::Issuer, p: Service<S>)
    requires fork::proper(l,who), dispatch::initiates(m), dispatch::weak_open(m,b), first::startup(m), issue::can_issue(m,res),
        cause::member_sample(m,first,b), cause::returning(m,b,p), fork::wire_route(b,p,who,rpc::replies()), ordinary_source(p),
    ensures arm(m,first,res,l,b,sources::replicas(p),calls::caller(p)),
{
    let t = sources::replicas(p); let c = calls::caller(p); let x = build::root(m,l,b);
    let ref_start = reference(m,b,5); let ref_ready = tape::after(m,ref_start,t);
    let z = build::prepared(m,l,b,t); let end = build::first_end(m,l,b,t,c); let cc = Process::FirstClient;
    let start = build::prefix_actions(b,t,c); let entry = asm::entry(m,l);
    sources::lift_available_sites(m,l,b,p,who);
    traffic::move_caller_last(m,b,p,who);
    assert forall|i:int| 0 <= i < c.len() implies (#[trigger] c[i]).actor == cc by {tape::picked(tape::record(p,0),cc,true,i);}
    initial_mailbox(m,ref_ready,c);
    assert forall|i:int| 0 <= i < c.len() && (#[trigger] c[i]).action is Deliver
        implies z.cfg.net.pending.get(c[i].action->Deliver_0) == c[i].incoming by {
        let id = c[i].action->Deliver_0; assert(ISet::<nat>::full().contains(id));
        assert(ref_ready.cfg.net.pending.get(id) == z.cfg.net.pending.get(id));
    }
    source_cells(m,b,p); build::prepared_frame(m,l,b,t);ordinary_cells(m,x,t);
    calls::finish_caller(m,first,b,p,who,z);
    build::exchange_heard(tape::record(p,0),crate::origin(b.branch));
    build::exchange_heard(tape::record(p,0),Replica::R3);
    assert forall|i:int| 0 <= i < c.len() implies !( (#[trigger] c[i]).action is Send) by {
        let rec = tape::record(p,0); tape::picked(rec,cc,true,i);
        let j = choose|j:int| 0 <= j < rec.len() && rec[j] == c[i];
        assert(mail::active_step(m)(p.states[j],p.actions[j],p.states[j+1]));
    }
    let ids = ISet::new(|i:nat| i>2 && i!=11 && i!=12);
    assert(tape::supports(t,ISet::full(),ids)) by {
        assert forall|i:int| 0 <= i < t.len() implies {
            let e = #[trigger] t[i]; ISet::<Process>::full().contains(e.actor)
                && (tape::slot(e.action).is_some() ==> ids.contains(tape::slot(e.action).unwrap()))
        } by { assert(traffic::preparation_input(t[i])); }
    }
    tape::frame(m,x,t,ISet::full(),ids);
    assert forall|id:nat| id<=2 implies #[trigger] end.cfg.net.pending.get(id)==state_after(b,5).pending.get(id) by {
        assert(ids.complement().contains(id)); assert(z.cfg.net.pending.get(id)==x.cfg.net.pending.get(id));
        if calls::takes(c,id) {assert(x.cfg.net.pending.contains_key(id) && x.cfg.net.pending[id].to==cc);}
    }
    assert(end.cfg.net.pending.get(11)==None && end.cfg.net.pending.get(12)==None);
    assert(pair::before_issue(m,end,l));
    asm::launch(m,l,Some(b)); asm::native_prefix(m,x,t,true); asm::native_prefix(m,z,c,true);
    asm::prefix_concat(m,entry,asm::boot(Some(b)),asm::actions(t),true);
    asm::prefix_concat(m,entry,asm::boot(Some(b))+asm::actions(t),asm::actions(c),true);
    pair::close_at(m,res,l,end,true); asm::prefix_concat(m,entry,start,pair::close(true),true);
    let issued = cutoff(m,l,b,t,c);
    assert forall|id:nat| id<=2 implies #[trigger] issued.cfg.net.pending.get(id)==state_after(b,5).pending.get(id)
        by {assert(end.cfg.net.pending.get(id)==state_after(b,5).pending.get(id));}
}
// Use A and operational no-await on the majority reference. If any
// registered ordinary service exists, use it, regardless of which service
// fair scheduling supplied. Otherwise exhibit an actual out-of-scope step.
pub proof fn available_arm_or_source_step<S>(m: Program<S>, first: spec_fn(S)->int, res: spec_fn(S)->Option<int>,
    l: Lanes, b: Fork, who: fork::Issuer, used: rpc::Ledger<S>, region: nb::Region<State<S>>,
    run: fair::Runnable, audit: trans::PacketAudit) -> (p: Service<S>)
    requires fork::proper(l,who), dispatch::initiates(m), dispatch::weak_open(m,b), first::startup(m), issue::can_issue(m,res),
        majority::read_a(m,first,res,reference(m,b,0),run), mail::fair_opportunity(m,run,reference(m,b,5)),
        trans::no_first_wait(m,b,audit), rpc::registered(m,b,region,who,used),
    ensures sources::source(m,b,who,audit,p),
        (ordinary_source(p) && arm(m,first,res,l,b,sources::replicas(p),calls::caller(p)))
        || ((forall|q: Service<S>| #[trigger] sources::source(m,b,who,audit,q) ==> !ordinary_source(q))
            && exists|i:int| 0<=i<p.actions.len() && {
                let e = #[trigger] tape::record(p,0)[i]; e.actor != Process::FirstClient && !ordinary_input(e)
            }),
{
    hide(arm);
    let fallback = sources::majority_source(m,res,b,who,audit,region,used,run);
    if exists|q:Service<S>| #[trigger] sources::source(m,b,who,audit,q) && ordinary_source(q) {
        let q = choose|q:Service<S>| #[trigger] sources::source(m,b,who,audit,q) && ordinary_source(q);
        crate::sr1_ordinary::ordinary_edges(m,b,audit,q);
        majority::first_quorum_rule(m,first,res,b);
        lift_majority_arm(m,first,res,l,b,who,q);
        q
    } else { fallback }
}
}
