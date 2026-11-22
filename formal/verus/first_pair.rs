// Replay the actual C1/R3 part of each service and continue through the
// independent call. Working and remaining transcripts are from real runs.
use vstd::prelude::*;
use crate::{Branch,Replica,checkpoint::*,delivery::*,protocol::*};
use crate::first_assembly::*;
use crate::first_splice::{self as s,Tape,after,plays,supports,same_slots,same_locals};
use crate::first_schedule::{self as first,reference};
use crate::first_mailbox as mail;
use crate::independent_read::{self as read,State};
use crate::read_call::{Event,Program};
use crate::read_issue as issue;
use crate::sr1_majorities as maj;

verus! {

pub open spec fn sources<S>(m:Program<S>,l:Lanes,n:Notice,ta:Tape,tb:Tape) -> bool {
    lanes_ok(l) && separable(ta,alpha(n),l) && separable(tb,beta(n),l)
        && plays(m,reference(m,alpha(n),5),ta) && plays(m,reference(m,beta(n),5),tb)
}
pub open spec fn sites() -> ISet<Process> { ISet::new(|p|p==at(Replica::R1) || p==at(Replica::R2)) }
pub open spec fn their_slots(l:Lanes) -> ISet<nat> {
    ISet::new(|i:nat|l.get(i)==Some(Replica::R1) || l.get(i)==Some(Replica::R2))
}
pub proof fn outside_work<S>(m:Program<S>,l:Lanes,n:Notice,ta:Tape,tb:Tape,key:Option<Fork>)
    requires sources(m,l,n,ta,tb),
    ensures ({
        let z=root(m,l,key);let t=work_pair(ta,tb,n);let y=after(m,z,t);
        common_ready(m,l,n,ta,tb,key) && same_locals(z,y,sites().complement()) && same_slots(z,y,their_slots(l).complement())
            && y.calls==z.calls && y.owners==z.owners && y.first_requested==z.first_requested && y.requested==z.requested
            && y.cfg.net.unavailable.is_none() && !y.cfg.net.r3_crashed && !y.cfg.net.first_stopped && !y.cfg.net.second_started
    }),
{
    prepare_both(m,l,n,ta,tb,key);let z=root(m,l,key);let u=working(tb,beta(n));let v=working(ta,alpha(n));let t=u+v;
    assert forall|i:int| 0<=i<t.len() implies {let e=#[trigger] t[i];sites().contains(e.actor)
        && (s::slot(e.action).is_some() ==> their_slots(l).contains(s::slot(e.action).unwrap()))} by {
        if i<u.len() {assert(t[i]==u[i]);} else {assert(t[i]==v[i-u.len()]);}
    }
    s::frame(m,z,t,sites(),their_slots(l));
}
proof fn reference_root<S>(m:Program<S>,l:Lanes,b:Fork)
    ensures same_locals(reference(m,b,5),root(m,l,Some(b)),tail_actors()),
        reference(m,b,5).cfg.net.pending==root(m,l,Some(b)).cfg.net.pending,
        reference(m,b,5).reserved==root(m,l,Some(b)).reserved,
{
    let z=root(m,l,Some(b));let x=reference(m,b,5);
    assert forall|p:Process| tail_actors().contains(p) implies #[trigger] (x.cfg.private)(p)==(z.cfg.private)(p) by {
        maj::local_at(m,b,p,5);assert(maj::count(b,5)==5);
    }
    assert(x.cfg.net.pending =~= z.cfg.net.pending);
}
pub proof fn finish<S>(m:Program<S>,l:Lanes,b:Fork,ta:Tape,tb:Tape)
    requires sources(m,l,b.notice,ta,tb),
    ensures ({
        let z=prepared(m,l,Some(b),b.notice,ta,tb);let t=if b.branch==Branch::Alpha {ta} else {tb};
        let rest=remaining(t,b);let end=fork_end(m,l,b,ta,tb);
        plays(m,z,rest) && same_locals(after(m,reference(m,b,5),t),end,tail_actors())
            && same_locals(z,end,tail_actors().complement()) && same_slots(z,end,tail_slots(b,l).complement())
            && end.owners==z.owners && end.calls==z.calls && end.first_requested==z.first_requested && end.requested==z.requested
            && !end.cfg.net.first_stopped && !end.cfg.net.r3_crashed && !end.cfg.net.second_started && end.cfg.net.unavailable.is_none()
    }),
{
    let n=b.notice;let t=if b.branch==Branch::Alpha {ta} else {tb};let r=crate::origin(b.branch);
    let root_z=root(m,l,Some(b));let z=prepared(m,l,Some(b),n,ta,tb);let x=reference(m,b,5);
    let u=working(t,b);let v=remaining(t,b);let y=after(m,x,u);
    if b.branch==Branch::Alpha {assert(b==alpha(n));} else {assert(b==beta(n));}
    assert(separable(t,b,l));outside_work(m,l,n,ta,tb,Some(b));assert(prepared_site(m,l,b,ta,tb,z));
    reference_root(m,l,b);s::factor(m,x,t,at(r));s::concat(m,x,u,v);s::frame(m,x,u,site(r),names(l,r));
    assert forall|p:Process| tail_actors().contains(p) implies #[trigger] (y.cfg.private)(p)==(z.cfg.private)(p) by {
        assert(site(r).complement().contains(p) && sites().complement().contains(p));
        assert((x.cfg.private)(p)==(y.cfg.private)(p) && (root_z.cfg.private)(p)==(z.cfg.private)(p));
    }
    assert(site(r).complement().contains(at(Replica::R3)) && sites().complement().contains(at(Replica::R3)));
    assert forall|i:nat| tail_slots(b,l).contains(i) implies #[trigger] y.cfg.net.pending.get(i)==z.cfg.net.pending.get(i)
        && y.reserved.contains(i)==z.reserved.contains(i) by {
        if names(l,r).contains(i) {assert(y.cfg.net.pending.get(i)==z.cfg.net.pending.get(i));}
        else {assert(names(l,r).complement().contains(i) && their_slots(l).complement().contains(i));
            assert(x.cfg.net.pending.get(i)==y.cfg.net.pending.get(i) && root_z.cfg.net.pending.get(i)==z.cfg.net.pending.get(i));}
    }
    assert forall|j:int| 0<=j<v.len() implies read::names_sender(z,(#[trigger] v[j]).action) by {
        if let Action::Send(id,packet)=v[j].action {assert(packet.from==at(Replica::R3));}
    }
    let r3=Replica::R3;
    assert((x.cfg.net.locals)(r3)==(root_z.cfg.net.locals)(r3));
    assert((x.cfg.net.locals)(r3)==(y.cfg.net.locals)(r3));
    assert((root_z.cfg.net.locals)(r3)==(z.cfg.net.locals)(r3));
    s::replay(m,y,z,v,tail_actors(),tail_slots(b,l));s::frame(m,z,v,tail_actors(),tail_slots(b,l));
}

pub open spec fn shadow<S>(early:State<S>,target:State<S>,l:Lanes) -> bool {
    (forall|i:nat| early.cfg.net.pending.contains_key(i) && survivor_actor(early.cfg.net.pending[i].to)
        ==> #[trigger] target.cfg.net.pending.get(i)==Some(early.cfg.net.pending[i]))
    && (forall|i:nat| #[trigger] target.cfg.net.pending.contains_key(i)
        ==> early.cfg.net.pending.get(i)==Some(target.cfg.net.pending[i]) || names(l,Replica::R3).contains(i))
    && (forall|i:nat| #[trigger] target.reserved.contains(i) ==> early.reserved.contains(i) || names(l,Replica::R3).contains(i))
}
proof fn same_reservations<S>(m:Program<S>,x:State<S>,y:State<S>,t:Tape)
    requires x.reserved==y.reserved,plays(m,x,t),plays(m,y,t),
    ensures after(m,x,t).reserved==after(m,y,t).reserved,
    decreases t.len(),
{
    if t.len()>0 {same_reservations(m,read::next(m,x,t[0].action),read::next(m,y,t[0].action),t.drop_first());}
}
proof fn shadow_tail<S>(m:Program<S>,l:Lanes,early:State<S>,z:State<S>,t:Tape)
    requires plays(m,z,t),supports(t,tail_actors(),ISet::full()),third_sends(t,l),shadow(early,z,l),
    ensures shadow(early,after(m,z,t),l),
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let y=read::next(m,z,e.action);let u=t.drop_first();assert(tail_actors().contains(e.actor));
        assert forall|i:nat| early.cfg.net.pending.contains_key(i) && survivor_actor(early.cfg.net.pending[i].to)
            implies #[trigger] y.cfg.net.pending.get(i)==Some(early.cfg.net.pending[i]) by {
            assert(z.cfg.net.pending.get(i)==Some(early.cfg.net.pending[i]));
            assert(e.action!=Action::<Wire>::Deliver(i));
        }
        assert forall|i:nat| #[trigger] y.cfg.net.pending.contains_key(i)
            implies early.cfg.net.pending.get(i)==Some(y.cfg.net.pending[i]) || names(l,Replica::R3).contains(i) by {
            if !z.cfg.net.pending.contains_key(i) {assert(e.action is Send && e.action->Send_0==i);}
        }
        assert forall|i:nat| #[trigger] y.reserved.contains(i) implies early.reserved.contains(i) || names(l,Replica::R3).contains(i) by {
            if !z.reserved.contains(i) {assert(e.action is Send && e.action->Send_0==i);}
        }
        assert forall|i:int| 0<=i<u.len() implies {let f=#[trigger] u[i];tail_actors().contains(f.actor)
            && match f.action {Action::Send(id,p)=>p.from==at(Replica::R3) && names(l,Replica::R3).contains(id),_=>true}}
            by {assert(u[i]==t[i+1]);}
        shadow_tail(m,l,early,y,u);
    }
}
pub open spec fn c1_protected<S>(x:State<S>) -> bool {
    forall|i:nat| x.cfg.net.pending.contains_key(i) && x.cfg.net.pending[i].to==Process::FirstClient
        ==> #[trigger] x.reserved.contains(i)
}
pub(crate) proof fn keep_protection<S>(m:Program<S>,x:State<S>,t:Tape)
    requires plays(m,x,t),c1_protected(x),
    ensures c1_protected(after(m,x,t)),
    decreases t.len(),
{
    if t.len()>0 {
        let y=read::next(m,x,t[0].action);
        assert forall|i:nat| y.cfg.net.pending.contains_key(i) && y.cfg.net.pending[i].to==Process::FirstClient
            implies #[trigger] y.reserved.contains(i) by {
            if x.cfg.net.pending.get(i)==Some(y.cfg.net.pending[i]) {assert(x.reserved.contains(i));}
        }
        keep_protection(m,y,t.drop_first());
    }
}
pub open spec fn queries() -> Seq<Event> {seq![Action::StartSecondClient,issue::send_first(),issue::send_second()]}
pub open spec fn close(o:bool) -> Seq<Event> {
    (if o {seq![Action::StopFirstClient]} else {Seq::empty()})+seq![Action::CrashR3]+queries()
}
pub open spec fn before_issue<S>(m:Program<S>,x:State<S>,l:Lanes) -> bool {
    x.calls.first==all_replicas() && x.calls.second==live_pair() && x.first_requested==all_replicas()
        && x.requested==Set::<Replica>::empty() && x.owners==owners(l)
        && !x.cfg.net.first_stopped && !x.cfg.net.r3_crashed && !x.cfg.net.second_started && x.cfg.net.unavailable.is_none()
        && (x.cfg.private)(Process::SecondClient)==(m.initial)(Process::SecondClient)
        && !x.cfg.net.pending.contains_key(11) && !x.cfg.net.pending.contains_key(12)
        && !x.reserved.contains(11) && !x.reserved.contains(12)
}
pub(crate) proof fn close_at<S>(m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,x:State<S>,o:bool)
    requires lanes_ok(l),before_issue(m,x,l),first::startup(m),issue::can_issue(m,res),o ==> mail::posted(m)(x),
    ensures prefix(m,x,close(o),o),read::issued_to_majority(drive(m,x,close(o))),!read::returned(res)(drive(m,x,close(o))),
        ({let end=drive(m,x,close(o));let c=Process::SecondClient;
            end.cfg.net.r3_crashed && end.cfg.net.first_stopped==o && end.cfg.net.second_started && end.cfg.net.unavailable.is_none()
            && end.cfg.net.locals==x.cfg.net.locals && (end.cfg.private)(c)==(m.update)((m.update)(issue::started(m),issue::local_event(issue::send_first())),issue::local_event(issue::send_second()))
            && same_locals(x,end,sites()) && end.cfg.net.pending==x.cfg.net.pending.insert(11,crate::sr2::query_packet(Replica::R1)).insert(12,crate::sr2::query_packet(Replica::R2))
            && end.reserved==x.reserved.union(read::retired_at_failure(x)) && end.owners==x.owners && x.reserved.subset_of(end.reserved) && (forall|i:nat| names(l,Replica::R3).contains(i) ==> #[trigger] end.reserved.contains(i))}),
{
    let c=Process::SecondClient;let a=close(o);
    let stop=if o {read::next(m,x,Action::StopFirstClient)} else {x};
    let y=read::next(m,stop,Action::CrashR3);let v=read::next(m,y,Action::StartSecondClient);
    let w=read::next(m,v,issue::send_first());let end=read::next(m,w,issue::send_second());
    assert((y.cfg.private)(c)==(m.initial)(c));assert((v.cfg.private)(c)==issue::started(m));
    assert(!read::retired_at_failure(stop).contains(11) && !read::retired_at_failure(stop).contains(12));
    assert(read::prefix_step(m)(y,Action::StartSecondClient,v));
    assert(read::prefix_step(m)(v,issue::send_first(),w));assert(read::prefix_step(m)(w,issue::send_second(),end));
    assert(w.requested =~= set![Replica::R1]);assert(end.requested =~= live_pair());
    assert(end.cfg.net.locals =~= x.cfg.net.locals);
    assert forall|i:nat| names(l,Replica::R3).contains(i) implies #[trigger] end.reserved.contains(i)
        by {assert(stop.owners.get(i)==Some(at(Replica::R3)));assert(read::retired_at_failure(stop).contains(i));}
    assert(end.cfg.net.pending =~= x.cfg.net.pending.insert(11,crate::sr2::query_packet(Replica::R1)).insert(12,crate::sr2::query_packet(Replica::R2)));
    assert(read::issued_to_majority(end)) by {assert(live(end.cfg.net,at(Replica::R1)) && live(end.cfg.net,at(Replica::R2)));}
    assert(read::retired_at_failure(stop) =~= read::retired_at_failure(x));assert(end.reserved =~= x.reserved.union(read::retired_at_failure(x)));
    reveal_with_fuel(drive,6);reveal_with_fuel(prefix,6);
}
pub open spec fn original_actions(b:Fork,ta:Tape,tb:Tape) -> Seq<Event> {
    let t=if b.branch==Branch::Alpha {ta} else {tb};
    boot(Some(b))+actions(work_pair(ta,tb,b.notice))+actions(remaining(t,b))
}
pub open spec fn early_actions(n:Notice,ta:Tape,tb:Tape) -> Seq<Event> {
    boot(None)+actions(work_pair(ta,tb,n))+close(false)
}
pub open spec fn auxiliary<S>(m:Program<S>,l:Lanes,n:Notice,ta:Tape,tb:Tape) -> State<S> {
    drive(m,prepared(m,l,None,n,ta,tb),close(false))
}
// Derive the queue/memory simulation needed by the existing C2 replay.
// The target can hold extra branch-specific packets, including ones for
// live recipients. Their original sender has failed and retains its names.
pub proof fn cover_after_service<S>(m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,ta:Tape,tb:Tape)
    requires sources(m,l,b.notice,ta,tb),crate::first_dispatch::initiates(m),crate::first_dispatch::weak_open(m,b),
        first::startup(m),issue::can_issue(m,res),
        mail::posted(m)(after(m,reference(m,b,5),if b.branch==Branch::Alpha {ta} else {tb})),
    ensures ({
        let n=b.notice;let x=entry(m,l);let e=auxiliary(m,l,n,ta,tb);let call=original_actions(b,ta,tb);
        let z=fork_end(m,l,b,ta,tb);let target=drive(m,z,close(true));
        prefix(m,x,call,true) && drive(m,x,call)==z && mail::posted(m)(z) && prefix(m,z,close(true),true)
            && prefix(m,x,early_actions(n,ta,tb),false) && drive(m,x,early_actions(n,ta,tb))==e
            && target.reserved.subset_of(e.reserved) && target.owners==e.owners && z.cfg.net.pending.submap_of(target.cfg.net.pending)
            && before_issue(m,prepared(m,l,None,n,ta,tb),l) && read::covers(e,target.cfg) && read::issued_to_majority(e) && !read::returned(res)(e)
            && !e.cfg.net.pending.contains_key(2) && e.reserved.contains(2)
            && target.cfg.net.pending.get(2)==Some(packet_for(b,2))
            && enabled(target.cfg.net,Action::Deliver(2))
    }),
{
    let n=b.notice;let f=Some(b);let x=entry(m,l);let t=if b.branch==Branch::Alpha {ta} else {tb};
    let u=work_pair(ta,tb,n);let v=remaining(t,b);let y=prepared(m,l,f,n,ta,tb);let z=fork_end(m,l,b,ta,tb);
    let early=prepared(m,l,None,n,ta,tb);
    let raw=root(m,l,None);let branch=root(m,l,f);
    launch(m,l,f);launch(m,l,None);outside_work(m,l,n,ta,tb,f);outside_work(m,l,n,ta,tb,None);
    finish(m,l,b,ta,tb);assert(tail_actors().contains(Process::FirstClient));assert(mail::posted(m)(z));
    native_prefix(m,branch,u,true);native_prefix(m,y,v,true);native_prefix(m,raw,u,false);
    prefix_concat(m,x,boot(f),actions(u),true);prefix_concat(m,x,boot(f)+actions(u),actions(v),true);
    prefix_concat(m,x,boot(None),actions(u),false);
    assert forall|p:Process| sites().contains(p) implies #[trigger] (early.cfg.private)(p)==(z.cfg.private)(p) by {
        let g=if p==at(Replica::R1) {beta(n)} else {alpha(n)};let r=crate::origin(g.branch);
        let past=after(m,reference(m,g,5),working(if g.branch==Branch::Alpha {ta} else {tb},g));
        assert(prepared_site(m,l,g,ta,tb,early) && prepared_site(m,l,g,ta,tb,y));assert(site(r).contains(p));
        assert((past.cfg.private)(p)==(early.cfg.private)(p) && (past.cfg.private)(p)==(y.cfg.private)(p));
        assert(tail_actors().complement().contains(p));
    }
    assert forall|r:Replica| sites().contains(at(r)) implies #[trigger] (early.cfg.net.locals)(r)==(z.cfg.net.locals)(r) by {
        let g=if r==Replica::R1 {beta(n)} else {alpha(n)};assert(crate::origin(g.branch)==r);
        assert(prepared_site(m,l,g,ta,tb,early) && prepared_site(m,l,g,ta,tb,y));assert(site(r).contains(at(r)));
        let past=after(m,reference(m,g,5),working(if g.branch==Branch::Alpha {ta} else {tb},g));
        assert((past.cfg.net.locals)(r)==(early.cfg.net.locals)(r) && (past.cfg.net.locals)(r)==(y.cfg.net.locals)(r));
        assert(tail_actors().complement().contains(at(r)));assert((y.cfg.net.locals)(r)==(z.cfg.net.locals)(r));
    }
    assert forall|i:nat| !names(l,Replica::R3).contains(i) && i!=0 && i!=1
        implies #[trigger] early.cfg.net.pending.get(i)==y.cfg.net.pending.get(i) by {
        if their_slots(l).contains(i) {
            let g=if l.get(i)==Some(Replica::R1) {beta(n)} else {alpha(n)};assert(names(l,crate::origin(g.branch)).contains(i));
            let past=after(m,reference(m,g,5),working(if g.branch==Branch::Alpha {ta} else {tb},g));
            assert(prepared_site(m,l,g,ta,tb,early) && prepared_site(m,l,g,ta,tb,y));
            assert(past.cfg.net.pending.get(i)==early.cfg.net.pending.get(i) && past.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));
        } else {assert(their_slots(l).complement().contains(i));assert(raw.cfg.net.pending.get(i)==branch.cfg.net.pending.get(i));}
    }
    assert forall|i:nat| early.cfg.net.pending.contains_key(i) && survivor_actor(early.cfg.net.pending[i].to)
        implies #[trigger] y.cfg.net.pending.get(i)==Some(early.cfg.net.pending[i]) by {
        if names(l,Replica::R3).contains(i) || i==0 || i==1 {
            assert(their_slots(l).complement().contains(i));assert(raw.cfg.net.pending.get(i)==early.cfg.net.pending.get(i));
            assert(i==0 || i==1);
        }
    }
    assert forall|i:nat| #[trigger] y.cfg.net.pending.contains_key(i)
        implies early.cfg.net.pending.get(i)==Some(y.cfg.net.pending[i]) || names(l,Replica::R3).contains(i) by {
        if i==0 || i==1 {assert(their_slots(l).complement().contains(i));assert(raw.cfg.net.pending.get(i)==early.cfg.net.pending.get(i));
            assert(branch.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));}
        else if !names(l,Replica::R3).contains(i) {assert(early.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));}
    }
    same_reservations(m,raw,branch,u);
    assert(separable(t,b,l));shadow_tail(m,l,early,y,v);keep_protection(m,raw,u);
    assert forall|i:int| 0<=i<5 implies (#[trigger] checkpoint_observations(b)[i]).actor!=Process::SecondClient by {prefix_index(i);}
    memory_during_quiescence(m,checkpoint_observations(b),Process::SecondClient,0,5);
    assert forall|i:int| 0<=i<3 implies (#[trigger] crate::early_crash::events()[i]).actor!=Process::SecondClient by {prefix_index(i);}
    memory_during_quiescence(m,crate::early_crash::events(),Process::SecondClient,0,3);
    assert(sites().complement().contains(Process::SecondClient) && tail_actors().complement().contains(Process::SecondClient));
    assert(their_slots(l).complement().contains(2) && tail_slots(b,l).complement().contains(2));
    assert(their_slots(l).complement().contains(11) && tail_slots(b,l).complement().contains(11));
    assert(their_slots(l).complement().contains(12) && tail_slots(b,l).complement().contains(12));
    assert((early.cfg.private)(Process::SecondClient)==(raw.cfg.private)(Process::SecondClient));
    assert((z.cfg.private)(Process::SecondClient)==(y.cfg.private)(Process::SecondClient));
    assert((y.cfg.private)(Process::SecondClient)==(branch.cfg.private)(Process::SecondClient));
    assert forall|i:nat| #![trigger early.cfg.net.pending.contains_key(i)] #![trigger early.reserved.contains(i)] #![trigger z.reserved.contains(i)] #![trigger z.cfg.net.pending.contains_key(i)] i==11 || i==12 implies !early.reserved.contains(i) && !z.reserved.contains(i)
        && !early.cfg.net.pending.contains_key(i) && !z.cfg.net.pending.contains_key(i) by {
        assert(raw.cfg.net.pending.get(i)==early.cfg.net.pending.get(i) && raw.reserved.contains(i)==early.reserved.contains(i));
        assert(branch.cfg.net.pending.get(i)==y.cfg.net.pending.get(i) && branch.reserved.contains(i)==y.reserved.contains(i));
        assert(y.cfg.net.pending.get(i)==z.cfg.net.pending.get(i) && y.reserved.contains(i)==z.reserved.contains(i));
    }
    assert(early.calls.first==all_replicas() && early.calls.second==live_pair());
    assert(early.first_requested==all_replicas() && early.requested==Set::<Replica>::empty());
    assert(early.owners==owners(l) && !early.cfg.net.first_stopped && !early.cfg.net.r3_crashed && !early.cfg.net.second_started && early.cfg.net.unavailable.is_none());
    assert((early.cfg.private)(Process::SecondClient)==(m.initial)(Process::SecondClient));
    assert(!early.cfg.net.pending.contains_key(11) && !early.cfg.net.pending.contains_key(12));
    assert(!early.reserved.contains(11) && !early.reserved.contains(12));
    assert(before_issue(m,early,l));assert(before_issue(m,z,l));
    close_at(m,res,l,early,false);close_at(m,res,l,z,true);
    prefix_concat(m,x,boot(None)+actions(u),close(false),false);
    let e=auxiliary(m,l,n,ta,tb);let target=drive(m,z,close(true));
    assert forall|p:Process| survivor_actor(p) implies #[trigger] (e.cfg.private)(p)==(target.cfg.private)(p) by {
        if p!=Process::SecondClient {assert(sites().contains(p));assert((early.cfg.private)(p)==(z.cfg.private)(p));}
    }
    assert forall|i:nat| target.cfg.net.pending.contains_key(i) implies e.cfg.net.pending.contains_key(i) || #[trigger] e.reserved.contains(i) by {
        if i!=11 && i!=12 {assert(z.cfg.net.pending.contains_key(i));if names(l,Replica::R3).contains(i) {assert(e.reserved.contains(i));}}
    }
    assert forall|i:nat| e.cfg.net.pending.contains_key(i) && survivor_actor(e.cfg.net.pending[i].to)
        implies #[trigger] target.cfg.net.pending.get(i)==Some(e.cfg.net.pending[i]) by {
        if i!=11 && i!=12 {assert(z.cfg.net.pending.get(i)==Some(early.cfg.net.pending[i]));}
    }
    assert forall|i:nat| e.cfg.net.pending.contains_key(i) && e.cfg.net.pending[i].to==Process::FirstClient implies #[trigger] e.reserved.contains(i)
        by {assert(early.reserved.contains(i));}
    assert(survivor(e.cfg.net)==survivor(target.cfg.net)) by {
        assert(sites().contains(at(Replica::R1)) && sites().contains(at(Replica::R2)));
        assert((early.cfg.net.locals)(Replica::R1)==(z.cfg.net.locals)(Replica::R1));
        assert((early.cfg.net.locals)(Replica::R2)==(z.cfg.net.locals)(Replica::R2));
    }
    assert forall|i:nat| #[trigger] target.reserved.contains(i) implies e.reserved.contains(i) by {
        if names(l,Replica::R3).contains(i) {assert(e.reserved.contains(i));}
        else if z.reserved.contains(i) {assert(early.reserved.contains(i));}
        else {
            assert(read::retired_at_failure(z).contains(i));assert(z.cfg.net.pending.contains_key(i) && z.cfg.net.pending[i].to==at(Replica::R3));
            assert(early.cfg.net.pending.get(i)==Some(z.cfg.net.pending[i]));assert(read::retired_at_failure(early).contains(i));
        }
    }
    assert(read::covers(e,target.cfg));
    assert(early.cfg.net.pending.get(2)==raw.cfg.net.pending.get(2));
    assert(z.cfg.net.pending.get(2)==y.cfg.net.pending.get(2) && y.cfg.net.pending.get(2)==branch.cfg.net.pending.get(2));
    assert(names(l,Replica::R3).contains(2));assert(e.reserved.contains(2));
}

}
