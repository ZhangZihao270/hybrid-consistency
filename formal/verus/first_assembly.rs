// Assemble the two majority executions from the histories of the processes
// that actually served them. The auxiliary caller never observes C1.
use vstd::prelude::*;
use crate::{Branch,Replica,checkpoint::*,delivery::*,protocol::*};
use crate::early_crash as probe;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::{self as first,reference};
use crate::first_splice::{self as splice,Observation,Tape,after,plays,pick,supports,same_slots,same_locals};
use crate::independent_read::{self as read,State};
use crate::ordinary_service::Configuration;
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program};
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::sr1_majorities as maj;

verus! {

pub type Lanes = Map<nat,Replica>;
pub type Service<S> = wait::Path<State<S>,Event>;
pub open spec fn lanes_ok(l:Lanes) -> bool {
    l.get(3)==Some(Replica::R1) && l.get(4)==Some(Replica::R2) && l.get(2)==Some(Replica::R3)
        && !l.contains_key(0) && !l.contains_key(1) && !l.contains_key(5)
        && !l.contains_key(11) && !l.contains_key(12)
}
pub open spec fn names(l:Lanes,r:Replica) -> ISet<nat> { ISet::new(|i:nat| l.get(i)==Some(r)) }
pub open spec fn site(r:Replica) -> ISet<Process> { ISet::new(|p|p==at(r)) }
pub open spec fn tail_actors() -> ISet<Process> { ISet::new(|p|p==at(Replica::R3) || p==Process::FirstClient) }
pub open spec fn tail_slots(b:Fork,l:Lanes) -> ISet<nat> {
    ISet::new(|i:nat|i>2 && i!=11 && i!=12 && l.get(i)!=Some(maj::missing(b)))
}
pub open spec fn owners(l:Lanes) -> Map<nat,Process> {
    Map::new(l.dom().filter(|i:nat| l[i]==Replica::R3),|_i:nat|at(Replica::R3))
}
pub open spec fn entry<S>(m:Program<S>,l:Lanes) -> State<S> { State{owners:owners(l),..probe::entry(m)} }
pub open spec fn root<S>(m:Program<S>,l:Lanes,b:Option<Fork>) -> State<S> {
    let x=probe::cut(m,3);
    match b {None=>State{owners:owners(l),..x},Some(f)=>State{cfg:first::cfg(m,f,5),owners:owners(l),..x}}
}
pub open spec fn working(t:Tape,b:Fork) -> Tape {pick(t,at(crate::origin(b.branch)),true)}
pub open spec fn remaining(t:Tape,b:Fork) -> Tape {pick(t,at(crate::origin(b.branch)),false)}
pub open spec fn third_sends(t:Tape,l:Lanes) -> bool {
    forall|i:int| 0<=i<t.len() ==> match (#[trigger] t[i]).action {
        Action::Send(id,p)=>p.from==at(Replica::R3) && names(l,Replica::R3).contains(id), _=>true,
    }
}
// A causal and naming condition on source events, independent of all
// return values and of the target states. Multiple ordinary messages can
// be indispensable to the call. A survivor may send to R3 or to itself.
pub open spec fn separable(t:Tape,b:Fork,l:Lanes) -> bool {
    let r=crate::origin(b.branch);let work=working(t,b);let rest=remaining(t,b);
    splice::movable(t,at(r)) && supports(work,site(r),names(l,r))
        && supports(rest,tail_actors(),tail_slots(b,l)) && third_sends(rest,l)
}
pub open spec fn work_pair(ta:Tape,tb:Tape,n:Notice) -> Tape {
    working(tb,beta(n))+working(ta,alpha(n))
}
pub open spec fn prepared<S>(m:Program<S>,l:Lanes,key:Option<Fork>,n:Notice,ta:Tape,tb:Tape) -> State<S> {
    after(m,root(m,l,key),work_pair(ta,tb,n))
}
pub open spec fn fork_end<S>(m:Program<S>,l:Lanes,b:Fork,ta:Tape,tb:Tape) -> State<S> {
    after(m,prepared(m,l,Some(b),b.notice,ta,tb),remaining(if b.branch==Branch::Alpha {ta} else {tb},b))
}

// The physical prefix monitor is shared with the service-loss proof.
// Stopping a caller after its recorded return is an environment action.
pub open spec fn drive<S>(m:Program<S>,x:State<S>,a:Seq<Event>) -> State<S>
    decreases a.len(),
{
    if a.len()==0 {x} else {drive(m,read::next(m,x,a[0]),a.drop_first())}
}
pub open spec fn prefix<S>(m:Program<S>,x:State<S>,a:Seq<Event>,original:bool) -> bool
    decreases a.len(),
{
    if a.len()==0 {true} else {
        let e=a[0];let y=read::next(m,x,e);
        (if original && e==Action::StopFirstClient {enabled(x.cfg.net,e) && mail::posted(m)(x)}
            else {read::prefix_step(m)(x,e,y)}) && prefix(m,y,a.drop_first(),original)
    }
}
pub open spec fn actions(t:Tape) -> Seq<Event> { t.map_values(|e:Observation|e.action) }
pub proof fn prefix_concat<S>(m:Program<S>,x:State<S>,a:Seq<Event>,b:Seq<Event>,o:bool)
    ensures prefix(m,x,a+b,o)==(prefix(m,x,a,o) && prefix(m,drive(m,x,a),b,o)),
        drive(m,x,a+b)==drive(m,drive(m,x,a),b),
    decreases a.len(),
{
    if a.len()==0 {assert(a+b =~= b);} else {
        assert((a+b).drop_first() =~= a.drop_first()+b);prefix_concat(m,read::next(m,x,a[0]),a.drop_first(),b,o);
    }
}
pub proof fn native_prefix<S>(m:Program<S>,x:State<S>,t:Tape,o:bool)
    requires plays(m,x,t),
    ensures prefix(m,x,actions(t),o),drive(m,x,actions(t))==after(m,x,t),
    decreases t.len(),
{
    if t.len()>0 {
        assert(actions(t).drop_first() =~= actions(t.drop_first()));
        native_prefix(m,read::next(m,x,t[0].action),t.drop_first(),o);
    }
}
pub open spec fn boot(b:Option<Fork>) -> Seq<Event> {
    match b {Some(f)=>actions_to_crash(f).take(5),None=>probe::actions().take(3)}
}
proof fn launch_at<S>(m:Program<S>,l:Lanes,b:Option<Fork>,k:nat,guards:bool)
    requires lanes_ok(l),guards ==> dispatch::initiates(m),guards && b.is_some() ==> dispatch::weak_open(m,b.unwrap()),k<=boot(b).len(),
    ensures ({
        let x=entry(m,l);let a=boot(b).take(k as int);
        let at_k=match b {Some(f)=>State{cfg:first::cfg(m,f,k),owners:owners(l),..reference(m,f,k)},
            None=>State{owners:owners(l),..probe::cut(m,k)}};
        (guards ==> prefix(m,x,a,b.is_some())) && drive(m,x,a)==at_k
    }),
    decreases k,
{
    let a=boot(b);let x=entry(m,l);
    if k==0 {
        if let Some(f)=b {assert(first::cfg(m,f,0).private =~= m.initial);assert(state_after(f,0).locals =~= after_local_rmws().locals);assert(state_after(f,0).pending =~= after_local_rmws().pending);}
        else {assert(probe::cut(m,0).cfg.net.pending =~= after_local_rmws().pending);assert(probe::cut(m,0).cfg.private =~= m.initial);}
        assert(a.take(0) =~= Seq::<Event>::empty());
    } else {
        let j=(k-1) as nat;launch_at(m,l,b,j,guards);let before=drive(m,x,a.take(j as int));let e=a[j as int];
        prefix_index(j as int);
        match b {
            Some(f)=>{
                if guards { dispatch::fanout_and_weak_open_launch(m,f); }
                maj::majority_transport(f);maj::local_at(m,f,process_step(before.cfg.net,e).actor,j);
                assert(maj::count(f,j)==j);assert(maj::obs(f)[j as int]==checkpoint_observations(f)[j as int]);
                let obs=maj::obs(f)[j as int];if guards { assert((m.accept)(memory(m,obs.actor,maj::obs(f),j),obs)); }
                let end=first::cfg(m,f,k);let y=read::next(m,before,e);
                assert(process_step(before.cfg.net,e)==obs);assert(y.cfg.net.pending =~= end.net.pending);
                assert(y.cfg.net.locals =~= end.net.locals);assert(y.cfg.private =~= end.private);
                assert(y.first_requested =~= reference(m,f,k).first_requested);assert(y==State{cfg:end,owners:owners(l),..reference(m,f,k)});
            },
            None=>{
                let ev=probe::events()[j as int];
                assert(ev==dispatch::initial_sends()[j as int] && ev==process_step(before.cfg.net,e));
                assert forall|i:int| 0<=i<j implies #[trigger] probe::events()[i]==dispatch::initial_sends()[i] by {assert(i==0 || i==1);}
                memory_on_common_prefix(m,Process::FirstClient,probe::events(),dispatch::initial_sends(),j);
                if guards { assert((m.accept)(memory(m,Process::FirstClient,dispatch::initial_sends(),j),ev)); }
                let y=read::next(m,before,e);let end=probe::cut(m,k);
                assert(y.cfg.net.pending =~= end.cfg.net.pending);assert(y.cfg.net.locals =~= end.cfg.net.locals);
                assert(y.cfg.private =~= end.cfg.private);assert(y.first_requested =~= end.first_requested);assert(y==State{owners:owners(l),..end});
            }
        }
        if guards { assert(prefix(m,before,seq![e],b.is_some())) by {reveal_with_fuel(prefix,2);} }
        assert(drive(m,before,seq![e])==read::next(m,before,e)) by {reveal_with_fuel(drive,2);}
        assert(a.take(k as int) =~= a.take(j as int)+seq![e]);prefix_concat(m,x,a.take(j as int),seq![e],b.is_some());
    }
}
pub proof fn launch<S>(m:Program<S>,l:Lanes,b:Option<Fork>)
    requires lanes_ok(l),dispatch::initiates(m),b.is_some() ==> dispatch::weak_open(m,b.unwrap()),
    ensures prefix(m,entry(m,l),boot(b),b.is_some()),drive(m,entry(m,l),boot(b))==root(m,l,b),
{
    launch_at(m,l,b,boot(b).len(),true);assert(boot(b).take(boot(b).len() as int) =~= boot(b));
}

// Compute the endpoint when a separate real trace already supplies the guards.
pub(crate) proof fn boot_state<S>(m:Program<S>,l:Lanes,b:Fork)
    requires lanes_ok(l),
    ensures drive(m,entry(m,l),boot(Some(b)))==root(m,l,Some(b)),
{
    let a=boot(Some(b));launch_at(m,l,Some(b),a.len(),false);
    assert(a.take(a.len() as int) =~= a);
}

proof fn initial_component<S>(m:Program<S>,l:Lanes,b:Fork,key:Option<Fork>)
    requires lanes_ok(l),
    ensures ({
        let x=reference(m,b,5);let z=root(m,l,key);let r=crate::origin(b.branch);
        same_locals(x,z,site(r)) && same_slots(x,z,names(l,r))
            && (forall|p:Process| site(r).contains(p) ==> #[trigger] live(z.cfg.net,p))
    }),
{
    let r=crate::origin(b.branch);let p=at(r);let x=reference(m,b,5);let z=root(m,l,key);
    assert forall|i:int| 0<=i<5 implies (#[trigger] maj::obs(b)[i]).actor!=p by {prefix_index(i);}
    memory_during_quiescence(m,maj::obs(b),p,0,5);
    match key {
        Some(f)=>{
            assert forall|i:int| 0<=i<5 implies (#[trigger] checkpoint_observations(f)[i]).actor!=p by {prefix_index(i);}
            memory_during_quiescence(m,checkpoint_observations(f),p,0,5);
        }
        None=>{
            assert forall|i:int| 0<=i<3 implies (#[trigger] probe::events()[i]).actor!=p by {prefix_index(i);}
            memory_during_quiescence(m,probe::events(),p,0,3);
        }
    }
    assert forall|i:nat| names(l,r).contains(i) implies #[trigger] x.cfg.net.pending.get(i)==z.cfg.net.pending.get(i)
        && x.reserved.contains(i)==z.reserved.contains(i) by {assert(i!=0 && i!=1 && i!=2);}
}
pub open spec fn prepared_site<S>(m:Program<S>,l:Lanes,b:Fork,ta:Tape,tb:Tape,end:State<S>) -> bool {
    let r=crate::origin(b.branch);
    let x=after(m,reference(m,b,5),working(if b.branch==Branch::Alpha {ta} else {tb},b));
    same_locals(x,end,site(r)) && same_slots(x,end,names(l,r))
}
pub open spec fn common_ready<S>(m:Program<S>,l:Lanes,n:Notice,ta:Tape,tb:Tape,key:Option<Fork>) -> bool {
    let z=root(m,l,key);let end=prepared(m,l,key,n,ta,tb);
    plays(m,z,work_pair(ta,tb,n)) &&
    forall|b:Fork| b.notice==n ==> #[trigger] prepared_site(m,l,b,ta,tb,end)
}
proof fn do_work<S>(m:Program<S>,l:Lanes,b:Fork,source:Tape,z:State<S>)
    requires lanes_ok(l),separable(source,b,l),plays(m,reference(m,b,5),source),
        z.owners==owners(l),z.cfg.net.unavailable.is_none(),!z.cfg.net.r3_crashed,
        same_locals(reference(m,b,5),z,site(crate::origin(b.branch))),
        same_slots(reference(m,b,5),z,names(l,crate::origin(b.branch))),
    ensures ({
        let t=working(source,b);let r=crate::origin(b.branch);let y=after(m,z,t);
        plays(m,z,t) && same_locals(after(m,reference(m,b,5),t),y,site(r)) && same_slots(after(m,reference(m,b,5),t),y,names(l,r))
            && same_locals(z,y,site(r).complement()) && same_slots(z,y,names(l,r).complement())
            && y.owners==z.owners && y.cfg.net.unavailable.is_none() && !y.cfg.net.r3_crashed
    }),
{
    let x=reference(m,b,5);let r=crate::origin(b.branch);let p=at(r);let t=working(source,b);
    splice::factor(m,x,source,p);splice::concat(m,x,t,remaining(source,b));
    assert forall|i:int| 0<=i<t.len() implies read::names_sender(z,(#[trigger] t[i]).action) by {
        if let Action::Send(id,_)=t[i].action {assert(names(l,r).contains(id));assert(!z.owners.contains_key(id));}
    }
    splice::replay(m,x,z,t,site(r),names(l,r));splice::frame(m,z,t,site(r),names(l,r));
}
pub proof fn prepare_both<S>(m:Program<S>,l:Lanes,n:Notice,ta:Tape,tb:Tape,key:Option<Fork>)
    requires lanes_ok(l),separable(ta,alpha(n),l),separable(tb,beta(n),l),
        plays(m,reference(m,alpha(n),5),ta),plays(m,reference(m,beta(n),5),tb),
    ensures common_ready(m,l,n,ta,tb,key),
{
    let a=alpha(n);let b=beta(n);let z=root(m,l,key);
    let u=working(tb,b);let v=working(ta,a);let y=after(m,z,u);
    initial_component(m,l,b,key);initial_component(m,l,a,key);do_work(m,l,b,tb,z);
    let r=Replica::R2;let x=reference(m,a,5);
    assert(site(Replica::R1).complement().contains(at(r)));
    assert forall|i:nat| names(l,r).contains(i) implies #[trigger] x.cfg.net.pending.get(i)==y.cfg.net.pending.get(i)
        && x.reserved.contains(i)==y.reserved.contains(i) by {
        assert(names(l,Replica::R1).complement().contains(i));assert(z.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));
        assert(x.cfg.net.pending.get(i)==z.cfg.net.pending.get(i));
    }
    do_work(m,l,a,ta,y);splice::concat(m,z,u,v);let end=after(m,z,u+v);
    assert forall|f:Fork| f.notice==n implies #[trigger] prepared_site(m,l,f,ta,tb,end) by {
        if f.branch==Branch::Alpha {assert(f==a);} else {
            assert(f==b);assert(site(r).complement().contains(at(Replica::R1)));
            let local=after(m,reference(m,b,5),u);
            assert forall|i:nat| names(l,Replica::R1).contains(i) implies #[trigger] local.cfg.net.pending.get(i)==end.cfg.net.pending.get(i)
                && local.reserved.contains(i)==end.reserved.contains(i) by {
                assert(names(l,r).complement().contains(i));assert(y.cfg.net.pending.get(i)==end.cfg.net.pending.get(i));
                assert(local.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));
            }
        }
    }
}

}
