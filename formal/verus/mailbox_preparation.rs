// The selected SR1 can finish privately as soon as its real input tape is
// in C1's inbox. Ordinary replica work can continue for an arbitrary time.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::first_assembly::{self as asm, Lanes};
use crate::first_causality as cause;
use crate::first_mailbox as mail;
use crate::first_pair as pair;
use crate::first_splice::{self as tape, Tape, Observation};
use crate::fork_alternatives as fork;
use crate::guarded_comparison::{self as cmp, ready, prepare, fired, end};
use crate::independent_preparations as prep;
use crate::independent_read::{self as read, State};
use crate::read_call::{Event,Program};

verus! {

pub open spec fn setup<S>(m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork) -> bool {
    asm::lanes_ok(l) && crate::first_dispatch::initiates(m) && crate::first_dispatch::weak_open(m,b)
        && crate::first_schedule::startup(m) && crate::read_issue::can_issue(m,res)
}

pub open spec fn ordinary<S>(m:Program<S>,x:State<S>,t:Tape) -> bool {
    tape::plays(m,x,t) && forall|i:int| 0<=i<t.len() ==> prep::ordinary_input(#[trigger] t[i])
}

pub open spec fn mailbox<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,c:Tape) -> bool {
    let p=Process::FirstClient;let z=tape::after(m,x,c);
    !x.cfg.net.first_stopped && tape::plays(m,x,c) && calls::client_inputs(c) && calls::sent_to_caller(x,c)
        && cause::pending_inputs(m,(x.cfg.private)(p),c) && mail::posted(m)(z) && first((z.cfg.private)(p))==first_value(b)
        && build::heard(c,crate::origin(b.branch)) && build::heard(c,Replica::R3)
        && forall|i:int| 0<=i<c.len() ==> {let e=#[trigger] c[i];!(e.action is Send)
            && (e.incoming.is_some() ==> e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3))}
}

// Replies are never duplicated in an actually playable private tape.
// Include the packet at its true slot, before C1 takes any callback.
proof fn inbox_inputs<S>(m:Program<S>,x:State<S>,c:Tape)
    requires tape::plays(m,x,c),forall|i:int| 0<=i<c.len() ==> (#[trigger] c[i]).actor==Process::FirstClient,
    ensures calls::client_inputs(c),calls::sent_to_caller(x,c),
        forall|i:int| 0<=i<c.len() && (#[trigger] c[i]).action is Deliver ==> c[i].incoming.is_some(),
    decreases c.len(),
{
    prep::initial_mailbox(m,x,c);
    if c.len()>0 {
        let t=c.drop_first();let a=c[0].action;let y=read::next(m,x,a);
        assert forall|i:int| 0<=i<t.len() implies (#[trigger] t[i]).actor==Process::FirstClient by {assert(t[i]==c[i+1]);}
        inbox_inputs(m,y,t);
        assert forall|i:int| 0<=i<c.len() && (#[trigger] c[i]).action is Deliver implies c[i].incoming.is_some()
            by {if i>0 {assert(t[i-1]==c[i]);}}
        assert forall|i:int,j:int| 0<=i<j<c.len() && (#[trigger] c[i]).action is Deliver implies (#[trigger] c[j]).action!=c[i].action by {
            assert(t[j-1]==c[j]);
            if i>0 {assert(t[i-1]==c[i]);}
            else if c[j].action==a {
                let id=a->Deliver_0;assert(y.cfg.net.pending.get(id)==None);
                assert(y.cfg.net.pending.get(id)==t[j-1].incoming);assert(t[j-1].incoming.is_some());
            }
        }
    }
}

pub proof fn arm_has_mailbox<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,t:fork::Tapes)
    requires fork::admitted(m,first,res,l,b,t),
    ensures ordinary(m,build::root(m,l,b),t.replicas),mailbox(m,first,b,build::prepared(m,l,b,t.replicas),t.caller),
{
    let z=build::prepared(m,l,b,t.replicas);
    inbox_inputs(m,z,t.caller);
}

pub proof fn native_proposals<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    ensures ordinary(m,x,fired(m,prepare(),x,s)),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0];let g=prepare();let y=cmp::attempt(m,g,x,a);
        let t=fired(m,g,x,s);let u=fired(m,g,y,s.drop_first());
        native_proposals(m,y,s.drop_first());
        if ready(m,g,x,a) {
            assert(t[0]==process_step(x.cfg.net,a) && t.drop_first() =~= u);
            assert forall|i:int| 0<=i<t.len() implies prep::ordinary_input(#[trigger] t[i])
                by {if i>0 {assert(t[i]==u[i-1]);}}
        }
    }
}

pub proof fn propose_native<S>(m:Program<S>,x:State<S>,t:Tape)
    requires ordinary(m,x,t),
    ensures fired(m,prepare(),x,asm::actions(t))==t,
    decreases t.len(),
{
    if t.len()==0 {assert(asm::actions(t) =~= Seq::empty() && t =~= Seq::empty());}
    else {
        let e=t[0];let u=t.drop_first();let s=asm::actions(t);assert(prep::ordinary_input(e));
        assert(s.drop_first() =~= asm::actions(u));assert(t =~= seq![e]+u);
        assert forall|j:int| 0<=j<u.len() implies prep::ordinary_input(#[trigger] u[j]) by {assert(u[j]==t[j+1]);}
        propose_native(m,read::next(m,x,e.action),u);
    }
}

// No ordinary replica callback can change C1 memory or consume an envelope
// addressed to C1. Extra packets do not prevent reusing its chosen inputs.
pub proof fn mailbox_survives_step<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,c:Tape,a:Event)
    requires mailbox(m,first,b,x,c),ready(m,prepare(),x,a),
    ensures mailbox(m,first,b,read::next(m,x,a),c),
{
    let y=read::next(m,x,a);
    inbox_inputs(m,x,c);
    assert forall|j:int| 0<=j<c.len() && (#[trigger] c[j]).action is Deliver
        implies y.cfg.net.pending.get(c[j].action->Deliver_0)==c[j].incoming by {
        let id=c[j].action->Deliver_0;assert(x.cfg.net.pending.get(id)==c[j].incoming);
        assert(c[j].incoming.is_some());
        // The actual receive in c determines its destination.
        let z=tape::after(m,x,c.take(j));
        assert(c.take(j)+c.skip(j) =~= c);tape::concat(m,x,c.take(j),c.skip(j));
        assert(c.skip(j)[0]==c[j]);assert(c[j]==process_step(z.cfg.net,c[j].action));
        assert(c[j].incoming.unwrap().to==Process::FirstClient);
    }
    calls::play_client(m,x,y,c);
}

pub proof fn mailbox_survives<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,c:Tape,s:Seq<Event>)
    requires mailbox(m,first,b,x,c),
    ensures mailbox(m,first,b,end(m,prepare(),x,s),c),
    decreases s.len(),
{
    if s.len()>0 {
        let g=prepare();let a=s[0];let y=cmp::attempt(m,g,x,a);
        if ready(m,g,x,a) {mailbox_survives_step(m,first,b,x,c,a);}
        cmp::scan_step(m,g,x,s);mailbox_survives(m,first,b,y,c,s.drop_first());
    }
}

// Any playable preparation and private mailbox of the specified quorum
// give a complete arm of the original construction, with the real crash
// and C2 startup. No quorum is required to emit an unused reply.
pub proof fn release<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,t:Tape,c:Tape)
    requires setup(m,res,l,b),ordinary(m,build::root(m,l,b),t),mailbox(m,first,b,build::prepared(m,l,b,t),c),
    ensures prep::arm(m,first,res,l,b,t,c),
{
    let x=build::root(m,l,b);let z=build::prepared(m,l,b,t);let u=build::first_end(m,l,b,t,c);
    let start=build::prefix_actions(b,t,c);let entry=asm::entry(m,l);
    assert forall|i:int| 0<=i<t.len() implies crate::coupled_traffic::preparation_input(#[trigger] t[i]) by {assert(prep::ordinary_input(t[i]));}
    build::prepared_frame(m,l,b,t);prep::ordinary_cells(m,x,t);calls::play_client(m,z,z,c);
    let ids=ISet::new(|i:nat|i>2 && i!=11 && i!=12);
    assert forall|i:int| 0<=i<t.len() implies {let e=#[trigger] t[i];tape::slot(e.action).is_none() || ids.contains(tape::slot(e.action).unwrap())}
        by {assert(prep::ordinary_input(t[i]));}
    tape::frame(m,x,t,ISet::full(),ids);
    assert forall|id:nat| id<=2 implies #[trigger] u.cfg.net.pending.get(id)==state_after(b,5).pending.get(id) by {
        assert(ids.complement().contains(id));assert(z.cfg.net.pending.get(id)==x.cfg.net.pending.get(id));
        if calls::takes(c,id) {assert(z.cfg.net.pending.contains_key(id) && z.cfg.net.pending[id].to==Process::FirstClient);}
    }
    assert(u.cfg.net.pending.get(11)==None && u.cfg.net.pending.get(12)==None);
    assert(pair::before_issue(m,u,l));asm::launch(m,l,Some(b));asm::native_prefix(m,x,t,true);asm::native_prefix(m,z,c,true);
    asm::prefix_concat(m,entry,asm::boot(Some(b)),asm::actions(t),true);
    asm::prefix_concat(m,entry,asm::boot(Some(b))+asm::actions(t),asm::actions(c),true);
    pair::close_at(m,res,l,u,true);asm::prefix_concat(m,entry,start,pair::close(true),true);
    let issued=prep::cutoff(m,l,b,t,c);
    assert forall|id:nat| id<=2 implies #[trigger] issued.cfg.net.pending.get(id)==state_after(b,5).pending.get(id)
        by {assert(u.cfg.net.pending.get(id)==state_after(b,5).pending.get(id));}
}

// Every alternative ordinary interleaving reaching the same prepared
// configuration lifts with the original private caller tape.
pub proof fn retime<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,t:fork::Tapes,u:Tape)
    requires setup(m,res,l,b),fork::admitted(m,first,res,l,b,t),ordinary(m,build::root(m,l,b),u),
        build::prepared(m,l,b,u)==build::prepared(m,l,b,t.replicas),
    ensures prep::arm(m,first,res,l,b,u,t.caller),prep::cutoff(m,l,b,u,t.caller)==fork::cut(m,l,b,t),
{
    arm_has_mailbox(m,first,res,l,b,t);release(m,first,res,l,b,u,t.caller);
}


pub proof fn swap_independent_neighbors<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,
    p:Tape,e:Observation,h:Observation,q:Tape,c:Tape)
    requires setup(m,res,l,b),prep::arm(m,first,res,l,b,p+seq![e,h]+q,c),tape::independent(e,h),
    ensures prep::arm(m,first,res,l,b,p+seq![h,e]+q,c),
        prep::cutoff(m,l,b,p+seq![h,e]+q,c)==prep::cutoff(m,l,b,p+seq![e,h]+q,c),
{
    let x=build::root(m,l,b);let y=tape::after(m,x,p);let t=p+seq![e,h]+q;let u=p+seq![h,e]+q;
    assert(t =~= p+(seq![e,h]+q) && u =~= p+(seq![h,e]+q));
    tape::concat(m,x,p,seq![e,h]+q);tape::concat(m,y,seq![e,h],q);tape::swap(m,y,e,h);
    tape::concat(m,y,seq![h,e],q);tape::concat(m,x,p,seq![h,e]+q);
    assert forall|i:int| 0<=i<u.len() implies prep::ordinary_input(#[trigger] u[i]) by {
        if i==p.len() {assert(u[i]==t[i+1]);} else if i==p.len()+1 {assert(u[i]==t[i-1]);} else {assert(u[i]==t[i]);}
    }
    retime(m,first,res,l,b,fork::Tapes{replicas:t,caller:c},u);
}

// After a private dequeue the reserved name cannot be sent or received
// again. Other ordinary names may be reused freely in the same run.
proof fn spent_reply<S>(m:Program<S>,x:State<S>,t:Tape,id:nat)
    requires tape::plays(m,x,t),x.reserved.contains(id),!x.cfg.net.pending.contains_key(id),
    ensures forall|k:int| 0<=k<t.len() ==> tape::slot((#[trigger] t[k]).action)!=Some(id),
    decreases t.len(),
{
    if t.len()>0 {
        let a=t[0].action;assert(tape::slot(a)!=Some(id));spent_reply(m,read::next(m,x,a),t.drop_first(),id);
        assert forall|k:int| 0<=k<t.len() implies tape::slot((#[trigger] t[k]).action)!=Some(id)
            by {if k>0 {assert(t[k]==t.drop_first()[k-1]);}}
    }
}

proof fn private_dequeues_commute<S>(m:Program<S>,x:State<S>,t:Tape)
    requires tape::plays(m,x,t),pair::c1_protected(x),
    ensures tape::reorderable(t,Process::FirstClient,false),
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let a=e.action;let y=read::next(m,x,a);let u=t.drop_first();
        assert(pair::c1_protected(y)) by {
            assert forall|id:nat| y.cfg.net.pending.contains_key(id) && y.cfg.net.pending[id].to==Process::FirstClient
                implies #[trigger] y.reserved.contains(id) by {
                if x.cfg.net.pending.get(id)==y.cfg.net.pending.get(id) {assert(x.reserved.contains(id));}
            }
        }
        private_dequeues_commute(m,y,u);
        if e.actor==Process::FirstClient && tape::slot(a).is_some() {
            let id=tape::slot(a).unwrap();assert(a is Deliver && x.cfg.net.pending[id].to==Process::FirstClient);
            assert(x.reserved.contains(id));spent_reply(m,y,u,id);
        }
        assert forall|i:int,j:int| 0<=i<j<t.len() && (#[trigger] t[i]).actor==Process::FirstClient
            && (#[trigger] t[j]).actor!=Process::FirstClient implies tape::independent(t[i],t[j]) by {
            assert(u[j-1]==t[j]);if i>0 {assert(u[i-1]==t[i]);}
        }
    }
}

// A property of a single unmodified native first-return history. C1 can
// be interleaved with replicas at arbitrary positions. There is no test
// here concerning the other execution, a scheduler or a future result.
pub open spec fn selected_service<S>(first:spec_fn(S)->int,b:Fork,p:asm::Service<S>) -> bool {
    let t=tape::record(p,0);let c=calls::caller(p);let r=crate::origin(b.branch);
    first((p.states.last().cfg.private)(Process::FirstClient))==first_value(b)
        && build::heard(c,r) && build::heard(c,Replica::R3)
        && forall|i:int| 0<=i<t.len() ==> {
            let e=#[trigger] t[i];
            if e.actor==Process::FirstClient {e.incoming.is_none() || e.incoming.unwrap().from==at(r)
                || e.incoming.unwrap().from==at(Replica::R3)} else {prep::ordinary_input(e)}
        }
}

pub proof fn normalize_selected_return<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,p:asm::Service<S>)
    requires pair::c1_protected(x),!x.cfg.net.first_stopped,
        crate::promotion_wait::first_return(mail::active_step(m),mail::posted(m),x,p),selected_service(first,b,p),
    ensures ({
        let t=crate::coupled_sources::replicas(p);let c=calls::caller(p);let z=tape::after(m,x,t);
        ordinary(m,x,t) && mailbox(m,first,b,z,c) && tape::after(m,z,c)==p.states.last()
    }),
{
    let full=tape::record(p,0);let t=crate::coupled_sources::replicas(p);let c=calls::caller(p);
    let caller=Process::FirstClient;let z=tape::after(m,x,t);
    tape::recorded(m,p,0);private_dequeues_commute(m,x,full);
    tape::factor_group(m,x,full,caller,false);tape::concat(m,x,t,c);cause::pending_on_caller(m,p,0);
    assert forall|i:int| 0<=i<t.len() implies prep::ordinary_input(#[trigger] t[i]) by {
        tape::picked(full,caller,false,i);let k=choose|k:int| 0<=k<full.len() && full[k]==t[i];assert(full[k].actor!=caller);
    }
    let sites=ISet::new(|q:Process|q is At);
    assert forall|i:int| 0<=i<t.len() implies sites.contains((#[trigger] t[i]).actor) by {assert(prep::ordinary_input(t[i]));}
    tape::frame(m,x,t,sites,ISet::full());assert(sites.complement().contains(caller));
    assert forall|i:int| 0<=i<c.len() implies {let e=#[trigger] c[i];e.actor==caller && !(e.action is Send)
        && (e.incoming.is_none() || e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3))}
        by {
            tape::picked(full,caller,true,i);let k=choose|k:int| 0<=k<full.len() && full[k]==c[i];
            assert(mail::active_step(m)(p.states[k],p.actions[k],p.states[k+1]));
        }
    inbox_inputs(m,z,c);
}

pub(crate) proof fn ordinary_keeps_caller<S>(m:Program<S>,x:State<S>,t:Tape)
    requires ordinary(m,x,t),
    ensures ({
        let z=tape::after(m,x,t);(z.cfg.private)(Process::FirstClient)==(x.cfg.private)(Process::FirstClient)
            && z.cfg.net.first_stopped==x.cfg.net.first_stopped
    }),
{
    let sites=ISet::new(|p:Process|p is At);
    assert forall|i:int| 0<=i<t.len() implies sites.contains((#[trigger] t[i]).actor)
        by {assert(crate::independent_preparations::ordinary_input(t[i]));}
    tape::frame(m,x,t,sites,ISet::full());assert(sites.complement().contains(Process::FirstClient));
}


proof fn pick_uniform(t:Tape,client:bool)
    requires forall|i:int| 0<=i<t.len() ==> ((#[trigger] t[i]).actor==Process::FirstClient)==client,
    ensures tape::pick(t,Process::FirstClient,true)==if client {t} else {Seq::<Observation>::empty()},
    decreases t.len(),
{
    if t.len()>0 {
        let u=t.drop_first();
        assert forall|i:int| 0<=i<u.len() implies ((#[trigger] u[i]).actor==Process::FirstClient)==client by {assert(u[i]==t[i+1]);}
        assert((t[0].actor==Process::FirstClient)==client);pick_uniform(u,client);assert(seq![t[0]]+u =~= t);
    }
}

proof fn private_pending_at<S>(m:Program<S>,x:State<S>,c:Tape,k:int)
    requires 0<=k<c.len(),tape::plays(m,x,c),cause::pending_inputs(m,(x.cfg.private)(Process::FirstClient),c),
        forall|i:int| 0<=i<c.len() ==> (#[trigger] c[i]).actor==Process::FirstClient,
    ensures !mail::posted(m)(tape::after(m,x,c.take(k))),
    decreases k,
{
    if k==0 {assert(c.take(0) =~= Seq::empty());} else {
        let u=c.drop_first();let y=read::next(m,x,c[0].action);
        assert(c[0].actor==Process::FirstClient && c.take(k)[0]==c[0] && c.take(k).drop_first() =~= u.take(k-1));
        assert forall|i:int| 0<=i<u.len() implies (#[trigger] u[i]).actor==Process::FirstClient by {assert(u[i]==c[i+1]);}
        private_pending_at(m,y,u,k-1);
    }
}

pub proof fn release_to_service<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,x:State<S>,t:Tape,c:Tape) -> (p:asm::Service<S>)
    requires ordinary(m,x,t),mailbox(m,first,b,tape::after(m,x,t),c),
    ensures crate::promotion_wait::first_return(mail::active_step(m),mail::posted(m),x,p),selected_service(first,b,p),
        tape::record(p,0)==t+c && p.states.last()==tape::after(m,tape::after(m,x,t),c),
{
    let z=tape::after(m,x,t);let u=t+c;let p=cmp::path(m,x,u);
    let caller=Process::FirstClient;tape::concat(m,x,t,c);ordinary_keeps_caller(m,x,t);
    assert(c.len()>0 && !mail::posted(m)(z));
    assert forall|i:int| 0<=i<u.len() implies ({
        let k=u.take(i);let v=tape::after(m,x,k);let a=#[trigger] p.actions[i];
        p.states[i]==v && u[i]==process_step(v.cfg.net,a) && mail::active_step(m)(v,a,p.states[i+1]) && !mail::posted(m)(v)
    }) by {
        let k=u.take(i);let rest=u.skip(i);let v=tape::after(m,x,k);
        assert(k+rest =~= u && rest[0]==u[i]);tape::concat(m,x,k,rest);
        assert(k+seq![u[i]] =~= u.take(i+1));tape::concat(m,x,k,seq![u[i]]);
        assert(seq![u[i]].drop_first() =~= Seq::empty());reveal_with_fuel(tape::after,2);
        if i<t.len() {
            assert(k =~= t.take(i));
            assert forall|j:int| 0<=j<k.len() implies prep::ordinary_input(#[trigger] k[j]) by {assert(k[j]==t[j]);}
            ordinary_keeps_caller(m,x,k);
        } else {
            let h=i-t.len();assert(k =~= t+c.take(h));tape::concat(m,x,t,c.take(h));private_pending_at(m,z,c,h);
        }
    }
    assert(crate::promotion_wait::valid_edges(mail::active_step(m),p));
    assert(crate::promotion_wait::pending_before(mail::posted(m),p)) by {
        assert forall|i:int| 0<=i<p.actions.len() implies !mail::posted(m)(#[trigger] p.states[i]) by {
            assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));
        }
    }
    assert(tape::record(p,0) =~= u);
    assert(u.take(0) =~= Seq::empty() && u.take(u.len() as int) =~= u);
    assert forall|i:int| 0<=i<t.len() implies (#[trigger] t[i]).actor!=caller by {assert(prep::ordinary_input(t[i]));}
    pick_uniform(t,false);pick_uniform(c,true);cause::pick_concat(t,c,caller,true);
    assert(calls::caller(p) =~= c);
    assert forall|i:int| 0<=i<u.len() implies {let e=#[trigger] u[i];if e.actor==caller {e.incoming.is_none()
        || e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3)} else {prep::ordinary_input(e)}}
        by {if i<t.len() {assert(u[i]==t[i]);} else {assert(u[i]==c[i-t.len()]);}}
    p
}

}
