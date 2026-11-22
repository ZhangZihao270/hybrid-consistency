// Same fork input, different live sets. Project an actual preparation
// onto its sole-majority reference, leaving in-flight traffic in place.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*};
use crate::coupled_construction as build;
use crate::first_assembly::{self as asm,Lanes};
use crate::first_schedule::reference;
use crate::first_splice::{self as tape,Observation,Tape};
use crate::guarded_comparison::{self as cmp,ready,prepare,end};
use crate::hybrid_fork::{self as names,Issuer};
use crate::independent_read::{self as read,State};
use crate::read_call::{Program,Event};
use crate::sr1_majorities::missing;

verus! {

pub open spec fn named(who:Issuer,a:Event) -> bool {
    match a {Action::Send(i,q)=>i>5 && i!=11 && i!=12 && q.from==at(who(i)),_=>true}
}
pub open spec fn fresh_script(who:Issuer,used:Set<nat>,s:Seq<Event>) -> bool {
    (forall|i:int| 0<=i<s.len() ==> named(who,#[trigger] s[i]) && (s[i] is Send ==> !used.contains(s[i]->Send_0)))
        && (forall|i:int,j:int| 0<=i<j<s.len() && (#[trigger] s[i]) is Send && (#[trigger] s[j]) is Send ==> s[i]->Send_0!=s[j]->Send_0)
}
pub open spec fn allocated(used:Set<nat>,a:Event) -> Set<nat> {
    if a is Send {used.insert(a->Send_0)} else {used}
}
pub open spec fn omitted_name(b:Fork,who:Issuer,id:nat) -> bool { id>5 && who(id)==missing(b) }

// The reference may still hold a packet addressed to the failed process
// that was consumed in the original. Omitted senders' fresh names are
// always empty in the reference. Their packets can remain queued for C1
// and for the serving replicas in the original.
pub open spec fn slot<S>(b:Fork,who:Issuer,x:State<S>,y:State<S>,id:nat) -> bool {
    let q=x.cfg.net.pending.get(id);let p=y.cfg.net.pending.get(id);let d=at(missing(b));
    if omitted_name(b,who,id) {
        q.is_none() && !x.reserved.contains(id) && (p.is_some() ==> p.unwrap().from==d)
    } else {
        x.reserved.contains(id)==y.reserved.contains(id) && (q==p || (q.is_some() && q.unwrap().to==d && p.is_none()))
    }
}
pub open spec fn allocator_ok<S>(who:Issuer,x:State<S>) -> bool {
    forall|i:nat| i>5 && x.owners.contains_key(i) ==> #[trigger] x.owners[i]==at(who(i))
}
pub open spec fn compared<S>(b:Fork,who:Issuer,x:State<S>,y:State<S>,changed:Set<Process>) -> bool {
    let d=missing(b);
    x.cfg.net.unavailable==Some(d) && y.cfg.net.unavailable.is_none()
        && !x.cfg.net.r3_crashed && !y.cfg.net.r3_crashed && !x.cfg.net.first_stopped && !y.cfg.net.first_stopped
        && !x.cfg.net.second_started && !y.cfg.net.second_started
        && allocator_ok(who,x) && allocator_ok(who,y)
        && (forall|p:Process| p!=at(d) && !changed.contains(p) ==> #[trigger] (x.cfg.private)(p)==(y.cfg.private)(p))
        && (forall|r:Replica| r!=d ==> #[trigger] (x.cfg.net.locals)(r)==(y.cfg.net.locals)(r))
        && (forall|id:nat| #[trigger] slot(b,who,x,y,id))
}
pub open spec fn shadow<S>(b:Fork,who:Issuer,x:State<S>,y:State<S>) -> bool {compared(b,who,x,y,Set::empty())}
pub open spec fn issued_names<S>(x:State<S>,used:Set<nat>) -> bool {
    forall|id:nat| id>5 && (x.cfg.net.pending.contains_key(id) || x.reserved.contains(id)) ==> #[trigger] used.contains(id)
}

pub proof fn initial_shadow<S>(m:Program<S>,l:Lanes,b:Fork,who:Issuer)
    requires names::proper(l,who),
    ensures shadow(b,who,reference(m,b,5),build::root(m,l,b)),issued_names(reference(m,b,5),Set::empty()),
{
    let x=reference(m,b,5);let y=build::root(m,l,b);
    assert(crate::sr1_majorities::count(b,5)==5);
    assert forall|p:Process| p!=at(missing(b)) implies #[trigger] (x.cfg.private)(p)==(y.cfg.private)(p)
        by {crate::sr1_majorities::local_at(m,b,p,5);}
    assert(x.cfg.net.pending =~= y.cfg.net.pending);
    assert forall|id:nat| #[trigger] slot(b,who,x,y,id) by {if id>5 {assert(!x.cfg.net.pending.contains_key(id));}}
    assert(allocator_ok(who,y)) by {
        assert forall|i:nat| i>5 && y.owners.contains_key(i) implies #[trigger] y.owners[i]==at(who(i)) by {assert(l.contains_key(i));}
    }
}

proof fn advance_both<S>(m:Program<S>,b:Fork,who:Issuer,x:State<S>,y:State<S>,a:Event,changed:Set<Process>)
    requires compared(b,who,x,y,changed),named(who,a),tape::moves(a),
        read::service_step(m)(x,a,read::next(m,x,a)),read::service_step(m)(y,a,read::next(m,y,a)),
        process_step(x.cfg.net,a)==process_step(y.cfg.net,a),
    ensures compared(b,who,read::next(m,x,a),read::next(m,y,a),changed),
{
    let u=read::next(m,x,a);let v=read::next(m,y,a);
    assert forall|id:nat| #[trigger] slot(b,who,u,v,id) by {
        assert(slot(b,who,x,y,id));
        if tape::slot(a)!=Some(id) {assert(u.cfg.net.pending.get(id)==x.cfg.net.pending.get(id) && v.cfg.net.pending.get(id)==y.cfg.net.pending.get(id));}
        else if a is Send {assert(a->Send_1.from!=at(missing(b)));}
    }
    assert forall|p:Process| p!=at(missing(b)) && !changed.contains(p) implies #[trigger] (u.cfg.private)(p)==(v.cfg.private)(p)
        by {assert((x.cfg.private)(p)==(y.cfg.private)(p));}
    assert forall|r:Replica| r!=missing(b) implies #[trigger] (u.cfg.net.locals)(r)==(v.cfg.net.locals)(r)
        by {assert((x.cfg.net.locals)(r)==(y.cfg.net.locals)(r));assert(local_input(x.cfg.net,a,r)==local_input(y.cfg.net,a,r));}
}

// Every reference step has its exact native callback in the original,
// including any peer delivery that the quorum needs. Extra enqueued
// packets and the original's live third process do not force an action.
pub(crate) proof fn offer_reference_step<S>(m:Program<S>,b:Fork,who:Issuer,x:State<S>,y:State<S>,a:Event,changed:Set<Process>)
    requires compared(b,who,x,y,changed),named(who,a),tape::moves(a),read::service_step(m)(x,a,read::next(m,x,a)),
    ensures ({
        let e=process_step(x.cfg.net,a);let u=read::next(m,x,a);let v=read::next(m,y,a);
        process_step(y.cfg.net,a)==e && enabled(y.cfg.net,a) && e.actor!=at(missing(b))
            && read::names_sender(y,a) && crate::confirmation::fresh_send(a,y.reserved)
            && read::service_step(m)(y,a,v)==(m.accept)((y.cfg.private)(e.actor),e)
            && (read::service_step(m)(y,a,v) ==> compared(b,who,u,v,changed))
            && (!read::service_step(m)(y,a,v) ==> changed.contains(e.actor))
    }),
{
    let e=process_step(x.cfg.net,a);let d=missing(b);
    assert(live(x.cfg.net,e.actor) && e.actor!=at(d));
    match a {
        Action::Deliver(i)=>{assert(slot(b,who,x,y,i));assert(x.cfg.net.pending[i].to!=at(d));
            assert(x.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));},
        Action::Send(i,q)=>{assert(!omitted_name(b,who,i) && slot(b,who,x,y,i));if y.owners.contains_key(i) {assert(y.owners[i]==at(who(i)));}},
        _=>{}
    }
    if e.actor is At {assert((x.cfg.net.locals)(e.actor->At_0)==(y.cfg.net.locals)(e.actor->At_0));}
    assert(process_step(y.cfg.net,a)==e);let v=read::next(m,y,a);
    assert(read::service_step(m)(y,a,v)==(m.accept)((y.cfg.private)(e.actor),e));
    if read::service_step(m)(y,a,v) {advance_both(m,b,who,x,y,a,changed);}
    else if !changed.contains(e.actor) {assert((x.cfg.private)(e.actor)==(y.cfg.private)(e.actor));}
}

pub open spec fn changes_on_foreign_input<S>(m:Program<S>,b:Fork,who:Issuer,y:State<S>,a:Event) -> bool {
    let e=process_step(y.cfg.net,a);let s=(y.cfg.private)(e.actor);
    ready(m,prepare(),y,a) && a is Deliver && omitted_name(b,who,a->Deliver_0)
        && e.actor is At && e.actor!=at(missing(b)) && e.incoming.is_some()
        && e.incoming.unwrap().from==at(missing(b)) && e.incoming.unwrap().to==e.actor
        && e.incoming.unwrap().path!=Path::Weak && (m.update)(s,e)!=s
}

pub open spec fn kept(b:Fork,who:Issuer,e:Observation) -> bool {
    e.actor!=at(missing(b)) && !(e.action is Deliver && omitted_name(b,who,e.action->Deliver_0))
}
pub open spec fn projection(b:Fork,who:Issuer,t:Tape) -> Tape
    decreases t.len(),
{
    if t.len()==0 {Seq::empty()} else {
        let r=projection(b,who,t.drop_first());if kept(b,who,t[0]) {seq![t[0]]+r} else {r}
    }
}
// Only an actually consumed omitted-sender packet that changes a private
// state can put its recipient in this set. It is an upper bound; a
// subsequent guard test establishes use.
pub open spec fn affected<S>(m:Program<S>,b:Fork,who:Issuer,y:State<S>,t:Tape) -> Set<Process> {
    set![at(Replica::R1),at(Replica::R2),at(Replica::R3)].filter(|p:Process|exists|j:int| 0<=j<t.len() && (#[trigger] t[j]).actor==p
        && changes_on_foreign_input(m,b,who,tape::after(m,y,t.take(j)),t[j].action))
}
pub open spec fn refusal<S>(m:Program<S>,yes:State<S>,no:State<S>,e:Observation) -> bool {
    let a=e.action;let u=(yes.cfg.private)(e.actor);let v=(no.cfg.private)(e.actor);
    e.actor is At && e==process_step(yes.cfg.net,a) && e==process_step(no.cfg.net,a) && tape::moves(a)
        && read::service_step(m)(yes,a,read::next(m,yes,a)) && enabled(no.cfg.net,a)
        && read::names_sender(no,a) && crate::confirmation::fresh_send(a,no.reserved)
        && u!=v && (m.accept)(u,e) && !(m.accept)(v,e)
}
// The accepting side is a physical reference. The rejected proposal is
// offered to the original only after a genuinely executed common prefix.
pub open spec fn suffix_refusal<S>(m:Program<S>,x:State<S>,y:State<S>,t:Tape,k:int) -> bool {
    let h=t.take(k);
    0<=k<t.len() && tape::plays(m,y,h) && refusal(m,tape::after(m,x,h),tape::after(m,y,h),t[k])
}

pub proof fn replay_or_refusal<S>(m:Program<S>,b:Fork,who:Issuer,x:State<S>,y:State<S>,t:Tape,changed:Set<Process>)
    requires compared(b,who,x,y,changed),forall|p:Process| #[trigger] changed.contains(p) ==> p is At,
        tape::plays(m,x,t),forall|i:int| 0<=i<t.len() ==> named(who,(#[trigger] t[i]).action),
    ensures (tape::plays(m,y,t) && compared(b,who,tape::after(m,x,t),tape::after(m,y,t),changed))
        || exists|k:int| #[trigger] suffix_refusal(m,x,y,t,k) && changed.contains(t[k].actor),
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let a=e.action;let tail=t.drop_first();let u=read::next(m,x,a);let v=read::next(m,y,a);
        assert(named(who,a));offer_reference_step(m,b,who,x,y,a,changed);
        if read::service_step(m)(y,a,v) {
            assert forall|i:int| 0<=i<tail.len() implies named(who,(#[trigger] tail[i]).action) by {assert(t[i+1]==tail[i]);}
            replay_or_refusal(m,b,who,u,v,tail,changed);
            if exists|j:int| #[trigger] suffix_refusal(m,u,v,tail,j) && changed.contains(tail[j].actor) {
                let j=choose|j:int| #[trigger] suffix_refusal(m,u,v,tail,j) && changed.contains(tail[j].actor);
                let k=j+1;let h=t.take(k);assert(h[0]==e && h.drop_first() =~= tail.take(j) && t[k]==tail[j]);
                assert(suffix_refusal(m,x,y,t,k) && changed.contains(t[k].actor));
            }
        } else {
            assert(t.take(0) =~= Seq::empty() && changed.contains(e.actor) && e.actor is At);assert(suffix_refusal(m,x,y,t,0));
        }
    }
}

pub open spec fn prefix_refusal<S>(m:Program<S>,b:Fork,who:Issuer,x:State<S>,y:State<S>,t:Tape,k:int) -> bool {
    let u=t.take(k);let v=projection(b,who,u);let r=tape::after(m,x,v);let z=tape::after(m,y,u);
    0<=k<t.len() && kept(b,who,t[k]) && tape::plays(m,x,v) && refusal(m,z,r,t[k])
}

// The prefix is taken from the actual, all-live tape. At each retained
// action compare its real observation, even when the private states have
// diverged. A masked guard must genuinely disagree to prevent projection.
proof fn inward<S>(m:Program<S>,b:Fork,who:Issuer,used:Set<nat>,x:State<S>,y:State<S>,e:Observation,changed:Set<Process>)
    requires compared(b,who,x,y,changed),issued_names(x,used),named(who,e.action),e.action is Send ==> !used.contains(e.action->Send_0),
        ready(m,prepare(),y,e.action),e==process_step(y.cfg.net,e.action),
    ensures ({
        let a=e.action;let v=read::next(m,y,a);let r=if kept(b,who,e) {read::next(m,x,a)} else {x};
        let add=if changes_on_foreign_input(m,b,who,y,a) {changed.insert(e.actor)} else {changed};
        issued_names(r,allocated(used,a))
            && if kept(b,who,e) {
                e==process_step(x.cfg.net,a) && !changes_on_foreign_input(m,b,who,y,a) &&
                ((ready(m,prepare(),x,a) && compared(b,who,r,v,changed))
                    || (refusal(m,y,x,e) && changed.contains(e.actor)))
            } else {compared(b,who,x,v,add)}
    }),
{
    let a=e.action;let g=prepare();let d=missing(b);let v=read::next(m,y,a);
    let r=if kept(b,who,e) {read::next(m,x,a)} else {x};
    assert forall|i:nat| i>5 && (r.cfg.net.pending.contains_key(i) || r.reserved.contains(i)) implies
        #[trigger] allocated(used,a).contains(i) by {
        if !(a is Send && a->Send_0==i) {assert(x.cfg.net.pending.contains_key(i) || x.reserved.contains(i));assert(used.contains(i));}
    }
    if kept(b,who,e) {
        if a is Deliver {
            let i=a->Deliver_0;assert(slot(b,who,x,y,i));assert(x.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));
        } else if a is Send {
            let i=a->Send_0;assert(!used.contains(i) && !x.cfg.net.pending.contains_key(i) && !x.reserved.contains(i));
            if x.owners.contains_key(i) {assert(x.owners[i]==at(who(i)));}
        }
        assert(e.actor is At && (x.cfg.net.locals)(e.actor->At_0)==(y.cfg.net.locals)(e.actor->At_0));
        assert(process_step(x.cfg.net,a)==e);assert(ready(m,g,x,a)==(m.accept)((x.cfg.private)(e.actor),e));
        if ready(m,g,x,a) {advance_both(m,b,who,x,y,a,changed);}
        else if !changed.contains(e.actor) {assert((x.cfg.private)(e.actor)==(y.cfg.private)(e.actor));}
    } else {
        let add=if changes_on_foreign_input(m,b,who,y,a) {changed.insert(e.actor)} else {changed};
        if e.actor!=at(d) {
            assert(slot(b,who,x,y,a->Deliver_0));assert(e.incoming.unwrap().from==at(d));
            assert(!changes_on_foreign_input(m,b,who,y,a) ==> (m.update)((y.cfg.private)(e.actor),e)==(y.cfg.private)(e.actor));
        }
        assert forall|p:Process| p!=at(d) && !add.contains(p) implies #[trigger] (x.cfg.private)(p)==(v.cfg.private)(p) by {assert((x.cfg.private)(p)==(y.cfg.private)(p));}
        assert forall|j:Replica| j!=d implies #[trigger] (x.cfg.net.locals)(j)==(v.cfg.net.locals)(j) by {
            assert((x.cfg.net.locals)(j)==(y.cfg.net.locals)(j));
            assert(local_input(y.cfg.net,a,j).is_none() || !(local_input(y.cfg.net,a,j).unwrap() is Copy));
        }
        assert forall|id:nat| #[trigger] slot(b,who,x,v,id) by {
            assert(slot(b,who,x,y,id));
            if tape::slot(a)!=Some(id) {assert(y.cfg.net.pending.get(id)==v.cfg.net.pending.get(id));}
        }
    }
}

pub(crate) proof fn fresh_tail(who:Issuer,used:Set<nat>,s:Seq<Event>)
    requires s.len()>0,fresh_script(who,used,s),
    ensures fresh_script(who,allocated(used,s[0]),s.drop_first()),
{
    let u=s.drop_first();let spent=allocated(used,s[0]);
    assert forall|i:int| 0<=i<u.len() implies named(who,#[trigger] u[i]) && (u[i] is Send ==> !spent.contains(u[i]->Send_0))
        by {assert(u[i]==s[i+1]);}
    assert forall|i:int,j:int| 0<=i<j<u.len() && (#[trigger] u[i]) is Send && (#[trigger] u[j]) is Send
        implies u[i]->Send_0!=u[j]->Send_0 by {assert(u[i]==s[i+1] && u[j]==s[j+1]);}
}

proof fn compare_prefix<S>(m:Program<S>,b:Fork,who:Issuer,used:Set<nat>,x:State<S>,y:State<S>,t:Tape,changed:Set<Process>)
    requires compared(b,who,x,y,changed),issued_names(x,used),crate::mailbox_preparation::ordinary(m,y,t),fresh_script(who,used,asm::actions(t)),
    ensures ({
        let v=projection(b,who,t);
        (tape::plays(m,x,v) && compared(b,who,tape::after(m,x,v),tape::after(m,y,t),changed.union(affected(m,b,who,y,t))))
            || exists|i:int| #[trigger] prefix_refusal(m,b,who,x,y,t,i) && changed.union(affected(m,b,who,y,t.take(i))).contains(t[i].actor)
    }),
    decreases t.len(),
{
    if t.len()==0 {assert(projection(b,who,t) =~= Seq::empty());assert(changed.union(affected(m,b,who,y,t)) =~= changed);}
    else {
        let e=t[0];let a=e.action;let s=asm::actions(t);let tail=t.drop_first();let v=read::next(m,y,a);
        let take=kept(b,who,e);let r=if take {read::next(m,x,a)} else {x};
        let add=if changes_on_foreign_input(m,b,who,y,a) {changed.insert(e.actor)} else {changed};
        assert(crate::independent_preparations::ordinary_input(e) && e==process_step(y.cfg.net,a));
        assert(s[0]==a && s.drop_first() =~= asm::actions(tail));assert(named(who,a));inward(m,b,who,used,x,y,e,changed);
        if take && !ready(m,prepare(),x,a) {
            assert(t.take(0) =~= Seq::empty() && projection(b,who,t.take(0)) =~= Seq::empty());assert(prefix_refusal(m,b,who,x,y,t,0));
            assert(changed.union(affected(m,b,who,y,t.take(0))).contains(e.actor));
        } else {
            fresh_tail(who,used,s);
            assert forall|i:int| 0<=i<tail.len() implies crate::independent_preparations::ordinary_input(#[trigger] tail[i]) by {assert(tail[i]==t[i+1]);}
            compare_prefix(m,b,who,allocated(used,a),r,v,tail,add);
            if take {
                assert(projection(b,who,t) =~= seq![e]+projection(b,who,tail));
                assert(projection(b,who,t).drop_first() =~= projection(b,who,tail));
            } else {assert(projection(b,who,t) =~= projection(b,who,tail));}
            assert(t.take(t.len() as int) =~= t && tail.take(t.len() as int-1) =~= tail);
            head_affected(m,b,who,y,t,changed,t.len() as int);
            if exists|j:int| #[trigger] prefix_refusal(m,b,who,r,v,tail,j) && add.union(affected(m,b,who,v,tail.take(j))).contains(tail[j].actor) {
                let j=choose|j:int| #[trigger] prefix_refusal(m,b,who,r,v,tail,j) && add.union(affected(m,b,who,v,tail.take(j))).contains(tail[j].actor);
                let k=j+1;let h=t.take(k);assert(h[0]==e && h.drop_first() =~= tail.take(j) && t[k]==tail[j]);
                if take {assert(projection(b,who,h) =~= seq![e]+projection(b,who,tail.take(j)));
                    assert(projection(b,who,h).drop_first() =~= projection(b,who,tail.take(j)));}
                else {assert(projection(b,who,h) =~= projection(b,who,tail.take(j)));}
                head_affected(m,b,who,y,t,changed,k);assert(prefix_refusal(m,b,who,x,y,t,k));
                assert(changed.union(affected(m,b,who,y,h)).contains(t[k].actor));
            }
        }
    }
}

proof fn head_affected<S>(m:Program<S>,b:Fork,who:Issuer,y:State<S>,t:Tape,c:Set<Process>,k:int)
    requires 0<k<=t.len(),t[0]==process_step(y.cfg.net,t[0].action),
    ensures ({
        let e=t[0];let v=read::next(m,y,e.action);let n=if changes_on_foreign_input(m,b,who,y,e.action) {c.insert(e.actor)} else {c};
        c.union(affected(m,b,who,y,t.take(k)))==n.union(affected(m,b,who,v,t.drop_first().take(k-1)))
    }),
{
    let e=t[0];let h=t.take(k);let t1=t.drop_first().take(k-1);let v=read::next(m,y,e.action);
    let n=if changes_on_foreign_input(m,b,who,y,e.action) {c.insert(e.actor)} else {c};
    assert(h[0]==e && h.take(0) =~= Seq::empty());
    assert forall|p:Process| #[trigger] c.union(affected(m,b,who,y,h)).contains(p)==n.union(affected(m,b,who,v,t1)).contains(p) by {
        if affected(m,b,who,y,h).contains(p) {
            let j=choose|j:int| 0<=j<h.len() && (#[trigger] h[j]).actor==p && changes_on_foreign_input(m,b,who,tape::after(m,y,h.take(j)),h[j].action);
            if j>0 {assert(h.take(j)[0]==e && h.take(j).drop_first() =~= t1.take(j-1) && t1[j-1]==h[j]);}
        }
        if affected(m,b,who,v,t1).contains(p) {
            let j=choose|j:int| 0<=j<t1.len() && (#[trigger] t1[j]).actor==p && changes_on_foreign_input(m,b,who,tape::after(m,v,t1.take(j)),t1[j].action);
            assert(h.take(j+1)[0]==e && h.take(j+1).drop_first() =~= t1.take(j) && h[j+1]==t1[j]);
        }
    }
    assert(c.union(affected(m,b,who,y,h)) =~= n.union(affected(m,b,who,v,t1)));
}

pub proof fn project_actual_preparation<S>(m:Program<S>,l:Lanes,b:Fork,who:Issuer,t:Tape)
    requires names::proper(l,who),crate::mailbox_preparation::ordinary(m,build::root(m,l,b),t),fresh_script(who,Set::empty(),asm::actions(t)),
    ensures ({
        let x=reference(m,b,5);let y=build::root(m,l,b);let v=projection(b,who,t);
        (tape::plays(m,x,v) && compared(b,who,tape::after(m,x,v),tape::after(m,y,t),affected(m,b,who,y,t)))
            || exists|i:int| #[trigger] prefix_refusal(m,b,who,x,y,t,i) && affected(m,b,who,y,t.take(i)).contains(t[i].actor)
    }),
{
    let x=reference(m,b,5);let y=build::root(m,l,b);
    initial_shadow(m,l,b,who);compare_prefix(m,b,who,Set::empty(),x,y,t,Set::empty());
    assert forall|u:Tape| Set::<Process>::empty().union(#[trigger] affected(m,b,who,y,u))==affected(m,b,who,y,u) by {assert(Set::<Process>::empty().union(affected(m,b,who,y,u)) =~= affected(m,b,who,y,u));}
}

}
