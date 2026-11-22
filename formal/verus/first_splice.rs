// Finite local histories from an actual first-call execution. A transcript
// includes the actual envelope consumed and the cell read by its handler.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*, protocol::*};
use crate::first_mailbox as mail;
use crate::independent_read::{self as read, State};
use crate::promotion_wait as wait;
use crate::read_call::{Event,Program};

verus! {

pub type Observation = ProcessStep<int,Wire>;
pub type Tape = Seq<Observation>;

pub open spec fn slot(a:Event) -> Option<nat> {
    match a {Action::Send(i,_)|Action::Deliver(i)=>Some(i), _=>None}
}
pub open spec fn moves(a:Event) -> bool {
    a!=Action::CrashR3 && a!=Action::StartSecondClient && a!=Action::StopFirstClient
}
pub open spec fn after<S>(m:Program<S>,x:State<S>,t:Tape) -> State<S>
    decreases t.len(),
{
    if t.len()==0 {x} else {after(m,read::next(m,x,t[0].action),t.drop_first())}
}
pub open spec fn plays<S>(m:Program<S>,x:State<S>,t:Tape) -> bool
    decreases t.len(),
{
    if t.len()==0 {true} else {
        let e=t[0];let y=read::next(m,x,e.action);
        moves(e.action) && read::service_step(m)(x,e.action,y) && process_step(x.cfg.net,e.action)==e
            && plays(m,y,t.drop_first())
    }
}
pub open spec fn record<S>(p:wait::Path<State<S>,Event>,j:nat) -> Tape {
    Seq::new((p.actions.len()-j) as nat,|i:int|process_step(p.states[j+i].cfg.net,p.actions[j+i]))
}
pub proof fn recorded<S>(m:Program<S>,p:wait::Path<State<S>,Event>,j:nat)
    requires j<=p.actions.len(),p.states.len()==p.actions.len()+1,
        wait::valid_edges(mail::active_step(m),p),wait::pending_before(mail::posted(m),p),
    ensures plays(m,p.states[j as int],record(p,j)),after(m,p.states[j as int],record(p,j))==p.states.last(),
    decreases p.actions.len()-j,
{
    if j<p.actions.len() {
        let a=p.actions[j as int];let x=p.states[j as int];let y=p.states[j as int+1];
        assert(mail::active_step(m)(x,a,y));assert(!mail::posted(m)(x));
        recorded(m,p,j+1);assert(record(p,j).drop_first() =~= record(p,j+1));
    }
}

pub open spec fn supports(t:Tape,ps:ISet<Process>,ids:ISet<nat>) -> bool {
    forall|i:int| 0<=i<t.len() ==> {let e=#[trigger] t[i];
        ps.contains(e.actor) && (slot(e.action).is_some() ==> ids.contains(slot(e.action).unwrap()))}
}
pub open spec fn same_locals<S>(x:State<S>,z:State<S>,ps:ISet<Process>) -> bool {
    (forall|p:Process| ps.contains(p) ==> #[trigger] (x.cfg.private)(p)==(z.cfg.private)(p))
    && (forall|r:Replica| ps.contains(at(r)) ==> #[trigger] (x.cfg.net.locals)(r)==(z.cfg.net.locals)(r))
}
pub open spec fn same_slots<S>(x:State<S>,z:State<S>,ids:ISet<nat>) -> bool {
    forall|i:nat| ids.contains(i) ==> #[trigger] x.cfg.net.pending.get(i)==z.cfg.net.pending.get(i)
        && x.reserved.contains(i)==z.reserved.contains(i)
}
// Check target ownership only on actual sends. The handler sees the event's
// number. The ownership table belongs to the transport.
pub open spec fn allocates<S>(x:State<S>,t:Tape) -> bool {
    forall|i:int| 0<=i<t.len() ==> read::names_sender(x,(#[trigger] t[i]).action)
}
pub proof fn replay<S>(m:Program<S>,x:State<S>,z:State<S>,t:Tape,ps:ISet<Process>,ids:ISet<nat>)
    requires plays(m,x,t),supports(t,ps,ids),same_locals(x,z,ps),same_slots(x,z,ids),allocates(z,t),
        forall|p:Process| ps.contains(p) && #[trigger] live(x.cfg.net,p) ==> live(z.cfg.net,p),
    ensures plays(m,z,t),same_locals(after(m,x,t),after(m,z,t),ps),same_slots(after(m,x,t),after(m,z,t),ids),
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let a=e.action;let y=read::next(m,x,a);let w=read::next(m,z,a);let tail=t.drop_first();
        assert(ps.contains(e.actor));assert(live(x.cfg.net,e.actor));assert(live(z.cfg.net,e.actor));
        if let Some(id)=slot(a) {assert(ids.contains(id));assert(x.cfg.net.pending.get(id)==z.cfg.net.pending.get(id));}
        if let Process::At(r)=e.actor {assert((x.cfg.net.locals)(r)==(z.cfg.net.locals)(r));}
        assert(process_step(z.cfg.net,a)==e);assert((x.cfg.private)(e.actor)==(z.cfg.private)(e.actor));
        assert(read::names_sender(z,a));assert(read::service_step(m)(z,a,w));
        assert forall|p:Process| ps.contains(p) implies #[trigger] (y.cfg.private)(p)==(w.cfg.private)(p) by {
            assert((x.cfg.private)(p)==(z.cfg.private)(p));
        }
        assert forall|r:Replica| ps.contains(at(r)) implies #[trigger] (y.cfg.net.locals)(r)==(w.cfg.net.locals)(r) by {
            assert((x.cfg.net.locals)(r)==(z.cfg.net.locals)(r));
        }
        assert forall|id:nat| ids.contains(id) implies #[trigger] y.cfg.net.pending.get(id)==w.cfg.net.pending.get(id)
            && y.reserved.contains(id)==w.reserved.contains(id) by {assert(x.cfg.net.pending.get(id)==z.cfg.net.pending.get(id));}
        assert forall|j:int| 0<=j<tail.len() implies {let f=#[trigger] tail[j];
            ps.contains(f.actor) && (slot(f.action).is_some() ==> ids.contains(slot(f.action).unwrap()))
                && read::names_sender(w,f.action)} by {assert(tail[j]==t[j+1]);}
        assert forall|p:Process| ps.contains(p) && #[trigger] live(y.cfg.net,p) implies live(w.cfg.net,p) by {
            assert(live(x.cfg.net,p));assert(live(z.cfg.net,p));
        }
        replay(m,y,w,tail,ps,ids);
    }
}

pub proof fn frame<S>(m:Program<S>,x:State<S>,t:Tape,ps:ISet<Process>,ids:ISet<nat>)
    requires plays(m,x,t),supports(t,ps,ids),
    ensures ({
        let y=after(m,x,t);
        same_locals(x,y,ps.complement()) && same_slots(x,y,ids.complement())
        && y.calls==x.calls && y.owners==x.owners && y.requested==x.requested && y.first_requested==x.first_requested
        && y.cfg.net.unavailable==x.cfg.net.unavailable && y.cfg.net.r3_crashed==x.cfg.net.r3_crashed
        && y.cfg.net.first_stopped==x.cfg.net.first_stopped && y.cfg.net.second_started==x.cfg.net.second_started
    }),
    decreases t.len(),
{
    if t.len()>0 {
        let e=t[0];let a=e.action;let y=read::next(m,x,a);let u=t.drop_first();let end=after(m,x,t);
        assert(ps.contains(e.actor));if slot(a).is_some(){assert(ids.contains(slot(a).unwrap()));}
        assert forall|j:int| 0<=j<u.len() implies {let f=#[trigger] u[j];ps.contains(f.actor)
            && (slot(f.action).is_some() ==> ids.contains(slot(f.action).unwrap()))} by {assert(u[j]==t[j+1]);}
        frame(m,y,u,ps,ids);
        assert forall|p:Process| !ps.contains(p) implies #[trigger] (x.cfg.private)(p)==(end.cfg.private)(p) by {
            assert(ps.complement().contains(p));assert((y.cfg.private)(p)==(end.cfg.private)(p));
        }
        assert forall|r:Replica| !ps.contains(at(r)) implies #[trigger] (x.cfg.net.locals)(r)==(end.cfg.net.locals)(r) by {
            assert(ps.complement().contains(at(r)));assert((y.cfg.net.locals)(r)==(end.cfg.net.locals)(r));
        }
        assert forall|id:nat| !ids.contains(id) implies #[trigger] x.cfg.net.pending.get(id)==end.cfg.net.pending.get(id)
            && x.reserved.contains(id)==end.reserved.contains(id) by {
            assert(ids.complement().contains(id));assert(y.cfg.net.pending.get(id)==end.cfg.net.pending.get(id));
        }
    }
}

// Move a retained event left only across independent local events. A send
// and its delivery use the same slot. Reuse of a slot is visible too.
pub open spec fn independent(e:Observation,f:Observation) -> bool {
    e.actor!=f.actor && (slot(e.action).is_none() || slot(e.action)!=slot(f.action))
}
pub(crate) proof fn swap<S>(m:Program<S>,x:State<S>,e:Observation,f:Observation)
    requires plays(m,x,seq![e,f]),independent(e,f),
    ensures plays(m,x,seq![f,e]),after(m,x,seq![e,f])==after(m,x,seq![f,e]),
{
    let a=e.action;let b=f.action;let y=read::next(m,x,a);let z=read::next(m,x,b);
    assert(seq![e,f].drop_first() =~= seq![f]);assert(seq![f,e].drop_first() =~= seq![e]);
    reveal_with_fuel(plays,3);reveal_with_fuel(after,3);
    if let Some(id)=slot(b) {assert(x.cfg.net.pending.get(id)==y.cfg.net.pending.get(id));}
    if let Process::At(r)=f.actor {assert(local_input(x.cfg.net,a,r).is_none());}
    assert(process_step(x.cfg.net,b)==f);assert(read::service_step(m)(x,b,z));
    if let Some(id)=slot(a) {assert(x.cfg.net.pending.get(id)==z.cfg.net.pending.get(id));}
    if let Process::At(r)=e.actor {assert(local_input(x.cfg.net,b,r).is_none());}
    assert(process_step(z.cfg.net,a)==e);
    let u=read::next(m,y,b);let v=read::next(m,z,a);
    assert(u.cfg.private =~= v.cfg.private);assert(u.cfg.net.locals =~= v.cfg.net.locals);
    assert(u.cfg.net.pending =~= v.cfg.net.pending);assert(u.reserved =~= v.reserved);
}

pub proof fn concat<S>(m:Program<S>,x:State<S>,t:Tape,u:Tape)
    ensures plays(m,x,t+u)==(plays(m,x,t) && plays(m,after(m,x,t),u)),
        after(m,x,t+u)==after(m,after(m,x,t),u),
    decreases t.len(),
{
    if t.len()==0 {assert(t+u =~= u);}
    else {assert((t+u).drop_first() =~= t.drop_first()+u);concat(m,read::next(m,x,t[0].action),t.drop_first(),u);}
}
proof fn cross<S>(m:Program<S>,x:State<S>,e:Observation,t:Tape)
    requires plays(m,x,seq![e]+t),forall|j:int| 0<=j<t.len() ==> independent(e,#[trigger] t[j]),
    ensures plays(m,x,t+seq![e]),after(m,x,t+seq![e])==after(m,x,seq![e]+t),
    decreases t.len(),
{
    if t.len()==0 {assert(t+seq![e] =~= seq![e]+t);} else {
        let f=t[0];let u=t.drop_first();let y=read::next(m,x,f.action);
        assert(seq![e]+t =~= seq![e,f]+u);concat(m,x,seq![e,f],u);
        assert(independent(e,f));swap(m,x,e,f);concat(m,x,seq![f,e],u);
        assert((seq![f,e]+u).drop_first() =~= seq![e]+u);
        assert forall|j:int| 0<=j<u.len() implies independent(e,#[trigger] u[j]) by {assert(u[j]==t[j+1]);}
        cross(m,y,e,u);assert((t+seq![e]).drop_first() =~= u+seq![e]);
    }
}

pub open spec fn pick(t:Tape,p:Process,keep:bool) -> Tape
    decreases t.len(),
{
    if t.len()==0 {Seq::empty()} else {
        let rest=pick(t.drop_first(),p,keep);
        if (t[0].actor==p)==keep {seq![t[0]]+rest} else {rest}
    }
}
pub proof fn picked(t:Tape,p:Process,keep:bool,j:int)
    requires 0<=j<pick(t,p,keep).len(),
    ensures ({let e=pick(t,p,keep)[j];(e.actor==p)==keep && t.contains(e)}),
    decreases t.len(),
{
    let skip=(t[0].actor==p)!=keep;
    if skip || j>0 {
        let k=if skip {j} else {j-1};let u=t.drop_first();picked(u,p,keep,k);
        let e=pick(t,p,keep)[j];assert(u.contains(e));let i=choose|i:int| 0<=i<u.len() && u[i]==e;
        assert(t[i+1]==e);
    } else {assert(t[0]==pick(t,p,keep)[j]);}
}
pub open spec fn reorderable(t:Tape,p:Process,front:bool) -> bool {
    forall|i:int,j:int| 0<=i<j<t.len() && ((#[trigger] t[i]).actor==p)!=front && ((#[trigger] t[j]).actor==p)==front
        ==> independent(t[i],t[j])
}
pub proof fn factor_group<S>(m:Program<S>,x:State<S>,t:Tape,p:Process,front:bool)
    requires plays(m,x,t),reorderable(t,p,front),
    ensures ({let ordered=pick(t,p,front)+pick(t,p,!front);plays(m,x,ordered) && after(m,x,ordered)==after(m,x,t)}),
    decreases t.len(),
{
    if t.len()==0 {assert(pick(t,p,front)+pick(t,p,!front) =~= t);}
    else {
        let e=t[0];let u=t.drop_first();let y=read::next(m,x,e.action);
        assert forall|i:int,j:int| 0<=i<j<u.len() && ((#[trigger] u[i]).actor==p)!=front && ((#[trigger] u[j]).actor==p)==front
            implies independent(u[i],u[j]) by {assert(u[i]==t[i+1] && u[j]==t[j+1]);}
        factor_group(m,y,u,p,front);
        let v=pick(u,p,front);let w=pick(u,p,!front);let end=pick(t,p,front)+pick(t,p,!front);
        let old=seq![e]+(v+w);assert(old.drop_first() =~= v+w);assert(plays(m,x,old));
        if (e.actor==p)==front {assert(end =~= old);} else {
            assert(old =~= (seq![e]+v)+w);concat(m,x,seq![e]+v,w);
            assert forall|j:int| 0<=j<v.len() implies independent(e,#[trigger] v[j]) by {
                picked(u,p,front,j);assert(u.contains(v[j]) && (v[j].actor==p)==front);
                let h=choose|h:int| 0<=h<u.len() && u[h]==v[j];assert(t[h+1]==v[j]);
            }
            cross(m,x,e,v);concat(m,x,v+seq![e],w);assert(end =~= (v+seq![e])+w);
        }
    }
}

pub open spec fn movable(t:Tape,p:Process) -> bool {reorderable(t,p,true)}
pub proof fn factor<S>(m:Program<S>,x:State<S>,t:Tape,p:Process)
    requires plays(m,x,t),movable(t,p),
    ensures ({let ordered=pick(t,p,true)+pick(t,p,false);plays(m,x,ordered) && after(m,x,ordered)==after(m,x,t)}),
{
    factor_group(m,x,t,p,true);
}
}
