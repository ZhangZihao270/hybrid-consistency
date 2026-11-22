// Specialize the reached-reference argument to a native service of the
// opposite sole majority. Identify the actual wire input to a guard that
// differs between the all-live target and its own masked reference.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::coupled_sources as sources;
use crate::first_assembly::{self as asm,Lanes,Service};
use crate::first_causality as cause;
use crate::first_mailbox as mail;
use crate::first_schedule::reference;
use crate::first_splice::{self as tape,Tape};
use crate::guarded_comparison::{self as cmp,prepare,fired};
use crate::hybrid_fork::{self as names,Issuer};
use crate::hybrid_majority as majority;
use crate::hybrid_transparency as trans;
use crate::independent_preparations as prep;
use crate::independent_read::{self as read,State};
use crate::mailbox_preparation as mb;
use crate::quorum_projection as proj;
use crate::quorum_schedules as qs;
use crate::read_call::{Program,Event};
use crate::read_nonblocking as nb;
use crate::reference_resume as resume;
use crate::sr1_contract as rpc;
use crate::sr1_majorities::missing;

verus! {

// Order-preserving positions in the actual proposal stream. Skipping a
// rejected offer never creates a new send or changes a send's payload.
spec fn indices(s:Seq<Event>,u:Seq<Event>,f:Seq<int>) -> bool {
    f.len()==s.len()
        && (forall|i:int| 0<=i<s.len() ==> 0<=#[trigger] f[i]<u.len() && s[i]==u[f[i]])
        && (forall|i:int,j:int| 0<=i<j<s.len() ==> #[trigger] f[i]<#[trigger] f[j])
}

proof fn shift_indices(s:Seq<Event>,u:Seq<Event>,f:Seq<int>,a:Event,keep:bool) -> (g:Seq<int>)
    requires indices(s,u,f),
    ensures indices(if keep {seq![a]+s} else {s},seq![a]+u,g),
{
    let g=f.map_values(|i:int|i+1);let r=if keep {seq![0int]+g} else {g};
    let v=if keep {seq![a]+s} else {s};let w=seq![a]+u;
    assert forall|i:int| 0<=i<v.len() implies 0<=#[trigger] r[i]<w.len() && v[i]==w[r[i]] by {
        if keep && i>0 {assert(r[i]==f[i-1]+1 && v[i]==s[i-1] && w[r[i]]==u[f[i-1]]);}
        else if !keep {assert(r[i]==f[i]+1 && w[r[i]]==u[f[i]]);}
    }
    assert forall|i:int,j:int| 0<=i<j<v.len() implies #[trigger] r[i]<#[trigger] r[j] by {
        if keep {assert(r[j]==f[j-1]+1);if i>0 {assert(r[i]==f[i-1]+1 && f[i-1]<f[j-1]);}}
        else {assert(r[i]==f[i]+1 && r[j]==f[j]+1 && f[i]<f[j]);}
    }
    r
}

proof fn picked_indices(t:Tape) -> (f:Seq<int>)
    ensures indices(asm::actions(tape::pick(t,Process::FirstClient,false)),asm::actions(t),f),
    decreases t.len(),
{
    if t.len()==0 {Seq::empty()} else {
        let tail=t.drop_first();let h=picked_indices(tail);let e=t[0];let keep=e.actor!=Process::FirstClient;
        let u=tape::pick(tail,Process::FirstClient,false);let v=tape::pick(t,Process::FirstClient,false);
        let f=shift_indices(asm::actions(u),asm::actions(tail),h,e.action,keep);
        assert(asm::actions(t) =~= seq![e.action]+asm::actions(tail));
        if keep {assert(asm::actions(v) =~= seq![e.action]+asm::actions(u));} f
    }
}

proof fn fired_indices<S>(m:Program<S>,y:State<S>,s:Seq<Event>) -> (f:Seq<int>)
    ensures indices(asm::actions(fired(m,prepare(),y,s)),s,f),
    decreases s.len(),
{
    if s.len()==0 {Seq::empty()} else {
        let a=s[0];let g=prepare();let tail=s.drop_first();let z=cmp::attempt(m,g,y,a);
        let h=fired_indices(m,z,tail);let v=fired(m,g,z,tail);let keep=cmp::ready(m,g,y,a);
        let f=shift_indices(asm::actions(v),tail,h,a,keep);assert(s =~= seq![a]+tail);
        if keep {assert(asm::actions(fired(m,g,y,s)) =~= seq![a]+asm::actions(v));} f
    }
}

proof fn inherit_names(s:Seq<Event>,u:Seq<Event>,who:Issuer,f:Seq<int>)
    requires indices(s,u,f),proj::fresh_script(who,Set::empty(),u),
    ensures proj::fresh_script(who,Set::empty(),s),
{
    assert forall|i:int| 0<=i<s.len() implies proj::named(who,#[trigger] s[i]) by {assert(s[i]==u[f[i]]);}
    assert forall|i:int,j:int| 0<=i<j<s.len() && (#[trigger] s[i]) is Send && (#[trigger] s[j]) is Send
        implies s[i]->Send_0!=s[j]->Send_0 by {assert(s[i]==u[f[i]] && s[j]==u[f[j]] && f[i]<f[j]);}
}

pub open spec fn copied<S>(m:Program<S>,l:Lanes,d:Fork,p:Service<S>) -> Tape {
    fired(m,prepare(),build::root(m,l,d),asm::actions(sources::replicas(p)))
}

// Both sends are earlier than their delivery. Same identifier, sender,
// recipient and entire envelope in both real preparations; R3's observed
// local cell is nevertheless different in the two real callbacks.
pub open spec fn same_contact(b:Fork,d:Fork,s:Tape,t:Tape,j:int,k:int,i:int,h:int) -> bool {
    0<=k<j<t.len() && 0<=h<i<s.len() && t[j].action is Deliver && t[j].incoming.is_some()
        && ({
            let id=t[j].action->Deliver_0;let q=t[j].incoming.unwrap();
            t[j].actor==at(Replica::R3) && s[i].actor==at(Replica::R3) && q.from==at(crate::origin(b.branch))
                && q.to==at(Replica::R3) && q.path!=Path::Weak && t[k].action==Action::Send(id,q)
                && s[h].action==t[k].action && s[i].action==t[j].action && s[i].incoming==Some(q)
                && s[i].own_local==Some(first_value(b)) && t[j].own_local==Some(first_value(d))
        })
}

proof fn earlier_send<S>(m:Program<S>,y:State<S>,t:Tape,j:int) -> (k:nat)
    requires mb::ordinary(m,y,t),0<=j<t.len(),t[j].action is Deliver,t[j].incoming.is_some(),
        !y.cfg.net.pending.contains_key(t[j].action->Deliver_0),
    ensures k<j,t[k as int].action==Action::Send(t[j].action->Deliver_0,t[j].incoming.unwrap()),
{
    cmp::prepared_tape(m,y,t);cmp::physical_steps(m,prepare(),y,t);
    let v=cmp::path(m,y,t);let id=t[j].action->Deliver_0;let q=t[j].incoming.unwrap();
    assert forall|i:int| 0<=i<t.len() implies mail::active_step(m)(v.states[i],#[trigger] v.actions[i],v.states[i+1]) by {
        assert(read::service_step(m)(v.states[i],v.actions[i],v.states[i+1]));assert(prep::ordinary_input(t[i]));
    }
    assert(t[j]==process_step(v.states[j].cfg.net,v.actions[j]) && v.states[j].cfg.net.pending.get(id)==Some(q));
    let k=mail::last_send(m,v,j as nat,id,q);assert(v.actions[k as int]==t[k as int].action);k
}

proof fn copied_contact<S>(m:Program<S>,l:Lanes,b:Fork,d:Fork,p:Service<S>,who:Issuer,f:Seq<int>,j:int)
    requires b.branch!=d.branch,cause::returning(m,b,p),names::native(p,who),prep::ordinary_source(p),
        indices(asm::actions(copied(m,l,d,p)),asm::actions(sources::replicas(p)),f),0<=j<copied(m,l,d,p).len(),
        ({let t=copied(m,l,d,p);let y=build::root(m,l,d);
          proj::changes_on_foreign_input(m,d,who,tape::after(m,y,t.take(j)),t[j].action)}),
    ensures exists|k:int,i:int,h:int| #[trigger] same_contact(b,d,sources::replicas(p),copied(m,l,d,p),j,k,i,h),
{
    let y=build::root(m,l,d);let s=sources::replicas(p);let t=copied(m,l,d,p);let g=prepare();let full=tape::record(p,0);
    mb::native_proposals(m,y,asm::actions(s));cmp::firing_is_native(m,g,y,asm::actions(s));cmp::physical_steps(m,g,y,t);
    let z=tape::after(m,y,t.take(j));let actual=cmp::path(m,y,t);
    assert(actual.actions[j]==t[j].action && actual.states[j]==z);assert(t[j]==process_step(z.cfg.net,actual.actions[j]));
    let id=t[j].action->Deliver_0;let q=t[j].incoming.unwrap();assert(id>5 && !y.cfg.net.pending.contains_key(id));
    let k=earlier_send(m,y,t,j) as int;let h=f[k];let i=f[j];
    assert(k<j && h<i && s[h].action==Action::Send(id,q) && s[i].action==Action::<Wire>::Deliver(id));
    let C=Process::FirstClient;tape::picked(full,C,false,i);tape::picked(full,C,false,h);
    let a=choose|a:int| 0<=a<full.len() && full[a]==s[i];
    let v=choose|v:int| 0<=v<full.len() && full[v]==s[h];
    assert(p.actions[a]==Action::<Wire>::Deliver(id) && p.actions[v]==Action::Send(id,q));
    let x=p.states[a];assert(mail::active_step(m)(x,p.actions[a],p.states[a+1]));
    let q0=x.cfg.net.pending[id];assert(x.cfg.net.pending.get(id)==Some(q0) && !p.states[0].cfg.net.pending.contains_key(id));
    let u=mail::last_send(m,p,a as nat,id,q0) as int;
    if u!=v {assert(p.actions[u] is Send && p.actions[v] is Send);if u<v {assert(p.actions[u]->Send_0!=p.actions[v]->Send_0);} else {assert(p.actions[v]->Send_0!=p.actions[u]->Send_0);}}
    assert(q==q0 && s[i].incoming==Some(q));cause::prefix_mask(m,p,a as nat);
    assert(live(x.cfg.net,q.to) && q.to!=at(missing(b)) && q.to!=at(missing(d)));
    assert(missing(b)!=missing(d) && q.to==at(Replica::R3));
    prep::source_cells(m,b,p);cause::stable_value(m,p,b,a as nat,Replica::R3);
    let u=t.take(j);assert(u+t.skip(j) =~= t);tape::concat(m,y,u,t.skip(j));
    assert forall|n:int| 0<=n<u.len() implies crate::coupled_traffic::preparation_input(#[trigger] u[n]) by {
        assert(u[n]==t[n] && prep::ordinary_input(t[n]));
    }
    prep::ordinary_cells(m,y,u);assert((z.cfg.net.locals)(Replica::R3)==first_value(d));
    assert(same_contact(b,d,s,t,j,k,i,h));
}

pub open spec fn contacts<S>(m:Program<S>,l:Lanes,b:Fork,d:Fork,who:Issuer,p:Service<S>) -> bool {
    let s=sources::replicas(p);let t=copied(m,l,d,p);let y=build::root(m,l,d);
    forall|j:int| 0<=j<t.len() && #[trigger] proj::changes_on_foreign_input(m,d,who,tape::after(m,y,t.take(j)),t[j].action)
        ==> exists|k:int,i:int,h:int| #[trigger] same_contact(b,d,s,t,j,k,i,h)
}

// Keep the receipt before the guard that uses the affected state, even
// if several different peer packets or several different suffixes exist.
pub open spec fn prior_contact<S>(m:Program<S>,l:Lanes,b:Fork,d:Fork,who:Issuer,p:Service<S>,limit:int) -> bool {
    let t=copied(m,l,d,p);let y=build::root(m,l,d);let s=sources::replicas(p);
    exists|j:int,k:int,i:int,h:int| j<limit && #[trigger] same_contact(b,d,s,t,j,k,i,h)
        && proj::changes_on_foreign_input(m,d,who,tape::after(m,y,t.take(j)),t[j].action)
}

proof fn locate_actor<S>(m:Program<S>,l:Lanes,b:Fork,d:Fork,p:Service<S>,who:Issuer,limit:int,actor:Process)
    requires contacts(m,l,b,d,who,p),0<=limit<=copied(m,l,d,p).len(), ({
        let t=copied(m,l,d,p);proj::affected(m,d,who,build::root(m,l,d),t.take(limit)).contains(actor)
    }),
    ensures actor==at(Replica::R3),prior_contact(m,l,b,d,who,p,limit),
{
    let t=copied(m,l,d,p);let v=t.take(limit);let y=build::root(m,l,d);
    let j=choose|j:int| 0<=j<v.len() && (#[trigger] v[j]).actor==actor && proj::changes_on_foreign_input(m,d,who,tape::after(m,y,v.take(j)),v[j].action);
    assert(v[j]==t[j] && v.take(j) =~= t.take(j));assert(proj::changes_on_foreign_input(m,d,who,tape::after(m,y,t.take(j)),t[j].action));
    let s=sources::replicas(p);let (k,i,h)=choose|k:int,i:int,h:int| #[trigger] same_contact(b,d,s,t,j,k,i,h);
    assert(j<limit && same_contact(b,d,s,t,j,k,i,h));
}

pub open spec fn r3_obstruction<S>(m:Program<S>,l:Lanes,b:Fork,d:Fork,p:Service<S>,who:Issuer,audit:trans::PacketAudit) -> bool {
    let t=copied(m,l,d,p);let x=reference(m,d,5);let y=build::root(m,l,d);
    let z=resume::projected_cut(m,d,who,t);let r=tape::after(m,y,t);
    (exists|k:int| #[trigger] proj::prefix_refusal(m,d,who,x,y,t,k) && t[k].actor==at(Replica::R3)
        && prior_contact(m,l,b,d,who,p,k))
    || (tape::plays(m,x,proj::projection(d,who,t)) && (
        (exists|v:Service<S>| #[trigger] resume::outside_at(m,d,audit,z,v))
        || (prior_contact(m,l,b,d,who,p,t.len() as int) && (exists|v:Service<S>| #[trigger] resume::ordinary_return(m,z,v))
            && forall|v:Service<S>| #[trigger] resume::ordinary_return(m,z,v) ==> {
                let w=resume::grouped(v);exists|k:int| #[trigger] proj::suffix_refusal(m,z,r,w,k)
                    && k<sources::replicas(v).len() && w[k].actor==at(Replica::R3)
            })))
}

proof fn explain_obstruction<S>(m:Program<S>,l:Lanes,b:Fork,d:Fork,p:Service<S>,who:Issuer,audit:trans::PacketAudit)
    requires contacts(m,l,b,d,who,p),resume::obstruction(m,l,d,who,audit,copied(m,l,d,p)),
    ensures r3_obstruction(m,l,b,d,p,who,audit),
{
    let t=copied(m,l,d,p);let x=reference(m,d,5);let y=build::root(m,l,d);let z=resume::projected_cut(m,d,who,t);
    let r=tape::after(m,y,t);let changed=proj::affected(m,d,who,y,t);
    assert(t.take(t.len() as int) =~= t);
    if resume::prefix_block(m,l,d,who,t) {
        let k=choose|k:int| #[trigger] proj::prefix_refusal(m,d,who,x,y,t,k) && proj::affected(m,d,who,y,t.take(k)).contains(t[k].actor);
        locate_actor(m,l,b,d,p,who,k,t[k].actor);
    } else if resume::all_blocked(m,z,r,changed) {
        assert forall|v:Service<S>| #[trigger] resume::ordinary_return(m,z,v) implies ({
            let w=resume::grouped(v);prior_contact(m,l,b,d,who,p,t.len() as int) && exists|k:int| #[trigger] proj::suffix_refusal(m,z,r,w,k)
                && k<sources::replicas(v).len() && w[k].actor==at(Replica::R3)
        }) by {
            let w=resume::grouped(v);assert(resume::blocked_service(m,z,r,v,changed));
            let k=choose|k:int| #[trigger] proj::suffix_refusal(m,z,r,w,k) && k<sources::replicas(v).len() && changed.contains(w[k].actor);
            locate_actor(m,l,b,d,p,who,t.len() as int,w[k].actor);
        }
        let v=choose|v:Service<S>| #[trigger] resume::ordinary_return(m,z,v);assert(prior_contact(m,l,b,d,who,p,t.len() as int));
    }
}

// The source actually returns through its solicited reporters. The target
// runs just the accepted portion of those proposals. No unselected sender
// is added to make this prefix work.
pub proof fn registered_collection_or_contact<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    b:Fork,d:Fork,p:Service<S>,who:Issuer,src:nb::Region<State<S>>,src_used:rpc::Ledger<S>,dst:nb::Region<State<S>>,dst_used:rpc::Ledger<S>,
    run:crate::fair_read::Runnable,audit:trans::PacketAudit)
    requires b.notice==n,d.notice==n,b.branch!=d.branch,names::proper(l,who),mb::setup(m,res,l,b),mb::setup(m,res,l,d),
        cause::returning(m,b,p),prep::ordinary_source(p),majority::sampling(m,first,res,reference(m,b,0)),
        rpc::registered(m,b,src,who,src_used),rpc::registered(m,d,dst,who,dst_used),
        majority::read_a(m,first,res,reference(m,d,0),run),trans::no_first_wait(m,d,audit),
        ({let t=copied(m,l,d,p);tape::plays(m,reference(m,d,5),proj::projection(d,who,t))
            && !(exists|v:Service<S>| #[trigger] resume::ordinary_return(m,resume::projected_cut(m,d,who,t),v))
            ==> mail::fair_opportunity(m,run,resume::projected_cut(m,d,who,t))}),
    ensures ({
        let x=build::root(m,l,b);let y=build::root(m,l,d);let s=sources::replicas(p);let t=copied(m,l,d,p);
        let c=calls::caller(p);
        prep::arm(m,first,res,l,b,s,c) && qs::collected(m,first,b,x,asm::actions(s),c) && mb::ordinary(m,y,t)
            && contacts(m,l,b,d,who,p)
            && (qs::can_join(m,first,b,d,x,y) || r3_obstruction(m,l,b,d,p,who,audit))
    }),
{
    let x=build::root(m,l,b);let y=build::root(m,l,d);let s=sources::replicas(p);let t=copied(m,l,d,p);let full=tape::record(p,0);
    let c=calls::caller(p);let script=asm::actions(s);
    majority::first_quorum_rule(m,first,res,b);rpc::solicited_majority_route(m,b,p,src);rpc::allocator_gives_native(m,b,p,src,who,src_used);
    prep::lift_majority_arm(m,first,res,l,b,who,p);mb::arm_has_mailbox(m,first,res,l,b,crate::fork_alternatives::Tapes{replicas:s,caller:c});
    mb::propose_native(m,x,s);mb::native_proposals(m,y,script);
    assert(asm::actions(full) =~= p.actions);
    let g=picked_indices(full);let f=fired_indices(m,y,script);
    assert(proj::fresh_script(who,Set::empty(),p.actions));inherit_names(script,p.actions,who,g);inherit_names(asm::actions(t),script,who,f);
    assert forall|j:int| 0<=j<t.len() && #[trigger] proj::changes_on_foreign_input(m,d,who,tape::after(m,y,t.take(j)),t[j].action)
        implies exists|k:int,i:int,h:int| #[trigger] same_contact(b,d,s,t,j,k,i,h) by {copied_contact(m,l,b,d,p,who,f,j);}
    resume::resume_reference_or_obstruction(m,first,res,l,d,who,dst_used,dst,run,audit,t);
    if qs::viable(m,first,d,tape::after(m,y,t)) {
        let v=qs::finish_other_quorum(m,first,b,d,x,y,script,c);assert(qs::joint(m,first,b,d,x,y,script+v));
    } else {explain_obstruction(m,l,b,d,p,who,audit);}
}

}
