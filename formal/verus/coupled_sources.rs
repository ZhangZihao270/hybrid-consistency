// Construct the candidate replica preparation from two actual one-crash
// services. Alpha's replica service can run before C1 takes any replies;
// the previously absent R1 can then attempt its own beta history.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::*};
use crate::coupled_construction as build;
use crate::coupled_traffic as traffic;
use crate::first_assembly::{self as asm,Lanes,Service};
use crate::first_causality as cause;
use crate::first_mailbox as mail;
use crate::first_schedule::reference;
use crate::first_splice::{self as tape,Tape,Observation};
use crate::hybrid_fork as fork;
use crate::independent_read::{self as read,State};
use crate::read_call::{Event,Program};
use crate::sr1_contract as rpc;
use crate::sr1_majorities as maj;

use crate::coupled_reads as calls;
use crate::fair_read as fair;
use crate::first_dispatch as dispatch;
use crate::first_schedule as first;
use crate::hybrid_majority as model;
use crate::hybrid_transparency as trans;
use crate::read_issue as issue;
use crate::read_nonblocking as nb;
use crate::sr1_ordinary as ordinary;

verus! {

pub open spec fn replicas<S>(p:Service<S>) -> Tape {tape::pick(tape::record(p,0),Process::FirstClient,false)}
spec fn source_plan<S>(a:Service<S>,b:Service<S>) -> Tape {
    replicas(a)+tape::pick(tape::record(b,0),at(Replica::R1),true)
}
pub(crate) proof fn lift_available_sites<S>(m:Program<S>,l:Lanes,b:Fork,p:Service<S>,who:fork::Issuer)
    requires fork::proper(l,who),cause::returning(m,b,p),fork::native(p,who),
    ensures tape::plays(m,build::root(m,l,b),replicas(p)),
        tape::same_slots(tape::after(m,reference(m,b,5),replicas(p)),build::prepared(m,l,b,replicas(p)),ISet::full()),
        tape::same_locals(build::root(m,l,b),build::prepared(m,l,b,replicas(p)),asm::site(maj::missing(b))),
{
    let x=reference(m,b,5);let y=build::root(m,l,b);let t=tape::record(p,0);let part=replicas(p);
    let r=maj::missing(b);let ps=ISet::new(|v:Process|v is At && v!=at(r));let ids=ISet::<nat>::full();
    traffic::move_caller_last(m,b,p,who);
    assert(tape::supports(part,ps,ids) && tape::allocates(y,part)) by {
        assert forall|i:int| 0<=i<part.len() implies {let e=#[trigger] part[i];ps.contains(e.actor)
            && (tape::slot(e.action).is_some() ==> ids.contains(tape::slot(e.action).unwrap())) && read::names_sender(y,e.action)} by {
            tape::picked(t,Process::FirstClient,false,i);
            let j=choose|j:int| 0<=j<t.len() && t[j]==part[i];let a=p.actions[j];let s=p.states[j];
            cause::prefix_mask(m,p,j as nat);assert(mail::active_step(m)(s,a,p.states[j+1]));assert(live(s.cfg.net,t[j].actor));
            if let Action::Send(id,q)=a {assert(q.from==at(who(id)));if y.owners.contains_key(id) {assert(l.contains_key(id) && l[id]==who(id));}}
        }
    }
    assert(tape::same_locals(x,y,ps)) by {
        assert forall|v:Process| ps.contains(v) implies #[trigger] (x.cfg.private)(v)==(y.cfg.private)(v) by {
            maj::local_at(m,b,v,5);assert(maj::count(b,5)==5);
        }
    }
    assert(x.cfg.net.pending =~= y.cfg.net.pending);
    tape::replay(m,x,y,part,ps,ids);tape::frame(m,y,part,ps,ids);
    assert(ps.complement().contains(at(r)));
}

// Reconstruct the input at the target from its own queue. Only the action
// (a slot for a receipt) comes from the missing site's source schedule.
pub open spec fn actual_inputs<S>(m:Program<S>,z:State<S>,site:Tape) -> Tape
    decreases site.len(),
{
    if site.len()==0 {Seq::empty()} else {
        let a=site[0].action;
        seq![process_step(z.cfg.net,a)]+actual_inputs(m,read::next(m,z,a),site.drop_first())
    }
}
pub open spec fn candidate<S>(m:Program<S>,l:Lanes,n:Notice,a:Service<S>,b:Service<S>) -> Tape {
    let z=build::prepared(m,l,alpha(n),replicas(a));
    replicas(a)+actual_inputs(m,z,tape::pick(tape::record(b,0),at(Replica::R1),true))
}
pub open spec fn bad_slot<S>(z:State<S>,e:Observation,f:traffic::Encoding) -> bool {
    match e.action {
        Action::Deliver(i)=>e.incoming.is_some() && traffic::packet(f,z.cfg.net.pending.get(i))!=e.incoming,
        Action::Send(i,_)=>z.cfg.net.pending.contains_key(i) || z.reserved.contains(i) || !read::names_sender(z,e.action),
        _=>false,
    }
}
pub open spec fn site_prefix(t:Tape,r:Replica,k:nat) -> Tape {tape::pick(t.take(k as int),at(r),true)}
pub open spec fn rejected_at_site<S>(m:Program<S>,f:traffic::Encoding,z:State<S>,e:Observation) -> bool {
    let h=process_step(z.cfg.net,e.action);
    bad_slot(z,e,f) || (h.actor==e.actor && enabled(z.cfg.net,h.action) && traffic::observation(f,h,2)==e
        && !(m.accept)((z.cfg.private)(e.actor),h))
}
proof fn add_site<S>(m:Program<S>,f:traffic::Encoding,r:Replica,x:State<S>,z:State<S>,t:Tape) -> (k:nat)
    requires r!=Replica::R3,traffic::recipient_use(m,f),tape::plays(m,x,t),live(z.cfg.net,at(r)),
        (x.cfg.net.locals)(r)==(z.cfg.net.locals)(r),(x.cfg.private)(at(r))==(z.cfg.private)(at(r)),
    ensures k<=t.len(),({let src=site_prefix(t,r,k);let out=actual_inputs(m,z,src);
        tape::plays(m,z,out) && traffic::translated(f,out,2)==src &&
        (k<t.len() ==> {let e=t[k as int];let y=traffic::at_cut(m,x,t,k);let u=tape::after(m,z,out);
            e.actor==at(r) && (y.cfg.private)(at(r))==(u.cfg.private)(at(r))
                && (m.accept)((u.cfg.private)(at(r)),e) && rejected_at_site(m,f,u,e)})}),
    decreases t.len(),
{
    if t.len()==0 {assert(t.take(0) =~= t);assert(traffic::translated(f,Seq::empty(),2) =~= t);0} else {
        let e=t[0];let a=e.action;let y=read::next(m,x,a);let tail=t.drop_first();let retained=e.actor==at(r);
        let h=process_step(z.cfg.net,a);let u=if retained {read::next(m,z,a)} else {z};
        if retained && !bad_slot(z,e,f) {
            assert(traffic::observation(f,h,2)==e);assert(enabled(z.cfg.net,a));
        }
        if retained && rejected_at_site(m,f,z,e) {
            assert(t.take(0) =~= Seq::<Observation>::empty());assert(traffic::translated(f,Seq::empty(),2) =~= t.take(0));0
        } else {
            if retained {
                assert((m.accept)((z.cfg.private)(at(r)),h));
                assert(read::service_step(m)(z,a,u));assert(local_input(z.cfg.net,a,r)==local_input(x.cfg.net,a,r));
                if a is Deliver {assert(traffic::observation(f,h,0)==e);} else {assert(h==e);}
                assert((u.cfg.private)(at(r))==(y.cfg.private)(at(r)));
            } else {assert(local_input(x.cfg.net,a,r).is_none());}
            let j=add_site(m,f,r,y,u,tail);let k=j+1;
            assert(t.take(k as int)[0]==e && t.take(k as int).drop_first() =~= tail.take(j as int));
            let src=site_prefix(t,r,k);let out=actual_inputs(m,z,src);
            let rest=site_prefix(tail,r,j);let extra=actual_inputs(m,u,rest);
            if retained {
                assert(src =~= seq![e]+rest);assert(src.drop_first() =~= rest);
                assert(out =~= seq![h]+extra);assert(out.drop_first() =~= extra);
                assert(traffic::translated(f,out,2) =~= seq![e]+traffic::translated(f,extra,2));
            }
            if k<t.len() {assert(t[k as int]==tail[j as int]);}
            k
        }
    }
}

proof fn local_positions(t:Tape,r:Replica,i:nat,j:nat) -> (k:(nat,nat))
    requires i<j<tape::pick(t,at(r),true).len(),
    ensures k.0<k.1<t.len(),t[k.0 as int]==tape::pick(t,at(r),true)[i as int],
        t[k.1 as int]==tape::pick(t,at(r),true)[j as int],
    decreases t.len(),
{
    let v=t.drop_first();let u=tape::pick(v,at(r),true);
    if t[0].actor!=at(r) {let (h,k)=local_positions(v,r,i,j);(h+1,k+1)}
    else if i>0 {
        let (h,k)=local_positions(v,r,(i-1) as nat,(j-1) as nat);(h+1,k+1)
    } else {
        tape::picked(v,at(r),true,j as int-1);
        let k=choose|k:int| 0<=k<v.len() && v[k]==u[j as int-1];(0,(k+1) as nat)
    }
}
proof fn all_respondents<S>(a:Service<S>,b:Service<S>,n:Notice)
    requires cause::source_shape(tape::record(a,0),alpha(n),rpc::replies()),cause::source_shape(tape::record(b,0),beta(n),rpc::replies()),
        forall|i:int| 0<=i<replicas(a).len() ==> (#[trigger] replicas(a)[i]).actor!=at(Replica::R1),
    ensures build::respondents(source_plan(a,b)),
{
    let t=source_plan(a,b);let ta=tape::record(a,0);let tb=tape::record(b,0);let one=at(Replica::R1);
    let extra=tape::pick(tb,one,true);
    assert forall|r:Replica| #[trigger] build::answered(t,r) by {
        let site=at(r);cause::pick_concat(replicas(a),extra,site,true);
        cause::nested(ta,Process::FirstClient,false,site);cause::nested(tb,one,true,site);
        if site==one {
            let pref=tape::pick(replicas(a),site,true);
            if pref.len()>0 {
                tape::picked(replicas(a),site,true,0);
                let k=choose|k:int| 0<=k<replicas(a).len() && replicas(a)[k]==pref[0];assert(replicas(a)[k].actor!=site);
            }
            assert(pref =~= Seq::<Observation>::empty());
        }
        let src=if r==Replica::R1 {tb} else {ta};
        assert(tape::pick(t,site,true) =~= tape::pick(src,site,true));
        assert(cause::exchange(src,r,rpc::replies()));
        let local=tape::pick(t,site,true);let (i,j)=choose|i:int,j:int| 0<=i<j<local.len()
            && cause::intake_at(#[trigger] local[i],r) && cause::answer_at(#[trigger] local[j],r,rpc::replies());
        let (h,k)=local_positions(t,r,i as nat,j as nat);
        assert(cause::intake_at(t[h as int],r) && cause::answer_at(t[k as int],r,rpc::replies()));
    }
}
pub open spec fn missing_site_input<S>(m:Program<S>,l:Lanes,n:Notice,f:traffic::Encoding,a:Service<S>,b:Service<S>) -> bool {
    let z=build::prepared(m,l,alpha(n),replicas(a));let x=reference(m,beta(n),5);let t=tape::record(b,0);
    exists|k:nat| k<t.len() && {let e=#[trigger] t[k as int];let src=site_prefix(t,Replica::R1,k);
        let out=actual_inputs(m,z,src);let u=tape::after(m,z,out);
        e.actor==at(Replica::R1) && tape::plays(m,z,out) && traffic::translated(f,out,2)==src && rejected_at_site(m,f,u,e)
            && (m.accept)((u.cfg.private)(e.actor),e) && (u.cfg.private)(e.actor)==(traffic::at_cut(m,x,t,k).cfg.private)(e.actor)}
}

proof fn sender<S>(m:Program<S>,x:State<S>,t:Tape,i:nat)
    requires tape::plays(m,x,t),i<t.len(),t[i as int].action is Send,
    ensures t[i as int].actor==t[i as int].action->Send_1.from,
    decreases i,
{
    if i>0 {sender(m,read::next(m,x,t[0].action),t.drop_first(),(i-1) as nat);}
}
pub proof fn ordinary_preparation_from_sources<S>(m:Program<S>,n:Notice,f:traffic::Encoding,a:Service<S>,b:Service<S>,who:fork::Issuer,l:Lanes)
    requires traffic::recipient_use(m,f),fork::proper(l,who),cause::returning(m,alpha(n),a),cause::returning(m,beta(n),b),
        fork::wire_route(alpha(n),a,who,rpc::replies()),fork::wire_route(beta(n),b,who,rpc::replies()),
    ensures tape::plays(m,build::root(m,l,alpha(n)),replicas(a)),
        (build::respondents(candidate(m,l,n,a,b)) && tape::plays(m,build::root(m,l,alpha(n)),candidate(m,l,n,a,b)))
            || missing_site_input(m,l,n,f,a,b),
{
    let ra=alpha(n);let rb=beta(n);let p=at(Replica::R1);let src=tape::record(b,0);
    let x=build::root(m,l,ra);let z=build::prepared(m,l,ra,replicas(a));let y=reference(m,rb,5);
    lift_available_sites(m,l,ra,a,who);tape::recorded(m,b,0);maj::local_at(m,rb,p,5);
    assert(maj::count(rb,5)==5);arbitrary_survivor_memory_agrees(n,m,p,5);
    assert(asm::site(Replica::R1).contains(p));assert((x.cfg.private)(p)==(z.cfg.private)(p));
    assert((x.cfg.net.locals)(Replica::R1)==(z.cfg.net.locals)(Replica::R1));
    tape::frame(m,x,replicas(a),ISet::full(),ISet::full());
    let k=add_site(m,f,Replica::R1,y,z,src);
    if k<src.len() {assert(missing_site_input(m,l,n,f,a,b));return;}
    assert(src.take(k as int) =~= src);
    let single=tape::pick(src,p,true);let out=actual_inputs(m,z,single);
    let head=replicas(a);let t=candidate(m,l,n,a,b);
    tape::concat(m,x,head,out);
    let all=tape::record(a,0);
    assert forall|i:int| 0<=i<head.len() implies (#[trigger] head[i]).actor!=p by {
        tape::picked(all,Process::FirstClient,false,i);let j=choose|j:int| 0<=j<all.len() && all[j]==head[i];
        cause::prefix_mask(m,a,j as nat);assert(mail::active_step(m)(a.states[j],a.actions[j],a.states[j+1]));assert(live(a.states[j].cfg.net,all[j].actor));
    }
    all_respondents(a,b,n);let plan=source_plan(a,b);
    assert forall|r:Replica| #[trigger] build::answered(t,r) by {
        assert(build::answered(plan,r));
        let (i,j)=choose|i:int,j:int|0<=i<j<plan.len() && cause::intake_at(#[trigger] plan[i],r) && cause::answer_at(#[trigger] plan[j],r,rpc::replies());
        if i<head.len() {assert(t[i]==plan[i]);} else {
            let h=i-head.len();assert(traffic::observation(f,out[h],2)==single[h]);assert(cause::intake_at(t[i],r));
        }
        if j<head.len() {assert(t[j]==plan[j]);} else {
            let h=j-head.len();assert(traffic::observation(f,out[h],2)==single[h]);
            tape::picked(src,p,true,h);assert(single[h].actor==p);
            sender(m,z,out,h as nat);
            assert(cause::answer_at(t[j],r,rpc::replies()));
        }
    }
}

pub open spec fn source<S>(m:Program<S>,b:Fork,who:fork::Issuer,audit:trans::PacketAudit,p:Service<S>) -> bool {
    ordinary::weak_free_return(m,b,audit,p) && fork::wire_route(b,p,who,rpc::replies())
}
pub(crate) proof fn majority_source<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,who:fork::Issuer,audit:trans::PacketAudit,
    scope:nb::Region<State<S>>,used:rpc::Ledger<S>,run:fair::Runnable) -> (p:Service<S>)
    requires dispatch::initiates(m),dispatch::weak_open(m,b),trans::no_first_wait(m,b,audit),rpc::registered(m,b,scope,who,used),
        model::eventual(m,res,reference(m,b,0),run),mail::fair_opportunity(m,run,reference(m,b,5)),
    ensures source(m,b,who,audit,p),
{
    let p=ordinary::service_with_ordinary_traffic(m,b,res,run,audit);
    ordinary::ordinary_edges(m,b,audit,p);rpc::allocator_gives_native(m,b,p,scope,who,used);rpc::solicited_majority_route(m,b,p,scope);p
}
pub open spec fn outcome<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    f:traffic::Encoding,rel:traffic::Relation<S>,audit:trans::PacketAudit,a:Service<S>,b:Service<S>) -> bool {
    let t=candidate(m,l,n,a,b);let u=traffic::translated(f,t,2);let x=build::root(m,l,alpha(n));let y=build::root(m,l,beta(n));
    missing_site_input(m,l,n,f,a,b)
        || (exists|i:int| 0<=i<t.len() && !traffic::preparation_input(#[trigger] t[i]))
        || (build::sender_refusal(m,l,n,f,t) && !(traffic::sender_control(m,f,rel,|_e:Observation|true,2)
            && rel((x.cfg.private)(at(Replica::R3)),(y.cfg.private)(at(Replica::R3)))))
        || build::input_obstruction(m,alpha(n),audit,build::prepared(m,l,alpha(n),t))
        || build::input_obstruction(m,beta(n),audit,build::prepared(m,l,beta(n),u))
        || exists|ca:Tape,cb:Tape,acts:Seq<Event>| #[trigger] build::completes(m,first,res,l,n,f,t,ca,cb,acts)
}

// A supplies both reference services. Each possible pair is tested; a
// failed choice is evidence only about that candidate. No full preparation,
// matching C2 view, successful return, or cross-run R3 guard is assumed.
pub proof fn registered_majorities_with_encoding<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    f:traffic::Encoding,rel:traffic::Relation<S>,who:fork::Issuer,used:rpc::Ledger<S>,region:spec_fn(Fork)->nb::Region<State<S>>,
    run:fair::Runnable,audit:trans::PacketAudit) -> (w:(Service<S>,Service<S>))
    requires fork::proper(l,who),dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b) && model::read_a(m,first,res,reference(m,b,0),run)
            && mail::fair_opportunity(m,run,reference(m,b,5)) && trans::no_first_wait(m,b,audit)
            && rpc::registered(m,b,region(b),who,used),
        build::keeps_reports(f),traffic::recipient_use(m,f),calls::distinct_weak_names(m),build::second_service(m,first,res,asm::entry(m,l),run,n),
    ensures source(m,alpha(n),who,audit,w.0) && source(m,beta(n),who,audit,w.1),
        forall|a:Service<S>,b:Service<S>| #[trigger] source(m,alpha(n),who,audit,a) && #[trigger] source(m,beta(n),who,audit,b)
            ==> outcome(m,first,res,l,n,f,rel,audit,a,b),
{
    let ra=alpha(n);let rb=beta(n);
    assert(dispatch::weak_open(m,ra) && dispatch::weak_open(m,rb));
    let pa=majority_source(m,res,ra,who,audit,region(ra),used,run);
    let pb=majority_source(m,res,rb,who,audit,region(rb),used,run);
    assert forall|a:Service<S>,b:Service<S>| #[trigger] source(m,ra,who,audit,a) && #[trigger] source(m,rb,who,audit,b)
        implies outcome(m,first,res,l,n,f,rel,audit,a,b) by {
        ordinary::ordinary_edges(m,ra,audit,a);ordinary::ordinary_edges(m,rb,audit,b);
        ordinary_preparation_from_sources(m,n,f,a,b,who,l);
        let t=candidate(m,l,n,a,b);let any=|_e:Observation|true;
        if !missing_site_input(m,l,n,f,a,b) && traffic::fitted(t,any) {
            build::two_reads_with_coupled_traffic(m,first,res,l,n,f,t,any,rel,who,used,region,run,audit);
        }
    }
    (pa,pb)
}

// Try the same ordinary peer messages for any deterministic local program.
// A differing R3 sample goes only to C1. There is no premise on how any
// survivor treats peer metadata and no premise that R3 accepts the replay.
pub proof fn registered_majorities<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,
    rel:traffic::Relation<S>,who:fork::Issuer,used:rpc::Ledger<S>,region:spec_fn(Fork)->nb::Region<State<S>>,
    run:fair::Runnable,audit:trans::PacketAudit) -> (w:(Service<S>,Service<S>))
    requires fork::proper(l,who),dispatch::initiates(m),first::startup(m),issue::can_issue(m,res),
        forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b) && model::read_a(m,first,res,reference(m,b,0),run)
            && mail::fair_opportunity(m,run,reference(m,b,5)) && trans::no_first_wait(m,b,audit)
            && rpc::registered(m,b,region(b),who,used),
        calls::distinct_weak_names(m),build::second_service(m,first,res,asm::entry(m,l),run,n),
    ensures source(m,alpha(n),who,audit,w.0) && source(m,beta(n),who,audit,w.1),
        forall|a:Service<S>,b:Service<S>| #[trigger] source(m,alpha(n),who,audit,a) && #[trigger] source(m,beta(n),who,audit,b)
            ==> outcome(m,first,res,l,n,traffic::sampled_reply(2),rel,audit,a,b),
{
    build::common_peer_inputs(m,2);
    registered_majorities_with_encoding(m,first,res,l,n,traffic::sampled_reply(2),rel,who,used,region,run,audit)
}
}
