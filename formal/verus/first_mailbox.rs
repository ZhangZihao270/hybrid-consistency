// What can make an already submitted read depend on a further wire input?
// The reference can run arbitrary real service at every live process.
use vstd::prelude::*;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::fair_read::{self as fair, Run, Runnable};
use crate::independent_read::{self as read, State};
use crate::promotion_wait::{self as wait, Relation};
use crate::read_call::{Event, Program};
use crate::read_nonblocking as nb;

verus! {

pub struct Inbox<S> { pub local:S, pub packets:Map<nat,Packet<Wire>> }

pub open spec fn for_client(q:Map<nat,Packet<Wire>>) -> Map<nat,Packet<Wire>> {
    q.restrict(q.dom().filter(|i:nat| q[i].to==Process::FirstClient))
}
pub open spec fn inbox<S>(x:State<S>) -> Inbox<S> {
    Inbox{local:(x.cfg.private)(Process::FirstClient),packets:for_client(x.cfg.net.pending)}
}
pub open spec fn event<S>(t:Inbox<S>,a:Event) -> ProcessStep<int,Wire> {
    ProcessStep{actor:Process::FirstClient,action:a,own_local:None,
        incoming:match a {Action::Deliver(i)=>t.packets.get(i),_=>None}}
}
pub open spec fn advance_client<S>(m:Program<S>,t:Inbox<S>,a:Event) -> Inbox<S> {
    Inbox{local:(m.update)(t.local,event(t,a)),packets:match a {
        Action::Deliver(i)=>t.packets.remove(i),_=>t.packets,
    }}
}
// Local clock/input and computation are freely interleavable with the
// actual queued replies. There is no bound on their number or order.
pub open spec fn client_step<S>(m:Program<S>) -> Relation<Inbox<S>,Event> {
    |t,a,u| u==advance_client(m,t,a) && (m.accept)(t.local,event(t,a)) && match a {
        Action::Strong(p)|Action::ClientInput(p,_) => p==Process::FirstClient,
        Action::Deliver(i) => t.packets.contains_key(i) && t.packets[i].to==Process::FirstClient,
        _ => false,
    }
}
pub open spec fn local_done<S>(m:Program<S>) -> nb::Region<Inbox<S>> { |t:Inbox<S>| (m.done)(t.local) }
pub open spec fn posted<S>(m:Program<S>) -> nb::Region<State<S>> {
    |x:State<S>| (m.done)((x.cfg.private)(Process::FirstClient))
}
// The first client remains nonfaulty until its publication. The genuine
// protocol and the queue still guard every transition. Stops after return
// are permitted. C1 has already sent its entire invocation.
pub open spec fn active_step<S>(m:Program<S>) -> Relation<State<S>,Event> {
    |x,a,y| read::service_step(m)(x,a,y) && (a!=Action::StopFirstClient || posted(m)(x))
}
pub open spec fn submitted<S>(x:State<S>) -> bool {
    !x.cfg.net.first_stopped && x.first_requested==x.calls.first &&
        exists|r:crate::Replica,s:crate::Replica| r!=s && x.first_requested.contains(r) && x.first_requested.contains(s)
            && #[trigger] live(x.cfg.net,at(r)) && #[trigger] live(x.cfg.net,at(s))
}
pub open spec fn honest<S>(m:Program<S>,e:Run<S>) -> bool {
    forall|i:nat| #[trigger] (e.action)(i)==Action::<Wire>::StopFirstClient ==> posted(m)((e.state)(i))
}
pub open spec fn fair_opportunity<S>(m:Program<S>,run:Runnable,x:State<S>) -> bool {
    exists|e:Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && honest(m,e)
}
// Scope may be the reachable configurations of this workload. This is the
// positive hybrid progress assumption, separately from existence of a fair run.
pub open spec fn first_availability<S>(m:Program<S>,run:Runnable,scope:nb::Region<State<S>>) -> bool {
    forall|x:State<S>,e:Run<S>| scope(x) && submitted(x) && #[trigger] fair::execution(m,e,x)
        && fair::fair(e,run) && honest(m,e) ==> exists|i:nat| #[trigger] posted(m)((e.state)(i))
}
pub proof fn fair_first_service<S>(m:Program<S>,run:Runnable,scope:nb::Region<State<S>>,x:State<S>)
    requires scope(x),submitted(x),first_availability(m,run,scope),fair_opportunity(m,run,x),
    ensures nb::possible(active_step(m),posted(m),x),
{
    let e=choose|e:Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && honest(m,e);
    let k=choose|i:nat| #[trigger] posted(m)((e.state)(i));
    let p=wait::Path{states:Seq::new(k+1,|j:int|(e.state)(j as nat)),actions:Seq::new(k,|j:int|(e.action)(j as nat))};
    assert forall|j:int| 0<=j<k implies active_step(m)(p.states[j],#[trigger] p.actions[j],p.states[j+1]) by {
        assert(read::service_step(m)((e.state)(j as nat),(e.action)(j as nat),(e.state)(j as nat+1)));
    }
    nb::from_path(active_step(m),posted(m),p,0);
}

// At every cut the target contains the still outstanding, initially issued
// packets. The source may hold any number of new packets too.
pub open spec fn remaining<S>(x:State<S>,ids:Set<nat>) -> Inbox<S> {
    Inbox{local:(x.cfg.private)(Process::FirstClient),packets:for_client(x.cfg.net.pending).restrict(ids)}
}
pub open spec fn can_use_issued<S>(m:Program<S>,ids:Set<nat>,x:State<S>) -> bool {
    nb::possible(client_step(m),local_done(m),remaining(x,ids))
}
pub open spec fn additional_input<S>(ids:Set<nat>) -> Relation<State<S>,Event> {
    |x:State<S>,a,_y| match a {
        Action::Deliver(i)=>!ids.contains(i) && x.cfg.net.pending.contains_key(i)
            && x.cfg.net.pending[i].to==Process::FirstClient,
        _=>false,
    }
}
proof fn project_step<S>(m:Program<S>,ids:Set<nat>,x:State<S>,a:Event,y:State<S>)
    requires active_step(m)(x,a,y),!posted(m)(x),ids.subset_of(x.reserved),!additional_input(ids)(x,a,y),
    ensures remaining(y,ids)==remaining(x,ids) || client_step(m)(remaining(x,ids),a,remaining(y,ids)),
{
    let t=remaining(x,ids);let e=process_step(x.cfg.net,a);let c=Process::FirstClient;
    let u=if e.actor==c {advance_client(m,t,a)} else {t};
    if let Action::Deliver(i)=a {
        if e.actor==c {assert(ids.contains(i) && t.packets.get(i)==Some(x.cfg.net.pending[i]));}
    }
    if let Action::Send(i,packet)=a {assert(!ids.contains(i));}
    assert(u.packets =~= remaining(y,ids).packets);
    if e.actor==c {assert(event(t,a)==e);assert(client_step(m)(t,a,u));}
}
pub open spec fn opens_service<S>(m:Program<S>,ids:Set<nat>,x:State<S>,a:Event,y:State<S>) -> bool {
    additional_input(ids)(x,a,y) && !can_use_issued(m,ids,x) && can_use_issued(m,ids,y)
}
proof fn first_unlock<S>(m:Program<S>,ids:Set<nat>,p:wait::Path<State<S>,Event>,j:nat) -> (k:nat)
    requires p.states.len()==p.actions.len()+1,j<=p.actions.len(),ids.subset_of(p.states[j as int].reserved),
        wait::valid_edges(active_step(m),p),wait::pending_before(posted(m),p),posted(m)(p.states.last()),
        !can_use_issued(m,ids,p.states[j as int]),
    ensures j<=k<p.actions.len(),opens_service(m,ids,p.states[k as int],p.actions[k as int],p.states[k as int+1]),
    decreases p.actions.len()-j,
{
    let x=p.states[j as int];let local=remaining(x,ids);
    if j==p.actions.len() {assert(nb::within(client_step(m),local_done(m),local,0));}
    let a=p.actions[j as int];let y=p.states[j as int+1];assert(active_step(m)(x,a,y));
    if can_use_issued(m,ids,y) {
        if !additional_input(ids)(x,a,y) {
            assert(!posted(m)(x));project_step(m,ids,x,a,y);
            if remaining(y,ids)!=local {nb::predecessor(client_step(m),local_done(m),local,a,remaining(y,ids));}
        }
        j
    } else {first_unlock(m,ids,p,j+1)}
}

// A later receipt matters here only when a real new send is consumed.
// A mandatory send to another process, or an unread copy, does not qualify.
pub open spec fn same_issue<S>(p:wait::Path<State<S>,Event>,i:int,j:int) -> bool {
    let a=p.actions[i];let packet=a->Send_1;let slot=a->Send_0;
    a is Send && p.actions[j]==Action::<Wire>::Deliver(slot) && packet.to==Process::FirstClient
        && p.states[j].cfg.net.pending.get(slot)==Some(packet) && live(p.states[i].cfg.net,packet.from)
        && forall|k:int| i<k<j ==> #[trigger] p.actions[k]!=Action::<Wire>::Deliver(slot)
}
pub open spec fn consumes_new_send<S>(m:Program<S>,p:wait::Path<State<S>,Event>,effect:Relation<State<S>,Event>) -> bool {
    exists|i:int,j:int| 0<=i<j<p.actions.len() && #[trigger] same_issue(p,i,j) && !effect(p.states[j],p.actions[j],p.states[j+1])
        && opens_service(m,inbox(p.states[0]).packets.dom(),p.states[j],p.actions[j],p.states[j+1])
}
pub(crate) proof fn last_send_after<S>(m:Program<S>,p:wait::Path<State<S>,Event>,lo:nat,j:nat,id:nat,packet:Packet<Wire>) -> (i:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(active_step(m),p),lo<=j<=p.actions.len(),
        p.states[j as int].cfg.net.pending.get(id)==Some(packet),p.states[lo as int].cfg.net.pending.get(id)!=Some(packet),
    ensures lo<=i<j,p.actions[i as int]==Action::Send(id,packet),live(p.states[i as int].cfg.net,packet.from),
        forall|k:int| i<k<j ==> #[trigger] p.actions[k]!=Action::<Wire>::Deliver(id),
    decreases j-lo,
{
    let k=(j-1) as nat;let x=p.states[k as int];let a=p.actions[k as int];
    assert(active_step(m)(x,a,p.states[j as int]));
    if a==Action::Send(id,packet) {k} else {last_send_after(m,p,lo,k,id,packet)}
}
pub(crate) proof fn last_send<S>(m:Program<S>,p:wait::Path<State<S>,Event>,j:nat,id:nat,packet:Packet<Wire>) -> (i:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(active_step(m),p),j<=p.actions.len(),
        p.states[j as int].cfg.net.pending.get(id)==Some(packet),p.states[0].cfg.net.pending.get(id)!=Some(packet),
    ensures i<j,p.actions[i as int]==Action::Send(id,packet),live(p.states[i as int].cfg.net,packet.from),
        forall|k:int| i<k<j ==> #[trigger] p.actions[k]!=Action::<Wire>::Deliver(id),
{
    last_send_after(m,p,0,j,id,packet)
}
pub open spec fn needs_further_input<S>(m:Program<S>,x:State<S>,effect:Relation<State<S>,Event>) -> bool {
    let step=active_step(m);let d=posted(m);
    (exists|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(step,d,x,p) && !wait::uses(p,effect))
    && forall|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(step,d,x,p) && !wait::uses(p,effect)
        ==> consumes_new_send(m,p,effect)
}
proof fn new_send_origin<S>(m:Program<S>,p:wait::Path<State<S>,Event>,effect:Relation<State<S>,Event>,j:nat)
    requires p.states.len()==p.actions.len()+1,j<p.actions.len(),wait::valid_edges(active_step(m),p),
        opens_service(m,inbox(p.states[0]).packets.dom(),p.states[j as int],p.actions[j as int],p.states[j as int+1]),
        !wait::uses(p,effect),
    ensures consumes_new_send(m,p,effect),
{
    let a=p.actions;let id=a[j as int]->Deliver_0;let packet=p.states[j as int].cfg.net.pending[id];
    assert(p.states[0].cfg.net.pending.get(id)!=Some(packet));
    let i=last_send(m,p,j,id,packet);
    assert(same_issue(p,i as int,j as int));
    assert(!effect(p.states[j as int],a[j as int],p.states[j as int+1]));
}

// Progress plus the independent no-await test yields a sharp alternative.
// No fairness is claimed for the shortened finite client schedule.
pub proof fn finish_or_new_input<S>(m:Program<S>,x:State<S>,effect:Relation<State<S>,Event>)
    requires nb::possible(active_step(m),posted(m),x),inbox(x).packets.dom().subset_of(x.reserved),
    ensures nb::possible(client_step(m),local_done(m),inbox(x))
        || wait::needs_class(active_step(m),posted(m),x,effect) || needs_further_input(m,x,effect),
{
    let r=active_step(m);let d=posted(m);let t=inbox(x);let ids=t.packets.dom();
    if !nb::possible(client_step(m),local_done(m),t) {
        if d(x) {assert(nb::within(client_step(m),local_done(m),t,0));}
        nb::first_response_iff(r,d,x);
        if !wait::needs_class(r,d,x,effect) {
            assert(exists|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(r,d,x,p) && !wait::uses(p,effect));
            assert forall|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(r,d,x,p) && !wait::uses(p,effect)
                implies consumes_new_send(m,p,effect) by {
                assert(t.packets =~= remaining(x,ids).packets);
                let j=first_unlock(m,ids,p,0);new_send_origin(m,p,effect,j);
            }
        }
    }
}


// A sufficient wire discipline. All ordinary SR1 answers have already
// been emitted. An additional delivery may carry genuine promotion
// evidence if the separate provenance audit establishes that fact.
pub open spec fn receipt_of<S>(evidence:spec_fn(Packet<Wire>)->bool) -> Relation<State<S>,Event> {
    |x:State<S>,a,_y| match a { Action::Deliver(id)=>x.cfg.net.pending.contains_key(id) && evidence(x.cfg.net.pending[id]),_=>false }
}
pub open spec fn no_new_ordinary_send<S>(m:Program<S>,scope:nb::Region<State<S>>,evidence:spec_fn(Packet<Wire>)->bool) -> bool {
    forall|x:State<S>,a:Event,y:State<S>| scope(x) && !posted(m)(x) && #[trigger] active_step(m)(x,a,y)
        && a is Send && a->Send_1.to==Process::FirstClient ==> evidence(a->Send_1)
}
pub open spec fn closed_while_pending<S>(m:Program<S>,scope:nb::Region<State<S>>) -> bool {
    nb::stays_in_scope(active_step(m),posted(m),scope)
}
pub(crate) proof fn pending_scope<S>(m:Program<S>,scope:nb::Region<State<S>>,p:wait::Path<State<S>,Event>,j:nat)
    requires wait::valid_edges(active_step(m),p),wait::pending_before(posted(m),p),j<p.actions.len(),
        scope(p.states[0]),closed_while_pending(m,scope),
    ensures scope(p.states[j as int]),
    decreases j,
{
    if j>0 {let i=(j-1) as nat;pending_scope(m,scope,p,i);assert(active_step(m)(p.states[i as int],p.actions[i as int],p.states[j as int]));}
}
// An ordinary delivery can change memory and even a selected result.
// This optional progress interface excludes only a new *necessary* input
// after the claimed final answers have been issued.
pub open spec fn preserves_issued_service<S>(m:Program<S>,scope:nb::Region<State<S>>,ids:Set<nat>,
    evidence:spec_fn(Packet<Wire>)->bool) -> bool {
    forall|x:State<S>,a:Event,y:State<S>| scope(x) && !posted(m)(x) && #[trigger] active_step(m)(x,a,y)
        && additional_input(ids)(x,a,y) && !receipt_of(evidence)(x,a,y) && can_use_issued(m,ids,y)
        ==> can_use_issued(m,ids,x)
}
pub proof fn closed_channel_suffices<S>(m:Program<S>,scope:nb::Region<State<S>>,evidence:spec_fn(Packet<Wire>)->bool,x:State<S>)
    requires scope(x),closed_while_pending(m,scope),no_new_ordinary_send(m,scope,evidence)
        || preserves_issued_service(m,scope,inbox(x).packets.dom(),evidence),
    ensures !needs_further_input(m,x,receipt_of(evidence)),
{
    let r=active_step(m);let d=posted(m);let effect=receipt_of(evidence);
    if needs_further_input(m,x,effect) {
        let p=choose|p:wait::Path<State<S>,Event>| #[trigger] wait::first_return(r,d,x,p) && !wait::uses(p,effect);
        assert(consumes_new_send(m,p,effect));
        let (i,j)=choose|i:int,j:int| 0<=i<j<p.actions.len() && #[trigger] same_issue(p,i,j) && !effect(p.states[j],p.actions[j],p.states[j+1])
        && opens_service(m,inbox(p.states[0]).packets.dom(),p.states[j],p.actions[j],p.states[j+1]);
        if no_new_ordinary_send(m,scope,evidence) {
            pending_scope(m,scope,p,i as nat);assert(r(p.states[i],p.actions[i],p.states[i+1]));assert(evidence(p.actions[i]->Send_1));
        } else {
            pending_scope(m,scope,p,j as nat);assert(r(p.states[j],p.actions[j],p.states[j+1]));
            assert(additional_input(inbox(x).packets.dom())(p.states[j],p.actions[j],p.states[j+1]));
        }
    }
}

// A local forward simulation certifies that a delivered packet's private
// bookkeeping cannot newly enable service. Values returned by the two
// related memories need not coincide.
pub open spec fn client_simulation<S>(m:Program<S>,rel:spec_fn(S,S)->bool) -> bool {
    (forall|s:S,t:S| #[trigger] rel(s,t) && (m.done)(t) ==> (m.done)(s))
        && forall|s:S,t:S,e:ProcessStep<int,Wire>| #[trigger] rel(s,t) && e.actor==Process::FirstClient
            && #[trigger] (m.accept)(t,e) ==> (m.accept)(s,e) && rel((m.update)(s,e),(m.update)(t,e))
}
proof fn simulate_client<S>(m:Program<S>,rel:spec_fn(S,S)->bool,s:Inbox<S>,t:Inbox<S>,k:nat)
    requires client_simulation(m,rel),s.packets==t.packets,rel(s.local,t.local),
        nb::within(client_step(m),local_done(m),t,k),
    ensures nb::within(client_step(m),local_done(m),s,k),
    decreases k,
{
    let step=client_step(m);let done=local_done(m);
    if !done(s) {
        let (a,u)=choose|a:Event,u:Inbox<S>| #[trigger] step(t,a,u) && nb::within(step,done,u,(k-1) as nat);
        let v=advance_client(m,s,a);assert(event(s,a)==event(t,a));assert(step(s,a,v));
        simulate_client(m,rel,v,u,(k-1) as nat);
    }
}
pub proof fn bookkeeping_does_not_unlock<S>(m:Program<S>,rel:spec_fn(S,S)->bool,ids:Set<nat>,x:State<S>,a:Event,y:State<S>)
    requires client_simulation(m,rel),active_step(m)(x,a,y),additional_input(ids)(x,a,y),
        rel((x.cfg.private)(Process::FirstClient),(y.cfg.private)(Process::FirstClient)),
    ensures !opens_service(m,ids,x,a,y),
{
    let s=remaining(x,ids);let t=remaining(y,ids);let d=local_done(m);let step=client_step(m);
    assert(s.packets =~= t.packets);
    if can_use_issued(m,ids,y) {
        simulate_client(m,rel,s,t,choose|k:nat| #[trigger] nb::within(step,d,t,k));
    }
}

// The existing scheduler construction can discharge the fair-reference
// existence obligation with finite transport and process turns.
pub proof fn fair_reference_from_turns<S>(m:Program<S>,run:Runnable,region:nb::Region<State<S>>,x:State<S>)
    requires region(x),fair::closed(m,region),
        forall|s:State<S>| region(s) ==> #[trigger] fair::schedulable(m,run,s),
        forall|s:State<S>,a:Event,u:State<S>| #[trigger] read::service_step(m)(s,a,u) && region(s)
            && a==Action::<Wire>::StopFirstClient ==> posted(m)(s),
    ensures fair_opportunity(m,run,x),
{
    let e=fair::fair_extension(m,run,region,x);
    assert forall|i:nat| #[trigger] (e.action)(i)==Action::<Wire>::StopFirstClient implies posted(m)((e.state)(i)) by {
        run_in_region(m,region,x,e,i);
        assert(read::service_step(m)((e.state)(i),(e.action)(i),(e.state)(i+1)));
    }
    assert(honest(m,e));
}
proof fn run_in_region<S>(m:Program<S>,region:nb::Region<State<S>>,x:State<S>,e:Run<S>,j:nat)
    requires region(x),fair::closed(m,region),fair::execution(m,e,x),
    ensures region((e.state)(j)),
    decreases j,
{
    if j>0 {let i=(j-1) as nat;run_in_region(m,region,x,e,i);assert(read::service_step(m)((e.state)(i),(e.action)(i),(e.state)(j)));}
}
}
