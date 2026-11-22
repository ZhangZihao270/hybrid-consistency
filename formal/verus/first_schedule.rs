// Construct a variable-length SR1 and continue the existing two histories.
use vstd::prelude::*;
use crate::{Branch, Replica, Op, checkpoint::*, delivery::*, protocol::*};
use crate::early_crash as probe;
use crate::fair_read as fair;
use crate::first_mailbox::{self as mail, Inbox};
use crate::independent_read::{self as read, State};
use crate::ordinary_service::{Configuration,allowed,apply};
use crate::promotion_wait::{self as wait,Relation};
use crate::read_call::{Event,Program,Net};
use crate::read_issue::{self as issue,send_first,send_second};
use crate::read_nonblocking as nb;
use crate::sr1_majorities as maj;

verus! {

pub type ClientPath<S> = wait::Path<Inbox<S>,Event>;
pub type Execution<S> = wait::Path<Configuration<S>,Event>;
pub open spec fn step<S>(m:Program<S>) -> Relation<Configuration<S>,Event> {
    |x:Configuration<S>,a,y| y==apply(m,x,a) && enabled(x.net,a) && match a {
        Action::CrashR3=>x.net.unavailable.is_none(),
        Action::StopFirstClient=>(m.done)((x.private)(Process::FirstClient)),
        _=>allowed(m,x,a),
    }
}
pub open spec fn cfg<S>(m:Program<S>,b:Fork,k:nat) -> Configuration<S> {
    Configuration{net:state_after(b,k),private:|p|memory(m,p,checkpoint_observations(b),k)}
}
pub open spec fn origin_slot(b:Fork) -> nat {if b.branch==Branch::Alpha {7} else {6}}
pub open spec fn selected(b:Fork) -> Set<nat> {set![origin_slot(b),8nat]}
pub open spec fn replies(b:Fork) -> Map<nat,Packet<Wire>> {
    Map::new(selected(b),|i:nat|packet_for(b,i))
}
pub open spec fn initial_client<S>(m:Program<S>,b:Fork) -> Inbox<S> {
    Inbox{local:(cfg(m,b,11).private)(Process::FirstClient),packets:replies(b)}
}

// Earlier direct-RPC interface ends at emission, strictly before the first
// C1 receipt. Each crash reference tests only those processes which are live.
pub open spec fn emitted<S>(m:Program<S>,b:Fork) -> bool {
    let es=maj::obs(b);
    forall|i:int| 0<=i<9 ==> {let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)}
}
pub open spec fn startup<S>(m:Program<S>) -> bool {
    (m.accept)((m.initial)(Process::SecondClient),issue::local_event(Action::StartSecondClient))
}
pub open spec fn reference<S>(m:Program<S>,b:Fork,k:nat) -> State<S> {
    let n=maj::net(b,k);
    let cs=if k<=2 {Set::empty()} else if k==3 {set![Replica::R1]} else if k==4 {live_pair()} else {all_replicas()};
    let ids=if k<=7 {Set::empty()} else if k==8 {set![origin_slot(b)]} else {selected(b)};
    State{cfg:Configuration{net:n,private:|p|memory(m,p,maj::obs(b),k)},first_requested:cs,
        requested:Set::empty(),calls:read::Calls{first:all_replicas(),second:live_pair()},reserved:ids,
        owners:Map::empty().insert(2nat,at(Replica::R3))}
}
pub open spec fn reached_in<S>(m:Program<S>,b:Fork) -> nb::Region<State<S>> {
    |x|read::reached(m,reference(m,b,0),x)
}
pub(crate) proof fn reference_edge<S>(m:Program<S>,b:Fork,k:nat)
    requires k<9,({let e=maj::obs(b)[k as int];(m.accept)(memory(m,e.actor,maj::obs(b),k),e)}),
    ensures read::prefix_step(m)(reference(m,b,k),maj::actions(b)[k as int],reference(m,b,k+1)),
        k>=5 ==> mail::active_step(m)(reference(m,b,k),maj::actions(b)[k as int],reference(m,b,k+1)),
{
    maj::majority_transport(b);let s=reference(m,b,k);let u=reference(m,b,k+1);
    let a=maj::actions(b)[k as int];let es=maj::obs(b);let e=es[k as int];let y=read::next(m,s,a);
    prefix_index(k as int);assert(enabled(s.cfg.net,a));assert(e==process_step(s.cfg.net,a));
    assert((m.accept)(memory(m,e.actor,es,k),e));
    assert(y.cfg.private =~= u.cfg.private);assert(y.first_requested =~= u.first_requested);assert(y.reserved =~= u.reserved);
}
pub(crate) proof fn ref_suffix<S>(m:Program<S>,b:Fork,k:nat,end:nat)
    requires k<=end<=9, forall|j:int| 0<=j<end ==> {let e=#[trigger] maj::obs(b)[j];(m.accept)(memory(m,e.actor,maj::obs(b),j as nat),e)},
    ensures nb::within(read::prefix_step(m),read::at_state(reference(m,b,end)),reference(m,b,k),(end-k) as nat),
    decreases end-k,
{
    if k<end {
        reference_edge(m,b,k);ref_suffix(m,b,k+1,end);
    }
}
pub proof fn reference_cut<S>(m:Program<S>,b:Fork)
    requires emitted(m,b),
    ensures ({
        let x=reference(m,b,9);
        reached_in(m,b)(x) && mail::submitted(x) && mail::inbox(x)==initial_client(m,b)
            && mail::inbox(x).packets.dom().subset_of(x.reserved)
            && x.cfg.net.pending.get(2)==Some(packet_for(b,2))
            && x.cfg.net.pending.get(if b.branch==Branch::Alpha {0nat} else {1nat})==
                Some(packet_for(b,if b.branch==Branch::Alpha {0nat} else {1nat}))
    }),
{
    maj::majority_transport(b);ref_suffix(m,b,0,9);
    assert(nb::within(read::prefix_step(m),read::at_state(reference(m,b,9)),reference(m,b,0),9));
    let x=reference(m,b,9);let c=Process::FirstClient;maj::local_at(m,b,c,11);
    assert(maj::count(b,11)==9);
    assert(mail::for_client(x.cfg.net.pending) =~= replies(b));
    assert(live(x.cfg.net,at(crate::origin(b.branch))) && live(x.cfg.net,at(Replica::R3)));
    assert(x.first_requested.contains(crate::origin(b.branch)) && x.first_requested.contains(Replica::R3));
}
proof fn live_guard<S>(m:Program<S>,b:Fork,k:nat)
    requires k<11,emitted(m,b),checkpoint_observations(b)[k as int].actor!=at(maj::missing(b)),
    ensures ({let es=checkpoint_observations(b);let e=es[k as int];(m.accept)(memory(m,e.actor,es,k),e)}),
{
    let es=checkpoint_observations(b);let e=es[k as int];let j=maj::count(b,k);
    prefix_index(k as int);maj::majority_transport(b);maj::local_at(m,b,e.actor,k);
    assert(j<9 && maj::kept_index(b,j)==k);
    assert(maj::obs(b)[j as int]==e);assert((m.accept)(memory(m,e.actor,maj::obs(b),j),e));
}
pub open spec fn prelude<S>(m:Program<S>,b:Fork) -> Execution<S> {
    wait::Path{states:Seq::new(12,|j:int|cfg(m,b,j as nat)),actions:actions_to_crash(b).take(11)}
}
pub(crate) proof fn assemble_offers<S>(m:Program<S>,b:Fork)
    requires emitted(m,b),emitted(m,maj::other(b)),startup(m),
    ensures wait::valid_edges(step(m),prelude(m,b)),probe::probe_inputs(m,b),
{
    prefix_transport_is_enabled(b);let es=checkpoint_observations(b);let d=maj::other(b);
    assert forall|i:int| 0<=i<11 implies {
        let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)
    } by {
        let p=es[i].actor;prefix_index(i);
        if p!=at(maj::missing(b)) {live_guard(m,b,i as nat);}
        else {
            live_guard(m,d,i as nat);assert(es[i]==checkpoint_observations(d)[i]);
            arbitrary_survivor_memory_agrees(b.notice,m,p,i as nat);
        }
    }
    assert forall|i:int| 0<=i<11 implies step(m)(prelude(m,b).states[i],#[trigger] prelude(m,b).actions[i],prelude(m,b).states[i+1]) by {
        let a=actions_to_crash(b)[i];let x=cfg(m,b,i as nat);let e=es[i];let y=cfg(m,b,i as nat+1);
        assert(allowed(m,x,a));assert(apply(m,x,a).private =~= y.private);
    }
    assert forall|j:int| 0<=j<16 implies (#[trigger] es[j]).actor!=Process::SecondClient by {prefix_index(j);}
    memory_during_quiescence(m,es,Process::SecondClient,0,16);
    assert(es[16]==issue::local_event(Action::StartSecondClient));
}

// Safety of the *caller* on arbitrary authentic batches, including mixed
// values and any senders. A response needs distinct respondents and is
// drawn from the consumed reports. Nothing requires a client to return.
pub open spec fn authentic(q:Map<nat,Packet<Wire>>) -> bool {
    forall|i:nat| #[trigger] q.contains_key(i) ==> first_reply(q[i])
}
pub open spec fn quorum_response<S>(m:Program<S>,first:spec_fn(S)->int,start:S) -> bool {
    forall|q:Map<nat,Packet<Wire>>,p:ClientPath<S>| #[trigger] authentic(q) && p.states.len()==p.actions.len()+1
        && p.states[0]==(Inbox{local:start,packets:q}) && #[trigger] wait::valid_edges(mail::client_step(m),p)
        && mail::local_done(m)(p.states.last()) ==> {
            let left=p.states.last().packets;
            (exists|i:nat,j:nat| #[trigger] q.contains_key(i) && #[trigger] q.contains_key(j)
                && !left.contains_key(i) && !left.contains_key(j) && q[i].from!=q[j].from)
            && exists|i:nat| #[trigger] q.contains_key(i) && !left.contains_key(i)
                && q[i].input==Wire::Reply(first(p.states.last().local))
        }
}
pub open spec fn placed<S>(m:Program<S>,b:Fork,t:Inbox<S>) -> Configuration<S> {
    let x=cfg(m,b,11);let rest=x.net.pending.remove(origin_slot(b)).remove(8nat);
    Configuration{net:Net{pending:rest.union_prefer_right(t.packets),..x.net},
        private:|p| if p==Process::FirstClient {t.local} else {(x.private)(p)}}
}
pub open spec fn at_client<S>(m:Program<S>,b:Fork,p:ClientPath<S>) -> Execution<S> {
    wait::Path{states:Seq::new(p.states.len(),|i:int|placed(m,b,p.states[i])),actions:p.actions}
}
pub(crate) proof fn subset_after<S>(m:Program<S>,p:ClientPath<S>,j:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::client_step(m),p),j<=p.actions.len(),
    ensures p.states[j as int].packets.submap_of(p.states[0].packets),
        p.states[j as int].packets.dom().subset_of(p.states[0].packets.dom()),
    decreases j,
{
    if j>0 {let k=(j-1) as nat;subset_after(m,p,k);
        assert(mail::client_step(m)(p.states[k as int],p.actions[k as int],p.states[j as int]));}
}

proof fn physical_client_steps<S>(m:Program<S>,b:Fork,p:ClientPath<S>)
    requires p.states.len()==p.actions.len()+1,p.states[0]==initial_client(m,b),wait::valid_edges(mail::client_step(m),p),
    ensures wait::valid_edges(step(m),at_client(m,b,p)),at_client(m,b,p).states[0]==cfg(m,b,11),
{
    let t=at_client(m,b,p);let c=Process::FirstClient;let q=replies(b);
    assert(t.states[0].net.pending =~= state_after(b,11).pending);assert(t.states[0].private =~= cfg(m,b,11).private);
    assert forall|i:int| 0<=i<p.actions.len() implies step(m)(t.states[i],#[trigger] t.actions[i],t.states[i+1]) by {
        let a=p.actions[i];let x=p.states[i];let u=p.states[i+1];let v=t.states[i];
        subset_after(m,p,i as nat);assert(mail::client_step(m)(x,a,u));
        if let Action::Deliver(id)=a {assert(x.packets.contains_key(id));assert(x.packets.dom().contains(id));assert(q.contains_key(id) && (id==8 || id==origin_slot(b)));}
        assert(process_step(v.net,a)==mail::event(x,a));assert(allowed(m,v,a));
        assert(apply(m,v,a).net.pending =~= t.states[i+1].net.pending);
        assert(apply(m,v,a).net.locals =~= t.states[i+1].net.locals);
        assert(apply(m,v,a).private =~= t.states[i+1].private);
    }
}

// Both replicas have already sent in each original. Only actual client
// deliveries are replayed, in the order accepted by that client.
pub proof fn client_execution<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:ClientPath<S>)
    requires p.states.len()==p.actions.len()+1,p.states[0]==initial_client(m,b),wait::valid_edges(mail::client_step(m),p),
        mail::local_done(m)(p.states.last()),quorum_response(m,first,initial_client(m,b).local),
    ensures ({
        let t=at_client(m,b,p);
        wait::valid_edges(step(m),t) && t.states[0]==cfg(m,b,11) && t.states.last().net==state_after(b,13)
            && first(p.states.last().local)==first_value(b)
            && p.states.last().packets==Map::<nat,Packet<Wire>>::empty()
    }),
{
    physical_client_steps(m,b,p);
    let t=at_client(m,b,p);let q=replies(b);
    assert(authentic(q));let last=p.states.last();let left=last.packets;
    let (i,j)=choose|i:nat,j:nat| #[trigger] q.contains_key(i) && #[trigger] q.contains_key(j)
        && !left.contains_key(i) && !left.contains_key(j) && q[i].from!=q[j].from;
    subset_after(m,p,p.actions.len());
    assert(i==origin_slot(b) || i==8);assert(j==origin_slot(b) || j==8);assert(i!=j);
    assert forall|id:nat| ! (#[trigger] left.contains_key(id)) by {if left.contains_key(id) {assert(left.dom().contains(id));assert(q.dom().contains(id));}}
    assert(left =~= Map::<nat,Packet<Wire>>::empty());
    let id=choose|i:nat| #[trigger] q.contains_key(i) && !left.contains_key(i) && q[i].input==Wire::Reply(first(last.local));
    assert(id==8 || id==origin_slot(b));
    assert(t.states.last().net.pending =~= state_after(b,13).pending);
}

// The first read has returned before the stop, crash, and fresh C2 start.
// Old and new C1 private histories can be arbitrarily different here.
pub open spec fn closing<S>(m:Program<S>,b:Fork,client:S,k:nat) -> Configuration<S> {
    let x=cfg(m,b,14+k);
    Configuration{private:|p| if p!=Process::FirstClient {(x.private)(p)} else if k==0 {client}
        else {(m.update)(client,process_step(state_after(b,14),Action::StopFirstClient))},..x}
}
pub open spec fn lifecycle<S>(m:Program<S>,b:Fork,s:S) -> Execution<S> {
    wait::Path{states:Seq::new(4,|k:int|closing(m,b,s,k as nat)),
        actions:seq![Action::StopFirstClient,Action::CrashR3,Action::StartSecondClient]}
}
pub open spec fn resumed<S>(m:Program<S>,b:Fork,p:ClientPath<S>) -> Program<S> {
    Program{initial:closing(m,b,p.states.last().local,3).private,..m}
}
proof fn post_return<S>(m:Program<S>,b:Fork,p:ClientPath<S>)
    requires p.states.len()>0,mail::local_done(m)(p.states.last()),
        at_client(m,b,p).states.last().net==state_after(b,13),startup(m),
    ensures lifecycle(m,b,p.states.last().local).states[0]==at_client(m,b,p).states.last(),
        wait::valid_edges(step(m),lifecycle(m,b,p.states.last().local)),
        closing(m,b,p.states.last().local,3).net==checkpoint_end(b),
        forall|who:Process| survivor_actor(who) ==> #[trigger] (resumed(m,b,p).initial)(who)==(resume_at(m,checkpoint_observations(b)).initial)(who),
{
    let s=p.states.last().local;let path=lifecycle(m,b,s);let es=checkpoint_observations(b);let c=Process::FirstClient;
    assert forall|q:Process| q!=c implies #[trigger] (cfg(m,b,14).private)(q)==(cfg(m,b,11).private)(q) by {
        assert forall|i:int| 11<=i<14 implies (#[trigger] es[i]).actor!=q by {prefix_index(i);}
        memory_during_quiescence(m,es,q,11,14);
    }
    assert(path.states[0].net.pending =~= state_after(b,13).pending);
    assert(path.states[0].private =~= at_client(m,b,p).states.last().private);
    let c2=Process::SecondClient;
    assert forall|i:int| 0<=i<16 implies (#[trigger] es[i]).actor!=c2 by {prefix_index(i);}
    memory_during_quiescence(m,es,c2,0,16);prefix_transport_is_enabled(b);
    assert forall|i:int| 0<=i<3 implies step(m)(path.states[i],#[trigger] path.actions[i],path.states[i+1]) by {
        assert(i==0 || i==1 || i==2);let x=path.states[i];let y=path.states[i+1];let a=path.actions[i];
        assert(a==actions_to_crash(b)[i+14]);
        assert(process_step(x.net,a)==es[i+14]);
        if i==2 {assert(allowed(m,x,a));}
        assert(apply(m,x,a).private =~= y.private);
    }
}

pub open spec fn join<S>(t:Execution<S>,u:Execution<S>) -> Execution<S> {
    wait::Path{states:t.states.drop_last()+u.states,actions:t.actions+u.actions}
}
proof fn join_steps<S>(m:Program<S>,t:Execution<S>,u:Execution<S>)
    requires t.states.len()==t.actions.len()+1,u.states.len()==u.actions.len()+1,t.states.last()==u.states[0],
        wait::valid_edges(step(m),t),wait::valid_edges(step(m),u),
    ensures wait::valid_edges(step(m),join(t,u)),join(t,u).states[0]==t.states[0],join(t,u).states.last()==u.states.last(),
        join(t,u).states.len()==join(t,u).actions.len()+1,
{
    let v=join(t,u);assert forall|i:int| 0<=i<v.actions.len() implies step(m)(v.states[i],#[trigger] v.actions[i],v.states[i+1]) by {
        if i<t.actions.len() {assert(step(m)(t.states[i],t.actions[i],t.states[i+1]));}
        else {let j=i-t.actions.len();assert(step(m)(u.states[j],u.actions[j],u.states[j+1]));}
    }
}
pub open spec fn original<S>(m:Program<S>,b:Fork,p:ClientPath<S>) -> Execution<S> {
    join(join(prelude(m,b),at_client(m,b,p)),lifecycle(m,b,p.states.last().local))
}
pub open spec fn before_answers<S>(m:Program<S>,b:Fork) -> bool {
    forall|k:nat| k<=11 ==> !(m.done)((#[trigger] cfg(m,b,k).private)(Process::FirstClient))
}
pub open spec fn first_read<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:ClientPath<S>) -> bool {
    let t=original(m,b,p);let c=Process::FirstClient;let j=11+p.actions.len();
    t.states.len()==t.actions.len()+1 && t.states[0]==cfg(m,b,0) && t.states.last().net==checkpoint_end(b)
        && t.states.last().private==resumed(m,b,p).initial && wait::valid_edges(step(m),t)
        && t.actions==actions_to_crash(b).take(11)+p.actions+seq![Action::StopFirstClient,Action::CrashR3,Action::StartSecondClient]
        && (forall|i:int| 0<=i<j ==> !(m.done)((#[trigger] t.states[i].private)(c)))
        && (m.done)((t.states[j as int].private)(c)) && first((t.states[j as int].private)(c))==first_value(b)
        && t.states[j as int].net==state_after(b,13) && t.states[j as int].net.pending.get(2)==Some(packet_for(b,2))
        && (forall|i:int| 0<=i<p.actions.len() ==> match #[trigger] p.actions[i] {
            Action::Deliver(id)=>selected(b).contains(id), Action::Strong(q)|Action::ClientInput(q,_)=>q==c,_=>false})
        && (forall|id:nat| #[trigger] selected(b).contains(id) ==> p.actions.contains(Action::<Wire>::Deliver(id)))
}
proof fn missing_delivery<S>(m:Program<S>,p:ClientPath<S>,k:nat,id:nat)
    requires p.states.len()==p.actions.len()+1,k<=p.actions.len(),wait::valid_edges(mail::client_step(m),p),
        p.states[0].packets.contains_key(id),!p.states[k as int].packets.contains_key(id),
    ensures exists|i:int| 0<=i<k && #[trigger] p.actions[i]==Action::<Wire>::Deliver(id),
    decreases k,
{
    let j=(k-1) as nat;assert(mail::client_step(m)(p.states[j as int],p.actions[j as int],p.states[k as int]));
    if p.actions[j as int]!=Action::<Wire>::Deliver(id) {missing_delivery(m,p,j,id);}
}
pub proof fn realize_client_path<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:ClientPath<S>)
    requires emitted(m,b),emitted(m,maj::other(b)),startup(m),before_answers(m,b),answer_policy(m,first,b),
        wait::first_return(mail::client_step(m),mail::local_done(m),initial_client(m,b),p),
    ensures first_read(m,first,b,p),
{
    let r=mail::client_step(m);let d=mail::local_done(m);let x=initial_client(m,b);
    let t=prelude(m,b);let u=at_client(m,b,p);let v=lifecycle(m,b,p.states.last().local);
    assemble_offers(m,b);
    if quorum_response(m,first,x.local) {client_execution(m,first,b,p);}
    else {assert(both_receipts(b,p));interval_execution(m,first,b,p);}
    post_return(m,b,p);
    join_steps(m,t,u);join_steps(m,join(t,u),v);
    let o=original(m,b,p);let j=11+p.actions.len();
    assert(o.actions =~= actions_to_crash(b).take(11)+p.actions+v.actions);
    assert(o.states[j as int]==u.states.last());
    assert forall|i:int| 0<=i<j implies !(m.done)((#[trigger] o.states[i].private)(Process::FirstClient)) by {
        if i<11 { assert(o.states[i]==cfg(m,b,i as nat)); }
        else {assert(!d(p.states[i-11]));assert(o.states[i]==u.states[i-11]);}
    }
    assert forall|i:int| 0<=i<p.actions.len() implies match #[trigger] p.actions[i] {
        Action::Deliver(id)=>selected(b).contains(id),Action::Strong(q)|Action::ClientInput(q,_)=>q==Process::FirstClient,_=>false}
        by {
            assert(r(p.states[i],p.actions[i],p.states[i+1]));subset_after(m,p,i as nat);
            if let Action::Deliver(id)=p.actions[i] {assert(p.states[i].packets.dom().contains(id));}
        }
    assert forall|id:nat| #[trigger] selected(b).contains(id) implies p.actions.contains(Action::<Wire>::Deliver(id))
        by {missing_delivery(m,p,p.actions.len(),id);}
}

pub proof fn assemble_first_read<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork)
    -> (p:ClientPath<S>)
    requires emitted(m,b),emitted(m,maj::other(b)),startup(m),before_answers(m,b),
        answer_policy(m,first,b),nb::possible(mail::client_step(m),mail::local_done(m),initial_client(m,b)),
    ensures first_read(m,first,b,p),
{
    let r=mail::client_step(m);let d=mail::local_done(m);let x=initial_client(m,b);
    let p=nb::to_path(r,d,x,choose|k:nat| #[trigger] nb::within(r,d,x,k));
    realize_client_path(m,first,b,p);p
}

proof fn covered_after_issue<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,p:ClientPath<S>)
    requires issue::can_issue(m,res),
    ensures ({
        let other=resumed(m,b,p);let l=issue::issued(b);
        crate::finite_service::requested_prefix(other,res,checkpoint_end(b),delayed_slots(),l.nets,l.actions)
            && read::covers(probe::cut(m,11),crate::finite_service::at_end(other,l.nets,l.actions))
    }),
{
    hide(read::covers);let past=resume_at(m,checkpoint_observations(b));let other=resumed(m,b,p);
    let l=issue::issued(b);let es=crate::read_call::obs(l);probe::initial_cover(m,res,b);
    let c=Process::SecondClient;
    assert(es =~= seq![issue::local_event(send_first()),issue::local_event(send_second())]);
    assert forall|q:Process,k:nat| k<=es.len() && survivor_actor(q) implies
        #[trigger] memory(other,q,es,k)==memory(past,q,es,k) by {memory_from_same_local_state(other,past,q,es,k);}
    assert(accepted(other,es)) by {
        assert forall|i:int| 0<=i<es.len() implies {let e=#[trigger] es[i];(other.accept)(memory(other,e.actor,es,i as nat),e)} by {
            assert(i==0 || i==1);assert(es[i].actor==c);assert((past.accept)(memory(past,c,es,i as nat),es[i]));
        }
    }
    assert(pending_before_end(other,res,es)) by {
        assert forall|k:nat| k<es.len() implies res(#[trigger] memory(other,c,es,k)).is_none()
            by {assert(res(memory(past,c,es,k)).is_none());}
    }
    reveal(read::covers);
}

pub open spec fn checkpoint_packets_remain(b:Fork,l:crate::read_call::Log) -> bool {
    checkpoint_end(b).pending.submap_of(l.nets.last().pending) && enabled(l.nets.last(),Action::Deliver(2))
}
proof fn still_queued(b:Fork,l:crate::read_call::Log,k:nat)
    requires trace(|x,w|cell(x,w),l.nets,l.actions),l.nets[0]==checkpoint_end(b),k<=l.actions.len(),
        forall|j:int| 0<=j<l.actions.len() ==> #[trigger] l.actions[j]!=Action::<Wire>::Deliver(2),
    ensures checkpoint_end(b).pending.submap_of(l.nets[k as int].pending),enabled(l.nets[k as int],Action::Deliver(2)),
    decreases k,
{
    crate::survivors::postcrash_schedule_has_only_live_actors(|x,w|cell(x,w),l.nets,l.actions,k);
    let old=checkpoint_end(b).pending;assert(checkpoint_end(b)==state_after(b,17));
    assert(old.contains_key(2nat) && old[2nat]==packet_for(b,2));
    withheld_packet_stays_pending(|x,w|cell(x,w),l.nets,l.actions,2,k as int);
    if k>0 {
        let j=(k-1) as nat;still_queued(b,l,j);let x=l.nets[j as int];let a=l.actions[j as int];
        crate::survivors::postcrash_schedule_has_only_live_actors(|x,w|cell(x,w),l.nets,l.actions,j);
        assert(enabled(x,a) && l.nets[k as int]==advance(|z,w|cell(z,w),x,a));
        assert forall|id:nat| #[trigger] old.contains_key(id) implies l.nets[k as int].pending.get(id)==Some(old[id]) by {
            assert(x.pending.get(id)==Some(old[id]));
            if id!=2 {assert(!live(x,old[id].to));} else {assert(l.actions[j as int]!=Action::<Wire>::Deliver(2));}
        }
    }
    assert(l.nets[k as int].pending.get(2)==Some(packet_for(b,2)));
}
pub open spec fn completed_pair<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    a:ClientPath<S>,b:ClientPath<S>,sa:crate::read_call::Log,sb:crate::read_call::Log,v:int) -> bool {
    first_read(m,first,alpha(n),a) && first_read(m,first,beta(n),b)
        && crate::service::response_path(resumed(m,alpha(n),a),res,checkpoint_end(alpha(n)),delayed_slots(),sa.nets,sa.actions,v)
        && crate::service::response_path(resumed(m,beta(n),b),res,checkpoint_end(beta(n)),delayed_slots(),sb.nets,sb.actions,v)
        && checkpoint_packets_remain(alpha(n),sa) && checkpoint_packets_remain(beta(n),sb)
        && sa.actions==sb.actions && sa.actions.len()>=2 && sa.actions[0]==send_first() && sa.actions[1]==send_second()
        && (forall|i:int| 0<=i<sa.actions.len() ==> #[trigger] sa.actions[i]!=Action::<Wire>::Deliver(2))
        && !(exists|ao:Seq<Op>,ax:Seq<int>,bo:Seq<Op>,bx:Seq<int>| #[trigger] crate::legal(ao,ax,5,v) && #[trigger] crate::legal(bo,bx,2,v))
}
pub open spec fn conflict<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>) -> bool {
    exists|a:ClientPath<S>,b:ClientPath<S>,sa:crate::read_call::Log,sb:crate::read_call::Log,v:int|
        #[trigger] completed_pair(n,m,first,res,a,b,sa,sb,v)
}
proof fn replay_one<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,p:ClientPath<S>,w:fair::Block<S>)
    -> (s:crate::read_call::Log)
    requires issue::can_issue(m,res),wait::first_return(read::service_step(m),read::returned(res),probe::cut(m,11),w),
    ensures crate::service::response_path(resumed(m,b,p),res,checkpoint_end(b),delayed_slots(),s.nets,s.actions,
            res((w.states.last().cfg.private)(Process::SecondClient)).unwrap()),
        s.actions==issue::issued(b).actions+read::retained_actions(w,0),s.actions.len()>=2,s.actions[0]==send_first(),s.actions[1]==send_second(),
        forall|i:int| 0<=i<s.actions.len() ==> #[trigger] s.actions[i]!=Action::<Wire>::Deliver(2),
{
    covered_after_issue(m,res,b,p);probe::initial_cover(m,res,b);let l=issue::issued(b);
    let s=read::project_response(m,resumed(m,b,p),res,w,0,checkpoint_end(b),delayed_slots(),l,2);
    assert(s.actions.take(2)[0]==s.actions[0] && s.actions.take(2)[1]==s.actions[1]);s
}
pub open spec fn service_at_offers<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork) -> bool {
    emitted(m,b) && before_answers(m,b) && answer_policy(m,first,b)
        && nb::possible(mail::client_step(m),mail::local_done(m),initial_client(m,b))
}
pub proof fn replay_at_both_returns<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    a:ClientPath<S>,b:ClientPath<S>,w:fair::Block<S>)
    requires first_read(m,first,alpha(n),a),first_read(m,first,beta(n),b),issue::can_issue(m,res),
        wait::first_return(read::service_step(m),read::returned(res),probe::cut(m,11),w),
    ensures exists|sa:crate::read_call::Log,sb:crate::read_call::Log,v:int| #[trigger] completed_pair(n,m,first,res,a,b,sa,sb,v),
{
    hide(crate::service::response_path);hide(crate::legal);
    let sa=replay_one(m,res,alpha(n),a,w);let sb=replay_one(m,res,beta(n),b,w);
    let v=res((w.states.last().cfg.private)(Process::SecondClient)).unwrap();
    assert(checkpoint_packets_remain(alpha(n),sa) && checkpoint_packets_remain(beta(n),sb)) by {
        reveal(crate::service::response_path);
        still_queued(alpha(n),sa,sa.actions.len());still_queued(beta(n),sb,sb.actions.len());
    }
    if exists|ao:Seq<Op>,ax:Seq<int>,bo:Seq<Op>,bx:Seq<int>| #[trigger] crate::legal(ao,ax,5,v) && #[trigger] crate::legal(bo,bx,2,v) {
        let (ao,ax,bo,bx)=choose|ao:Seq<Op>,ax:Seq<int>,bo:Seq<Op>,bx:Seq<int>| #[trigger] crate::legal(ao,ax,5,v) && #[trigger] crate::legal(bo,bx,2,v);
        crate::conditional_history_contradiction(ao,ax,bo,bx,v);
    }
    assert(completed_pair(n,m,first,res,a,b,sa,sb,v));
}
pub proof fn pair_with_variable_sr1<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires startup(m),issue::can_issue(m,res),service_at_offers(m,first,alpha(n)),service_at_offers(m,first,beta(n)),
        nb::possible(read::service_step(m),read::returned(res),probe::cut(m,11)),
    ensures conflict(n,m,first,res),
{
    hide(wait::first_return);hide(crate::service::response_path);hide(crate::legal);
    assert(emitted(m,alpha(n)));assert(emitted(m,beta(n)));
    let a=assemble_first_read(m,first,alpha(n));let b=assemble_first_read(m,first,beta(n));
    assemble_offers(m,alpha(n));probe::reachable_independent_call(m,res,alpha(n));
    let step=read::service_step(m);let done=read::returned(res);let x=probe::cut(m,11);
    assert(nb::possible(step,done,x));
    let w=nb::to_path(step,done,x,choose|k:nat| #[trigger] nb::within(step,done,x,k));
    replay_at_both_returns(n,m,first,res,a,b,w);
}


// The manuscript's value rule applies to the actual read interval. This
// alternative does not require a table in C1 or a selector over packet bodies.
pub open spec fn read_event(e:ProcessStep<int,Wire>) -> bool {
    match e.action {
        Action::Send(_,p)=> (p.from==Process::FirstClient && invocation_packet(p)) || first_reply(p),
        Action::Deliver(_) => e.incoming.is_some() && {
            let p=e.incoming.unwrap();(p.from==Process::FirstClient && invocation_packet(p)) || first_reply(p)
        },
        Action::Strong(p)|Action::ClientInput(p,_)=>p==Process::FirstClient,
        _=>false,
    }
}
pub open spec fn observed<S>(t:Execution<S>,j:int) -> ProcessStep<int,Wire> {
    process_step(t.states[j].net,t.actions[j])
}
pub open spec fn answer_at<S>(t:Execution<S>,j:int,r:Replica) -> bool {
    let e=observed(t,j);
    e.incoming.is_some() && first_reply(e.incoming.unwrap()) && e.incoming.unwrap().from==at(r)
}
// 'start' is a fresh invocation. This safety policy ranges over every
// completed direct RPC trace from it that consumed a majority of replies.
pub open spec fn interval_policy<S>(m:Program<S>,first:spec_fn(S)->int,start:Configuration<S>) -> bool {
    let c=Process::FirstClient;let d=|x:Configuration<S>| (m.done)((x.private)(c));
    forall|t:Execution<S>| t.states.len()==t.actions.len()+1 && t.states[0]==start
        && #[trigger] wait::valid_edges(step(m),t) && wait::pending_before(d,t) && d(t.states.last())
        && t.actions.len()>0 && t.actions[0] is Send && t.actions[0]->Send_1.from==c
        && (forall|i:int| 0<=i<t.actions.len() ==> read_event(#[trigger] observed(t,i)))
        && (exists|i:int,j:int,r:Replica,s:Replica| 0<=i<t.actions.len() && 0<=j<t.actions.len() && r!=s
                && #[trigger] answer_at(t,i,r) && #[trigger] answer_at(t,j,s)) ==>
            exists|j:int,k:int,r:Replica| 0<=j<t.actions.len() && 0<=k<t.states.len() && #[trigger] answer_at(t,j,r)
                && #[trigger] (t.states[k].net.locals)(r)==first((t.states.last().private)(c))
}
pub open spec fn both_receipts<S>(b:Fork,p:ClientPath<S>) -> bool {
    p.actions.contains(Action::<Wire>::Deliver(8)) && p.actions.contains(Action::<Wire>::Deliver(origin_slot(b)))
}
pub open spec fn inbox_quorum<S>(m:Program<S>,b:Fork) -> bool {
    forall|p:ClientPath<S>| #[trigger] wait::first_return(mail::client_step(m),mail::local_done(m),initial_client(m,b),p)
        ==> both_receipts(b,p)
}
pub open spec fn value_rule<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork) -> bool {
    quorum_response(m,first,initial_client(m,b).local) || interval_policy(m,first,cfg(m,b,2))
}
pub open spec fn answer_policy<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork) -> bool {
    quorum_response(m,first,initial_client(m,b).local) || (interval_policy(m,first,cfg(m,b,2)) && inbox_quorum(m,b))
}

proof fn consumed<S>(m:Program<S>,p:ClientPath<S>,j:nat,k:nat,id:nat)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::client_step(m),p),j<k<=p.actions.len(),
        p.actions[j as int]==Action::<Wire>::Deliver(id),
    ensures !p.states[k as int].packets.contains_key(id),
    decreases k-j,
{
    let i=(k-1) as nat;assert(mail::client_step(m)(p.states[i as int],p.actions[i as int],p.states[k as int]));
    if j<i {consumed(m,p,j,i,id);}
}
proof fn interval_execution<S>(m:Program<S>,first:spec_fn(S)->int,b:Fork,p:ClientPath<S>)
    requires wait::valid_edges(step(m),prelude(m,b)),before_answers(m,b),interval_policy(m,first,cfg(m,b,2)),both_receipts(b,p),
        wait::first_return(mail::client_step(m),mail::local_done(m),initial_client(m,b),p),
    ensures ({
        let t=at_client(m,b,p);wait::valid_edges(step(m),t) && t.states[0]==cfg(m,b,11)
            && t.states.last().net==state_after(b,13) && first(p.states.last().local)==first_value(b)
            && p.states.last().packets==Map::<nat,Packet<Wire>>::empty()
    }),
{
    hide(allowed);hide(apply);hide(memory);hide(maj::net);hide(interval_policy);
    let c=Process::FirstClient;
    let start=Execution{states:prelude(m,b).states.skip(2),actions:prelude(m,b).actions.skip(2)};
    let u=at_client(m,b,p);physical_client_steps(m,b,p);let t=join(start,u);
    assert forall|i:int| 0<=i<9 implies step(m)(start.states[i],#[trigger] start.actions[i],start.states[i+1]) by {
        assert(step(m)(prelude(m,b).states[i+2],prelude(m,b).actions[i+2],prelude(m,b).states[i+3]));
    }
    join_steps(m,start,u);let end=t.states.last();let d=|x:Configuration<S>| (m.done)((x.private)(c));
    assert forall|i:int| 0<=i<t.actions.len() implies !d(#[trigger] t.states[i]) by {
        if i<9 {assert(t.states[i]==cfg(m,b,i as nat+2));}
        else {assert(!mail::local_done(m)(p.states[i-9]));}
    }
    assert forall|i:int| 0<=i<t.actions.len() implies read_event(#[trigger] observed(t,i)) by {
        if i<9 { prefix_index(i+2); }
        else {
            let j=i-9;let a=p.actions[j];
            assert(mail::client_step(m)(p.states[j],a,p.states[j+1]));subset_after(m,p,j as nat);
            if let Action::Deliver(id)=a {
                assert(p.states[j].packets.dom().contains(id));
                assert(id==8 || id==origin_slot(b));assert(p.states[j].packets[id]==packet_for(b,id));
            }
        }
    }
    assert forall|i:int,r:Replica| 0<=i<t.actions.len() && #[trigger] answer_at(t,i,r) implies
        i>=9 && (r==Replica::R3 || r==crate::origin(b.branch))
            && p.actions[i-9]==Action::<Wire>::Deliver(if r==Replica::R3 {8nat} else {origin_slot(b)}) by {
        if i<9 {prefix_index(i+2);}
        else {
            let j=i-9;let a=p.actions[j];let id=a->Deliver_0;
            assert(mail::client_step(m)(p.states[j],a,p.states[j+1]));assert(a is Deliver);subset_after(m,p,j as nat);
            assert(p.states[j].packets.dom().contains(id));assert(id==8 || id==origin_slot(b));
        }
    }
    assert(wait::pending_before(d,t) && t.states[0]==cfg(m,b,2));
    reveal(interval_policy);
    let i=choose|i:int| 0<=i<p.actions.len() && #[trigger] p.actions[i]==Action::<Wire>::Deliver(8);
    let j=choose|j:int| 0<=j<p.actions.len() && #[trigger] p.actions[j]==Action::<Wire>::Deliver(origin_slot(b));
    assert forall|h:int,w:Replica| (h==i || h==j) && w==(if h==i {Replica::R3} else {crate::origin(b.branch)}) implies #[trigger] answer_at(t,9+h,w) by {
        subset_after(m,p,h as nat);let id=p.actions[h]->Deliver_0;
        assert(mail::client_step(m)(p.states[h],p.actions[h],p.states[h+1]));assert(p.states[h].packets.dom().contains(id));
        assert(p.states[h].packets[id]==packet_for(b,id));
    }
    assert(answer_at(t,9+i,Replica::R3) && answer_at(t,9+j,crate::origin(b.branch)));
    consumed(m,p,i as nat,p.actions.len(),8);consumed(m,p,j as nat,p.actions.len(),origin_slot(b));
    subset_after(m,p,p.actions.len());let left=p.states.last().packets;
    assert forall|k:nat| ! (#[trigger] left.contains_key(k)) by {if left.contains_key(k) {assert(left.dom().contains(k));}}
    assert(left =~= Map::<nat,Packet<Wire>>::empty());
    let (j,k,r)=choose|j:int,k:int,r:Replica| 0<=j<t.actions.len() && 0<=k<t.states.len() && #[trigger] answer_at(t,j,r)
        && #[trigger] (t.states[k].net.locals)(r)==first((end.private)(c));
    if k<9 {assert(t.states[k]==cfg(m,b,k as nat+2));} else {assert(t.states[k]==u.states[k-9]);}
    assert(u.states.last().net.pending =~= state_after(b,13).pending);
}

}
