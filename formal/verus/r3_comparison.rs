// Same machine, weak fork and C1 history. Move the sampling boundary across
// each peer receipt by delaying that packet until the two SR2 replies are
// already in flight. Every packet to a live survivor is still consumed.
use vstd::prelude::*;
use crate::{Branch, Op, Replica, RecoveredOrder, checkpoint::*, delivery::*, protocol::*};
use crate::r3_value::{self as r3, Rule, Local, Row};
use crate::information_flow as flow;
use crate::order_extension as history;
use crate::read_call::{Event, Log, Net, obs};
use crate::precedence::{self, Side, at_side};
use crate::sr2::query_packet;
use crate::independent_read as read;
use crate::hybrid_majority as majority;
use crate::promotion_wait as wait;
use crate::first_splice::{Observation, Tape, pick};
use crate::first_causality::pick_concat;
use crate::fork_alternatives as alternatives;
use crate::{fork_information as info, retained_order};
use crate::guarded_comparison as cmp;
use crate::first_assembly as asm;
use crate::first_splice as tape;

verus! {

// early is the number of the two receipts delivered before either report.
// All other steps keep their order; report payloads come from the same handler.
pub open spec fn site(j: nat) -> Replica {
    if j == 0 { Replica::R1 } else { Replica::R2 }
}

pub open spec fn receive_index(early: nat, j: nat) -> nat {
    if j < early { 10 + j } else { 25 + j }
}

pub open spec fn report<M>(rule: Rule<M>, b: Fork, early: nat, j: nat) -> Row {
    let saved = if j < early { (rule.remember)(rule.empty, first_value(b)) } else { rule.empty };
    r3::row(rule, saved, (checkpoint_end(b).locals)(site(j)), true)
}

pub open spec fn actions<M>(rule: Rule<M>, b: Fork, early: nat) -> Seq<Event> {
    let a = r3::actions(rule, b);
    let cut = 10 + early as int;
    a.take(cut) + a.subrange(12, 25)
        + seq![Action::Send(13, r3::answer(site(0), report(rule,b,early,0))),
               Action::Send(14, r3::answer(site(1), report(rule,b,early,1)))]
        + a.subrange(cut, 12) + a.skip(27)
}

// Location in the native trace with respect to all work other than the
// two peer deliveries. At a late delivery the native cursor stays at 27.
pub open spec fn cursor(early: nat, k: nat) -> nat {
    if k <= 10 + early || k >= 27 { k }
    else if k <= 25 + early { (k + 2 - early) as nat } else { 27 }
}

pub open spec fn net<M>(rule: Rule<M>, b: Fork, early: nat, k: nat) -> Net {
    let t = cursor(early,k);
    let base = state_after(b, r3::original_cut(t));
    let p = base.pending;
    let p = if 9 <= k <= receive_index(early,0) { p.insert(9, r3::peer(site(0), first_value(b))) } else { p };
    let p = if 10 <= k <= receive_index(early,1) { p.insert(10, r3::peer(site(1), first_value(b))) } else { p };
    let p = if 22 <= t < 24 { p.insert(11, query_packet(site(0))) } else { p };
    let p = if 23 <= t < 25 { p.insert(12, query_packet(site(1))) } else { p };
    let p = if 26 <= t < 28 { p.insert(13, r3::answer(site(0), report(rule,b,early,0))) } else { p };
    let p = if 27 <= t < 29 { p.insert(14, r3::answer(site(1), report(rule,b,early,1))) } else { p };
    Network { pending: p, ..base }
}

pub open spec fn run<M>(rule: Rule<M>, b: Fork, early: nat) -> Log {
    Log { nets: Seq::new(31, |k: int| net(rule, b, early, k as nat)), actions: actions(rule,b,early) }
}

pub open spec fn local<M>(rule: Rule<M>, b: Fork, early: nat, p: Process, k: nat) -> Local<M> {
    let base = r3::local(rule,b,p,cursor(early,k));
    let saved = (p == at(site(0)) && k > receive_index(early,0)) || (p == at(site(1)) && k > receive_index(early,1));
    let l = report(rule,b,early,0); let r = report(rule,b,early,1);
    let c = p == Process::SecondClient;
    Local { memo: if saved { (rule.remember)(rule.empty,first_value(b)) } else { rule.empty },
        left: if c && k >= 28 { Some(l) } else { None },
        right: if c && k >= 29 { Some(r) } else { None },
        choice: if c && k >= 30 { Some((rule.elect)(l,r)) } else { None }, ..base }
}

pub open spec fn state<M>(rule: Rule<M>, l: Log, p: Process, k: nat) -> Local<M> {
    memory(r3::machine(rule), p, obs(l), k)
}

proof fn transport_edge<M>(rule: Rule<M>, b: Fork, early: nat, k: nat)
    requires early <= 2, k < 30,
    ensures ({
        let l = run(rule,b,early); let a = l.actions[k as int]; let n = l.nets[k as int];
        enabled(n,a) && advance(|x,w| cell(x,w), n, a) == l.nets[k as int+1]
    }),
{
    let t = cursor(early,k);
    let l = run(rule,b,early); let a = l.actions[k as int]; let n = l.nets[k as int];
    let next = advance(|x,w| cell(x,w), n, a);
    let target = l.nets[k as int+1];
    if k < 10 {
        r3::transport_edge(rule,b,k);
        assert(n == r3::net(rule,b,k) && target == r3::net(rule,b,k+1));
    } else {
        assert(early == 0 || early == 1 || early == 2);
        r3::index(k as int);
        assert(next.pending =~= target.pending);
        assert(next.locals =~= target.locals);
    }
}

spec fn private_step<M>(rule: Rule<M>, b: Fork, early: nat, p: Process, k: nat) -> bool {
    let l = run(rule,b,early); let e = obs(l)[k as int]; let s = local(rule,b,early,p,k);
    (e.actor == p ==> r3::accepts(rule,s,e))
        && (if e.actor == p { r3::update(rule,s,e) } else { s }) == local(rule,b,early,p,k+1)
}

proof fn private_prefix<M>(rule: Rule<M>, b: Fork, early: nat, p: Process, k: nat)
    requires early <= 2, k < 30, k < 10 + early,
    ensures private_step(rule,b,early,p,k),
{
    let l = run(rule,b,early); let native = r3::run(rule,b);
    r3::handler_edge(rule,b,p,k);
    assert(obs(l)[k as int] == obs(native)[k as int]);
    assert(local(rule,b,early,p,k) == r3::local(rule,b,p,k));
    assert(local(rule,b,early,p,k+1) == r3::local(rule,b,p,k+1));
}

proof fn private_middle<M>(rule: Rule<M>, b: Fork, early: nat, p: Process, k: nat)
    requires early <= 2, k < 30, 10 + early <= k < 23 + early,
    ensures private_step(rule,b,early,p,k),
{
    let l = run(rule,b,early); let native = r3::run(rule,b);
    let i = (k + 2 - early) as nat;
    r3::handler_edge(rule,b,p,i);
    let e = obs(l)[k as int]; let s = local(rule,b,early,p,k); let u = r3::local(rule,b,p,i);
    assert(e == obs(native)[i as int]) by {
        r3::index(i as int); assert(early == 0 || early == 1 || early == 2);
    }
    assert(s == (Local { memo: s.memo, ..u }));
    assert(s.memo == local(rule,b,early,p,k+1).memo);
    assert(local(rule,b,early,p,k+1) == (Local { memo: s.memo, ..r3::local(rule,b,p,i+1) }));
    assert(!(e.action is Send) || (!(e.action->Send_1.input is Peer) && !(e.action->Send_1.input is StampedAnswer)));
    assert(e.incoming.is_none() || !r3::is_peer(e.incoming.unwrap()));
}

proof fn private_reports<M>(rule: Rule<M>, b: Fork, early: nat, p: Process, k: nat)
    requires early <= 2, k < 30, 23 + early <= k,
    ensures private_step(rule,b,early,p,k),
{
    assert(early == 0 || early == 1 || early == 2);
    if k < 25 + early {
        assert(private_step(rule,b,early,p,k)) by { assert(k == 23 + early || k == 24 + early); }
    } else if k < 27 {
        assert(private_step(rule,b,early,p,k)) by { assert(k == 25 || k == 26); }
    } else {
        assert(private_step(rule,b,early,p,k)) by { assert(k == 27 || k == 28 || k == 29); }
    }
}

proof fn handler_edge<M>(rule: Rule<M>, b: Fork, early: nat, p: Process, k: nat)
    requires early <= 2, k < 30,
    ensures private_step(rule,b,early,p,k),
{
    if k < 10 + early { private_prefix(rule,b,early,p,k); }
    else if k < 23 + early { private_middle(rule,b,early,p,k); }
    else { private_reports(rule,b,early,p,k); }
}

pub proof fn actual_local<M>(rule: Rule<M>, b: Fork, early: nat, p: Process, k: nat)
    requires early <= 2, k <= 30,
    ensures state(rule,run(rule,b,early),p,k) == local(rule,b,early,p,k),
    decreases k,
{
    if k > 0 {
        let j = (k-1) as nat;
        actual_local(rule,b,early,p,j); handler_edge(rule,b,early,p,j);
    }
}

pub open spec fn admitted<M>(rule: Rule<M>, l: Log) -> bool {
    l.nets[0] == after_local_rmws() && trace(|x,w| cell(x,w),l.nets,l.actions)
        && accepted(r3::machine(rule),obs(l))
}

pub proof fn retimed_service_executes<M>(rule: Rule<M>, b: Fork, early: nat)
    requires early <= 2,
    ensures admitted(rule,run(rule,b,early)),
{
    let l = run(rule,b,early);
    prefix_transport_is_enabled(b);
    assert forall|k: int| 0 <= k < l.actions.len() implies {
        let a = #[trigger] l.actions[k]; let n = l.nets[k];
        enabled(n,a) && l.nets[k+1] == advance(|x,w| cell(x,w),n,a)
    } by { transport_edge(rule,b,early,k as nat); }
    assert forall|k: int| 0 <= k < l.actions.len() implies {
        let e = #[trigger] obs(l)[k];
        (r3::machine(rule).accept)(memory(r3::machine(rule),e.actor,obs(l),k as nat),e)
    } by {
        let p = obs(l)[k].actor;
        actual_local(rule,b,early,p,k as nat); handler_edge(rule,b,early,p,k as nat);
    }
}

// Run the unchanged independent-client monitor over each actual timing.
pub open spec fn monitored<M>(rule: Rule<M>, b: Fork, early: nat, k: nat) -> read::State<Local<M>> {
    let base = r3::monitored(rule,b,cursor(early,k));
    read::State { cfg: crate::ordinary_service::Configuration {
        net: net(rule,b,early,k), private: |p| local(rule,b,early,p,k),
    }, ..base }
}

pub open spec fn segment<M>(rule: Rule<M>, b: Fork, early: nat, start: nat, length: nat)
    -> crate::first_assembly::Service<Local<M>>
{
    wait::Path { states: Seq::new(length+1, |j: int| monitored(rule,b,early,(start+j) as nat)),
        actions: actions(rule,b,early).subrange(start as int,(start+length) as int) }
}

proof fn monitored_configuration<M>(rule: Rule<M>, b: Fork, early: nat, k: nat)
    requires early <= 2, k < 30,
    ensures ({
        let m = r3::machine(rule); let a = actions(rule,b,early)[k as int]; let x = monitored(rule,b,early,k);
        crate::ordinary_service::allowed(m,x.cfg,a)
            && crate::ordinary_service::apply(m,x.cfg,a) == monitored(rule,b,early,k+1).cfg
    }),
{
    hide(r3::accepts); hide(r3::update);
    let m = r3::machine(rule); let a = actions(rule,b,early)[k as int];
    let x = monitored(rule,b,early,k); let y = monitored(rule,b,early,k+1);
    let z = crate::ordinary_service::apply(m,x.cfg,a); let e = process_step(x.cfg.net,a);
    transport_edge(rule,b,early,k); handler_edge(rule,b,early,e.actor,k);
    assert(z.private =~= y.cfg.private) by {
        assert forall|p: Process| #[trigger] (z.private)(p) == (y.cfg.private)(p) by { handler_edge(rule,b,early,p,k); }
    }
}

proof fn monitored_step<M>(rule: Rule<M>, b: Fork, early: nat, k: nat)
    requires early <= 2, k < 30,
    ensures ({
        let m = r3::machine(rule); let a = actions(rule,b,early)[k as int];
        let x = monitored(rule,b,early,k); let y = monitored(rule,b,early,k+1);
        read::prefix_step(m)(x,a,y) && (k >= 21+early ==> read::service_step(m)(x,a,y))
    }),
{
    hide(crate::ordinary_service::apply); hide(r3::accepts); hide(r3::update);
    let m = r3::machine(rule); let a = actions(rule,b,early)[k as int];
    let x = monitored(rule,b,early,k); let y = monitored(rule,b,early,k+1);
    let z = read::next(m,x,a);
    monitored_configuration(rule,b,early,k);
    assert(early == 0 || early == 1 || early == 2);
    if k == 17+early { assert(read::retired_at_failure(x) =~= set![2nat,r3::other_copy(b)]); }
    r3::index(k as int);
    assert(z.reserved =~= y.reserved);
}

proof fn reach_invocation<M>(rule: Rule<M>, b: Fork, early: nat)
    requires early <= 2,
    ensures read::reached(r3::machine(rule),crate::early_crash::entry(r3::machine(rule)),monitored(rule,b,early,19+early)),
{
    hide(read::prefix_step); hide(read::service_step);
    let m = r3::machine(rule); let x = monitored(rule,b,early,19+early); let t = segment(rule,b,early,0,19+early);
    let base = crate::early_crash::entry(m);
    prefix_transport_is_enabled(b);
    assert(t.states[0].cfg.private =~= m.initial);
    assert(t.states[0] == base);
    assert forall|i: int| 0 <= i < 19+early implies read::prefix_step(m)(t.states[i],#[trigger] t.actions[i],t.states[i+1])
        by { monitored_step(rule,b,early,i as nat); }
    crate::read_nonblocking::from_path(read::prefix_step(m),read::at_state(x),t,0);
}

pub open spec fn native_quorum<M>(rule: Rule<M>, b: Fork, early: nat) -> bool {
    let m = r3::machine(rule); let q = live_pair(); let res = |s: Local<M>| r3::selected(s);
    let h = segment(rule,b,early,19+early,2); let t = segment(rule,b,early,21+early,(9-early) as nat);
    read::reached(m,crate::early_crash::entry(m),h.states[0])
        && majority::served(majority::Caller::Second,m,res,h,t,q)
        && majority::held(t.states,q,result(rule,run(rule,b,early)).unwrap())
}

pub proof fn retimed_quorum_service<M>(rule: Rule<M>, b: Fork, early: nat)
    requires early <= 2,
    ensures native_quorum(rule,b,early),
{
    hide(read::prefix_step); hide(read::service_step); hide(read::reached); hide(memory);
    let m = r3::machine(rule); let q = live_pair(); let res = |s: Local<M>| r3::selected(s);
    let h = segment(rule,b,early,19+early,2); let t = segment(rule,b,early,21+early,(9-early) as nat);
    reach_invocation(rule,b,early);
    assert forall|i: int| 0 <= i < 2 implies read::prefix_step(m)(h.states[i],#[trigger] h.actions[i],h.states[i+1])
        by { monitored_step(rule,b,early,(19+early+i) as nat); }
    assert forall|i: int| 0 <= i < 9-early implies read::service_step(m)(t.states[i],#[trigger] t.actions[i],t.states[i+1])
        by { monitored_step(rule,b,early,(21+early+i) as nat); }
    assert forall|i: int| 0 <= i < 2 implies !read::returned(res)(#[trigger] h.states[i]) by {};
    assert forall|i: int| 0 <= i < 9-early implies !read::returned(res)(#[trigger] t.states[i]) by {};
    assert(early == 0 || early == 1 || early == 2);
    assert(live(h.states.last().cfg.net,at(site(0))) && live(h.states.last().cfg.net,at(site(1))));
    assert(read::issued_to_majority(h.states.last()));
    assert(majority::sole(h.states[0].cfg.net,q) && majority::sole(t.states.last().cfg.net,q));
    assert(wait::first_return(read::service_step(m),read::returned(res),h.states.last(),t));
    assert(majority::served(majority::Caller::Second,m,res,h,t,q));
    actual_local(rule,b,early,Process::SecondClient,30);
    let member = at_side((site(0),site(1)),local(rule,b,early,Process::SecondClient,30).choice.unwrap());
    assert(q.contains(member) && (t.states.last().cfg.net.locals)(member) == result(rule,run(rule,b,early)).unwrap());
    assert(majority::held(t.states,q,result(rule,run(rule,b,early)).unwrap()));
}

// Restore the original index order only for comparing the actors' tapes.
spec fn native_order(es: Tape, early: nat) -> Tape {
    let h = 10 + early as int; let t = 25 + early as int;
    es.take(h) + es.subrange(t,27) + es.subrange(h,t) + es.skip(27)
}

proof fn client_ignores_moved_receipts<M>(rule: Rule<M>, b: Fork, early: nat, p: Process)
    requires early <= 2, outside_replica(p),
    ensures ({
        let es = obs(run(rule,b,early)); pick(native_order(es,early),p,true) == pick(es,p,true)
    }),
{
    let es = obs(run(rule,b,early));
    let h = 10 + early as int; let t = 25 + early as int;
    let head = es.take(h); let mid = es.subrange(h,t); let late = es.subrange(t,27); let end = es.skip(27);
    if pick(late,p,true).len() > 0 {
        crate::first_splice::picked(late,p,true,0);
        let j = choose|j: int| 0 <= j < late.len() && late[j] == pick(late,p,true)[0];
        assert(t+j == 25 || t+j == 26);
        assert(late[j].actor == at(site((t+j-25) as nat)));
    }
    assert(pick(late,p,true) =~= Seq::empty());
    assert(es =~= head + mid + late + end);
    pick_concat(head,mid,p,true); pick_concat(head+mid,late,p,true); pick_concat(head+mid+late,end,p,true);
    pick_concat(head,late,p,true); pick_concat(head+late,mid,p,true); pick_concat(head+late+mid,end,p,true);
    assert(pick(es,p,true) =~= pick(native_order(es,early),p,true));
}

proof fn same_observations(a: Tape, d: Tape, p: Process)
    requires a.len() == d.len(), forall|i: int| 0 <= i < a.len() ==> {
        let x = #[trigger] a[i]; let y = #[trigger] d[i]; (x.actor == p || y.actor == p) ==> x == y
    },
    ensures pick(a,p,true) == pick(d,p,true),
    decreases a.len(),
{
    if a.len() > 0 {
        let u = a.drop_first(); let v = d.drop_first();
        assert forall|i: int| 0 <= i < u.len() implies {
            let x = #[trigger] u[i]; let y = #[trigger] v[i]; (x.actor == p || y.actor == p) ==> x == y
        } by { assert(u[i] == a[i+1] && v[i] == d[i+1]); }
        same_observations(u,v,p);
    }
}

pub open spec fn client_alignment(a: Log, d: Log) -> bool {
    pick(obs(a),Process::FirstClient,true) == pick(obs(d),Process::FirstClient,true)
        && flow::c2_schedule(a) == flow::c2_schedule(d)
}

proof fn aligned_clients<M>(rule: Rule<M>, b: Fork, early: nat)
    requires early <= 2,
    ensures client_alignment(run(rule,b,early),r3::run(rule,b)),
{
    let l = run(rule,b,early); let n = r3::run(rule,b);
    let a = native_order(obs(l),early); let d = obs(n);
    let c1 = Process::FirstClient; let c2 = Process::SecondClient;
    client_ignores_moved_receipts(rule,b,early,c1); client_ignores_moved_receipts(rule,b,early,c2);
    assert forall|i: int| 0 <= i < a.len() implies {
        let x = #[trigger] a[i]; let y = #[trigger] d[i];
        ((x.actor == c1 || y.actor == c1) ==> x == y)
            && (x.actor == c2) == (y.actor == c2) && (x.actor == c2 ==> x.action == y.action)
    } by { r3::index(i); assert(early == 0 || early == 1 || early == 2); }
    same_observations(a,d,c1); flow::aligned_actions(a,d,c2);
}

pub proof fn all_early_is_native<M>(rule: Rule<M>, b: Fork)
    ensures run(rule,b,2) == r3::run(rule,b),
{
    let l = run(rule,b,2); let n = r3::run(rule,b);
    assert(l.nets =~= n.nets);
    assert(l.actions =~= n.actions);
}

// Decode the actual selected report on the wire. W1 and W2 have distinct
// original cells and neither cell accepts any later write in these logs.
pub open spec fn physical_source<M>(rule: Rule<M>, l: Log) -> Op {
    let end = state(rule,l,Process::SecondClient,l.actions.len());
    let i = if end.choice == Some(Side::Left) { 27int } else { 28int };
    if obs(l)[i].incoming.unwrap().from == at(Replica::R1) { Op::W1 } else { Op::W2 }
}

pub open spec fn result<M>(rule: Rule<M>, l: Log) -> Option<int> {
    flow::result(r3::machine(rule), |s: Local<M>| r3::selected(s), l)
}

// For each sender, check the identity and value at both ends, the queue
// from emission through intake, and the record the client actually uses.
pub open spec fn wires<M>(rule: Rule<M>, b: Fork, early: nat, j: nat) -> bool {
    let l = run(rule,b,early); let es = obs(l);
    let r = site(j); let p = at(r); let id = 9 + j;
    let put = 8 + j as int; let take = receive_index(early,j) as int;
    let out = 23 + early as int + j as int; let intake = 27 + j as int;
    let v = first_value(b); let w = if j == 0 { Op::W1 } else { Op::W2 };
    let q = r3::peer(r,v); let s = state(rule,l,p,out as nat);
    let rec = r3::row(rule,s.memo,crate::next(w,1),true); let reply = r3::answer(r,rec);
    let c2 = state(rule,l,Process::SecondClient,29);
    es[0].incoming == Some(packet_for(b,if b.branch == Branch::Alpha { 1 } else { 0 }))
        && es[0].actor == at(Replica::R3) && (l.nets[1].locals)(Replica::R3) == v
        && (forall|k: int| 1 <= k < put ==> #[trigger] local_input(l.nets[k],l.actions[k],Replica::R3).is_none())
        && es[put].own_local == Some(v) && es[put].action == Action::Send(id,q)
        && (forall|k: int| put < k <= take ==> #[trigger] l.nets[k].pending.get(id) == Some(q))
        && es[take].incoming == Some(q) && es[take].actor == p && es[take].action == Action::<Wire>::Deliver(id)
        && state(rule,l,p,take as nat).memo == rule.empty
        && state(rule,l,p,(take+1) as nat).memo == (rule.remember)(rule.empty,v)
        && s.memo == (if take < out { (rule.remember)(rule.empty,v) } else { rule.empty })
        && s.control.answered_first && s.asked
        && es[out].own_local == Some(crate::next(w,1)) && es[out].action == Action::Send(13+j,reply)
        && (forall|k: int| out < k <= intake ==> #[trigger] l.nets[k].pending.get(13+j) == Some(reply))
        && es[intake].action == Action::<Wire>::Deliver(13+j) && es[intake].incoming == Some(reply)
        && es[intake].actor == Process::SecondClient && r3::record_of(es[intake]) == rec
        && (if j == 0 { c2.left } else { c2.right }) == Some(rec)
}

#[verifier::rlimit(16)]
proof fn follow_wires<M>(rule: Rule<M>, b: Fork, early: nat, j: nat)
    requires early <= 2, j < 2,
    ensures wires(rule,b,early,j),
{
    let l = run(rule,b,early); let put = 8 + j as int;
    let take = receive_index(early,j); let out = 23 + early + j; let intake = 27 + j as int;
    let r = site(j); let p = at(r); let id = 9+j;
    assert(j == 0 || j == 1); assert(early == 0 || early == 1 || early == 2);
    actual_local(rule,b,early,p,take); actual_local(rule,b,early,p,take+1);
    actual_local(rule,b,early,p,out); actual_local(rule,b,early,Process::SecondClient,29);
    assert forall|k: int| 1 <= k < put implies #[trigger] local_input(l.nets[k],l.actions[k],Replica::R3).is_none()
        by { r3::index(k); }
    assert forall|k: int| put < k <= take implies #[trigger] l.nets[k].pending.get(id) == Some(r3::peer(r,first_value(b)))
        by { r3::index(k); }
    assert forall|k: int| out < k <= intake implies #[trigger] l.nets[k].pending.get(13+j) == Some(r3::answer(r,report(rule,b,early,j)))
        by { r3::index(k); }
}

pub open spec fn weak_frame<M>(rule: Rule<M>, b: Fork, early: nat, k: nat) -> bool {
    let l = run(rule,b,early); let n = l.nets[k as int];
    n.locals == l.nets[2].locals && survivor(n) == (2int,5int)
        && (forall|id: nat| #[trigger] weak_at(n,id) == weak_at(l.nets[2],id))
        && (forall|p: Process| {
            let now = #[trigger] state(rule,l,p,k); let old = state(rule,l,p,2);
            now.control.weak_copy == old.control.weak_copy && now.control.learned == old.control.learned
        })
        && (k == 30 || {
            let e = obs(l)[k as int];
            !(e.action is Local) && !(e.action is ClientInput)
                && (e.action is Send ==> e.action->Send_1.path != Path::Weak)
                && (e.incoming.is_some() ==> e.incoming.unwrap().path != Path::Weak)
        })
}

proof fn weak_frame_at<M>(rule: Rule<M>, b: Fork, early: nat, k: nat)
    requires early <= 2, 2 <= k <= 30,
    ensures weak_frame(rule,b,early,k),
{
    let l = run(rule,b,early);
    assert(early == 0 || early == 1 || early == 2);
    if k < 30 { r3::index(k as int); }
    assert(l.nets[k as int].locals =~= l.nets[2].locals);
    assert forall|id: nat| #[trigger] weak_at(l.nets[k as int],id) == weak_at(l.nets[2],id) by {};
    assert forall|p: Process| {
        let now = #[trigger] state(rule,l,p,k); let old = state(rule,l,p,2);
        now.control.weak_copy == old.control.weak_copy && now.control.learned == old.control.learned
    } by { actual_local(rule,b,early,p,k); actual_local(rule,b,early,p,2); }
}
// Index of an original event in the physical log. Only receipts 9 and 10
// move. All other events retain their original relative order.
pub open spec fn at_time(early: nat, i: int) -> int {
    if i < 10 + early || i >= 27 { i } else if i < 12 { i+15 } else { i + early - 2 }
}

pub open spec fn same_report(x: Observation, y: Observation, j: nat, outgoing: bool) -> bool {
    let r = site(j); let id = 13+j;
    let a = if outgoing { x.action->Send_1 } else { x.incoming.unwrap() };
    let d = if outgoing { y.action->Send_1 } else { y.incoming.unwrap() };
    a == r3::answer(r,(a.input->StampedAnswer_0,a.input->StampedAnswer_1))
        && d == r3::answer(r,(a.input->StampedAnswer_0,d.input->StampedAnswer_1))
        && x.actor == y.actor && x.own_local == y.own_local
        && (if outgoing {
            x.actor == at(r) && x.action == Action::Send(id,a) && y.action == Action::Send(id,d)
                && x.incoming.is_none() && y.incoming.is_none()
        } else {
            x.actor == Process::SecondClient && x.action == Action::<Wire>::Deliver(id) && y.action == x.action
                && x.incoming == Some(a) && y.incoming == Some(d)
        })
}

pub open spec fn aligned_callback(old: Log, new: Log, j: nat, i: int) -> bool {
    let x = obs(old)[at_time(j,i)]; let y = obs(new)[at_time(j+1,i)];
    if i == 25+j { same_report(x,y,j,true) } else if i == 27+j { same_report(x,y,j,false) } else { x == y }
}

// An observable, one-receipt intervention. Both runs use the same program
// and entry. At matched callbacks only the affected report's header may
// differ (including at its intake). Client schedules are also compared in
// their actual order. Eligibility makes no requirement about who wins.
pub open spec fn controlled<M>(rule: Rule<M>, j: nat, old: Log, new: Log) -> bool {
    j < 2 && admitted(rule,old) && admitted(rule,new) && old.nets[0] == new.nets[0]
        && old.actions.len() == 30 && new.actions.len() == 30 && client_alignment(old,new)
        && (forall|i: int| 0 <= i < 30 ==> #[trigger] aligned_callback(old,new,j,i))
        && old.actions[25+j as int] == Action::<Wire>::Deliver(9+j)
        && new.actions[10+j as int] == Action::<Wire>::Deliver(9+j)
}

proof fn callback_alignment<M>(rule: Rule<M>, b: Fork, j: nat, i: int)
    requires j < 2, 0 <= i < 30,
    ensures aligned_callback(run(rule,b,j),run(rule,b,j+1),j,i),
{
    r3::index(i);
    assert(j == 0 || j == 1);
}

proof fn one_receipt_comparison<M>(rule: Rule<M>, b: Fork, j: nat)
    requires j < 2,
    ensures controlled(rule,j,run(rule,b,j),run(rule,b,j+1)),
{
    hide(admitted); hide(aligned_callback); hide(flow::c2_schedule); hide(pick);
    let a = run(rule,b,j); let d = run(rule,b,j+1);
    retimed_service_executes(rule,b,j); retimed_service_executes(rule,b,j+1);
    aligned_clients(rule,b,j); aligned_clients(rule,b,j+1);
    assert(j == 0 || j == 1);
    assert forall|i: int| 0 <= i < 30 implies #[trigger] aligned_callback(a,d,j,i)
        by { callback_alignment(rule,b,j,i); }
}

pub open spec fn probes<M>(rule: Rule<M>, b: Fork) -> Seq<Log> {
    Seq::new(3, |j: int| run(rule,b,j as nat))
}

pub open spec fn prefix_result<M>(rule: Rule<M>, l: Log, early: nat) -> Option<int> {
    let ctrl = state(rule,l,Process::FirstClient,16+early).control;
    if ctrl.finished { ctrl.reply } else { None }
}

// The selected source is authenticated by sender and sampled cell. Its
// relation to the native retention cuts is a consequence of the transitions.
pub proof fn sample_from_wire<M>(rule: Rule<M>, b: Fork, early: nat)
    requires early <= 2,
    ensures ({
        let l = run(rule,b,early); let c = Process::SecondClient;
        let native = r3::run(rule,b); let src = physical_source(rule,l);
        let s = state(rule,l,c,30); let cut = r3::memos(rule,b,10+early);
        let elected = r3::elect_at(rule,r3::contest(native),cut);
        admitted(rule,l) && prefix_result(rule,l,early) == Some(first_value(b))
            && l.actions[16+early as int] == Action::StopFirstClient
            && l.actions[17+early as int] == Action::CrashR3 && l.actions[18+early as int] == Action::StartSecondClient
            && state(rule,l,c,18+early) == (r3::machine(rule).initial)(c)
            && s.control.sent_requests == live_pair() && crate::hybrid_majority::sole(l.nets[30],live_pair())
            && wires(rule,b,early,0) && wires(rule,b,early,1)
            && (forall|k: nat| 2 <= k <= 30 ==> #[trigger] weak_frame(rule,b,early,k))
            && r3::contest(l) == r3::contest(native) && s.choice == Some(elected)
            && src == at_side(precedence::source_versions(),elected) && result(rule,l) == Some(crate::next(src,1))
            && result(rule,l) == Some((l.nets[29].locals)(at_side((site(0),site(1)),elected)))
    }),
{
    hide(admitted); hide(wires); hide(weak_frame); hide(memory);
    let l = run(rule,b,early); let c = Process::SecondClient;
    assert(early == 0 || early == 1 || early == 2);
    retimed_service_executes(rule,b,early);
    follow_wires(rule,b,early,0); follow_wires(rule,b,early,1);
    actual_local(rule,b,early,c,18+early); actual_local(rule,b,early,c,30);
    actual_local(rule,b,early,Process::FirstClient,16+early);
    r3::actual_local(rule,b,at(site(0)),10+early); r3::actual_local(rule,b,at(site(1)),10+early);
    assert forall|k: nat| 2 <= k <= 30 implies #[trigger] weak_frame(rule,b,early,k) by { weak_frame_at(rule,b,early,k); }
}

pub proof fn wire_history_test<M>(rule: Rule<M>, b: Fork, early: nat, prefix: RecoveredOrder)
    requires early <= 2, history::legal_first(prefix,first_value(b)),
    ensures ({
        let l = run(rule,b,early); let f = prefix_result(rule,l,early).unwrap(); let v = result(rule,l).unwrap();
        history::can_keep(prefix.ops,observed_writer(b),physical_source(rule,l))
            == (exists|g: RecoveredOrder| #[trigger] crate::legal(g.ops,g.states,f,v))
    }),
{
    hide(admitted); hide(wires); hide(weak_frame); hide(result); hide(physical_source); hide(prefix_result);
    let l = run(rule,b,early);
    sample_from_wire(rule,b,early);
    history::history_test_is_exact(b,prefix,physical_source(rule,l));
}

pub open spec fn policy<M>(rule: Rule<M>, b: Fork, old: RecoveredOrder, credit: precedence::Credit) -> bool {
    let l = r3::run(rule,b);
    history::history_clause(old.ops,seq![10int,11int],|i: int| r3::source(l,i),probes(rule,b),
        |i: int, a: Log, d: Log| controlled(rule,(i-10) as nat,a,d), |p: Log| physical_source(rule,p),
        r3::independent(rule,b),credit)
}

pub proof fn physical_history_bridge<M>(rule: Rule<M>, branch: Branch, prefix: RecoveredOrder, credit: precedence::Credit)
    requires history::legal_first(prefix,first_value(r3::fork(branch))),
    ensures ({
        let b = r3::fork(branch); let ps = probes(rule,b);
        policy(rule,b,prefix,credit) == r3::audit(rule,b,credit)
            && ps[2] == r3::run(rule,b)
            && controlled(rule,0,ps[0],ps[1]) && controlled(rule,1,ps[1],ps[2])
    }),
{
    hide(history::history_clause); hide(flow::supported_retention); hide(history::legal_first);
    hide(r3::run); hide(run); hide(r3::state); hide(state); hide(r3::independent);
    hide(r3::native_quorum); hide(r3::weak_entry); hide(r3::admitted); hide(r3::calls); hide(r3::weak_frame);
    hide(admitted); hide(controlled); hide(wires); hide(weak_frame); hide(r3::forwarded);
    hide(r3::source); hide(r3::elect_at); hide(r3::contest); hide(r3::memos); hide(physical_source);
    let b = r3::fork(branch); let l = r3::run(rule,b); let steps = seq![10int,11int];
    let cuts = seq![r3::memos(rule,b,10),r3::memos(rule,b,11),r3::memos(rule,b,12)];
    let ps = probes(rule,b);
    let from = |i: int| r3::source(l,i);
    let eligible = |i: int, a: Log, d: Log| controlled(rule,(i-10) as nat,a,d);
    let read_from = |p: Log| physical_source(rule,p);
    let elect = |m: (M,M)| r3::elect_at(rule,r3::contest(l),m);
    all_early_is_native(rule,b);
    r3::paired_trace_arm(rule,branch);
    assert(from(10) == Some(observed_writer(b)) && from(11) == Some(observed_writer(b))) by {
        reveal(r3::forwarded);
    }
    one_receipt_comparison(rule,b,0); one_receipt_comparison(rule,b,1);
    assert forall|j: int| 0 <= j < steps.len() implies {
        let e = #[trigger] steps[j];
        eligible(e,ps[j],ps[j+1]) && (from(e).is_none() || from(e) == Some(observed_writer(b)))
    } by { assert(j == 0 || j == 1); }
    assert forall|j: int| 0 <= j < cuts.len() implies
        #[trigger] read_from(ps[j]) == at_side(precedence::source_versions(),elect(cuts[j])) by {
        assert(j == 0 || j == 1 || j == 2); sample_from_wire(rule,b,j as nat);
    }
    history::history_clause_iff_supported_retention(b,prefix,steps,cuts,from,ps,eligible,read_from,elect,r3::independent(rule,b),credit);
}

pub proof fn h_requires_history_gain<M>(rule: Rule<M>, credit: precedence::Credit,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>)
    requires r3::explains(rule,r3::fork(Branch::Alpha),ao,ax), r3::explains(rule,r3::fork(Branch::Beta),bo,bx),
        precedence::sound_credit(credit,precedence::actual_cuts(Notice::Replication,false,false)),
    ensures ({
        let a = r3::fork(Branch::Alpha); let b = r3::fork(Branch::Beta);
        !policy(rule,a,history::at_first(a),credit) || !policy(rule,b,history::at_first(b),credit)
    }),
{
    hide(policy); hide(r3::audit); hide(r3::explains);
    let a = r3::fork(Branch::Alpha); let b = r3::fork(Branch::Beta);
    history::canonical_orders_exist(a); history::canonical_orders_exist(b);
    physical_history_bridge(rule,Branch::Alpha,history::at_first(a),credit);
    physical_history_bridge(rule,Branch::Beta,history::at_first(b),credit);
    r3::h_forces_retained_source_use(rule,credit,ao,ax,bo,bx);
}
proof fn alpha_reports()
    ensures ({
        let b = r3::fork(Branch::Alpha); let rule = r3::value_cache(true);
        let old = run(rule,b,1); let new = run(rule,b,2); let r2 = at(Replica::R2);
        state(rule,old,r2,25).memo == None && state(rule,new,r2,26).memo == Some(5)
            && r3::record_of(obs(old)[28]).1 == 0 && r3::record_of(obs(new)[28]).1 == 1
            && state(rule,old,r2,30).memo == Some(5) && state(rule,new,r2,30).memo == Some(5)
            && physical_source(rule,old) == Op::W1 && result(rule,old) == Some(2)
            && physical_source(rule,new) == Op::W2 && result(rule,new) == Some(5)
    }),
{
    hide(memory);
    let rule = r3::value_cache(true); let b = r3::fork(Branch::Alpha); let r2 = at(Replica::R2);
    actual_local(rule,b,1,r2,25); actual_local(rule,b,2,r2,26);
    actual_local(rule,b,1,r2,30); actual_local(rule,b,2,r2,30);
    actual_local(rule,b,1,Process::SecondClient,30); actual_local(rule,b,2,Process::SecondClient,30);
}

// A cache with no weak provenance in its interface. Move only R2's
// receipt in alpha. Test legality of each completion against its own
// independent SR1 prefix; only the native completion admits an H order.
pub proof fn cache_preserves_observed_history()
    ensures ({
        let b = r3::fork(Branch::Alpha); let rule = r3::value_cache(true);
        let old = run(rule,b,1); let new = run(rule,b,2); let h = history::at_first(b); let full = history::at_second(b);
        let r2 = at(Replica::R2); let w = Op::W2;
        new == r3::run(rule,b) && r3::native_quorum(rule,b) && r3::weak_entry(rule,b)
            && native_quorum(rule,b,1) && native_quorum(rule,b,2)
            && controlled(rule,1,old,new) && wires(rule,b,1,1) && wires(rule,b,2,1)
            && prefix_result(rule,old,1) == Some(5) && prefix_result(rule,new,2) == Some(5)
            && weak_assignment(b,false).ops.len() == 0 && truthful_notice(b,weak_assignment(b,false).ops)
            && (forall|k: nat| 2 <= k <= 30 ==> #[trigger] weak_frame(rule,b,1,k) && #[trigger] weak_frame(rule,b,2,k))
            && state(rule,old,r2,25).memo == None && state(rule,new,r2,26).memo == Some(5)
            && r3::record_of(obs(old)[28]).1 == 0 && r3::record_of(obs(new)[28]).1 == 1
            && state(rule,old,r2,30).memo == Some(5) && state(rule,new,r2,30).memo == Some(5)
            && physical_source(rule,old) == Op::W1 && result(rule,old) == Some(2)
            && physical_source(rule,new) == w && result(rule,new) == Some(5)
            && history::legal_first(h,5) && history::reads_from(h.ops,Op::SR1,w)
            && history::same_weak_order(h.ops,full.ops) && history::extension(h.ops,w,physical_source(rule,new),full)
            && crate::legal(full.ops,full.states,prefix_result(rule,new,2).unwrap(),result(rule,new).unwrap())
            && !history::can_keep(h.ops,w,physical_source(rule,old))
            && (forall|o: Seq<Op>, xs: Seq<int>|
                !#[trigger] crate::legal(o,xs,prefix_result(rule,old,1).unwrap(),result(rule,old).unwrap()))
            && !policy(rule,b,h,r3::no_credit())
    }),
{
    hide(native_quorum);
    hide(run); hide(r3::run); hide(state); hide(result); hide(physical_source); hide(prefix_result); hide(obs);
    hide(history::can_keep); hide(history::reads_from); hide(history::same_weak_order); hide(history::restricts_to);
    hide(r3::calls); hide(r3::pivotal); hide(r3::explains); hide(r3::forwarded); hide(r3::admitted);
    hide(r3::weak_frame); hide(r3::memos); hide(r3::second); hide(r3::state); hide(r3::elect_at);
    hide(admitted); hide(wires); hide(weak_frame); hide(r3::native_quorum); hide(controlled);
    hide(policy); hide(r3::audit); hide(r3::weak_entry);
    let b = r3::fork(Branch::Alpha); let rule = r3::value_cache(true); let r2 = at(Replica::R2);
    let old = run(rule,b,1); let new = run(rule,b,2);
    let h = history::at_first(b); let g = history::at_second(b);
    history::canonical_orders_exist(b); r3::paired_trace_arm(rule,Branch::Alpha); r3::value_cache_witness(Branch::Alpha);
    physical_history_bridge(rule,Branch::Alpha,h,r3::no_credit());
    sample_from_wire(rule,b,1); sample_from_wire(rule,b,2);
    retimed_quorum_service(rule,b,1); retimed_quorum_service(rule,b,2);
    alpha_reports();
    history::extension_iff_writer(b,h,Op::W1);
    history::canonical_extension(b);
    assert forall|o: Seq<Op>, xs: Seq<int>|
        !#[trigger] crate::legal(o,xs,prefix_result(rule,old,1).unwrap(),result(rule,old).unwrap()) by {
        if crate::legal(o,xs,5,2) { crate::legal_history_keeps_first_read(o,xs,5,2); }
    }
}

// If both receivers sample before either peer receipt, arbitrary encodings
// start empty on both forks. Thus no member of this service family can meet
// H on every one of its admitted schedules, regardless of how T is read.
pub proof fn delayed_pair_cannot_both_satisfy_h<M>(rule: Rule<M>,
    ao: Seq<Op>, ax: Seq<int>, bo: Seq<Op>, bx: Seq<int>)
    ensures ({
        let a = r3::fork(Branch::Alpha); let b = r3::fork(Branch::Beta);
        let x = run(rule,a,0); let y = run(rule,b,0);
        admitted(rule,x) && admitted(rule,y)
            && prefix_result(rule,x,0) == Some(5) && prefix_result(rule,y,0) == Some(2)
            && physical_source(rule,x) == physical_source(rule,y) && result(rule,x) == result(rule,y)
            && (!crate::legal(ao,ax,5,result(rule,x).unwrap()) || !crate::legal(bo,bx,2,result(rule,y).unwrap()))
    }),
{
    hide(admitted); hide(wires); hide(weak_frame);
    let a = r3::fork(Branch::Alpha); let b = r3::fork(Branch::Beta);
    let x = run(rule,a,0); let y = run(rule,b,0);
    sample_from_wire(rule,a,0); sample_from_wire(rule,b,0);
    actual_local(rule,a,0,Process::SecondClient,30); actual_local(rule,b,0,Process::SecondClient,30);
    if crate::legal(ao,ax,5,result(rule,x).unwrap()) && crate::legal(bo,bx,2,result(rule,y).unwrap()) {
        crate::legal_history_keeps_first_read(ao,ax,5,result(rule,x).unwrap());
        crate::legal_history_keeps_first_read(bo,bx,2,result(rule,y).unwrap());
    }
}
// Reuse the native all-early traces to exercise the arbitrary-program
// certificate checker. All offered messages, including the other branch's
// candidates, go through the actual guard. No fair-run premise is needed.
pub open spec fn cache_lanes() -> asm::Lanes {map![2nat=>Replica::R3,3nat=>Replica::R1,4nat=>Replica::R2]}
pub open spec fn cache_tapes<M>(r:Rule<M>,b:Fork) -> alternatives::Tapes {
    let t=obs(r3::run(r,b));alternatives::Tapes{replicas:t.subrange(5,15),caller:t.subrange(15,18)}
}

proof fn native_slice<M>(r:Rule<M>,b:Fork,i:nat,k:nat)
    requires i<=k<=30,
    ensures ({
        let m=r3::machine(r);let x=r3::monitored(r,b,i);let y=r3::monitored(r,b,k);
        let acts=r3::actions(r,b).subrange(i as int,k as int);let t=obs(r3::run(r,b)).subrange(i as int,k as int);
        asm::prefix(m,x,acts,true) && asm::drive(m,x,acts)==y && asm::actions(t)==acts
            && (5<=i && k<=18 ==> tape::plays(m,x,t) && tape::after(m,x,t)==y)
    }),
    decreases k-i,
{
    let m=r3::machine(r);let x=r3::monitored(r,b,i);let log=r3::run(r,b);
    let a=log.actions.subrange(i as int,k as int);let t=obs(log).subrange(i as int,k as int);
    assert(asm::actions(t) =~= a);
    if i<k {
        r3::monitored_edge(r,b,i);r3::index(i as int);
        if i==18 {r3::actual_local(r,b,Process::FirstClient,18);}
        assert(t[0]==process_step(x.cfg.net,a[0]));
        assert(a.drop_first() =~= log.actions.subrange(i as int+1,k as int));
        assert(t.drop_first() =~= obs(log).subrange(i as int+1,k as int));
        native_slice(r,b,i+1,k);
    }
}

proof fn cache_root<M>(r:Rule<M>,b:Fork)
    ensures asm::entry(r3::machine(r),cache_lanes())==r3::monitored(r,b,0),
        crate::coupled_construction::root(r3::machine(r),cache_lanes(),b)==r3::monitored(r,b,5),
{
    hide(r3::machine);hide(r3::sample_row);
    let m=r3::machine(r);let l=cache_lanes();let root=crate::coupled_construction::root(m,l,b);let log=r3::run(r,b);
    assert(log.nets[0]==after_local_rmws()) by {r3::value_service_executes(r,b);}
    assert(asm::owners(l) =~= r3::monitored(r,b,0).owners);
    assert(r3::monitored(r,b,0).cfg.private =~= m.initial);
    assert(asm::entry(m,l)==r3::monitored(r,b,0));
    assert forall|i:int| 0<=i<5 implies #[trigger] obs(log)[i]==checkpoint_observations(b)[i] by {prefix_index(i);}
    assert(root.cfg.private =~= r3::monitored(r,b,5).cfg.private) by {
        assert forall|p:Process| #[trigger] (root.cfg.private)(p)==(r3::monitored(r,b,5).cfg.private)(p)
            by {memory_on_common_prefix(m,p,obs(log),checkpoint_observations(b),5);}
    }
    assert(root.cfg.net.pending =~= r3::monitored(r,b,5).cfg.net.pending);assert(root==r3::monitored(r,b,5));
}

proof fn cache_mailbox<M>(r:Rule<M>,b:Fork)
    ensures ({
        let m=r3::machine(r);let t=cache_tapes(r,b);let c=t.caller;let z=r3::monitored(r,b,15);let u=r3::monitored(r,b,18);let cc=Process::FirstClient;
        crate::coupled_reads::client_change(z,u,c) && crate::first_causality::pending_inputs(m,(z.cfg.private)(cc),c)
            && crate::first_mailbox::posted(m)(u) && (u.cfg.private)(cc).control.reply==Some(first_value(b))
            && crate::coupled_construction::heard(c,crate::origin(b.branch)) && crate::coupled_construction::heard(c,Replica::R3)
            && forall|j:int| 0<=j<c.len() ==> {let e=#[trigger] c[j];e.actor==cc && !(e.action is Send)
                && (e.incoming.is_some() ==> e.incoming.unwrap().from==at(crate::origin(b.branch)) || e.incoming.unwrap().from==at(Replica::R3))}
    }),
{
    let m=r3::machine(r);let branch=b.branch;let t=cache_tapes(r,b);let log=r3::run(r,b);let cc=Process::FirstClient;
    let z=r3::monitored(r,b,15);let u=r3::monitored(r,b,18);
    native_slice(r,b,15,18);
    assert forall|j:int| 0<=j<t.caller.len() implies {
        let e=#[trigger] t.caller[j];e.actor==cc && !(e.action is Send)
            && (e.incoming.is_some() ==> e.incoming.unwrap().from==at(crate::origin(branch)) || e.incoming.unwrap().from==at(Replica::R3))
            && (e.action is Deliver ==> z.cfg.net.pending.get(e.action->Deliver_0)==e.incoming)
    } by {assert(j==0 || j==1 || j==2);}
    assert(crate::coupled_reads::client_inputs(t.caller)) by {
        assert forall|j:int,k:int| 0<=j<k<t.caller.len() && (#[trigger] t.caller[j]).action is Deliver implies
            (#[trigger] t.caller[k]).action!=t.caller[j].action by {assert(j==0 || j==1);assert(k==1 || k==2);}
    }
    crate::coupled_reads::play_client(m,z,z,t.caller);
    r3::actual_local(r,b,cc,15);r3::actual_local(r,b,cc,18);
    reveal_with_fuel(crate::first_causality::pending_inputs,4);
    assert(crate::coupled_construction::heard(t.caller,crate::origin(branch))) by {assert(t.caller[0]==obs(log)[15]);}
    assert(crate::coupled_construction::heard(t.caller,Replica::R3)) by {assert(t.caller[1]==obs(log)[16]);}
}

proof fn cache_slice_facts<M>(r:Rule<M>,b:Fork)
    ensures ({
        let t=cache_tapes(r,b);let log=r3::run(r,b);let prefix=crate::coupled_construction::prefix_actions(b,t.replicas,t.caller);
        prefix==log.actions.subrange(0,18) && prefix+crate::first_pair::close(true)==log.actions.subrange(0,23)
            && crate::first_pair::close(true)==log.actions.subrange(18,23)
            && crate::coupled_traffic::fitted(t.replicas,|_e:Observation|true)
            && (forall|j:int| 0<=j<t.replicas.len() ==> crate::independent_preparations::ordinary_input(#[trigger] t.replicas[j]))
            && crate::coupled_traffic::weak_queue(r3::monitored(r,b,18),b) && crate::coupled_traffic::weak_queue(r3::monitored(r,b,23),b)
            && r3::monitored(r,b,23).cfg.net.locals==state_after(b,5).locals
    }),
{
    let t=cache_tapes(r,b);let log=r3::run(r,b);
    native_slice(r,b,5,15);native_slice(r,b,15,18);
    let prefix=crate::coupled_construction::prefix_actions(b,t.replicas,t.caller);
    assert(prefix =~= log.actions.take(18));assert(log.actions.take(18) =~= log.actions.subrange(0,18));
    assert(crate::first_pair::close(true) =~= log.actions.subrange(18,23));
    assert(prefix+crate::first_pair::close(true) =~= log.actions.subrange(0,23));
    assert forall|j:int| 0<=j<t.replicas.len() implies crate::independent_preparations::ordinary_input(#[trigger] t.replicas[j])
        by {r3::index(j+5);}
    assert forall|id:nat| id<=2 implies #[trigger] r3::monitored(r,b,18).cfg.net.pending.get(id)==state_after(b,5).pending.get(id)
        && r3::monitored(r,b,23).cfg.net.pending.get(id)==state_after(b,5).pending.get(id) by {assert(id==0 || id==1 || id==2);}
}

proof fn native_arm<M>(r:Rule<M>,branch:Branch)
    ensures ({
        let m=r3::machine(r);let l=cache_lanes();let b=r3::fork(branch);let t=cache_tapes(r,b);
        alternatives::admitted(m,|s:Local<M>|s.control.reply.unwrap(),|s:Local<M>|r3::selected(s),l,b,t)
            && alternatives::cut(m,l,b,t)==r3::monitored(r,b,23) && crate::coupled_construction::root(m,l,b)==r3::monitored(r,b,5)
    }),
{
    hide(r3::monitored);hide(r3::run);hide(r3::actions);hide(obs);hide(memory);hide(r3::machine);
    hide(crate::coupled_traffic::weak_queue);hide(crate::coupled_traffic::fitted);hide(crate::independent_preparations::ordinary_input);
    hide(r3::calls);hide(r3::weak_entry);hide(r3::admitted);hide(r3::weak_frame);hide(r3::forwarded);
    hide(crate::first_causality::pending_inputs);hide(crate::coupled_reads::client_change);
    hide(tape::plays);hide(tape::after);hide(asm::drive);hide(asm::prefix);
    let m=r3::machine(r);let l=cache_lanes();let b=r3::fork(branch);let t=cache_tapes(r,b);let log=r3::run(r,b);
    let z=r3::monitored(r,b,15);let u=r3::monitored(r,b,18);let x=r3::monitored(r,b,23);
    let root=crate::coupled_construction::root(m,l,b);let cc=Process::FirstClient;
    r3::paired_trace_arm(r,branch);
    cache_root(r,b);
    assert(log.actions==r3::actions(r,b)) by {reveal(r3::run);}
    native_slice(r,b,0,18);native_slice(r,b,0,23);native_slice(r,b,5,15);native_slice(r,b,15,18);native_slice(r,b,18,23);
    cache_slice_facts(r,b);
    cache_mailbox(r,b);
    crate::coupled_construction::prepared_frame(m,l,b,t.replicas);
    assert(crate::coupled_construction::prepared(m,l,b,t.replicas)==z);
    assert(crate::coupled_construction::first_end(m,l,b,t.replicas,t.caller)==u);
    assert(alternatives::cut(m,l,b,t)==x);
    assert(crate::first_pair::before_issue(m,u,l)) by {
        reveal(crate::coupled_reads::client_change);
        assert(u.cfg.net.pending.get(11)==if crate::coupled_reads::takes(t.caller,11){None}else{z.cfg.net.pending.get(11)});
        assert(u.cfg.net.pending.get(12)==if crate::coupled_reads::takes(t.caller,12){None}else{z.cfg.net.pending.get(12)});
        assert((u.cfg.private)(Process::SecondClient)==(z.cfg.private)(Process::SecondClient));
    }
    crate::first_pair::close_at(m,|s:Local<M>|r3::selected(s),l,u,true);
    assert(crate::first_splice::same_locals(z,x,crate::first_pair::sites())) by {
        reveal(crate::coupled_reads::client_change);
        assert forall|p:Process| crate::first_pair::sites().contains(p) implies #[trigger] (z.cfg.private)(p)==(x.cfg.private)(p)
            by {assert(p!=cc);assert((z.cfg.private)(p)==(u.cfg.private)(p));}
    }
}

pub open spec fn offers<M>(r:Rule<M>,i:nat,k:nat) -> Seq<Event>
    decreases k-i,
{
    if i>=k {Seq::empty()} else {
        let a=r3::actions(r,r3::fork(Branch::Alpha))[i as int];let b=r3::actions(r,r3::fork(Branch::Beta))[i as int];
        (if a==b {seq![a]} else {seq![a,b]})+offers(r,i+1,k)
    }
}

proof fn paired_offers<M>(r:Rule<M>,branch:Branch,i:nat,k:nat)
    requires i<=k,(5<=i && k<=15 || 23<=i && k<=30),
    ensures ({
        let m=r3::machine(r);let b=r3::fork(branch);let x=r3::monitored(r,b,i);let s=offers(r,i,k);
        let g=if k<=15 {cmp::prepare()} else {cmp::second(true,|s:Local<M>|r3::selected(s))};
        cmp::fired(m,g,x,s)==obs(r3::run(r,b)).subrange(i as int,k as int) && cmp::end(m,g,x,s)==r3::monitored(r,b,k)
    }),
    decreases k-i,
{
    let m=r3::machine(r);let b=r3::fork(branch);let x=r3::monitored(r,b,i);let y=r3::monitored(r,b,i+1);let s=offers(r,i,k);
    let g=if k<=15 {cmp::prepare()} else {cmp::second(true,|s:Local<M>|r3::selected(s))};
    let es=obs(r3::run(r,b));let t=es.subrange(i as int,k as int);
    if i==k {assert(t =~= Seq::empty());return;}
    let a=r3::actions(r,r3::fork(Branch::Alpha))[i as int];let d=r3::actions(r,r3::fork(Branch::Beta))[i as int];
    let native=r3::actions(r,b)[i as int];r3::monitored_edge(r,b,i);r3::index(i as int);
    r3::actual_local(r,b,Process::SecondClient,i);assert(cmp::ready(m,g,x,native));
    let tail=offers(r,i+1,k);paired_offers(r,branch,i+1,k);
    if a==d {
        assert(s.drop_first() =~= tail);cmp::scan_step(m,g,x,s);
    } else {
        assert(a is Send && d is Send && a->Send_0==d->Send_0);
        let e=process_step(x.cfg.net,a);r3::actual_local(r,b,e.actor,i);
        if branch==Branch::Alpha {assert(!cmp::ready(m,g,y,d));} else {assert(!cmp::ready(m,g,x,a));}
        assert(s.drop_first() =~= seq![d]+tail);assert(s.drop_first().drop_first() =~= tail);
        cmp::scan_step(m,g,x,s);cmp::scan_step(m,g,cmp::attempt(m,g,x,a),s.drop_first());
        reveal_with_fuel(cmp::fired,2);
    }
    assert(t =~= seq![es[i as int]]+es.subrange(i as int+1,k as int));
}

proof fn cache_arm_certificate(br:Branch)
    ensures ({
        let r=r3::value_cache(true);let m=r3::machine(r);let l=cache_lanes();
        let first=|s:Local<Option<int>>|s.control.reply.unwrap();let res=|s:Local<Option<int>>|r3::selected(s);
        let pre=offers(r,5,15);let post=offers(r,23,30);
        let key=r3::fork(br);let t=cache_tapes(r,key);let x=alternatives::cut(m,l,key,t);
        alternatives::admitted(m,first,res,l,key,t) && cmp::fired(m,cmp::prepare(),crate::coupled_construction::root(m,l,key),pre)==t.replicas
            && alternatives::sampled(true,m,res,l,key,t,post) && alternatives::outcome(true,m,res,x,post)==Some(first_value(key))
    }),
{
        let r=r3::value_cache(true);let m=r3::machine(r);let l=cache_lanes();
        let first=|s:Local<Option<int>>|s.control.reply.unwrap();let res=|s:Local<Option<int>>|r3::selected(s);
        let pre=offers(r,5,15);let post=offers(r,23,30);
        let key=r3::fork(br);let t=cache_tapes(r,key);let x=alternatives::cut(m,l,key,t);
        native_arm(r,br);r3::value_cache_witness(br);paired_offers(r,br,5,15);paired_offers(r,br,23,30);
        cmp::returned_run(true,m,res,key,x,post);
        let p=cmp::path(m,x,cmp::fired(m,cmp::second(true,res),x,post));
        assert(p.states[0]==x);assert(live_pair().contains(crate::origin(br)));
        assert((x.cfg.net.locals)(crate::origin(br))==first_value(key));
        assert(majority::held(p.states,live_pair(),first_value(key)));
    }

// The exact existing cache run realizes the general controlled-use branch.
// This finite check uses no global hybrid availability or fairness.
pub proof fn cache_realizes_controlled_fork()
    ensures ({
        let r=r3::value_cache(true);let l=cache_lanes();let m=r3::machine(r);let n=Notice::Replication;
        let first=|s:Local<Option<int>>|s.control.reply.unwrap();let res=|s:Local<Option<int>>|r3::selected(s);
        let a=cache_tapes(r,alpha(n));let b=cache_tapes(r,beta(n));let pre=offers(r,5,15);let post=offers(r,23,30);
        let x=alternatives::cut(m,l,alpha(n),a);let y=alternatives::cut(m,l,beta(n),b);
        let c=info::caller2(x);let ra=info::live_view(x);let rb=info::live_view(y);
        let inputs=ISet::empty().insert(post);let orders=precedence::actual_cuts(n,false,false);
        alternatives::candidate(m,first,res,l,n,a,b) && alternatives::aligned(m,l,n,a,b,pre)
            && alternatives::sampled(true,m,res,l,alpha(n),a,post) && alternatives::sampled(true,m,res,l,beta(n),b,post)
            && alternatives::controlled_use(true,m,res,l,n,a,b,pre,post)
            && retained_order::record_enables_observed_order(m,res,alpha(n),c,ra,rb,inputs,post,orders)
            && retained_order::record_enables_observed_order(m,res,beta(n),c,rb,ra,inputs,post,orders)
            && (forall|k:nat| 2<=k<=30 ==> #[trigger] weak_frame(r,alpha(n),2,k) && #[trigger] weak_frame(r,beta(n),2,k))
            && policy(r,beta(n),history::at_first(beta(n)),r3::no_credit())
            && !alternatives::supported(beta(n),Some(2),Some(5),r3::no_credit())
    }),
{
    hide(retained_order::record_enables_observed_order); hide(weak_frame);
    let n=Notice::Replication;let r=r3::value_cache(true);let m=r3::machine(r);let l=cache_lanes();
    let first=|s:Local<Option<int>>|s.control.reply.unwrap();let res=|s:Local<Option<int>>|r3::selected(s);
    let a=cache_tapes(r,alpha(n));let b=cache_tapes(r,beta(n));let pre=offers(r,5,15);let post=offers(r,23,30);
    cache_arm_certificate(Branch::Alpha);cache_arm_certificate(Branch::Beta);
    history::canonical_orders_exist(alpha(n));history::canonical_orders_exist(beta(n));
    assert(crate::coupled_reads::legal_returns(5,5)) by {let h=history::at_second(alpha(n));assert(crate::legal(h.ops,h.states,5,5));}
    assert(crate::coupled_reads::legal_returns(2,2)) by {let h=history::at_second(beta(n));assert(crate::legal(h.ops,h.states,2,2));}
    let inputs=ISet::empty().insert(post);
    let x=alternatives::cut(m,l,alpha(n),a);let y=alternatives::cut(m,l,beta(n),b);
    assert(!retained_order::history_failure(m,res,alpha(n),x,inputs));
    assert(!retained_order::history_failure(m,res,beta(n),y,inputs));
    retained_order::original_fork_requires_preservation(m,first,res,l,n,a,b,inputs,post,post,false,false);
    sample_from_wire(r,alpha(n),2);sample_from_wire(r,beta(n),2);
    alternatives::two_native_histories_use_r3(true,m,first,res,l,n,a,b,pre,post);
    r3::value_cache_witness(Branch::Beta);physical_history_bridge(r,Branch::Beta,history::at_first(beta(n)),r3::no_credit());
    history::extension_iff_writer(beta(n),history::at_first(beta(n)),Op::W1);history::extension_iff_writer(beta(n),history::at_first(beta(n)),Op::W2);
}

}
