// Feasibility of the weak prefix of the original HOT executions.
use vstd::prelude::*;
use crate::{Branch, Op, Replica, RecoveredOrder, checkpoint::*, delivery::*};
use crate::async_fork as af;
use crate::async_messages::{self as net, Headers};
use crate::first_assembly as asm;
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule as schedule;
use crate::fair_read as fair;
use crate::hybrid_majority as maj;
use crate::independent_preparations as prep;
use crate::independent_read as read;
use crate::native_fork as fork;
use crate::operation_history as op;
use crate::order_extension as order;
use crate::original_application as app;
use crate::read_call::{Event, Program};
use crate::register_history as reg;
use crate::semantic_promotion as retention;
use crate::weak_round as weak;

verus! {

pub open spec fn start<S>(m: Program<S>) -> read::State<S> {
    prep::before_offers(m,app::lanes())
}

pub open spec fn selected(b: Fork) -> nat { if b.branch == Branch::Alpha { 1 } else { 0 } }

pub open spec fn receipt(b: Fork, notice: bool) -> Seq<Event> {
    let d = Action::Deliver(selected(b));
    if notice { seq![d, received_replies(b)[1]] } else { seq![d] }
}

// Test one origin on the real post-RMW machine, with the other origin idle.
// A receipt without a subsequent confirmation suffices to expose the value.
pub open spec fn isolated_actions(b: Fork, notice: bool) -> Seq<Event> {
    seq![prep::offers()[selected(b) as int]] + receipt(b,notice)
}

pub open spec fn isolated_install<S>(m: Program<S>, b: Fork, notice: bool) -> bool {
    asm::prefix(m,start(m),isolated_actions(b,notice),true)
}

pub open spec fn joint_actions(b: Fork, notice: bool) -> Seq<Event> {
    prep::offers() + receipt(b,notice)
}

// Before the first weak delivery the scheduler may run replica CPUs and
// any number of real weak sends. No raw local input can manufacture a copy.
pub open spec fn background(a: Event) -> bool {
    match a {
        Action::Strong(Process::At(_)) => true,
        Action::Send(_,body) => body.path==Path::Weak && body.from is At && body.to is At,
        _ => false,
    }
}

// An actual packet at the cut has a source even when earlier occurrences
// have been consumed and the same transport handle has been reused.
pub(crate) proof fn prefix_packet_source<S>(m: Program<S>, x: read::State<S>, s: Seq<Event>, h: nat, packet: Packet<Wire>)
    requires asm::prefix(m,x,s,true),
    ensures asm::drive(m,x,s).cfg.net.pending.get(h)==Some(packet) ==> x.cfg.net.pending.get(h)==Some(packet)
        || exists|i:int| 0<=i<s.len() && #[trigger] s[i]==Action::Send(h,packet),
    decreases s.len(),
{
    if s.len()>0 {
        let y=read::next(m,x,s[0]); let t=s.drop_first();
        prefix_packet_source(m,y,t,h,packet);
        if exists|j:int| 0<=j<t.len() && #[trigger] t[j]==Action::Send(h,packet) {
            let j=choose|j:int| 0<=j<t.len() && #[trigger] t[j]==Action::Send(h,packet);
            assert(s[j+1]==Action::Send(h,packet));
        }
    }
}

proof fn before_delivery<S>(m: Program<S>, x: read::State<S>, s: Seq<Event>, h: nat, packet: Packet<Wire>)
    requires asm::prefix(m,x,s,true), forall|i:int| 0<=i<s.len() ==> #[trigger] background(s[i]),
    ensures ({
        let q=asm::drive(m,x,s).cfg.net;
        q.locals==x.cfg.net.locals && q.unavailable==x.cfg.net.unavailable && q.r3_crashed==x.cfg.net.r3_crashed
            && (q.pending.get(h)==Some(packet) ==> x.cfg.net.pending.get(h)==Some(packet)
                || exists|i:int| 0<=i<s.len() && #[trigger] s[i]==Action::Send(h,packet))
    }),
    decreases s.len(),
{
    prefix_packet_source(m,x,s,h,packet);
    if s.len()>0 {
        let y=read::next(m,x,s[0]); let t=s.drop_first(); assert(background(s[0]));
        assert(y.cfg.net.locals =~= x.cfg.net.locals);
        assert forall|i:int| 0<=i<t.len() implies #[trigger] background(t[i]) by { assert(t[i]==s[i+1]); }
        before_delivery(m,y,t,h,packet);
    }
}

pub open spec fn ready_copy<S>(m: Program<S>, q: read::State<S>, b: Fork, h: nat) -> bool {
    q.cfg.net.pending.get(h)==Some(packet_for(b,selected(b)))
        && (m.accept)((q.cfg.private)(at(Replica::R3)),process_step(q.cfg.net,Action::Deliver(h)))
}

// An exact test at ANY common prefix of this form, independent of its
// length, the send order, or the packet IDs. Apply it twice to the same
// prefix for the original alternative installations. Competing packets,
// source memories and all other survivor observations are kept in place.
pub proof fn exposed_at_common_cut<S>(p: Program<S>, k: Headers, pre: Seq<Event>, b: Fork, h: nat)
    requires asm::prefix(net::implementation(k,p),start(net::implementation(k,p)),pre,true),
        forall|i:int| 0<=i<pre.len() ==> #[trigger] background(pre[i]),
    ensures ({
        let m=net::implementation(k,p); let x=start(m); let q=asm::drive(m,x,pre);
        let a=Action::Deliver(h); let full=pre+seq![a]; let y=asm::drive(m,x,full); let packet=packet_for(b,selected(b));
        let takes=asm::prefix(m,x,full,true) && process_step(q.cfg.net,a).incoming==Some(packet);
        ready_copy(m,q,b,h)==takes && (takes ==> {
            (exists|i:int| 0<=i<pre.len() && #[trigger] pre[i]==Action::Send(h,packet))
                && net::trace(p,net::snapshot(k,x),net::turns(k,full),true)
                && net::end(p,net::snapshot(k,x),net::turns(k,full))==net::snapshot(k,y)
                && (q.cfg.net.locals)(Replica::R3)==1 && (y.cfg.net.locals)(Replica::R3)==first_value(b)
                && survivor(q.cfg.net)==(2int,5int) && survivor(y.cfg.net)==survivor(q.cfg.net)
                && y.cfg.net.pending==q.cfg.net.pending.remove(h)
                && forall|c:Process| c!=at(Replica::R3) ==> (#[trigger] (y.cfg.private)(c))==(q.cfg.private)(c)
        })
    }),
{
    let m=net::implementation(k,p); let x=start(m); let q=asm::drive(m,x,pre);
    let packet=packet_for(b,selected(b)); let a=Action::Deliver(h);
    before_delivery(m,x,pre,h,packet); crate::isolated_rmws();
    asm::prefix_concat(m,x,pre,seq![a],true);
    assert(asm::drive(m,q,seq![a])==read::next(m,q,a)) by { reveal_with_fuel(asm::drive,2); }
    assert(asm::prefix(m,q,seq![a],true)==read::prefix_step(m)(q,a,read::next(m,q,a))) by { reveal_with_fuel(asm::prefix,2); }
    if ready_copy(m,q,b,h) { net::project_prefix(p,k,x,pre+seq![a],true,|_s:S|None); }
}

spec fn source_admits<S>(m: Program<S>, b: Fork) -> bool {
    let a = prep::offers()[selected(b) as int];
    (m.accept)((m.initial)(at(crate::origin(b.branch))),process_step(start(m).cfg.net,a))
}

spec fn receiver_admits<S>(m: Program<S>, b: Fork, notice: bool) -> bool {
    let r = at(Replica::R3); let obs = crate::sr1_majorities::obs(b);
    let state = (m.initial)(r);
    (m.accept)(state,obs[0]) && (!notice || (m.accept)((m.update)(state,obs[0]),obs[1]))
}

// Inserting the other origin's send changes the queue and its sender's
// private memory. Neither change is visible in these R3 callbacks.
proof fn local_tests<S>(m: Program<S>, b: Fork, notice: bool)
    ensures isolated_install(m,b,notice) == (source_admits(m,b) && receiver_admits(m,b,notice)),
        asm::prefix(m,start(m),joint_actions(b,notice),true)
            == (reg::origin_send_guards(m) && receiver_admits(m,b,notice)),
        receiver_admits(m,b,true) == dispatch::weak_open(prep::after_offers(m,app::lanes()),b),
{
    crate::isolated_rmws();
    crate::sr1_majorities::majority_transport(b);
    let x = start(m); let offers = prep::offers(); let o = offers[selected(b) as int];
    let one = read::next(m,x,o);
    let both = read::next(m,read::next(m,x,offers[0]),offers[1]);
    let d = Action::Deliver(selected(b)); let ack = received_replies(b)[1];
    assert(process_step(one.cfg.net,d) == crate::sr1_majorities::obs(b)[0]);
    assert(process_step(both.cfg.net,d) == process_step(one.cfg.net,d));
    assert(process_step(read::next(m,one,d).cfg.net,ack) == crate::sr1_majorities::obs(b)[1]);
    assert(process_step(read::next(m,both,d).cfg.net,ack) == crate::sr1_majorities::obs(b)[1]);
    assert((one.cfg.private)(at(Replica::R3)) == (m.initial)(at(Replica::R3)));
    assert((both.cfg.private)(at(Replica::R3)) == (m.initial)(at(Replica::R3)));
    assert(asm::drive(m,x,offers) == both) by { reveal_with_fuel(asm::drive,3); }
    asm::prefix_concat(m,x,offers,receipt(b,notice),true);
    asm::prefix_concat(m,x,seq![o],receipt(b,notice),true);
    reveal_with_fuel(asm::drive,3);
    reveal_with_fuel(asm::prefix,3);
}

// Exact specialization used by the existing strong-phase entry. This
// adapter queues one confirmation; no protocol-wide ACK rule is inferred.
pub open spec fn immediate_handlers<S>(p: Program<S>, k: Headers, b: Fork, notice: bool) -> bool {
    let packet=crate::weak_visibility::copy(b); let id=net::message(k,selected(b),packet).id;
    let r=at(Replica::R3); let before=(p.initial)(r);
    let input=crate::weak_visibility::receive(b,id);
    let ack=packet_for(b,2); let ack_id=net::message(k,2,ack).id;
    let output=ProcessStep { actor:r, own_local:Some(first_value(b)), incoming:None, action:Action::Send(ack_id,ack) };
    crate::weak_visibility::can_offer(p,b,crate::weak_visibility::Offer { steps:seq![],id })
        && crate::weak_visibility::can_take(p,seq![],b,id)
        && (!notice || (p.accept)((p.update)(before,input),output))
}

pub proof fn weak_entry_exact<S>(p: Program<S>, k: Headers, b: Fork, notice: bool)
    ensures immediate_handlers(p,k,b,notice)==isolated_install(net::implementation(k,p),b,notice),
{
    let m=net::implementation(k,p); local_tests(m,b,notice);
    crate::isolated_rmws(); crate::sr1_majorities::majority_transport(b);
}

pub open spec fn installed<S>(p: Program<S>, k: Headers, f: Fork, notice: bool) -> bool {
    let m = net::implementation(k,p); let x = start(m);
    let s = joint_actions(f,notice); let y = asm::drive(m,x,s); let other = (1-selected(f)) as nat;
    net::trace(p,net::snapshot(k,x),net::turns(k,s),true)
        && net::end(p,net::snapshot(k,x),net::turns(k,s)) == net::snapshot(k,y)
        && (y.cfg.net.locals)(Replica::R3) == first_value(f) && survivor(y.cfg.net) == (2int,5int)
        && y.cfg.net.pending.get(other) == Some(packet_for(f,other))
        && (notice ==> y.cfg.net.pending.get(2) == Some(packet_for(f,2)))
        && (y.cfg.private)(at(Replica::R1)) == (prep::after_offers(m,app::lanes()).initial)(at(Replica::R1))
        && (y.cfg.private)(at(Replica::R2)) == (prep::after_offers(m,app::lanes()).initial)(at(Replica::R2))
}

// Necessary and sufficient for exactly these prefixes. Each certificate
// is for one active source. Neither multicast nor ACK delivery is needed.
pub proof fn independent_weak_installs_compose<S>(p: Program<S>, k: Headers, n: Notice, notice: bool)
    ensures ({
        let m = net::implementation(k,p); let x = start(m); let a = alpha(n); let b = beta(n);
        let both = isolated_install(m,a,notice) && isolated_install(m,b,notice);
        both == (asm::prefix(m,x,joint_actions(a,notice),true) && asm::prefix(m,x,joint_actions(b,notice),true))
            && (both ==> forall|f: Fork| f.notice == n ==> #[trigger] installed(p,k,f,notice))
    }),
{
    let m = net::implementation(k,p); let x = start(m); let a = alpha(n); let b = beta(n);
    local_tests(m,a,notice); local_tests(m,b,notice);
    assert(reg::origin_send_guards(m) == (source_admits(m,a) && source_admits(m,b)));
    if isolated_install(m,a,notice) && isolated_install(m,b,notice) {
        assert forall|f: Fork| f.notice == n implies #[trigger] installed(p,k,f,notice) by {
            assert(f == a || f == b);
            let s = joint_actions(f,notice);
            net::project_prefix(p,k,x,s,true,|_s:S| None);
            asm::prefix_concat(m,x,prep::offers(),receipt(f,notice),true);
            crate::isolated_rmws();
            reveal_with_fuel(asm::drive,3);
        }
    }
}

// Discharge the complete weak and invocation prefix for the existing
// checkpoint handlers. Payload IDs can be arbitrary. No SR1 reply or
// strong progress property of this adapter is needed here.
pub proof fn checkpoint_weak_and_client_prefix(k: Headers, b: Fork)
    ensures ({
        let p = checkpoint_machine(); let raw = net::implementation(k,p); let m = af::after_offers(p,k);
        let s = prep::offers()+asm::boot(Some(b));
        isolated_install(raw,b,true) && installed(p,k,b,true)
            && dispatch::initiates(m) && schedule::startup(m)
            && asm::prefix(raw,start(raw),s,true)
            && net::trace(p,net::snapshot(k,start(raw)),net::turns(k,s),true)
            && asm::drive(raw,start(raw),s).first_requested == all_replicas()
            && !crate::first_mailbox::posted(raw)(asm::drive(raw,start(raw),s))
    }),
{
    let p = checkpoint_machine(); let raw = net::implementation(k,p); let m = af::after_offers(p,k);
    let n=b.notice; let a=alpha(n); let d=beta(n);
    assert forall|f: Fork| f.notice == n implies #[trigger] isolated_install(raw,f,true) by {
        local_tests(raw,f,true); crate::sr1_majorities::majority_transport(f); crate::isolated_rmws();
    }
    independent_weak_installs_compose(p,k,n,true);
    local_tests(raw,a,true); local_tests(raw,d,true); local_tests(raw,b,true);
    assert(reg::origin_send_guards(raw));
    reg::offers_need_only_origin_guards(raw);
    prep::shared_weak_entry(raw,app::lanes(),b);
    let c = Process::FirstClient; let es = dispatch::initial_sends();
    assert((m.initial)(c)==initial_control() && (m.initial)(Process::SecondClient)==initial_control()) by {
        reveal_with_fuel(asm::drive,3);
    }
    assert forall|i:int| 0<=i<es.len() implies {
        let e=#[trigger] es[i]; (m.accept)(crate::protocol::memory(m,e.actor,es,i as nat),e)
    } by { assert(i==0 || i==1 || i==2); reveal_with_fuel(crate::protocol::memory,4); }
    assert forall|i:nat| i<=3 implies !(m.done)(#[trigger] crate::protocol::memory(m,c,es,i))
        by { assert(i==0 || i==1 || i==2 || i==3); reveal_with_fuel(crate::protocol::memory,4); }
    asm::launch(m,app::lanes(),Some(b));
    prep::rebase_preserves_steps(raw,app::lanes(),asm::entry(m,app::lanes()),asm::boot(Some(b)));
    asm::prefix_concat(raw,start(raw),prep::offers(),asm::boot(Some(b)),true);
    dispatch::caller_memory(m,b,5);
    net::project_prefix(p,k,start(raw),prep::offers()+asm::boot(Some(b)),true,|_s:Control|None);
}

pub open spec fn journal_copies(s:weak::World,w:Op) -> Set<Replica> {
    all_replicas().filter(|r:Replica| (s.journal)(r).contains_key(weak::request(w).id))
}

// O supplies the local returns. At this cut the two weak calls have no
// session or read-from edge to each other. No strong call is in the ledger.
pub proof fn prior_to_observation(b: Fork)
    ensures ({
        let s = crate::guarded_history::weak_end(); let w = weak::request(Op::W1); let v = weak::request(Op::W2);
        let c = op::Calls { issued: reg::weak_calls(), replies: reg::weak_replies() };
        let h = op::Word { ops: Seq::empty(), states: seq![1int] };
        w.id.0 != v.id.0 && s.answers.get(w.id) == Some(1) && s.answers.get(v.id) == Some(1)
            && (s.journal)(w.site).contains_key(w.id) && (s.journal)(v.site).contains_key(v.id)
            && weak::origin_only(s) && op::legal(reg::register(),c,h)
            && journal_copies(s,Op::W1)==set![Replica::R1] && journal_copies(s,Op::W2)==set![Replica::R2]
            && (forall|order:Seq<Op>,w:Op| order::weak(w) ==>
                !#[trigger] crate::guarantee::ordered_on_majority(order,journal_copies(s,w),w))
            && crate::quorum_value(crate::isolated(),crate::first_quorum(b.branch),1)
    }),
{
    weak::actual_overlap(b);
    crate::isolated_rmws();
    assert(crate::first_quorum(b.branch).contains(Replica::R3) && crate::load(crate::isolated(),Replica::R3) == 1);
    assert((crate::guarded_history::weak_end().journal)(Replica::R1).contains_key(weak::request(Op::W1).id));
    assert((crate::guarded_history::weak_end().journal)(Replica::R2).contains_key(weak::request(Op::W2).id));
    let s=crate::guarded_history::weak_end();
    assert(journal_copies(s,Op::W1) =~= set![Replica::R1]);
    assert(journal_copies(s,Op::W2) =~= set![Replica::R2]);
    assert(set![Replica::R1].len()==1 && set![Replica::R2].len()==1);
}

// Evaluate the paper's session and read-from edges on the actual journals
// of the two completed weak calls. The three possible register values in
// this prefix have distinct sources (initial, W1, W2).
pub open spec fn journal_reads_from(w: Op, v: Op) -> bool {
    let s=crate::guarded_history::weak_end(); let u=weak::request(w); let t=weak::request(v);
    reg::weak_calls().contains(w) && reg::weak_calls().contains(v)
        && (s.journal)(u.site)[u.id].after==(s.journal)(t.site)[t.id].before
}

pub open spec fn journal_edge(w: Op, v: Op) -> bool {
    let u=weak::request(w); let t=weak::request(v);
    (reg::weak_calls().contains(w) && reg::weak_calls().contains(v) && u.id.0==t.id.0 && u.id.1<t.id.1)
        || journal_reads_from(w,v)
}

// The empty relation is a strict transitive extension of those edges.
// Causal visibility is an obligation on subsequent operations. The G
// deadline ranges over the total word. Neither requires a new site to
// see either writer on this weak-only prefix.
pub proof fn weak_prefix_history(b: Fork)
    ensures ({
        let calls=op::Calls { issued: reg::weak_calls(), replies: reg::weak_replies() };
        let h=op::Word { ops: Seq::<Op>::empty(), states: seq![1int] };
        let causal=Set::<(Op,Op)>::empty(); let s=crate::guarded_history::weak_end();
        (forall|w:Op,v:Op| #[trigger] journal_edge(w,v) ==> causal.contains((w,v)))
            && (forall|w:Op| !#[trigger] causal.contains((w,w)))
            && (forall|w:Op,u:Op,v:Op| #[trigger] causal.contains((w,u)) && #[trigger] causal.contains((u,v))
                ==> causal.contains((w,v)))
            && (forall|w:Op,v:Op| #[trigger] causal.contains((w,v)) ==> journal_reads_from(w,v))
            && op::legal(reg::register(),calls,h)
            && (forall|w:Op| #[trigger] h.ops.contains(w) ==> crate::guarantee::ordered_on_majority(h.ops,journal_copies(s,w),w))
            && (forall|w:Op| reg::weak_calls().contains(w) ==> #[trigger] journal_copies(s,w)==set![weak::request(w).site])
    }),
{
    prior_to_observation(b);
    let s=crate::guarded_history::weak_end(); let f=weak::request(Op::W1); let g=weak::request(Op::W2);
    assert((s.journal)(f.site)[f.id].before==1 && (s.journal)(f.site)[f.id].after==2);
    assert((s.journal)(g.site)[g.id].before==1 && (s.journal)(g.site)[g.id].after==5);
    assert forall|w:Op,v:Op| !#[trigger] journal_edge(w,v) by {
        if reg::weak_calls().contains(w) && reg::weak_calls().contains(v) {
            assert((w==Op::W1 || w==Op::W2) && (v==Op::W1 || v==Op::W2));
        }
    }
}

// Credit a majority reached at ANY earlier point, even if copies later
// disappear. copies is an interpretation of actual stored operations,
// including encoded records. It is independent of read results.
pub open spec fn holders<S>(m: Program<S>, x: read::State<S>, s: Seq<Event>,
    copies: crate::fanout_service::Copies<S>, w: Op, i: int) -> Set<Replica> {
    copies(fork::states(m,x,s)[i].cfg,w)
}

pub open spec fn observed_g_by_return<S>(m: Program<S>, x: read::State<S>, s: Seq<Event>,
    copies: crate::fanout_service::Copies<S>, h: RecoveredOrder) -> bool {
    forall|w: Op| order::reads_from(h.ops,Op::SR1,w) ==> exists|i: int| 0 <= i <= s.len()
        && #[trigger] crate::guarantee::ordered_on_majority(h.ops,holders(m,x,s,copies,w,i),w)
}

pub open spec fn no_gain_at<S>(m: Program<S>, x: read::State<S>, s: Seq<Event>,
    copies: crate::fanout_service::Copies<S>, w: Op, i: int) -> bool {
    holders(m,x,s,copies,w,i+1).subset_of(holders(m,x,s,copies,w,i))
}

proof fn no_later_gain<S>(m: Program<S>, x: read::State<S>, s: Seq<Event>,
    copies: crate::fanout_service::Copies<S>, w: Op, cut: nat, j: nat)
    requires cut <= j <= s.len(), forall|i:int| cut <= i < s.len() ==> #[trigger] no_gain_at(m,x,s,copies,w,i),
    ensures holders(m,x,s,copies,w,j as int).subset_of(holders(m,x,s,copies,w,cut as int)),
    decreases j-cut,
{
    if cut < j {
        no_later_gain(m,x,s,copies,w,cut,(j-1) as nat);
        assert(no_gain_at(m,x,s,copies,w,j-1));
    }
}

// Apply H/G backwards to an actual SR1 publication. During the isolated
// weak prefix the other origin never stores this operation. During the
// read no new holder is added. H then forces PRIOR storage at R3, without
// specifying the route, installation callback, or current register value.
pub proof fn observed_g_requires_prior_r3<S>(m: Program<S>, first: spec_fn(S)->int, x: read::State<S>,
    s: Seq<Event>, cut: nat, b: Fork, copies: crate::fanout_service::Copies<S>, h: RecoveredOrder)
    requires asm::prefix(m,x,s,true), cut <= s.len(), ({
        let y = asm::drive(m,x,s); let w = observed_writer(b);
        crate::first_mailbox::posted(m)(y) && first((y.cfg.private)(Process::FirstClient)) == first_value(b)
            && order::legal_first(h,first((y.cfg.private)(Process::FirstClient)))
            && observed_g_by_return(m,x,s,copies,h)
            && (forall|i:int| 0 <= i <= cut ==> #[trigger] holders(m,x,s,copies,w,i).subset_of(
                set![crate::origin(b.branch),Replica::R3]))
            && forall|i:int| cut <= i < s.len() ==> #[trigger] no_gain_at(m,x,s,copies,w,i)
    }),
    ensures exists|i:int| 0 <= i <= cut && #[trigger] holders(m,x,s,copies,observed_writer(b),i)
        == set![crate::origin(b.branch),Replica::R3],
{
    let w = observed_writer(b); let src = crate::origin(b.branch);
    order::exact_first_order(b,h);
    assert(h.ops[0]==w && h.ops[1]==Op::SR1 && order::reads_from(h.ops,Op::SR1,w));
    let j = choose|i:int| 0 <= i <= s.len()
        && #[trigger] crate::guarantee::ordered_on_majority(h.ops,holders(m,x,s,copies,w,i),w);
    let i = if j <= cut { j } else { cut as int };
    if cut < j { no_later_gain(m,x,s,copies,w,cut,j as nat); }
    let a = holders(m,x,s,copies,w,j); let q = holders(m,x,s,copies,w,i);
    assert(a.subset_of(q) && q.subset_of(set![src,Replica::R3]));
    if !a.contains(src) { assert(a.subset_of(set![Replica::R3])); assert(a =~= set![Replica::R3] || a =~= Set::empty()); }
    if !a.contains(Replica::R3) { assert(a.subset_of(set![src])); assert(a =~= set![src] || a =~= Set::empty()); }
    assert(q =~= set![src,Replica::R3]);
}

// The first receipt of this very occurrence, or loss of its recipient.
proof fn find_receipt<S>(m: Program<S>, e: fair::Run<S>, h: nat, packet: Packet<Wire>, i: nat, limit: nat)
    -> (j: nat)
    requires fork::call_run(m,(e.state)(0),e), i <= limit,
        (e.state)(i).cfg.net.pending.get(h)==Some(packet),
        (e.action)(limit)==Action::Deliver(h) || !live((e.state)(limit).cfg.net,packet.to),
    ensures i <= j <= limit, (e.state)(j).cfg.net.pending.get(h)==Some(packet),
        (e.action)(j)==Action::Deliver(h) || !live((e.state)(j).cfg.net,packet.to),
        forall|u: nat| i <= u < j ==> #[trigger] (e.action)(u)!=Action::Deliver(h) && live((e.state)(u).cfg.net,packet.to),
    decreases limit-i,
{
    if (e.action)(i)==Action::Deliver(h) || !live((e.state)(i).cfg.net,packet.to) { i } else {
        assert(read::prefix_step(m)((e.state)(i),(e.action)(i),(e.state)(i+1)));
        if let Action::Send(slot,body)=(e.action)(i) { assert(slot!=h); }
        find_receipt(m,e,h,packet,i+1,limit)
    }
}

pub proof fn fair_install_of_issued_copy<S>(m: Program<S>, e: fair::Run<S>, i: nat, h: nat, b: Fork)
    -> (j: nat)
    requires fork::call_run(m,(e.state)(0),e), crate::progress::delivery_fair(fair::physical(e)),
        (e.state)(i).cfg.net.pending.get(h)==Some(packet_for(b,selected(b))),
    ensures i<=j, (e.state)(j).cfg.net.pending.get(h)==Some(packet_for(b,selected(b))),
        live((e.state)(j).cfg.net,at(Replica::R3)) ==> (e.action)(j)==Action::Deliver(h)
            && process_step((e.state)(j).cfg.net,(e.action)(j)).incoming==Some(packet_for(b,selected(b)))
            && ((e.state)(j+1).cfg.net.locals)(Replica::R3)==first_value(b),
        forall|u: nat| i<=u<j ==> #[trigger] (e.action)(u)!=Action::Deliver(h) && live((e.state)(u).cfg.net,at(Replica::R3)),
{
    let physical=fair::physical(e); let packet=packet_for(b,selected(b));
    assert((physical.state)(i).pending.contains_key(h));
    let limit=choose|u:nat| u>=i && (#[trigger] (physical.action)(u)==Action::Deliver(h)
        || !live((physical.state)(u),packet.to));
    let j=find_receipt(m,e,h,packet,i,limit);
    assert(read::prefix_step(m)((e.state)(j),(e.action)(j),(e.state)(j+1)));
    j
}

// Only the two single-source weak runs are needed to enable the original
// prefix. C1 and C2 have independent initial callbacks. The reference
// and the all-live prefix see the same calls at R3.
proof fn original_launch<S>(raw: Program<S>, n: Notice)
    requires isolated_install(raw,alpha(n),true), isolated_install(raw,beta(n),true),
    ensures ({
        let m=prep::after_offers(raw,app::lanes()); let s=prep::offers();
        asm::prefix(raw,start(raw),s,true) && asm::drive(raw,start(raw),s)==asm::entry(m,app::lanes())
            && (forall|b:Fork| b.notice==n ==> #[trigger] dispatch::weak_open(m,b))
            && (dispatch::pending_fanout(raw) ==> dispatch::pending_fanout(m))
            && (schedule::startup(raw) ==> schedule::startup(m))
    }),
{
    let m=prep::after_offers(raw,app::lanes()); let l=alpha(n); let r=beta(n);
    local_tests(raw,l,true); local_tests(raw,r,true);
    assert forall|b:Fork| b.notice==n implies #[trigger] dispatch::weak_open(m,b) by { assert(b==l || b==r); }
    assert(reg::origin_send_guards(raw));
    reg::offers_need_only_origin_guards(raw);
    prep::shared_weak_entry(raw,app::lanes(),l);
    let c=Process::FirstClient; let es=dispatch::initial_sends();
    assert((m.initial)(c)==(raw.initial)(c)
        && (m.initial)(Process::SecondClient)==(raw.initial)(Process::SecondClient)) by {
        reveal_with_fuel(asm::drive,3);
    }
    assert forall|i:nat| i<=3 implies #[trigger] crate::protocol::memory(m,c,es,i)
        == crate::protocol::memory(raw,c,es,i) by { crate::protocol::memory_from_same_local_state(m,raw,c,es,i); }
}

pub open spec fn invoked_second<S>(p: Program<S>, k: Headers, x: read::State<S>) -> bool {
    let raw=net::implementation(k,p); let initial=start(raw);
    exists|s: Seq<Event>| s.len()>0 && s.last()==Action::StartSecondClient
        && #[trigger] asm::prefix(raw,initial,s,true) && asm::drive(raw,initial,s)==x
        && net::trace(p,net::snapshot(k,initial),net::turns(k,s),true)
        && net::end(p,net::snapshot(k,initial),net::turns(k,s))==net::snapshot(k,x)
}

// Reach the independent invocation before applying any C2 progress law.
proof fn reach_second<S>(p: Program<S>, k: Headers, first: spec_fn(S)->int, b: Fork, s: asm::Service<S>)
    requires ({
        let raw=net::implementation(k,p); let m=af::after_offers(p,k);
        isolated_install(raw,alpha(b.notice),true) && isolated_install(raw,beta(b.notice),true)
            && dispatch::initiates(m) && schedule::startup(raw) && fork::selected_first(m,first,b,s)
    }),
    ensures invoked_second(p,k,fork::invocation(af::after_offers(p,k),s))
        && fork::available(fork::invocation(af::after_offers(p,k),s)),
{
    let raw=net::implementation(k,p); let m=af::after_offers(p,k); let l=app::lanes(); let x=start(raw);
    let pre=asm::boot(Some(b))+s.actions; let wake=crate::fork_alternatives::wake();
    original_launch(raw,b.notice); app::accepted_first_prefix(m,first,b,s);
    fork::actual_handoff(m,first,b,s,Set::empty());
    asm::prefix_concat(m,asm::entry(m,l),pre,wake,true);
    prep::rebase_preserves_steps(raw,l,asm::entry(m,l),pre+wake);
    asm::prefix_concat(raw,x,prep::offers(),pre+wake,true);
    let trace=prep::offers()+(pre+wake);
    net::project_prefix(p,k,x,trace,true,|_s:S|None);
    assert(trace.last()==Action::StartSecondClient && asm::prefix(raw,x,trace,true));
}

// Invocation-time A fixes the first answers and rules out premature
// publication on C1's requests. The caller need only supply a fair
// reference and the no-await clause on each of the two selected majorities.
pub open spec fn reference_service<S>(m: Program<S>, first: spec_fn(S)->int, b: Fork, run: fair::Runnable) -> bool {
    let x=schedule::reference(m,b,5);
    maj::first_invocation_sampling(m,first,schedule::reference(m,b,0))
        && mail::first_availability(m,run,schedule::reached_in(m,b)) && mail::fair_opportunity(m,run,x)
        && !crate::promotion_wait::needs_class(mail::active_step(m),mail::posted(m),x,app::weak_replica_step())
}

pub proof fn original_first_services<S>(p: Program<S>, k: Headers, first: spec_fn(S)->int,
    res: spec_fn(S)->Option<int>, n: Notice, run: fair::Runnable) -> (pair:(asm::Service<S>,asm::Service<S>))
    requires ({
        let raw=net::implementation(k,p); let m=af::after_offers(p,k);
        isolated_install(raw,alpha(n),true) && isolated_install(raw,beta(n),true)
            && dispatch::pending_fanout(raw) && schedule::startup(raw)
            && reference_service(m,first,alpha(n),run) && reference_service(m,first,beta(n),run)
    }),
    ensures ({
        let m=af::after_offers(p,k);
        dispatch::initiates(m) && fork::selected_first(m,first,alpha(n),pair.0)
            && fork::selected_first(m,first,beta(n),pair.1)
            && first((pair.0.states.last().cfg.private)(Process::FirstClient))==5
            && first((pair.1.states.last().cfg.private)(Process::FirstClient))==2
            && invoked_second(p,k,fork::invocation(m,pair.0)) && fork::available(fork::invocation(m,pair.0))
            && invoked_second(p,k,fork::invocation(m,pair.1)) && fork::available(fork::invocation(m,pair.1))
    }),
{
    let raw=net::implementation(k,p); let m=af::after_offers(p,k); let l=alpha(n); let r=beta(n);
    original_launch(raw,n);
    assert forall|b:Fork| b.notice==n implies #[trigger] dispatch::weak_open(m,b)
        && maj::first_invocation_sampling(m,first,schedule::reference(m,b,0)) by { assert(b==l || b==r); }
    maj::invocation_a_keeps_fanout_pending(m,first,n);
    maj::invocation_includes_submitted_sampling(m,first,res,schedule::reference(m,l,0));
    maj::invocation_includes_submitted_sampling(m,first,res,schedule::reference(m,r,0));
    let a=app::first_from_reference_a(m,first,res,l,run); let b=app::first_from_reference_a(m,first,res,r,run);
    reach_second(p,k,first,l,a); reach_second(p,k,first,r,b);
    (a,b)
}

// Use only the C2 opportunities reached by these two C1 services. Each
// chosen alternative suffix, including one violating H, is reassembled
// with the actual prefix and projected to an admitted public history.
pub proof fn original_hot_at_selected_invocations<S>(p: Program<S>, k: Headers, first: spec_fn(S)->int,
    res: spec_fn(S)->Option<int>, n: Notice, aa: bool, ab: bool, run: fair::Runnable,
    a: asm::Service<S>, b: asm::Service<S>) -> (pair:(fork::ReadPair<S>,fork::ReadPair<S>))
    requires op::operation_t(reg::system(p,k,first,res),reg::register()), n!=Notice::Replication ==> aa && ab, ({
        let raw=net::implementation(k,p); let m=af::after_offers(p,k);
        isolated_install(raw,alpha(n),true) && isolated_install(raw,beta(n),true) && schedule::startup(raw)
            && dispatch::initiates(m) && fork::selected_first(m,first,alpha(n),a) && fork::selected_first(m,first,beta(n),b)
            && fork::opportunity(m,res,fork::invocation(m,a),run) && fork::opportunity(m,res,fork::invocation(m,b),run)
    }),
    ensures ({
        let raw=net::implementation(k,p); let m=af::after_offers(p,k); let (u,v)=pair;
        u.first==a && v.first==b && fork::completed_history(raw,m,first,res,alpha(n),u) && af::public_history(p,k,alpha(n),u)
            && fork::completed_history(raw,m,first,res,beta(n),v) && af::public_history(p,k,beta(n),v)
            && (!fork::legal_history(m,first,res,u) || !fork::legal_history(m,first,res,v))
    }),
{
    let raw=net::implementation(k,p); let m=af::after_offers(p,k); let l=alpha(n); let r=beta(n);
    let x=fork::invocation(m,a); let y=fork::invocation(m,b); let mask=Set::<nat>::empty();
    original_launch(raw,n);
    let u=fork::complete_selected_first(raw,m,first,res,l,a,run);
    let v=fork::complete_selected_first(raw,m,first,res,r,b,run);
    af::publish_history(p,k,first,res,l,u); af::publish_history(p,k,first,res,r,v);
    let t=retention::Trial {arm:l,assigned:aa,path:u}; let z=retention::Trial {arm:r,assigned:ab,path:v};
    reg::operation_t_implies_register_t(p,k,first,res);
    retention::functional_t_preserves_original_options(p,k,first,res,t,z,run);
    af::started_options(p,k,res,x); af::started_options(p,k,res,y);
    fork::native_fork_requires_preservation(m,first,res,n,a,b,u.second,v.second,mask,aa,ab);
    (u,v)
}

// Apply the accepted invocation laws only after reachability was proved.
// A quantifies over fair runs; existence of an admissible fair scheduler
// and the independent no-await clause each do separate work. In each
// arm the weak entry tests the source send, R3 receipt and R3 confirmation
// send on their actual local states.
pub proof fn original_hot_from_weak_installs<S>(p: Program<S>, k: Headers, first: spec_fn(S)->int,
    res: spec_fn(S)->Option<int>, n: Notice, aa: bool, ab: bool, run: fair::Runnable)
    -> (pair:(fork::ReadPair<S>,fork::ReadPair<S>))
    requires op::operation_t(reg::system(p,k,first,res),reg::register()), n!=Notice::Replication ==> aa && ab, ({
        let raw=net::implementation(k,p); let m=af::after_offers(p,k);
        let issued=|x:read::State<S>| invoked_second(p,k,x) && fork::available(x);
        immediate_handlers(p,k,alpha(n),true) && immediate_handlers(p,k,beta(n),true)
            && dispatch::pending_fanout(raw) && schedule::startup(raw)
            && reference_service(m,first,alpha(n),run) && reference_service(m,first,beta(n),run)
            && crate::promotion_wait::no_await(read::prefix_step(m),read::returned(res),issued,fork::weak_step())
            && forall|x:read::State<S>| #[trigger] invoked_second(p,k,x) && fork::available(x) ==>
                fork::invocation_a(m,res,x,run) && exists|e:fair::Run<S>| #[trigger] fork::call_run(m,x,e) && fair::fair(e,run)
    }),
    ensures ({
        let raw=net::implementation(k,p); let m=af::after_offers(p,k); let (a,b)=pair;
        fork::completed_history(raw,m,first,res,alpha(n),a) && af::public_history(p,k,alpha(n),a)
            && fork::completed_history(raw,m,first,res,beta(n),b) && af::public_history(p,k,beta(n),b)
            && (!fork::legal_history(m,first,res,a) || !fork::legal_history(m,first,res,b))
    }),
{
    weak_entry_exact(p,k,alpha(n),true); weak_entry_exact(p,k,beta(n),true);
    let m=af::after_offers(p,k); let (a,b)=original_first_services(p,k,first,res,n,run);
    let issued=|x:read::State<S>| invoked_second(p,k,x) && fork::available(x);
    assert(issued(fork::invocation(m,a)) && issued(fork::invocation(m,b)));
    original_hot_at_selected_invocations(p,k,first,res,n,aa,ab,run,a,b)
}

// Fairness of a finite delay is decided by the continuation. In
// particular, a pending, undelivered occurrence is the same packet at
// the next cut. No live-recipient delivery duty is discarded at a splice.
pub open spec fn original_run<S>(m:Program<S>, x:read::State<S>, e:fair::Run<S>) -> bool {
    (e.state)(0)==x && forall|i:nat| {
        let q=(e.state)(i); let a=#[trigger] (e.action)(i);
        asm::prefix(m,q,seq![a],true) && (e.state)(i+1)==read::next(m,q,a)
    }
}

spec fn prepend<S>(x:read::State<S>, a:Event, e:fair::Run<S>) -> fair::Run<S> {
    fair::Run { state:|i:nat| if i==0 {x} else {(e.state)((i-1) as nat)},
        action:|i:nat| if i==0 {a} else {(e.action)((i-1) as nat)} }
}

proof fn prepend_fair_step<S>(m:Program<S>, x:read::State<S>, a:Event, e:fair::Run<S>, run:fair::Runnable)
    requires asm::prefix(m,x,seq![a],true), original_run(m,read::next(m,x,a),e), fair::fair(e,run),
    ensures original_run(m,x,prepend(x,a,e)), fair::fair(prepend(x,a,e),run),
{
    let z=prepend(x,a,e); let phys=fair::physical(z); let tail=fair::physical(e);
    assert forall|i:nat| {
        let q=(z.state)(i); let ev=#[trigger] (z.action)(i);
        asm::prefix(m,q,seq![ev],true) && (z.state)(i+1)==read::next(m,q,ev)
    } by { if i>0 { let j=(i-1) as nat; assert(asm::prefix(m,(e.state)(j),seq![(e.action)(j)],true)); } }
    assert forall|i:nat,h:nat| #[trigger] (phys.state)(i).pending.contains_key(h) implies
        exists|j:nat| j>=i && (#[trigger] (phys.action)(j)==Action::Deliver(h)
            || !live((phys.state)(j),(phys.state)(i).pending[h].to)) by {
        if i==0 && a==Action::<Wire>::Deliver(h) { assert((phys.action)(0)==Action::Deliver(h)); }
        else {
            let t=if i==0 {0nat} else {(i-1) as nat};
            if i==0 { if let Action::Send(id,_) = a { assert(id!=h) by { reveal(asm::prefix); } } }
            assert((tail.state)(t).pending.get(h)==Some((phys.state)(i).pending[h]));
            assert((tail.state)(t).pending.contains_key(h));
            let j=choose|j:nat| j>=t && (#[trigger] (tail.action)(j)==Action::Deliver(h)
                || !live((tail.state)(j),(tail.state)(t).pending[h].to));
            assert((phys.action)(j+1)==(tail.action)(j) && (phys.state)(j+1)==(tail.state)(j));
        }
    }
    assert forall|i:nat,c:Process| #[trigger] crate::progress::continuously_runnable(phys,run,i,c) implies
        exists|j:nat| j>=i && #[trigger] crate::progress::runs_at(phys,j,c) by {
        let t=if i==0 {0nat} else {(i-1) as nat};
        assert forall|u:nat| u>=t implies #[trigger] run((tail.state)(u),c) by { assert(run((phys.state)(u+1),c)); }
        assert(crate::progress::continuously_runnable(tail,run,t,c));
        let j=choose|j:nat| j>=t && #[trigger] crate::progress::runs_at(tail,j,c);
        assert(crate::progress::runs_at(phys,j+1,c));
    }
}

pub proof fn fair_extension_of_original_prefix<S>(m:Program<S>, x:read::State<S>, s:Seq<Event>,
    tail:fair::Run<S>, run:fair::Runnable) -> (e:fair::Run<S>)
    requires asm::prefix(m,x,s,true), original_run(m,asm::drive(m,x,s),tail), fair::fair(tail,run),
    ensures original_run(m,x,e), fair::fair(e,run),
        forall|i:nat| i<s.len() ==> #[trigger] (e.action)(i)==s[i as int],
        forall|j:nat| #[trigger] (e.state)(s.len()+j)==(tail.state)(j) && (e.action)(s.len()+j)==(tail.action)(j),
    decreases s.len(),
{
    if s.len()==0 { tail } else {
        let a=s[0]; let rest=fair_extension_of_original_prefix(m,read::next(m,x,a),s.drop_first(),tail,run);
        assert(asm::prefix(m,x,seq![a],true)) by { reveal_with_fuel(asm::prefix,2); }
        prepend_fair_step(m,x,a,rest,run);
        let e=prepend(x,a,rest);
        assert forall|i:nat| i<s.len() implies #[trigger] (e.action)(i)==s[i as int] by {
            if i>0 { let j=(i-1) as nat; assert((rest.action)(j)==s.drop_first()[j as int]); }
        }
        assert forall|j:nat| #[trigger] (e.state)(s.len()+j)==(tail.state)(j) && (e.action)(s.len()+j)==(tail.action)(j)
            by { assert((rest.state)(s.drop_first().len()+j)==(tail.state)(j)); }
        e
    }
}

// Test the two paper quorums before the scheduler has installed a copy.
// If interval runs from SR1 invocation through publication, its first
// state already counts for A. The history and weak-G tests below concern
// candidate values. The actual handler's return is never chosen here.
pub proof fn original_quorum_before_receipt<S>(
    m: Program<S>, b: Fork, pre: Seq<Event>, interval: Seq<Event>,
    copies: crate::fanout_service::Copies<S>,
)
    requires
        asm::prefix(m, start(m), pre, true),
        forall|i: int| 0 <= i < pre.len() ==> #[trigger] background(pre[i]),
        asm::prefix(m, asm::drive(m, start(m), pre), interval, true),
    ensures ({
        let x = start(m);
        let trace = pre + interval;
        let samples = fork::states(m, asm::drive(m, x, pre), interval);
        let q = crate::first_quorum(b.branch);
        let v = first_value(b);
        let w = observed_writer(b);
        let initial = crate::irrevocable_order::read_genesis();
        asm::prefix(m, x, trace, true)
            && maj::held(samples, q, 1) && maj::held(samples, q, v)
            && order::legal_first(initial, 1) && observed_g_by_return(m, x, trace, copies, initial)
            && ((exists|h: RecoveredOrder| #[trigger] order::legal_first(h, v)
                    && observed_g_by_return(m, x, trace, copies, h))
                == (exists|i: int| 0 <= i <= trace.len()
                    && (#[trigger] holders(m, x, trace, copies, w, i)).len() >= 2))
    }),
{
    let x = start(m);
    let entry = asm::drive(m, x, pre);
    let trace = pre + interval;
    asm::prefix_concat(m, x, pre, interval, true);
    before_delivery(m, x, pre, 0, packet_for(b, selected(b)));
    crate::isolated_rmws();
    let samples = fork::states(m, entry, interval);
    let src = crate::origin(b.branch);
    let q = crate::first_quorum(b.branch);
    assert(interval.take(0) =~= Seq::<Event>::empty());
    assert(samples[0] == entry);
    assert(q.contains(Replica::R3) && (samples[0].cfg.net.locals)(Replica::R3) == 1);
    assert(q.contains(src) && (samples[0].cfg.net.locals)(src) == first_value(b));

    let initial = crate::irrevocable_order::read_genesis();
    assert(initial.ops[0] == Op::SR1);
    assert forall|u: Op| !#[trigger] order::reads_from(initial.ops, Op::SR1, u) by {};

    let w = observed_writer(b);
    let canonical = order::at_first(b);
    order::canonical_orders_exist(b);
    assert(canonical.ops[0] == w && canonical.ops[1] == Op::SR1);
    assert(order::reads_from(canonical.ops, Op::SR1, w));
    assert forall|u: Op| #[trigger] order::reads_from(canonical.ops, Op::SR1, u) implies u == w by {};
    if exists|h: RecoveredOrder| #[trigger] order::legal_first(h, first_value(b))
        && observed_g_by_return(m, x, trace, copies, h) {
        let h = choose|h: RecoveredOrder| #[trigger] order::legal_first(h, first_value(b))
            && observed_g_by_return(m, x, trace, copies, h);
        order::exact_first_order(b, h);
        let i = choose|i: int| 0 <= i <= trace.len()
            && #[trigger] crate::guarantee::ordered_on_majority(h.ops, holders(m, x, trace, copies, w, i), w);
        assert(holders(m, x, trace, copies, w, i).len() >= 2);
    } else if exists|i: int| 0 <= i <= trace.len() && (#[trigger] holders(m, x, trace, copies, w, i)).len() >= 2 {
        let i = choose|i: int| 0 <= i <= trace.len() && (#[trigger] holders(m, x, trace, copies, w, i)).len() >= 2;
        assert(crate::guarantee::ordered_on_majority(canonical.ops, holders(m, x, trace, copies, w, i), w));
        assert(observed_g_by_return(m, x, trace, copies, canonical));
    }
}

} // verus!
