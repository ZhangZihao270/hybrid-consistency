// The scheduler can combine independently enabled weak sends. Which write
// R3 can expose is determined by its actual local receive guard.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::async_messages::{self as net, Command, Headers, Message};
use crate::first_assembly as asm;
use crate::first_splice::Observation;
use crate::independent_read::{self as read, State};
use crate::read_call::{Event, Program};
use crate::weak_construction as wc;

verus! {

pub struct Offer { pub steps: Seq<Event>, pub id: nat }

pub open spec fn copy(b: Fork) -> Packet<Wire> { packet_for(b,wc::selected(b)) }

pub open spec fn local_input(a: Event) -> Observation { process_step(local_rmw_cells(),a) }

pub open spec fn receive(b: Fork, id: nat) -> Observation {
    Observation { actor: at(Replica::R3), own_local: Some(1), incoming: Some(copy(b)),
        action: Action::Deliver(id) }
}

// The word contains only local computations and weak sends by this site.
// IDs in it are payload data. No other site, network state, or future read
// appears in the test.
pub open spec fn walk<S>(p: Program<S>, r: Replica, state: S, word: Seq<Event>) -> Option<S>
    decreases word.len(),
{
    if word.len()==0 { Some(state) } else {
        let a=word[0]; let e=local_input(a);
        if wc::background(a) && e.actor==at(r) && (p.accept)(state,e) {
            walk(p,r,(p.update)(state,e),word.drop_first())
        } else { None }
    }
}

pub open spec fn can_offer<S>(p: Program<S>, b: Fork, offer: Offer) -> bool {
    let r=crate::origin(b.branch); let z=walk(p,r,(p.initial)(at(r)),offer.steps);
    z.is_some() && (p.accept)(z.unwrap(),local_input(Action::Send(offer.id,copy(b))))
}

pub open spec fn can_take<S>(p: Program<S>, steps: Seq<Event>, b: Fork, id: nat) -> bool {
    let r=Replica::R3; let z=walk(p,r,(p.initial)(at(r)),steps);
    z.is_some() && (p.accept)(z.unwrap(),receive(b,id))
}

pub open spec fn background_prefix<S>(m: Program<S>, x: State<S>, s: Seq<Event>) -> bool {
    asm::prefix(m,x,s,true) && forall|i:int| 0<=i<s.len() ==> #[trigger] wc::background(s[i])
}

pub open spec fn at_site(s: Seq<Event>, r: Replica) -> bool {
    forall|i:int| 0<=i<s.len() ==> local_input(#[trigger] s[i]).actor==at(r)
}

pub open spec fn frame<S>(x: State<S>, y: State<S>, r: Replica) -> bool {
    x.cfg.net.locals==y.cfg.net.locals && x.cfg.net.unavailable==y.cfg.net.unavailable
        && x.cfg.net.r3_crashed==y.cfg.net.r3_crashed && x.cfg.net.pending.submap_of(y.cfg.net.pending)
        && forall|c:Process| c!=at(r) ==> (#[trigger] (y.cfg.private)(c))==(x.cfg.private)(c)
}

proof fn carry(q: Map<nat,Packet<Wire>>, next: Map<nat,Packet<Wire>>, h: nat)
    requires q.submap_of(next), q.get(h).is_some(),
    ensures next.get(h)==q.get(h),
{
    assert(q.dom().contains(h)); assert(next.dom().contains(h));
}

proof fn join<S>(m: Program<S>, x: State<S>, a: Seq<Event>, b: Seq<Event>)
    ensures background_prefix(m,x,a+b)==(background_prefix(m,x,a) && background_prefix(m,asm::drive(m,x,a),b)),
        asm::drive(m,x,a+b)==asm::drive(m,asm::drive(m,x,a),b),
{
    asm::prefix_concat(m,x,a,b,true);
    if background_prefix(m,x,a+b) {
        assert forall|i:int| 0<=i<a.len() implies #[trigger] wc::background(a[i]) by { assert(a[i]==(a+b)[i]); }
        assert forall|i:int| 0<=i<b.len() implies #[trigger] wc::background(b[i]) by { assert(b[i]==(a+b)[a.len()+i]); }
    } else if background_prefix(m,x,a) && background_prefix(m,asm::drive(m,x,a),b) {
        assert forall|i:int| 0<=i<(a+b).len() implies #[trigger] wc::background((a+b)[i]) by {
            if i<a.len() { assert((a+b)[i]==a[i]); } else { assert((a+b)[i]==b[i-a.len()]); }
        }
    }
}

// Project a guarded native prefix onto the local inputs actually seen at
// one site. Before the first receipt its cell is constant.
proof fn project_site<S>(p: Program<S>, k: Headers, x: State<S>, s: Seq<Event>, r: Replica) -> (word: Seq<Event>)
    requires x.cfg.net.locals==local_rmw_cells().locals, background_prefix(net::implementation(k,p),x,s),
    ensures ({
        let y=asm::drive(net::implementation(k,p),x,s);
        walk(p,r,(x.cfg.private)(at(r)),word)==Some((y.cfg.private)(at(r)))
            && y.cfg.net.locals==x.cfg.net.locals
    }),
    decreases s.len(),
{
    if s.len()==0 { seq![] } else {
        let m=net::implementation(k,p); let a=s[0]; let y=read::next(m,x,a); let t=s.drop_first();
        let e=net::callback(k,process_step(x.cfg.net,a));
        assert(wc::background(a));
        assert(y.cfg.net.locals =~= x.cfg.net.locals);
        assert(wc::background(e.action) && e==local_input(e.action));
        assert forall|i:int| 0<=i<t.len() implies #[trigger] wc::background(t[i]) by { assert(t[i]==s[i+1]); }
        let tail=project_site(p,k,y,t,r);
        if e.actor==at(r) {
            let w=seq![e.action]+tail; assert(w.drop_first() =~= tail); w
        } else { tail }
    }
}

spec fn proposal(a: Event) -> Command {
    match a { Action::Send(id,body) => Command::Send(Message { id, body }), _ => Command::Other(a) }
}

// Lift one local guard to a native action, allocating a fresh occurrence
// while retaining its exact payload ID. All older packets remain pending.
proof fn local_step<S>(p: Program<S>, k: Headers, x: State<S>, r: Replica, a: Event) -> (e: Event)
    requires x.cfg.net.locals==local_rmw_cells().locals, live(x.cfg.net,at(r)), wc::background(a),
        local_input(a).actor==at(r), (p.accept)((x.cfg.private)(at(r)),local_input(a)),
    ensures ({
        let m=net::implementation(k,p); let y=read::next(m,x,e);
        background_prefix(m,x,seq![e]) && frame(x,y,r)
            && (y.cfg.private)(at(r))==(p.update)((x.cfg.private)(at(r)),local_input(a))
            && asm::drive(m,x,seq![e])==y && net::command(k,e)==proposal(a) && local_input(e).actor==at(r)
    }),
{
    let c=proposal(a); let m=net::implementation(k,p);
    assert(net::ready(p,k,x,c,false));
    let e=net::realize_step(p,k,x,c,false,Set::empty());
    assert(wc::background(e));
    let y=read::next(m,x,e);
    assert(y.cfg.net.locals =~= x.cfg.net.locals);
    assert(x.cfg.net.pending.submap_of(y.cfg.net.pending));
    reveal_with_fuel(asm::prefix,2); reveal_with_fuel(asm::drive,2);
    e
}

proof fn run_site<S>(p: Program<S>, k: Headers, x: State<S>, r: Replica, word: Seq<Event>) -> (s: Seq<Event>)
    requires x.cfg.net.locals==local_rmw_cells().locals, live(x.cfg.net,at(r)),
        walk(p,r,(x.cfg.private)(at(r)),word).is_some(),
    ensures ({
        let m=net::implementation(k,p); let y=asm::drive(m,x,s);
        background_prefix(m,x,s) && frame(x,y,r) && at_site(s,r)
            && Some((y.cfg.private)(at(r)))==walk(p,r,(x.cfg.private)(at(r)),word)
    }),
    decreases word.len(),
{
    if word.len()==0 { seq![] } else {
        let m=net::implementation(k,p); let e=local_step(p,k,x,r,word[0]); let y=read::next(m,x,e);
        let t=run_site(p,k,y,r,word.drop_first()); let z=asm::drive(m,y,t);
        join(m,x,seq![e],t);
        vstd::map_lib::lemma_submap_of_trans(x.cfg.net.pending,y.cfg.net.pending,z.cfg.net.pending);
        assert forall|i:int| 0<=i<(seq![e]+t).len() implies local_input(#[trigger] (seq![e]+t)[i]).actor==at(r) by {
            if i>0 { assert((seq![e]+t)[i]==t[i-1]); }
        }
        seq![e]+t
    }
}

proof fn issue<S>(p: Program<S>, k: Headers, x: State<S>, b: Fork, o: Offer) -> (issued: (Seq<Event>,nat))
    requires x.cfg.net.locals==local_rmw_cells().locals, live(x.cfg.net,at(crate::origin(b.branch))),
        (x.cfg.private)(at(crate::origin(b.branch)))==(p.initial)(at(crate::origin(b.branch))), can_offer(p,b,o),
    ensures ({
        let m=net::implementation(k,p); let (s,h)=issued; let y=asm::drive(m,x,s);
        background_prefix(m,x,s) && frame(x,y,crate::origin(b.branch))
            && y.cfg.net.pending.get(h)==Some(copy(b)) && net::message(k,h,copy(b)).id==o.id
    }),
{
    let m=net::implementation(k,p); let r=crate::origin(b.branch);
    let pre=run_site(p,k,x,r,o.steps); let q=asm::drive(m,x,pre);
    let e=local_step(p,k,q,r,Action::Send(o.id,copy(b)));
    join(m,x,pre,seq![e]);
    let y=read::next(m,q,e);
    vstd::map_lib::lemma_submap_of_trans(x.cfg.net.pending,q.cfg.net.pending,y.cfg.net.pending);
    (pre+seq![e],e->Send_0)
}

pub struct Cut { pub pre: Seq<Event>, pub five: nat, pub two: nat }

// Replica work before the first strong invocation. A receipt names a live
// occurrence in the current queue. Inter-replica control traffic can use
// either path. There is no raw local write or extra client invocation.
pub open spec fn replica_input(e: Observation) -> bool {
    match e.action {
        Action::Strong(Process::At(_)) => true,
        Action::Send(_, packet) => packet.from is At && packet.to is At,
        Action::Deliver(_) => e.incoming.is_some() && e.incoming.unwrap().from is At && e.incoming.unwrap().to is At,
        _ => false,
    }
}

pub open spec fn replica_prefix<S>(m: Program<S>, x: State<S>, s: Seq<Event>) -> bool
    decreases s.len(),
{
    s.len() == 0 || {
        let a = s[0];
        let y = read::next(m,x,a);
        replica_input(process_step(x.cfg.net,a)) && read::prefix_step(m)(x,a,y)
            && replica_prefix(m,y,s.drop_first())
    }
}

// Weak order evidence may depend on the whole pre-invocation history of
// actual callbacks. Queue handles are absent; payload IDs and cells remain.
pub open spec fn callbacks(k: Headers, n: crate::read_call::Net, s: Seq<Event>) -> Seq<Observation>
    decreases s.len(),
{
    if s.len()==0 {seq![]} else {
        let a=s[0];
        seq![net::callback(k,process_step(n,a))]+callbacks(k,advance(|x,w|cell(x,w),n,a),s.drop_first())
    }
}

pub open spec fn channel_callbacks<S>(p: Program<S>, x: net::Channel<S>, ts: Seq<net::Turn>) -> Seq<Observation>
    decreases ts.len(),
{
    if ts.len()==0 {seq![]} else {
        seq![net::public_input(x.local.cfg.net,x.packets,ts[0].0)]
            +channel_callbacks(p,net::apply_turn(p,x,ts[0]),ts.drop_first())
    }
}

pub open spec fn replica_word(word: Seq<Observation>) -> bool {
    forall|i:int| 0<=i<word.len() ==> replica_input(#[trigger] word[i])
}

pub(crate) proof fn lift_replica_callbacks<S>(p: Program<S>, k: Headers, x: State<S>, s: Seq<Event>,
    public: net::Channel<S>, ts: Seq<net::Turn>)
    requires net::same_callbacks(p,k,x,s,public,ts), asm::prefix(net::implementation(k,p),x,s,true),
        replica_word(channel_callbacks(p,public,ts)),
    ensures replica_prefix(net::implementation(k,p),x,s),callbacks(k,x.cfg.net,s)==channel_callbacks(p,public,ts),
    decreases s.len(),
{
    if s.len()>0 {
        let m=net::implementation(k,p);
        let u=net::apply_turn(p,public,ts[0]);
        let tail=channel_callbacks(p,u,ts.drop_first());
        let word=channel_callbacks(p,public,ts);
        assert(replica_input(word[0]));
        assert(replica_input(process_step(x.cfg.net,s[0])));
        assert forall|i:int| 0<=i<tail.len() implies replica_input(#[trigger] tail[i]) by {
            assert(tail[i]==word[i+1]);
        }
        lift_replica_callbacks(p,k,read::next(m,x,s[0]),s.drop_first(),u,ts.drop_first());
    }
}

pub proof fn join_replica_prefix<S>(m: Program<S>, x: State<S>, s: Seq<Event>, t: Seq<Event>)
    ensures replica_prefix(m,x,s+t) == (replica_prefix(m,x,s) && replica_prefix(m,asm::drive(m,x,s),t)),
    decreases s.len(),
{
    if s.len() == 0 { assert(s+t =~= t); } else {
        assert((s+t).drop_first() =~= s.drop_first()+t);
        join_replica_prefix(m,read::next(m,x,s[0]),s.drop_first(),t);
    }
}

// This receipt changes R3's read-visible cell to v, which remains there up
// to the strong invocation. Its sender and occurrence come from this arm.
pub open spec fn applies_at<S>(m: Program<S>, x: State<S>, s: Seq<Event>, v: int, i: int) -> bool {
    let q = asm::drive(m,x,s.take(i));
    let a = s[i];
    let packet = q.cfg.net.pending.get(a->Deliver_0);
    0 <= i < s.len() && a is Deliver && packet.is_some() && packet.unwrap().from is At
        && packet.unwrap().to == at(Replica::R3) && packet.unwrap().path == Path::Weak
        && packet.unwrap().input == Wire::Copy(v) && (q.cfg.net.locals)(Replica::R3) != v
        && read::prefix_step(m)(q,a,read::next(m,q,a))
        && (read::next(m,q,a).cfg.net.locals)(Replica::R3) == v
        && forall|j:int| i<j<=s.len() ==> (asm::drive(m,x,#[trigger] s.take(j)).cfg.net.locals)(Replica::R3)==v
}

pub(crate) proof fn find_application<S>(m: Program<S>, x: State<S>, s: Seq<Event>, v: int) -> (i: int)
    requires replica_prefix(m,x,s), (x.cfg.net.locals)(Replica::R3) != v,
        (asm::drive(m,x,s).cfg.net.locals)(Replica::R3) == v,
    ensures applies_at(m,x,s,v,i),
    decreases s.len(),
{
    assert(s.len() > 0);
    let last = s.len() as int-1;
    let pre = s.take(last);
    let a = s[last];
    let q = asm::drive(m,x,pre);
    assert(pre+seq![a] =~= s);
    join_replica_prefix(m,x,pre,seq![a]); asm::prefix_concat(m,x,pre,seq![a],true);
    assert(asm::drive(m,q,seq![a])==read::next(m,q,a)) by {reveal_with_fuel(asm::drive,2);}
    assert(s.take(s.len() as int) =~= s);
    if (q.cfg.net.locals)(Replica::R3) != v {
        assert(replica_input(process_step(q.cfg.net,a)));
        last
    } else {
        let i = find_application(m,x,pre,v);
        assert(pre[i]==s[i] && pre.take(i) =~= s.take(i));
        assert forall|j:int| i<j<=s.len() implies (asm::drive(m,x,#[trigger] s.take(j)).cfg.net.locals)(Replica::R3)==v by {
            if j<=last {assert(pre.take(j) =~= s.take(j));}
        }
        i
    }
}

// Before the choice at R3, a receipt is classified by the packet currently
// in the queue. This permits receipts at either origin, including data and
// acknowledgments. At R3 it defers either candidate value's installation,
// irrespective of the sender or the occurrence used to transport it.
pub open spec fn preparation_input(e: Observation) -> bool {
    match e.action {
        Action::Deliver(_) => {
            let p = e.incoming.unwrap();
            e.incoming.is_some() && p.path == Path::Weak && p.from is At && p.to is At
                && !(p.to == at(Replica::R3) && (p.input == Wire::Copy(2) || p.input == Wire::Copy(5)))
        },
        _ => wc::background(e.action),
    }
}

pub open spec fn before_candidate(n: crate::read_call::Net, a: Event) -> bool {
    preparation_input(process_step(n,a))
}

pub open spec fn weak_preparation<S>(m: Program<S>, x: State<S>, s: Seq<Event>) -> bool
    decreases s.len(),
{
    s.len() == 0 || {
        let a = s[0];
        let y = read::next(m, x, a);
        before_candidate(x.cfg.net, a) && read::prefix_step(m)(x, a, y)
            && weak_preparation(m, y, s.drop_first())
    }
}

// Keep the earlier independent local preparations as a sufficient subcase.
pub proof fn sends_only_preparation<S>(m: Program<S>, x: State<S>, s: Seq<Event>)
    requires background_prefix(m, x, s),
    ensures weak_preparation(m, x, s), asm::drive(m, x, s).cfg.net.locals == x.cfg.net.locals,
    decreases s.len(),
{
    if s.len() > 0 {
        let a = s[0];
        let y = read::next(m, x, a);
        let t = s.drop_first();
        assert(wc::background(a));
        assert(y.cfg.net.locals =~= x.cfg.net.locals);
        assert forall|i: int| 0 <= i < t.len() implies #[trigger] wc::background(t[i]) by {
            assert(t[i] == s[i+1]);
        }
        sends_only_preparation(m, y, t);
    }
}

pub open spec fn shared_cut<S>(p: Program<S>, k: Headers, n: Notice, c: Cut) -> bool {
    let m = net::implementation(k,p);
    let x = wc::start(m);
    let q = asm::drive(m, x, c.pre);
    weak_preparation(m, x, c.pre) && survivor(q.cfg.net) == (2int,5int)
        && wc::ready_copy(m, q, alpha(n), c.five) && wc::ready_copy(m, q, beta(n), c.two)
}

pub open spec fn public_weak_inputs<S>(p: Program<S>, public: net::Channel<S>, ts: Seq<net::Turn>) -> bool
    decreases ts.len(),
{
    ts.len() == 0 || (preparation_input(net::public_input(public.local.cfg.net, public.packets, ts[0].0))
        && public_weak_inputs(p, net::apply_turn(p,public,ts[0]), ts.drop_first()))
}

proof fn matched_preparation<S>(p: Program<S>, k: Headers, x: State<S>, s: Seq<Event>,
    public: net::Channel<S>, ts: Seq<net::Turn>)
    requires asm::prefix(net::implementation(k,p), x, s, true),
        net::same_callbacks(p,k,x,s,public,ts), public_weak_inputs(p,public,ts),
    ensures weak_preparation(net::implementation(k,p),x,s),
    decreases s.len(),
{
    if s.len() > 0 {
        let m = net::implementation(k,p);
        let a = s[0];
        assert(preparation_input(net::callback(k,process_step(x.cfg.net,a))));
        assert(before_candidate(x.cfg.net,a));
        matched_preparation(p,k,read::next(m,x,a),s.drop_first(),net::apply_turn(p,public,ts[0]),ts.drop_first());
    }
}

// A witness may be given directly as a guarded schedule on the independent
// queue. The map translates its live occurrences, including the two choices
// for R3. All earlier send, receipt and acknowledgment callbacks agree.
pub proof fn shared_cut_from_channel<S>(p: Program<S>, k: Headers, n: Notice, ts: Seq<net::Turn>,
    five: nat, two: nat) -> (result: (Cut,Map<nat,nat>))
    requires ({
        let public = net::snapshot(k,wc::start(net::implementation(k,p)));
        let z = net::end(p,public,ts);
        net::trace(p,public,ts,true) && public_weak_inputs(p,public,ts)
            && survivor(z.local.cfg.net) == (2int,5int)
            && net::permitted(p,z.local,z.packets,Command::Deliver(five),false) && z.packets[five].body == copy(alpha(n))
            && net::permitted(p,z.local,z.packets,Command::Deliver(two),false) && z.packets[two].body == copy(beta(n))
    }),
    ensures ({
        let (c, keys) = result;
        let m = net::implementation(k,p);
        let x = wc::start(m);
        let q = asm::drive(m,x,c.pre);
        let public = net::snapshot(k,x);
        let z = net::end(p,public,ts);
        shared_cut(p,k,n,c) && net::same_callbacks(p,k,x,c.pre,public,ts)
            && z.local == net::control(q) && net::represents(z.packets,keys,net::queue(k,q.cfg.net))
            && keys.get(five) == Some(c.five) && keys.get(two) == Some(c.two)
    }),
{
    let m = net::implementation(k,p);
    let x = wc::start(m);
    let public = net::snapshot(k,x);
    assert(public.packets =~= Map::empty());
    let (s,keys) = net::lift_prefix(p,k,x,public,Map::empty(),ts,true,|_s:S|None);
    matched_preparation(p,k,x,s,public,ts);
    let q = asm::drive(m,x,s);
    let z = net::end(p,public,ts);
    assert forall|h:nat| #[trigger] z.packets.contains_key(h) implies
        net::callback(k,process_step(q.cfg.net,Action::Deliver(keys[h])))
            == net::public_input(z.local.cfg.net,z.packets,Command::Deliver(h)) by {
        assert(keys.contains_key(h));
        assert(net::queue(k,q.cfg.net).get(keys[h]) == Some(z.packets[h]));
    }
    (Cut {pre:s, five:keys[five], two:keys[two]}, keys)
}

// A receipt on a survivor, including an ACK, can itself be a preparation
// step. The callback may update all of its private state. The register cell
// changes according to the delivered body. An installing receipt at R3
// uses this same transition after the common prefix.
pub proof fn weak_receipt<S>(p: Program<S>, k: Headers, x: State<S>, h: nat)
    requires net::ready(p, k, x, Command::Deliver(h), false), ({
        let packet = x.cfg.net.pending[h];
        packet.path == Path::Weak && packet.from is At && packet.to is At
    }),
    ensures ({
        let m = net::implementation(k,p);
        let a = Action::Deliver(h);
        let y = read::next(m, x, a);
        let packet = x.cfg.net.pending[h];
        let r = packet.to->At_0;
        let input = net::input(k, x.cfg.net, Command::Deliver(h));
        asm::prefix(m, x, seq![a], true) && asm::drive(m, x, seq![a]) == y
            && (before_candidate(x.cfg.net, a) ==> weak_preparation(m, x, seq![a]))
            && input.incoming == Some(packet) && input.actor == at(r)
            && (y.cfg.private)(at(r)) == (p.update)((x.cfg.private)(at(r)), input)
            && (y.cfg.net.locals)(r) == cell((x.cfg.net.locals)(r), packet.input)
            && (forall|c: Process| c != at(r) ==> (#[trigger] (y.cfg.private)(c)) == (x.cfg.private)(c))
            && (forall|other: Replica| other != r ==> (#[trigger] (y.cfg.net.locals)(other)) == (x.cfg.net.locals)(other))
            && y.cfg.net.pending == x.cfg.net.pending.remove(h)
            && net::queue(k, y.cfg.net) == net::queue(k, x.cfg.net).remove(h)
    }),
{
    net::project_step(p, k, x, Action::Deliver(h), false);
    reveal_with_fuel(asm::prefix, 2);
    reveal_with_fuel(asm::drive, 2);
    reveal_with_fuel(weak_preparation, 2);
}

pub open spec fn ready_pair<S>(p: Program<S>, k: Headers, n: Notice, cut: Cut) -> bool {
    let m=net::implementation(k,p); let x=wc::start(m); let q=asm::drive(m,x,cut.pre);
    background_prefix(m,x,cut.pre) && wc::ready_copy(m,q,alpha(n),cut.five) && wc::ready_copy(m,q,beta(n),cut.two)
}

// Run the two origins once, before the choice at R3. The two origins may
// have different local work and may reuse the same application message ID.
proof fn collect_offers<S>(p: Program<S>, k: Headers, n: Notice, five: Offer, two: Offer) -> (c: Cut)
    requires can_offer(p,alpha(n),five), can_offer(p,beta(n),two),
    ensures ({
        let m=net::implementation(k,p); let x=wc::start(m); let z=asm::drive(m,x,c.pre);
        background_prefix(m,x,c.pre) && z.cfg.net.locals==x.cfg.net.locals && live(z.cfg.net,at(Replica::R3))
            && (z.cfg.private)(at(Replica::R3))==(p.initial)(at(Replica::R3))
            && z.cfg.net.pending.get(c.five)==Some(copy(alpha(n))) && net::message(k,c.five,copy(alpha(n))).id==five.id
            && z.cfg.net.pending.get(c.two)==Some(copy(beta(n))) && net::message(k,c.two,copy(beta(n))).id==two.id
    }),
{
    let m=net::implementation(k,p); let x=wc::start(m);
    let (left,h)=issue(p,k,x,beta(n),two); let y=asm::drive(m,x,left);
    let (right,j)=issue(p,k,y,alpha(n),five); let z=asm::drive(m,y,right);
    join(m,x,left,right);
    carry(y.cfg.net.pending,z.cfg.net.pending,h);
    Cut { pre:left+right, five:j, two:h }
}

proof fn receipt_guard<S>(p: Program<S>, k: Headers, x: State<S>, r3work: Seq<Event>, b: Fork, h: nat)
    requires x.cfg.net.locals==local_rmw_cells().locals, x.cfg.net.pending.get(h)==Some(copy(b)),
        walk(p,Replica::R3,(p.initial)(at(Replica::R3)),r3work)==Some((x.cfg.private)(at(Replica::R3))),
        can_take(p,r3work,b,net::message(k,h,copy(b)).id),
    ensures wc::ready_copy(net::implementation(k,p),x,b,h),
{
    crate::isolated_rmws();
    assert(net::callback(k,process_step(x.cfg.net,Action::Deliver(h)))==receive(b,net::message(k,h,copy(b)).id));
}

// For the literal common pre-delivery state, one receiver preparation
// accepting both inputs is necessary and sufficient (converse below).
pub proof fn schedule_offers<S>(p: Program<S>, k: Headers, n: Notice, five: Offer, two: Offer, receiver: Seq<Event>)
    -> (cut: Cut)
    requires can_offer(p,alpha(n),five), can_offer(p,beta(n),two),
        can_take(p,receiver,alpha(n),five.id), can_take(p,receiver,beta(n),two.id),
    ensures ready_pair(p,k,n,cut),
        paired_installation(p,k,n,(cut,seq![],seq![])),
        net::message(k,cut.five,copy(alpha(n))).id==five.id && net::message(k,cut.two,copy(beta(n))).id==two.id,
{
    let c=collect_offers(p,k,n,five,two);
    let m=net::implementation(k,p); let x=wc::start(m); let z=asm::drive(m,x,c.pre);
    let t=run_site(p,k,z,Replica::R3,receiver); let q=asm::drive(m,z,t);
    join(m,x,c.pre,t);
    carry(z.cfg.net.pending,q.cfg.net.pending,c.five); carry(z.cfg.net.pending,q.cfg.net.pending,c.two);
    receipt_guard(p,k,q,receiver,alpha(n),c.five); receipt_guard(p,k,q,receiver,beta(n),c.two);
    let cut=Cut { pre:c.pre+t, ..c };
    assert(cut.pre+Seq::empty() =~= cut.pre);
    wc::exposed_at_common_cut(p,k,cut.pre,alpha(n),cut.five);
    wc::exposed_at_common_cut(p,k,cut.pre,beta(n),cut.two);
    cut
}

proof fn source_of_copy<S>(p: Program<S>, k: Headers, pre: Seq<Event>, b: Fork, h: nat) -> (o: Offer)
    requires ({
        let m=net::implementation(k,p); let x=wc::start(m);
        background_prefix(m,x,pre) && wc::ready_copy(m,asm::drive(m,x,pre),b,h)
    }),
    ensures can_offer(p,b,o), o.id==net::message(k,h,copy(b)).id,
{
    let m=net::implementation(k,p); let x=wc::start(m); let packet=copy(b);
    wc::exposed_at_common_cut(p,k,pre,b,h);
    let ev=Action::Send(h,packet);
    let i=choose|i:int| 0<=i<pre.len() && #[trigger] pre[i]==ev;
    let head=pre.take(i); let tail=pre.skip(i); assert(head+tail =~= pre);
    join(m,x,head,tail);
    let q=asm::drive(m,x,head); let r=crate::origin(b.branch);
    let word=project_site(p,k,x,head,r);
    assert(tail[0]==ev);
    assert(read::prefix_step(m)(q,ev,read::next(m,q,ev)));
    Offer { steps:word, id:net::message(k,h,packet).id }
}

// The converse extracts witnesses from the actual sends and the complete
// receiver transcript; the test cannot exclude a guarded common cut of
// this form.
pub proof fn guards_at_cut<S>(p: Program<S>, k: Headers, n: Notice, c: Cut) -> (w: (Offer,Offer,Seq<Event>))
    requires ready_pair(p,k,n,c),
    ensures can_offer(p,alpha(n),w.0) && can_offer(p,beta(n),w.1)
        && can_take(p,w.2,alpha(n),w.0.id) && can_take(p,w.2,beta(n),w.1.id),
{
    let m=net::implementation(k,p); let x=wc::start(m); let q=asm::drive(m,x,c.pre);
    let a=alpha(n); let b=beta(n);
    let five=source_of_copy(p,k,c.pre,a,c.five); let two=source_of_copy(p,k,c.pre,b,c.two);
    let receiver=project_site(p,k,x,c.pre,Replica::R3);
    crate::isolated_rmws();
    assert(net::callback(k,process_step(q.cfg.net,Action::Deliver(c.five)))==receive(a,five.id));
    assert(net::callback(k,process_step(q.cfg.net,Action::Deliver(c.two)))==receive(b,two.id));
    (five,two,receiver)
}

// A single-arm input is an actual possible first receipt. Its preparation
// need not contain the other copy, or share any schedule with the other arm.
pub open spec fn opportunity<S>(p: Program<S>, k: Headers, b: Fork, pre: Seq<Event>, h: nat) -> bool {
    let m=net::implementation(k,p); let x=wc::start(m);
    background_prefix(m,x,pre) && wc::ready_copy(m,asm::drive(m,x,pre),b,h)
}

pub open spec fn receiver_state<S>(p: Program<S>, k: Headers, pre: Seq<Event>) -> S {
    let m=net::implementation(k,p);
    (asm::drive(m,wc::start(m),pre).cfg.private)(at(Replica::R3))
}

proof fn single_guards<S>(p: Program<S>, k: Headers, b: Fork, pre: Seq<Event>, h: nat)
    -> (w: (Offer,Seq<Event>))
    requires opportunity(p,k,b,pre,h),
    ensures can_offer(p,b,w.0), can_take(p,w.1,b,w.0.id), w.0.id==net::message(k,h,copy(b)).id,
        walk(p,Replica::R3,(p.initial)(at(Replica::R3)),w.1)==Some(receiver_state(p,k,pre)),
{
    let m=net::implementation(k,p); let x=wc::start(m); let q=asm::drive(m,x,pre);
    let o=source_of_copy(p,k,pre,b,h); let t=project_site(p,k,x,pre,Replica::R3);
    crate::isolated_rmws();
    assert(net::callback(k,process_step(q.cfg.net,Action::Deliver(h)))==receive(b,o.id));
    (o,t)
}

pub open spec fn installation<S>(p: Program<S>, k: Headers, b: Fork, c: Cut, t: Seq<Event>) -> bool {
    let m=net::implementation(k,p); let x=wc::start(m); let common=asm::drive(m,x,c.pre);
    let a=b.branch==crate::Branch::Alpha; let h=if a { c.five } else { c.two };
    let rival=if a { c.two } else { c.five }; let other=if a { beta(b.notice) } else { alpha(b.notice) };
    let pre=c.pre+t; let q=asm::drive(m,x,pre);
    let s=pre+seq![Action::Deliver(h)]; let y=asm::drive(m,x,s);
    at_site(t,Replica::R3) && opportunity(p,k,b,pre,h)
        && common.cfg.net.pending.get(h)==Some(copy(b)) && common.cfg.net.pending.get(rival)==Some(copy(other))
        && asm::prefix(m,x,s,true) && net::trace(p,net::snapshot(k,x),net::turns(k,s),true)
        && net::end(p,net::snapshot(k,x),net::turns(k,s))==net::snapshot(k,y)
        && y.cfg.net.pending==q.cfg.net.pending.remove(h) && y.cfg.net.pending.get(rival)==Some(copy(other))
        && (y.cfg.net.locals)(Replica::R3)==first_value(b) && survivor(y.cfg.net)==(2int,5int)
        && forall|c:Process| c!=at(Replica::R3) ==> (y.cfg.private)(c)==(#[trigger] (common.cfg.private)(c))
}

proof fn install_one<S>(p: Program<S>, k: Headers, b: Fork, c: Cut, work: Seq<Event>) -> (t: Seq<Event>)
    requires ({
        let m=net::implementation(k,p); let x=wc::start(m); let z=asm::drive(m,x,c.pre);
        let h=if b.branch==crate::Branch::Alpha { c.five } else { c.two };
        background_prefix(m,x,c.pre) && z.cfg.net.locals==x.cfg.net.locals && live(z.cfg.net,at(Replica::R3))
            && (z.cfg.private)(at(Replica::R3))==(p.initial)(at(Replica::R3))
            && z.cfg.net.pending.get(c.five)==Some(copy(alpha(b.notice))) && z.cfg.net.pending.get(c.two)==Some(copy(beta(b.notice)))
            && can_take(p,work,b,net::message(k,h,copy(b)).id)
    }),
    ensures installation(p,k,b,c,t),
        walk(p,Replica::R3,(p.initial)(at(Replica::R3)),work)==Some(receiver_state(p,k,c.pre+t)),
{
    let m=net::implementation(k,p); let x=wc::start(m); let z=asm::drive(m,x,c.pre);
    let t=run_site(p,k,z,Replica::R3,work); join(m,x,c.pre,t);
    let h=if b.branch==crate::Branch::Alpha { c.five } else { c.two };
    let q=asm::drive(m,z,t);
    carry(z.cfg.net.pending,q.cfg.net.pending,c.five); carry(z.cfg.net.pending,q.cfg.net.pending,c.two);
    receipt_guard(p,k,q,work,b,h);
    wc::exposed_at_common_cut(p,k,c.pre+t,b,h);
    t
}

pub open spec fn local_guards<S>(p: Program<S>, b: Fork, w: (Offer,Seq<Event>)) -> bool {
    can_offer(p,b,w.0) && can_take(p,w.1,b,w.0.id)
}

pub open spec fn selective_input<S>(p: Program<S>, b: Fork) -> bool {
    exists|w:(Offer,Seq<Event>)| #[trigger] local_guards(p,b,w)
}

pub open spec fn paired_installation<S>(p: Program<S>, k: Headers, n: Notice, f: (Cut,Seq<Event>,Seq<Event>)) -> bool {
    installation(p,k,alpha(n),f.0,f.1) && installation(p,k,beta(n),f.0,f.2)
}

// No common queue, send ID, receiver state, future read or H witness is
// required of the two local tests. All origin work is shared in the
// realized executions. Branch-specific work at R3 is retained in full.
pub proof fn selective_visibility_exact<S>(p: Program<S>, k: Headers, n: Notice)
    ensures (selective_input(p,alpha(n)) && selective_input(p,beta(n)))
        == (exists|f:(Cut,Seq<Event>,Seq<Event>)| #[trigger] paired_installation(p,k,n,f)),
{
    let a=alpha(n); let b=beta(n);
    if selective_input(p,a) && selective_input(p,b) {
        let (five,aw)=choose|w:(Offer,Seq<Event>)| #[trigger] local_guards(p,a,w);
        let (two,bw)=choose|w:(Offer,Seq<Event>)| #[trigger] local_guards(p,b,w);
        let c=collect_offers(p,k,n,five,two);
        let ta=install_one(p,k,a,c,aw); let tb=install_one(p,k,b,c,bw);
        assert(paired_installation(p,k,n,(c,ta,tb)));
    } else if exists|f:(Cut,Seq<Event>,Seq<Event>)| #[trigger] paired_installation(p,k,n,f) {
        let (c,ta,tb)=choose|f:(Cut,Seq<Event>,Seq<Event>)| #[trigger] paired_installation(p,k,n,f);
        let wa=single_guards(p,k,a,c.pre+ta,c.five); let wb=single_guards(p,k,b,c.pre+tb,c.two);
        assert(local_guards(p,a,wa) && local_guards(p,b,wb));
    }
}

pub proof fn separate_opportunities_compose<S>(p: Program<S>, k: Headers, n: Notice,
    a: Seq<Event>, five: nat, b: Seq<Event>, two: nat) -> (fork: (Cut,Seq<Event>,Seq<Event>))
    requires opportunity(p,k,alpha(n),a,five), opportunity(p,k,beta(n),b,two),
    ensures paired_installation(p,k,n,fork),
        net::message(k,fork.0.five,copy(alpha(n))).id==net::message(k,five,copy(alpha(n))).id,
        net::message(k,fork.0.two,copy(beta(n))).id==net::message(k,two,copy(beta(n))).id,
        receiver_state(p,k,fork.0.pre+fork.1)==receiver_state(p,k,a),
        receiver_state(p,k,fork.0.pre+fork.2)==receiver_state(p,k,b),
{
    let (fo,aw)=single_guards(p,k,alpha(n),a,five); let (to,bw)=single_guards(p,k,beta(n),b,two);
    let c=collect_offers(p,k,n,fo,to);
    (c,install_one(p,k,alpha(n),c,aw),install_one(p,k,beta(n),c,bw))
}

}
