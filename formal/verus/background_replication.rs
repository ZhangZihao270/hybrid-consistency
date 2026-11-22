// Background replication after a local weak return, and its application
// to the original two reads. All queue occurrences and callbacks are real.
use vstd::prelude::*;
use crate::{Op, Replica, checkpoint::*, delivery::*};
use crate::async_fork as af;
use crate::async_messages::{self as net, Headers};
use crate::first_assembly as asm;
use crate::independent_read::{self as read, State};
use crate::original_application::all_available;
use crate::prepared_hot as hot;
use crate::prepared_service as svc;
use crate::read_call::{Event, Program};
use crate::weak_construction as wc;
use crate::weak_visibility as vis;

verus! {

// No later client action is needed for replication. An idle tick lets a
// finished, passive system have a fair infinite continuation.
pub struct Run<S> { pub state: spec_fn(nat)->State<S>, pub turn: spec_fn(nat)->Option<Event> }

pub open spec fn replica_step<S>(m: Program<S>, x: State<S>, a: Event) -> bool {
    vis::replica_input(process_step(x.cfg.net,a)) && read::prefix_step(m)(x,a,read::next(m,x,a))
}
pub open spec fn follows<S>(m: Program<S>, base: State<S>, e: Run<S>) -> bool {
    (e.state)(0) == base && forall|i:nat| {
        let x = (e.state)(i);
        match #[trigger] (e.turn)(i) {
            None => (e.state)(i+1) == x,
            Some(a) => replica_step(m,x,a) && (e.state)(i+1) == read::next(m,x,a),
        }
    }
}
pub open spec fn runnable<S>(m: Program<S>, x: State<S>, r: Replica) -> bool {
    exists|a:Event| #[trigger] replica_step(m,x,a) && process_step(x.cfg.net,a).actor == at(r)
}
pub open spec fn receives<S>(e: Run<S>, i: nat, h: nat) -> bool {
    (e.turn)(i) == Some(Action::Deliver(h))
}
pub open spec fn runs_at<S>(e: Run<S>, i: nat, r: Replica) -> bool {
    (e.turn)(i).is_some() && process_step((e.state)(i).cfg.net,(e.turn)(i).unwrap()).actor == at(r)
}
pub open spec fn continuously_runnable<S>(m: Program<S>, e: Run<S>, i: nat, r: Replica) -> bool {
    forall|j:nat| j>=i ==> #[trigger] runnable(m,(e.state)(j),r)
}
pub open spec fn fair_background<S>(m: Program<S>, base: State<S>, e: Run<S>) -> bool {
    follows(m,base,e)
        && (forall|i:nat,h:nat| #[trigger] (e.state)(i).cfg.net.pending.contains_key(h)
            && live((e.state)(i).cfg.net,(e.state)(i).cfg.net.pending[h].to)
            ==> exists|j:nat| j>=i && #[trigger] receives(e,j,h))
        && forall|i:nat,r:Replica| #[trigger] continuously_runnable(m,e,i,r)
            ==> exists|j:nat| j>=i && #[trigger] runs_at(e,j,r)
}

pub open spec fn events<S>(e: Run<S>, n: nat) -> Seq<Event>
    decreases n,
{
    if n == 0 { seq![] } else {
        let i = (n-1) as nat;
        match (e.turn)(i) { None => events(e,i), Some(a) => events(e,i).push(a) }
    }
}
proof fn finite_prefix<S>(m: Program<S>, base: State<S>, e: Run<S>, n: nat)
    requires follows(m,base,e),
    ensures vis::replica_prefix(m,base,events(e,n)), asm::drive(m,base,events(e,n)) == (e.state)(n),
        (e.state)(n).cfg.net.unavailable == base.cfg.net.unavailable,
        (e.state)(n).cfg.net.r3_crashed == base.cfg.net.r3_crashed,
    decreases n,
{
    if n>0 {
        let i=(n-1) as nat;
        finite_prefix(m,base,e,i);
        if let Some(a)=(e.turn)(i) {
            let x=(e.state)(i);
            assert(replica_step(m,x,a));
            assert(vis::replica_prefix(m,x,seq![a])) by { reveal_with_fuel(vis::replica_prefix,2); }
            assert(events(e,n) =~= events(e,i)+seq![a]);
            vis::join_replica_prefix(m,base,events(e,i),seq![a]);
            asm::prefix_concat(m,base,events(e,i),seq![a],true);
            assert(asm::drive(m,x,seq![a]) == read::next(m,x,a)) by { reveal_with_fuel(asm::drive,2); }
        }
    }
}

// An implementation supplies the interpretation of a local stored command,
// delta, or incorporated state. It sees no queue, schedule or read result.
pub type Stored<S> = spec_fn(Replica,S,int,Op)->bool;
pub struct Hop { pub sent: nat, pub delivered: nat }
pub open spec fn body<S>(e: Run<S>, hop: Hop) -> Packet<Wire> {
    (e.turn)(hop.sent).unwrap()->Send_1
}
pub open spec fn hop_taken<S>(e: Run<S>, hop: Hop) -> bool {
    let turn = (e.turn)(hop.sent);
    let a = turn.unwrap();
    let h = a->Send_0;
    let packet = body(e,hop);
    turn.is_some() && a is Send && hop.sent < hop.delivered
        && packet.from is At && packet.to is At
        && receives(e,hop.delivered,h) && (e.state)(hop.delivered).cfg.net.pending.get(h)==Some(packet)
        && forall|t:nat| hop.sent<t<hop.delivered ==> !#[trigger] receives(e,t,h)
}
// A potential causal path from the origin. A relay can process other
// inputs before forwarding. A hop need not expose the writer in its body.
pub open spec fn route<S>(e: Run<S>, src: Replica, dst: Replica, t: nat, hops: Seq<Hop>) -> bool {
    hops.len()>0 && body(e,hops.first()).from==at(src) && body(e,hops.last()).to==at(dst)
        && forall|j:int| 0<=j<hops.len() ==> #[trigger] hop_taken(e,hops[j]) && hops[j].delivered<t
            && (j==0 || (hops[j-1].delivered<hops[j].sent && body(e,hops[j-1]).to==body(e,hops[j]).from))
}
proof fn route_starts_live<S>(m: Program<S>, base: State<S>, e: Run<S>, src: Replica, dst: Replica,
    t: nat, hops: Seq<Hop>)
    requires follows(m,base,e), route(e,src,dst,t,hops),
    ensures live(base.cfg.net,at(src)),
{
    let hop=hops.first();
    assert(hop_taken(e,hops[0]));
    let i=hop.sent; let a=(e.turn)(i).unwrap();
    assert(replica_step(m,(e.state)(i),a));
    assert(live((e.state)(i).cfg.net,at(src)));
    finite_prefix(m,base,e,i);
}
// The caller identifies sites and queued occurrences already downstream of
// this write at the boundary. An eager send before the local reply counts.
pub struct Frontier { pub sites: Set<Replica>, pub packets: Set<nat> }
pub open spec fn isolated(src: Replica) -> Frontier {
    Frontier { sites: set![src], packets: Set::empty() }
}
pub open spec fn entry_receipt<S>(e: Run<S>, h: nat, i: nat) -> bool {
    let q=(e.state)(0).cfg.net.pending;
    q.contains_key(h) && q[h].to is At && receives(e,i,h)
        && (e.state)(i).cfg.net.pending.get(h)==Some(q[h]) && forall|j:nat| j<i ==> !#[trigger] receives(e,j,h)
}
pub open spec fn downstream<S>(e: Run<S>, f: Frontier, dst: Replica, t: nat) -> bool {
    f.sites.contains(dst)
        || (exists|src:Replica,hops:Seq<Hop>| f.sites.contains(src) && #[trigger] route(e,src,dst,t,hops))
        || exists|h:nat,i:nat| f.packets.contains(h) && i<t && #[trigger] entry_receipt(e,h,i) && {
            let relay=(e.state)(0).cfg.net.pending[h].to->At_0;
            relay==dst || exists|hops:Seq<Hop>| #[trigger] route(e,relay,dst,t,hops) && i<hops.first().sent
        }
}
pub open spec fn replicated<S>(d: Stored<S>, e: Run<S>, w: Op, f: Frontier, src: Replica, dst: Replica, t: nat) -> bool {
    let x=(e.state)(t);
    src!=dst && live(x.cfg.net,at(dst)) && d(dst,(x.cfg.private)(at(dst)),(x.cfg.net.locals)(dst),w)
        && downstream(e,f,dst,t)
}
// With all replicas as destinations this requires one live remote copy.
// A smaller destination set describes a stronger coverage promise. This
// formulation concerns a suffix with a stable set of available replicas.
pub open spec fn background_replication<S>(m: Program<S>, base: State<S>, w: Op, src: Replica,
    f: Frontier, dest: Set<Replica>, d: Stored<S>) -> bool {
    live(base.cfg.net,at(src)) && d(src,(base.cfg.private)(at(src)),(base.cfg.net.locals)(src),w)
        && f.sites.contains(src) && f.packets.subset_of(base.cfg.net.pending.dom())
        && (exists|e:Run<S>| #[trigger] fair_background(m,base,e))
        && forall|e:Run<S>| #[trigger] fair_background(m,base,e) ==>
            exists|r:Replica,t:nat| dest.contains(r) && #[trigger] replicated(d,e,w,f,src,r,t)
}

proof fn route_from_origin<S>(d: Stored<S>, e: Run<S>, w: Op, src: Replica, r: Replica, t: nat)
    -> (path: Seq<Hop>)
    requires replicated(d,e,w,isolated(src),src,r,t),
    ensures route(e,src,r,t,path),
{
    let (s,path)=choose|s:Replica,path:Seq<Hop>| isolated(src).sites.contains(s) && #[trigger] route(e,s,r,t,path);
    assert(s==src);
    path
}

pub proof fn remote_storage_prefix<S>(m: Program<S>, base: State<S>, w: Op, src: Replica,
    dest: Set<Replica>, d: Stored<S>, e: Run<S>) -> (found: (Replica,nat,Seq<Hop>))
    requires background_replication(m,base,w,src,isolated(src),dest,d), fair_background(m,base,e),
    ensures ({
        let (r,t,hops)=found;
        dest.contains(r) && replicated(d,e,w,isolated(src),src,r,t) && route(e,src,r,t,hops)
            && vis::replica_prefix(m,base,events(e,t)) && asm::drive(m,base,events(e,t))==(e.state)(t)
    }),
{
    let (r,t)=choose|r:Replica,t:nat| dest.contains(r) && #[trigger] replicated(d,e,w,isolated(src),src,r,t);
    let hops=route_from_origin(d,e,w,src,r,t);
    finite_prefix(m,base,e,t);
    (r,t,hops)
}

// No particular sender or application ID. A queued value copy still has
// to pass the guarded recipient callback on the chosen fair run.
pub open spec fn offered<S>(e: Run<S>, v: int, i: nat, h: nat) -> bool {
    let q=(e.state)(i).cfg.net.pending;
    q.contains_key(h) && q[h].from is At && q[h].to==at(Replica::R3)
        && q[h].path==Path::Weak && q[h].input==Wire::Copy(v)
}
pub open spec fn installs<S>(e: Run<S>, v: int, i: nat) -> bool {
    let turn=(e.turn)(i);
    let a=turn.unwrap();
    turn.is_some() && a is Deliver && offered(e,v,i,a->Deliver_0)
}
proof fn take_pending<S>(m: Program<S>, base: State<S>, e: Run<S>, v: int, h: nat, i: nat, limit: nat)
    -> (j:nat)
    requires follows(m,base,e), offered(e,v,i,h), i<=limit, receives(e,limit,h),
    ensures i<=j<=limit, receives(e,j,h), offered(e,v,j,h), installs(e,v,j),
    decreases limit-i,
{
    if receives(e,i,h) { i } else {
        if let Some(a)=(e.turn)(i) {
            assert(replica_step(m,(e.state)(i),a));
            if a is Send { assert(a->Send_0!=h); }
        }
        assert((e.state)(i+1).cfg.net.pending.get(h)==(e.state)(i).cfg.net.pending.get(h));
        take_pending(m,base,e,v,h,i+1,limit)
    }
}
proof fn earlier_offer<S>(m: Program<S>, base: State<S>, e: Run<S>, v: int, n: nat) -> (ih:(nat,nat))
    requires follows(m,base,e), (base.cfg.net.locals)(Replica::R3)!=v, ((e.state)(n).cfg.net.locals)(Replica::R3)==v,
    ensures ih.0<n, offered(e,v,ih.0,ih.1), installs(e,v,ih.0),
    decreases n,
{
    assert(n>0); let i=(n-1) as nat;
    if ((e.state)(i).cfg.net.locals)(Replica::R3)==v { earlier_offer(m,base,e,v,i) }
    else {
        let a=(e.turn)(i).unwrap();
        assert((e.turn)(i)==Some(a) && replica_step(m,(e.state)(i),a));
        (i,a->Deliver_0)
    }
}

// Exact for this register's background transitions. A representation that
// buffers a command can satisfy storage replication without emitting Copy.
pub proof fn fair_offer_iff_readable<S>(m: Program<S>, base: State<S>, e: Run<S>, v: int)
    requires fair_background(m,base,e), live(base.cfg.net,at(Replica::R3)), (base.cfg.net.locals)(Replica::R3)!=v,
    ensures (exists|i:nat,h:nat| #[trigger] offered(e,v,i,h))
        == (exists|n:nat| (#[trigger] ((e.state)(n).cfg.net.locals)(Replica::R3))==v),
        (exists|i:nat,h:nat| #[trigger] offered(e,v,i,h)) ==> exists|j:nat| #[trigger] installs(e,v,j),
{
    if exists|i:nat,h:nat| #[trigger] offered(e,v,i,h) {
        let (i,h)=choose|i:nat,h:nat| #[trigger] offered(e,v,i,h);
        finite_prefix(m,base,e,i);
        assert((e.state)(i).cfg.net.pending.contains_key(h));
        let limit=choose|j:nat| j>=i && #[trigger] receives(e,j,h);
        let j=take_pending(m,base,e,v,h,i,limit);
        assert(replica_step(m,(e.state)(j),Action::Deliver(h)));
        assert(((e.state)(j+1).cfg.net.locals)(Replica::R3)==v);
    } else if exists|n:nat| (#[trigger] ((e.state)(n).cfg.net.locals)(Replica::R3))==v {
        let n=choose|n:nat| (#[trigger] ((e.state)(n).cfg.net.locals)(Replica::R3))==v;
        earlier_offer(m,base,e,v,n);
    }
}

// A stopped-peer reference is optional. Its finite replica actions can
// also run with the omitted peer merely delayed, with exactly the same
// callbacks and queues. Only the availability bit is restored.
proof fn lift_prefix<S>(m: Program<S>, x: State<S>, s: Seq<Event>)
    requires vis::replica_prefix(m,x,s),
    ensures vis::replica_prefix(m,all_available(x),s),
        asm::drive(m,all_available(x),s)==all_available(asm::drive(m,x,s)),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0]; let y=read::next(m,x,a); let u=all_available(x);
        assert(replica_step(m,x,a));
        assert(process_step(u.cfg.net,a)==process_step(x.cfg.net,a));
        assert(read::next(m,u,a).cfg.net.locals =~= y.cfg.net.locals);
        assert(read::next(m,u,a).cfg.private =~= y.cfg.private);
        assert(read::next(m,u,a)==all_available(y) && replica_step(m,u,a));
        lift_prefix(m,y,s.drop_first());
    }
}

pub struct Trial<S> { pub background: Run<S>, pub omit_other: bool, pub destinations: Set<Replica> }
pub open spec fn entry<S>(m: Program<S>, b: Fork, trial: Trial<S>) -> State<S> {
    if trial.omit_other { svc::reference(wc::start(m),b) } else { wc::start(m) }
}
pub open spec fn r3_record<S>(d: Stored<S>, b: Fork, e: Run<S>, t: nat) -> bool {
    let src=crate::origin(b.branch);
    replicated(d,e,observed_writer(b),isolated(src),src,Replica::R3,t)
}
pub open spec fn r3_coverage<S>(m: Program<S>, b: Fork, trial: Trial<S>, d: Stored<S>) -> bool {
    let x=entry(m,b,trial); let src=crate::origin(b.branch);
    background_replication(m,x,observed_writer(b),src,isolated(src),trial.destinations,d)
        && fair_background(m,x,trial.background)
        && (trial.omit_other || trial.destinations.remove(src).subset_of(set![Replica::R3])
            || exists|t:nat| #[trigger] r3_record(d,b,trial.background,t))
}

proof fn sole_destination<S>(m: Program<S>, b: Fork, trial: Trial<S>, r: Replica)
    requires trial.omit_other || trial.destinations.remove(crate::origin(b.branch)).subset_of(set![Replica::R3]),
        r!=crate::origin(b.branch), trial.destinations.contains(r), live(entry(m,b,trial).cfg.net,at(r)),
    ensures r==Replica::R3,
{
    if !trial.omit_other { assert(trial.destinations.remove(crate::origin(b.branch)).contains(r)); }
}

pub proof fn original_r3_storage<S>(m: Program<S>, b: Fork, trial: Trial<S>, d: Stored<S>)
    -> (found: (nat,Seq<Hop>))
    requires r3_coverage(m,b,trial,d),
    ensures ({
        let (t,hops)=found; let e=trial.background; let src=crate::origin(b.branch);
        let q=asm::drive(m,wc::start(m),events(e,t));
        replicated(d,e,observed_writer(b),isolated(src),src,Replica::R3,t) && route(e,src,Replica::R3,t,hops)
            && vis::replica_prefix(m,wc::start(m),events(e,t)) && q==all_available((e.state)(t))
            && d(Replica::R3,(q.cfg.private)(at(Replica::R3)),(q.cfg.net.locals)(Replica::R3),observed_writer(b))
    }),
{
    let x=entry(m,b,trial); let src=crate::origin(b.branch); let e=trial.background;
    if !(exists|t:nat| #[trigger] r3_record(d,b,e,t)) {
        let (r,j,path)=remote_storage_prefix(m,x,observed_writer(b),src,trial.destinations,d,e);
        finite_prefix(m,x,e,j);
        assert(live((e.state)(j).cfg.net,at(r)) && r!=src);
        sole_destination(m,b,trial,r);
        assert(r3_record(d,b,e,j));
    }
    let t=choose|t:nat| #[trigger] r3_record(d,b,e,t);
    let hops=route_from_origin(d,e,observed_writer(b),src,Replica::R3,t);
    finite_prefix(m,x,e,t);
    assert(all_available(x)==wc::start(m));
    lift_prefix(m,x,events(e,t));
    (t,hops)
}

// Additional representation fact for one chosen background run. It
// imposes no deadline or relative order on the offers. The copy may be
// sent by a relay and may be accepted before or after the storage cut.
pub open spec fn offers_recorded_value<S>(d: Stored<S>, b: Fork, e: Run<S>) -> bool {
    let src=crate::origin(b.branch);
    forall|t:nat| #[trigger] replicated(d,e,observed_writer(b),isolated(src),src,Replica::R3,t)
        ==> exists|i:nat,h:nat| #[trigger] offered(e,first_value(b),i,h)
}
pub open spec fn first_install<S>(e: Run<S>, v: int, i: nat) -> bool {
    installs(e,v,i) && forall|j:nat| j<i ==> !#[trigger] installs(e,v,j)
}
proof fn first_install_by<S>(e: Run<S>, v: int, i: nat) -> (j:nat)
    requires installs(e,v,i),
    ensures j<=i, first_install(e,v,j),
    decreases i,
{
    if exists|t:nat| t<i && #[trigger] installs(e,v,t) {
        first_install_by(e,v,choose|t:nat| t<i && #[trigger] installs(e,v,t))
    } else { i }
}
pub proof fn original_value_receipt<S>(m: Program<S>, b: Fork, trial: Trial<S>, d: Stored<S>) -> (j:nat)
    requires r3_coverage(m,b,trial,d), offers_recorded_value(d,b,trial.background),
    ensures ({
        let e=trial.background; let v=first_value(b); let base=wc::start(m);
        first_install(e,v,j) && ((e.state)(j).cfg.net.locals)(Replica::R3)!=v
            && vis::replica_prefix(m,base,events(e,j+1))
            && asm::drive(m,base,events(e,j+1))==all_available((e.state)(j+1))
            && ((e.state)(j+1).cfg.net.locals)(Replica::R3)==v
    }),
{
    let (t,hops)=original_r3_storage(m,b,trial,d);
    let x=entry(m,b,trial); let e=trial.background; let v=first_value(b);
    crate::isolated_rmws();
    fair_offer_iff_readable(m,x,e,v);
    let i=choose|i:nat| #[trigger] installs(e,v,i);
    let j=first_install_by(e,v,i);
    if ((e.state)(j).cfg.net.locals)(Replica::R3)==v { earlier_offer(m,x,e,v,j); }
    let a=(e.turn)(j).unwrap(); assert(replica_step(m,(e.state)(j),a));
    finite_prefix(m,x,e,j+1); lift_prefix(m,x,events(e,j+1));
    j
}

pub open spec fn exposure<S>(b: Fork, e: Run<S>, n: nat) -> svc::Exposure {
    svc::Exposure { arm:b, events:events(e,n) }
}
proof fn receipt_view<S>(p: Program<S>, k: Headers, b: Fork, trial: Trial<S>, i: nat)
    requires fair_background(net::implementation(k,p),entry(net::implementation(k,p),b,trial),trial.background),
        installs(trial.background,first_value(b),i), survivor((trial.background.state)(i).cfg.net)==(2int,5int),
    ensures svc::exposed(p,k,exposure(b,trial.background,i+1)),
        hot::evidence(p,k,exposure(b,trial.background,i+1))==af::view(k,all_available((trial.background.state)(i))),
{
    let m=net::implementation(k,p); let x=entry(m,b,trial); let e=trial.background;
    let a=(e.turn)(i).unwrap(); let h=a->Deliver_0;
    let pre=exposure(b,e,i); let q=all_available((e.state)(i));
    finite_prefix(m,x,e,i); lift_prefix(m,x,events(e,i));
    finite_prefix(m,x,e,i+1); lift_prefix(m,x,events(e,i+1));
    assert(events(e,i+1) =~= events(e,i)+seq![a]);
    vis::join_replica_prefix(m,wc::start(m),events(e,i),seq![a]);
    assert(read::prefix_step(m)(q,a,read::next(m,q,a)));
    net::project_step(p,k,q,a,false);
    hot::available_value_preserves_view(p,k,pre,Some(h));
}

// Attribution applies only when the weak copy represents the indicated
// original update. Its actual receipt must end a causal path from that
// origin. Equal integers alone do not establish this fact.
pub open spec fn receipt_path<S>(b: Fork, e: Run<S>, i: nat) -> bool {
    exists|hops:Seq<Hop>|
        #[trigger] route(e,crate::origin(b.branch),Replica::R3,i+1,hops) && hops.last().delivered==i
}
pub open spec fn sourced_copies<S>(b: Fork, e: Run<S>) -> bool {
    forall|i:nat| #[trigger] installs(e,first_value(b),i) ==> receipt_path(b,e,i)
}
pub open spec fn rival_deferred<S>(b: Fork, trial: Trial<S>) -> bool {
    let e=trial.background; let other=crate::sr1_majorities::other(b);
    (trial.omit_other && sourced_copies(other,e)) || forall|i:nat| #[trigger] first_install(e,first_value(b),i)
        ==> forall|j:nat| j<i ==> !#[trigger] installs(e,first_value(other),j)
}
pub proof fn no_prior_rival<S>(m: Program<S>, b: Fork, trial: Trial<S>, i: nat)
    requires follows(m,entry(m,b,trial),trial.background), rival_deferred(b,trial),
        first_install(trial.background,first_value(b),i),
    ensures forall|j:nat| j<i ==> !#[trigger] installs(trial.background,first_value(crate::sr1_majorities::other(b)),j),
{
    let e=trial.background; let other=crate::sr1_majorities::other(b); let src=crate::origin(other.branch);
    if trial.omit_other && sourced_copies(other,e) {
        assert(!live(entry(m,b,trial).cfg.net,at(src)));
        assert forall|j:nat| j<i implies !#[trigger] installs(e,first_value(other),j) by {
            if installs(e,first_value(other),j) {
                let hops=choose|hops:Seq<Hop>| #[trigger] route(e,src,Replica::R3,j+1,hops) && hops.last().delivered==j;
                route_starts_live(m,entry(m,b,trial),e,src,Replica::R3,j+1,hops);
            }
        }
    }
}

// Only survivor observations immediately before the two selected receipts
// are compared. Liveness supplies the first receipt on each chosen run.
pub open spec fn matching_survivors<S>(k: Headers, a: Run<S>, b: Run<S>) -> bool {
    forall|i:nat,j:nat| #[trigger] first_install(a,5,i) && #[trigger] first_install(b,2,j) ==> {
        let x=all_available((a.state)(i)); let y=all_available((b.state)(j));
        survivor(x.cfg.net)==(2int,5int) && af::view(k,x)==af::view(k,y)
    }
}

pub proof fn original_hot_from_background<S>(
    p: Program<S>, k: Headers, first: spec_fn(S)->int, res: spec_fn(S)->Option<int>, o: hot::WeakOrder,
    notice: Notice, left: Trial<S>, right: Trial<S>, d: Stored<S>, plan: svc::Requests, run: crate::fair_read::Runnable,
) -> (pair:(hot::Execution<S>,hot::Execution<S>))
    requires r3_coverage(net::implementation(k,p),alpha(notice),left,d),
        r3_coverage(net::implementation(k,p),beta(notice),right,d),
        offers_recorded_value(d,alpha(notice),left.background), offers_recorded_value(d,beta(notice),right.background),
        rival_deferred(alpha(notice),left), rival_deferred(beta(notice),right),
        matching_survivors(k,left.background,right.background),
        hot::fresh_caller(p,plan), crate::first_schedule::startup(net::implementation(k,p)),
        svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        crate::operation_history::operation_t(hot::system(p,k,first,res,o),crate::register_history::register()),
        forall|i:nat,j:nat| #[trigger] first_install(left.background,5,i) && #[trigger] first_install(right.background,2,j)
            ==> hot::weak_word(hot::positions(k,o,exposure(alpha(notice),left.background,i+1)))
                && hot::weak_word(hot::positions(k,o,exposure(beta(notice),right.background,j+1))),
    ensures hot::completed(p,k,first,res,pair.0), hot::completed(p,k,first,res,pair.1),
        pair.0.first.sends==pair.1.first.sends, svc::contents(k,pair.0.first.sends)==plan,
        hot::matching_preparations(p,k,pair.0.first.weak,pair.1.first.weak),
        (exists|u:int| #[trigger] hot::sourced_application(p,k,pair.0.first.weak,u)),
        (exists|u:int| #[trigger] hot::sourced_application(p,k,pair.1.first.weak,u)),
        exists|i:nat,j:nat| #[trigger] first_install(left.background,5,i) && #[trigger] first_install(right.background,2,j)
            && pair.0.first.weak==exposure(alpha(notice),left.background,i+1)
            && pair.1.first.weak==exposure(beta(notice),right.background,j+1)
            && (forall|t:nat| t<i ==> !#[trigger] installs(left.background,2,t))
            && (forall|t:nat| t<j ==> !#[trigger] installs(right.background,5,t))
            && (sourced_copies(alpha(notice),left.background) ==> receipt_path(alpha(notice),left.background,i))
            && (sourced_copies(beta(notice),right.background) ==> receipt_path(beta(notice),right.background,j)),
        hot::bad(net::implementation(k,p),first,res,pair.0) || hot::bad(net::implementation(k,p),first,res,pair.1),
{
    let m=net::implementation(k,p); let a=alpha(notice); let b=beta(notice);
    let i=original_value_receipt(m,a,left,d); let j=original_value_receipt(m,b,right,d);
    no_prior_rival(m,a,left,i); no_prior_rival(m,b,right,j);
    receipt_view(p,k,a,left,i); receipt_view(p,k,b,right,j);
    let l=exposure(a,left.background,i+1); let r=exposure(b,right.background,j+1);
    hot::original_hot_from_matched_preparations(p,k,first,res,o,l,r,plan,run)
}

}
