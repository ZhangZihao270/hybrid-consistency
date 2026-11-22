// The input and output of the retained strong-path information channel.
// The two physical C1 tapes may differ. The checkpoint interface proves
// that their private consumes of protected replies cannot drive SR2.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*, protocol::*};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::coupled_traffic as traffic;
use crate::first_assembly::Lanes;
use crate::first_splice::{self as tape, Tape};
use crate::guarded_comparison::{self as cmp, end, second, attempt, ready, prepare};
use crate::independent_preparations as prep;
use crate::independent_read::{self as read, State};
use crate::read_call::{Event,Program};
use crate::sr2::query_packet;

verus! {

pub struct Residual<S> {
    pub cells:(int,int),
    pub left:S, pub right:S,
    pub owners:Map<nat,Process>,
    pub reserved:Set<nat>,
    pub packets:spec_fn(nat)->Option<Packet<Wire>>,
}

pub open spec fn visible(q:Option<Packet<Wire>>, locked:bool) -> Option<Packet<Wire>> {
    if locked && q.is_some() && q.unwrap().to==Process::FirstClient { None } else { q }
}

pub open spec fn residual<S>(x:State<S>, queue:Map<nat,Packet<Wire>>, reserved:Set<nat>) -> Residual<S> {
    Residual { cells:survivor(x.cfg.net), left:(x.cfg.private)(at(Replica::R1)), right:(x.cfg.private)(at(Replica::R2)),
        owners:x.owners, reserved:reserved.filter(|i:nat|i>2),
        packets:|i:nat| if i<=2 {None} else {visible(queue.get(i),reserved.contains(i))} }
}
pub open spec fn live_view<S>(x:State<S>) -> Residual<S> { residual(x,x.cfg.net.pending,x.reserved) }

// Concrete data at the prepared cut, BEFORE C1 consumes its replies.
// The two public queries and the crash reservations are fixed by the model.
pub open spec fn retained<S>(z:State<S>) -> Residual<S> {
    residual(z,z.cfg.net.pending.insert(11,query_packet(Replica::R1)).insert(12,query_packet(Replica::R2)),
        z.reserved.union(read::retired_at_failure(z)))
}

pub proof fn private_first_return_cannot_signal<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,b:Fork,t:Tape,c:Tape)
    requires prep::arm(m,first,res,l,b,t,c),
    ensures retained(build::prepared(m,l,b,t))==live_view(prep::cutoff(m,l,b,t,c)),
{
    let z=build::prepared(m,l,b,t);let u=build::first_end(m,l,b,t,c);let x=prep::cutoff(m,l,b,t,c);
    assert(read::retired_at_failure(z) =~= read::retired_at_failure(u)) by {
        assert forall|i:nat| #[trigger] read::retired_at_failure(z).contains(i)==read::retired_at_failure(u).contains(i) by {
            assert(u.cfg.net.pending.get(i)==if calls::takes(c,i){None}else{z.cfg.net.pending.get(i)});
        }
    }
    assert(crate::first_pair::sites().contains(at(Replica::R1)) && crate::first_pair::sites().contains(at(Replica::R2)));
    assert(retained(z).packets =~= live_view(x).packets) by {
        assert forall|i:nat| #[trigger] (retained(z).packets)(i)==(live_view(x).packets)(i) by {
            assert(u.cfg.net.pending.get(i)==if calls::takes(c,i){None}else{z.cfg.net.pending.get(i)});
            if calls::takes(c,i) {assert(z.reserved.contains(i));}
        }
    }
}

pub open spec fn post_equal<S>(x:State<S>,y:State<S>) -> bool {
    live_view(x)==live_view(y) && (x.cfg.private)(Process::SecondClient)==(y.cfg.private)(Process::SecondClient)
}

proof fn side_step<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>,a:Event)
    requires crate::survivors::after_crash(x.cfg.net),crate::survivors::after_crash(y.cfg.net),post_equal(x,y),ready(m,second(quiet,res),x,a),
    ensures ready(m,second(quiet,res),y,a), process_step(x.cfg.net,a)==process_step(y.cfg.net,a),
        post_equal(read::next(m,x,a),read::next(m,y,a)),
{
    let ex=process_step(x.cfg.net,a);let ey=process_step(y.cfg.net,a);
    let u=read::next(m,x,a);let v=read::next(m,y,a);
    if tape::slot(a).is_some() {
        let i=tape::slot(a).unwrap();assert(i>2);
        assert((live_view(x).packets)(i)==(live_view(y).packets)(i));
        assert(live_view(x).reserved.contains(i)==live_view(y).reserved.contains(i));
        if a is Deliver {assert(live(x.cfg.net,x.cfg.net.pending[i].to));}
        assert(x.cfg.net.pending.get(i)==y.cfg.net.pending.get(i));
    }
    assert(survivor_actor(ex.actor) && ex==ey);
    assert((x.cfg.private)(ex.actor)==(y.cfg.private)(ey.actor));
    assert(ready(m,second(quiet,res),y,a));
    assert((u.cfg.net.locals)(Replica::R1)==(v.cfg.net.locals)(Replica::R1));
    assert((u.cfg.net.locals)(Replica::R2)==(v.cfg.net.locals)(Replica::R2));
    assert(live_view(u).reserved =~= live_view(v).reserved) by {
        assert forall|i:nat| #[trigger] live_view(u).reserved.contains(i)==live_view(v).reserved.contains(i) by {
            assert(live_view(x).reserved.contains(i)==live_view(y).reserved.contains(i));
        }
    }
    assert(live_view(u).packets =~= live_view(v).packets) by {
        assert forall|id:nat| #[trigger] (live_view(u).packets)(id)==(live_view(v).packets)(id) by {
            assert((live_view(x).packets)(id)==(live_view(y).packets)(id));
            assert(live_view(x).reserved.contains(id)==live_view(y).reserved.contains(id));
        }
    }
}

pub proof fn same_residual_replays_sr2<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>,script:Seq<Event>)
    requires crate::survivors::after_crash(x.cfg.net),crate::survivors::after_crash(y.cfg.net),post_equal(x,y),
    ensures cmp::fired(m,second(quiet,res),x,script)==cmp::fired(m,second(quiet,res),y,script),
        post_equal(end(m,second(quiet,res),x,script),end(m,second(quiet,res),y,script)),
    decreases script.len(),
{
    if script.len()>0 {
        let a=script[0];let g=second(quiet,res);let u=attempt(m,g,x,a);let v=attempt(m,g,y,a);
        if ready(m,g,x,a) {side_step(quiet,m,res,x,y,a);} else if ready(m,g,y,a) {side_step(quiet,m,res,y,x,a);}
        cmp::scan_step(m,g,x,script);cmp::scan_step(m,g,y,script);same_residual_replays_sr2(quiet,m,res,u,v,script.drop_first());
    }
}

// Project away the three postponed weak envelopes for ordinary preparation.
// This is an observation function. The original full queues are used to
// establish admission of BOTH traces.
pub open spec fn omit_seeds<S>(x:State<S>) -> State<S> {
    let n=x.cfg.net;State{cfg:crate::ordinary_service::Configuration{
        net:Network{pending:n.pending.remove(0).remove(1).remove(2),..n},..x.cfg},..x}
}

proof fn seed_step<S>(m:Program<S>,x:State<S>,a:Event)
    ensures ready(m,prepare(),x,a)==ready(m,prepare(),omit_seeds(x),a),
        omit_seeds(attempt(m,prepare(),x,a))==attempt(m,prepare(),omit_seeds(x),a),
{
    if tape::slot(a).is_none() || tape::slot(a).unwrap()>2 {
        assert(process_step(x.cfg.net,a)==process_step(omit_seeds(x).cfg.net,a));
    }
    if ready(m,prepare(),x,a) {
        let u=omit_seeds(read::next(m,x,a));let v=read::next(m,omit_seeds(x),a);
        assert(u.cfg.net.pending =~= v.cfg.net.pending);assert(u.cfg.net.locals =~= v.cfg.net.locals);
        assert(u.cfg.private =~= v.cfg.private);
    }
}

// The fork input includes the copy's sender, slot and body, and R3's actual
// confirmation send. An arbitrary handler can depend on any of these.
pub open spec fn installed<S>(m:Program<S>,b:Fork) -> (int,S) {
    let es=checkpoint_observations(b);let r=at(Replica::R3);
    (first_value(b),(m.update)((m.update)((m.initial)(r),es[0]),es[1]))
}

pub open spec fn ordinary_root<S>(m:Program<S>,l:Lanes,n:Notice,input:(int,S)) -> State<S> {
    let base=omit_seeds(build::root(m,l,alpha(n)));let cfg=base.cfg;
    State{cfg:crate::ordinary_service::Configuration{
        net:Network{locals:|r:Replica|if r==Replica::R3 {input.0} else {(cfg.net.locals)(r)},..cfg.net},
        private:|p:Process|if p==at(Replica::R3) {input.1} else {(cfg.private)(p)},
    },..base}
}

proof fn root_from_installation<S>(m:Program<S>,l:Lanes,b:Fork)
    ensures omit_seeds(build::root(m,l,b))==ordinary_root(m,l,b.notice,installed(m,b)),
{
    let x=build::root(m,l,b);let y=ordinary_root(m,l,b.notice,installed(m,b));
    let f=|p:Packet<Wire>|p.input;traffic::pair_at_fanout(m,l,b.notice,f);
    if b.branch==crate::Branch::Alpha {assert(b==alpha(b.notice));} else {assert(b==beta(b.notice));}
    assert(omit_seeds(x).cfg.net.pending =~= y.cfg.net.pending);
    assert(omit_seeds(x).cfg.net.locals =~= y.cfg.net.locals);
    assert((x.cfg.private)(at(Replica::R3))==installed(m,b).1) by { reveal_with_fuel(memory,6); }
    assert(omit_seeds(x).cfg.private =~= y.cfg.private);
}

proof fn projected_preparation<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
    ensures omit_seeds(end(m,prepare(),x,s))==end(m,prepare(),omit_seeds(x),s),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0];seed_step(m,x,a);cmp::scan_step(m,prepare(),x,s);cmp::scan_step(m,prepare(),omit_seeds(x),s);
        projected_preparation(m,attempt(m,prepare(),x,a),s.drop_first());
    }
}

proof fn retained_ignores_seeds<S>(x:State<S>)
    ensures retained(x)==retained(omit_seeds(x)),
{
    let y=omit_seeds(x);
    assert forall|i:nat| i>2 implies #[trigger] read::retired_at_failure(x).contains(i)==read::retired_at_failure(y).contains(i) by {};
    assert(retained(x).reserved =~= retained(y).reserved);assert(retained(x).packets =~= retained(y).packets);
}

pub open spec fn channel<S>(m:Program<S>,l:Lanes,n:Notice,s:Seq<Event>,input:(int,S)) -> Residual<S> {
    retained(end(m,prepare(),ordinary_root(m,l,n,input),s))
}

// This projection holds at any native preparation prefix, including one
// where the two quorum mailboxes still need different continuations.
pub proof fn channel_at_prefix<S>(m:Program<S>,l:Lanes,b:Fork,s:Seq<Event>)
    ensures channel(m,l,b.notice,s,installed(m,b))==retained(end(m,prepare(),build::root(m,l,b),s)),
{
    let x=build::root(m,l,b);root_from_installation(m,l,b);projected_preparation(m,x,s);
    retained_ignores_seeds(end(m,prepare(),x,s));
}

// Factorization at the real SR1/SR2 boundary. For one common proposal list
// the only varying argument is R3's installed observation, regardless of
// which native sends or receives the guards forced on each execution.
pub proof fn source_to_retained_cut<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,b:Fork,t:Tape,c:Tape,s:Seq<Event>)
    requires prep::arm(m,first,res,l,b,t,c),cmp::fired(m,prepare(),build::root(m,l,b),s)==t,
    ensures channel(m,l,b.notice,s,installed(m,b))==live_view(prep::cutoff(m,l,b,t,c)),
{
    private_first_return_cannot_signal(m,first,res,l,b,t,c);channel_at_prefix(m,l,b,s);
}

// Find the final transition from an equal observation to a difference that
// persists to the end. Intermediate divergences that disappear do not count.
proof fn last_boundary(test:spec_fn(int)->bool, k:nat) -> (j:int)
    requires test(0), !test(k as int),
    ensures 0<=j<k, test(j), forall|i:int| j<i<=k ==> !#[trigger] test(i),
    decreases k,
{
    if test(k as int-1) {k as int-1} else {last_boundary(test,(k-1) as nat)}
}

pub open spec fn prefix_cut<S>(m:Program<S>,g:cmp::Gate<S>,x:State<S>,s:Seq<Event>,j:int) -> State<S> {
    end(m,g,x,s.take(j))
}

proof fn next_cut<S>(m:Program<S>,g:cmp::Gate<S>,x:State<S>,s:Seq<Event>,j:int)
    requires 0<=j<s.len(),
    ensures prefix_cut(m,g,x,s,j+1)==attempt(m,g,prefix_cut(m,g,x,s,j),s[j]),
{
    let t=seq![s[j]];assert(s.take(j+1) =~= s.take(j)+t);cmp::append_script(m,g,x,s.take(j),t);
    cmp::scan_step(m,g,prefix_cut(m,g,x,s,j),t);assert(t.drop_first() =~= Seq::empty());
}

pub open spec fn caller2<S>(x:State<S>) -> S {(x.cfg.private)(Process::SecondClient)}

pub open spec fn receipt<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,a:Event) -> Option<Packet<Wire>> {
    let e=process_step(x.cfg.net,a);
    if ready(m,second(quiet,res),x,a) && e.actor==Process::SecondClient { e.incoming } else { None }
}

// The same local proposal at two equal, live C2 memories cannot split
// them. A packet actually consumed on at least one side is necessary.
proof fn receipt_splits<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>,a:Event)
    requires crate::survivors::after_crash(x.cfg.net),crate::survivors::after_crash(y.cfg.net),
        caller2(x)==caller2(y), caller2(attempt(m,second(quiet,res),x,a))!=caller2(attempt(m,second(quiet,res),y,a)),
    ensures a is Deliver, a->Deliver_0>2, receipt(quiet,m,res,x,a)!=receipt(quiet,m,res,y,a),
        receipt(quiet,m,res,x,a).is_some() ==> receipt(quiet,m,res,x,a)==x.cfg.net.pending.get(a->Deliver_0)
            && receipt(quiet,m,res,x,a).unwrap().to==Process::SecondClient,
        receipt(quiet,m,res,y,a).is_some() ==> receipt(quiet,m,res,y,a)==y.cfg.net.pending.get(a->Deliver_0)
            && receipt(quiet,m,res,y,a).unwrap().to==Process::SecondClient,
{
    let g=second(quiet,res);let ex=process_step(x.cfg.net,a);let ey=process_step(y.cfg.net,a);
    if !ready(m,g,x,a) || ex.actor!=Process::SecondClient {assert(caller2(attempt(m,g,x,a))==caller2(x));}
    if !ready(m,g,y,a) || ey.actor!=Process::SecondClient {assert(caller2(attempt(m,g,y,a))==caller2(y));}
    if !(a is Deliver) {
        assert((a is Strong || a is ClientInput) && ex.actor==Process::SecondClient && ex==ey);
        assert(ready(m,g,x,a)==ready(m,g,y,a));
    }
}

pub open spec fn used_receipt<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,y:State<S>,s:Seq<Event>,j:int) -> bool {
    let g=second(quiet,res);let u=prefix_cut(m,g,x,s,j);let v=prefix_cut(m,g,y,s,j);let a=s[j];
    0<=j<s.len() && caller2(u)==caller2(v) && a is Deliver && a->Deliver_0>2
        && receipt(quiet,m,res,u,a)!=receipt(quiet,m,res,v,a)
        && (receipt(quiet,m,res,u,a).is_some() ==> receipt(quiet,m,res,u,a)==u.cfg.net.pending.get(a->Deliver_0)
            && receipt(quiet,m,res,u,a).unwrap().to==Process::SecondClient)
        && (receipt(quiet,m,res,v,a).is_some() ==> receipt(quiet,m,res,v,a)==v.cfg.net.pending.get(a->Deliver_0)
            && receipt(quiet,m,res,v,a).unwrap().to==Process::SecondClient)
        && forall|k:int| j<k<=s.len() ==> #[trigger] caller2(prefix_cut(m,g,x,s,k))!=caller2(prefix_cut(m,g,y,s,k))
}

pub proof fn distinguishing_delivery<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,n:Notice,x:State<S>,y:State<S>,s:Seq<Event>) -> (j:int)
    requires cmp::issued(x,alpha(n)),cmp::issued(y,beta(n)),caller2(x)==caller2(y),
        caller2(end(m,second(quiet,res),x,s))!=caller2(end(m,second(quiet,res),y,s)),
    ensures used_receipt(quiet,m,res,x,y,s,j),
{
    let g=second(quiet,res);let test=|k:int|caller2(prefix_cut(m,g,x,s,k))==caller2(prefix_cut(m,g,y,s,k));
    assert(s.take(0) =~= Seq::empty() && s.take(s.len() as int) =~= s);
    let j=last_boundary(test,s.len());let u=prefix_cut(m,g,x,s,j);let v=prefix_cut(m,g,y,s,j);
    cmp::issue_remains(quiet,m,res,alpha(n),x,s.take(j));cmp::issue_remains(quiet,m,res,beta(n),y,s.take(j));
    next_cut(m,g,x,s,j);next_cut(m,g,y,s,j);assert(!test(j+1));receipt_splits(quiet,m,res,u,v,s[j]);
    assert forall|k:int| j<k<=s.len() implies #[trigger] caller2(prefix_cut(m,g,x,s,k))!=caller2(prefix_cut(m,g,y,s,k))
        by {assert(!test(k));}
    j
}

pub open spec fn identity() -> traffic::Encoding {|q:Packet<Wire>|q.input}

pub(crate) proof fn paired_retention<S>(x:State<S>,y:State<S>,n:Notice)
    requires traffic::paired(x,y,n,identity()),
    ensures retained(x)==retained(y),
{
    assert forall|i:nat| i>2 implies #[trigger] y.cfg.net.pending.get(i)==x.cfg.net.pending.get(i) by {
        assert(y.cfg.net.pending.get(i)==traffic::packet(identity(),x.cfg.net.pending.get(i)));
    }
    assert forall|i:nat| i>2 implies #[trigger] read::retired_at_failure(x).contains(i)==read::retired_at_failure(y).contains(i)
        by {assert(y.cfg.net.pending.get(i)==x.cfg.net.pending.get(i));}
    assert(retained(x).reserved =~= retained(y).reserved);
    assert(retained(x).packets =~= retained(y).packets) by {
        assert forall|i:nat| #[trigger] (retained(x).packets)(i)==(retained(y).packets)(i) by {
            if i>2 {assert(y.cfg.net.pending.get(i)==x.cfg.net.pending.get(i));
                assert(read::retired_at_failure(x).contains(i)==read::retired_at_failure(y).contains(i));}
        }
    }
}

// While only R3 can see the fork, a common proposal can make that fork
// externally visible only through an actual R3 send or dequeue. The other
// transport is physically enabled and its local handler refuses the action.
pub open spec fn exported<S>(m:Program<S>,x:State<S>,y:State<S>,a:Event) -> bool {
    let e=process_step(x.cfg.net,a);let h=process_step(y.cfg.net,a);
    e.actor==at(Replica::R3) && h.actor==e.actor && e.incoming==h.incoming && (a is Send || a is Deliver)
        && enabled(x.cfg.net,a) && enabled(y.cfg.net,a)
        && (ready(m,prepare(),x,a)!=ready(m,prepare(),y,a))
        && ready(m,prepare(),x,a)==(m.accept)((x.cfg.private)(e.actor),e)
        && ready(m,prepare(),y,a)==(m.accept)((y.cfg.private)(h.actor),h)
}

proof fn export_step<S>(m:Program<S>,n:Notice,x:State<S>,y:State<S>,a:Event)
    requires traffic::paired(x,y,n,identity()), !traffic::paired(attempt(m,prepare(),x,a),attempt(m,prepare(),y,a),n,identity()),
    ensures exported(m,x,y,a),
{
    let g=prepare();let ex=process_step(x.cfg.net,a);let ey=process_step(y.cfg.net,a);
    let u=attempt(m,g,x,a);let v=attempt(m,g,y,a);
    assert(ready(m,g,x,a) || ready(m,g,y,a));
    if tape::slot(a).is_some() {
        let id=tape::slot(a).unwrap();assert(id>2);assert(y.cfg.net.pending.get(id)==traffic::packet(identity(),x.cfg.net.pending.get(id)));
    }
    assert(ex.actor==ey.actor && ex.incoming==ey.incoming && g(x,a) && g(y,a));
    assert(enabled(x.cfg.net,a) && enabled(y.cfg.net,a));
    assert(ready(m,g,x,a)==(m.accept)((x.cfg.private)(ex.actor),ex));
    assert(ready(m,g,y,a)==(m.accept)((y.cfg.private)(ey.actor),ey));
    if ex.actor!=at(Replica::R3) {assert(ex==ey);assert((x.cfg.private)(ex.actor)==(y.cfg.private)(ex.actor));}
    if !exported(m,x,y,a) {
        assert forall|r:Replica| #[trigger] (u.cfg.net.locals)(r)==(x.cfg.net.locals)(r)
            && (v.cfg.net.locals)(r)==(y.cfg.net.locals)(r) by {
            if let Some(w)=local_input(x.cfg.net,a,r) {assert(!(w is Copy));}
            if let Some(w)=local_input(y.cfg.net,a,r) {assert(!(w is Copy));}
        }
        assert(u.cfg.net.locals =~= x.cfg.net.locals && v.cfg.net.locals =~= y.cfg.net.locals);
        assert forall|p:Process| p!=at(Replica::R3) implies #[trigger] (u.cfg.private)(p)==(v.cfg.private)(p)
            by {assert((x.cfg.private)(p)==(y.cfg.private)(p));}
        assert forall|i:nat| i>2 implies #[trigger] v.cfg.net.pending.get(i)==traffic::packet(identity(),u.cfg.net.pending.get(i))
            by {assert(y.cfg.net.pending.get(i)==traffic::packet(identity(),x.cfg.net.pending.get(i)));}
        assert forall|i:nat| i<=2 implies #[trigger] u.cfg.net.pending.get(i)==x.cfg.net.pending.get(i)
            && v.cfg.net.pending.get(i)==y.cfg.net.pending.get(i) by {assert(tape::slot(a)!=Some(i));}
        assert(traffic::weak_queue(u,alpha(n)) && traffic::weak_queue(v,beta(n)));
        assert(traffic::paired(u,v,n,identity()));
    }
}

pub proof fn retained_difference_leaves_r3<S>(m:Program<S>,l:Lanes,n:Notice,s:Seq<Event>) -> (j:int)
    requires retained(end(m,prepare(),build::root(m,l,alpha(n)),s))!=retained(end(m,prepare(),build::root(m,l,beta(n)),s)),
    ensures 0<=j<s.len(), ({
        let u=prefix_cut(m,prepare(),build::root(m,l,alpha(n)),s,j);let v=prefix_cut(m,prepare(),build::root(m,l,beta(n)),s,j);
        traffic::paired(u,v,n,identity()) && exported(m,u,v,s[j])
    }),
{
    let g=prepare();let x=build::root(m,l,alpha(n));let y=build::root(m,l,beta(n));
    let test=|k:int|traffic::paired(prefix_cut(m,g,x,s,k),prefix_cut(m,g,y,s,k),n,identity());
    assert(s.take(0) =~= Seq::empty() && s.take(s.len() as int) =~= s);
    traffic::pair_at_fanout(m,l,n,identity());
    if test(s.len() as int) {paired_retention(end(m,g,x,s),end(m,g,y,s),n);}
    let j=last_boundary(test,s.len());next_cut(m,g,x,s,j);next_cut(m,g,y,s,j);
    assert(!test(j+1));export_step(m,n,prefix_cut(m,g,x,s,j),prefix_cut(m,g,y,s,j),s[j]);j
}

}
