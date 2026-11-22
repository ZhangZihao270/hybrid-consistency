// Feasibility of the weak prefix of the original HOT executions.
use vstd::prelude::*;
use crate::{Op, Replica, checkpoint::*, delivery::*};
use crate::first_assembly as asm;
use crate::independent_preparations as prep;
use crate::independent_read as read;
use crate::operation_history as op;
use crate::order_extension as order;
use crate::original_application as app;
use crate::read_call::{Event, Program};
use crate::register_history as reg;
use crate::weak_round as weak;

verus! {

pub open spec fn start<S>(m: Program<S>) -> read::State<S> {
    prep::before_offers(m,app::lanes())
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

} // verus!
