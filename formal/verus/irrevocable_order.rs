use vstd::prelude::*;
use crate::{Op,RecoveredOrder,legal_recovery,next};
use crate::checkpoint::*;
use crate::delivery::{Action,Network,Process};
use crate::protocol::{accepted,LocalProtocol};
use crate::second_copy_schedule as sched;

verus! {

type Net = Network<int,Wire>;
type Event = Action<Wire>;

// An instrument for objective, already assigned weak order positions. X
// can contain every process and weak-ordering input. No process has an
// API for reading it. Fix the same nondeterministic choices on identical
// prefixes, or include those choices in an event refinement.
#[verifier::reject_recursive_types(X)]
pub struct OrderMachine<X> {
    pub after_offers:X,
    pub step:spec_fn(X,Net,Event)->X,
    pub placed:spec_fn(X,Op)->bool,
}
pub open spec fn run<X>(o:OrderMachine<X>,t:Seq<Net>,a:Seq<Event>,k:nat) -> X
    decreases k,
{
    if k==0 {o.after_offers} else {let i=k-1;(o.step)(run(o,t,a,i as nat),t[i],a[i])}
}
pub open spec fn placed_at<X>(o:OrderMachine<X>,t:Seq<Net>,a:Seq<Event>,k:nat,w:Op) -> bool {
    (o.placed)(run(o,t,a,k),w)
}
pub open spec fn ordinary(n:Net,a:Event) -> bool {
    match a {
        Action::Send(_,p)=>invocation_packet(p) || first_reply(p),
        Action::Deliver(id)=> n.pending.contains_key(id) && (invocation_packet(n.pending[id]) || first_reply(n.pending[id])),
        Action::Strong(Process::FirstClient)=>true,_=>false,
    }
}
pub open spec fn new_on_strong<X>(o:OrderMachine<X>,t:Seq<Net>,a:Seq<Event>,k:nat,w:Op) -> bool {
    ordinary(t[k as int],a[k as int]) && !placed_at(o,t,a,k,w) && placed_at(o,t,a,k+1,w)
}
pub open spec fn retracted<X>(o:OrderMachine<X>,t:Seq<Net>,a:Seq<Event>,k:nat,w:Op) -> bool {
    placed_at(o,t,a,k,w) && !placed_at(o,t,a,k+1,w)
}
pub open spec fn single_read(h:RecoveredOrder,v:int) -> bool {
    legal_recovery(h) && h.ops.no_duplicates() && !h.ops.contains(Op::SR2)
        && exists|i:int| 0<=i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 && h.states[i]==v
}
// Only the membership part of G is needed. A selected writer preceding
// the read must have been placed by response, and an irrevocably placed
// writer belongs to the actual total order. No positions are inferred
// from copying data, or from what the client or origin knows.
pub open spec fn respects_positions<X>(o:OrderMachine<X>,x:X,h:RecoveredOrder) -> bool {
    (forall|w:Op| (w==Op::W1 || w==Op::W2) && #[trigger] (o.placed)(x,w) ==> h.ops.contains(w))
        && (forall|j:int,i:int| 0<=j<i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1
            && (#[trigger] h.ops[j]==Op::W1 || h.ops[j]==Op::W2) ==> (o.placed)(x,h.ops[j]))
}
pub(crate) proof fn writer_before(h:RecoveredOrder,k:nat)
    requires legal_recovery(h),k<=h.ops.len(),h.states[k as int]!=1,
    ensures exists|j:int| 0<=j<k && (#[trigger] h.ops[j]==Op::W1 && h.states[k as int]==2
        || h.ops[j]==Op::W2 && h.states[k as int]==5),
    decreases k,
{
    if k>0 {
        let j=k-1; assert(h.states[k as int]==next(h.ops[j],h.states[j]));
        if h.ops[j]==Op::W1 || h.ops[j]==Op::W2 {assert(h.states[j]==1);} else {writer_before(h,j as nat);}
    }
}
proof fn seen<X>(o:OrderMachine<X>,x:X,h:RecoveredOrder,b:Fork)
    requires single_read(h,first_value(b)),respects_positions(o,x,h),
    ensures h.ops.contains(observed_writer(b)),(o.placed)(x,observed_writer(b)),
{
    let i=choose|i:int| 0<=i<h.ops.len() && #[trigger] h.ops[i]==Op::SR1 && h.states[i]==first_value(b);
    writer_before(h,i as nat);
    let j=choose|j:int| 0<=j<i && (#[trigger] h.ops[j]==Op::W1 && h.states[i]==2 || h.ops[j]==Op::W2 && h.states[i]==5);
    assert(h.ops[j]==observed_writer(b));
}
proof fn locate_gain<X>(o:OrderMachine<X>,t:Seq<Net>,a:Seq<Event>,lo:nat,hi:nat,w:Op)
    requires lo<=hi,!placed_at(o,t,a,lo,w),placed_at(o,t,a,hi,w),
        forall|i:nat| lo<=i<hi ==> ordinary(t[i as int],#[trigger] a[i as int]),
    ensures exists|i:nat| lo<=i<hi && #[trigger] new_on_strong(o,t,a,i,w),
    decreases hi-lo,
{
    if hi>lo {
        let j=(hi-1) as nat;
        if placed_at(o,t,a,j,w) {locate_gain(o,t,a,lo,j,w);} else {assert(new_on_strong(o,t,a,j,w));}
    }
}
proof fn locate_loss<X>(o:OrderMachine<X>,t:Seq<Net>,a:Seq<Event>,lo:nat,hi:nat,w:Op)
    requires lo<=hi,placed_at(o,t,a,lo,w),!placed_at(o,t,a,hi,w),
    ensures exists|i:nat| lo<=i<hi && #[trigger] retracted(o,t,a,i,w),
    decreases hi-lo,
{
    if hi>lo {
        let j=(hi-1) as nat;
        if !placed_at(o,t,a,j,w) {locate_loss(o,t,a,lo,j,w);} else {assert(retracted(o,t,a,j,w));}
    }
}

pub open spec fn ordering_fault<X>(o:OrderMachine<X>,b:Fork,eo:nat,q:Seq<Net>,e:Seq<Event>,es:nat) -> bool {
    let d=sched::rival(b);let w=observed_writer(d);
    (exists|i:nat| 2<=i<eo && #[trigger] new_on_strong(o,checkpoint_states(d),actions_to_crash(d),i,w))
        || (exists|i:nat| 2<=i<es && #[trigger] retracted(o,q,e,i,w))
}
// Only the common weak prefix is used to transport a pre-existing
// position. The alternative may have any number of actual later events.
pub proof fn two_completed_prefixes<X>(o:OrderMachine<X>,b:Fork,eo:nat,q:Seq<Net>,e:Seq<Event>,es:nat,
    original:RecoveredOrder,switched:RecoveredOrder)
    requires 13<=eo<=14,2<=es<=e.len(),q.len()==e.len()+1,
        q[0]==checkpoint_states(sched::rival(b))[0],q[1]==checkpoint_states(sched::rival(b))[1],
        e[0]==actions_to_crash(sched::rival(b))[0],e[1]==actions_to_crash(sched::rival(b))[1],
        single_read(original,first_value(sched::rival(b))),
        respects_positions(o,run(o,checkpoint_states(sched::rival(b)),actions_to_crash(sched::rival(b)),eo),original),
        single_read(switched,first_value(b)),respects_positions(o,run(o,q,e,es),switched),
    ensures ordering_fault(o,b,eo,q,e,es),
{
    let d=sched::rival(b);let w=observed_writer(d);let t=checkpoint_states(d);let a=actions_to_crash(d);
    assert(run(o,t,a,2)==run(o,q,e,2)) by {reveal_with_fuel(run,3);}
    seen(o,run(o,t,a,eo),original,d);seen(o,run(o,q,e,es),switched,b);
    if !placed_at(o,t,a,2,w) {
        assert forall|i:nat| 2<=i<eo implies ordinary(t[i as int],#[trigger] a[i as int]) by {prefix_index(i as int);}
        locate_gain(o,t,a,2,eo,w);
    } else if !placed_at(o,q,e,es,w) {locate_loss(o,q,e,2,es,w);}
    else {
        assert(switched.ops.contains(w));crate::recovered_order_cannot_keep_both_rmws(switched);
    }
}

pub open spec fn through_response<S>(b:Fork,p:crate::promotion_wait::Path<sched::C<S>,Event>) -> (Seq<Net>,Seq<Event>) {
    (sched::states(b).take(11)+p.states.map(|_i:int,s:sched::C<S>|s.net),sched::actions(b).take(11)+p.actions)
}
// The required R3 service is limited to an enabled ordinary sample of its
// actual cell. The preparation may contain compulsory or optional work at
// any replica. There is no requirement to send a particular second receipt.
pub proof fn accepting_second_installation<S,X>(m:LocalProtocol<S,int,Wire>,value:spec_fn(S)->int,o:OrderMachine<X>,b:Fork,
    prep:crate::promotion_wait::Path<sched::C<S>,Event>) -> (p:crate::promotion_wait::Path<sched::C<S>,Event>)
    requires accepted(m,checkpoint_observations(b)),accepted(m,checkpoint_observations(sched::rival(b))),
        completed_quorum_sample(m,value,b),completed_quorum_sample(m,value,sched::rival(b)),
        sched::preparation(m,b,prep),(prep.states.last().net.locals)(crate::Replica::R3)==first_value(b),
        crate::ordinary_service::allowed(m,prep.states.last(),sched::sample(prep.states.last())),
    ensures ({
        let d=sched::rival(b);let eo=first_return_len(m,d);let v=value((p.states.last().private)(Process::FirstClient));
        let (q,e)=through_response(b,p);
        crate::fanout_service::reached(m,sched::cfg(m,b,11))
            && crate::promotion_wait::first_return(crate::fanout_service::run_step(m),crate::fanout_service::done(m),sched::cfg(m,b,11),p)
            && v==first_value(b)
            && forall|old:RecoveredOrder,new:RecoveredOrder| single_read(old,first_result(m,value,d))
                && #[trigger] respects_positions(o,run(o,checkpoint_states(d),actions_to_crash(d),eo),old)
                && single_read(new,v) && #[trigger] respects_positions(o,run(o,q,e,e.len()),new)
                ==> ordering_fault(o,b,eo,q,e,e.len())
    }),
{
    let d=sched::rival(b);let eo=first_return_len(m,d);
    sched::cut_reachable(m,b);stable_responder_cells_fix_first_sample(m,value,d);
    let p=sched::completed_from_prepared_sample(m,value,b,prep);let (q,e)=through_response(b,p);
    assert forall|old:RecoveredOrder,new:RecoveredOrder| single_read(old,first_result(m,value,d))
        && #[trigger] respects_positions(o,run(o,checkpoint_states(d),actions_to_crash(d),eo),old)
        && single_read(new,value((p.states.last().private)(Process::FirstClient)))
        && #[trigger] respects_positions(o,run(o,q,e,e.len()),new) implies ordering_fault(o,b,eo,q,e,e.len()) by {
        two_completed_prefixes(o,b,eo,q,e,e.len(),old,new);
    }
    p
}

// Instantiate both completions for the fallback. Making an ordinary
// genesis image available at R3 adds another enabled branch; it cannot
// erase the already admitted, installation-first executions.
pub proof fn fallback_with_actual_positions<X>(o:OrderMachine<X>,b:Fork,old:RecoveredOrder,new:RecoveredOrder)
    requires single_read(old,first_value(sched::rival(b))),single_read(new,first_value(b)),
        respects_positions(o,run(o,checkpoint_states(sched::rival(b)),actions_to_crash(sched::rival(b)),14),old),
        respects_positions(o,run(o,sched::states(b),sched::actions(b),16),new),
    ensures ordering_fault(o,b,14,sched::states(b),sched::actions(b),16),
        crate::fallback_program::cut(b,16).core.calls[1].answer==Some(first_value(b))
        && crate::facade_hybrid::prefix(sched::rival(b),14).calls[1].answer==Some(first_value(sched::rival(b))),
        (forall|k:nat| k<16 ==> #[trigger] crate::fallback_program::genuine_turn(crate::weak_round::paper_ops(),
            crate::genesis_escape::resolver(),b,k)),
{
    crate::facade_transport::actual_first_rpc(sched::rival(b),14);
    assert forall|k:nat| k<16 implies #[trigger] crate::fallback_program::genuine_turn(crate::weak_round::paper_ops(),
        crate::genesis_escape::resolver(),b,k) by {crate::fallback_program::executes_switched_prefix(crate::weak_round::paper_ops(),b,k);}
    two_completed_prefixes(o,b,14,sched::states(b),sched::actions(b),16,old,new);
}

// Separate legal, retrospective witnesses for the two first responses
// alone. An independent genesis observation need not include either RMW.
pub open spec fn only_first(b:Fork) -> RecoveredOrder {
    RecoveredOrder {ops:seq![observed_writer(b),Op::SR1],states:seq![1int,first_value(b),first_value(b)]}
}
pub open spec fn read_genesis() -> RecoveredOrder {
    RecoveredOrder {ops:seq![Op::SR1],states:seq![1int,1int]}
}
pub proof fn separate_histories(b:Fork)
    ensures single_read(only_first(b),first_value(b)),single_read(only_first(sched::rival(b)),first_value(sched::rival(b))),
        single_read(read_genesis(),1),!only_first(b).ops.contains(observed_writer(sched::rival(b))),
        !read_genesis().ops.contains(Op::W1) && !read_genesis().ops.contains(Op::W2),
{assert(read_genesis().ops[0]==Op::SR1 && read_genesis().states[0]==1);}
// A different receiver policy for the *same offered data*. It journals
// each delivered weak operation at R3 but exposes only its first ordered
// RMW in the shared cell. This is a finite receiver fragment.
pub struct WeakSite { pub stored:Set<Op>, pub head:Option<Op>, pub value:int }
pub open spec fn receive(s:WeakSite,p:crate::delivery::Packet<Wire>) -> WeakSite {
    if !crate::metadata_provenance::authentic_copy(p) || p.to!=at(crate::Replica::R3) {s}
    else {
        let w=if p.input==Wire::Copy(2) {Op::W1} else {Op::W2};
        WeakSite {stored:s.stored.insert(w),head:if s.head.is_some() {s.head} else {Some(w)},
            value:if s.head.is_some() {s.value} else {next(w,1)}}
    }
}
pub proof fn actually_receiving_both_need_not_expose_the_second(b:Fork)
    ensures ({
        let d=sched::rival(b);let n=sched::net(b,0);let cut=sched::net(b,11);
        let initial=WeakSite {stored:Set::empty(),head:None,value:1};
        let first=receive(initial,n.pending[sched::copy_id(d)]);let second=receive(first,cut.pending[sched::copy_id(b)]);
        let after=crate::delivery::advance(|x,w|if x==1 {cell(x,w)} else {x},cut,sched::action(b,11));
        let ack=crate::delivery::advance(|x,w|if x==1 {cell(x,w)} else {x},after,sched::action(b,12));
        let r=crate::Replica::R3;let c=Process::FirstClient;let packet=packet_for(d,8);
        let actual=Action::Send(8,packet);let sent=crate::delivery::advance(|x,w|if x==1 {cell(x,w)} else {x},ack,actual);
        crate::delivery::enabled(n,sched::action(b,0)) && sched::action(b,0)==Action::Deliver(sched::copy_id(d))
          && first.head==Some(observed_writer(d)) && first.value==(cut.locals)(r)
          && crate::delivery::enabled(cut,sched::action(b,11)) && !after.pending.contains_key(sched::copy_id(b))
          && second.stored.contains(Op::W1) && second.stored.contains(Op::W2)
          && first.head==second.head && first.value==second.value && second.value==(after.locals)(r)
          && crate::delivery::enabled(after,sched::action(b,12)) && ack.pending.get(9)==Some(sched::receipt(b))
          && crate::delivery::enabled(ack,actual) && packet.from==at(r) && packet.to==c
          && packet.input==Wire::Reply((ack.locals)(r)) && packet.input!=Wire::Reply(first_value(b))
          && crate::delivery::enabled(sent,Action::Deliver(8))
          && ack.pending.get(2)==Some(sched::receipt(d)) && sent.pending.get(sched::reply_id(d))==Some(packet_for(d,sched::reply_id(d)))
    }),
{
    sched::transport(b);
}
}
