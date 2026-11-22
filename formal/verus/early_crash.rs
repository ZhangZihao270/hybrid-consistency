// A liveness probe for the direct SR1 prefixes. Only alpha and beta enter
// the history contradiction. In the probe C1 stays live and C2 starts
// independently. Receipt at C1 stays private. Each issued packet
// remains queued until an actual delivery.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*, protocol::*};
use crate::finite_service::{at_end,requested_prefix};
use crate::independent_read::{self as independent, State};
use crate::ordinary_service::{Configuration,pending};
use crate::read_call::{self as call, Event, Log, Net, Program};
use crate::read_issue::{self, send_first, send_second};
use crate::read_nonblocking as nb;
use crate::service::{self as svc, incompatible_completions};
use crate::service_obstruction::{original_reads,suffix_protocol};

verus! {

pub open spec fn actions() -> Seq<Event> {
    let c=Process::FirstClient;
    seq![send(3,Path::Strong,c,at(Replica::R1),Wire::Request),
         send(4,Path::Strong,c,at(Replica::R2),Wire::Request),
         send(5,Path::Strong,c,at(Replica::R3),Wire::Request),
         Action::Deliver(3),Action::Deliver(4),
         send(6,Path::FirstReadReply,at(Replica::R1),c,Wire::Reply(2)),
         send(7,Path::FirstReadReply,at(Replica::R2),c,Wire::Reply(5)),
         Action::CrashR3, Action::StartSecondClient, send_first(),send_second()]
}

pub open spec fn present(id:nat,k:nat) -> bool {
    id==0 || id==1 || (id==3 && 1<=k<=3) || (id==4 && 2<=k<=4) || (id==5 && k>=3)
        || (id==6 && k>=6) || (id==7 && k>=7) || (id==11 && k>=10) || (id==12 && k>=11)
}
pub open spec fn network(k:nat) -> Net {
    let n=after_local_rmws();
    Net { r3_crashed:k>=8,second_started:k>=9,
        pending:Map::new(set![0nat,1,3,4,5,6,7,11,12].filter(|id:nat|present(id,k)),
            |id:nat| if id==11 { crate::sr2::query_packet(Replica::R1) }
                else if id==12 { crate::sr2::query_packet(Replica::R2) }
                else { packet_for(alpha(Notice::G),id) }), ..n }
}
pub open spec fn events() -> Seq<ProcessStep<int,Wire>> {
    observations(Seq::new(12,|i:int|network(i as nat)),actions())
}
pub open spec fn cut<S>(m:Program<S>,k:nat) -> State<S> {
    let ids=if k>=8 {set![0nat,1,2,5]} else {Set::empty()};
    let first=if k>=6 {ids.insert(6)} else {ids};
    let sent=if k>=10 {set![Replica::R1]} else {Set::empty()};
    let c1=if k==0 {Set::empty()} else if k==1 {set![Replica::R1]} else if k==2 {live_pair()} else {all_replicas()};
    State {calls:independent::Calls{first:all_replicas(),second:live_pair()},owners:Map::empty().insert(2nat,at(Replica::R3)),first_requested:c1,
        cfg:Configuration {net:network(k),private:|p|memory(m,p,events(),k)},
        reserved:if k>=7 {first.insert(7)} else {first},
        requested:if k>=11 {sent.insert(Replica::R2)} else {sent} }
}
// Two in-flight weak offers to R3. Envelope 2 belongs to R3 even in
// executions where R3 dies before using it. No live sender needs that name.
pub open spec fn entry<S>(m:Program<S>) -> State<S> {
    State {calls:independent::Calls{first:all_replicas(),second:live_pair()},owners:Map::empty().insert(2nat,at(Replica::R3)),first_requested:Set::empty(),
        cfg:Configuration{net:after_local_rmws(),private:m.initial},reserved:Set::empty(),requested:Set::empty()}
}
spec fn original_index(k:nat) -> nat {
    seq![2nat,3,4,5,6,8,9,15,16,17][k as int]
}
proof fn index(k:nat)
    requires k<11,
    ensures k==0 || k==1 || k==2 || k==3 || k==4 || k==5 || k==6 || k==7 || k==8 || k==9 || k==10,
{}
// Compare actual local observations, including the replica state sampled
// on a send. C1 agrees only through its initial sends; no later C1 state
// is used. R3's crash can have a different local observation.
proof fn retained_memory<S>(m:Program<S>,b:Fork,p:Process,k:nat)
    requires k<=9,survivor_actor(p) || (p==Process::FirstClient && k<=3),
    ensures memory(m,p,events(),k)==memory(m,p,checkpoint_observations(b),original_index(k)),
    decreases k,
{
    let real_events=checkpoint_observations(b);
    if k==0 {
        assert forall|i:int| 0<=i<2 implies (#[trigger] real_events[i]).actor!=p by { assert(i==0 || i==1); }
        memory_during_quiescence(m,real_events,p,0,2);
    } else {
        let j=(k-1) as nat;let pos=original_index(j);let end=original_index(k);
        retained_memory(m,b,p,j);index(j);
        assert(events()[j as int]==real_events[pos as int] ||
            (events()[j as int].actor!=p && real_events[pos as int].actor!=p));
        assert forall|i:int| pos+1<=i<end implies (#[trigger] real_events[i]).actor!=p by {
            prefix_index(i); index(j);
        }
        memory_during_quiescence(m,real_events,p,pos+1,end);
    }
}
// The probe never executes C1's receive or completion handler. Only
// the initial sends, the two surviving responders and C2 startup are used.
pub open spec fn probe_inputs<S>(m:Program<S>,b:Fork) -> bool {
    let es=checkpoint_observations(b);
    forall|i:int| (2<=i<=6 || i==8 || i==9 || i==16) ==> {
        let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)
    }
}
proof fn one_probe_step<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,k:nat)
    requires probe_inputs(m,b),read_issue::can_issue(m,res),k<11,
    ensures independent::prefix_step(m)(cut(m,k),actions()[k as int],cut(m,k+1)),
{
    let x=cut(m,k);let a=actions()[k as int];let e=events()[k as int];let p=e.actor;
    let y=independent::next(m,x,a);let es=checkpoint_observations(b);
    index(k);
    if k<7 || k==8 {
        let j=original_index(k);assert(e==es[j as int]);
        assert(survivor_actor(p) || (p==Process::FirstClient && k<=3));
        retained_memory(m,b,p,k);
        assert((m.accept)(memory(m,p,es,j),e));
    }
    assert(y.cfg.net.locals =~= network(k+1).locals);
    assert(y.cfg.net.pending =~= network(k+1).pending);
    assert(y.cfg.private =~= cut(m,k+1).cfg.private);
    assert(y.first_requested =~= cut(m,k+1).first_requested);
    assert(y.requested =~= cut(m,k+1).requested);
    if k==7 {assert(independent::retired_at_failure(x) =~= set![0nat,1,2,5]);}
    assert(y.reserved =~= cut(m,k+1).reserved);
    if k>=9 {
        let c=Process::SecondClient;
        assert(events()[8]==read_issue::local_event(Action::StartSecondClient));
        assert(memory(m,c,events(),8)==(m.initial)(c)) by {
            assert forall|i:int| 0<=i<8 implies (#[trigger] events()[i]).actor!=c by {index(i as nat);}
            memory_during_quiescence(m,events(),c,0,8);
        }
        assert(memory(m,c,events(),9)==read_issue::started(m));
        assert((m.accept)((x.cfg.private)(p),e)) by {reveal_with_fuel(memory,2);}
    }
}
proof fn remaining_prefix<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork,k:nat)
    requires probe_inputs(m,b),read_issue::can_issue(m,res),k<=11,
    ensures nb::within(independent::prefix_step(m),independent::at_state(cut(m,11)),cut(m,k),(11-k) as nat),
    decreases 11-k,
{
    if k<11 {
        one_probe_step(m,res,b,k);remaining_prefix(m,res,b,k+1);
        let s=independent::prefix_step(m);let a=actions()[k as int];
        assert(s(cut(m,k),a,cut(m,k+1)));
    }
}
pub proof fn reachable_independent_call<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork)
    requires probe_inputs(m,b),read_issue::can_issue(m,res),
    ensures independent::reached(m,entry(m),cut(m,11)),independent::issued_to_majority(cut(m,11)),
        pending(cut(m,11).cfg,res),!network(11).first_stopped,network(11).r3_crashed,
        network(11).pending.dom()==set![0nat,1,5,6,7,11,12],!network(11).pending.contains_key(2),
        network(11).pending.get(6)==Some(packet_for(b,6)),network(11).pending.get(7)==Some(packet_for(b,7)),
{
    let c=Process::SecondClient;
    remaining_prefix(m,res,b,0);
    assert(network(0).pending =~= after_local_rmws().pending);
    assert(cut(m,0).cfg.private =~= m.initial);
    assert(cut(m,0)==entry(m));
    assert(nb::within(independent::prefix_step(m),independent::at_state(cut(m,11)),entry(m),11));
    assert(independent::reached(m,entry(m),cut(m,11)));
    assert(live(network(11),at(Replica::R1)) && live(network(11),at(Replica::R2)));
    assert(cut(m,11).requested.contains(Replica::R1) && cut(m,11).requested.contains(Replica::R2));
    assert(network(11).pending.dom() =~= set![0nat,1,5,6,7,11,12]);
    assert forall|i:int| 0<=i<8 implies (#[trigger] events()[i]).actor!=c by {index(i as nat);}
    memory_during_quiescence(m,events(),c,0,8);
    assert(memory(m,c,events(),9)==read_issue::started(m));
    reveal_with_fuel(memory,3);
}

// All private survivor histories and live source packets match after both
// actual query sends. The originals still contain the branch-specific
// confirmation, the unconsumed late reply and the weak copy to dead R3.
pub(crate) proof fn initial_cover<S>(m:Program<S>,res:spec_fn(S)->Option<int>,b:Fork)
    requires read_issue::can_issue(m,res),
    ensures ({
        let l=read_issue::issued(b);let dst=resume_at(m,checkpoint_observations(b));
        requested_prefix(dst,res,checkpoint_end(b),delayed_slots(),l.nets,l.actions)
          && independent::covers(cut(m,11),at_end(dst,l.nets,l.actions))
          && delayed_slots().subset_of(cut(m,11).reserved)
    }),
{
    hide(memory); hide(checkpoint_end);hide(requested_prefix);
    read_issue::issue_on_original(b,m,res);
    let l=read_issue::issued(b);let dst=resume_at(m,checkpoint_observations(b));let t=at_end(dst,l.nets,l.actions);
    let c=Process::SecondClient;let net=network(11);
    assert(call::obs(l) =~= seq![read_issue::local_event(send_first()),read_issue::local_event(send_second())]);
    assert(res((dst.initial)(c)).is_none()) by {
        reveal(memory);
        assert(pending_before_end(dst,res,call::obs(l)));
        assert(res(memory(dst,c,call::obs(l),0)).is_none());
    }
    assert(requested_prefix(dst,res,checkpoint_end(b),delayed_slots(),l.nets,l.actions)) by {reveal(requested_prefix);}
    assert forall|p:Process| survivor_actor(p) implies #[trigger] (cut(m,11).cfg.private)(p)==(t.private)(p) by {
        retained_memory(m,b,p,9);
        reveal_with_fuel(memory,3);
    }
    reveal(checkpoint_end);
    assert forall|id:nat| net.pending.contains_key(id) && survivor_actor(net.pending[id].to)
        implies #[trigger] t.net.pending.get(id)==Some(net.pending[id]) by { assert(id==11 || id==12); }
    assert forall|id:nat| #[trigger] t.net.pending.contains_key(id)
        implies net.pending.contains_key(id) || cut(m,11).reserved.contains(id) by {};
    assert forall|id:nat| net.pending.contains_key(id) && net.pending[id].to==Process::FirstClient
        implies #[trigger] cut(m,11).reserved.contains(id) by {};
}

pub proof fn returning_probe_yields_pair<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires original_reads(n,m,first),read_issue::can_issue(m,res),
        nb::possible(independent::service_step(m),independent::returned(res),cut(m,11)),
    ensures exists|a:Seq<Event>,v:int| #[trigger] incompatible_completions(n,m,first,res,a,v)
        && a.len()>=2 && a[0]==send_first() && a[1]==send_second(),
{
    hide(incompatible_completions);hide(svc::response_path);hide(crate::legal);hide(independent::covers);
    let b=alpha(n);let dst=suffix_protocol(m,n);let net=checkpoint_end(b);
    let x=cut(m,11);let l=read_issue::issued(b);let ids=delayed_slots();
    initial_cover(m,res,b);
    let step=independent::service_step(m);let done=independent::returned(res);
    assert(nb::possible(step,done,x));
    let k=choose|k:nat| #[trigger] nb::within(step,done,x,k);
    let path=nb::to_path(step,done,x,k);
    let o=independent::project_response(m,dst,res,path,0,net,ids,l,2);
    let v=res((at_end(dst,o.nets,o.actions).private)(Process::SecondClient)).unwrap();
    assert(!svc::consumed_issue(net,2,o.nets,o.actions));
    svc::path_without_notice_preserves_delays(n,dst,res,o.nets,o.actions,v);
    svc::held_path_is_an_ordinary_opportunity(n,dst,res,o.nets,o.actions,v);
    svc::pair_from_ordinary_path(n,m,first,res,replay(|x,w|cell(x,w),crate::confirmation::after_receipt(n),o.actions),o.actions,v);
    assert(o.actions.take(2)[0]==o.actions[0] && o.actions.take(2)[1]==o.actions[1]);
}

pub proof fn original_pair_from_hybrid_service<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires original_reads(n,m,first),read_issue::can_issue(m,res),independent::hybrid_read_service(m,res,entry(m)),
    ensures exists|a:Seq<Event>,v:int| #[trigger] incompatible_completions(n,m,first,res,a,v)
        && a.len()>=2 && a[0]==send_first() && a[1]==send_second(),
{
    reachable_independent_call(m,res,alpha(n));
    returning_probe_yields_pair(n,m,first,res);
}

// H alone imposes a practical cost on the reachable probe: after C2's
// sends, even delivering both C1 replies, doing weak work between live
// sites or running an ordinary repair cannot produce a response.
pub proof fn safety_strands_independent_call<S>(n:Notice,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>)
    requires original_reads(n,m,first),read_issue::can_issue(m,res),
        crate::read_service_contract::admits_strong_history(alpha(n),m,first,res),
        crate::read_service_contract::admits_strong_history(beta(n),m,first,res),
    ensures ({
        let x=cut(m,11);let step=independent::service_step(m);let done=independent::returned(res);
        independent::reached(m,entry(m),x) && independent::issued_to_majority(x) && !done(x)
            && !nb::possible(step,done,x) && nb::pending_trap(step,done,nb::hopeless(step,done))
    }),
{
    hide(incompatible_completions);
    reachable_independent_call(m,res,alpha(n));
    crate::read_service_contract::safe_branches_exclude_conflict(n,m,first,res);
    let step=independent::service_step(m);let done=independent::returned(res);
    if nb::possible(step,done,cut(m,11)) {returning_probe_yields_pair(n,m,first,res);}
    nb::largest_trap(step,done);
}

// Positive finite-service check on the existing sender-sensitive direct
// reader. C1 actually consumes R1's reply in the probe; that receipt has no
// counterpart after C1 stops in either target.
spec fn direct_action(j:nat) -> Event {
    if j==0 {Action::Deliver(6)} else {crate::sr2::completed_actions(alpha(Notice::G))[j as int+1]}
}
pub open spec fn direct_cut(sel:crate::sr2::Select,j:nat) -> State<crate::sr2::Reader> {
    let b=alpha(Notice::G);let m=crate::sr2::read_protocol(Set::empty(),Notice::G,sel);
    let x=cut(m,11);let after=independent::next(m,x,Action::Deliver(6));
    if j==0 {x} else {
        let phys=crate::sr2::exchange_net(b,j+1);
        let queue=phys.pending.remove(2).remove(6).insert(1,packet_for(b,1))
            .insert(5,packet_for(b,5)).insert(7,packet_for(b,7));
        State {cfg:Configuration{
            net:Net{pending:queue,..after.cfg.net},
            private:|p|if survivor_actor(p) {crate::sr2::exchange_memory(b,sel,p,j+1)} else {(after.cfg.private)(p)}
        },..after}
    }
}
proof fn direct_initial(sel:crate::sr2::Select)
    ensures ({
        let b=alpha(Notice::G);let m=crate::sr2::read_protocol(Set::empty(),Notice::G,sel);let x=cut(m,11);
        independent::service_step(m)(x,Action::Deliver(6),direct_cut(sel,1))
            && (direct_cut(sel,1).cfg.private)(Process::FirstClient).prior.reply==Some(2)
    }),
{
    let b=alpha(Notice::G);let c=Process::FirstClient;let m=crate::sr2::read_protocol(Set::empty(),Notice::G,sel);
    let x=cut(m,11);let y=independent::next(m,x,Action::Deliver(6));let l=read_issue::issued(b);
    let res=|s:crate::sr2::Reader|s.returned;
    crate::sr2::fresh_reader_resumes_actual_sr1_state(b,Set::empty(),sel);
    crate::read_issue::gated_and_ungated_clients_issue(Notice::G,Set::empty(),sel);
    initial_cover(m,res,b);
    assert forall|i:int| 3<=i<11 implies (#[trigger] events()[i]).actor!=c by {index(i as nat);}
    memory_during_quiescence(m,events(),c,3,11);
    assert((x.cfg.private)(c).prior.reply.is_none()) by {reveal_with_fuel(memory,4);}
    let dst=suffix_protocol(m,Notice::G);let t=at_end(dst,l.nets,l.actions);
    let es=observations(crate::sr2::exchange_states(b,true),crate::sr2::completed_actions(b));
    assert forall|i:int| 0<=i<2 implies #[trigger] call::obs(l)[i]==#[trigger] es[i] by {assert(i==0 || i==1);}
    assert(y.cfg.private =~= direct_cut(sel,1).cfg.private) by {
        assert forall|p:Process| #[trigger] (y.cfg.private)(p)==(direct_cut(sel,1).cfg.private)(p) by {
            if survivor_actor(p) {
                assert((x.cfg.private)(p)==(t.private)(p));
                memory_on_common_prefix(dst,p,call::obs(l),es,2);
                crate::sr2::exchange_tracks_private_memory(b,Set::empty(),sel,true,p,2);
            }
        }
    }
    assert(y.cfg.net.pending =~= direct_cut(sel,1).cfg.net.pending);
}
proof fn direct_after(sel:crate::sr2::Select,j:nat)
    requires 1<=j<8,
    ensures ({
        let m=crate::sr2::read_protocol(Set::empty(),Notice::G,sel);
        independent::service_step(m)(direct_cut(sel,j),direct_action(j),direct_cut(sel,j+1))
    }),
{
    let b=alpha(Notice::G);let m=crate::sr2::read_protocol(Set::empty(),Notice::G,sel);
    let x=direct_cut(sel,j);let a=direct_action(j);let y=independent::next(m,x,a);
    let es=observations(crate::sr2::exchange_states(b,true),crate::sr2::completed_actions(b));
    let k=j+1;let e=es[k as int];
    crate::sr2::ordinary_quorum_can_return(b,Set::empty(),sel);
    assert(accepted(crate::sr2::reader(b,Set::empty(),sel),es));
    crate::sr2::exchange_tracks_private_memory(b,Set::empty(),sel,true,e.actor,k);
    assert((m.accept)(crate::sr2::exchange_memory(b,sel,e.actor,k),e));
    index(j);
    assert(process_step(x.cfg.net,a)==e);
    assert(y.cfg.private =~= direct_cut(sel,j+1).cfg.private) by {
        assert forall|p:Process| #[trigger] (y.cfg.private)(p)==(direct_cut(sel,j+1).cfg.private)(p) by {
            if survivor_actor(p) {
                crate::sr2::exchange_tracks_private_memory(b,Set::empty(),sel,true,p,k);
                crate::sr2::exchange_tracks_private_memory(b,Set::empty(),sel,true,p,k+1);
            }
        }
    }
    assert(y.cfg.net.pending =~= direct_cut(sel,j+1).cfg.net.pending);
    assert(y.cfg.net.locals =~= direct_cut(sel,j+1).cfg.net.locals);
}
pub proof fn direct_probe_returns(sel:crate::sr2::Select)
    ensures ({
        let m=crate::sr2::read_protocol(Set::empty(),Notice::G,sel);let res=|s:crate::sr2::Reader|s.returned;
        let b=alpha(Notice::G);let u=direct_cut(sel,8);
        nb::possible(independent::service_step(m),independent::returned(res),cut(m,11))
            && (u.cfg.private)(Process::SecondClient).returned==Some(sel(crate::sr2::report(b,Replica::R1),crate::sr2::report(b,Replica::R2)))
            && (u.cfg.private)(Process::FirstClient).prior.reply==Some(2) && u.cfg.net.pending.get(7)==Some(packet_for(b,7))
            && enabled(u.cfg.net,Action::Deliver(7)) && !crate::ordinary_service::allowed(m,u.cfg,Action::Deliver(7))
    }),
{
    let m=crate::sr2::read_protocol(Set::empty(),Notice::G,sel);let step=independent::service_step(m);
    let done=independent::returned(|s:crate::sr2::Reader|s.returned);
    let b=crate::promotion_wait::Path{states:Seq::new(9,|j:int|direct_cut(sel,j as nat)),actions:Seq::new(8,|j:int|direct_action(j as nat))};
    direct_initial(sel);
    assert forall|i:int| 0<=i<8 implies step(b.states[i],#[trigger] b.actions[i],b.states[i+1]) by {
        if i>0 {direct_after(sel,i as nat);}
    }
    assert(done(b.states.last()));nb::from_path(step,done,b,0);
}

}
