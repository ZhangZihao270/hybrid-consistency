// Exercise the first-read construction on previously checked reader families.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::*};
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::{self as first,ClientPath};
use crate::promotion_wait as wait;
use crate::read_nonblocking as nb;
use crate::sr2::{self,Reader,Select};
use crate::quorum_rpc::{self as rpc,Round,Rpc,Resolver};
use crate::{rpc_majority as stocks,stock_reports as reports,stock_availability as stock};

verus! {

// Any two different senders, either delivery order, any reachable stock
// log and any total member selector on authentic (possibly mixed) stamps.
// The third site can have participated independently. Its reply stays queued.
pub proof fn any_issued_stock_pair(rho:Resolver,s:Round,r:Replica,q:Replica)
    requires stocks::total_sample(rho),rpc::normal(s),s.started,s.returned.is_none(),
        s.book.received.dom().is_empty(),r!=q,(s.stage)(r)==3,(s.stage)(q)==3,
    ensures ({
        let a=Rpc::TakeReply(r);let b=Rpc::TakeReply(q);let x=rpc::advance_round(rho,s,a);let y=rpc::advance_round(rho,x,b);
        let z=rpc::advance_round(rho,y,Rpc::Poll);let t=seq![s,x,y,z];
        let rows=s.book.received.insert(r,s.book.packets[rpc::slot(r)].data).insert(q,s.book.packets[rpc::slot(q)].data);
        stock::first_answer(stocks::rpc_stock(rho),t,seq![a,b,Rpc::Poll],rho(rows).unwrap())
            && rho(rows).is_some() && z.book.received==rows
            && z.book.packets==s.book.packets.remove(rpc::slot(r)).remove(rpc::slot(q))
            && stock::read_a(stocks::rpc_stock(rho),|e|rpc::fair(all_replicas(),e))
    }),
{
    let p=stocks::rpc_stock(rho);stocks::any_majority_stock_read(rho);
    let a=Rpc::TakeReply(r);let b=Rpc::TakeReply(q);let x=rpc::advance_round(rho,s,a);let y=rpc::advance_round(rho,x,b);
    let z=rpc::advance_round(rho,y,Rpc::Poll);let rows=y.book.received;let log=s.book.store.log;
    assert(rpc::slot(r)!=rpc::slot(q));
    assert(reports::from_log(log,rows)) by {
        assert forall|w:Replica| #[trigger] rows.contains_key(w) implies crate::ordered_store::authentic(log,rows[w]) by {
            assert(w==q || w==r);
        }
    }
    assert(crate::ordered_store::majority(rows.dom()));assert(reports::has_log(rows));assert(rho(rows).is_some());
    let t=seq![s,x,y,z];let acts=seq![a,b,Rpc::Poll];
    assert forall|i:int| 0<=i<3 implies (p.next)(t[i],#[trigger] acts[i],t[i+1]) by {assert(i==0 || i==1 || i==2);}
    assert forall|i:int| 0<=i<3 implies (p.response)(#[trigger] t[i]).is_none() by {assert(i==0 || i==1 || i==2);}
}
pub open spec fn fanout_cut(s:Round,rho:Resolver,k:nat) -> Round {
    let x=stocks::during_service(s,rho,s.live,k);
    Round{stage:|r:Replica|if s.live.contains(r) {(x.stage)(r)} else if k>(rpc::slot(r)-13) {1nat} else {0nat},..x}
}
pub open spec fn fanout_event(s:Round,k:nat) -> Rpc {
    if k<3 {Rpc::Dispatch(stocks::site(13+k))} else {stocks::serve_a_quorum(s.live,k)}
}
proof fn stock_fanout_step(rho:Resolver,s:Round,i:nat)
    requires rpc::at_invocation(s),crate::ordered_store::majority(s.live),i<9,
    ensures (stocks::rpc_stock(rho).next)(fanout_cut(s,rho,i),fanout_event(s,i),fanout_cut(s,rho,i+1)),
{
    prefix_index(i as int);let x=fanout_cut(s,rho,i);let a=fanout_event(s,i);let t=fanout_cut(s,rho,i+1);
    let y=rpc::advance_round(rho,x,a);assert(rpc::enabled(x,all_replicas(),a));
    assert(y.stage =~= t.stage);assert(y.book.packets =~= t.book.packets);assert(y.book.received =~= t.book.received);
}
pub proof fn stock_fanout_serves_any_pair(rho:Resolver,s:Round,r:Replica,q:Replica)
    requires stocks::total_sample(rho),stock::reaches(stocks::rpc_stock(rho),s),rpc::at_invocation(s),r!=q,
        s.live.contains(r),s.live.contains(q),
    ensures ({
        let cut=fanout_cut(s,rho,9);let u=rpc::advance_round(rho,cut,Rpc::TakeReply(r));
        let v=rpc::advance_round(rho,u,Rpc::TakeReply(q));let z=rpc::advance_round(rho,v,Rpc::Poll);
        let actions=Seq::new(9,|i:int|fanout_event(s,i as nat))+seq![Rpc::TakeReply(r),Rpc::TakeReply(q),Rpc::Poll];
        let states=Seq::new(10,|i:int|fanout_cut(s,rho,i as nat))+seq![u,v,z];
        states[0]==s && actions[0]==Rpc::Dispatch(Replica::R1) && actions[1]==Rpc::Dispatch(Replica::R2)
            && actions[2]==Rpc::Dispatch(Replica::R3) && z.returned.is_some()
            && stock::first_answer(stocks::rpc_stock(rho),states,actions,z.returned.unwrap())
            && (forall|w:Replica| #[trigger] (cut.stage)(w)==if s.live.contains(w) {3nat} else {1nat})
            && z.book.received.dom()==set![r,q] && z.book.packets==cut.book.packets.remove(rpc::slot(r)).remove(rpc::slot(q))
    }),
{
    hide(stock::read_a);hide(stocks::total_sample);hide(stock::reaches);
    let sys=stocks::rpc_stock(rho);let cut=fanout_cut(s,rho,9);
    let t=Seq::new(10,|i:int|fanout_cut(s,rho,i as nat));let a=Seq::new(9,|i:int|fanout_event(s,i as nat));
    assert(t[0].stage =~= s.stage);assert(t[0].book.packets =~= s.book.packets);assert(t[0].book.received =~= s.book.received);
    assert(crate::ordered_store::majority(s.live));
    assert forall|i:int| 0<=i<9 implies (sys.next)(t[i],#[trigger] a[i],t[i+1]) by {
        stock_fanout_step(rho,s,i as nat);
    }
    rpc::rpc_invariant(all_replicas(),rho);stock::reachable_invariant(sys,|x:Round|rpc::normal(x),s);
    stock::invariant_on_path(sys,|x:Round|rpc::normal(x),t,a,9);
    assert(cut.book.received.dom() =~= Set::<Replica>::empty());any_issued_stock_pair(rho,cut,r,q);
    let u=rpc::advance_round(rho,cut,Rpc::TakeReply(r));let v=rpc::advance_round(rho,u,Rpc::TakeReply(q));let z=rpc::advance_round(rho,v,Rpc::Poll);
    let all=t+seq![u,v,z];let events=a+seq![Rpc::TakeReply(r),Rpc::TakeReply(q),Rpc::Poll];
    assert(z.book.received.dom() =~= set![r,q]);
    assert forall|i:int| 0<=i<12 implies (sys.next)(all[i],#[trigger] events[i],all[i+1]) by {
        if i<9 {assert((sys.next)(t[i],a[i],t[i+1]));} else {prefix_index(i);}
    }
    assert forall|i:int| 0<=i<12 implies (sys.response)(#[trigger] all[i]).is_none() by {if i<9 {assert(all[i]==t[i]);} else {prefix_index(i);}}
}
spec fn got(q:Map<nat,Packet<Wire>>,left:Map<nat,Packet<Wire>>,r:Replica) -> bool {
    exists|i:nat| #[trigger] q.contains_key(i) && !left.contains_key(i) && q[i].from==at(r)
}
spec fn has_pair(rs:Set<Replica>) -> bool {
    exists|r:Replica,s:Replica| r!=s && #[trigger] rs.contains(r) && #[trigger] rs.contains(s)
}
proof fn two_distinct(rs:Set<Replica>)
    requires rs.len()==2,
    ensures has_pair(rs),
{
    if !has_pair(rs) {
        if exists|r:Replica| #[trigger] rs.contains(r) {
            let r=choose|r:Replica| #[trigger] rs.contains(r);assert(rs =~= set![r]);
        } else {assert(rs =~= Set::<Replica>::empty());}
    }
}
spec fn represents(q:Map<nat,Packet<Wire>>,t:mail::Inbox<Reader>) -> bool {
    let s=t.local.prior;
    t.local.returned.is_none() && t.packets.dom().subset_of(q.dom()) && t.packets.submap_of(q)
        && (forall|r:Replica| #[trigger] s.replies_from.contains(r) ==> got(q,t.packets,r))
        && (s.reply.is_some() ==> exists|i:nat| #[trigger] q.contains_key(i) && !t.packets.contains_key(i)
            && q[i].input==Wire::Reply(s.reply.unwrap()))
        && (s.finished ==> has_pair(s.replies_from) && s.reply.is_some())
        && (s.reply.is_none() ==> s.replies_from.is_empty())
}
proof fn received_prefix(gates:Set<Replica>,n:Notice,sel:Select,p:ClientPath<Reader>,j:nat)
    requires p.states.len()==p.actions.len()+1,j<=p.actions.len(),first::authentic(p.states[0].packets),
        represents(p.states[0].packets,p.states[0]),wait::valid_edges(mail::client_step(sr2::read_protocol(gates,n,sel)),p),
    ensures represents(p.states[0].packets,p.states[j as int]),
    decreases j,
{
    if j>0 {
        let i=(j-1) as nat;received_prefix(gates,n,sel,p,i);let t=p.states[i as int];let u=p.states[j as int];
        let a=p.actions[i as int];let q=p.states[0].packets;let s=t.local.prior;let m=sr2::read_protocol(gates,n,sel);
        assert(mail::client_step(m)(t,a,u));
        if let Action::Deliver(id)=a {
            assert(t.packets.contains_key(id));assert(t.packets.dom().contains(id));
            assert(t.packets[id]==q[id] && first_reply(q[id]));
            assert(got(q,u.packets,q[id].from->At_0));
            assert forall|r:Replica| #[trigger] s.replies_from.contains(r) implies got(q,u.packets,r) by {
                let h=choose|h:nat| #[trigger] q.contains_key(h) && !t.packets.contains_key(h) && q[h].from==at(r);
                assert(!u.packets.contains_key(h));
            }
            if has_pair(s.replies_from) {
                let (r,w)=choose|r:Replica,w:Replica| r!=w && #[trigger] s.replies_from.contains(r) && #[trigger] s.replies_from.contains(w);
                assert(u.local.prior.replies_from.contains(r) && u.local.prior.replies_from.contains(w));
            }
        }
        if a==Action::<Wire>::Strong(Process::FirstClient) {two_distinct(s.replies_from);}
    }
}
proof fn reader_local_safety(gates:Set<Replica>,n:Notice,sel:Select,s:Reader)
    requires !s.prior.finished,s.returned.is_none(),s.prior.replies_from.is_empty(),s.prior.reply.is_none(),
    ensures first::quorum_response(sr2::read_protocol(gates,n,sel),|s:Reader|s.prior.reply.unwrap(),s),
{
    let m=sr2::read_protocol(gates,n,sel);let value=|s:Reader|s.prior.reply.unwrap();
    assert forall|q:Map<nat,Packet<Wire>>,p:ClientPath<Reader>| #[trigger] first::authentic(q) && p.states.len()==p.actions.len()+1
        && p.states[0]==(mail::Inbox{local:s,packets:q}) && #[trigger] wait::valid_edges(mail::client_step(m),p)
        && mail::local_done(m)(p.states.last()) implies {
            let left=p.states.last().packets;
            (exists|i:nat,j:nat| #[trigger] q.contains_key(i) && #[trigger] q.contains_key(j)
                && !left.contains_key(i) && !left.contains_key(j) && q[i].from!=q[j].from)
            && exists|i:nat| #[trigger] q.contains_key(i) && !left.contains_key(i) && q[i].input==Wire::Reply(value(p.states.last().local))
        } by {
            received_prefix(gates,n,sel,p,p.actions.len());let end=p.states.last();let rs=end.local.prior.replies_from;
            let (r,w)=choose|r:Replica,w:Replica| r!=w && #[trigger] rs.contains(r) && #[trigger] rs.contains(w);
            let i=choose|h:nat| #[trigger] q.contains_key(h) && !end.packets.contains_key(h) && q[h].from==at(r);
            let j=choose|h:nat| #[trigger] q.contains_key(h) && !end.packets.contains_key(h) && q[h].from==at(w);
            assert(q[i].from!=q[j].from);
        }
}
pub open spec fn reverse_path(b:Fork,sel:Select,ticks:nat) -> ClientPath<Reader> {
    let m=sr2::read_protocol(Set::empty(),b.notice,sel);let x=first::initial_client(m,b);let c=Process::FirstClient;
    let a=Action::<Wire>::Deliver(8);let late=Action::Deliver(first::origin_slot(b));
    let y=mail::advance_client(m,x,a);let z=mail::advance_client(m,y,late);let done=Action::Strong(c);
    wait::Path{actions:Seq::new(ticks+3,|j:int|if j==0 {a} else if j<=ticks {Action::ClientInput(c,Wire::Peer(17))}
            else if j==ticks+1 {late} else {done}),
        states:Seq::new(ticks+4,|j:int|if j==0 {x} else if j<=ticks+1 {y} else if j==ticks+2 {z} else {mail::advance_client(m,z,done)})}
}
// Reverse the two receipts and allow arbitrary local clock inputs between
// them. These are actual client transitions of the existing combined reader.
pub proof fn reversed_quorum_read(b:Fork,sel:Select,ticks:nat)
    ensures ({
        let m=sr2::read_protocol(Set::empty(),b.notice,sel);let x=first::initial_client(m,b);
        let d=mail::local_done(m);let step=mail::client_step(m);
        wait::first_return(step,d,x,reverse_path(b,sel,ticks)) && first::service_at_offers(m,|s:Reader|s.prior.reply.unwrap(),b)
            && dispatch::ready(m,first::reference(m,b,5),crate::origin(b.branch))
            && dispatch::ready(m,first::reference(m,b,5),Replica::R3)
    }),
{
    let gs=Set::<Replica>::empty();let m=sr2::read_protocol(gs,b.notice,sel);let c=Process::FirstClient;
    let first_value_of=|s:Reader|s.prior.reply.unwrap();let x=first::initial_client(m,b);
    crate::sr1_majorities::direct_readers_supply_references(b,gs,sel);
    assert(first::emitted(m,b)) by {
        let es=crate::sr1_majorities::obs(b);
        assert forall|i:int| 0<=i<9 implies {let e=#[trigger] es[i];(m.accept)(memory(m,e.actor,es,i as nat),e)} by {
            assert((m.accept)(memory(m,es[i].actor,es,i as nat),es[i]));}
    }
    assert forall|k:nat| k<=11 implies !(m.done)((#[trigger] first::cfg(m,b,k).private)(c)) by {
        sr2::sr1_preserves_all_private_memory(b,gs,sel,c,k);prefix_memory_tracks_actual_messages(b,c,k);
    }
    sr2::sr1_preserves_all_private_memory(b,gs,sel,c,11);prefix_memory_tracks_actual_messages(b,c,11);
    reader_local_safety(gs,b.notice,sel,x.local);
    let step=mail::client_step(m);let d=mail::local_done(m);
    let a=Action::<Wire>::Deliver(8);let other=Action::<Wire>::Deliver(first::origin_slot(b));
    let y=mail::advance_client(m,x,a);let z=mail::advance_client(m,y,other);
    let f=Action::Strong(c);let end=mail::advance_client(m,z,f);
    assert(step(x,a,y) && step(y,other,z));assert(z.local.prior.replies_from =~= set![Replica::R3,crate::origin(b.branch)]);
    assert(z.local.prior.replies_from.len()==2);assert(step(z,f,end) && d(end));
    assert(nb::within(step,d,end,0));assert(nb::within(step,d,z,1));assert(nb::within(step,d,y,2));
    let clock=Action::ClientInput(c,Wire::Peer(17));assert(step(y,clock,y));
    let p=reverse_path(b,sel,ticks);
    assert forall|j:int| 0<=j<p.actions.len() implies step(p.states[j],#[trigger] p.actions[j],p.states[j+1]) by {};
    assert forall|j:int| 0<=j<p.actions.len() implies !d(#[trigger] p.states[j]) by {};
    nb::from_path(step,d,p,0);
    let r=crate::origin(b.branch);let refx=first::reference(m,b,5);
    assert forall|site:Replica| site==r || site==Replica::R3 implies #[trigger] dispatch::ready(m,refx,site) by {
        crate::sr1_majorities::local_at(m,b,at(site),5);
        sr2::sr1_preserves_all_private_memory(b,gs,sel,at(site),5);prefix_memory_tracks_actual_messages(b,at(site),5);
    }
}
pub proof fn original_pair_for_existing_reader(sel:Select,alpha_ticks:nat,beta_ticks:nat)
    ensures ({
        let n=Notice::G;let m=sr2::read_protocol(Set::empty(),n,sel);
        let value=|s:Reader|s.prior.reply.unwrap();let res=|s:Reader|s.returned;
        exists|sa:crate::read_call::Log,sb:crate::read_call::Log,v:int|
            #[trigger] first::completed_pair(n,m,value,res,
                reverse_path(alpha(n),sel,alpha_ticks),reverse_path(beta(n),sel,beta_ticks),sa,sb,v)
    }),
{
    let n=Notice::G;let m=sr2::read_protocol(Set::empty(),n,sel);
    let a=reverse_path(alpha(n),sel,alpha_ticks);let b=reverse_path(beta(n),sel,beta_ticks);
    reversed_quorum_read(alpha(n),sel,alpha_ticks);reversed_quorum_read(beta(n),sel,beta_ticks);
    first::realize_client_path(m,|s:Reader|s.prior.reply.unwrap(),alpha(n),a);
    first::realize_client_path(m,|s:Reader|s.prior.reply.unwrap(),beta(n),b);
    crate::read_issue::gated_and_ungated_clients_issue(n,Set::empty(),sel);crate::early_crash::direct_probe_returns(sel);
    let res=|s:Reader|s.returned;let x=crate::early_crash::cut(m,11);let step=crate::independent_read::service_step(m);
    let done=crate::independent_read::returned(res);first::assemble_offers(m,alpha(n));crate::early_crash::reachable_independent_call(m,res,alpha(n));
    let w=nb::to_path(step,done,x,choose|k:nat| #[trigger] nb::within(step,done,x,k));
    first::replay_at_both_returns(n,m,|s:Reader|s.prior.reply.unwrap(),res,a,b,w);
}

// Passive C1 delivery counters may differ even on actual ordinary inputs.
// This is a local implementation test, independent of the alpha/beta schedules.
pub open spec fn counted<S>(base:crate::read_call::Program<S>) -> crate::read_call::Program<(S,nat)> {
    LocalProtocol{initial:|p|((base.initial)(p),0nat),done:|s:(S,nat)|(base.done)(s.0),
        accept:|s:(S,nat),e|(base.accept)(s.0,e),update:|s:(S,nat),e:ProcessStep<int,Wire>|
            ((base.update)(s.0,e),if e.incoming.is_some() {s.1+1} else {s.1})}
}
pub proof fn counting_an_ordinary_receipt(gates:Set<Replica>,n:Notice,sel:Select,ids:Set<nat>,
    x:crate::independent_read::State<(Reader,nat)>,id:nat)
    requires !ids.contains(id),x.cfg.net.pending.contains_key(id),
        x.cfg.net.pending[id].to==Process::FirstClient,x.cfg.net.pending[id].input is Peer,!x.cfg.net.first_stopped,
    ensures ({
        let m=counted(sr2::read_protocol(gates,n,sel));let a=Action::<Wire>::Deliver(id);
        let y=crate::independent_read::next(m,x,a);let c=Process::FirstClient;
        mail::active_step(m)(x,a,y) && (y.cfg.private)(c).1==(x.cfg.private)(c).1+1 && !mail::opens_service(m,ids,x,a,y)
    }),
{
    let base=sr2::read_protocol(gates,n,sel);let m=counted(base);let a=Action::<Wire>::Deliver(id);
    let y=crate::independent_read::next(m,x,a);let rel=|s:(Reader,nat),t:(Reader,nat)| s.0==t.0;
    assert(mail::client_simulation(m,rel));mail::bookkeeping_does_not_unlock(m,rel,ids,x,a,y);
}

}
