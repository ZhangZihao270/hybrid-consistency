// A finite first-read arbitration fragment for the reached-cut implication.
// R3 accepts the first ordinary participation packet, independently of
// its cell. Every first reply carries the sender's actual local value.
use vstd::prelude::*;
use crate::{Replica,checkpoint::*,delivery::*,protocol::LocalProtocol};
use crate::coupled_construction as build;
use crate::first_assembly::{self as asm,Lanes};
use crate::first_dispatch as dispatch;
use crate::first_mailbox as mail;
use crate::first_schedule::reference;
use crate::first_splice::{self as tape,Observation,Tape};
use crate::guarded_comparison::{self as cmp,prepare,end};
use crate::independent_read::{self as read,State};
use crate::mailbox_preparation as mb;
use crate::quorum_schedules as qs;
use crate::read_call::{Program,Event};
use crate::fair_read as fair;

verus! {

pub struct Local {
    pub requested:bool, pub replied:bool, pub peer:Option<Replica>,
    pub heard:Set<Replica>, pub tickets:Set<Replica>, pub result:Option<int>,
    pub queried:bool, pub participant_value:Option<int>,
}
pub open spec fn empty() -> Local {
    Local{requested:false,replied:false,peer:None,heard:Set::empty(),tickets:Set::empty(),result:None,
        queried:false,participant_value:None}
}
pub open spec fn vote(r:Replica) -> Packet<Wire> {Packet{from:at(r),to:at(Replica::R3),path:Path::Strong,input:Wire::Peer(0)}}
pub open spec fn is_vote(q:Packet<Wire>) -> bool {q==vote(Replica::R1) || q==vote(Replica::R2)}
pub open spec fn vote_id(r:Replica) -> nat {if r==Replica::R1 {9} else {10}}
pub open spec fn ticket(r:Replica) -> nat {if r==Replica::R1 {14} else {15}}
pub open spec fn reply(r:Replica,v:int) -> Packet<Wire> {Packet{from:at(r),to:Process::FirstClient,path:Path::FirstReadReply,input:Wire::Reply(v)}}
pub open spec fn report_id(r:Replica) -> nat {if r==Replica::R1 {6} else {7}}
pub open spec fn sampled(r:Replica) -> int {if r==Replica::R1 {2} else {5}}
pub open spec fn report2(r:Replica,v:int,participated:bool) -> Packet<Wire> {
    Packet{path:Path::Strong,from:at(r),to:Process::SecondClient,input:Wire::Answer2(Report{value:v,answered_first:participated})}
}
pub open spec fn permitted(s:Local,e:Observation) -> bool {
    match e.action {
        Action::Send(id,q) => invocation_packet(q) ||
            (id==2 && notice_to(q,q.to) && e.own_local==Some(sampled(q.to->At_0))) ||
            (q.path==Path::Weak && q.from is At && q.from!=at(Replica::R3) && q.to==at(Replica::R3)
                && id==(if q.from==at(Replica::R1) {0nat} else {1nat}) && q.input==Wire::Copy(e.own_local.unwrap())) ||
            (is_vote(q) && id==vote_id(q.from->At_0) && s.replied) ||
            (first_reply(q) && s.requested && !s.replied && e.own_local==Some(q.input->Reply_0)
                && if q.from==at(Replica::R3) {s.peer.is_some() && id==ticket(s.peer.unwrap())} else {id==report_id(q.from->At_0)}) ||
            (q.from is At && q.from!=at(Replica::R3) && s.queried && id==report_id(q.from->At_0)+14
                && q==report2(q.from->At_0,e.own_local.unwrap(),s.replied)),
        Action::StopFirstClient=>s.result.is_some(),
        _=>true,
    }
}
pub open spec fn update(s:Local,e:Observation) -> Local {
    if e.incoming.is_some() {
        let q=e.incoming.unwrap();let r=q.from->At_0;
        if is_vote(q) && s.peer.is_none() {Local{peer:Some(r),..s}}
        else if invocation_packet(q) && q.input==Wire::Request {Local{requested:true,..s}}
        else if invocation_packet(q) && q.input==Wire::Query2 {Local{queried:true,..s}}
        else if first_reply(q) {
            let h=s.heard.insert(r);let id=e.action->Deliver_0;
            let t=if r==Replica::R3 {s.tickets.insert(if id==ticket(Replica::R1) {Replica::R1} else {Replica::R2})} else {s.tickets};
            let done=(h.contains(Replica::R1) && h.contains(Replica::R2)) || !t.intersect(h).is_empty();
            Local{heard:h,tickets:t,result:if s.result.is_none() && done {Some(q.input->Reply_0)} else {s.result},..s}
        } else if q.to==Process::SecondClient && q.input is Answer2 {
            let row=q.input->Answer2_0;let h=s.heard.insert(r);let v=if row.answered_first {Some(row.value)} else {s.participant_value};
            Local{heard:h,participant_value:v,result:if s.result.is_none() && h.contains(Replica::R1) && h.contains(Replica::R2)
                {Some(v.unwrap_or(row.value))} else {s.result},..s}
        } else {s}
    } else if e.action is Send && first_reply(e.action->Send_1) {Local{replied:true,..s}} else {s}
}
pub open spec fn machine() -> Program<Local> {
    LocalProtocol{initial:|_p|empty(),accept:|s,e|permitted(s,e),update:|s,e|update(s,e),done:|s:Local|s.result.is_some()}
}
pub open spec fn first() -> spec_fn(Local)->int {|s:Local|s.result.unwrap()}
pub open spec fn res() -> spec_fn(Local)->Option<int> {|s:Local|s.result}
pub open spec fn lanes() -> Lanes {Map::empty().insert(2,Replica::R3).insert(3,Replica::R1).insert(4,Replica::R2)}
pub open spec fn prefix(r:Replica) -> Seq<Event> {
    seq![Action::<Wire>::Deliver(dispatch::request_id(r)),Action::Send(report_id(r),reply(r,sampled(r))),
         Action::Send(vote_id(r),vote(r)),Action::Deliver(5),Action::Deliver(vote_id(r))]
}
pub open spec fn native(b:Fork,r:Replica) -> Seq<Event> {prefix(r)+seq![Action::Send(ticket(r),reply(Replica::R3,first_value(b)))]}
// The two candidate sends use the same name. Exactly the native reply
// for the current R3 cell can fire. The other offer is a scheduler stutter.
pub open spec fn agenda(r:Replica) -> Seq<Event> {
    prefix(r)+seq![Action::Send(ticket(r),reply(Replica::R3,5)),Action::Send(ticket(r),reply(Replica::R3,2))]
}
pub open spec fn ready_root(x:State<Local>,b:Fork,r:Replica) -> bool {
    let c=Process::FirstClient;let n=x.cfg.net;
    r!=Replica::R3 && live(n,at(r)) && live(n,at(Replica::R3)) && live(n,c)
        && (x.cfg.private)(at(r))==empty() && (x.cfg.private)(at(Replica::R3))==empty() && (x.cfg.private)(c)==empty()
        && n.pending==state_after(b,5).pending && n.locals==state_after(b,5).locals
        && x.reserved.is_empty() && (forall|id:nat| id>5 ==> !#[trigger] x.owners.contains_key(id))
}
proof fn roots(b:Fork,r:Replica)
    requires r!=Replica::R3,
    ensures mb::setup(machine(),res(),lanes(),b),ready_root(build::root(machine(),lanes(),b),b,r),
        ready_root(reference(machine(),b,5),b,crate::origin(b.branch)),
{
    let m=machine();let x=build::root(m,lanes(),b);let z=reference(m,b,5);
    assert forall|p:Process| #[trigger] (x.cfg.private)(p)==empty() by {
        reveal_with_fuel(crate::protocol::memory,6);crate::checkpoint::prefix_index(0);
    }
    assert(crate::sr1_majorities::count(b,5)==5);
    assert forall|p:Process| p!=at(crate::sr1_majorities::missing(b)) implies #[trigger] (z.cfg.private)(p)==empty() by {assert((x.cfg.private)(p)==empty());crate::sr1_majorities::local_at(m,b,p,5);}
    assert(z.cfg.net.pending =~= state_after(b,5).pending && z.cfg.net.locals =~= state_after(b,5).locals);
    let es=dispatch::initial_sends();
    assert forall|i:int| 0<=i<es.len() implies (m.accept)(crate::protocol::memory(m,es[i].actor,es,i as nat),#[trigger] es[i])
        by {assert(i==0 || i==1 || i==2);}
    assert forall|k:nat| k<=3 implies !(m.done)(#[trigger] crate::protocol::memory(m,Process::FirstClient,es,k))
        by {assert(k==0 || k==1 || k==2 || k==3);reveal_with_fuel(crate::protocol::memory,4);}
}

pub open spec fn locked(x:State<Local>,r:Replica) -> bool {
    (x.cfg.private)(at(Replica::R3)).peer==Some(r)
        && forall|id:nat| x.cfg.net.pending.contains_key(id) && first_reply(#[trigger] x.cfg.net.pending[id])
            && x.cfg.net.pending[id].from==at(Replica::R3) ==> id==ticket(r)
}
pub open spec fn queued(x:State<Local>,b:Fork,r:Replica) -> bool {
    locked(x,r) && (x.cfg.private)(Process::FirstClient)==empty() && !x.cfg.net.first_stopped
        && x.cfg.net.pending.get(report_id(r))==Some(reply(r,sampled(r)))
        && x.cfg.net.pending.get(ticket(r))==Some(reply(Replica::R3,first_value(b)))
}

spec fn fired_actions(m:Program<Local>,g:cmp::Gate<Local>,x:State<Local>,s:Seq<Event>) -> Seq<Event> {asm::actions(cmp::fired(m,g,x,s))}

proof fn accepted_proposals(m:Program<Local>,g:cmp::Gate<Local>,x:State<Local>,s:Seq<Event>,states:Seq<State<Local>>)
    requires states.len()==s.len()+1,states[0]==x,forall|i:int| 0<=i<s.len() ==>
        cmp::ready(m,g,states[i],#[trigger] s[i]) && read::next(m,states[i],s[i])==states[i+1],
    ensures fired_actions(m,g,x,s)==s,
        forall|i:int| 0<=i<s.len() ==> #[trigger] cmp::fired(m,g,x,s)[i]==process_step(states[i].cfg.net,s[i]),
    decreases s.len(),
{
    if s.len()>0 {
        let t=s.drop_first();let h=states.drop_first();assert(cmp::ready(m,g,x,s[0]));
        assert forall|i:int| 0<=i<t.len() implies cmp::ready(m,g,h[i],#[trigger] t[i]) && read::next(m,h[i],t[i])==h[i+1] by {
            assert(h[i]==states[i+1] && t[i]==s[i+1] && h[i+1]==states[i+2]);
        }
        accepted_proposals(m,g,h[0],t,h);assert(fired_actions(m,g,x,s) =~= seq![s[0]]+fired_actions(m,g,h[0],t));assert(s =~= seq![s[0]]+t);
        assert forall|i:int| 0<=i<s.len() implies #[trigger] cmp::fired(m,g,x,s)[i]==process_step(states[i].cfg.net,s[i]) by {
            if i>0 {assert(cmp::fired(m,g,x,s)[i]==cmp::fired(m,g,h[0],t)[i-1] && t[i-1]==s[i] && h[i-1]==states[i]);}
        }
    }
}
// Check the cut on both possible live sets and on either weak input.
proof fn collect(x:State<Local>,b:Fork,r:Replica)
    requires ready_root(x,b,r),
    ensures queued(end(machine(),prepare(),x,agenda(r)),b,r),
        ({let z=end(machine(),prepare(),x,prefix(r));let R=at(Replica::R3);
            locked(z,r) && (z.cfg.private)(R)==Local{requested:true,peer:Some(r),..empty()} && (z.cfg.private)(Process::FirstClient)==empty()
                && live(z.cfg.net,at(Replica::R3)) && z.cfg.net.locals==x.cfg.net.locals && (forall|i:nat| i==14 || i==15 ==> !#[trigger] z.cfg.net.pending.contains_key(i)
                    && !z.owners.contains_key(i) && !z.reserved.contains(i))}),
        end(machine(),prepare(),x,native(b,r))==end(machine(),prepare(),x,agenda(r)),
        asm::actions(cmp::fired(machine(),prepare(),x,agenda(r)))==native(b,r),
        ({let t=cmp::fired(machine(),prepare(),x,agenda(r));crate::first_causality::intake_at(t[0],r)
            && crate::first_causality::intake_at(t[3],Replica::R3)
            && forall|i:int| 0<=i<t.len() ==> (#[trigger] t[i]).actor==if i<3 {at(r)} else {at(Replica::R3)}}),
        (end(machine(),prepare(),x,agenda(r)).cfg.private)(at(r))==(Local{requested:true,replied:true,..empty()}),
        ({let z=end(machine(),prepare(),x,agenda(r));let other=if r==Replica::R1 {Replica::R2} else {Replica::R1};
            (z.cfg.private)(at(other))==(x.cfg.private)(at(other)) && !z.cfg.net.pending.contains_key(20) && !z.cfg.net.pending.contains_key(21)
                && !z.reserved.contains(20) && !z.reserved.contains(21)}),
{
    let m=machine();let g=prepare();let s=prefix(r);
    let x1=read::next(m,x,s[0]);let x2=read::next(m,x1,s[1]);let x3=read::next(m,x2,s[2]);
    let x4=read::next(m,x3,s[3]);let x5=read::next(m,x4,s[4]);
    assert((x.cfg.net.locals)(r)==sampled(r) && (x.cfg.net.locals)(Replica::R3)==first_value(b));
    assert(cmp::ready(m,g,x,s[0]) && cmp::ready(m,g,x1,s[1]) && cmp::ready(m,g,x2,s[2]));
    assert(cmp::ready(m,g,x3,s[3]) && cmp::ready(m,g,x4,s[4]));
    cmp::scan_step(m,g,x,s);cmp::scan_step(m,g,x1,s.skip(1));cmp::scan_step(m,g,x2,s.skip(2));
    cmp::scan_step(m,g,x3,s.skip(3));cmp::scan_step(m,g,x4,s.skip(4));
    assert forall|j:int| 0<=j<5 implies #[trigger] s.skip(j).drop_first()==s.skip(j+1) by {assert(s.skip(j).drop_first() =~= s.skip(j+1));}
    assert(end(m,g,x,s)==x5);
    let u=agenda(r).skip(5);assert(s+u =~= agenda(r));cmp::append_script(m,g,x,s,u);cmp::scan_step(m,g,x5,u);
    let a=Action::Send(ticket(r),reply(Replica::R3,first_value(b)));let z=read::next(m,x5,a);
    assert(cmp::ready(m,g,x5,a));cmp::scan_step(m,g,cmp::attempt(m,g,x5,u[0]),u.drop_first());
    assert(u.drop_first().drop_first() =~= Seq::empty() && end(m,g,x,agenda(r))==z);
    let last=seq![a];assert(native(b,r) =~= s+last);cmp::append_script(m,g,x,s,last);cmp::scan_step(m,g,x5,last);
    let states=seq![x,x1,x2,x3,x4,x5];
    assert forall|i:int| 0<=i<s.len() implies cmp::ready(m,g,states[i],#[trigger] s[i]) && read::next(m,states[i],s[i])==states[i+1]
        by {assert(i==0 || i==1 || i==2 || i==3 || i==4);}
    accepted_proposals(m,g,x,s,states);
    let t=cmp::fired(m,g,x,agenda(r));let h=cmp::fired(m,g,x,s);
    assert(t =~= h+seq![process_step(x5.cfg.net,a)]);
    assert forall|i:int| 0<=i<t.len() implies (#[trigger] t[i]).actor==if i<3 {at(r)} else {at(Replica::R3)} by {
        if i<5 {assert(t[i]==h[i] && h[i]==process_step(states[i].cfg.net,s[i]));assert(i==0 || i==1 || i==2 || i==3 || i==4);}
    }
    assert(t[0]==process_step(x.cfg.net,s[0]) && t[3]==process_step(x3.cfg.net,s[3]));
    assert(asm::actions(cmp::fired(m,g,x,agenda(r))) =~= native(b,r));
    assert(locked(x5,r));assert(locked(z,r));
}

pub open spec fn caller(x:State<Local>,r:Replica) -> Tape {
    let d=Action::<Wire>::Deliver(report_id(r));let e=Action::<Wire>::Deliver(ticket(r));
    seq![process_step(x.cfg.net,d),process_step(read::next(machine(),x,d).cfg.net,e)]
}
proof fn publish(x:State<Local>,b:Fork,r:Replica)
    requires queued(x,b,r),r!=Replica::R3,
    ensures ({let m=machine();let c=caller(x,r);let z=tape::after(m,x,c);
        tape::plays(m,x,c) && mail::posted(m)(z) && first()((z.cfg.private)(Process::FirstClient))==first_value(b)
            && c[0].incoming==Some(reply(r,sampled(r))) && c[1].incoming==Some(reply(Replica::R3,first_value(b)))
            && (r==crate::origin(b.branch) ==> mb::mailbox(m,first(),b,x,c))}),
{
    let m=machine();let c=caller(x,r);let e=c[0];let y=read::next(m,x,e.action);let z=read::next(m,y,c[1].action);
    assert(c.drop_first() =~= seq![c[1]] && c.drop_first().drop_first() =~= Seq::empty());
    assert((z.cfg.private)(Process::FirstClient).tickets.intersect((z.cfg.private)(Process::FirstClient).heard).contains(r));
    reveal_with_fuel(tape::plays,3);reveal_with_fuel(tape::after,3);reveal_with_fuel(crate::first_causality::pending_inputs,3);
    assert forall|i:int| 0<=i<c.len() implies (#[trigger] c[i]).actor==Process::FirstClient && c[i].action is Deliver
        && c[i].incoming==x.cfg.net.pending.get(c[i].action->Deliver_0) by {assert(i==0 || i==1);}
    crate::independent_preparations::initial_mailbox(m,x,c);
    assert(build::heard(c,r)) by {assert(c[0].incoming==Some(reply(r,sampled(r))));}
    assert(build::heard(c,Replica::R3)) by {assert(c[1].incoming==Some(reply(Replica::R3,first_value(b))));}
}

proof fn keep_lock(x:State<Local>,r:Replica,a:Event)
    requires locked(x,r),read::service_step(machine())(x,a,read::next(machine(),x,a)),
    ensures locked(read::next(machine(),x,a),r),
{
    let y=read::next(machine(),x,a);
    assert forall|id:nat| y.cfg.net.pending.contains_key(id) && first_reply(#[trigger] y.cfg.net.pending[id])
        && y.cfg.net.pending[id].from==at(Replica::R3) implies id==ticket(r) by {
        if !(a is Send && a->Send_0==id) {assert(y.cfg.net.pending.get(id)==x.cfg.net.pending.get(id));}
    }
}
proof fn lock_on_tape(x:State<Local>,r:Replica,t:Tape)
    requires locked(x,r),tape::plays(machine(),x,t),
    ensures locked(tape::after(machine(),x,t),r),
    decreases t.len(),
{
    if t.len()>0 {keep_lock(x,r,t[0].action);lock_on_tape(read::next(machine(),x,t[0].action),r,t.drop_first());}
}
pub open spec fn unheard(s:Local,r:Replica) -> bool {s.result.is_none() && !s.heard.contains(r) && s.tickets.subset_of(set![r])}
proof fn caller_cannot_finish(x:State<Local>,r:Replica,c:Tape)
    requires r!=Replica::R3,locked(x,r),unheard((x.cfg.private)(Process::FirstClient),r),tape::plays(machine(),x,c),
        forall|i:int| 0<=i<c.len() ==> (#[trigger] c[i]).actor==Process::FirstClient && (c[i].incoming.is_some() ==>
            c[i].incoming.unwrap().from!=at(r) && c[i].incoming.unwrap().to==Process::FirstClient),
    ensures !mail::posted(machine())(tape::after(machine(),x,c)),
    decreases c.len(),
{
    if c.len()>0 {
        let e=c[0];let y=read::next(machine(),x,e.action);let C=Process::FirstClient;
        assert(e.actor==C && (e.incoming.is_some() ==> e.incoming.unwrap().from!=at(r) && e.incoming.unwrap().to==C));
        keep_lock(x,r,e.action);
        if e.incoming.is_some() && first_reply(e.incoming.unwrap()) {
            let q=e.incoming.unwrap();let s=(x.cfg.private)(C);let h=s.heard.insert(q.from->At_0);let t=(y.cfg.private)(C).tickets;
            if q.from==at(Replica::R3) {assert(e.action is Deliver && x.cfg.net.pending[e.action->Deliver_0]==q && e.action->Deliver_0==ticket(r));}
            assert(t.subset_of(set![r]) && !h.contains(r));assert(t.intersect(h) =~= Set::empty());
        }
        assert(unheard((y.cfg.private)(C),r));let u=c.drop_first();
        assert forall|i:int| 0<=i<u.len() implies (#[trigger] u[i]).actor==C && (u[i].incoming.is_some() ==>
            u[i].incoming.unwrap().from!=at(r) && u[i].incoming.unwrap().to==C) by {assert(u[i]==c[i+1]);}
        caller_cannot_finish(y,r,u);
    }
}

proof fn no_designated_service(x:State<Local>,b:Fork,r:Replica)
    requires r!=Replica::R3,r!=crate::origin(b.branch),locked(x,r),(x.cfg.private)(Process::FirstClient)==empty(),
    ensures !qs::viable(machine(),first(),b,x),
{
    let m=machine();if qs::viable(m,first(),b,x) {
        let (t,c)=choose|t:Tape,c:Tape| #[trigger] qs::complete(m,first(),b,x,t,c);let z=tape::after(m,x,t);
        lock_on_tape(x,r,t);mb::ordinary_keeps_caller(m,x,t);
        assert forall|i:int| 0<=i<c.len() implies (#[trigger] c[i]).actor==Process::FirstClient && (c[i].incoming.is_some() ==>
            c[i].incoming.unwrap().from!=at(r) && c[i].incoming.unwrap().to==Process::FirstClient) by {
            if c[i].incoming.is_some() {let h=c.take(i);assert(h+c.skip(i) =~= c);tape::concat(m,z,h,c.skip(i));assert(c.skip(i)[0]==c[i]);
                assert(process_step(tape::after(m,z,h).cfg.net,c[i].action)==c[i]);assert(c[i].action is Deliver);}
        }
        caller_cannot_finish(z,r,c);
    }
}

pub proof fn local_loss(b:Fork,d:Fork)
    requires b.branch!=d.branch,b.notice==d.notice,
    ensures ({
        let m=machine();let r=crate::origin(b.branch);let s=agenda(r);let x=build::root(m,lanes(),b);let y=build::root(m,lanes(),d);
        let z=end(m,prepare(),y,s);let c=caller(end(m,prepare(),x,s),r);
        (forall|q:Replica| q!=Replica::R3 ==> #[trigger] (end(m,prepare(),x,s).cfg.private)(at(q))==(z.cfg.private)(at(q)))
            && qs::collected(m,first(),b,x,s,c) && qs::viable(m,first(),d,y) && !qs::viable(m,first(),d,z)
            && tape::plays(m,z,caller(z,r)) && first()((tape::after(m,z,caller(z,r)).cfg.private)(Process::FirstClient))==first_value(d)
            && mail::fair_opportunity(m,runnable(),z) && (forall|e:fair::Run<Local>| #[trigger] fair::execution(m,e,z) && fair::fair(e,runnable())
                ==> exists|k:nat| #[trigger] mail::posted(m)((e.state)(k)))
    }),
{
    let m=machine();let r=crate::origin(b.branch);let q=crate::origin(d.branch);let g=prepare();let s=agenda(r);
    let x=build::root(m,lanes(),b);let y=build::root(m,lanes(),d);let z=end(m,g,y,s);
    roots(b,r);roots(b,q);roots(d,r);roots(d,q);collect(x,b,r);collect(y,d,r);publish(end(m,g,x,s),b,r);publish(z,d,r);
    fair_continuation(z);
    assert forall|e:fair::Run<Local>| #[trigger] fair::execution(m,e,z) && fair::fair(e,runnable())
        implies exists|k:nat| #[trigger] mail::posted(m)((e.state)(k)) by {all_fair_returns_from_queued_cut(z,d,r,e);}
    no_designated_service(z,d,r);collect(y,d,q);let h=agenda(q);let v=end(m,g,y,h);
    publish(v,d,q);mb::native_proposals(m,y,h);
    assert(qs::complete(m,first(),d,y,cmp::fired(m,g,y,h),caller(v,q)));
}

// A genuine sole-majority suffix, offered at the same R3 value after the
// opposite native collection. Both R3 requests were consumed. Neither R3
// has sent a reply yet. Its first peer is the only difference in memory.
pub proof fn native_collection_blocks_target(b:Fork,d:Fork)
    requires b.branch!=d.branch,b.notice==d.notice,
    ensures ({
        let m=machine();let g=prepare();let l=lanes();let p=crate::origin(b.branch);let q=crate::origin(d.branch);
        let x=build::root(m,l,b);let y=build::root(m,l,d);let s=native(b,p);let z=end(m,g,y,s);
        let masked=reference(m,d,5);let u=end(m,g,masked,prefix(q));let a=native(d,q).last();
        let R=at(Replica::R3);let e=process_step(u.cfg.net,a);
        qs::collected(m,first(),b,x,s,caller(end(m,g,x,s),p)) && !qs::viable(m,first(),d,z)
            && mb::mailbox(m,first(),d,end(m,g,masked,native(d,q)),caller(end(m,g,masked,native(d,q)),q))
            && crate::quorum_projection::refusal(m,u,z,e) && e.own_local==Some(first_value(d))
            && (u.cfg.private)(R)==Local{peer:Some(q),..(z.cfg.private)(R)}
            && (z.cfg.private)(R).peer==Some(p) && cmp::ready(m,g,z,native(d,p).last())
            && queued(read::next(m,z,native(d,p).last()),d,p)
    }),
{
    let m=machine();let g=prepare();let l=lanes();let p=crate::origin(b.branch);let q=crate::origin(d.branch);
    let x=build::root(m,l,b);let y=build::root(m,l,d);let s=native(b,p);let h=prefix(p);
    roots(b,p);roots(d,p);collect(x,b,p);publish(end(m,g,x,s),b,p);collect(y,d,p);
    let z=end(m,g,y,h);let last=seq![s.last()];
    assert(s =~= h+last);cmp::append_script(m,g,y,h,last);cmp::scan_step(m,g,z,last);
    assert(!cmp::ready(m,g,z,s.last()) && end(m,g,y,s)==z);no_designated_service(z,d,p);
    let masked=reference(m,d,5);collect(masked,d,q);let u=end(m,g,masked,prefix(q));let a=native(d,q).last();
    publish(end(m,g,masked,native(d,q)),d,q);
    assert(a==Action::Send(ticket(q),reply(Replica::R3,first_value(d))));
    assert(!u.cfg.net.pending.contains_key(ticket(q)) && !z.cfg.net.pending.contains_key(ticket(q)));
    assert(process_step(u.cfg.net,a)==process_step(z.cfg.net,a));
    let e=process_step(u.cfg.net,a);let R=at(Replica::R3);
    assert((u.cfg.private)(R)==Local{peer:Some(q),..(z.cfg.private)(R)});
    assert(enabled(u.cfg.net,a) && enabled(z.cfg.net,a));
    assert(read::names_sender(u,a) && read::names_sender(z,a));
    assert(crate::confirmation::fresh_send(a,u.reserved) && crate::confirmation::fresh_send(a,z.reserved));
    assert(e.own_local==Some(first_value(d)) && permitted((u.cfg.private)(R),e) && !permitted((z.cfg.private)(R),e));
    assert(cmp::ready(m,g,u,a));assert(read::service_step(m)(u,a,read::next(m,u,a)));
    assert(crate::quorum_projection::refusal(m,u,z,e));
    assert(qs::collected(m,first(),b,x,s,caller(end(m,g,x,s),p)));
    assert(e.own_local==Some(first_value(d)));
    let v=seq![native(d,p).last()];assert(native(d,p) =~= h+v);cmp::append_script(m,g,y,h,v);cmp::scan_step(m,g,z,v);
    assert(cmp::ready(m,g,z,native(d,p).last()));assert(queued(read::next(m,z,native(d,p).last()),d,p));
}

pub open spec fn who() -> crate::hybrid_fork::Issuer {
    |i:nat| if i==6 || i==9 || i==20 {Replica::R1} else if i==7 || i==10 || i==21 {Replica::R2} else {Replica::R3}
}

proof fn one_actor(t:Tape,p:Process,q:Process,keep:bool)
    requires forall|i:int| 0<=i<t.len() ==> (#[trigger] t[i]).actor==p,
    ensures tape::pick(t,q,keep)==if (p==q)==keep {t} else {Seq::empty()},
    decreases t.len(),
{
    if t.len()>0 {
        let u=t.drop_first();assert(t[0].actor==p && seq![t[0]]+u =~= t);
        assert forall|i:int| 0<=i<u.len() implies (#[trigger] u[i]).actor==p by {assert(u[i]==t[i+1]);}
        one_actor(u,p,q,keep);
    }
}
proof fn read_groups(full:Tape,r:Replica,q:Process,keep:bool)
    requires full.len()==8,r!=Replica::R3,forall|i:int| 0<=i<8 ==> (#[trigger] full[i]).actor==if i<3 {at(r)}
        else if i<6 {at(Replica::R3)} else {Process::FirstClient},
    ensures tape::pick(full,q,keep)==
        (if (at(r)==q)==keep {full.take(3)} else {Seq::empty()})
        +(if (at(Replica::R3)==q)==keep {full.subrange(3,6)} else {Seq::empty()})
        +(if (Process::FirstClient==q)==keep {full.skip(6)} else {Seq::empty()}),
{
    let a=full.take(3);let b=full.subrange(3,6);let c=full.skip(6);assert(a+b+c =~= full);
    assert forall|i:int|0<=i<b.len() implies (#[trigger] b[i]).actor==at(Replica::R3) by {assert(b[i]==full[i+3]);}
    assert forall|i:int|0<=i<c.len() implies (#[trigger] c[i]).actor==Process::FirstClient by {assert(c[i]==full[i+6]);}
    assert forall|i:int|0<=i<a.len() implies (#[trigger] a[i]).actor==at(r) by {assert(a[i]==full[i]);}
    one_actor(a,at(r),q,keep);one_actor(b,at(Replica::R3),q,keep);one_actor(c,Process::FirstClient,q,keep);
    crate::first_causality::pick_concat(a,b,q,keep);crate::first_causality::pick_concat(a+b,c,q,keep);
}

proof fn solicited_trace(b:Fork,r:Replica,t:Tape,c:Tape)
    requires r==crate::origin(b.branch),t.len()==6,c.len()==2,asm::actions(t)==native(b,r),
        crate::first_causality::intake_at(t[0],r),crate::first_causality::intake_at(t[3],Replica::R3),
        forall|i:int| 0<=i<t.len() ==> (#[trigger] t[i]).actor==if i<3 {at(r)} else {at(Replica::R3)},
        c[0].actor==Process::FirstClient,c[0].action==Action::<Wire>::Deliver(report_id(r)),c[0].incoming==Some(reply(r,sampled(r))),
        c[1].actor==Process::FirstClient,c[1].action==Action::<Wire>::Deliver(ticket(r)),c[1].incoming==Some(reply(Replica::R3,first_value(b))),
    ensures crate::first_causality::source_shape(t+c,b,crate::sr1_contract::replies()),tape::pick(t+c,Process::FirstClient,false)==t,
{
    let C=Process::FirstClient;let full=t+c;
    assert forall|i:int| 0<=i<8 implies (#[trigger] full[i]).actor==if i<3 {at(r)} else if i<6 {at(Replica::R3)} else {C}
        by {if i<6 {assert(full[i]==t[i]);} else {assert(full[i]==c[i-6] && (i==6 || i==7));}}
    let left=tape::pick(full,at(r),true);let right=tape::pick(full,at(Replica::R3),true);let cc=tape::pick(full,C,true);
    read_groups(full,r,at(r),true);read_groups(full,r,at(Replica::R3),true);read_groups(full,r,C,true);read_groups(full,r,C,false);
    assert(left =~= full.take(3) && right =~= full.subrange(3,6) && cc =~= c && tape::pick(full,C,false) =~= t);
    assert(left[0]==t[0] && left[1]==t[1] && right[0]==t[3] && right[2]==t[5]);
    assert(t[1].action==asm::actions(t)[1] && t[5].action==asm::actions(t)[5]);
    let audit=crate::sr1_contract::replies();
    assert(crate::first_causality::intake_at(left[0],r) && crate::first_causality::answer_at(left[1],r,audit) && crate::first_causality::delivered(left[1],cc[0]));
    assert(crate::first_causality::intake_at(right[0],Replica::R3) && crate::first_causality::answer_at(right[2],Replica::R3,audit)
        && crate::first_causality::delivered(right[2],cc[1]));
}

proof fn trace_names<S>(b:Fork,r:Replica,p:asm::Service<S>)
    requires r==crate::origin(b.branch),p.actions==native(b,r)+seq![Action::<Wire>::Deliver(report_id(r)),Action::Deliver(ticket(r))],
    ensures crate::hybrid_fork::native(p,who()),
{
    assert forall|i:int| 0<=i<p.actions.len() implies crate::quorum_projection::named(who(),#[trigger] p.actions[i])
        by {assert(i==0 || i==1 || i==2 || i==3 || i==4 || i==5 || i==6 || i==7);}
    assert forall|i:int,j:int| 0<=i<j<p.actions.len() && (#[trigger] p.actions[i]) is Send && (#[trigger] p.actions[j]) is Send
        implies p.actions[i]->Send_0!=p.actions[j]->Send_0 by {assert(i==1 || i==2 || i==5);assert(j==1 || j==2 || j==5);}
}

// Check the actual reference returned by the fragment against the
// existing named, solicited wire interface used to construct an arm.
pub proof fn native_reference(b:Fork) -> (p:asm::Service<Local>)
    ensures crate::first_causality::returning(machine(),b,p),crate::independent_preparations::ordinary_source(p),
        crate::hybrid_fork::wire_route(b,p,who(),crate::sr1_contract::replies()),
        asm::actions(crate::coupled_sources::replicas(p))==native(b,crate::origin(b.branch)),
        first()((p.states.last().cfg.private)(Process::FirstClient))==first_value(b),
{
    let m=machine();let r=crate::origin(b.branch);let x=reference(m,b,5);let g=prepare();let s=agenda(r);
    roots(b,r);collect(x,b,r);let t=cmp::fired(m,g,x,s);let z=end(m,g,x,s);let c=caller(z,r);
    mb::native_proposals(m,x,s);publish(z,b,r);let p=mb::release_to_service(m,first(),b,x,t,c);
    assert(t.len()==asm::actions(t).len() && native(b,r).len()==6);solicited_trace(b,r,t,c);let full=tape::record(p,0);assert(full==t+c && asm::actions(full) =~= p.actions);
    assert(asm::actions(t+c) =~= asm::actions(t)+asm::actions(c));
    assert(asm::actions(c) =~= seq![Action::<Wire>::Deliver(report_id(r)),Action::Deliver(ticket(r))]);trace_names(b,r,p);p
}

pub open spec fn runnable() -> fair::Runnable {|n:crate::read_call::Net,p|live(n,p)}

// Each live packet or live process has a genuine one-step turn. This
// also gives fair extensions of the measured terminal prefixes.
pub proof fn fair_continuation(x:State<Local>)
    ensures mail::fair_opportunity(machine(),runnable(),x),
{
    let m=machine();let run=runnable();let region=|_s:State<Local>|true;
    assert forall|s:State<Local>| region(s) implies #[trigger] fair::schedulable(m,run,s) by {
        assert forall|d:fair::Duty| #[trigger] fair::can_schedule(m,run,s,d) by {
            let net=s.cfg.net;let a=match d {
                fair::Duty::Packet(id) if net.pending.contains_key(id) && live(net,net.pending[id].to)=>Action::Deliver(id),
                fair::Duty::Turn(p) if live(net,p)=>Action::Strong(p),
                _=>Action::Strong(if net.unavailable==Some(Replica::R1) {at(Replica::R2)} else {at(Replica::R1)}),
            };
            let y=read::next(m,s,a);assert(read::service_step(m)(s,a,y) && fair::discharged(d,run,net,a));
            let w=crate::promotion_wait::Path{states:seq![s,y],actions:seq![a]};
            assert forall|i:int| 0<=i<w.actions.len() implies read::service_step(m)(w.states[i],#[trigger] w.actions[i],w.states[i+1]) by {assert(i==0);}
            assert(fair::discharged(d,run,w.states[0].cfg.net,w.actions[0]));
            assert(exists|j:int| 0<=j<w.actions.len() && #[trigger] fair::discharged(d,run,w.states[j].cfg.net,w.actions[j]));assert(fair::turn(m,run,s,d,w));
        }
    }
    mail::fair_reference_from_turns(m,run,region,x);
}

spec fn seen(x:State<Local>,r:Replica,tag:bool) -> bool {
    let c=(x.cfg.private)(Process::FirstClient);if tag {c.tickets.contains(r)} else {c.heard.contains(r)}
}
spec fn outstanding(x:State<Local>,b:Fork,r:Replica,tag:bool) -> bool {
    if tag {x.cfg.net.pending.get(ticket(r))==Some(reply(Replica::R3,first_value(b)))}
    else {x.cfg.net.pending.get(report_id(r))==Some(reply(r,sampled(r)))}
}
spec fn consistent(x:State<Local>,r:Replica) -> bool {
    seen(x,r,true) && seen(x,r,false) ==> mail::posted(machine())(x)
}
proof fn remember(x:State<Local>,b:Fork,r:Replica,tag:bool,a:Event,y:State<Local>)
    requires r!=Replica::R3,consistent(x,r),read::service_step(machine())(x,a,y),
    ensures consistent(y,r),seen(x,r,tag) ==> seen(y,r,tag),
        outstanding(x,b,r,tag) ==> outstanding(y,b,r,tag) || seen(y,r,tag),
        outstanding(x,b,r,tag) && a==Action::<Wire>::Deliver(if tag {ticket(r)} else {report_id(r)}) ==> seen(y,r,tag),
{
    let c=Process::FirstClient;let e=process_step(x.cfg.net,a);
    if e.actor==c && e.incoming.is_some() {
        assert(e.action is Deliver && e.incoming.unwrap().to==c);
        if seen(y,r,true) && seen(y,r,false) {
            assert((y.cfg.private)(c).tickets.intersect((y.cfg.private)(c).heard).contains(r));
        }
    }
}
proof fn until(e:fair::Run<Local>,b:Fork,r:Replica,tag:bool,i:nat,j:nat)
    requires i<=j,r!=Replica::R3,fair::execution(machine(),e,(e.state)(0)),consistent((e.state)(i),r),
    ensures consistent((e.state)(j),r),seen((e.state)(i),r,tag) ==> seen((e.state)(j),r,tag),
        outstanding((e.state)(i),b,r,tag) ==> outstanding((e.state)(j),b,r,tag) || seen((e.state)(j),r,tag),
        (forall|k:nat| i<=k<j ==> !#[trigger] mail::posted(machine())((e.state)(k))) && !(e.state)(i).cfg.net.first_stopped
            ==> !(e.state)(j).cfg.net.first_stopped,
    decreases j-i,
{
    if i<j {
        let k=(j-1) as nat;until(e,b,r,tag,i,k);
        assert(read::service_step(machine())((e.state)(k),(e.action)(k),(e.state)(j)));
        remember((e.state)(k),b,r,tag,(e.action)(k),(e.state)(j));
        if (forall|n:nat| i<=n<j ==> !#[trigger] mail::posted(machine())((e.state)(n))) && !(e.state)(i).cfg.net.first_stopped {
            assert forall|n:nat| i<=n<k implies !#[trigger] mail::posted(machine())((e.state)(n)) by {};
            assert(!mail::posted(machine())((e.state)(k)));assert((e.action)(k)!=Action::<Wire>::StopFirstClient);
        }
    }
}
proof fn fair_receipt(x:State<Local>,b:Fork,r:Replica,tag:bool,e:fair::Run<Local>) -> (i:nat)
    requires queued(x,b,r),r!=Replica::R3,fair::execution(machine(),e,x),fair::fair(e,runnable()),
        forall|k:nat| !#[trigger] mail::posted(machine())((e.state)(k)),
    ensures seen((e.state)(i),r,tag),
{
    let id=if tag {ticket(r)} else {report_id(r)};let phy=fair::physical(e);
    assert((phy.state)(0).pending.contains_key(id) && (phy.state)(0).pending[id].to==Process::FirstClient);
    let j=choose|j:nat| j>=0 && (#[trigger] (phy.action)(j)==Action::<Wire>::Deliver(id)
        || !live((phy.state)(j),(phy.state)(0).pending[id].to));
    until(e,b,r,tag,0,j);assert((e.action)(j)==Action::<Wire>::Deliver(id));
    assert(read::service_step(machine())((e.state)(j),(e.action)(j),(e.state)(j+1)));
    remember((e.state)(j),b,r,tag,(e.action)(j),(e.state)(j+1));j+1
}

// Quantifies over every fair interleaving at the reached cut, including
// other genuine replica work and weak delivery. Slots cannot be stolen.
pub proof fn all_fair_returns_from_queued_cut(x:State<Local>,b:Fork,r:Replica,e:fair::Run<Local>)
    requires r!=Replica::R3,queued(x,b,r),fair::execution(machine(),e,x),fair::fair(e,runnable()),
    ensures exists|k:nat| #[trigger] mail::posted(machine())((e.state)(k)),
{
    if !(exists|k:nat| #[trigger] mail::posted(machine())((e.state)(k))) {
        let i=fair_receipt(x,b,r,false,e);let j=fair_receipt(x,b,r,true,e);
        let k=if i>j {i} else {j};until(e,b,r,false,0,i);until(e,b,r,true,0,j);
        until(e,b,r,false,i,k);until(e,b,r,true,j,k);assert(mail::posted(machine())((e.state)(k)));
    }
}

// The only outgoing ordinary SR1 packet R3 can issue is to C1.
// Its value is a genuine sample. The ballot update itself uses the
// packet's sender and is insensitive to the value in R3's cell.
pub proof fn ballot_flow(s:Local,e:Observation,r:Replica,v:int)
    requires e.actor==at(Replica::R3),r!=Replica::R3,
    ensures (forall|h:Observation| #[trigger] update(s,h).replied==(s.replied || (h.incoming.is_none() && h.action is Send && first_reply(h.action->Send_1)))),
        (e.incoming==Some(vote(r)) && e.action is Deliver ==> ({
            let other=ProcessStep{own_local:Some(v),..e};
            permitted(s,e) && permitted(s,other) && update(s,e)==update(s,other)
                && update(s,e).peer==if s.peer.is_some() {s.peer} else {Some(r)}
        })),
        (crate::independent_preparations::ordinary_input(e) && e.action is Send && e.action->Send_1.from==e.actor && permitted(s,e)
            ==> first_reply(e.action->Send_1) && e.action->Send_1.to==Process::FirstClient
                && e.own_local==Some(e.action->Send_1.input->Reply_0)),
{}

pub open spec fn issued_for(x:State<Local>,r:Replica) -> bool {
    let one=Replica::R1;let two=Replica::R2;let c=Process::SecondClient;let n=x.cfg.net;
    r!=Replica::R3 && read::issued_to_majority(x) && crate::survivors::after_crash(n)
        && n.pending.get(11)==Some(crate::sr2::query_packet(one)) && n.pending.get(12)==Some(crate::sr2::query_packet(two))
        && !n.pending.contains_key(20) && !n.pending.contains_key(21) && !x.reserved.contains(20) && !x.reserved.contains(21)
        && !x.owners.contains_key(20) && !x.owners.contains_key(21) && (x.cfg.private)(c)==empty()
        && (n.locals)(one)==2 && (n.locals)(two)==5
        && (x.cfg.private)(at(one)).replied==(r==one) && (x.cfg.private)(at(two)).replied==(r==two)
}
pub open spec fn second_actions(r:Replica) -> Seq<Event> {
    let one=Replica::R1;let two=Replica::R2;
    seq![Action::Deliver(11),Action::Deliver(12),Action::Send(20,report2(one,2,r==one)),Action::Send(21,report2(two,5,r==two)),
        Action::Deliver(20),Action::Deliver(21)]
}

// On the independent invocation the observed participation bits suffice
// for this selection for arbitrary old R3 memory and fork input.
pub proof fn read_participation(x:State<Local>,r:Replica) -> (p:asm::Service<Local>)
    requires issued_for(x,r),
    ensures p.actions==second_actions(r),crate::promotion_wait::first_return(read::service_step(machine()),read::returned(res()),x,p),
        res()((p.states.last().cfg.private)(Process::SecondClient))==Some(sampled(r)),
        majority_held(p,sampled(r)),mail::fair_opportunity(machine(),runnable(),p.states.last()),
{
    let m=machine();let a=second_actions(r);
    let x1=read::next(m,x,a[0]);let x2=read::next(m,x1,a[1]);let x3=read::next(m,x2,a[2]);
    let x4=read::next(m,x3,a[3]);let x5=read::next(m,x4,a[4]);let x6=read::next(m,x5,a[5]);
    let p=crate::promotion_wait::Path{states:seq![x,x1,x2,x3,x4,x5,x6],actions:a};
    assert forall|i:int| 0<=i<6 implies read::service_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1])
        && !read::returned(res())(p.states[i]) by {assert(i==0 || i==1 || i==2 || i==3 || i==4 || i==5);}
    assert forall|i:int| 0<=i<6 implies !read::returned(res())(#[trigger] p.states[i]) by {assert(i==0 || i==1 || i==2 || i==3 || i==4 || i==5);}
    assert((p.states[0].cfg.net.locals)(r)==sampled(r) && live_pair().contains(r));fair_continuation(x6);p
}
pub open spec fn majority_held(p:asm::Service<Local>,v:int) -> bool {crate::hybrid_majority::held(p.states,live_pair(),v)}

pub open spec fn original_tape(b:Fork) -> Tape {
    cmp::fired(machine(),prepare(),build::root(machine(),lanes(),b),agenda(crate::origin(b.branch)))
}

proof fn weak_entry(b:Fork)
    ensures ({let m=machine();let l=lanes();let x=crate::independent_preparations::before_offers(m,l);let a=crate::independent_preparations::offers();
        asm::prefix(m,x,a,true) && asm::drive(m,x,a)==asm::entry(m,l)
            && crate::guarded_history::weak_end().answers.get(crate::weak_round::request(crate::Op::W1).id)==Some(1)
            && crate::guarded_history::weak_end().answers.get(crate::weak_round::request(crate::Op::W2).id)==Some(1)
    }),
{
    let m=machine();let l=lanes();let u=crate::independent_preparations::after_offers(m,l);
    crate::checkpoint::origin_updates_are_actually_offered();crate::independent_preparations::shared_weak_entry(m,l,b);
    reveal_with_fuel(asm::drive,3);assert(u.initial =~= m.initial);assert(u==m);
}

// The two original arms have valid finite H histories and fair
// continuations. The differing survivor bit comes from the survivor's
// own SR1 send. Only the elected peer and R3 report to the first caller.
pub proof fn original_calls(b:Fork) -> (p:asm::Service<Local>)
    ensures ({
        let m=machine();let r=crate::origin(b.branch);let t=original_tape(b);let z=build::prepared(m,lanes(),b,t);let c=caller(z,r);
        let x=crate::independent_preparations::cutoff(m,lanes(),b,t,c);let v=res()((p.states.last().cfg.private)(Process::SecondClient)).unwrap();
        asm::prefix(m,crate::independent_preparations::before_offers(m,lanes()),crate::independent_preparations::offers(),true)
            && asm::drive(m,crate::independent_preparations::before_offers(m,lanes()),crate::independent_preparations::offers())==asm::entry(m,lanes())
            && crate::independent_preparations::arm(m,first(),res(),lanes(),b,t,c) && issued_for(x,r)
            && crate::promotion_wait::first_return(read::service_step(m),read::returned(res()),x,p) && p.actions==second_actions(r)
            && v==first_value(b) && majority_held(p,v) && mail::fair_opportunity(m,runnable(),p.states.last())
            && crate::legal(crate::order_extension::at_second(b).ops,crate::order_extension::at_second(b).states,first_value(b),v)
    }),
{
    let m=machine();let l=lanes();let r=crate::origin(b.branch);let other=crate::sr1_majorities::missing(b);
    let x=build::root(m,l,b);let t=original_tape(b);let z=build::prepared(m,l,b,t);let c=caller(z,r);
    weak_entry(b);roots(b,r);roots(b,other);collect(x,b,r);publish(z,b,r);mb::native_proposals(m,x,agenda(r));mb::release(m,first(),res(),l,b,t,c);
    let final1=build::first_end(m,l,b,t,c);let issued=crate::independent_preparations::cutoff(m,l,b,t,c);
    tape::frame(m,x,t,ISet::full(),ISet::full());
    assert(crate::first_pair::sites().contains(at(r)) && crate::first_pair::sites().contains(at(other)));
    assert(final1.cfg.net.pending.get(20)==None && final1.cfg.net.pending.get(21)==None);
    assert(!read::retired_at_failure(final1).contains(20) && !read::retired_at_failure(final1).contains(21));
    assert(issued_for(issued,r));let p=read_participation(issued,r);crate::order_extension::canonical_orders_exist(b);p
}


}
