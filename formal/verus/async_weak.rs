// The weak port for the original all-live fork. Application callbacks see
// their own messages and private state. The transport owns occurrence handles.
use vstd::prelude::*;
use crate::{Op, Replica, checkpoint::*, delivery::*};
use crate::async_messages::{self as net, Command, Headers, Message};
use crate::first_assembly as asm;
use crate::first_splice::Observation;
use crate::independent_read::{self as read, State};
use crate::prepared_hot as hot;
use crate::prepared_service::{self as svc, Exposure};
use crate::read_call::{Event, Program};
use crate::weak_construction as wc;
use crate::weak_round as weak;
use crate::weak_visibility as vis;

verus! {

// These two projections interpret the implementation; neither is a field
// of a packet or an extra argument to a handler.
#[verifier::reject_recursive_types(S)]
pub struct Port<S> {
    pub effect: spec_fn(S, Observation) -> Option<int>,
    pub buffered: spec_fn(S, int) -> bool,
}

pub open spec fn record(b: Fork) -> weak::Receipt {
    let w = weak::request(observed_writer(b));
    (crate::guarded_history::weak_end().journal)(w.site)[w.id]
}

pub proof fn completed_effect(b: Fork)
    ensures record(b).before == 1, record(b).response == 1, record(b).after == first_value(b),
        weak::request(observed_writer(b)).site == crate::origin(b.branch),
        !wc::journal_edge(Op::W1,Op::W2), !wc::journal_edge(Op::W2,Op::W1),
{
    weak::actual_overlap(b);
    wc::weak_prefix_history(b);
}

// A ghost causal mark follows an actual occurrence from its recorded weak
// writer. Relays are allowed. This does not alter a guard or assert storage.
pub struct Marks { pub sites: Set<Replica>, pub flight: Set<nat> }

pub open spec fn seed(b: Fork) -> Marks {
    Marks { sites: set![weak::request(observed_writer(b)).site], flight: Set::empty() }
}
pub open spec fn mark<S>(k: Headers, port: Port<S>, v: int, x: State<S>, a: Event, g: Marks) -> Marks {
    let e = net::callback(k,process_step(x.cfg.net,a));
    let carries = (port.effect)((x.cfg.private)(e.actor),e) == Some(v);
    match a {
        Action::Send(h,msg) => Marks {
            flight: if msg.path==Path::Weak && msg.from is At && g.sites.contains(msg.from->At_0) && carries {
                g.flight.insert(h)
            } else { g.flight.remove(h) }, ..g
        },
        Action::Deliver(h) => Marks {
            sites: if g.flight.contains(h) && e.actor is At && carries { g.sites.insert(e.actor->At_0) } else { g.sites },
            flight: g.flight.remove(h),
        },
        _ => g,
    }
}
pub open spec fn follow<S>(p:Program<S>,k:Headers,port:Port<S>,v:int,x:State<S>,g:Marks,s:Seq<Event>) -> Marks
    decreases s.len(),
{
    if s.len()==0 { g } else {
        follow(p,k,port,v,read::next(net::implementation(k,p),x,s[0]),mark(k,port,v,x,s[0],g),s.drop_first())
    }
}
proof fn follow_join<S>(p:Program<S>,k:Headers,port:Port<S>,v:int,x:State<S>,g:Marks,s:Seq<Event>,t:Seq<Event>)
    ensures follow(p,k,port,v,x,g,s+t) == follow(p,k,port,v,asm::drive(net::implementation(k,p),x,s),
        follow(p,k,port,v,x,g,s),t),
    decreases s.len(),
{
    if s.len()==0 { assert(s+t =~= t); } else {
        assert((s+t).drop_first() =~= s.drop_first()+t);
        follow_join(p,k,port,v,read::next(net::implementation(k,p),x,s[0]),mark(k,port,v,x,s[0],g),s.drop_first(),t);
    }
}
proof fn exclusive_flight<S>(p:Program<S>,k:Headers,port:Port<S>,v:int,w:int,x:State<S>,g:Marks,j:Marks,s:Seq<Event>)
    requires v!=w, g.flight.disjoint(j.flight),
    ensures follow(p,k,port,v,x,g,s).flight.disjoint(follow(p,k,port,w,x,j,s).flight),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0]; let u=mark(k,port,v,x,a,g); let t=mark(k,port,w,x,a,j);
        assert(u.flight.disjoint(t.flight));
        exclusive_flight(p,k,port,v,w,read::next(net::implementation(k,p),x,a),u,t,s.drop_first());
    }
}
pub open spec fn lineage<S>(p:Program<S>,k:Headers,port:Port<S>,b:Fork,pre:Seq<Event>) -> Marks {
    follow(p,k,port,first_value(b),wc::start(net::implementation(k,p)),seed(b),pre)
}

// The common preparation can run real inter-replica sends, arrivals and
// acknowledgments. No arrival of either selected effect at R3 precedes
// the scheduling choice, and its readable cell is still the initial one.
pub open spec fn before_choice<S>(p:Program<S>,k:Headers,port:Port<S>,x:State<S>,s:Seq<Event>) -> bool
    decreases s.len(),
{
    (x.cfg.net.locals)(Replica::R3)==1 && (s.len()==0 || {
        let a=s[0]; let e=net::callback(k,process_step(x.cfg.net,a));
        let v=(port.effect)((x.cfg.private)(e.actor),e);
        !(a is Deliver && e.actor==at(Replica::R3) && e.incoming.unwrap().path==Path::Weak
            && (v==Some(2int) || v==Some(5int)))
            && before_choice(p,k,port,read::next(net::implementation(k,p),x,a),s.drop_first())
    })
}
proof fn before_join<S>(p:Program<S>,k:Headers,port:Port<S>,x:State<S>,s:Seq<Event>,t:Seq<Event>)
    ensures before_choice(p,k,port,x,s+t) == (before_choice(p,k,port,x,s)
        && before_choice(p,k,port,asm::drive(net::implementation(k,p),x,s),t)),
    decreases s.len(),
{
    if s.len()==0 { assert(s+t =~= t); } else {
        assert((s+t).drop_first() =~= s.drop_first()+t);
        before_join(p,k,port,read::next(net::implementation(k,p),x,s[0]),s.drop_first(),t);
    }
}

pub open spec fn to_third(msg:Message) -> bool {
    msg.body.path==Path::Weak && msg.body.from is At && msg.body.from!=at(Replica::R3) && msg.body.to==at(Replica::R3)
}
pub open spec fn queued<S>(k:Headers,x:State<S>,g:Marks,msg:Message,h:nat) -> bool {
    g.flight.contains(h) && net::queue(k,x.cfg.net).get(h)==Some(msg)
}
pub open spec fn offered<S>(k:Headers,x:State<S>,g:Marks,msg:Message) -> bool {
    exists|h:nat| #[trigger] queued(k,x,g,msg,h)
}
// If already in flight there is no second send. Otherwise this is precisely
// the emitting replica's guard and its interpretation of its outgoing callback.
pub open spec fn release<S>(p:Program<S>,k:Headers,port:Port<S>,x:State<S>,g:Marks,b:Fork,msg:Message,mem:S) -> bool {
    let e=net::input(k,x.cfg.net,Command::Send(msg));
    to_third(msg) && (offered(k,x,g,msg) || (g.sites.contains(msg.body.from->At_0)
        && (p.accept)(mem,e) && (port.effect)(mem,e)==Some(record(b).after)))
}
pub open spec fn after_release<S>(p:Program<S>,k:Headers,x:State<S>,g:Marks,msg:Message,c:Process) -> S {
    let e=net::input(k,x.cfg.net,Command::Send(msg));
    if !offered(k,x,g,msg) && c==msg.body.from { (p.update)((x.cfg.private)(c),e) } else { (x.cfg.private)(c) }
}

proof fn callbacks_join<S>(m:Program<S>,k:Headers,x:State<S>,s:Seq<Event>,t:Seq<Event>)
    ensures vis::callbacks(k,x.cfg.net,s+t) == vis::callbacks(k,x.cfg.net,s)
        +vis::callbacks(k,asm::drive(m,x,s).cfg.net,t),
    decreases s.len(),
{
    if s.len()==0 { assert(s+t =~= t); } else {
        assert((s+t).drop_first() =~= s.drop_first()+t);
        callbacks_join(m,k,read::next(m,x,s[0]),s.drop_first(),t);
        assert(vis::callbacks(k,x.cfg.net,s+t) =~= vis::callbacks(k,x.cfg.net,s)
            +vis::callbacks(k,asm::drive(m,x,s).cfg.net,t));
    }
}
pub open spec fn send_log<S>(k:Headers,x:State<S>,g:Marks,msg:Message) -> Seq<Observation> {
    if offered(k,x,g,msg) {seq![]} else {seq![net::input(k,x.cfg.net,Command::Send(msg))]}
}

pub struct Issue { pub events:Seq<Event>, pub handle:nat }

proof fn issue<S>(p:Program<S>,k:Headers,port:Port<S>,pre:Seq<Event>,b:Fork,msg:Message) -> (out:Issue)
    requires ({
        let m=net::implementation(k,p); let x=asm::drive(m,wc::start(m),pre);
        svc::idle(m,x) && release(p,k,port,x,lineage(p,k,port,b,pre),b,msg,(x.cfg.private)(msg.body.from))
    }),
    ensures ({
        let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,pre); let y=asm::drive(m,x,out.events);
        let g=lineage(p,k,port,b,pre);
        vis::replica_prefix(m,x,out.events) && y.cfg.net.locals==x.cfg.net.locals && svc::idle(m,y)
            && (forall|c:Process| (#[trigger] (y.cfg.private)(c))==after_release(p,k,x,g,msg,c))
            && queued(k,y,lineage(p,k,port,b,pre+out.events),msg,out.handle)
            && vis::callbacks(k,x.cfg.net,out.events)==send_log(k,x,g,msg)
            && (if offered(k,x,g,msg) { out.events.len()==0 }
                else { out.events==seq![Action::Send(out.handle,msg.body)] && !x.cfg.net.pending.contains_key(out.handle) })
    }),
{
    let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,pre);
    let g=lineage(p,k,port,b,pre); completed_effect(b);
    if offered(k,x,g,msg) {
        let h=choose|h:nat| #[trigger] queued(k,x,g,msg,h);
        assert(pre+Seq::<Event>::empty() =~= pre);
        Issue { events:seq![], handle:h }
    } else {
        let a=net::realize_step(p,k,x,Command::Send(msg),false,Set::empty());
        let y=read::next(m,x,a); let s=seq![a]; let h=a->Send_0;
        net::project_step(p,k,x,a,false);
        assert(vis::replica_prefix(m,x,s)) by { reveal_with_fuel(vis::replica_prefix,2); }
        assert(asm::drive(m,x,s)==y) by { reveal_with_fuel(asm::drive,2); }
        assert(y.cfg.net.locals =~= x.cfg.net.locals);
        follow_join(p,k,port,first_value(b),base,seed(b),pre,s);
        assert(follow(p,k,port,first_value(b),x,g,s)==mark(k,port,first_value(b),x,a,g)) by { reveal_with_fuel(follow,2); }
        assert(vis::callbacks(k,x.cfg.net,s)==send_log(k,x,g,msg)) by {reveal_with_fuel(vis::callbacks,2);}
        Issue { events:s, handle:h }
    }
}

// Only these local steps are needed at R3 once an arrival is selected.
// Emitting feedback invokes the actual send handler and enqueues the packet.
pub enum Work { Cpu, Feedback(Message) }
pub open spec fn local_event(a:Work) -> Event {
    match a { Work::Cpu => Action::Strong(at(Replica::R3)), Work::Feedback(msg) => Action::Send(msg.id,msg.body) }
}
pub open spec fn local_input(v:int,a:Event) -> Observation {
    Observation { actor:at(Replica::R3), own_local:Some(v), action:a, incoming:None }
}
pub open spec fn local_work<S>(p:Program<S>,z:S,v:int,s:Seq<Work>) -> Option<S>
    decreases s.len(),
{
    if s.len()==0 { Some(z) } else {
        let e=local_input(v,local_event(s[0]));
        let allowed=match s[0] { Work::Cpu => true, Work::Feedback(msg) =>
            msg.body.from==at(Replica::R3) && msg.body.to is At && msg.body.path==Path::Weak };
        if allowed && (p.accept)(z,e) { local_work(p,(p.update)(z,e),v,s.drop_first()) } else { None }
    }
}
pub open spec fn work_log(v:int,s:Seq<Work>) -> Seq<Observation> {
    s.map_values(|w:Work| local_input(v,local_event(w)))
}
pub struct Receiver { pub wait:Seq<Work>, pub prepare:Seq<Work>, pub finish:Seq<Work> }
pub open spec fn arrival(msg:Message) -> Observation {
    Observation { actor:at(Replica::R3), own_local:Some(1int), action:Action::Deliver(msg.id), incoming:Some(msg.body) }
}
pub open spec fn install(v:int) -> Event { Action::Local(Replica::R3,Wire::Copy(v)) }

// The second disjunct is the buffered weak port: receipt records a new
// pending effect; after optional local work, only this recorded effect is
// applied. Install is a local register action, never a mandatory wire tag.
pub open spec fn receiver<S>(p:Program<S>,port:Port<S>,z:S,b:Fork,msg:Message,r:Receiver) -> bool {
    let waiting=local_work(p,z,1,r.wait); let at_receipt=waiting.unwrap();
    let v=record(b).after; let e=arrival(msg); let received=(p.update)(at_receipt,e);
    let cell_after=cell(1,msg.body.input);
    let work=local_work(p,received,cell_after,r.prepare); let t=work.unwrap();
    let apply=local_input(1,install(v)); let direct=cell_after==v;
    to_third(msg) && waiting.is_some() && (p.accept)(at_receipt,e) && (port.effect)(at_receipt,e)==Some(v) && work.is_some()
        && (direct || (cell_after==1 && !(port.buffered)(at_receipt,v) && (port.buffered)(received,v)
            && (port.buffered)(t,v) && (p.accept)(t,apply)))
        && local_work(p,if direct {t} else {(p.update)(t,apply)},v,r.finish).is_some()
}

pub open spec fn receipt_log(b:Fork,msg:Message,r:Receiver) -> Seq<Observation> {
    let v=first_value(b); let at_delivery=cell(1,msg.body.input);
    let local=if at_delivery==v {seq![]} else {seq![local_input(1,install(v))]};
    (((work_log(1,r.wait)+seq![arrival(msg)])+work_log(at_delivery,r.prepare))+local)+work_log(v,r.finish)
}

pub open spec fn r3_frame<S>(k:Headers,x:State<S>,y:State<S>) -> bool {
    svc::ordinary(x)==svc::ordinary(y) && survivor(x.cfg.net)==survivor(y.cfg.net)
        && (forall|c:Process| c!=at(Replica::R3) ==> (#[trigger] (y.cfg.private)(c))==(x.cfg.private)(c))
}
pub open spec fn retained<S>(k:Headers,x:State<S>,y:State<S>) -> bool {
    net::queue(k,x.cfg.net).submap_of(net::queue(k,y.cfg.net))
}
proof fn combine_retention<S>(k:Headers,x:State<S>,y:State<S>,z:State<S>)
    requires retained(k,x,y), retained(k,y,z),
    ensures retained(k,x,z),
{
    vstd::map_lib::lemma_submap_of_trans(net::queue(k,x.cfg.net),net::queue(k,y.cfg.net),net::queue(k,z.cfg.net));
}
pub open spec fn receiver_work(s:Seq<Event>) -> bool {
    forall|i:int| 0<=i<s.len() ==> match #[trigger] s[i] {
        Action::Strong(q) => q==at(Replica::R3),
        Action::Send(_,msg) => msg.from==at(Replica::R3) && msg.to is At && msg.path==Path::Weak,
        _ => false,
    }
}
proof fn run_work<S>(p:Program<S>,k:Headers,x:State<S>,s:Seq<Work>) -> (events:Seq<Event>)
    requires svc::idle(net::implementation(k,p),x), svc::replica_weak(x),
        local_work(p,(x.cfg.private)(at(Replica::R3)),(x.cfg.net.locals)(Replica::R3),s).is_some(),
    ensures ({
        let m=net::implementation(k,p); let y=asm::drive(m,x,events); let q=at(Replica::R3);
        vis::replica_prefix(m,x,events) && receiver_work(events) && asm::prefix(m,x,events,true)
            && y.cfg.net.locals==x.cfg.net.locals && r3_frame(k,x,y) && retained(k,x,y)
            && svc::idle(m,y) && svc::replica_weak(y)
            && (y.cfg.private)(q)==local_work(p,(x.cfg.private)(q),(x.cfg.net.locals)(Replica::R3),s).unwrap()
            && vis::callbacks(k,x.cfg.net,events)==work_log((x.cfg.net.locals)(Replica::R3),s)
            && events.len()==s.len() && forall|i:int| 0<=i<s.len() ==> net::command(k,#[trigger] events[i]) ==
                match s[i] { Work::Cpu=>Command::Other(local_event(s[i])),Work::Feedback(msg)=>Command::Send(msg) }
    }),
    decreases s.len(),
{
    let m=net::implementation(k,p);
    if s.len()==0 { assert(work_log((x.cfg.net.locals)(Replica::R3),s) =~= seq![]); seq![] } else {
        let cmd=match s[0] { Work::Cpu=>Command::Other(local_event(s[0])),Work::Feedback(msg)=>Command::Send(msg) };
        let a=net::realize_step(p,k,x,cmd,false,Set::empty()); let u=read::next(m,x,a);
        net::project_step(p,k,x,a,false);
        assert(vis::replica_prefix(m,x,seq![a])) by { reveal_with_fuel(vis::replica_prefix,2); }
        assert(asm::drive(m,x,seq![a])==u) by { reveal_with_fuel(asm::drive,2); }
        svc::replica_frame(m,x,seq![a]);
        assert(u.cfg.net.locals =~= x.cfg.net.locals); assert(svc::ordinary(u) =~= svc::ordinary(x));
        let rest=run_work(p,k,u,s.drop_first()); let events=seq![a]+rest;
        vis::join_replica_prefix(m,x,seq![a],rest); asm::prefix_concat(m,x,seq![a],rest,true);
        assert forall|i:int| 0<=i<events.len() implies {
            let ev=#[trigger] events[i];
            net::command(k,ev)==match s[i] {Work::Cpu=>Command::Other(local_event(s[i])),Work::Feedback(msg)=>Command::Send(msg)}
                && match ev {Action::Strong(q)=>q==at(Replica::R3),Action::Send(_,msg)=>
                    msg.from==at(Replica::R3) && msg.to is At && msg.path==Path::Weak,_=>false}
        } by { if i>0 {assert(events[i]==rest[i-1] && s[i]==s.drop_first()[i-1]);} }
        let value=(x.cfg.net.locals)(Replica::R3);
        assert(events.drop_first() =~= rest);
        assert(work_log(value,s) =~= seq![local_input(value,local_event(s[0]))]+work_log(value,s.drop_first())) by {
            assert forall|i:int| 0<=i<s.len() implies #[trigger] work_log(value,s)[i]
                ==(seq![local_input(value,local_event(s[0]))]+work_log(value,s.drop_first()))[i] by {
                if i>0 { assert(s[i]==s.drop_first()[i-1]); }
            }
        }
        work_frame(p,k,x,events);
        events
    }
}

pub open spec fn feedback_pending<S>(x:State<S>,s:Seq<Event>) -> bool {
    forall|i:int| 0<=i<s.len() && (#[trigger] s[i]) is Send ==>
        crate::native_fork::weak_packets(x).get(s[i]->Send_0)==Some(s[i]->Send_1)
}
proof fn work_frame<S>(p:Program<S>,k:Headers,x:State<S>,s:Seq<Event>)
    requires vis::replica_prefix(net::implementation(k,p),x,s), receiver_work(s),
    ensures ({
        let y=asm::drive(net::implementation(k,p),x,s);
        y.cfg.net.locals==x.cfg.net.locals && r3_frame(k,x,y) && retained(k,x,y) && feedback_pending(y,s)
    }),
    decreases s.len(),
{
    if s.len()>0 {
        let a=s[0]; let y=read::next(net::implementation(k,p),x,a); let t=s.drop_first();
        assert(match s[0] {Action::Strong(q)=>q==at(Replica::R3),Action::Send(_,msg)=>
            msg.from==at(Replica::R3) && msg.to is At && msg.path==Path::Weak,_=>false});
        assert(receiver_work(t)) by {
            assert forall|i:int| 0<=i<t.len() implies match #[trigger] t[i] {
                Action::Strong(q)=>q==at(Replica::R3),Action::Send(_,msg)=>msg.from==at(Replica::R3)
                    && msg.to is At && msg.path==Path::Weak,_=>false
            } by {assert(t[i]==s[i+1]);}
        }
        net::project_step(p,k,x,a,false);
        assert(y.cfg.net.locals =~= x.cfg.net.locals); assert(svc::ordinary(x) =~= svc::ordinary(y));
        let z=asm::drive(net::implementation(k,p),y,t);
        assert(r3_frame(k,x,y) && retained(k,x,y));
        work_frame(p,k,y,t);
        combine_retention(k,x,y,z);
        assert(r3_frame(k,x,z));
        assert forall|i:int| 0<=i<s.len() && (#[trigger] s[i]) is Send implies
            crate::native_fork::weak_packets(z).get(s[i]->Send_0)==Some(s[i]->Send_1) by {
            if i==0 {
                let h=a->Send_0;
                assert(net::queue(k,y.cfg.net).contains_key(h) && net::queue(k,z.cfg.net).contains_key(h));
            } else { assert(t[i-1]==s[i]); }
        }
    }
}

#[verifier::reject_recursive_types(S)]
pub struct Install<S> {
    pub port:Port<S>, pub pre:Seq<Event>, pub handle:nat, pub wait:Seq<Event>, pub prepare:Seq<Event>, pub finish:Seq<Event>,
}
pub open spec fn feedback_delayed<S>(x:State<S>,c:Install<S>) -> bool {
    feedback_pending(x,c.wait) && feedback_pending(x,c.prepare) && feedback_pending(x,c.finish)
}
pub open spec fn local_install(v:int,msg:Message) -> Seq<Event> {
    if cell(1,msg.body.input)==v { seq![] } else { seq![install(v)] }
}
pub open spec fn trace_for<S>(b:Fork,c:Install<S>,msg:Message) -> Seq<Event> {
    ((((c.pre+c.wait)+seq![Action::Deliver(c.handle)])+c.prepare)+local_install(first_value(b),msg))+c.finish
}

// A certificate records which genuine arrival supplied the value. The only
// extra local cell transition admitted to strong service consumes a buffered
// effect after that receipt. All intermediate guards use native state.
pub open spec fn installation<S>(p:Program<S>,k:Headers,e:Exposure,c:Install<S>) -> bool {
    let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,c.pre);
    let h=c.handle; let b=e.arm; let v=first_value(b); let q=at(Replica::R3);
    let msg=net::queue(k,x.cfg.net)[h]; let at_receipt=asm::drive(m,x,c.wait);
    let u=read::next(m,at_receipt,Action::Deliver(h));
    let t=asm::drive(m,u,c.prepare); let local=local_install(v,msg); let y=asm::drive(m,t,local);
    vis::replica_prefix(m,base,c.pre) && before_choice(p,k,c.port,base,c.pre)
        && survivor(x.cfg.net)==(2int,5int) && (x.cfg.net.locals)(Replica::R3)==1
        && queued(k,x,lineage(p,k,c.port,b,c.pre),msg,h) && to_third(msg)
        && vis::replica_prefix(m,x,c.wait) && receiver_work(c.wait)
        && (c.port.effect)((at_receipt.cfg.private)(q),arrival(msg))==Some(v)
        && net::ready(p,k,at_receipt,Command::Deliver(h),false)
        && vis::replica_prefix(m,u,c.prepare) && receiver_work(c.prepare)
        && (cell(1,msg.body.input)==v || (cell(1,msg.body.input)==1
            && !(c.port.buffered)((at_receipt.cfg.private)(q),v) && (c.port.buffered)((u.cfg.private)(q),v)
            && (c.port.buffered)((t.cfg.private)(q),v) && net::ready(p,k,t,Command::Other(install(v)),false)))
        && vis::replica_prefix(m,y,c.finish) && receiver_work(c.finish)
        && e.events==trace_for(b,c,msg)
}

pub(crate) proof fn installation_frame<S>(p:Program<S>,k:Headers,e:Exposure,c:Install<S>)
    requires installation(p,k,e,c),
    ensures ({
        let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,c.pre);
        let z=svc::endpoint(p,k,e); let h=c.handle;
        asm::prefix(m,base,e.events,true) && svc::idle(m,z) && svc::replica_weak(z)
            && survivor(z.cfg.net)==(2int,5int) && (z.cfg.net.locals)(Replica::R3)==first_value(e.arm)
            && r3_frame(k,x,z) && feedback_delayed(z,c)
            && net::queue(k,x.cfg.net).remove(h).submap_of(net::queue(k,z.cfg.net))
            && (exists|i:int| 0<=i<c.pre.len() && #[trigger] c.pre[i]==Action::Send(h,x.cfg.net.pending[h]))
    }),
{
    let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,c.pre); let h=c.handle;
    let msg=net::queue(k,x.cfg.net)[h]; let d=seq![Action::Deliver(h)];
    let at_receipt=asm::drive(m,x,c.wait); let u=read::next(m,at_receipt,d[0]);
    let v=first_value(e.arm); let t=asm::drive(m,u,c.prepare); let local=local_install(v,msg);
    let y=asm::drive(m,t,local);
    svc::replica_frame(m,base,c.pre);
    wc::prefix_packet_source(m,base,c.pre,h,msg.body);
    svc::replica_frame(m,x,c.wait); work_frame(p,k,x,c.wait);
    assert(net::queue(k,at_receipt.cfg.net).get(h)==Some(msg));
    vis::weak_receipt(p,k,at_receipt,h);
    assert(vis::replica_prefix(m,at_receipt,d)) by {reveal_with_fuel(vis::replica_prefix,2);}
    svc::replica_frame(m,at_receipt,d); assert(svc::ordinary(u) =~= svc::ordinary(at_receipt));
    svc::replica_frame(m,u,c.prepare); work_frame(p,k,u,c.prepare);
    if cell(1,msg.body.input)!=v {net::project_step(p,k,t,install(v),false);}
    assert(asm::prefix(m,t,local,true) && svc::idle(m,y) && svc::replica_weak(y)
        && (y.cfg.net.locals)(Replica::R3)==v && r3_frame(k,t,y) && retained(k,t,y)) by {
        reveal_with_fuel(asm::prefix,2); reveal_with_fuel(asm::drive,2);
    }
    svc::replica_frame(m,y,c.finish); work_frame(p,k,y,c.finish);
    asm::prefix_concat(m,base,c.pre,c.wait,true); let pre=c.pre+c.wait;
    asm::prefix_concat(m,base,pre,d,true);
    asm::prefix_concat(m,base,pre+d,c.prepare,true);
    asm::prefix_concat(m,base,(pre+d)+c.prepare,local,true);
    asm::prefix_concat(m,base,((pre+d)+c.prepare)+local,c.finish,true);
    let z=svc::endpoint(p,k,e);
    combine_retention(k,u,t,y); combine_retention(k,u,y,z);
    assert(r3_frame(k,x,u) && r3_frame(k,x,z));
    assert forall|i:int| 0<=i<c.wait.len() && (#[trigger] c.wait[i]) is Send implies {
        let a=c.wait[i];
        crate::native_fork::weak_packets(z).get(a->Send_0)==Some(a->Send_1)
    } by {
        let a=c.wait[i]; let j=a->Send_0;
        assert(crate::native_fork::weak_packets(at_receipt).get(j)==Some(a->Send_1));
        assert(j!=h && net::queue(k,u.cfg.net).contains_key(j) && net::queue(k,z.cfg.net).contains_key(j));
    }
    combine_retention(k,t,y,z);
    assert forall|i:int| 0<=i<c.prepare.len() && (#[trigger] c.prepare[i]) is Send implies {
        let a=c.prepare[i];
        crate::native_fork::weak_packets(z).get(a->Send_0)==Some(a->Send_1)
    } by {
        let j=c.prepare[i]->Send_0;
        assert(net::queue(k,t.cfg.net).contains_key(j) && net::queue(k,z.cfg.net).contains_key(j));
    }
    let kept=net::queue(k,x.cfg.net).remove(h);
    assert(kept.submap_of(net::queue(k,u.cfg.net)));
    vstd::map_lib::lemma_submap_of_trans(kept,net::queue(k,u.cfg.net),net::queue(k,z.cfg.net));
}

proof fn take_effect<S>(p:Program<S>,k:Headers,port:Port<S>,b:Fork,pre:Seq<Event>,msg:Message,h:nat,r:Receiver)
    -> (out:(Exposure,Install<S>))
    requires ({
        let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,pre);
        vis::replica_prefix(m,base,pre) && before_choice(p,k,port,base,pre) && (x.cfg.net.locals)(Replica::R3)==1
            && survivor(x.cfg.net)==(2int,5int) && queued(k,x,lineage(p,k,port,b,pre),msg,h)
            && receiver(p,port,(x.cfg.private)(at(Replica::R3)),b,msg,r)
    }),
    ensures out.0.arm==b, out.1.port==port, out.1.pre==pre, out.1.handle==h, installation(p,k,out.0,out.1),
        vis::callbacks(k,local_rmw_cells(),out.0.events)==vis::callbacks(k,local_rmw_cells(),pre)+receipt_log(b,msg,r),
{
    let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,pre); let q=at(Replica::R3);
    let v=first_value(b); let d=seq![Action::Deliver(h)]; completed_effect(b);
    svc::replica_frame(m,base,pre);
    let wait=run_work(p,k,x,r.wait); let at_receipt=asm::drive(m,x,wait);
    let u=read::next(m,at_receipt,d[0]);
    assert(net::queue(k,at_receipt.cfg.net).get(h)==Some(msg));
    assert(net::input(k,at_receipt.cfg.net,Command::Deliver(h))==arrival(msg));
    vis::weak_receipt(p,k,at_receipt,h);
    assert(vis::replica_prefix(m,at_receipt,d)) by {reveal_with_fuel(vis::replica_prefix,2);}
    svc::replica_frame(m,at_receipt,d);
    let s=run_work(p,k,u,r.prepare); let t=asm::drive(m,u,s);
    let local=local_install(v,msg); let y=asm::drive(m,t,local);
    if cell(1,msg.body.input)!=v { net::project_step(p,k,t,install(v),false); }
    assert(svc::idle(m,y) && svc::replica_weak(y) && (y.cfg.net.locals)(Replica::R3)==v
        && (y.cfg.private)(q)==(if cell(1,msg.body.input)==v {(t.cfg.private)(q)}
            else {(p.update)((t.cfg.private)(q),local_input(1,install(v)))})) by {reveal_with_fuel(asm::drive,2);}
    let f=run_work(p,k,y,r.finish);
    let c=Install {port,pre,handle:h,wait,prepare:s,finish:f};
    let e=Exposure {arm:b,events:trace_for(b,c,msg)};
    let w=pre+wait; let ds=w+d; let ps=ds+s; let installed=ps+local;
    asm::prefix_concat(m,base,pre,wait,true); asm::prefix_concat(m,base,w,d,true);
    asm::prefix_concat(m,base,ds,s,true); asm::prefix_concat(m,base,ps,local,true);
    callbacks_join(m,k,base,pre,wait); callbacks_join(m,k,base,w,d); callbacks_join(m,k,base,ds,s);
    callbacks_join(m,k,base,ps,local); callbacks_join(m,k,base,installed,f);
    assert(vis::callbacks(k,at_receipt.cfg.net,d)==seq![arrival(msg)]) by {reveal_with_fuel(vis::callbacks,2);}
    assert(vis::callbacks(k,t.cfg.net,local)==(if cell(1,msg.body.input)==v {seq![]} else {seq![local_input(1,install(v))]}))
        by {reveal_with_fuel(vis::callbacks,2);}
    assert(vis::callbacks(k,base.cfg.net,e.events) =~= vis::callbacks(k,base.cfg.net,pre)+receipt_log(b,msg,r));
    (e,c)
}

pub struct Background {
    pub common:Seq<Event>, pub five:Message, pub two:Message, pub alpha:Receiver, pub beta:Receiver,
}

// This interface contains local release, receive, application and optional
// feedback guards only. If both releases run at one relay, its second guard
// sees the real private update from its first send. A pending offer needs
// no send. No pair of post-receipt states or strong result is an input.
pub open spec fn asynchronous<S>(p:Program<S>,k:Headers,port:Port<S>,n:Notice,d:Background) -> bool {
    let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,d.common);
    let a=alpha(n); let b=beta(n); let g=lineage(p,k,port,a,d.common); let j=lineage(p,k,port,b,d.common);
    let third=(x.cfg.private)(at(Replica::R3));
    vis::replica_prefix(m,base,d.common) && before_choice(p,k,port,base,d.common)
        && survivor(x.cfg.net)==(2int,5int)
        && release(p,k,port,x,g,a,d.five,(x.cfg.private)(d.five.body.from))
        && release(p,k,port,x,j,b,d.two,after_release(p,k,x,g,d.five,d.two.body.from))
        && receiver(p,port,third,a,d.five,d.alpha) && receiver(p,port,third,b,d.two,d.beta)
}

// At the unmodified post-RMW boundary the two senders are distinct and the
// queue is empty. Their individual local release guards suffice directly.
pub open spec fn origin_send<S>(p:Program<S>,port:Port<S>,b:Fork,msg:Message) -> bool {
    let src=at(weak::request(observed_writer(b)).site);
    let e=process_step(local_rmw_cells(),Action::Send(msg.id,msg.body));
    to_third(msg) && msg.body.from==src && (p.accept)((p.initial)(src),e)
        && (port.effect)((p.initial)(src),e)==Some(record(b).after)
}
pub proof fn independent_origin_ports<S>(p:Program<S>,k:Headers,port:Port<S>,n:Notice,d:Background)
    requires d.common.len()==0, origin_send(p,port,alpha(n),d.five), origin_send(p,port,beta(n),d.two),
        receiver(p,port,(p.initial)(at(Replica::R3)),alpha(n),d.five,d.alpha),
        receiver(p,port,(p.initial)(at(Replica::R3)),beta(n),d.two,d.beta),
    ensures asynchronous(p,k,port,n,d),
{
    completed_effect(alpha(n)); completed_effect(beta(n)); crate::isolated_rmws();
}

pub open spec fn public_preparation<S>(p:Program<S>,k:Headers,port:Port<S>,n:Notice,d:Background,b:Fork) -> Seq<Observation> {
    let m=net::implementation(k,p); let x=asm::drive(m,wc::start(m),d.common);
    let s=vis::callbacks(k,local_rmw_cells(),d.common);
    let five=send_log(k,x,lineage(p,k,port,alpha(n),d.common),d.five);
    let two=send_log(k,x,lineage(p,k,port,beta(n),d.common),d.two);
    let tail=if b.branch==crate::Branch::Alpha {receipt_log(b,d.five,d.alpha)} else {receipt_log(b,d.two,d.beta)};
    ((s+five)+two)+tail
}

// A release has no R3 input. An occurrence marked for the other writer
// survives even if the two public messages have identical IDs and bodies.
proof fn other_offer<S>(p:Program<S>,k:Headers,port:Port<S>,other:Fork,pre:Seq<Event>,s:Seq<Event>,msg:Message,rival:Message)
    requires ({
        let m=net::implementation(k,p); let x=asm::drive(m,wc::start(m),pre);
        (x.cfg.net.locals)(Replica::R3)==1 && (s.len()==0 || (s.len()==1 && s[0] is Send
            && net::command(k,s[0])==Command::Send(msg) && read::prefix_step(m)(x,s[0],read::next(m,x,s[0]))
            && (port.effect)((x.cfg.private)(msg.body.from),net::input(k,x.cfg.net,Command::Send(msg)))!=Some(first_value(other))))
    }),
    ensures ({
        let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,pre); let y=asm::drive(m,x,s);
        let g=lineage(p,k,port,other,pre); let j=lineage(p,k,port,other,pre+s);
        before_choice(p,k,port,x,s) && j.sites==g.sites
            && forall|h:nat| #[trigger] queued(k,y,j,rival,h)==queued(k,x,g,rival,h)
    }),
{
    let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,pre);
    let g=lineage(p,k,port,other,pre); follow_join(p,k,port,first_value(other),base,seed(other),pre,s);
    if s.len()>0 {
        let a=s[0]; let y=read::next(m,x,a); assert(s.drop_first() =~= seq![]);
        net::project_step(p,k,x,a,false);
        assert((y.cfg.net.locals)(Replica::R3)==1);
        assert(asm::drive(m,x,s)==y) by {reveal_with_fuel(asm::drive,2);}
        assert(before_choice(p,k,port,x,s)) by {reveal_with_fuel(before_choice,2);}
        assert(follow(p,k,port,first_value(other),x,g,s)==mark(k,port,first_value(other),x,a,g))
            by {reveal_with_fuel(follow,2);}
        let j=lineage(p,k,port,other,pre+s);
        assert forall|h:nat| #[trigger] queued(k,y,j,rival,h)==queued(k,x,g,rival,h) by {
            if h==a->Send_0 { assert(!x.cfg.net.pending.contains_key(h) && !j.flight.contains(h)); }
        }
    }
}

#[verifier::reject_recursive_types(S)]
pub struct Preparations<S> {
    pub left:Exposure, pub right:Exposure, pub a:Install<S>, pub b:Install<S>,
}
pub open spec fn original<S>(p:Program<S>,k:Headers,port:Port<S>,n:Notice,d:Background,f:Preparations<S>) -> bool {
    let m=net::implementation(k,p); let base=wc::start(m); let cut=asm::drive(m,base,f.a.pre);
    let l=svc::endpoint(p,k,f.left); let r=svc::endpoint(p,k,f.right);
    f.left.arm==alpha(n) && f.right.arm==beta(n) && f.a.pre==f.b.pre && f.a.pre.take(d.common.len() as int)==d.common
        && f.a.port==port && f.b.port==port && installation(p,k,f.left,f.a) && installation(p,k,f.right,f.b)
        && f.a.handle!=f.b.handle && net::queue(k,cut.cfg.net).get(f.a.handle)==Some(d.five)
        && net::queue(k,cut.cfg.net).get(f.b.handle)==Some(d.two)
        && net::queue(k,l.cfg.net).get(f.b.handle)==Some(d.two) && net::queue(k,r.cfg.net).get(f.a.handle)==Some(d.five)
        && vis::callbacks(k,base.cfg.net,f.left.events)==public_preparation(p,k,port,n,d,alpha(n))
        && vis::callbacks(k,base.cfg.net,f.right.events)==public_preparation(p,k,port,n,d,beta(n))
        && hot::evidence(p,k,f.left)==hot::evidence(p,k,f.right)
}

pub proof fn schedule_original<S>(p:Program<S>,k:Headers,port:Port<S>,n:Notice,d:Background) -> (f:Preparations<S>)
    requires asynchronous(p,k,port,n,d),
    ensures original(p,k,port,n,d,f),
{
    let m=net::implementation(k,p); let base=wc::start(m); let x=asm::drive(m,base,d.common);
    let a=alpha(n); let b=beta(n); completed_effect(a); completed_effect(b);
    before_join(p,k,port,base,d.common,seq![]); assert(d.common+Seq::<Event>::empty() =~= d.common);
    svc::replica_frame(m,base,d.common);
    let five=issue(p,k,port,d.common,a,d.five); let pre=d.common+five.events;
    asm::prefix_concat(m,base,d.common,five.events,true); vis::join_replica_prefix(m,base,d.common,five.events);
    let y=asm::drive(m,base,pre);
    assert(five.events.len()==0 || net::command(k,five.events[0])==Command::Send(d.five));
    other_offer(p,k,port,b,d.common,five.events,d.five,d.two);
    before_join(p,k,port,base,d.common,five.events);
    let j=lineage(p,k,port,b,d.common); let jy=lineage(p,k,port,b,pre);
    assert(offered(k,y,jy,d.two)==offered(k,x,j,d.two)) by {
        if offered(k,x,j,d.two) {
            let h=choose|h:nat| #[trigger] queued(k,x,j,d.two,h);
            assert(queued(k,y,jy,d.two,h));
        }
        if offered(k,y,jy,d.two) {
            let h=choose|h:nat| #[trigger] queued(k,y,jy,d.two,h);
            assert(queued(k,x,j,d.two,h));
        }
    }
    assert(net::input(k,x.cfg.net,Command::Send(d.two))==net::input(k,y.cfg.net,Command::Send(d.two)));
    assert((y.cfg.private)(d.two.body.from)==after_release(p,k,x,lineage(p,k,port,a,d.common),d.five,d.two.body.from));
    let two=issue(p,k,port,pre,b,d.two); let all=pre+two.events;
    asm::prefix_concat(m,base,pre,two.events,true); vis::join_replica_prefix(m,base,pre,two.events);
    assert(two.events.len()==0 || net::command(k,two.events[0])==Command::Send(d.two));
    other_offer(p,k,port,a,pre,two.events,d.two,d.five);
    before_join(p,k,port,base,pre,two.events);
    let cut=asm::drive(m,base,all);
    let ja=lineage(p,k,port,a,pre); let jb=lineage(p,k,port,a,all);
    assert(queued(k,y,ja,d.five,five.handle) && queued(k,cut,jb,d.five,five.handle));
    exclusive_flight(p,k,port,5,2,base,seed(a),seed(b),all);
    assert(five.handle!=two.handle);
    let (l,ac)=take_effect(p,k,port,a,all,d.five,five.handle,d.alpha);
    let (r,bc)=take_effect(p,k,port,b,all,d.two,two.handle,d.beta);
    installation_frame(p,k,l,ac); installation_frame(p,k,r,bc);
    hot::view_from_queue(k,svc::endpoint(p,k,l),cut); hot::view_from_queue(k,svc::endpoint(p,k,r),cut);
    assert(net::queue(k,cut.cfg.net).remove(ac.handle).contains_key(bc.handle));
    assert(net::queue(k,cut.cfg.net).remove(bc.handle).contains_key(ac.handle));
    assert(net::queue(k,svc::endpoint(p,k,l).cfg.net).get(bc.handle)==Some(d.two));
    assert(net::queue(k,svc::endpoint(p,k,r).cfg.net).get(ac.handle)==Some(d.five));
    callbacks_join(m,k,base,d.common,five.events); callbacks_join(m,k,base,pre,two.events);
    assert(all.take(d.common.len() as int) =~= d.common);
    Preparations {left:l,right:r,a:ac,b:bc}
}

// Fix one implementation's weak interpretation for every functional-T
// window. The operation law itself and its native read outcomes are unchanged.
pub open spec fn admitted<S>(p:Program<S>,k:Headers,port:Port<S>) -> hot::Admission {
    |e:Exposure| exists|c:Install<S>| c.port==port && #[trigger] installation(p,k,e,c)
}
pub proof fn original_hot_from_async_replication<S>(p:Program<S>,k:Headers,port:Port<S>,n:Notice,d:Background,
    first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:hot::WeakOrder,plan:svc::Requests,run:crate::fair_read::Runnable)
    -> (out:(Preparations<S>,hot::Execution<S>,hot::Execution<S>))
    requires asynchronous(p,k,port,n,d), hot::fresh_caller(p,plan), crate::first_schedule::startup(net::implementation(k,p)),
        svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        crate::operation_history::operation_t(hot::system_for(p,k,first,res,o,admitted(p,k,port)),crate::register_history::register()),
        hot::weak_word(o(public_preparation(p,k,port,n,d,alpha(n)))),
        hot::weak_word(o(public_preparation(p,k,port,n,d,beta(n)))),
    ensures ({
        let (f,l,r)=out; let m=net::implementation(k,p); let base=wc::start(m);
        let u=asm::drive(m,base,hot::lead(l.first)+l.second); let v=asm::drive(m,base,hot::lead(r.first)+r.second);
        original(p,k,port,n,d,f) && l.first.weak==f.left && r.first.weak==f.right && l.first.sends==r.first.sends
            && svc::contents(k,l.first.sends)==plan && hot::completed(p,k,first,res,l) && hot::completed(p,k,first,res,r)
            && net::queue(k,u.cfg.net).get(f.b.handle)==Some(d.two) && net::queue(k,v.cfg.net).get(f.a.handle)==Some(d.five)
            && feedback_delayed(u,f.a) && feedback_delayed(v,f.b)
            && (hot::bad(m,first,res,l) || hot::bad(m,first,res,r))
    }),
{
    let f=schedule_original(p,k,port,n,d);
    assert(svc::service_entry(p,k,f.left) && svc::service_entry(p,k,f.right));
    hot::laws_at_exposures(p,k,first,res,o,run,f.left,f.right);
    installation_frame(p,k,f.left,f.a); installation_frame(p,k,f.right,f.b);
    let allow=admitted(p,k,port);
    assert(allow(f.left) && allow(f.right));
    let (l,r)=hot::original_hot_at_admitted_exposures(p,k,first,res,o,allow,f.left,f.right,plan,run);
    let m=net::implementation(k,p); let base=wc::start(m);
    let u=asm::drive(m,base,hot::lead(l.first)+l.second); let v=asm::drive(m,base,hot::lead(r.first)+r.second);
    assert(crate::native_fork::weak_packets(svc::endpoint(p,k,f.left)).get(f.b.handle)==Some(d.two.body));
    assert(crate::native_fork::weak_packets(svc::endpoint(p,k,f.right)).get(f.a.handle)==Some(d.five.body));
    assert(crate::native_fork::weak_packets(u).get(f.b.handle)==Some(d.two.body));
    assert(crate::native_fork::weak_packets(v).get(f.a.handle)==Some(d.five.body));
    (f,l,r)
}

}
