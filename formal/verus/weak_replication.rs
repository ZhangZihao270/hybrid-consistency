// BEGIN MODULE: weak_round
pub mod weak_round {
    use vstd::prelude::*;
    use crate::{Op,Replica};
    use crate::facade_linear::CommandSemantics;
    use crate::ordered_round::{self as base,Store};
    use crate::ordered_store::Stamp;
    use crate::stock_facade::{State,Method,initial};
    use crate::checkpoint::Fork;
    use crate::facade_hybrid::prefix;
    use crate::read_recovery::Record;

    verus! {

    // A local weak RPC adapter for the same register and command API as the
    // stock front end. Weak caller IDs are independent of the two strong calls.
    pub type Id = (nat,nat); // weak client, that client's invocation number
    pub struct Request { pub id:Id, pub site:Replica, pub method:Method }
    pub struct Receipt { pub method:Method, pub before:int,pub after:int,pub response:int }
    pub enum Packet { Request(Request), Reply(Id,int) }
    pub struct World {
        pub front:State<Store>,pub wire:Map<nat,Packet>,
        pub issued:Set<Id>,pub answers:Map<Id,int>,pub stopped:Set<nat>,
        pub journal:spec_fn(Replica)->Map<Id,Receipt>,
    }
    pub enum Action { Send(nat,Request), Handle(nat), Receive(nat), Duplicate(nat,nat) }
    pub open spec fn enabled(s:World,a:Action) -> bool {
        match a {
            Action::Send(slot,q)=>!s.wire.contains_key(slot) && !s.issued.contains(q.id) && !s.stopped.contains(q.id.0),
            Action::Handle(i)=>s.wire.contains_key(i) && s.wire[i] is Request && s.front.base.live.contains(s.wire[i]->Request_0.site),
            Action::Receive(i)=>s.wire.contains_key(i) && s.wire[i] is Reply && !s.stopped.contains(s.wire[i]->Reply_0.0),
            Action::Duplicate(i,j)=>s.wire.contains_key(i) && !s.wire.contains_key(j),
        }
    }
    pub open spec fn evaluate(f:CommandSemantics,q:Request,x:int) -> Receipt {
        let (new,returned)=match q.method {Method::Read=>(x,x),Method::Command(code)=>f(code,x)};
        Receipt {method:q.method,before:x,after:new,response:returned}
    }
    pub open spec fn serve(f:CommandSemantics,s:World,i:nat,q:Request) -> World {
        let seen=(s.journal)(q.site);
        if seen.contains_key(q.id) {
            World {wire:s.wire.insert(i,Packet::Reply(q.id,seen[q.id].response)),..s}
        } else {
            let entry=evaluate(f,q,(s.front.base.disk)(q.site).value);
            let disk=|r|if r==q.site {Stamp{value:entry.after,..(s.front.base.disk)(r)}} else {(s.front.base.disk)(r)};
            World {wire:s.wire.insert(i,Packet::Reply(q.id,entry.response)),
                journal:|r|if r==q.site {seen.insert(q.id,entry)} else {(s.journal)(r)},
                front:State{base:Store{disk,..s.front.base},..s.front},..s}
        }
    }
    pub open spec fn step(f:CommandSemantics,s:World,a:Action) -> World {
        match a {
            Action::Send(i,q)=>World {wire:s.wire.insert(i,Packet::Request(q)),issued:s.issued.insert(q.id),..s},
            Action::Handle(i)=>serve(f,s,i,s.wire[i]->Request_0),
            Action::Receive(i)=>World {answers:s.answers.insert(s.wire[i]->Reply_0,s.wire[i]->Reply_1),wire:s.wire.remove(i),..s},
            Action::Duplicate(i,j)=>World {wire:s.wire.insert(j,s.wire[i]),..s},
        }
    }

    // A bound on allocated network slots and per-client sequence numbers.
    // Ordinary/background service can change the shared state and liveness.
    // Only the weak RPC endpoints own these request IDs, replies and receipts.
    pub open spec fn bounded(s:World,n:nat) -> bool {
        (forall|id:Id| #[trigger] s.issued.contains(id) ==> id.1<n)
        && (forall|id:Id| #[trigger] s.answers.contains_key(id) ==> id.1<n)
        && (forall|r:Replica,id:Id| #[trigger] (s.journal)(r).contains_key(id) ==> id.1<n)
        && forall|i:nat| #[trigger] s.wire.contains_key(i) ==> i<n && match s.wire[i] {
            Packet::Request(q)=>q.id.1<n, Packet::Reply(id,_)=>id.1<n,
        }
    }
    pub open spec fn paper_ops() -> CommandSemantics {
        |code:nat,x:int| (if code==0 {x+1} else {5*x},x)
    }
    pub open spec fn request(w:Op) -> Request {
        if w==Op::W1 {Request{id:(0,0),site:Replica::R1,method:Method::Command(0)}}
        else {Request{id:(1,0),site:Replica::R2,method:Method::Command(1)}}
    }
    pub open spec fn start() -> World {
        World {front:initial(base::engine(paper_ops())),wire:Map::empty(),issued:Set::empty(),answers:Map::empty(),
            stopped:Set::empty(),journal:|_r|Map::empty()}
    }
    pub open spec fn origin_only(s:World) -> bool {
        forall|r:Replica| {
            let log=#[trigger] (s.journal)(r);
            (log.contains_key(request(Op::W1).id) ==> r==Replica::R1)
                && (log.contains_key(request(Op::W2).id) ==> r==Replica::R2)
        }
    }
    // Both calls are outstanding before either site acts. The replies are
    // consumed by their original weak clients, never by C1 or C2.
    pub proof fn actual_overlap(b:Fork)
        ensures bounded(start(),0),({
            let f=paper_ops();let x=start();let q=request(Op::W1);let t=request(Op::W2);
            let one=step(f,x,Action::Send(0,q));let both=step(f,one,Action::Send(1,t));
            let left=step(f,both,Action::Handle(0));let right=step(f,both,Action::Handle(1));
            let lr=step(f,left,Action::Handle(1));let rl=step(f,right,Action::Handle(0));
            let got=step(f,lr,Action::Receive(0));let end=step(f,got,Action::Receive(1));
            enabled(x,Action::Send(0,q)) && enabled(one,Action::Send(1,t))
              && enabled(both,Action::Handle(0)) && enabled(both,Action::Handle(1))
              && enabled(left,Action::Handle(1)) && enabled(right,Action::Handle(0)) && lr==rl
              && enabled(lr,Action::Receive(0)) && enabled(got,Action::Receive(1))
              && end.answers.get(q.id)==Some(1) && end.answers.get(t.id)==Some(1)
              && end.wire.is_empty() && end.front==prefix(b,0)
              && origin_only(x) && origin_only(one) && origin_only(both)
              && origin_only(left) && origin_only(right) && origin_only(lr) && origin_only(rl) && origin_only(got) && origin_only(end)
              && projection((end.journal)(q.site)[q.id],Op::W1)==(crate::read_recovery::origin_records(f).records)(q.site)[0]
              && projection((end.journal)(t.site)[t.id],Op::W2)==(crate::read_recovery::origin_records(f).records)(t.site)[0]
        }),
    {
        let f=paper_ops();let x=start();let both=step(f,step(f,x,Action::Send(0,request(Op::W1))),Action::Send(1,request(Op::W2)));
        let lr=step(f,step(f,both,Action::Handle(0)),Action::Handle(1));let rl=step(f,step(f,both,Action::Handle(1)),Action::Handle(0));
        crate::facade_hybrid::weak_calls_and_issued_offers(f,b);
        assert(lr.front.base.disk =~= rl.front.base.disk && lr.front.base.disk =~= prefix(b,0).base.disk);
        assert(lr.journal =~= rl.journal);assert(lr.wire =~= rl.wire);
        assert(step(f,step(f,lr,Action::Receive(0)),Action::Receive(1)).wire =~= Map::<nat,Packet>::empty());
    }
    pub open spec fn projection(entry:Receipt,w:Op) -> Record {
        Record {op:w,returned:entry.response,installed:entry.after}
    }
    }
}
// END MODULE: weak_round

// BEGIN MODULE: independent_preparations
pub mod independent_preparations {
    use vstd::prelude::*;
    use crate::{Replica, checkpoint::*, delivery::*};
    use crate::first_assembly::{self as asm, Lanes};
    use crate::independent_read::State;
    use crate::read_call::{Event, Program};

    verus! {

    pub open spec fn offers() -> Seq<Event> {
        seq![send(0,Path::Weak,at(Replica::R1),at(Replica::R3),Wire::Copy(2)),
             send(1,Path::Weak,at(Replica::R2),at(Replica::R3),Wire::Copy(5))]
    }
    pub open spec fn before_offers<S>(m:Program<S>,l:Lanes) -> State<S> {
        let x=asm::entry(m,l);State{cfg:crate::ordinary_service::Configuration{net:local_rmw_cells(),..x.cfg},..x}
    }
    pub open spec fn after_offers<S>(m:Program<S>,l:Lanes) -> Program<S> {
        crate::protocol::LocalProtocol{initial:asm::drive(m,before_offers(m,l),offers()).cfg.private,..m}
    }
    }
}
// END MODULE: independent_preparations

// BEGIN MODULE: weak_construction
pub mod weak_construction {
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
}
// END MODULE: weak_construction

// BEGIN MODULE: weak_visibility
pub mod weak_visibility {
    // The scheduler can combine independently enabled weak sends. Which write
    // R3 can expose is determined by its actual local receive guard.
    use vstd::prelude::*;
    use crate::{Replica, checkpoint::*, delivery::*};
    use crate::async_messages::{self as net, Command, Headers};
    use crate::first_assembly as asm;
    use crate::first_splice::Observation;
    use crate::independent_read::{self as read, State};
    use crate::read_call::{Event, Program};
    use crate::weak_construction as wc;

    verus! {

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

    pub proof fn join_replica_prefix<S>(m: Program<S>, x: State<S>, s: Seq<Event>, t: Seq<Event>)
        ensures replica_prefix(m,x,s+t) == (replica_prefix(m,x,s) && replica_prefix(m,asm::drive(m,x,s),t)),
        decreases s.len(),
    {
        if s.len() == 0 { assert(s+t =~= t); } else {
            assert((s+t).drop_first() =~= s.drop_first()+t);
            join_replica_prefix(m,read::next(m,x,s[0]),s.drop_first(),t);
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

    }
}
// END MODULE: weak_visibility
