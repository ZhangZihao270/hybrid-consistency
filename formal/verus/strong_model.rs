// BEGIN MODULE: ordered_store
pub mod ordered_store {
    use vstd::prelude::*;
    use crate::Replica;

    verus! {

    // These are ordinary command invocations in the comparison SMR. Each
    // returns the old register and installs the new one. Distinct log entries
    // denote distinct invocations, including entries with the same command.
    pub enum Command { Increment, TimesFive }

    pub open spec fn majority(q: Set<Replica>) -> bool {
        (q.contains(Replica::R1) && q.contains(Replica::R2))
            || (q.contains(Replica::R1) && q.contains(Replica::R3))
            || (q.contains(Replica::R2) && q.contains(Replica::R3))
    }

    pub struct Disk {
        pub known: nat, // Available decided entries, including unapplied ones
        pub applied: nat, // Position actually installed in the shared register
        pub value: int,
    }

    pub struct LogPacket { pub from: Replica, pub to: Replica, pub entries: Seq<Command> }

    pub struct Store {
        pub log: Seq<Command>,
        pub disk: spec_fn(Replica) -> Disk,
        pub pending: Map<nat, LogPacket>,
    }

    pub open spec fn initial_store() -> Store {
        Store { log: Seq::empty(), disk: |r| Disk { known: 0, applied: 0, value: 1 }, pending: Map::empty() }
    }

    pub struct Stamp { pub version: nat, pub value: int }

    pub open spec fn sample(s: Store, r: Replica) -> Stamp {
        Stamp { version: (s.disk)(r).applied, value: (s.disk)(r).value }
    }

    }
}
// END MODULE: ordered_store

// BEGIN MODULE: stock_facade
pub mod stock_facade {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::checkpoint::all_replicas;
    use crate::metadata_stock::Rows;
    use crate::metadata_reader::reference_read;
    use crate::ordered_store::{Stamp, majority};

    verus! {

    // A wrapper of an existing strong service. Only a non-mutating read can
    // bypass the service. Commands are arbitrary application operation codes.
    // Submit is the underlying local invocation; Work retains its actual steps.
    pub enum Method { Read, Command(nat) }
    pub enum Input<E> { Idle, Submit(nat, Method), Work(E) }
    #[verifier::reject_recursive_types(X)]
    #[verifier::reject_recursive_types(E)]
    pub struct Engine<X,E> {
        pub initial: X,
        pub ready: spec_fn(X,Input<E>) -> bool,
        pub step: spec_fn(X,Input<E>) -> X,
        pub up: spec_fn(X) -> Set<Replica>,
        pub client: spec_fn(X,nat) -> bool,
        pub cell: spec_fn(X,Replica) -> int,
        pub submitted: spec_fn(X,nat) -> Option<Method>,
        pub reply: spec_fn(X,nat) -> Option<int>,
    }

    // Physical read samples and write-fence acknowledgments are immutable in
    // flight. Each (invocation, replica) has a distinct request/reply slot.
    pub enum Leg { Unsent, Request, AtServer, InFlight(Stamp), Received(Stamp) }
    pub struct Call {
        pub method: Method,
        pub legs: spec_fn(Replica) -> Leg,
        pub submitted: bool,
        pub answer: Option<int>,
    }
    pub struct State<X> {
        pub base: X,
        pub closed: Set<Replica>,
        pub calls: Map<nat,Call>,
    }
    pub enum Stage { Offer, DeliverRequest, EmitReply, DeliverReply }
    pub enum Event<E> { Idle, Invoke(nat,Method), Rpc(nat,Replica,Stage), Poll(nat), Work(E), Duplicate(nat,Replica) }

    pub open spec fn initial<X,E>(p: Engine<X,E>) -> State<X> {
        State { base: p.initial, closed: Set::empty(), calls: Map::empty() }
    }
    pub open spec fn fresh(m: Method) -> Call {
        Call { method: m, legs: |_r| Leg::Unsent, submitted: false, answer: None }
    }
    pub open spec fn rows(c: Call) -> Rows {
        Map::new(all_replicas().filter(|r: Replica| (c.legs)(r) is Received),
            |r| (c.legs)(r)->Received_0)
    }
    pub open spec fn early(c: Call) -> bool {
        c.method is Read && forall|r: Replica| #[trigger] rows(c).contains_key(r) ==> rows(c)[r].version==0
    }
    pub open spec fn delegate(c: Call) -> bool {
        !c.submitted && c.answer.is_none() && majority(rows(c).dom()) && !early(c)
    }
    pub open spec fn input<X,E>(s: State<X>, e: Event<E>) -> Input<E> {
        match e {
            Event::Work(w) => Input::Work(w),
            Event::Poll(id) if s.calls.contains_key(id) && delegate(s.calls[id]) => Input::Submit(id,s.calls[id].method),
            _ => Input::Idle,
        }
    }
    pub open spec fn rpc_enabled(c: Call,r: Replica,stage: Stage,server_up: bool,client_up: bool) -> bool {
        match stage {
            Stage::Offer => client_up && (c.legs)(r) is Unsent && !majority(rows(c).dom()),
            Stage::DeliverRequest => server_up && (c.legs)(r) is Request,
            Stage::EmitReply => server_up && (c.legs)(r) is AtServer,
            Stage::DeliverReply => client_up && (c.legs)(r) is InFlight,
        }
    }

    pub open spec fn enabled<X,E>(p: Engine<X,E>, s: State<X>, e: Event<E>) -> bool {
        (p.ready)(s.base,input(s,e)) && match e {
            Event::Invoke(id,_) => !s.calls.contains_key(id) && (p.client)(s.base,id),
            Event::Poll(id) => s.calls.contains_key(id) && s.calls[id].answer.is_none() && (p.client)(s.base,id),
            Event::Rpc(id,r,stage) => s.calls.contains_key(id)
                && rpc_enabled(s.calls[id],r,stage,(p.up)(s.base).contains(r),(p.client)(s.base,id)),
            // Duplicate deliveries use the original slot and are idempotent.
            Event::Duplicate(id,r) => s.calls.contains_key(id) && ((s.calls[id].legs)(r) is AtServer || (s.calls[id].legs)(r) is Received),
            Event::Work(_) | Event::Idle => true,
        }
    }
    pub open spec fn stamp<X,E>(p: Engine<X,E>, s: State<X>, r: Replica) -> Stamp {
        Stamp { version: if s.closed.contains(r) {1} else {0}, value: (p.cell)(s.base,r) }
    }
    pub open spec fn local_poll(c: Call, backend_reply: Option<int>) -> Call {
        if c.answer.is_some() { c }
        else if c.submitted { Call { answer: backend_reply, ..c } }
        else if !majority(rows(c).dom()) { c }
        else if early(c) { Call { answer: reference_read(Replica::R3)(rows(c)), ..c } }
        else { Call { submitted: true, ..c } }
    }
    pub open spec fn poll<X,E>(p: Engine<X,E>, s: State<X>, id: nat) -> Call {
        local_poll(s.calls[id],(p.reply)(s.base,id))
    }
    pub open spec fn advance_rpc(c: Call,r: Replica,stage: Stage,sampled: Stamp) -> Call {
        let leg=match stage {
            Stage::Offer => Leg::Request, Stage::DeliverRequest => Leg::AtServer,
            Stage::EmitReply => Leg::InFlight(sampled), Stage::DeliverReply => Leg::Received((c.legs)(r)->InFlight_0),
        };
        Call { legs: |site| if site==r {leg} else {(c.legs)(site)}, ..c }
    }
    pub open spec fn step<X,E>(p: Engine<X,E>, s: State<X>, e: Event<E>) -> State<X> {
        let base=(p.step)(s.base,input(s,e));
        // The ordinary store closes its own flag on a local application write.
        // No process observes another site's base memory to maintain this flag.
        // Each bit lives at its own replica. A local ordinary data change or
        // delivery of a command fence there closes its direct-read generation.
        let closed=s.closed.union(all_replicas().filter(|r| (p.cell)(base,r)!=(p.cell)(s.base,r)));
        let closed=match e {
            Event::Rpc(id,r,Stage::DeliverRequest) if s.calls[id].method is Command => closed.insert(r),
            _ => closed,
        };
        let calls=match e {
            Event::Invoke(id,m) => s.calls.insert(id,fresh(m)),
            Event::Rpc(id,r,stage) => s.calls.insert(id,advance_rpc(s.calls[id],r,stage,stamp(p,s,r))),
            Event::Poll(id) => s.calls.insert(id,poll(p,s,id)),
            _ => s.calls,
        };
        State { base, closed, calls }
    }

    }
}
// END MODULE: stock_facade

// BEGIN MODULE: facade_linear
pub mod facade_linear {
    use vstd::prelude::*;

    verus! {

    pub type CommandSemantics = spec_fn(nat,int)->(int,int); // new state, return value

    }
}
// END MODULE: facade_linear

// BEGIN MODULE: facade_transport
pub mod facade_transport {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::stock_facade::{Call,Method,Stage,advance_rpc,local_poll,fresh};
    use crate::checkpoint::*;
    use crate::delivery::*;
    use crate::metadata_pair::{replica_answer,signed_row};
    use crate::ordered_store::Stamp;

    verus! {

    pub enum Service { Other, Rpc(Replica,Stage,Option<Stamp>), Poll }
    pub open spec fn wire_event(p: Packet<Wire>, client: Process, sent: bool) -> Service {
        if p.from==client && invocation_packet(p) {
            Service::Rpc(p.to->At_0, if sent {Stage::Offer} else {Stage::DeliverRequest}, None)
        } else if p.to==client && (first_reply(p) || replica_answer(p)) {
            let stamp=if first_reply(p) {Stamp {version:0,value:p.input->Reply_0}} else {signed_row(p)};
            Service::Rpc(p.from->At_0, if sent {Stage::EmitReply} else {Stage::DeliverReply},Some(stamp))
        } else { Service::Other }
    }
    pub open spec fn service(n: Network<int,Wire>,a: Action<Wire>,client: Process) -> Service {
        match a {
            Action::Send(_,p)=>wire_event(p,client,true),
            Action::Deliver(id) if n.pending.contains_key(id)=>wire_event(n.pending[id],client,false),
            Action::Strong(p) if p==client =>Service::Poll, _=>Service::Other,
        }
    }
    pub open spec fn sees(n: Network<int,Wire>,r: Replica) -> Stamp { Stamp { version:0,value:(n.locals)(r) } }
    pub open spec fn run_local(n: Network<int,Wire>,ev: Service,c: Call) -> Call {
        match ev {
            Service::Rpc(r,st,_)=>advance_rpc(c,r,st,sees(n,r)), Service::Poll=>local_poll(c,None), _=>c,
        }
    }
    pub open spec fn at_time(nets: spec_fn(nat)->Network<int,Wire>,acts: spec_fn(nat)->Action<Wire>,client: Process,k: nat) -> Call
        decreases k,
    {
        if k==0 { fresh(Method::Read) } else {
            let i=(k-1) as nat; run_local(nets(i),service(nets(i),acts(i),client),at_time(nets,acts,client,i))
        }
    }
    pub open spec fn pre_net(b: Fork) -> spec_fn(nat)->Network<int,Wire> { |i|state_after(b,i) }
    pub open spec fn pre_act(b: Fork) -> spec_fn(nat)->Action<Wire> { |i: nat|actions_to_crash(b)[i as int] }
    pub open spec fn client1(b: Fork,k: nat) -> Call { at_time(pre_net(b),pre_act(b),Process::FirstClient,k) }

    }
}
// END MODULE: facade_transport

// BEGIN MODULE: ordered_round
pub mod ordered_round {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::checkpoint::all_replicas;
    use crate::ordered_store::{Stamp,majority};
    use crate::quorum_rpc::latest_site;
    use crate::stock_facade::*;
    use crate::facade_linear::CommandSemantics;

    verus! {

    // A nonempty instance of the backend contract at the atomic ordered-quorum
    // interface. Serving a command on Q is one atomic service round here.
    // Implementing that primitive by asynchronous consensus is external to this
    // instance; the wrapper proof above accepts arbitrary real backend steps.
    pub enum Work { Serve(nat,Set<Replica>), Crash(Replica), Tick(Replica), StopClient(nat) }
    pub struct Store {
        pub calls: Map<nat,Method>, pub done: Map<nat,int>, pub stopped: Set<nat>, pub live: Set<Replica>,
        pub disk: spec_fn(Replica)->Stamp,
        pub tip: Stamp, // ghost proof of the newest published ordinary state
    }
    pub open spec fn start() -> Store {
        let root=Stamp{version:0,value:1};
        Store {calls:Map::empty(),done:Map::empty(),stopped:Set::empty(),live:all_replicas(),disk:|_r|root,tip:root}
    }
    pub open spec fn current(s: Store,q: Set<Replica>) -> Replica { latest_site(Map::new(q,s.disk)) }
    pub open spec fn ready(s: Store,a: Input<Work>) -> bool {
        match a {
            Input::Idle=>true, Input::Submit(id,_)=>!s.calls.contains_key(id),
            Input::Work(Work::Tick(r))=>s.live.contains(r),
            Input::Work(Work::StopClient(id))=>!s.stopped.contains(id),
            Input::Work(Work::Crash(r))=>s.live.contains(r) && majority(s.live.remove(r)),
            Input::Work(Work::Serve(id,q))=>s.calls.contains_key(id) && !s.done.contains_key(id) && majority(q) && q.subset_of(s.live),
        }
    }
    pub open spec fn advance(f: CommandSemantics,s: Store,a: Input<Work>) -> Store {
        match a {
            Input::Submit(id,m)=>Store {calls:s.calls.insert(id,m),..s},
            Input::Work(Work::StopClient(id))=>Store{stopped:s.stopped.insert(id),..s},
            Input::Work(Work::Crash(r))=>Store {live:s.live.remove(r),..s},
            Input::Work(Work::Serve(id,q))=>{
                let d=(s.disk)(current(s,q));
                match s.calls[id] {
                    Method::Read=>Store {done:s.done.insert(id,d.value),..s},
                    Method::Command(code)=>{
                        let (new,ret)=f(code,d.value); let entry=Stamp{version:d.version+1,value:new};
                        Store {disk:|r|if q.contains(r){entry}else{(s.disk)(r)},tip:entry,done:s.done.insert(id,ret),..s}
                    },
                }
            },
            _=>s,
        }
    }
    pub open spec fn engine(f: CommandSemantics) -> Engine<Store,Work> {
        Engine {initial:start(),ready:|s,a|ready(s,a),step:|s,a|advance(f,s,a),up:|s: Store|s.live,client:|s: Store,id|!s.stopped.contains(id),
            cell:|s: Store,r|(s.disk)(r).value,submitted:|s: Store,id|s.calls.get(id),reply:|s: Store,id|s.done.get(id)}
    }

    }
}
// END MODULE: ordered_round

// BEGIN MODULE: facade_hybrid
pub mod facade_hybrid {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::checkpoint::*;
    use crate::delivery::{self,Action,Network,Process,Path};
    use crate::stock_facade::*;
    use crate::facade_linear::CommandSemantics;
    use crate::facade_transport::{Service,service,client1};
    use crate::ordered_round::{self as base,Store,Work,engine};
    use crate::ordered_store::Stamp;

    verus! {

    // There is ONE working cell per replica. Weak installations overwrite the
    // value read by the backend and front end. The backend's tip is a ghost and
    // is never a repair input. No ordinary image is stored separately here.
    pub open spec fn storage(n: Network<int,Wire>) -> Store {
        Store { disk: |r| Stamp {version:0,value:(n.locals)(r)},
            live:all_replicas().filter(|r|delivery::live(n,at(r))),
            stopped:if n.first_stopped {set![1nat]} else {Set::empty()},..base::start() }
    }
    pub open spec fn prefix(b: Fork,k: nat) -> State<Store> {
        let map=if k>=3 {Map::empty().insert(1nat,client1(b,k))} else {Map::empty()};
        State {base:storage(state_after(b,k)),closed:Set::empty(),calls:if k>=17 {map.insert(2, fresh(Method::Read))} else {map}}
    }
    pub open spec fn request(e: Service,id: nat) -> Event<Work> {
        match e {Service::Rpc(r,st,_)=>Event::Rpc(id,r,st),Service::Poll=>Event::Poll(id),_=>Event::Idle}
    }
    pub open spec fn inner(n: Network<int,Wire>,a: Action<Wire>) -> Event<Work> {
        let c=service(n,a,Process::FirstClient); let d=service(n,a,Process::SecondClient);
        if !(c is Other) {request(c,1)} else if !(d is Other) {request(d,2)} else {
            match a {
                Action::CrashR3=>Event::Work(Work::Crash(Replica::R3)), Action::StopFirstClient=>Event::Work(Work::StopClient(1)),
                Action::StartSecondClient=>Event::Invoke(2,Method::Read), Action::Strong(Process::At(r))=>Event::Work(Work::Tick(r)),
                _=>Event::Idle,
            }
        }
    }
    pub open spec fn invocation(s: State<Store>,n: Network<int,Wire>,a: Action<Wire>) -> Event<Work> {
        if !s.calls.contains_key(1) && service(n,a,Process::FirstClient) is Rpc {Event::Invoke(1,Method::Read)} else {Event::Idle}
    }
    pub open spec fn weak_part(s: State<Store>,n: Network<int,Wire>,a: Action<Wire>) -> State<Store> {
        match a {
            Action::Deliver(id) if n.pending.contains_key(id) && n.pending[id].path==Path::Weak
                && n.pending[id].to is At && n.pending[id].input is Copy =>{
                let d=s.base; let p=n.pending[id];
                State { base:Store { disk:|r| if p.to==at(r) {Stamp {value:p.input->Copy_0,..(d.disk)(r)}} else {(d.disk)(r)}, ..d },..s }
            }, _=>s
        }
    }
    pub open spec fn joint(f: CommandSemantics,n: Network<int,Wire>,a: Action<Wire>,s: State<Store>,u: State<Store>) -> bool {
        let p=engine(f); let begin=invocation(s,n,a); let middle=step(p,s,begin); let ev=inner(n,a);
        delivery::enabled(n,a) && enabled(p,s,begin) && enabled(p,middle,ev)
            && u==weak_part(step(p,middle,ev),n,a)
            && !(input(s,begin) is Submit) && !(input(middle,ev) is Submit)
    }

    // Both external weak invocations are outstanding. Each RMW reads and
    // returns the same shared cell that an ordinary RPC would sample here.
    pub open spec fn weak_rmw(s:State<Store>,site:Replica,op:crate::Op) -> (State<Store>,int) {
        let old=(s.base.disk)(site);
        let disk=|r:Replica| if r==site {Stamp {value:crate::next(op,old.value),..old}} else {(s.base.disk)(r)};
        (State {base:Store{disk,..s.base},..s},old.value)
    }
    pub open spec fn prefix_entry(f:CommandSemantics,b:Fork) -> bool {
        let s=initial(engine(f));let r1=Replica::R1;let r2=Replica::R2;let r3=Replica::R3;
        let first=weak_rmw(s,r1,crate::Op::W1);let second=weak_rmw(s,r2,crate::Op::W2);
        let ab=weak_rmw(first.0,r2,crate::Op::W2);let ba=weak_rmw(second.0,r1,crate::Op::W1);
        let n=local_rmw_cells();
        let one=send(0,Path::Weak,at(r1),at(r3),Wire::Copy((ab.0.base.disk)(r1).value));
        let two=send(1,Path::Weak,at(r2),at(r3),Wire::Copy((ab.0.base.disk)(r2).value));
        let middle=delivery::advance(|x,w|cell(x,w),n,one);
        first.1==1 && second.1==1 && ab.1==1 && ba.1==1 && ab.0==ba.0 && ab.0==prefix(b,0)
            && joint(f,n,one,ab.0,ab.0) && joint(f,middle,two,ab.0,prefix(b,0))
            && delivery::advance(|x,w|cell(x,w),middle,two)==state_after(b,0)
    }
    pub proof fn weak_calls_and_issued_offers(f:CommandSemantics,b:Fork)
        ensures prefix_entry(f,b),
    {
        origin_updates_are_actually_offered();crate::isolated_rmws();prefix_transport_is_enabled(b);
        let s=initial(engine(f));let r1=Replica::R1;let r2=Replica::R2;
        let ab=weak_rmw(weak_rmw(s,r1,crate::Op::W1).0,r2,crate::Op::W2).0;
        let ba=weak_rmw(weak_rmw(s,r2,crate::Op::W2).0,r1,crate::Op::W1).0;
        assert(ab.base.disk =~= ba.base.disk);assert(ab.base.disk =~= prefix(b,0).base.disk);
        assert(prefix(b,0).base.live =~= all_replicas());
        assert(ab==prefix(b,0) && ba==ab);
        let n=local_rmw_cells();let r3=Replica::R3;
        let one=send(0,Path::Weak,at(r1),at(r3),Wire::Copy(2));
        let two=send(1,Path::Weak,at(r2),at(r3),Wire::Copy(5));
        let middle=delivery::advance(|x,w|cell(x,w),n,one);
        assert(step(engine(f),ab,Event::Idle).closed =~= ab.closed);
        assert(step(engine(f),ab,Event::Idle)==ab);
        assert(joint(f,n,one,ab,ab));assert(joint(f,middle,two,ab,prefix(b,0)));
        assert(checkpoint_states(b)[0]==state_after(b,0) && state_after(b,0)==after_local_rmws());
        assert(delivery::advance(|x,w|cell(x,w),middle,two)==after_local_rmws());
    }

    }
}
// END MODULE: facade_hybrid

// BEGIN MODULE: quorum_rpc
pub mod quorum_rpc {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::ordered_store::*;

    verus! {

    pub type Resolver = spec_fn(Map<Replica, Stamp>) -> Option<int>;

    // A deterministic stock resolver that selects one of the actual reports.
    pub open spec fn fresher(m: Map<Replica, Stamp>, a: Replica, b: Replica) -> Replica {
        if !m.contains_key(a) || (m.contains_key(b) && m[b].version>m[a].version) { b } else { a }
    }

    pub open spec fn latest_site(m: Map<Replica, Stamp>) -> Replica {
        fresher(m, fresher(m, Replica::R1, Replica::R2), Replica::R3)
    }

    pub open spec fn latest(m: Map<Replica, Stamp>) -> Option<int> {
        if majority(m.dom()) { Some(m[latest_site(m)].value) } else { None }
    }

    }
}
// END MODULE: quorum_rpc

// BEGIN MODULE: metadata_stock
pub mod metadata_stock {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::ordered_store::*;

    verus! {

    pub type Rows = Map<Replica, Stamp>;

    }
}
// END MODULE: metadata_stock

// BEGIN MODULE: metadata_pair
pub mod metadata_pair {
    use vstd::prelude::*;
    use crate::checkpoint::*;
    use crate::delivery::*;
    use crate::ordered_store::Stamp;

    // One physical request and sampled reply per selected site. The header
    // in the *issued packet* is the number of locally applied ordinary
    // commands. C2 has no access to the sender's later state.
    verus! {

    pub open spec fn replica_answer(p: Packet<Wire>) -> bool {
        p.from is At && p.to == Process::SecondClient && p.path == Path::Strong && p.input is StampedAnswer
    }

    pub open spec fn signed_row(p: Packet<Wire>) -> Stamp {
        Stamp { value: p.input->StampedAnswer_0.value, version: p.input->StampedAnswer_1 }
    }

    }
}
// END MODULE: metadata_pair

// BEGIN MODULE: metadata_reader
pub mod metadata_reader {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::metadata_stock::*;
    use crate::ordered_store::*;
    use crate::quorum_rpc::{Resolver, latest};

    verus! {

    // A designated reference site can permit a cheaper unanimous-read check.
    // Without that site, position zero is validated against the ordinary
    // initial image. This remains an any-majority protocol on stock states.
    pub open spec fn unanimous(m: Rows) -> bool {
        forall|i: Replica,j: Replica| #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) ==> m[i].value==m[j].value
    }

    pub open spec fn valid_root(m: Rows) -> bool {
        forall|r: Replica| #[trigger] m.contains_key(r) && m[r].version==0 ==> m[r].value==sample(initial_store(),r).value
    }

    pub open spec fn root_or_reference(reference: Replica, m: Rows) -> bool {
        (m.contains_key(reference) && unanimous(m)) || valid_root(m)
    }

    pub open spec fn reference_read(reference: Replica) -> Resolver {
        |m: Rows| if root_or_reference(reference,m) { latest(m) } else { None }
    }

    }
}
// END MODULE: metadata_reader
