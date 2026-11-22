// BEGIN MODULE: sr2
pub mod sr2 {
    use vstd::prelude::*;
    use crate::Replica;
    use crate::checkpoint::*;
    use crate::delivery::*;

    verus! {

    pub open spec fn query_packet(r: Replica) -> Packet<Wire> {
        Packet { path: Path::Strong, from: Process::SecondClient, to: at(r), input: Wire::Query2 }
    }

    }
}
// END MODULE: sr2

// BEGIN MODULE: promotion_wait
pub mod promotion_wait {
    use vstd::prelude::*;

    verus! {

    // A service test for a pending operation with a fixed external workload.
    // The transition relation includes the protocol's guards and transport.
    // The designated class can be supplied by a data-installation or evidence
    // audit. The rule concerns finite opportunity, not the returned value.
    pub type Relation<S,A> = spec_fn(S,A,S)->bool;
    pub struct Path<S,A> { pub states: Seq<S>, pub actions: Seq<A> }

    pub open spec fn valid_edges<S,A>(step:Relation<S,A>,path:Path<S,A>) -> bool {
        forall|i:int| 0<=i<path.actions.len() ==> step(path.states[i],#[trigger] path.actions[i],path.states[i+1])
    }
    pub open spec fn pending_before<S,A>(done:spec_fn(S)->bool,path:Path<S,A>) -> bool {
        forall|i:int| 0<=i<path.actions.len() ==> !done(#[trigger] path.states[i])
    }
    pub open spec fn first_return<S,A>(step: Relation<S,A>, done: spec_fn(S)->bool, start:S, path:Path<S,A>) -> bool {
        path.states.len()==path.actions.len()+1 && path.states[0]==start && !done(start) && done(path.states.last())
            && valid_edges(step,path) && pending_before(done,path)
    }

    pub open spec fn uses<S,A>(path:Path<S,A>, effect:Relation<S,A>) -> bool {
        exists|i:int| 0<=i<path.actions.len() && effect(path.states[i],#[trigger] path.actions[i],path.states[i+1])
    }


    pub open spec fn can_finish<S,A>(step:Relation<S,A>,done:spec_fn(S)->bool,start:S) -> bool {
        exists|p:Path<S,A>| #[trigger] first_return(step,done,start,p)
    }

    pub open spec fn needs_class<S,A>(step:Relation<S,A>,done:spec_fn(S)->bool,start:S,effect:Relation<S,A>) -> bool {
        can_finish(step,done,start) && forall|p:Path<S,A>| #[trigger] first_return(step,done,start,p) ==> uses(p,effect)
    }

    }
}
// END MODULE: promotion_wait

// BEGIN MODULE: guarded_history
pub mod guarded_history {
    use vstd::prelude::*;
    use crate::weak_round as weak;

    verus! {

    pub open spec fn weak_end() -> weak::World {
        let f=weak::paper_ops();let one=weak::step(f,weak::start(),weak::Action::Send(0,weak::request(crate::Op::W1)));
        let both=weak::step(f,one,weak::Action::Send(1,weak::request(crate::Op::W2)));
        let left=weak::step(f,both,weak::Action::Handle(0));let right=weak::step(f,left,weak::Action::Handle(1));
        weak::step(f,weak::step(f,right,weak::Action::Receive(0)),weak::Action::Receive(1))
    }

    }
}
// END MODULE: guarded_history

// BEGIN MODULE: read_nonblocking
pub mod read_nonblocking {
    // Nonblocking service and causal waiting for an arbitrary pending operation.
    // The caller supplies a fixed workload, the actual transition relation and
    // the observer of this operation (or an ordinary protocol milestone).
    use vstd::prelude::*;
    use crate::promotion_wait::{self as wait, Path, Relation};

    verus! {

    // Predicates allow regions over unbounded queues and internal memories.
    pub type Region<S> = spec_fn(S)->bool;

    // Backward reachability using only real transitions. There is no finite
    // state bound. A different public result may be reached on every path.
    pub open spec fn within<S,A>(step:Relation<S,A>, posted:spec_fn(S)->bool, x:S, n:nat) -> bool
        decreases n,
    {
        posted(x) || (n>0 && exists|a:A,y:S| #[trigger] step(x,a,y) && within(step,posted,y,(n-1) as nat))
    }
    pub open spec fn possible<S,A>(step:Relation<S,A>, posted:spec_fn(S)->bool, x:S) -> bool {
        exists|n:nat| #[trigger] within(step,posted,x,n)
    }

    pub proof fn from_path<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,t:Path<S,A>,i:nat)
        requires t.states.len()==t.actions.len()+1,wait::valid_edges(step,t),posted(t.states.last()),i<=t.actions.len(),
        ensures within(step,posted,t.states[i as int],(t.actions.len()-i) as nat),
        decreases t.actions.len()-i,
    {
        if i<t.actions.len() {
            from_path(step,posted,t,i+1);
            assert(step(t.states[i as int],t.actions[i as int],t.states[i as int+1]));
        }
    }

    pub proof fn to_path<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,x:S,n:nat) -> (t:Path<S,A>)
        requires within(step,posted,x,n),
        ensures t.states.len()==t.actions.len()+1,t.states[0]==x,t.actions.len()<=n,
            wait::valid_edges(step,t),wait::pending_before(posted,t),posted(t.states.last()),
            !posted(x) ==> wait::first_return(step,posted,x,t),
        decreases n,
    {
        if posted(x) {Path{states:seq![x],actions:Seq::empty()}} else {
            let (a,y)=choose|a:A,y:S| #[trigger] step(x,a,y) && within(step,posted,y,(n-1) as nat);
            let rest=to_path(step,posted,y,(n-1) as nat);
            let t=Path{states:seq![x]+rest.states,actions:seq![a]+rest.actions};
            assert forall|i:int| 0<=i<t.actions.len() implies step(t.states[i],#[trigger] t.actions[i],t.states[i+1]) by {
                if i>0 {assert(step(rest.states[i-1],rest.actions[i-1],rest.states[i]));}
            }
            assert forall|i:int| 0<=i<t.actions.len() implies !posted(#[trigger] t.states[i]) by {
                if i>0 {assert(!posted(rest.states[i-1]));}
            }
            t
        }
    }
    pub proof fn first_response_iff<S,A>(step:Relation<S,A>,posted:spec_fn(S)->bool,x:S)
        ensures possible(step,posted,x)==(posted(x)||wait::can_finish(step,posted,x)),
    {
        if posted(x) {assert(within(step,posted,x,0));}
        else if possible(step,posted,x) {
            let t=to_path(step,posted,x,choose|n:nat| #[trigger] within(step,posted,x,n));
            assert(wait::first_return(step,posted,x,t));
        } else if wait::can_finish(step,posted,x) {
            let t=choose|t:Path<S,A>| #[trigger] wait::first_return(step,posted,x,t);
            from_path(step,posted,t,0);
        }
    }

    }
}
// END MODULE: read_nonblocking

// BEGIN MODULE: read_call
pub mod read_call {
    use vstd::prelude::*;
    use crate::checkpoint::*;
    use crate::delivery::*;
    use crate::protocol::*;

    verus! {

    pub type Program<S> = LocalProtocol<S,int,Wire>;
    pub type Net = Network<int,Wire>;
    pub type Event = Action<Wire>;

    }
}
// END MODULE: read_call

// BEGIN MODULE: read_issue
pub mod read_issue {
    // Independent C2's local send opportunity, before any reply. No premise
    // concerning either survivor's read/repair guard or protocol state.
    use vstd::prelude::*;
    use crate::Replica;
    use crate::checkpoint::*;
    use crate::delivery::*;
    use crate::read_call::Event;

    verus! {

    pub open spec fn send_first() -> Event { Action::Send(11,crate::sr2::query_packet(Replica::R1)) }
    pub open spec fn send_second() -> Event { Action::Send(12,crate::sr2::query_packet(Replica::R2)) }
    pub open spec fn local_event(a:Event) -> ProcessStep<int,Wire> {
        ProcessStep{actor:Process::SecondClient,action:a,incoming:None,own_local:None}
    }
    }
}
// END MODULE: read_issue

// BEGIN MODULE: independent_read
pub mod independent_read {
    // A separate, nonfaulty caller can invoke while another read is in flight.
    // The transport checks allocation. Send and delivery handlers see the chosen number.
    use vstd::prelude::*;
    use crate::{Replica, checkpoint::*, delivery::*};
    use crate::confirmation::fresh_send;
    use crate::finite_service::no_client_send;
    use crate::ordinary_service::{Configuration, allowed, apply, pending};
    use crate::promotion_wait::Relation;
    use crate::read_call::{Event, Program};
    use crate::read_nonblocking as nb;

    verus! {

    // Workload inputs name the two calls' initial fanouts. A deployed
    // protocol must actually support the fanouts used by a construction.
    pub struct Calls { pub first:Set<Replica>, pub second:Set<Replica> }

    pub struct State<S> {
        pub calls: Calls,
        pub owners: Map<nat,Process>,
        pub first_requested: Set<Replica>,
        pub cfg: Configuration<S>,
        pub reserved: Set<nat>,
        pub requested: Set<Replica>,
    }

    // C1 sends only its initial fanout. Envelopes addressed to it keep their
    // identities: consuming a reply privately cannot free a shared name for a
    // different send. Other traffic can reuse a freed unreserved slot.
    pub open spec fn retired_at_failure<S>(x:State<S>) -> Set<nat> {
        let old=x.cfg.net.pending;
        x.owners.dom().filter(|i:nat| x.owners[i]==at(Replica::R3))
            .union(old.dom().filter(|i:nat| old[i].to==at(Replica::R3)))
    }
    pub open spec fn names_sender<S>(x:State<S>,a:Event) -> bool {
        match a {
            Action::Send(id,p) => !x.owners.contains_key(id) || x.owners[id]==p.from,
            _ => true,
        }
    }
    pub open spec fn next<S>(m: Program<S>, x: State<S>, a: Event) -> State<S> {
        State { calls:x.calls, owners:x.owners, cfg: apply(m,x.cfg,a),
            first_requested: match a {
                Action::Send(_,p) if p.from==Process::FirstClient && p.path==Path::Strong
                    && p.input==Wire::Request && p.to is At => x.first_requested.insert(p.to->At_0),
                _ => x.first_requested,
            },
            reserved: match a {
                Action::CrashR3 => x.reserved.union(retired_at_failure(x)),
                Action::Send(id,p) if p.to == Process::FirstClient => x.reserved.insert(id),
                _ => x.reserved,
            },
            requested: match a {
                Action::Send(_,p) if p.from == Process::SecondClient && p.path == Path::Strong
                    && p.input == Wire::Query2 && p.to is At => x.requested.insert(p.to->At_0),
                _ => x.requested,
            },
        }
    }

    pub open spec fn initial_send<S>(x:State<S>,a:Event) -> bool {
        match a {
            Action::Send(_,p) if p.from==Process::FirstClient => p.path==Path::Strong && p.input==Wire::Request
                && p.to is At && x.calls.first.contains(p.to->At_0) && !x.first_requested.contains(p.to->At_0),
            Action::Send(_,p) if p.from==Process::SecondClient => p.path==Path::Strong && p.input==Wire::Query2
                && p.to is At && x.calls.second.contains(p.to->At_0) && !x.requested.contains(p.to->At_0),
            _ => true,
        }
    }

    // A fail-stop is an environment event. Starting this independent client has
    // no guard on C1's state. The actual local startup handler is still checked.
    pub open spec fn prefix_step<S>(m: Program<S>) -> Relation<State<S>,Event> {
        |x:State<S>,a,y| y == next(m,x,a) && initial_send(x,a) && names_sender(x,a) && fresh_send(a,x.reserved) && match a {
            Action::CrashR3 => enabled(x.cfg.net,a) && x.cfg.net.unavailable.is_none(),
            Action::StartSecondClient => !x.cfg.net.second_started &&
                (m.accept)((x.cfg.private)(Process::SecondClient),process_step(x.cfg.net,a)),
            _ => allowed(m,x.cfg,a),
        }
    }

    // The post-submission workload introduces no new client sends or failures.
    // C1 may receive, run, and stop. All actual ordinary replica work, internal
    // messages (also to C1), weak work and clock inputs remain eligible.
    pub open spec fn service_step<S>(m: Program<S>) -> Relation<State<S>,Event> {
        |x:State<S>,a,y| no_client_send(a) && a != Action::CrashR3 && a != Action::StartSecondClient
            && names_sender(x,a) && fresh_send(a,x.reserved) && allowed(m,x.cfg,a) && y == next(m,x,a)
    }

    pub open spec fn issued_to_majority<S>(x: State<S>) -> bool {
        x.cfg.net.second_started && x.first_requested==x.calls.first && x.requested==x.calls.second
            && exists|r:Replica,q:Replica| r != q
            && x.requested.contains(r) && x.requested.contains(q)
            && #[trigger] live(x.cfg.net,at(r)) && #[trigger] live(x.cfg.net,at(q))
    }

    pub open spec fn at_state<S>(x:State<S>) -> nb::Region<State<S>> { |y:State<S>| y==x }

    pub open spec fn reached<S>(m: Program<S>, entry: State<S>, x: State<S>) -> bool {
        nb::possible(prefix_step(m),at_state(x),entry)
    }

    pub open spec fn returned<S>(res: spec_fn(S)->Option<int>) -> nb::Region<State<S>> {
        |x:State<S>| !pending(x.cfg,res)
    }

    }
}
// END MODULE: independent_read

// BEGIN MODULE: fair_read
pub mod fair_read {
    use vstd::prelude::*;
    use crate::{delivery::*,progress};
    use crate::independent_read::{self as read,State};
    use crate::read_call::{Event,Net,Program};
    use crate::promotion_wait::Path;

    verus! {

    pub type Runnable = spec_fn(Net,Process)->bool;
    pub type Block<S> = Path<State<S>,Event>;
    pub struct Run<S> { pub state:spec_fn(nat)->State<S>, pub action:spec_fn(nat)->Event }
    pub open spec fn physical<S>(e:Run<S>) -> progress::Execution<int,crate::checkpoint::Wire> {
        progress::Execution{state:|i:nat|(e.state)(i).cfg.net,action:e.action}
    }
    pub open spec fn execution<S>(m:Program<S>,e:Run<S>,x:State<S>) -> bool {
        (e.state)(0)==x && forall|i:nat| read::service_step(m)((e.state)(i),#[trigger] (e.action)(i),(e.state)(i+1))
    }
    pub open spec fn fair<S>(e:Run<S>,run:Runnable) -> bool {
        progress::delivery_fair(physical(e)) && progress::process_fair(physical(e),run)
    }
    pub(crate) open spec fn initial_block<S>(e:Run<S>,k:nat) -> Block<S> {
        Path{states:Seq::new(k+1,|j:int|(e.state)(j as nat)),actions:Seq::new(k,|j:int|(e.action)(j as nat))}
    }

    }
}
// END MODULE: fair_read

// BEGIN MODULE: early_crash
pub mod early_crash {
    // A liveness probe for the direct SR1 prefixes. Only alpha and beta enter
    // the history contradiction. In the probe C1 stays live and C2 starts
    // independently. Receipt at C1 stays private. Each issued packet
    // remains queued until an actual delivery.
    use vstd::prelude::*;
    use crate::{Replica, checkpoint::*, delivery::*};
    use crate::independent_read::{self as independent, State};
    use crate::ordinary_service::Configuration;
    use crate::read_call::{Event, Program};
    use crate::read_issue::{send_first, send_second};

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
    // Two in-flight weak offers to R3. Envelope 2 belongs to R3 even in
    // executions where R3 dies before using it. No live sender needs that name.
    pub open spec fn entry<S>(m:Program<S>) -> State<S> {
        State {calls:independent::Calls{first:all_replicas(),second:live_pair()},owners:Map::empty().insert(2nat,at(Replica::R3)),first_requested:Set::empty(),
            cfg:Configuration{net:after_local_rmws(),private:m.initial},reserved:Set::empty(),requested:Set::empty()}
    }

    }
}
// END MODULE: early_crash

// BEGIN MODULE: sr1_majorities
pub mod sr1_majorities {
    use vstd::prelude::*;
    use crate::{Branch,Replica,checkpoint::*};

    verus! {

    pub open spec fn missing(b:Fork) -> Replica {
        if b.branch==Branch::Alpha {Replica::R1} else {Replica::R2}
    }

    }
}
// END MODULE: sr1_majorities

// BEGIN MODULE: first_mailbox
pub mod first_mailbox {
    // What can make an already submitted read depend on a further wire input?
    // The reference can run arbitrary real service at every live process.
    use vstd::prelude::*;
    use crate::checkpoint::*;
    use crate::delivery::*;
    use crate::fair_read::{self as fair, Run, Runnable};
    use crate::independent_read::{self as read, State};
    use crate::promotion_wait::{self as wait, Relation};
    use crate::read_call::{Event, Program};
    use crate::read_nonblocking as nb;

    verus! {

    pub open spec fn posted<S>(m:Program<S>) -> nb::Region<State<S>> {
        |x:State<S>| (m.done)((x.cfg.private)(Process::FirstClient))
    }
    // The first client remains nonfaulty until its publication. The genuine
    // protocol and the queue still guard every transition. Stops after return
    // are permitted. C1 has already sent its entire invocation.
    pub open spec fn active_step<S>(m:Program<S>) -> Relation<State<S>,Event> {
        |x,a,y| read::service_step(m)(x,a,y) && (a!=Action::StopFirstClient || posted(m)(x))
    }
    pub open spec fn submitted<S>(x:State<S>) -> bool {
        !x.cfg.net.first_stopped && x.first_requested==x.calls.first &&
            exists|r:crate::Replica,s:crate::Replica| r!=s && x.first_requested.contains(r) && x.first_requested.contains(s)
                && #[trigger] live(x.cfg.net,at(r)) && #[trigger] live(x.cfg.net,at(s))
    }
    pub open spec fn honest<S>(m:Program<S>,e:Run<S>) -> bool {
        forall|i:nat| #[trigger] (e.action)(i)==Action::<Wire>::StopFirstClient ==> posted(m)((e.state)(i))
    }
    pub open spec fn fair_opportunity<S>(m:Program<S>,run:Runnable,x:State<S>) -> bool {
        exists|e:Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && honest(m,e)
    }
    // Scope may be the reachable configurations of this workload. This is the
    // positive hybrid progress assumption, separately from existence of a fair run.
    pub open spec fn first_availability<S>(m:Program<S>,run:Runnable,scope:nb::Region<State<S>>) -> bool {
        forall|x:State<S>,e:Run<S>| scope(x) && submitted(x) && #[trigger] fair::execution(m,e,x)
            && fair::fair(e,run) && honest(m,e) ==> exists|i:nat| #[trigger] posted(m)((e.state)(i))
    }
    pub proof fn fair_first_service<S>(m:Program<S>,run:Runnable,scope:nb::Region<State<S>>,x:State<S>)
        requires scope(x),submitted(x),first_availability(m,run,scope),fair_opportunity(m,run,x),
        ensures nb::possible(active_step(m),posted(m),x),
    {
        let e=choose|e:Run<S>| #[trigger] fair::execution(m,e,x) && fair::fair(e,run) && honest(m,e);
        let k=choose|i:nat| #[trigger] posted(m)((e.state)(i));
        let p=wait::Path{states:Seq::new(k+1,|j:int|(e.state)(j as nat)),actions:Seq::new(k,|j:int|(e.action)(j as nat))};
        assert forall|j:int| 0<=j<k implies active_step(m)(p.states[j],#[trigger] p.actions[j],p.states[j+1]) by {
            assert(read::service_step(m)((e.state)(j as nat),(e.action)(j as nat),(e.state)(j as nat+1)));
        }
        nb::from_path(active_step(m),posted(m),p,0);
    }
    }
}
// END MODULE: first_mailbox

// BEGIN MODULE: first_schedule
pub mod first_schedule {
    use vstd::prelude::*;
    use crate::delivery::*;
    use crate::read_call::Program;
    use crate::read_issue as issue;

    verus! {

    pub open spec fn startup<S>(m:Program<S>) -> bool {
        (m.accept)((m.initial)(Process::SecondClient),issue::local_event(Action::StartSecondClient))
    }

    }
}
// END MODULE: first_schedule

// BEGIN MODULE: first_splice
pub mod first_splice {
    // Finite local histories from an actual first-call execution. A transcript
    // includes the actual envelope consumed and the cell read by its handler.
    use vstd::prelude::*;
    use crate::{checkpoint::*, delivery::*};
    use crate::first_mailbox as mail;
    use crate::independent_read::{self as read, State};
    use crate::promotion_wait as wait;
    use crate::read_call::{Event,Program};

    verus! {

    pub type Observation = ProcessStep<int,Wire>;
    pub type Tape = Seq<Observation>;

    pub open spec fn slot(a:Event) -> Option<nat> {
        match a {Action::Send(i,_)|Action::Deliver(i)=>Some(i), _=>None}
    }
    pub open spec fn moves(a:Event) -> bool {
        a!=Action::CrashR3 && a!=Action::StartSecondClient && a!=Action::StopFirstClient
    }
    pub open spec fn after<S>(m:Program<S>,x:State<S>,t:Tape) -> State<S>
        decreases t.len(),
    {
        if t.len()==0 {x} else {after(m,read::next(m,x,t[0].action),t.drop_first())}
    }
    pub open spec fn plays<S>(m:Program<S>,x:State<S>,t:Tape) -> bool
        decreases t.len(),
    {
        if t.len()==0 {true} else {
            let e=t[0];let y=read::next(m,x,e.action);
            moves(e.action) && read::service_step(m)(x,e.action,y) && process_step(x.cfg.net,e.action)==e
                && plays(m,y,t.drop_first())
        }
    }
    pub open spec fn record<S>(p:wait::Path<State<S>,Event>,j:nat) -> Tape {
        Seq::new((p.actions.len()-j) as nat,|i:int|process_step(p.states[j+i].cfg.net,p.actions[j+i]))
    }
    pub proof fn recorded<S>(m:Program<S>,p:wait::Path<State<S>,Event>,j:nat)
        requires j<=p.actions.len(),p.states.len()==p.actions.len()+1,
            wait::valid_edges(mail::active_step(m),p),wait::pending_before(mail::posted(m),p),
        ensures plays(m,p.states[j as int],record(p,j)),after(m,p.states[j as int],record(p,j))==p.states.last(),
        decreases p.actions.len()-j,
    {
        if j<p.actions.len() {
            let a=p.actions[j as int];let x=p.states[j as int];let y=p.states[j as int+1];
            assert(mail::active_step(m)(x,a,y));assert(!mail::posted(m)(x));
            recorded(m,p,j+1);assert(record(p,j).drop_first() =~= record(p,j+1));
        }
    }
    }
}
// END MODULE: first_splice

// BEGIN MODULE: first_assembly
pub mod first_assembly {
    // Assemble the two majority executions from the histories of the processes
    // that actually served them. The auxiliary caller never observes C1.
    use vstd::prelude::*;
    use crate::{Replica,checkpoint::*,delivery::*};
    use crate::early_crash as probe;
    use crate::first_mailbox as mail;
    use crate::first_splice::{Observation,Tape,after,plays};
    use crate::independent_read::{self as read,State};
    use crate::promotion_wait as wait;
    use crate::read_call::{Event,Program};

    verus! {

    pub type Lanes = Map<nat,Replica>;
    pub type Service<S> = wait::Path<State<S>,Event>;
    pub open spec fn owners(l:Lanes) -> Map<nat,Process> {
        Map::new(l.dom().filter(|i:nat| l[i]==Replica::R3),|_i:nat|at(Replica::R3))
    }
    pub open spec fn entry<S>(m:Program<S>,l:Lanes) -> State<S> { State{owners:owners(l),..probe::entry(m)} }

    // The physical prefix monitor is shared with the service-loss proof.
    // Stopping a caller after its recorded return is an environment action.
    pub open spec fn drive<S>(m:Program<S>,x:State<S>,a:Seq<Event>) -> State<S>
        decreases a.len(),
    {
        if a.len()==0 {x} else {drive(m,read::next(m,x,a[0]),a.drop_first())}
    }
    pub open spec fn prefix<S>(m:Program<S>,x:State<S>,a:Seq<Event>,original:bool) -> bool
        decreases a.len(),
    {
        if a.len()==0 {true} else {
            let e=a[0];let y=read::next(m,x,e);
            (if original && e==Action::StopFirstClient {enabled(x.cfg.net,e) && mail::posted(m)(x)}
                else {read::prefix_step(m)(x,e,y)}) && prefix(m,y,a.drop_first(),original)
        }
    }
    pub open spec fn actions(t:Tape) -> Seq<Event> { t.map_values(|e:Observation|e.action) }
    pub proof fn prefix_concat<S>(m:Program<S>,x:State<S>,a:Seq<Event>,b:Seq<Event>,o:bool)
        ensures prefix(m,x,a+b,o)==(prefix(m,x,a,o) && prefix(m,drive(m,x,a),b,o)),
            drive(m,x,a+b)==drive(m,drive(m,x,a),b),
        decreases a.len(),
    {
        if a.len()==0 {assert(a+b =~= b);} else {
            assert((a+b).drop_first() =~= a.drop_first()+b);prefix_concat(m,read::next(m,x,a[0]),a.drop_first(),b,o);
        }
    }
    pub proof fn native_prefix<S>(m:Program<S>,x:State<S>,t:Tape,o:bool)
        requires plays(m,x,t),
        ensures prefix(m,x,actions(t),o),drive(m,x,actions(t))==after(m,x,t),
        decreases t.len(),
    {
        if t.len()>0 {
            assert(actions(t).drop_first() =~= actions(t.drop_first()));
            native_prefix(m,read::next(m,x,t[0].action),t.drop_first(),o);
        }
    }
    pub open spec fn boot(b:Option<Fork>) -> Seq<Event> {
        match b {Some(f)=>actions_to_crash(f).take(5),None=>probe::actions().take(3)}
    }

    }
}
// END MODULE: first_assembly

// BEGIN MODULE: hybrid_majority
pub mod hybrid_majority {
    // The author's A applies to both stock and hybrid operations. These are its
    // read clauses as used by the monitored workload, with explicit fair runs.
    use vstd::prelude::*;
    use crate::{Replica,checkpoint::*,delivery::*};
    use crate::first_assembly::*;
    use crate::first_mailbox as mail;
    use crate::independent_read::{self as read,State};
    use crate::promotion_wait as wait;
    use crate::read_call::{Event,Program,Net};
    use crate::read_nonblocking as nb;

    verus! {

    pub enum Caller { First, Second }
    pub open spec fn due<S>(c:Caller,x:State<S>) -> bool {
        match c {Caller::First=>mail::submitted(x),Caller::Second=>read::issued_to_majority(x)}
    }
    pub open spec fn published<S>(c:Caller,m:Program<S>,res:spec_fn(S)->Option<int>) -> nb::Region<State<S>> {
        match c {Caller::First=>mail::posted(m),Caller::Second=>read::returned(res)}
    }
    pub open spec fn service<S>(c:Caller,m:Program<S>) -> wait::Relation<State<S>,Event> {
        match c {Caller::First=>mail::active_step(m),Caller::Second=>read::service_step(m)}
    }
    pub open spec fn value<S>(c:Caller,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,x:State<S>) -> int {
        match c {Caller::First=>first((x.cfg.private)(Process::FirstClient)),
            Caller::Second=>res((x.cfg.private)(Process::SecondClient)).unwrap()}
    }
    pub open spec fn sole(n:Net,q:Set<Replica>) -> bool {
        q.len()==2 && forall|r:Replica| #[trigger] q.contains(r)==live(n,at(r))
    }
    pub open spec fn fresh_invocation<S>(c:Caller,x:State<S>,a:Event) -> bool {
        match a {
            Action::Send(_,p)=>p.path==Path::Strong && p.to is At && match c {
                Caller::First=>p.from==Process::FirstClient && p.input==Wire::Request && x.first_requested.is_empty(),
                Caller::Second=>p.from==Process::SecondClient && p.input==Wire::Query2 && x.requested.is_empty() && x.cfg.net.second_started,
            },_=>false,
        }
    }
    // Both halves are native traces. The head includes the initial sends.
    // Exactly Q is live at invocation and return, in a crash-stop network.
    pub open spec fn served<S>(c:Caller,m:Program<S>,res:spec_fn(S)->Option<int>,h:Service<S>,t:Service<S>,q:Set<Replica>) -> bool {
        let d=published(c,m,res);
        h.actions.len()>0 && h.states.len()==h.actions.len()+1 && wait::valid_edges(read::prefix_step(m),h)
            && fresh_invocation(c,h.states[0],h.actions[0]) && wait::pending_before(d,h) && due(c,h.states.last())
            && wait::first_return(service(c,m),d,h.states.last(),t)
            && sole(h.states[0].cfg.net,q) && sole(t.states.last().cfg.net,q)
    }
    pub open spec fn held<S>(states:Seq<State<S>>,q:Set<Replica>,v:int) -> bool {
        exists|i:int,r:Replica| 0<=i<states.len() && q.contains(r) && #[trigger] (states[i].cfg.net.locals)(r)==v
    }

    // Sampling from invocation includes a first publication on a request send.
    // Both endpoints have the same sole live quorum in this crash-stop model.
    pub open spec fn first_invocation_interval<S>(m:Program<S>,p:Service<S>,q:Set<Replica>) -> bool {
        p.actions.len()>0 && wait::first_return(read::prefix_step(m),mail::posted(m),p.states[0],p)
            && fresh_invocation(Caller::First,p.states[0],p.actions[0]) && !p.states.last().cfg.net.first_stopped
            && sole(p.states[0].cfg.net,q) && sole(p.states.last().cfg.net,q)
    }

    pub open spec fn first_invocation_sampling<S>(m:Program<S>,first:spec_fn(S)->int,base:State<S>) -> bool {
        forall|p:Service<S>,q:Set<Replica>| #[trigger] first_invocation_interval(m,p,q) && read::reached(m,base,p.states[0])
            ==> held(p.states,q,first((p.states.last().cfg.private)(Process::FirstClient)))
    }

    pub open spec fn submitted_first_sampling<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,base:State<S>) -> bool {
        forall|h:Service<S>,t:Service<S>,q:Set<Replica>| #[trigger] served(Caller::First,m,res,h,t,q)
            && read::reached(m,base,h.states[0]) && !t.states.last().cfg.net.first_stopped ==> {
                let v=value(Caller::First,first,res,t.states.last()); held(h.states,q,v) || held(t.states,q,v)
            }
    }

    pub proof fn invocation_includes_submitted_sampling<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,base:State<S>)
        requires first_invocation_sampling(m,first,base),
        ensures submitted_first_sampling(m,first,res,base),
    {
        let c=Caller::First;
        assert forall|h:Service<S>,t:Service<S>,q:Set<Replica>| #[trigger] served(c,m,res,h,t,q)
            && read::reached(m,base,h.states[0]) && !t.states.last().cfg.net.first_stopped implies {
                let v=value(c,first,res,t.states.last()); held(h.states,q,v) || held(t.states,q,v)
            } by {
            let n=h.actions.len(); let p=wait::Path { states:h.states.drop_last()+t.states,actions:h.actions+t.actions };
            let d=published(c,m,res);
            assert forall|i:int| 0<=i<p.actions.len() implies read::prefix_step(m)(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
                if i<n { assert(read::prefix_step(m)(h.states[i],h.actions[i],h.states[i+1])); }
                else { let j=i-n; assert(service(c,m)(t.states[j],t.actions[j],t.states[j+1]));
                    assert(read::initial_send(t.states[j],t.actions[j])); }
            }
            assert forall|i:int| 0<=i<p.actions.len() implies !d(#[trigger] p.states[i]) by {
                if i<n { assert(!d(h.states[i])); } else { assert(!d(t.states[i-n])); }
            }
            assert(first_invocation_interval(m,p,q));
            let v=value(c,first,res,t.states.last()); assert(held(p.states,q,v));
            let (j,r)=choose|j:int,r:Replica| 0<=j<p.states.len() && q.contains(r) && #[trigger] (p.states[j].cfg.net.locals)(r)==v;
            if j<n { assert((h.states[j].cfg.net.locals)(r)==v); } else { assert((t.states[j-n].cfg.net.locals)(r)==v); }
        }
    }

    }
}
// END MODULE: hybrid_majority

// BEGIN MODULE: read_recovery
pub mod read_recovery {
    use vstd::prelude::*;
    use crate::{Op,Replica};
    use crate::facade_linear::CommandSemantics;
    use crate::facade_hybrid::weak_rmw;
    use crate::ordered_round::{self as engine,Store};
    use crate::stock_facade::{State,initial};

    verus! {

    // An alternative local recovery service with actual retained RMW records.
    // The journal is per site. Keeping a record says nothing about its total-
    // order position or its inclusion in another site's strong history.
    pub struct Record { pub op:Op,pub returned:int,pub installed:int }
    pub type Journals = spec_fn(Replica)->Seq<Record>;
    pub struct Storage { pub core:State<Store>,pub records:Journals }

    pub open spec fn save_call(s:Storage,site:Replica,w:Op) -> Storage {
        let (post,old)=weak_rmw(s.core,site,w);
        let record=Record {op:w,returned:old,installed:(post.base.disk)(site).value};
        Storage {core:post,records:|r|if r==site {(s.records)(r).push(record)} else {(s.records)(r)}}
    }
    pub open spec fn origin_records(f:CommandSemantics) -> Storage {
        let start=Storage {core:initial(engine::engine(f)),records:|_site|Seq::empty()};
        save_call(save_call(start,Replica::R1,Op::W1),Replica::R2,Op::W2)
    }
    }
}
// END MODULE: read_recovery

// BEGIN MODULE: ordinary_service
pub mod ordinary_service {
    use vstd::prelude::*;
    use crate::checkpoint::*;
    use crate::delivery::*;
    use crate::protocol::*;

    verus! {

    pub struct Configuration<S> {
        pub net: Network<int,Wire>,
        pub private: spec_fn(Process)->S,
    }
    pub open spec fn allowed<S>(m: LocalProtocol<S,int,Wire>,s: Configuration<S>,a: Action<Wire>) -> bool {
        let ev=process_step(s.net,a);
        enabled(s.net,a) && (m.accept)((s.private)(ev.actor),ev)
    }
    pub open spec fn apply<S>(m: LocalProtocol<S,int,Wire>,s: Configuration<S>,a: Action<Wire>) -> Configuration<S> {
        let ev=process_step(s.net,a);
        Configuration {net:advance(|x,w|cell(x,w),s.net,a),
            private:|p| if p==ev.actor {(m.update)((s.private)(p),ev)} else {(s.private)(p)} }
    }
    pub open spec fn pending<S>(s: Configuration<S>,result: spec_fn(S)->Option<int>) -> bool {
        result((s.private)(Process::SecondClient)).is_none()
    }

    }
}
// END MODULE: ordinary_service

// BEGIN MODULE: finite_service
pub mod finite_service {
    use vstd::prelude::*;
    use crate::delivery::*;
    use crate::checkpoint::*;

    verus! {

    // Once both queries have gone out, clocks and other private inputs also
    // preserve the invocation. Only another client send needs scrutiny here.
    pub open spec fn no_client_send(event:Action<Wire>) -> bool {
        match event { Action::Send(_,p) => p.from is At, _ => true }
    }

    }
}
// END MODULE: finite_service

// BEGIN MODULE: prepared_service
pub mod prepared_service {
    // Strong service at real weak-prefix endpoints. The sole-majority reference
    // changes only availability. Its whole queue and all handler memories survive.
    use vstd::prelude::*;
    use crate::{Replica,checkpoint::*,delivery::*};
    use crate::async_messages::{self as net,Headers,Command,Message};
    use crate::first_assembly::{self as asm,Service};
    use crate::first_mailbox as mail;
    use crate::hybrid_majority as maj;
    use crate::independent_read::{self as read,State};
    use crate::native_fork as fork;
    use crate::original_application as app;
    use crate::promotion_wait as wait;
    use crate::read_call::{Program,Event};
    use crate::read_nonblocking as nb;
    use crate::fair_read as fair;
    use crate::weak_construction as wc;
    use crate::weak_visibility as vis;

    verus! {

    pub struct Exposure { pub arm:Fork, pub events:Seq<Event> }

    pub open spec fn weak_trace(e:Exposure) -> Seq<Event> {
        e.events
    }

    pub open spec fn exposed<S>(p:Program<S>,k:Headers,e:Exposure) -> bool {
        let m=net::implementation(k,p);
        let z=endpoint(p,k,e);
        vis::replica_prefix(m,wc::start(m),weak_trace(e)) && survivor(z.cfg.net)==(2int,5int)
            && (z.cfg.net.locals)(Replica::R3)==first_value(e.arm)
    }

    pub open spec fn endpoint<S>(p:Program<S>,k:Headers,e:Exposure) -> State<S> {
        let m=net::implementation(k,p); asm::drive(m,wc::start(m),weak_trace(e))
    }

    pub open spec fn ordinary<S>(x:State<S>) -> Map<nat,Packet<Wire>> {
        let q=x.cfg.net.pending; q.restrict(q.dom().filter(|i:nat| q[i].path!=Path::Weak))
    }

    pub open spec fn replica_weak<S>(x:State<S>) -> bool {
        let w=fork::weak_packets(x);
        forall|h:nat| w.contains_key(h) ==> (#[trigger] w[h]).to is At
    }

    pub open spec fn idle<S>(m:Program<S>,x:State<S>) -> bool {
        x.calls.first==all_replicas() && x.calls.second==live_pair()
            && x.first_requested.is_empty() && x.requested.is_empty()
            && !x.cfg.net.first_stopped && !x.cfg.net.second_started && !x.cfg.net.r3_crashed && x.cfg.net.unavailable.is_none()
            && (x.cfg.private)(Process::FirstClient)==(m.initial)(Process::FirstClient)
            && (x.cfg.private)(Process::SecondClient)==(m.initial)(Process::SecondClient)
    }

    pub(crate) proof fn replica_frame<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
        requires vis::replica_prefix(m,x,s),idle(m,x),replica_weak(x),
        ensures asm::prefix(m,x,s,true),idle(m,asm::drive(m,x,s)),replica_weak(asm::drive(m,x,s)),
        decreases s.len(),
    {
        if s.len()>0 {
            let a=s[0];
            let y=read::next(m,x,a);
            assert(vis::replica_input(process_step(x.cfg.net,a)));
            assert(process_step(x.cfg.net,a).actor is At);
            assert forall|h:nat| fork::weak_packets(y).contains_key(h) implies (#[trigger] fork::weak_packets(y)[h]).to is At by {
                if !(a is Send && a->Send_0==h) {assert(fork::weak_packets(x).get(h)==Some(fork::weak_packets(y)[h]));}
            }
            replica_frame(m,y,s.drop_first());
        }
    }

    // Strong service can also start after a guarded application of a buffered
    // weak receipt. The older receipt-only exposure keeps its original meaning.
    pub open spec fn service_entry<S>(p:Program<S>,k:Headers,e:Exposure) -> bool {
        exposed(p,k,e) || exists|c:crate::async_weak::Install<S>| #[trigger] crate::async_weak::installation(p,k,e,c)
    }

    pub proof fn weak_endpoint<S>(p:Program<S>,k:Headers,e:Exposure)
        requires service_entry(p,k,e),
        ensures ({
            let m=net::implementation(k,p); let x=wc::start(m); let z=endpoint(p,k,e);
            asm::prefix(m,x,weak_trace(e),true) && idle(m,z) && replica_weak(z)
                && survivor(z.cfg.net)==(2int,5int) && (z.cfg.net.locals)(Replica::R3)==first_value(e.arm)
        }),
    {
        let m=net::implementation(k,p);
        if exposed(p,k,e) {
            replica_frame(m,wc::start(m),weak_trace(e));
        } else {
            let c=choose|c:crate::async_weak::Install<S>| #[trigger] crate::async_weak::installation(p,k,e,c);
            crate::async_weak::installation_frame(p,k,e,c);
        }
    }

    // The reference models one failure of the omitted replica after this
    // weak prefix, before invocation. No pending occurrence is retracted.
    pub open spec fn lost<S>(x:State<S>,r:Replica) -> State<S> {
        State {cfg:crate::ordinary_service::Configuration {net:crate::read_call::Net {
            unavailable:Some(r),..x.cfg.net},..x.cfg},..x}
    }
    pub open spec fn reference<S>(x:State<S>,b:Fork) -> State<S> { lost(x,crate::sr1_majorities::missing(b)) }

    // The native alphabet has CrashR3. For references the environment can
    // instead stop R1 or R2 once, at a reached cut. Only its availability bit
    // changes. Native CrashR3 is disabled with this bit set.
    pub type Route = (Seq<Event>,Option<Replica>,Seq<Event>);
    pub open spec fn reaches<S>(m:Program<S>,base:State<S>,route:Route,x:State<S>) -> bool {
        let y=asm::drive(m,base,route.0);
        let z=if route.1.is_some() {lost(y,route.1.unwrap())} else {y};
        asm::prefix(m,base,route.0,true)
            && (route.1.is_some() ==> route.1.unwrap()!=Replica::R3 && y.cfg.net.unavailable.is_none() && !y.cfg.net.r3_crashed)
            && asm::prefix(m,z,route.2,true) && asm::drive(m,z,route.2)==x
    }
    pub open spec fn reachable<S>(m:Program<S>,base:State<S>,x:State<S>) -> bool {
        exists|t:Route| #[trigger] reaches(m,base,t,x)
    }

    pub type Requests = Seq<(Replica,nat)>;
    pub open spec fn packet(r:Replica) -> Packet<Wire> {
        Packet {from:Process::FirstClient,to:at(r),path:Path::Strong,input:Wire::Request}
    }
    pub open spec fn request(a:Event) -> bool {
        a is Send && a->Send_1.to is At && a->Send_1==packet(a->Send_1.to->At_0)
    }
    pub open spec fn input(r:Replica,id:nat) -> crate::first_splice::Observation {
        process_step(local_rmw_cells(),Action::Send(id,packet(r)))
    }
    pub open spec fn supported<S>(p:Program<S>,z:S,plan:Requests) -> bool
        decreases plan.len(),
    {
        if plan.len()==0 || (p.done)(z) {true} else {
            let e=input(plan[0].0,plan[0].1);
            (p.accept)(z,e) && supported(p,(p.update)(z,e),plan.drop_first())
        }
    }
    pub open spec fn recipients(t:Requests) -> Seq<Replica> { t.map_values(|v:(Replica,nat)|v.0) }

    pub open spec fn fan<S>(m:Program<S>,x:State<S>,s:Seq<Event>) -> bool
        decreases s.len(),
    {
        if s.len()==0 {true} else {
            let a=s[0]; let y=read::next(m,x,a);
            !mail::posted(m)(x) && request(a) && read::prefix_step(m)(x,a,y) && fan(m,y,s.drop_first())
        }
    }

    pub open spec fn contents(k:Headers,s:Seq<Event>) -> Requests {
        s.map_values(|a:Event| (a->Send_1.to->At_0,net::message(k,a->Send_0,a->Send_1).id))
    }

    // Select fresh queue handles on both real cuts. Equal application IDs can
    // occur in different requests. Stop immediately if C1 publishes.
    pub(crate) proof fn emit<S>(p:Program<S>,k:Headers,x:State<S>,y:State<S>,t:Requests) -> (s:Seq<Event>)
        requires x.calls.first==all_replicas(),y.calls.first==all_replicas(),
            !x.cfg.net.first_stopped,!y.cfg.net.first_stopped,x.first_requested==y.first_requested,
            (x.cfg.private)(Process::FirstClient)==(y.cfg.private)(Process::FirstClient),
            supported(p,(x.cfg.private)(Process::FirstClient),t),recipients(t).no_duplicates(),
            x.first_requested.disjoint(recipients(t).to_set()),
        ensures ({
            let m=net::implementation(k,p); let u=asm::drive(m,x,s); let v=asm::drive(m,y,s);
            fan(m,x,s) && fan(m,y,s) && (u.cfg.private)(Process::FirstClient)==(v.cfg.private)(Process::FirstClient)
                && u.first_requested==v.first_requested
                && s.len()<=t.len() && contents(k,s)==t.take(s.len() as int)
                && (!mail::posted(m)(u) ==> contents(k,s)==t && u.first_requested==x.first_requested.union(recipients(t).to_set()))
        }),
        decreases t.len(),
    {
        let m=net::implementation(k,p); let c=Process::FirstClient;
        if t.len()==0 || mail::posted(m)(x) {
            if t.len()==0 { assert(recipients(t).to_set() =~= Set::empty()); }
            assert(contents(k,seq![]) =~= t.take(0));
            seq![]
        } else {
            let r=t[0].0; let msg=Message {id:t[0].1,body:packet(r)}; let cmd=Command::Send(msg);
            let tail=t.drop_first(); let rs=recipients(t); let rt=recipients(tail);
            assert(rs[0]==r && rs.contains(r)); assert(rt =~= rs.drop_first());
            assert(rs.to_set() =~= rt.to_set().insert(r)) by {assert(rs =~= seq![r]+rt);}
            assert(!rt.contains(r));
            let avoid=y.cfg.net.pending.dom().union(y.reserved).union(y.owners.dom());
            assert(net::ready(p,k,x,cmd,false) && net::ready(p,k,y,cmd,false));
            let a=net::realize_step(p,k,x,cmd,false,avoid);
            assert(net::allocatable(y,a)); net::project_step(p,k,y,a,false);
            let u=read::next(m,x,a); let v=read::next(m,y,a);
            assert(u.first_requested.disjoint(rt.to_set()));
            let rest=emit(p,k,u,v,tail); let s=seq![a]+rest; assert(s.drop_first() =~= rest);
            assert(contents(k,s) =~= seq![t[0]]+contents(k,rest)) by {
                assert forall|i:int| 0<=i<s.len() implies #[trigger] contents(k,s)[i]==(seq![t[0]]+contents(k,rest))[i] by {
                    if i>0 {assert(s[i]==rest[i-1]);}
                }
            }
            assert(seq![t[0]]+tail.take(rest.len() as int) =~= t.take(s.len() as int));
            assert(u.first_requested.union(rt.to_set()) =~= x.first_requested.union(rs.to_set()));
            s
        }
    }

    pub open spec fn path<S>(m:Program<S>,x:State<S>,s:Seq<Event>) -> Service<S> {
        wait::Path { states:fork::states(m,x,s), actions:s }
    }

    pub proof fn index_step<S>(m:Program<S>,x:State<S>,s:Seq<Event>,i:int)
        requires 0<=i<s.len(),
        ensures fork::states(m,x,s)[i+1]==read::next(m,fork::states(m,x,s)[i],s[i]),
    {
        let head=s.take(i);let a=seq![s[i]];assert(head+a =~= s.take(i+1));asm::prefix_concat(m,x,head,a,true);
        reveal_with_fuel(asm::drive,2);
    }

    pub proof fn endpoints<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
        ensures path(m,x,s).states[0]==x, path(m,x,s).states.last()==asm::drive(m,x,s),
    {
        assert(s.take(0) =~= seq![] && s.take(s.len() as int) =~= s);
    }

    pub(crate) proof fn fan_at<S>(m:Program<S>,x:State<S>,s:Seq<Event>,i:nat)
        requires fan(m,x,s),i<=s.len(),
        ensures ({
            let q=fork::states(m,x,s)[i as int];
            q.cfg.net==crate::read_call::Net{pending:q.cfg.net.pending,..x.cfg.net}
                && q.calls==x.calls && q.requested==x.requested
                && (forall|c:Process| c!=Process::FirstClient ==> (#[trigger] (q.cfg.private)(c))==(x.cfg.private)(c))
                && fork::weak_packets(q)==fork::weak_packets(x)
                && (i<s.len() ==> !mail::posted(m)(q) && request(s[i as int])
                    && read::prefix_step(m)(q,s[i as int],fork::states(m,x,s)[i as int+1]))
        }),
        decreases i,
    {
        if i==0 {endpoints(m,x,s); if s.len()>0 {index_step(m,x,s,0);}}
        else {
            let y=read::next(m,x,s[0]); let tail=s.drop_first(); let j=(i-1) as nat;
            assert(request(s[0])); assert(y.cfg.net.locals =~= x.cfg.net.locals);
            assert(fork::weak_packets(y) =~= fork::weak_packets(x));
            assert(s.take(i as int) =~= seq![s[0]]+tail.take(j as int));
            asm::prefix_concat(m,x,seq![s[0]],tail.take(j as int),true);
            assert(asm::drive(m,x,seq![s[0]])==y) by {reveal_with_fuel(asm::drive,2);}
            if i<s.len() {index_step(m,x,s,i as int);index_step(m,y,tail,j as int);assert(tail[j as int]==s[i as int]);}
            fan_at(m,y,tail,j);
        }
    }
    pub(crate) proof fn fan_path<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
        requires fan(m,x,s),
        ensures wait::valid_edges(read::prefix_step(m),path(m,x,s)),wait::pending_before(mail::posted(m),path(m,x,s)),
    {
        let h=path(m,x,s);
        assert forall|i:int| 0<=i<s.len() implies read::prefix_step(m)(h.states[i],#[trigger] h.actions[i],h.states[i+1])
            by {fan_at(m,x,s,i as nat);}
        assert forall|i:int| 0<=i<s.len() implies !mail::posted(m)(#[trigger] h.states[i]) by {fan_at(m,x,s,i as nat);}
    }

    proof fn early_value<S>(m:Program<S>,first:spec_fn(S)->int,x:State<S>,b:Fork,s:Seq<Event>)
        requires fan(m,x,s), x.first_requested.is_empty(), !mail::posted(m)(x),mail::posted(m)(asm::drive(m,x,s)),
            maj::sole(x.cfg.net,crate::first_quorum(b.branch)),!x.cfg.net.first_stopped,
            forall|r:Replica| crate::first_quorum(b.branch).contains(r) ==> (#[trigger] (x.cfg.net.locals)(r))==first_value(b),
            maj::first_invocation_sampling(m,first,x),
        ensures first((asm::drive(m,x,s).cfg.private)(Process::FirstClient))==first_value(b),
    {
        let h=path(m,x,s); let q=crate::first_quorum(b.branch); endpoints(m,x,s);
        assert(s.len()>0);fan_at(m,x,s,0);fan_at(m,x,s,s.len());
        assert forall|i:int| 0<=i<s.len() implies read::prefix_step(m)(h.states[i],#[trigger] s[i],h.states[i+1])
            && !mail::posted(m)(h.states[i]) by {fan_at(m,x,s,i as nat);}
        fan_path(m,x,s);assert(maj::fresh_invocation(maj::Caller::First,x,s[0]));
        assert(wait::first_return(read::prefix_step(m),mail::posted(m),x,h));
        assert forall|r:Replica| #[trigger] q.contains(r)==live(h.states.last().cfg.net,at(r)) by {
            assert(q.contains(r)==live(x.cfg.net,at(r)));
        }
        assert(maj::first_invocation_interval(m,h,q)); assert(nb::within(read::prefix_step(m),read::at_state(x),x,0));
        let v=first((h.states.last().cfg.private)(Process::FirstClient));
        let (j,r)=choose|j:int,r:Replica| 0<=j<h.states.len() && q.contains(r) && #[trigger] (h.states[j].cfg.net.locals)(r)==v;
        fan_at(m,x,s,j as nat);
    }

    pub open spec fn service_laws<S>(m:Program<S>,first:spec_fn(S)->int,x:State<S>,run:fair::Runnable) -> bool {
        maj::first_invocation_sampling(m,first,x) && (forall|s:Seq<Event>| #[trigger] fan(m,x,s)
            && mail::submitted(asm::drive(m,x,s)) && !mail::posted(m)(asm::drive(m,x,s)) ==> {
                let y=asm::drive(m,x,s);
                mail::first_availability(m,run,read::at_state(y)) && mail::fair_opportunity(m,run,y)
                    && !wait::needs_class(mail::active_step(m),mail::posted(m),y,app::weak_replica_step())
            })
    }

    // Positive service and held-value sampling are hybrid A. Fair executions
    // are the scheduler premise. The two needs_class tests are no-await on
    // the actual weak work. None of these clauses selects a read result.
    pub open spec fn invocation_laws<S>(m:Program<S>,base:State<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
        run:fair::Runnable) -> bool {
        forall|x:State<S>| #[trigger] reachable(m,base,x) ==> (
            (x.first_requested.is_empty() && !x.cfg.net.first_stopped && !x.cfg.net.second_started
                ==> maj::first_invocation_sampling(m,first,x))
            && (mail::submitted(x) && !mail::posted(m)(x) && !x.cfg.net.second_started ==>
                mail::first_availability(m,run,read::at_state(x)) && mail::fair_opportunity(m,run,x)
                    && !wait::needs_class(mail::active_step(m),mail::posted(m),x,app::weak_replica_step()))
            && (crate::survivors::after_crash(x.cfg.net) && fork::available(x) && x.requested.is_empty()
                ==> fork::opportunity(m,res,x,run)))
    }
    pub(crate) proof fn fan_prefix<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
        requires fan(m,x,s),
        ensures asm::prefix(m,x,s,true),
        decreases s.len(),
    {
        if s.len()>0 {fan_prefix(m,read::next(m,x,s[0]),s.drop_first());}
    }

    pub proof fn reference_laws<S>(p:Program<S>,k:Headers,e:Exposure,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,run:fair::Runnable)
        requires service_entry(p,k,e),invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
        ensures ({
            let m=net::implementation(k,p);let x=reference(endpoint(p,k,e),e.arm);
            reachable(m,wc::start(m),x) && service_laws(m,first,x,run)
        }),
    {
        let m=net::implementation(k,p);let base=wc::start(m);let z=endpoint(p,k,e);let r=crate::sr1_majorities::missing(e.arm);
        let x=reference(z,e.arm);weak_endpoint(p,k,e);
        assert(reaches(m,base,(weak_trace(e),Some(r),seq![]),x));
        assert(reachable(m,base,x));assert(maj::first_invocation_sampling(m,first,x));
        assert forall|s:Seq<Event>| #[trigger] fan(m,x,s) && mail::submitted(asm::drive(m,x,s)) && !mail::posted(m)(asm::drive(m,x,s))
            implies {
                let y=asm::drive(m,x,s);
                mail::first_availability(m,run,read::at_state(y)) && mail::fair_opportunity(m,run,y)
                    && !wait::needs_class(mail::active_step(m),mail::posted(m),y,app::weak_replica_step())
            } by {
                let y=asm::drive(m,x,s);fan_prefix(m,x,s);fan_at(m,x,s,s.len());endpoints(m,x,s);
                assert(reaches(m,base,(weak_trace(e),Some(r),s),y));assert(reachable(m,base,y));
            }
    }
    proof fn ref_cells<S>(p:Program<S>,k:Headers,e:Exposure)
        requires service_entry(p,k,e),
        ensures ({
            let m=net::implementation(k,p); let x=reference(endpoint(p,k,e),e.arm); let q=crate::first_quorum(e.arm.branch);
            app::all_available(x)==endpoint(p,k,e) && maj::sole(x.cfg.net,q) && q.len()==2
                && (forall|r:Replica| q.contains(r) ==> (#[trigger] (x.cfg.net.locals)(r))==first_value(e.arm))
        }),
    {
        weak_endpoint(p,k,e); let q=crate::first_quorum(e.arm.branch);
        assert(q =~= set![crate::origin(e.arm.branch),Replica::R3]);assert(crate::origin(e.arm.branch)!=Replica::R3);
        assert(set![crate::origin(e.arm.branch),Replica::R3].len()==2);
    }

    // The two sole-quorum value sets are disjoint. Since C1 sees only its
    // own identical proposals, it cannot publish during this common fanout.
    pub proof fn paired_fanout<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,l:Exposure,r:Exposure,t:Requests)
        -> (s:Seq<Event>)
        requires service_entry(p,k,l),service_entry(p,k,r),l.arm.branch!=r.arm.branch,
            recipients(t).no_duplicates(),recipients(t).to_set()==all_replicas(),supported(p,(p.initial)(Process::FirstClient),t),
            !(p.done)((p.initial)(Process::FirstClient)),
            maj::first_invocation_sampling(net::implementation(k,p),first,reference(endpoint(p,k,l),l.arm)),
            maj::first_invocation_sampling(net::implementation(k,p),first,reference(endpoint(p,k,r),r.arm)),
        ensures ({
            let m=net::implementation(k,p); let x=reference(endpoint(p,k,l),l.arm);let y=reference(endpoint(p,k,r),r.arm);
            fan(m,x,s) && fan(m,y,s) && contents(k,s)==t && !mail::posted(m)(asm::drive(m,x,s)) && !mail::posted(m)(asm::drive(m,y,s))
                && asm::drive(m,x,s).first_requested==all_replicas() && asm::drive(m,y,s).first_requested==all_replicas()
        }),
    {
        weak_endpoint(p,k,l);weak_endpoint(p,k,r);ref_cells(p,k,l);ref_cells(p,k,r);
        let m=net::implementation(k,p);let x=reference(endpoint(p,k,l),l.arm);let y=reference(endpoint(p,k,r),r.arm);
        let s=emit(p,k,x,y,t);
        if mail::posted(m)(asm::drive(m,x,s)) {early_value(m,first,x,l.arm,s);early_value(m,first,y,r.arm,s);}
        s
    }

    pub proof fn lift_fan<S>(m:Program<S>,x:State<S>,s:Seq<Event>)
        requires fan(m,x,s),
        ensures fan(m,app::all_available(x),s),asm::prefix(m,app::all_available(x),s,true),
            asm::drive(m,app::all_available(x),s)==app::all_available(asm::drive(m,x,s)),
        decreases s.len(),
    {
        if s.len()>0 {
            let a=s[0];let u=app::all_available(x);let v=read::next(m,u,a);let y=read::next(m,x,a);
            assert(request(a));assert(v.cfg.private =~= y.cfg.private);assert(v.cfg.net.locals =~= y.cfg.net.locals);
            assert(v==app::all_available(y));lift_fan(m,y,s.drop_first());
        }
    }

    pub open spec fn first_path<S>(m:Program<S>,first:spec_fn(S)->int,e:Exposure,root:State<S>,u:Service<S>) -> bool {
        wait::first_return(mail::active_step(m),mail::posted(m),root,u) && !wait::uses(u,app::weak_replica_step())
            && first((u.states.last().cfg.private)(Process::FirstClient))==first_value(e.arm)
            && forall|i:int| 0<=i<u.actions.len() ==> process_step(u.states[i].cfg.net,#[trigger] u.actions[i]).actor
                != at(crate::sr1_majorities::missing(e.arm))
    }

    pub proof fn first_service<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
        e:Exposure,s:Seq<Event>,run:fair::Runnable) -> (u:Service<S>)
        requires service_entry(p,k,e), ({
            let m=net::implementation(k,p);let x=reference(endpoint(p,k,e),e.arm);let y=asm::drive(m,x,s);
            fan(m,x,s) && y.first_requested==all_replicas() && !mail::posted(m)(y) && service_laws(m,first,x,run)
        }),
        ensures ({
            let m=net::implementation(k,p);let z=endpoint(p,k,e);let root=asm::drive(m,z,s);
            fan(m,z,s) && asm::prefix(m,z,s,true) && first_path(m,first,e,root,u)
        }),
    {
        let m=net::implementation(k,p);let b=e.arm;let x=reference(endpoint(p,k,e),b);let y=asm::drive(m,x,s);
        let q=crate::first_quorum(b.branch);let h=path(m,x,s);
        weak_endpoint(p,k,e);ref_cells(p,k,e);lift_fan(m,x,s);endpoints(m,x,s);fan_at(m,x,s,0);fan_at(m,x,s,s.len());
        assert(q.contains(crate::origin(b.branch)) && q.contains(Replica::R3));
        assert(live(y.cfg.net,at(crate::origin(b.branch))) && live(y.cfg.net,at(Replica::R3)));
        assert(y.first_requested.contains(crate::origin(b.branch)) && y.first_requested.contains(Replica::R3));
        assert(mail::submitted(y));
        mail::fair_first_service(m,run,read::at_state(y),y);nb::first_response_iff(mail::active_step(m),mail::posted(m),y);
        let t=choose|t:Service<S>| #[trigger] wait::first_return(mail::active_step(m),mail::posted(m),y,t) && !wait::uses(t,app::weak_replica_step());
        assert forall|i:int| 0<=i<s.len() implies read::prefix_step(m)(h.states[i],#[trigger] s[i],h.states[i+1]) && !mail::posted(m)(h.states[i])
            by {fan_at(m,x,s,i as nat);}
        assert(s.len()>0);
        let u=wait::Path {states:t.states.map_values(|z|app::all_available(z)),actions:t.actions};
        assert forall|i:int| 0<=i<t.actions.len() implies {
            let a=#[trigger] t.actions[i];let z=t.states[i];let v=t.states[i+1];
            mail::active_step(m)(u.states[i],a,u.states[i+1]) && !mail::posted(m)(u.states[i])
                && !app::weak_replica_step()(u.states[i],a,u.states[i+1])
                && process_step(u.states[i].cfg.net,a).actor!=at(crate::sr1_majorities::missing(b))
        } by {
            assert(mail::active_step(m)(t.states[i],t.actions[i],t.states[i+1]) && !mail::posted(m)(t.states[i]));
            service_frame(m,t,i as nat);app::original_step(m,t.states[i],t.actions[i],t.states[i+1]);
            assert(live(t.states[i].cfg.net,process_step(t.states[i].cfg.net,t.actions[i]).actor));
        }
        service_frame(m,t,t.actions.len());
        fan_path(m,x,s);assert(maj::fresh_invocation(maj::Caller::First,x,s[0]));
        assert forall|r:Replica| #[trigger] q.contains(r)==live(t.states.last().cfg.net,at(r)) by {
            assert(q.contains(r)==live(x.cfg.net,at(r)));
        }
        assert(maj::served(maj::Caller::First,m,res,h,t,q));assert(nb::within(read::prefix_step(m),read::at_state(x),x,0));
        maj::invocation_includes_submitted_sampling(m,first,res,x);
        let v=first((t.states.last().cfg.private)(Process::FirstClient));
        if maj::held(h.states,q,v) {
            let (i,r)=choose|i:int,r:Replica| 0<=i<h.states.len() && q.contains(r) && #[trigger] (h.states[i].cfg.net.locals)(r)==v;
            fan_at(m,x,s,i as nat);
        } else {
            assert(maj::held(t.states,q,v));
            let (i,r)=choose|i:int,r:Replica| 0<=i<t.states.len() && q.contains(r) && #[trigger] (t.states[i].cfg.net.locals)(r)==v;
            app::cells_at(m,t,i as nat);
        }
        u
    }

    pub proof fn service_frame<S>(m:Program<S>,t:Service<S>,i:nat)
        requires t.states.len()>0,wait::first_return(mail::active_step(m),mail::posted(m),t.states[0],t),
            !wait::uses(t,app::weak_replica_step()),i<t.states.len(), !t.states[0].cfg.net.second_started,
            // All initially postponed weak traffic in the original prefix is replica-to-replica.
            replica_weak(t.states[0]),
        ensures ({
            let x=t.states[0];let y=t.states[i as int];
            y.cfg.net.locals==x.cfg.net.locals && y.cfg.net.unavailable==x.cfg.net.unavailable
                && y.cfg.net.r3_crashed==x.cfg.net.r3_crashed && y.cfg.net.first_stopped==x.cfg.net.first_stopped
                && y.cfg.net.second_started==x.cfg.net.second_started && y.calls==x.calls && y.requested==x.requested
                && y.first_requested==x.first_requested && crate::fork_information::caller2(y)==crate::fork_information::caller2(x)
                && fork::weak_packets(y)==fork::weak_packets(x)
        }),
        decreases i,
    {
        if i>0 {
            let j=i as int-1;service_frame(m,t,(i-1) as nat);let x=t.states[j];let a=t.actions[j];let y=t.states[i as int];
            assert(mail::active_step(m)(x,a,y) && !mail::posted(m)(x) && !app::weak_replica_step()(x,a,y));
            app::quiet_cells(m,x,a,y);
            if let Action::Deliver(h)=a {
                if x.cfg.net.pending[h].path==Path::Weak {
                    assert(fork::weak_packets(x).get(h)==Some(x.cfg.net.pending[h]));
                    assert(fork::weak_packets(t.states[0])[h].to is At);
                    assert(app::weak_replica_step()(x,a,y));
                }
            }
            if a is Send {assert(a->Send_1.from is At && a->Send_1.path!=Path::Weak);}
            assert(fork::weak_packets(y) =~= fork::weak_packets(x));
        }
    }

    }
}
// END MODULE: prepared_service
