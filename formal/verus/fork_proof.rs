// BEGIN MODULE: guarded_comparison
pub mod guarded_comparison {
    use vstd::prelude::*;
    use crate::delivery::*;
    use crate::first_splice::Observation;

    verus! {

    // SR2 starts after its invocation. Protect the three original weak slots.
    // Every other ordinary packet is offered to the real handler. After its
    // own first return an arm stops taking proposals.
    pub open spec fn weak_work(e:Observation) -> bool {
        match e.action {
            Action::Send(_,q) => q.path==Path::Weak,
            Action::Deliver(_) => e.incoming.is_some() && e.incoming.unwrap().path==Path::Weak,
            Action::Local(_,w) | Action::ClientInput(_,w) => w is Copy || w is WeakConfirm,
            _ => false,
        }
    }
    }
}
// END MODULE: guarded_comparison

// BEGIN MODULE: fork_information
pub mod fork_information {
    use vstd::prelude::*;
    use crate::delivery::*;
    use crate::independent_read::State;

    verus! {

    pub open spec fn caller2<S>(x:State<S>) -> S {(x.cfg.private)(Process::SecondClient)}

    }
}
// END MODULE: fork_information

// BEGIN MODULE: fork_alternatives
pub mod fork_alternatives {
    use vstd::prelude::*;
    use crate::delivery::*;
    use crate::read_call::Event;

    verus! {

    pub open spec fn wake() -> Seq<Event> {seq![Action::StopFirstClient,Action::CrashR3,Action::StartSecondClient]}

    }
}
// END MODULE: fork_alternatives

// BEGIN MODULE: original_application
pub mod original_application {
    use vstd::prelude::*;
    use crate::{Replica, delivery::*};
    use crate::first_assembly::{Lanes, Service};
    use crate::first_mailbox as mail;
    use crate::guarded_comparison as cmp;
    use crate::independent_read::{self as read, State};
    use crate::promotion_wait as wait;
    use crate::read_call::{Event, Net, Program};

    verus! {

    // Only the existing R3 confirmation has a statically owned envelope.
    pub open spec fn lanes() -> Lanes { map![2nat => Replica::R3, 3nat => Replica::R1, 4nat => Replica::R2] }

    pub open spec fn weak_replica_step<S>() -> wait::Relation<State<S>, Event> {
        |x: State<S>, a: Event, _y: State<S>| {
            let e = process_step(x.cfg.net, a);
            e.actor is At && cmp::weak_work(e)
        }
    }

    pub(crate) proof fn quiet_cells<S>(m: Program<S>, x: State<S>, a: Event, y: State<S>)
        requires read::service_step(m)(x,a,y), !weak_replica_step()(x,a,y),
        ensures y.cfg.net.locals == x.cfg.net.locals,
    {
        assert forall|r: Replica| (#[trigger] local_input(x.cfg.net,a,r)).is_none()
            || !(local_input(x.cfg.net,a,r).unwrap() is Copy) by {};
        assert(y.cfg.net.locals =~= x.cfg.net.locals);
    }

    // Remove only the service mask. The omitted replica takes no action in the
    // copied interval. In particular no queued packet is deleted or renamed.
    pub open spec fn all_available<S>(x: State<S>) -> State<S> {
        State { cfg: crate::ordinary_service::Configuration { net: Net { unavailable: None, ..x.cfg.net }, ..x.cfg }, ..x }
    }

    pub(crate) proof fn original_step<S>(m: Program<S>, x: State<S>, a: Event, y: State<S>)
        requires mail::active_step(m)(x,a,y),
        ensures mail::active_step(m)(all_available(x),a,all_available(y)),
            process_step(all_available(x).cfg.net,a) == process_step(x.cfg.net,a),
    {
        let u = all_available(x); let v = read::next(m,u,a);
        assert(process_step(u.cfg.net,a) == process_step(x.cfg.net,a));
        assert(v.cfg.net.locals =~= y.cfg.net.locals);
        assert(v.cfg.private =~= y.cfg.private);
        assert(v == all_available(y));
    }

    pub(crate) proof fn cells_at<S>(m:Program<S>,p:Service<S>,k:nat)
        requires p.states.len()==p.actions.len()+1,wait::valid_edges(mail::active_step(m),p),
            !wait::uses(p,weak_replica_step()), k<p.states.len(),
        ensures p.states[k as int].cfg.net.locals==p.states[0].cfg.net.locals,
        decreases k,
    {
        if k>0 {
            let i=k as int-1; cells_at(m,p,(k-1) as nat);
            assert(mail::active_step(m)(p.states[i],p.actions[i],p.states[i+1]));
            quiet_cells(m,p.states[i],p.actions[i],p.states[i+1]);
        }
    }

    }
}
// END MODULE: original_application

// BEGIN MODULE: native_fork
pub mod native_fork {
    // The original two reads, using physical first returns and all native
    // ordinary continuations from the independent second invocation.
    use vstd::prelude::*;
    use crate::{Replica, checkpoint::*, delivery::*};
    use crate::fair_read as fair;
    use crate::first_assembly::{self as asm, Service};
    use crate::fork_alternatives as fork;
    use crate::fork_information::caller2;
    use crate::guarded_comparison as cmp;
    use crate::hybrid_majority as maj;
    use crate::independent_read::{self as read, State};
    use crate::promotion_wait as wait;
    use crate::protocol::survivor_actor;
    use crate::read_call::{Event,Program};
    use crate::read_nonblocking as nb;
    use crate::survivors::after_crash;

    verus! {

    pub open spec fn invocation<S>(m:Program<S>,p:Service<S>) -> State<S> {
        asm::drive(m,p.states.last(),fork::wake())
    }

    pub open spec fn weak_packets<S>(x:State<S>) -> Map<nat,Packet<Wire>> {
        let q=x.cfg.net.pending;
        q.restrict(q.dom().filter(|i:nat| q[i].path==Path::Weak))
    }

    pub open spec fn masks_send(mask:Set<nat>,a:Event) -> bool {
        a is Send && mask.contains(a->Send_0)
    }

    pub open spec fn uses_name(mask:Set<nat>,s:Seq<Event>) -> bool {
        exists|j:int| 0<=j<s.len() && masks_send(mask,#[trigger] s[j])
    }

    // Only the payload/path of the actual transition identifies postponed
    // work. All request, delivery and ordinary-send guards are the native ones.
    pub open spec fn step<S>(m:Program<S>,quiet:bool) -> wait::Relation<State<S>,Event> {
        |x:State<S>,a:Event,y:State<S>| read::prefix_step(m)(x,a,y)
            && (!quiet || !cmp::weak_work(process_step(x.cfg.net,a)))
    }

    pub open spec fn completes<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>,quiet:bool) -> bool
        decreases s.len(),
    {
        if s.len()==0 {read::returned(res)(x)} else {
            let a=s[0];let y=read::next(m,x,a);
            !read::returned(res)(x) && step(m,quiet)(x,a,y) && completes(m,res,y,s.drop_first(),quiet)
        }
    }

    pub open spec fn value<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>) -> Option<int> {
        res(caller2(asm::drive(m,x,s)))
    }

    pub open spec fn same_reader<S>(x:State<S>,y:State<S>) -> bool {
        caller2(x)==caller2(y) && x.calls==y.calls && x.requested==y.requested && x.first_requested==y.first_requested
    }

    // The existing issued-majority liveness predicate starts after the fanout.
    // Here StartSecondClient is the invocation. Its native prefix_step may
    // send requests, use previously queued messages, or complete immediately.
    pub open spec fn call_run<S>(m:Program<S>,x:State<S>,e:fair::Run<S>) -> bool {
        (e.state)(0)==x && forall|i:nat| read::prefix_step(m)((e.state)(i),#[trigger] (e.action)(i),(e.state)(i+1))
    }

    pub open spec fn states<S>(m:Program<S>,x:State<S>,s:Seq<Event>) -> Seq<State<S>> {
        Seq::new(s.len()+1,|i:int| asm::drive(m,x,s.take(i)))
    }

    pub open spec fn available<S>(x:State<S>) -> bool {
        maj::sole(x.cfg.net,live_pair()) && live(x.cfg.net,Process::SecondClient)
    }

    proof fn live_through_call<S>(m:Program<S>,x:State<S>,e:fair::Run<S>,k:nat)
        requires after_crash(x.cfg.net),call_run(m,x,e),
        ensures after_crash((e.state)(k).cfg.net),available((e.state)(k)),
        decreases k,
    {
        if k>0 {
            live_through_call(m,x,e,(k-1) as nat);
            assert(read::prefix_step(m)((e.state)((k-1) as nat),(e.action)((k-1) as nat),(e.state)(k)));
        }
        assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
    }

    pub open spec fn invocation_a<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,run:fair::Runnable) -> bool {
        (forall|e:fair::Run<S>| #[trigger] call_run(m,x,e) && fair::fair(e,run)
            && (forall|k:nat| #[trigger] available((e.state)(k)))
            ==> exists|i:nat| #[trigger] read::returned(res)((e.state)(i)))
        && (forall|s:Seq<Event>| #[trigger] completes(m,res,x,s,false)
            && (forall|k:int| 0<=k<=s.len() ==> #[trigger] available(states(m,x,s)[k]))
            ==> maj::held(states(m,x,s),live_pair(),value(m,res,x,s).unwrap()))
    }

    pub open spec fn weak_step<S>() -> wait::Relation<State<S>,Event> {
        |x:State<S>,a:Event,_y:State<S>| cmp::weak_work(process_step(x.cfg.net,a))
    }

    pub open spec fn opportunity<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,run:fair::Runnable) -> bool {
        invocation_a(m,res,x,run)
            && (exists|e:fair::Run<S>| #[trigger] call_run(m,x,e) && fair::fair(e,run))
            && !wait::needs_class(read::prefix_step(m),read::returned(res),x,weak_step())
    }

    proof fn native_actions<S>(m:Program<S>,res:spec_fn(S)->Option<int>,p:Service<S>,k:nat)
        requires wait::first_return(read::prefix_step(m),read::returned(res),p.states[0],p),
            !wait::uses(p,weak_step()),k<=p.actions.len(),
        ensures completes(m,res,p.states[k as int],p.actions.skip(k as int),true),
        decreases p.actions.len()-k,
    {
        let s=p.actions.skip(k as int);
        if k<p.actions.len() {
            let a=p.actions[k as int];let x=p.states[k as int];let y=p.states[k as int+1];
            assert(read::prefix_step(m)(x,a,y) && !weak_step()(x,a,y));
            assert(s.drop_first() =~= p.actions.skip(k as int+1));native_actions(m,res,p,k+1);
        }
    }

    pub proof fn native_return_from_a<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,run:fair::Runnable) -> (s:Seq<Event>)
        requires after_crash(x.cfg.net),maj::sole(x.cfg.net,live_pair()),opportunity(m,res,x,run),
        ensures completes(m,res,x,s,true),
    {
        let d=read::returned(res);let st=read::prefix_step(m);
        if d(x) {Seq::empty()} else {
            let e=choose|e:fair::Run<S>| #[trigger] call_run(m,x,e) && fair::fair(e,run);
            assert forall|k:nat| #[trigger] available((e.state)(k)) by {live_through_call(m,x,e,k);}
            let k=choose|i:nat| #[trigger] d((e.state)(i));
            let p=fair::initial_block(e,k);
            assert forall|i:int| 0<=i<p.actions.len() implies st(p.states[i],#[trigger] p.actions[i],p.states[i+1]) by {
                assert(st((e.state)(i as nat),(e.action)(i as nat),(e.state)((i+1) as nat)));
            }
            nb::from_path(st,d,p,0);assert(nb::possible(st,d,x));nb::first_response_iff(st,d,x);
            let q=choose|q:Service<S>| #[trigger] wait::first_return(st,d,x,q) && !wait::uses(q,weak_step());
            native_actions(m,res,q,0);assert(q.actions.skip(0) =~= q.actions);q.actions
        }
    }

    pub(crate) proof fn completion_facts<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>)
        requires after_crash(x.cfg.net),completes(m,res,x,s,true),
        ensures completes(m,res,x,s,false),value(m,res,x,s).is_some(),asm::prefix(m,x,s,true),
            forall|k:int| 0<=k<=s.len() ==> #[trigger] available(states(m,x,s)[k]),
            forall|k:int| 0<=k<=s.len() ==> (#[trigger] states(m,x,s)[k]).cfg.net.locals==x.cfg.net.locals,
            forall|k:int| 0<=k<=s.len() ==> #[trigger] weak_packets(states(m,x,s)[k])==weak_packets(x),
            forall|k:int| 0<=k<s.len() && (#[trigger] s[k]) is Send ==>
                !states(m,x,s)[k].cfg.net.pending.contains_key(s[k]->Send_0) && !weak_packets(x).contains_key(s[k]->Send_0),
            forall|k:int| 0<=k<s.len() ==> survivor_actor(#[trigger] process_step(states(m,x,s)[k].cfg.net,s[k]).actor),
        decreases s.len(),
    {
        assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
        if s.len()>0 {
            let a=s[0];let y=read::next(m,x,a);let tail=s.drop_first();
            assert(after_crash(y.cfg.net) && a!=Action::StopFirstClient);
            assert(weak_packets(y) =~= weak_packets(x));
            assert(y.cfg.net.locals =~= x.cfg.net.locals) by {
                assert forall|r:Replica| (#[trigger] local_input(x.cfg.net,a,r)).is_none()
                    || !(local_input(x.cfg.net,a,r).unwrap() is Copy) by {};
            }
            completion_facts(m,res,y,tail);
            assert forall|k:int| 1<=k<=s.len() implies #[trigger] states(m,x,s)[k]==states(m,y,tail)[k-1] by {
                assert(s.take(k)[0]==a && s.take(k).drop_first() =~= tail.take(k-1));
            }
            assert forall|k:int| 0<=k<s.len() implies survivor_actor(#[trigger] process_step(states(m,x,s)[k].cfg.net,s[k]).actor) by {
                if k>0 {assert(s[k]==tail[k-1]);assert(survivor_actor(process_step(states(m,y,tail)[k-1].cfg.net,tail[k-1]).actor));}
            }
            assert forall|k:int| 0<=k<s.len() && (#[trigger] s[k]) is Send implies
                !states(m,x,s)[k].cfg.net.pending.contains_key(s[k]->Send_0) && !weak_packets(x).contains_key(s[k]->Send_0) by {
                if k>0 {assert(s[k]==tail[k-1]);}
            }
        }
    }

    pub proof fn sampled_native_return<S>(m:Program<S>,res:spec_fn(S)->Option<int>,x:State<S>,s:Seq<Event>,run:fair::Runnable)
        requires after_crash(x.cfg.net),survivor(x.cfg.net)==(2int,5int),invocation_a(m,res,x,run),completes(m,res,x,s,true),
        ensures maj::held(states(m,x,s),live_pair(),value(m,res,x,s).unwrap()),
            value(m,res,x,s)==Some(2) || value(m,res,x,s)==Some(5),asm::prefix(m,x,s,true),
            forall|k:int| 0<=k<=s.len() ==> #[trigger] weak_packets(states(m,x,s)[k])==weak_packets(x),
            forall|k:int| 0<=k<s.len() ==> survivor_actor(#[trigger] process_step(states(m,x,s)[k].cfg.net,s[k]).actor),
    {
        completion_facts(m,res,x,s);let v=value(m,res,x,s).unwrap();
        let (i,r)=choose|i:int,r:Replica| 0<=i<states(m,x,s).len() && live_pair().contains(r)
            && #[trigger] (states(m,x,s)[i].cfg.net.locals)(r)==v;
        assert(states(m,x,s)[i].cfg.net.locals==x.cfg.net.locals);
    }

    }
}
// END MODULE: native_fork

// BEGIN MODULE: async_fork
pub mod async_fork {
    use vstd::prelude::*;
    use crate::{Replica, checkpoint::*, delivery::*};
    use crate::async_messages::{self as net, Command, Headers, Message, implementation};
    use crate::first_splice::Observation;
    use crate::independent_read::{self as read, State};
    use crate::native_fork as fork;
    use crate::protocol::survivor_actor;
    use crate::read_call::{Event, Net, Program};
    use crate::survivors::after_crash;

    verus! {

    pub open spec fn occurrences(k: Headers, n: Net, msg: Message) -> Set<nat> {
        let q = net::queue(k, n);
        q.dom().filter(|h: nat| q[h] == msg)
    }

    pub struct View<S> {
        pub cells: (int, int), pub left: S, pub right: S,
        pub copies: spec_fn(Message) -> nat,
    }

    pub open spec fn channel_view<S>(x: net::Channel<S>) -> View<S> {
        View { cells: survivor(x.local.cfg.net), left: (x.local.cfg.private)(at(Replica::R1)),
            right: (x.local.cfg.private)(at(Replica::R2)),
            copies: |msg: Message| if msg.body.path != Path::Weak && survivor_actor(msg.body.to) {
                x.packets.dom().filter(|h:nat| x.packets[h]==msg).len()
            } else { 0 },
        }
    }

    pub open spec fn view<S>(k: Headers, x: State<S>) -> View<S> {
        channel_view(net::snapshot(k,x))
    }

    pub(crate) proof fn visible_count<S>(k: Headers, x: State<S>, msg: Message)
        requires msg.body.path != Path::Weak, survivor_actor(msg.body.to),
        ensures (view(k, x).copies)(msg) == occurrences(k, x.cfg.net, msg).len(),
    {}

    pub(crate) closed spec fn count_after(count: nat, msg: Message, e: Observation) -> nat {
        match e.action {
            Action::Send(id, p) if msg == (Message { id, body: p }) => count + 1,
            Action::Deliver(id) if msg.id == id && e.incoming == Some(msg.body) => (count - 1) as nat,
            _ => count,
        }
    }

    pub(crate) proof fn count_step<S>(p: Program<S>, k: Headers, x: State<S>, a: Event, msg: Message)
        requires ({
            let m = implementation(k, p); fork::step(m, true)(x, a, read::next(m, x, a))
        }),
        ensures ({
            let y = read::next(implementation(k, p), x, a);
            occurrences(k, y.cfg.net, msg).len() == count_after(occurrences(k, x.cfg.net, msg).len(),
                msg, net::callback(k, process_step(x.cfg.net, a)))
        }),
    {
        net::project_step(p, k, x, a, true);
        let n = x.cfg.net; let y = read::next(implementation(k, p), x, a);
        let before = occurrences(k, n, msg); let after = occurrences(k, y.cfg.net, msg);
        match a {
            Action::Send(h, body) if net::message(k, h, body) == msg => {
                assert(!before.contains(h)); assert(after =~= before.insert(h));
            },
            Action::Deliver(h) if net::queue(k, n)[h] == msg => {
                assert(before.contains(h)); assert(after =~= before.remove(h));
            },
            _ => { assert(after =~= before); },
        }
    }

    // Replay one accepted logical input. A delivery consumes one actual equal
    // message on the target. Only newly allocated send handles avoid the mask.
    proof fn replay_step<S>(p: Program<S>, k: Headers, x: State<S>, y: State<S>, a: Event,
        avoid: Set<nat>) -> (b: Event)
        requires after_crash(x.cfg.net), after_crash(y.cfg.net), fork::same_reader(x, y), view(k, x) == view(k, y),
            ({ let m = implementation(k, p); fork::step(m, true)(x, a, read::next(m, x, a)) }),
        ensures ({
            let m = implementation(k, p); let u = read::next(m, x, a); let v = read::next(m, y, b);
            fork::step(m, true)(y, b, v) && !fork::masks_send(avoid, b)
                && net::callback(k, process_step(x.cfg.net, a)) == net::callback(k, process_step(y.cfg.net, b))
                && after_crash(u.cfg.net) && after_crash(v.cfg.net) && fork::same_reader(u, v) && view(k, u) == view(k, v)
        }),
    {
        let m = implementation(k, p); let c = net::command(k, a);
        net::project_step(p, k, x, a, true);
        let d = if let Command::Deliver(h) = c {
            let msg = net::queue(k, x.cfg.net)[h];
            let xs = occurrences(k, x.cfg.net, msg); let ys = occurrences(k, y.cfg.net, msg);
            assert(xs.contains(h));
            assert(msg.body.path != Path::Weak && survivor_actor(msg.body.to));
            assert((view(k, x).copies)(msg) == (view(k, y).copies)(msg));
            assert(xs.len() == (view(k, x).copies)(msg) && ys.len() == (view(k, y).copies)(msg));
            vstd::set::lemma_set_contains_len(xs, h);
            assert(ys.len() > 0);
            vstd::set::lemma_set_choose_len(ys);
            let j = ys.choose();
            assert(ys.contains(j));
            assert(net::queue(k, y.cfg.net).get(j) == Some(msg));
            Command::Deliver(j)
        } else { c };
        let e = net::input(k, x.cfg.net, c);
        assert(survivor_actor(e.actor));
        assert(net::input(k, y.cfg.net, d) == e);
        assert((x.cfg.private)(e.actor) == (y.cfg.private)(e.actor));
        assert(net::ready(p, k, y, d, true));
        let b = net::realize_step(p, k, y, d, true, avoid);
        let u = read::next(m, x, a); let v = read::next(m, y, b);
        net::project_step(p, k, y, b, true);
        assert(net::callback(k, process_step(x.cfg.net, a)) == e && net::callback(k, process_step(y.cfg.net, b)) == e);
        assert forall|r: Replica| (#[trigger] local_input(x.cfg.net, a, r)).is_none()
            || !(local_input(x.cfg.net, a, r).unwrap() is Copy) by {};
        assert forall|r: Replica| (#[trigger] local_input(y.cfg.net, b, r)).is_none()
            || !(local_input(y.cfg.net, b, r).unwrap() is Copy) by {};
        assert forall|msg: Message| #[trigger] (view(k, u).copies)(msg) == (view(k, v).copies)(msg) by {
            if msg.body.path != Path::Weak && survivor_actor(msg.body.to) {
                visible_count(k, x, msg); visible_count(k, y, msg);
                visible_count(k, u, msg); visible_count(k, v, msg);
                assert((view(k, x).copies)(msg) == (view(k, y).copies)(msg));
                assert(occurrences(k, x.cfg.net, msg).len() == occurrences(k, y.cfg.net, msg).len());
                count_step(p, k, x, a, msg); count_step(p, k, y, b, msg);
                assert(occurrences(k, u.cfg.net, msg).len() == occurrences(k, v.cfg.net, msg).len());
            }
        }
        assert(view(k, u).copies =~= view(k, v).copies);
        b
    }

    pub open spec fn callbacks<S>(p: Program<S>, k: Headers, x: State<S>, s: Seq<Event>) -> Seq<Observation>
        decreases s.len(),
    {
        if s.len() == 0 { seq![] } else {
            seq![net::callback(k, process_step(x.cfg.net, s[0]))]
                + callbacks(p, k, read::next(implementation(k, p), x, s[0]), s.drop_first())
        }
    }

    pub proof fn replay_return<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>,
        x: State<S>, y: State<S>, s: Seq<Event>, avoid: Set<nat>) -> (t: Seq<Event>)
        requires after_crash(x.cfg.net), after_crash(y.cfg.net), fork::same_reader(x, y), view(k, x) == view(k, y),
            fork::completes(implementation(k, p), res, x, s, true),
        ensures ({
            let m = implementation(k, p);
            !fork::uses_name(avoid, t) && fork::completes(m, res, y, t, true)
                && fork::value(m, res, x, s) == fork::value(m, res, y, t)
                && callbacks(p, k, x, s) == callbacks(p, k, y, t) && t.len() == s.len()
        }),
        decreases s.len(),
    {
        let m = implementation(k, p);
        if s.len() == 0 { seq![] } else {
            let a = s[0]; let b = replay_step(p, k, x, y, a, avoid);
            let suffix = replay_return(p, k, res, read::next(m, x, a), read::next(m, y, b), s.drop_first(), avoid);
            let t = seq![b] + suffix;
            assert(t.drop_first() =~= suffix);
            assert forall|j: int| 0 <= j < t.len() implies !fork::masks_send(avoid, #[trigger] t[j]) by {
                if j > 0 { assert(t[j] == suffix[j-1]); }
            }
            t
        }
    }

    pub open spec fn after_offers<S>(p: Program<S>, k: Headers) -> Program<S> {
        crate::independent_preparations::after_offers(implementation(k, p), crate::original_application::lanes())
    }

    }
}
// END MODULE: async_fork

// BEGIN MODULE: prepared_hot
pub mod prepared_hot {
    // Apply the functional preservation rule to the two real service windows
    // reached from selective weak visibility.
    use vstd::prelude::*;
    use crate::{Op,Replica,checkpoint::*,delivery::*};
    use crate::async_fork as af;
    use crate::async_messages::{self as net,Headers};
    use crate::first_assembly::{self as asm,Service};
    use crate::first_mailbox as mail;
    use crate::first_splice::{self as tape,Observation};
    use crate::independent_read::{self as read,State};
    use crate::native_fork as fork;
    use crate::operation_history as op;
    use crate::order_extension as order;
    use crate::original_application as app;
    use crate::prepared_service::{self as svc,Exposure};
    use crate::read_call::{Event,Program};
    use crate::register_history as reg;
    use crate::semantic_promotion as retain;
    use crate::weak_construction as wc;
    use crate::weak_visibility as vis;

    verus! {

    // Independent evidence is taken before SR1. It includes the complete private
    // memories of R1/R2, their cells, and ordinary messages available to the
    // surviving actors. Weak positions are computed separately on the full trace.
    pub type Evidence<S> = af::View<S>;
    pub open spec fn evidence<S>(p:Program<S>,k:Headers,e:Exposure) -> Evidence<S> {
        af::view(k,svc::endpoint(p,k,e))
    }

    // A fixed interpretation of independently assigned weak positions on the
    // public weak history. It sees no strong operation, return or future cut.
    pub type WeakOrder = spec_fn(Seq<Observation>)->Seq<Op>;
    pub open spec fn positions(k:Headers,o:WeakOrder,e:Exposure) -> Seq<Op> { o(vis::callbacks(k,local_rmw_cells(),svc::weak_trace(e))) }
    pub open spec fn weak_word(s:Seq<Op>) -> bool {
        s.no_duplicates() && forall|i:int| 0<=i<s.len() ==> order::weak(#[trigger] s[i])
    }

    pub struct Phase<S> { pub weak:Exposure, pub sends:Seq<Event>, pub service:Service<S> }
    pub open spec fn root<S>(p:Program<S>,k:Headers,e:Exposure,s:Seq<Event>) -> State<S> {
        asm::drive(net::implementation(k,p),svc::endpoint(p,k,e),s)
    }
    pub open spec fn at_entry<S>(p:Program<S>,k:Headers,e:Exposure,s:Seq<Event>,x:State<S>) -> bool {
        let m=net::implementation(k,p);
        svc::service_entry(p,k,e) && svc::fan(m,svc::endpoint(p,k,e),s) && x==root(p,k,e,s)
            && x.first_requested==all_replicas() && !mail::posted(m)(x)
    }
    pub open spec fn phase<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,h:Phase<S>) -> bool {
        let m=net::implementation(k,p);let z=h.service.states[0];
        at_entry(p,k,h.weak,h.sends,z) && svc::first_path(m,first,h.weak,z,h.service)
    }

    pub type Input<S> = (Evidence<S>,S,read::Calls,Set<Replica>,Set<Replica>);
    pub type Runtime<S> = op::System<State<S>,Event,Op,int,af::View<S>,Input<S>,Evidence<S>>;
    pub type Window<S> = op::Window<State<S>,Event,Op,Evidence<S>>;

    pub open spec fn entry_witness<S>(p:Program<S>,k:Headers,o:WeakOrder,w:(Exposure,Seq<Event>),
        x:State<S>,ev:Evidence<S>,weak:Seq<Op>) -> bool {
        at_entry(p,k,w.0,w.1,x) && ev==evidence(p,k,w.0) && weak==positions(k,o,w.0)
    }
    pub type Admission = spec_fn(Exposure)->bool;
    // Restrict the functional-T domain to the actual weak interface. Replica
    // guards, operation records and all possible ordinary returns stay native.
    pub open spec fn system_for<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission) -> Runtime<S> {
        let raw=net::implementation(k,p);
        op::System {
            entry:|x:State<S>,ev:Evidence<S>,weak:Seq<Op>| exists|w:(Exposure,Seq<Event>)| #[trigger] entry_witness(p,k,o,w,x,ev,weak) && allows_entry(w.0),
            step:reg::native_step(raw), quiet:reg::quiet(), installer:retain::ordinary_replica(k),
            calls:|x:State<S>|reg::ledger(raw,first,res,x), record:|x:State<S>|af::view(k,x),
            input:|x:State<S>,_op:Op,ev:Evidence<S>|(ev,crate::fork_information::caller2(x),x.calls,x.requested,x.first_requested),
            service_cut: |x:State<S>,b:Op| b==Op::SR2 && crate::survivors::after_crash(x.cfg.net),
            ordinary_input: |x:State<S>,b:Op,a:Event| b==Op::SR2 && crate::survivors::after_crash(x.cfg.net)
                && !crate::guarded_comparison::weak_work(process_step(x.cfg.net,a)),
        }
    }
    pub open spec fn window<S>(p:Program<S>,k:Headers,o:WeakOrder,h:Phase<S>) -> Window<S> {
        let wake=crate::fork_alternatives::wake();
        op::Window { service:h.service,handoff:svc::path(net::implementation(k,p),h.service.states.last(),wake),
            producer:Op::SR1,consumer:Op::SR2,writer:observed_writer(h.weak.arm),
            evidence:evidence(p,k,h.weak),weak_order:positions(k,o,h.weak) }
    }

    // Changing the admitted producer entries and their evidence has no effect
    // on the underlying guarded consumer executions.
    proof fn same_finish<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
        x:State<S>,t:Seq<(Event,State<S>)>,d:int)
        ensures op::finishes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2,t,d)==op::finishes(reg::system(p,k,first,res),x,Op::SR2,t,d),
        decreases t.len(),
    {
        if t.len()>0 {
            let (a,y)=t[0];let raw=net::implementation(k,p);let old=af::after_offers(p,k);
            assert(read::next(raw,x,a)==read::next(old,x,a));
            assert(asm::prefix(raw,x,seq![a],true)==asm::prefix(old,x,seq![a],true)) by {reveal_with_fuel(asm::prefix,2);}
            same_finish(p,k,first,res,o,allows_entry,y,t.drop_first(),d);
        }
    }
    proof fn transfer_outcome<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
        x:State<S>,y:State<S>,d:int)
        requires crate::survivors::after_crash(x.cfg.net),crate::survivors::after_crash(y.cfg.net),fork::same_reader(x,y),
            af::view(k,x)==af::view(k,y),op::outcomes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2).contains(d),
        ensures op::outcomes(system_for(p,k,first,res,o,allows_entry),y,Op::SR2).contains(d),
    {
        let s=actual_option(p,k,first,res,o,allows_entry,x,d);
        let t=af::replay_return(p,k,res,x,y,s,Set::empty());
        option_for(p,k,first,res,o,allows_entry,y,t);
    }
    proof fn determines<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission)
        ensures op::determined_by_record(system_for(p,k,first,res,o,allows_entry),Op::SR2),
    {
        let sys=system_for(p,k,first,res,o,allows_entry);let b=Op::SR2;
        assert forall|x:State<S>,y:State<S>,e:Evidence<S>,f:Evidence<S>| (sys.service_cut)(x,b) && (sys.service_cut)(y,b)
            && (sys.record)(x)==(sys.record)(y) && #[trigger] (sys.input)(x,b,e)==#[trigger] (sys.input)(y,b,f)
            implies op::outcomes(sys,x,b)==op::outcomes(sys,y,b) by {
            let u=op::outcomes(sys,x,b);let v=op::outcomes(sys,y,b);
            assert forall|d:int| #[trigger] u.contains(d)==#[trigger] v.contains(d) by {
                if u.contains(d) {transfer_outcome(p,k,first,res,o,allows_entry,x,y,d);}
                if v.contains(d) {transfer_outcome(p,k,first,res,o,allows_entry,y,x,d);}
            }
            assert(u =~= v);
        }
    }

    pub(crate) proof fn view_from_queue<S>(k:Headers,x:State<S>,y:State<S>)
        requires svc::ordinary(x)==svc::ordinary(y),survivor(x.cfg.net)==survivor(y.cfg.net),
            (x.cfg.private)(at(Replica::R1))==(y.cfg.private)(at(Replica::R1)),(x.cfg.private)(at(Replica::R2))==(y.cfg.private)(at(Replica::R2)),
        ensures af::view(k,x)==af::view(k,y),
    {
        assert forall|msg:net::Message| (#[trigger] (af::view(k,x).copies)(msg))==(af::view(k,y).copies)(msg) by {
            if msg.body.path!=Path::Weak && crate::protocol::survivor_actor(msg.body.to) {
                assert(af::occurrences(k,x.cfg.net,msg) =~= af::occurrences(k,y.cfg.net,msg)) by {
                    assert forall|j:nat| #[trigger] af::occurrences(k,x.cfg.net,msg).contains(j)==#[trigger] af::occurrences(k,y.cfg.net,msg).contains(j)
                        by {assert(svc::ordinary(x).get(j)==svc::ordinary(y).get(j));}
                }
            }
        }
        assert(af::view(k,x).copies =~= af::view(k,y).copies);
    }
    // Fanout adds the same public requests to possibly differently named queues.
    // Counts retain the payload ID, body, sender, recipient and multiplicity.
    proof fn fan_view<S>(p:Program<S>,k:Headers,x:State<S>,y:State<S>,s:Seq<Event>)
        requires af::view(k,x)==af::view(k,y),svc::fan(net::implementation(k,p),x,s),svc::fan(net::implementation(k,p),y,s),
        ensures af::view(k,asm::drive(net::implementation(k,p),x,s))==af::view(k,asm::drive(net::implementation(k,p),y,s)),
        decreases s.len(),
    {
        if s.len()>0 {
            let m=net::implementation(k,p);
            let a=s[0];let u=read::next(m,x,a);let v=read::next(m,y,a);assert(svc::request(a));
            assert(process_step(x.cfg.net,a)==process_step(y.cfg.net,a));
            assert forall|msg:net::Message| (#[trigger] (af::view(k,u).copies)(msg))==(af::view(k,v).copies)(msg) by {
                if msg.body.path!=Path::Weak && crate::protocol::survivor_actor(msg.body.to) {
                    assert((af::view(k,x).copies)(msg)==(af::view(k,y).copies)(msg));
                    af::visible_count(k,x,msg);af::visible_count(k,y,msg);
                    af::visible_count(k,u,msg);af::visible_count(k,v,msg);
                    af::count_step(p,k,x,a,msg);af::count_step(p,k,y,a,msg);
                }
            }
            assert(af::view(k,u).copies =~= af::view(k,v).copies);
            fan_view(p,k,u,v,s.drop_first());
        }
    }
    proof fn same_entry<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,a:Phase<S>,b:Phase<S>)
        requires phase(p,k,first,a),phase(p,k,first,b),a.sends==b.sends,evidence(p,k,a.weak)==evidence(p,k,b.weak),
        ensures af::view(k,a.service.states[0])==af::view(k,b.service.states[0]),
    {
        let x=svc::endpoint(p,k,a.weak);let y=svc::endpoint(p,k,b.weak);let s=a.sends;
        fan_view(p,k,x,y,s);
    }

    pub open spec fn lead<S>(h:Phase<S>) -> Seq<Event> {
        ((svc::weak_trace(h.weak)+h.sends)+h.service.actions)+crate::fork_alternatives::wake()
    }
    pub open spec fn invoked<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,h:Phase<S>,x:State<S>) -> bool {
        phase(p,k,first,h) && x==fork::invocation(net::implementation(k,p),h.service)
            && asm::prefix(net::implementation(k,p),wc::start(net::implementation(k,p)),lead(h),true)
    }
    #[verifier::rlimit(20)]
    pub(crate) proof fn handoff_for<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,h:Phase<S>)
        requires allows_entry(h.weak),phase(p,k,first,h),crate::first_schedule::startup(net::implementation(k,p)),weak_word(positions(k,o,h.weak)),
        ensures ({
            let m=net::implementation(k,p);let sys=system_for(p,k,first,res,o,allows_entry);let w=window(p,k,o,h);let z=h.service.states.last();
            let x=fork::invocation(m,h.service);let base=wc::start(m);let weak=svc::endpoint(p,k,h.weak);
            invoked(p,k,first,h,x) && asm::drive(m,base,lead(h))==x && fork::available(x) && crate::survivors::after_crash(x.cfg.net)
                && net::trace(p,net::snapshot(k,base),net::turns(k,lead(h)),true)
                && op::genuine(sys,reg::register(),w) && op::observation(sys,w).position==reg::contest()
                && w.handoff.states.last()==x && x.cfg.net.pending==z.cfg.net.pending && af::view(k,z)==af::view(k,x)
                && fork::weak_packets(x)==fork::weak_packets(weak) && survivor(x.cfg.net)==(2int,5int)
                && x.calls==weak.calls && x.first_requested==all_replicas() && x.requested.is_empty()
                && crate::fork_information::caller2(x)==(m.update)((m.initial)(Process::SecondClient),crate::read_issue::local_event(Action::StartSecondClient))
        }),
    {
        let m=net::implementation(k,p);let base=wc::start(m);let weak=svc::endpoint(p,k,h.weak);let s=h.service;let z=s.states.last();
        let sys=system_for(p,k,first,res,o,allows_entry);let w=window(p,k,o,h);let wake=crate::fork_alternatives::wake();let x=fork::invocation(m,s);
        let root=s.states[0];
        svc::weak_endpoint(p,k,h.weak);svc::fan_at(m,weak,h.sends,h.sends.len());svc::endpoints(m,weak,h.sends);
        svc::lift_fan(m,weak,h.sends);assert(app::all_available(weak)==weak);
        svc::service_frame(m,s,s.actions.len());
        assert((sys.entry)(root,w.evidence,w.weak_order)) by {assert(entry_witness(p,k,o,(h.weak,h.sends),root,w.evidence,w.weak_order));}
        assert forall|j:int| 0<=j<s.actions.len() implies reg::native_step(m)(s.states[j],#[trigger] s.actions[j],s.states[j+1])
            && reg::quiet()(s.states[j],s.actions[j]) by {
            assert(mail::active_step(m)(s.states[j],s.actions[j],s.states[j+1]) && !mail::posted(m)(s.states[j]));
            assert(read::initial_send(s.states[j],s.actions[j]));
            assert(asm::prefix(m,s.states[j],seq![s.actions[j]],true)) by {reveal_with_fuel(asm::prefix,2);}
        }
        assert forall|j:int| 0<=j<s.actions.len() implies {
            let c=reg::ledger(m,first,res,#[trigger] s.states[j]);
            c.issued.contains(Op::SR1) && !c.replies.contains_key(Op::SR1) && !c.issued.contains(Op::SR2)
        } by {svc::service_frame(m,s,j as nat);assert(!mail::posted(m)(s.states[j]));}
        assert(reg::ledger(m,first,res,z)==reg::publication(h.weak.arm));reg::earlier_source(h.weak.arm);
        tape::recorded(m,s,0);asm::native_prefix(m,root,tape::record(s,0),true);assert(asm::actions(tape::record(s,0)) =~= s.actions);
        assert(asm::prefix(m,z,wake,true)) by {reveal_with_fuel(asm::prefix,4);}
        reg::wake_segment(m,z);svc::endpoints(m,z,wake);
        assert forall|j:int| 0<=j<wake.len() implies !reg::ledger(m,first,res,#[trigger] w.handoff.states[j]).issued.contains(Op::SR2)
            by {assert(j==0 || j==1 || j==2);reveal_with_fuel(asm::drive,3);}
        assert(x.cfg.net.pending==z.cfg.net.pending && svc::ordinary(x)==svc::ordinary(z)
            && x.first_requested==z.first_requested && x.requested==z.requested && x.calls==z.calls
            && crate::survivors::after_crash(x.cfg.net) && survivor(x.cfg.net)==survivor(z.cfg.net)
            && (x.cfg.private)(at(Replica::R1))==(z.cfg.private)(at(Replica::R1))
            && (x.cfg.private)(at(Replica::R2))==(z.cfg.private)(at(Replica::R2))
            && crate::fork_information::caller2(x)==(m.update)((m.initial)(Process::SecondClient),crate::read_issue::local_event(Action::StartSecondClient)))
            by {reveal_with_fuel(asm::drive,4);}
        assert(live_pair().len()==2) by {assert(set![Replica::R1,Replica::R2].len()==2);}
        view_from_queue(k,z,x);
        assert(op::question(reg::ledger(m,first,res,x),Op::SR1,Op::SR2)==reg::contest()) by {
            assert(op::question(reg::ledger(m,first,res,x),Op::SR1,Op::SR2).background.replies =~= reg::weak_replies());
        }
        asm::prefix_concat(m,base,svc::weak_trace(h.weak),h.sends,true);
        asm::prefix_concat(m,base,svc::weak_trace(h.weak)+h.sends,s.actions,true);
        asm::prefix_concat(m,base,(svc::weak_trace(h.weak)+h.sends)+s.actions,wake,true);
        net::project_prefix(p,k,base,lead(h),true,res);
    }

    // A pending C1 has no sends during service. Consuming a packet addressed
    // to C1 cannot change the ordinary packets that a survivor could consume.
    proof fn client_frame<S>(p:Program<S>,k:Headers,x:State<S>,a:Event,y:State<S>)
        requires mail::active_step(net::implementation(k,p))(x,a,y),!mail::posted(net::implementation(k,p))(x),
            !x.cfg.net.second_started,!(process_step(x.cfg.net,a).actor is At),
        ensures af::view(k,x)==af::view(k,y),
    {
        let e=process_step(x.cfg.net,a);assert(e.actor==Process::FirstClient && !(a is Send));
        assert(y.cfg.net.locals =~= x.cfg.net.locals);
        assert forall|msg:net::Message| (#[trigger] (af::view(k,x).copies)(msg))==(af::view(k,y).copies)(msg) by {
            if msg.body.path!=Path::Weak && crate::protocol::survivor_actor(msg.body.to) {
                assert(af::occurrences(k,x.cfg.net,msg) =~= af::occurrences(k,y.cfg.net,msg));
            }
        }
        assert(af::view(k,x).copies =~= af::view(k,y).copies);
    }

    proof fn last_change<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,h:Phase<S>,i:nat) -> (j:int)
        requires phase(p,k,first,h),i<h.service.states.len(),
            !h.service.states[0].cfg.net.second_started,svc::replica_weak(h.service.states[0]),
            af::view(k,h.service.states[0])!=af::view(k,h.service.states.last()),
            af::view(k,h.service.states[i as int])==af::view(k,h.service.states.last()),
        ensures ({
            let s=h.service;
            0<=j<s.actions.len() && retain::ordinary_replica(k)(s.states[j],s.actions[j])
                && af::view(k,s.states[j])!=af::view(k,s.states.last())
                && af::view(k,s.states[j+1])==af::view(k,s.states.last())
        }),
        decreases i,
    {
        let m=net::implementation(k,p);let s=h.service;
        assert(i>0);let j=i as int-1;let x=s.states[j];let y=s.states[i as int];let a=s.actions[j];
        if af::view(k,x)==af::view(k,y) {last_change(p,k,first,h,(i-1) as nat)} else {
            svc::service_frame(m,s,j as nat);
            assert(mail::active_step(m)(x,a,y) && !mail::posted(m)(x) && !app::weak_replica_step()(x,a,y));
            if !(process_step(x.cfg.net,a).actor is At) {client_frame(p,k,x,a,y);}
            j
        }
    }

    proof fn installed_exit<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,h:Phase<S>)
        requires phase(p,k,first,h), af::view(k,h.service.states[0])!=af::view(k,h.service.states.last()),
        ensures retain::installed(op::observation(system_for(p,k,first,res,o,allows_entry),window(p,k,o,h))),
    {
        let sys=system_for(p,k,first,res,o,allows_entry);let w=window(p,k,o,h);let s=h.service;let m=net::implementation(k,p);
        let weak=svc::endpoint(p,k,h.weak);svc::weak_endpoint(p,k,h.weak);
        svc::fan_at(m,weak,h.sends,h.sends.len());svc::endpoints(m,weak,h.sends);
        let j=last_change(p,k,first,h,s.actions.len());
        let z=op::observation(sys,w);let prev=af::view(k,s.states[j]);
        assert(z.ordinary_edges.contains((prev,z.exit)));
    }

    proof fn supports_value(b:Fork,d:int)
        ensures op::supports(reg::register(),reg::contest(),observed_writer(b),d)==(d==first_value(b)),
    {
        reg::register_question_is_exact(b,d);let w=observed_writer(b);let h=order::at_first(b);
        order::canonical_orders_exist(b);order::extension_iff_writer(b,h,w);
        if retain::keeps_value()(h.ops,w,d) {
            let v=choose|v:Op| order::weak(v) && d==crate::next(v,1) && #[trigger] order::can_keep(h.ops,w,v);
            order::extension_iff_writer(b,h,v);
        } else if d==first_value(b) {assert(d==crate::next(w,1) && order::can_keep(h.ops,w,w));}
    }

    proof fn asymmetric(o:Seq<Op>,a:Op,b:Op)
        ensures !crate::precedence::has_precedence(o,a,b) || !crate::precedence::has_precedence(o,b,a),
    {
        if crate::precedence::has_precedence(o,a,b) && crate::precedence::has_precedence(o,b,a) {
            let i=choose|i:int| 0<=i<o.len() && #[trigger] o[i]==a && forall|j:int| i<j<o.len() ==> #[trigger] o[j]!=b;
            let j=choose|j:int| 0<=j<o.len() && #[trigger] o[j]==b && forall|i:int| j<i<o.len() ==> #[trigger] o[i]!=a;
            assert(i!=j);
        }
    }

    pub type Episode<S> = retain::Episode<Op,op::Question<Op,int>,af::View<S>,Input<S>>;
    proof fn direction<S>(a:Episode<S>,b:Episode<S>,l:Fork,r:Fork,ds:ISet<int>,other:ISet<int>)
        requires l.branch!=r.branch,a.writer==observed_writer(l),b.writer==observed_writer(r),
            a.position==reg::contest(),b.position==reg::contest(),retain::retained_difference(a,b),
            !crate::precedence::has_precedence(a.weak_order,a.writer,b.writer) || !crate::precedence::has_precedence(b.weak_order,a.writer,b.writer),
            ds.contains(first_value(l)),other.contains(first_value(r)),
            forall|d:int| #[trigger] other.contains(d) ==> d==first_value(r),
        ensures retain::unsupported_outcomes(a,b,ds,other,|q:op::Question<Op,int>,w:Op,d:int|op::supports(reg::register(),q,w,d)),
    {
        hide(op::supports);
        let test=|q:op::Question<Op,int>,w:Op,d:int|op::supports(reg::register(),q,w,d);
        supports_value(l,first_value(l));supports_value(r,first_value(l));supports_value(l,first_value(r));supports_value(r,first_value(r));
        assert(test(a.position,a.writer,first_value(l)) && !test(b.position,b.writer,first_value(l)));
        assert(retain::resolves(other,(b.position,b.writer),(a.position,a.writer),test));
    }

    proof fn rules_out_both<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
        l:Phase<S>,r:Phase<S>)
        requires allows_entry(l.weak),allows_entry(r.weak),phase(p,k,first,l),phase(p,k,first,r),l.weak.arm.branch!=r.weak.arm.branch,
            l.sends==r.sends,evidence(p,k,l.weak)==evidence(p,k,r.weak),
            crate::first_schedule::startup(net::implementation(k,p)), weak_word(positions(k,o,l.weak)),weak_word(positions(k,o,r.weak)),
            op::operation_t(system_for(p,k,first,res,o,allows_entry),reg::register()), ({
                let sys=system_for(p,k,first,res,o,allows_entry);let m=net::implementation(k,p);
                let u=op::outcomes(sys,fork::invocation(m,l.service),Op::SR2);
                let v=op::outcomes(sys,fork::invocation(m,r.service),Op::SR2);
                u.contains(first_value(l.weak.arm)) && v.contains(first_value(r.weak.arm))
                    && (forall|d:int| #[trigger] u.contains(d) ==> d==first_value(l.weak.arm))
                    && (forall|d:int| #[trigger] v.contains(d) ==> d==first_value(r.weak.arm))
            }),
        ensures false,
    {
        hide(op::genuine);hide(op::supports);hide(op::finishes);hide(phase);hide(svc::service_entry);
        let sys=system_for(p,k,first,res,o,allows_entry);let m=net::implementation(k,p);let wa=window(p,k,o,l);let wb=window(p,k,o,r);
        let a=op::observation(sys,wa);let b=op::observation(sys,wb);let x=fork::invocation(m,l.service);let y=fork::invocation(m,r.service);
        let u=op::outcomes(sys,x,Op::SR2);let v=op::outcomes(sys,y,Op::SR2);
        handoff_for(p,k,first,res,o,allows_entry,l);handoff_for(p,k,first,res,o,allows_entry,r);same_entry(p,k,first,l,r);determines(p,k,first,res,o,allows_entry);
        assert((sys.input)(x,Op::SR2,wa.evidence)==(sys.input)(y,Op::SR2,wb.evidence)) by {
            reveal(phase);reveal(svc::service_entry);svc::weak_endpoint(p,k,l.weak);svc::weak_endpoint(p,k,r.weak);
        }
        assert(a.input==b.input && a.entry==b.entry && a.exit==a.inherited && b.exit==b.inherited);
        assert(u!=v);
        assert((sys.service_cut)(x,Op::SR2) && (sys.service_cut)(y,Op::SR2));
        assert(a.inherited!=b.inherited);
        if a.entry!=a.exit {installed_exit(p,k,first,res,o,allows_entry,l);} else {installed_exit(p,k,first,res,o,allows_entry,r);}
        assert(retain::retained_difference(a,b) && retain::retained_difference(b,a));
        asymmetric(a.weak_order,a.writer,b.writer);
        let test=|q:op::Question<Op,int>,w:Op,d:int|op::supports(reg::register(),q,w,d);
        if !crate::precedence::has_precedence(a.weak_order,a.writer,b.writer) {
            direction(a,b,l.weak.arm,r.weak.arm,u,v);
            assert(!retain::unsupported_outcomes(a,b,u,v,test));
        } else {
            direction(b,a,r.weak.arm,l.weak.arm,v,u);
            assert(!retain::unsupported_outcomes(b,a,v,u,test));
        }
    }

    pub struct Execution<S> { pub first:Phase<S>, pub second:Seq<Event> }
    pub open spec fn result<S>(m:Program<S>,res:spec_fn(S)->Option<int>,h:Execution<S>) -> int {
        fork::value(m,res,fork::invocation(m,h.first.service),h.second).unwrap()
    }
    pub open spec fn completed<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,h:Execution<S>) -> bool {
        let m=net::implementation(k,p);let f=h.first;let x=fork::invocation(m,f.service);let base=wc::start(m);
        let all=lead(f)+h.second;let z=asm::drive(m,base,all);let d=result(m,res,h);
        let w=crate::guarded_history::weak_end();
        w.answers.get(crate::weak_round::request(Op::W1).id)==Some(1)
            && w.answers.get(crate::weak_round::request(Op::W2).id)==Some(1) && crate::weak_round::origin_only(w)
            && (forall|r:Replica| (#[trigger] (base.cfg.net.locals)(r))==(w.front.base.disk)(r).value)
            && invoked(p,k,first,f,x) && fork::completes(m,res,x,h.second,true) && fork::available(x)
            && asm::prefix(m,base,all,true) && net::trace(p,net::snapshot(k,base),net::turns(k,all),true)
            && net::end(p,net::snapshot(k,base),net::turns(k,all))==net::snapshot(k,z)
            && first((f.service.states.last().cfg.private)(Process::FirstClient))==first_value(f.weak.arm)
            && res(crate::fork_information::caller2(z))==Some(d) && (d==2 || d==5)
            && x.cfg.net.pending==f.service.states.last().cfg.net.pending
            && fork::weak_packets(z)==fork::weak_packets(svc::endpoint(p,k,f.weak))
            && (forall|i:int| 0<=i<f.service.states.len() ==> #[trigger] fork::weak_packets(f.service.states[i])==fork::weak_packets(x))
            && (forall|i:int| 0<=i<=h.second.len() ==> #[trigger] fork::weak_packets(fork::states(m,x,h.second)[i])==fork::weak_packets(x))
            && forall|i:int| 0<=i<h.second.len() ==> crate::protocol::survivor_actor(
                #[trigger] process_step(fork::states(m,x,h.second)[i].cfg.net,h.second[i]).actor)
    }

    proof fn publish<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,h:Execution<S>,
        run:crate::fair_read::Runnable)
        requires allows_entry(h.first.weak),phase(p,k,first,h.first),weak_word(positions(k,o,h.first.weak)),crate::first_schedule::startup(net::implementation(k,p)), ({
            let m=net::implementation(k,p);let x=fork::invocation(m,h.first.service);
            fork::completes(m,res,x,h.second,true) && fork::invocation_a(m,res,x,run)
        }),
        ensures completed(p,k,first,res,h),
    {
        let m=net::implementation(k,p);let f=h.first;let x=fork::invocation(m,f.service);let base=wc::start(m);
        crate::weak_round::actual_overlap(f.weak.arm);
        crate::isolated_rmws();
        assert forall|r:Replica| (#[trigger] (base.cfg.net.locals)(r))==(crate::guarded_history::weak_end().front.base.disk)(r).value by {
            assert((crate::guarded_history::weak_end().front.base.disk)(r).value==(state_after(f.weak.arm,0).locals)(r));
        }
        handoff_for(p,k,first,res,o,allows_entry,f);fork::sampled_native_return(m,res,x,h.second,run);
        let weak=svc::endpoint(p,k,f.weak);svc::weak_endpoint(p,k,f.weak);
        svc::fan_at(m,weak,f.sends,f.sends.len());svc::endpoints(m,weak,f.sends);
        assert forall|i:int| 0<=i<f.service.states.len() implies #[trigger] fork::weak_packets(f.service.states[i])==fork::weak_packets(x)
            by {svc::service_frame(m,f.service,i as nat);}
        svc::endpoints(m,x,h.second);asm::prefix_concat(m,base,lead(f),h.second,true);
        net::project_prefix(p,k,base,lead(f)+h.second,true,res);
    }

    proof fn option_for<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,x:State<S>,s:Seq<Event>)
        requires crate::survivors::after_crash(x.cfg.net),fork::completes(net::implementation(k,p),res,x,s,true),
        ensures op::outcomes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2).contains(fork::value(net::implementation(k,p),res,x,s).unwrap()),
    {
        let m=net::implementation(k,p);let d=fork::value(m,res,x,s).unwrap();fork::completion_facts(m,res,x,s);
        let t=reg::native_to_window_return(p,k,first,res,x,s,d);same_finish(p,k,first,res,o,allows_entry,x,t,d);
        assert(op::finishes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2,t,d));
    }
    proof fn actual_option<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,x:State<S>,d:int)
        -> (s:Seq<Event>)
        requires crate::survivors::after_crash(x.cfg.net),op::outcomes(system_for(p,k,first,res,o,allows_entry),x,Op::SR2).contains(d),
        ensures fork::completes(net::implementation(k,p),res,x,s,true),fork::value(net::implementation(k,p),res,x,s)==Some(d),
    {
        let sys=system_for(p,k,first,res,o,allows_entry);
        let t=choose|t:Seq<(Event,State<S>)>| #[trigger] op::finishes(sys,x,Op::SR2,t,d);
        same_finish(p,k,first,res,o,allows_entry,x,t,d);reg::window_to_native_return(p,k,first,res,x,t,d)
    }

    pub open spec fn bad<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,h:Execution<S>) -> bool {
        !crate::coupled_reads::legal_returns(first((h.first.service.states.last().cfg.private)(Process::FirstClient)),result(m,res,h))
    }

    proof fn incompatible(b:Fork,d:int)
        requires d!=first_value(b),
        ensures !crate::coupled_reads::legal_returns(first_value(b),d),
    {
        if crate::coupled_reads::legal_returns(first_value(b),d) {
            let (ops,states)=choose|ops:Seq<Op>,states:Seq<int>| #[trigger] crate::legal(ops,states,first_value(b),d);
            order::exact_completed_order(b,crate::RecoveredOrder{ops,states},d);
        }
    }

    // Only two reached SR2 invocations need service. All possible ordinary
    // returns there are real guarded continuations of these same weak prefixes.
    #[verifier::rlimit(18)]
    proof fn finish_admitted_phases<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,allows_entry:Admission,
        l:Phase<S>,r:Phase<S>,run:crate::fair_read::Runnable) -> (pair:(Execution<S>,Execution<S>))
        requires allows_entry(l.weak),allows_entry(r.weak),phase(p,k,first,l),phase(p,k,first,r),l.weak.arm.branch!=r.weak.arm.branch,l.sends==r.sends,
            evidence(p,k,l.weak)==evidence(p,k,r.weak),weak_word(positions(k,o,l.weak)),weak_word(positions(k,o,r.weak)),
            crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system_for(p,k,first,res,o,allows_entry),reg::register()), ({
                let m=net::implementation(k,p);
                fork::opportunity(m,res,fork::invocation(m,l.service),run) && fork::opportunity(m,res,fork::invocation(m,r.service),run)
            }),
        ensures pair.0.first==l,pair.1.first==r,completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
            bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
    {
        hide(op::genuine);hide(op::supports);hide(op::operation_t);
        let m=net::implementation(k,p);let x=fork::invocation(m,l.service);let y=fork::invocation(m,r.service);
        let a=l.weak.arm;let b=r.weak.arm;let sys=system_for(p,k,first,res,o,allows_entry);
        handoff_for(p,k,first,res,o,allows_entry,l);handoff_for(p,k,first,res,o,allows_entry,r);
        let u=op::outcomes(sys,x,Op::SR2);let v=op::outcomes(sys,y,Op::SR2);
        let s=fork::native_return_from_a(m,res,x,run);let t=fork::native_return_from_a(m,res,y,run);
        option_for(p,k,first,res,o,allows_entry,x,s);option_for(p,k,first,res,o,allows_entry,y,t);
        let (left,right)=if exists|d:int| #[trigger] u.contains(d) && d!=first_value(a) {
            let d=choose|d:int| #[trigger] u.contains(d) && d!=first_value(a);
            incompatible(a,d);(actual_option(p,k,first,res,o,allows_entry,x,d),t)
        } else if exists|d:int| #[trigger] v.contains(d) && d!=first_value(b) {
            let d=choose|d:int| #[trigger] v.contains(d) && d!=first_value(b);
            incompatible(b,d);(s,actual_option(p,k,first,res,o,allows_entry,y,d))
        } else {
            assert(u.contains(first_value(a)) && v.contains(first_value(b)));
            rules_out_both(p,k,first,res,o,allows_entry,l,r);(s,t)
        };
        let h=Execution {first:l,second:left};let g=Execution {first:r,second:right};
        publish(p,k,first,res,o,allows_entry,h,run);publish(p,k,first,res,o,allows_entry,g,run);(h,g)
    }

    pub open spec fn fresh_caller<S>(p:Program<S>,plan:svc::Requests) -> bool {
        !(p.done)((p.initial)(Process::FirstClient)) && svc::recipients(plan).no_duplicates()
            && svc::recipients(plan).to_set()==all_replicas() && svc::supported(p,(p.initial)(Process::FirstClient),plan)
    }

    pub open spec fn second_opportunities<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
        run:crate::fair_read::Runnable,l:Exposure,r:Exposure) -> bool {
        forall|h:Phase<S>| (h.weak==l || h.weak==r) && #[trigger] invoked(p,k,first,h,fork::invocation(net::implementation(k,p),h.service))
            ==> fork::opportunity(net::implementation(k,p),res,fork::invocation(net::implementation(k,p),h.service),run)
    }

    // Optional R3 work after installation, including any real confirmation
    // actually sent, is part of each supplied exposure and its public trace.
    pub proof fn original_hot_at_admitted_exposures<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
        o:WeakOrder,allows_entry:Admission,l:Exposure,r:Exposure,plan:svc::Requests,run:crate::fair_read::Runnable) -> (pair:(Execution<S>,Execution<S>))
        requires allows_entry(l),allows_entry(r),svc::service_entry(p,k,l),svc::service_entry(p,k,r),l.arm.branch!=r.arm.branch,evidence(p,k,l)==evidence(p,k,r),
            weak_word(positions(k,o,l)),weak_word(positions(k,o,r)),fresh_caller(p,plan),
            crate::first_schedule::startup(net::implementation(k,p)),op::operation_t(system_for(p,k,first,res,o,allows_entry),reg::register()),
            svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,l),l.arm),run),
            svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,r),r.arm),run),
            second_opportunities(p,k,first,res,run,l,r),
        ensures pair.0.first.weak==l,pair.1.first.weak==r,pair.0.first.sends==pair.1.first.sends,svc::contents(k,pair.0.first.sends)==plan,
            completed(p,k,first,res,pair.0),completed(p,k,first,res,pair.1),
            bad(net::implementation(k,p),first,res,pair.0) || bad(net::implementation(k,p),first,res,pair.1),
    {
        let m=net::implementation(k,p);let s=svc::paired_fanout(p,k,first,l,r,plan);
        let a=svc::first_service(p,k,first,res,l,s,run);let b=svc::first_service(p,k,first,res,r,s,run);
        let h=Phase{weak:l,sends:s,service:a};let g=Phase{weak:r,sends:s,service:b};
        assert(phase(p,k,first,h) && phase(p,k,first,g)) by {
            svc::weak_endpoint(p,k,l);svc::weak_endpoint(p,k,r);
            svc::lift_fan(m,svc::reference(svc::endpoint(p,k,l),l.arm),s);
            svc::lift_fan(m,svc::reference(svc::endpoint(p,k,r),r.arm),s);
        }
        handoff_for(p,k,first,res,o,allows_entry,h);handoff_for(p,k,first,res,o,allows_entry,g);finish_admitted_phases(p,k,first,res,o,allows_entry,h,g,run)
    }

    pub(crate) proof fn laws_at_exposures<S>(p:Program<S>,k:Headers,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,o:WeakOrder,
        run:crate::fair_read::Runnable,l:Exposure,r:Exposure)
        requires svc::service_entry(p,k,l),svc::service_entry(p,k,r),
            svc::invocation_laws(net::implementation(k,p),wc::start(net::implementation(k,p)),first,res,run),
            crate::first_schedule::startup(net::implementation(k,p)),
            weak_word(positions(k,o,l)),weak_word(positions(k,o,r)),
        ensures svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,l),l.arm),run),
            svc::service_laws(net::implementation(k,p),first,svc::reference(svc::endpoint(p,k,r),r.arm),run),
            second_opportunities(p,k,first,res,run,l,r),
    {
        let m=net::implementation(k,p);let base=wc::start(m);
        svc::reference_laws(p,k,l,first,res,run);svc::reference_laws(p,k,r,first,res,run);
        assert forall|h:Phase<S>| (h.weak==l || h.weak==r) && #[trigger] invoked(p,k,first,h,fork::invocation(m,h.service))
            implies fork::opportunity(m,res,fork::invocation(m,h.service),run) by {
                let x=fork::invocation(m,h.service);handoff_for(p,k,first,res,o,|_entry:Exposure|true,h);
                assert(svc::reaches(m,base,(lead(h),None,seq![]),x));assert(svc::reachable(m,base,x));
            }
    }

    }
}
// END MODULE: prepared_hot
