// A separate, nonfaulty caller can invoke while another read is in flight.
// The transport checks allocation. Send and delivery handlers see the chosen number.
use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*, protocol::*};
use crate::confirmation::fresh_send;
use crate::finite_service::{at_end, no_client_send, push_event, requested_prefix};
use crate::ordinary_service::{Configuration, allowed, apply, pending};
use crate::promotion_wait::Relation;
use crate::read_call::{self as call, Event, Log, Net, Program};
use crate::read_nonblocking as nb;
use crate::service::response_path;
use crate::survivors::after_crash;

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

// A finite consequence of hybrid availability. No particular return,
// completion schedule, promotion exemption or quorum symmetry is specified.
pub open spec fn hybrid_read_service<S>(m: Program<S>, res: spec_fn(S)->Option<int>, entry: State<S>) -> bool {
    forall|x:State<S>| #[trigger] reached(m,entry,x) && issued_to_majority(x) && pending(x.cfg,res)
        ==> nb::possible(service_step(m),returned(res),x)
}

pub open spec fn covers<S>(x: State<S>, t: Configuration<S>) -> bool {
    let s=x.cfg;
    s.net.r3_crashed && s.net.second_started && s.net.unavailable.is_none() && after_crash(t.net)
    && survivor(s.net)==survivor(t.net)
    && (forall|p:Process| survivor_actor(p) ==> #[trigger] (s.private)(p)==(t.private)(p))
    && (forall|id:nat| s.net.pending.contains_key(id) && survivor_actor(s.net.pending[id].to)
          ==> #[trigger] t.net.pending.get(id)==Some(s.net.pending[id]))
    && (forall|id:nat| #[trigger] t.net.pending.contains_key(id) ==> s.net.pending.contains_key(id) || x.reserved.contains(id))
    && (forall|id:nat| s.net.pending.contains_key(id) && s.net.pending[id].to==Process::FirstClient
          ==> #[trigger] x.reserved.contains(id))
}

pub(crate) proof fn project_step<S>(src:Program<S>,dst:Program<S>,x:State<S>,y:State<S>,t:Configuration<S>,a:Event)
    requires src.accept==dst.accept,src.update==dst.update,covers(x,t),service_step(src)(x,a,y),
    ensures ({
        let e=process_step(x.cfg.net,a);
        if e.actor==Process::FirstClient { covers(y,t) } else {
            survivor_actor(e.actor) && process_step(t.net,a)==e && allowed(dst,t,a) && covers(y,apply(dst,t,a))
        }
    }),
{
    let s=x.cfg; let e=process_step(s.net,a);
    let skip=e.actor==Process::FirstClient;
    let u=if skip {t} else {apply(dst,t,a)};
    match a {
        Action::Deliver(id) => {
            assert(s.net.pending.contains_key(id));
            if skip { assert(x.reserved.contains(id)); }
            else { assert(survivor_actor(e.actor)); assert(t.net.pending.get(id)==Some(s.net.pending[id])); }
        },
        Action::Send(id,p) => {
            assert(!x.reserved.contains(id) && !s.net.pending.contains_key(id));
            assert(!t.net.pending.contains_key(id));
        },
        _ => {},
    }
    if !skip {
        assert(survivor_actor(e.actor));
        assert((s.private)(e.actor)==(t.private)(e.actor));
        assert(process_step(t.net,a)==e);
    }
    assert forall|p:Process| survivor_actor(p) implies #[trigger] (y.cfg.private)(p)==(u.private)(p) by {
        assert((s.private)(p)==(t.private)(p));
    }
    assert forall|id:nat| y.cfg.net.pending.contains_key(id) && survivor_actor(y.cfg.net.pending[id].to)
        implies #[trigger] u.net.pending.get(id)==Some(y.cfg.net.pending[id]) by {
        match a { Action::Send(j,_) if j==id => {}, _ => {assert(t.net.pending.get(id)==Some(s.net.pending[id]));} }
    }
    assert forall|id:nat| #[trigger] u.net.pending.contains_key(id) implies y.cfg.net.pending.contains_key(id) || y.reserved.contains(id) by {
        if !y.cfg.net.pending.contains_key(id) {
            assert(t.net.pending.contains_key(id));
            if s.net.pending.contains_key(id) { assert(a==Action::<Wire>::Deliver(id) && skip); assert(x.reserved.contains(id)); }
        }
    }
    assert forall|id:nat| y.cfg.net.pending.contains_key(id) && y.cfg.net.pending[id].to==Process::FirstClient
        implies #[trigger] y.reserved.contains(id) by {
        match a { Action::Send(j,_) if j==id => {}, _ => {assert(x.reserved.contains(id));} }
    }
}

pub open spec fn retained_actions<S>(path:crate::promotion_wait::Path<State<S>,Event>,j:nat) -> Seq<Event>
    decreases path.actions.len()-j,
{
    if j>=path.actions.len() { Seq::empty() } else {
        let a=path.actions[j as int];let tail=retained_actions(path,j+1);
        if process_step(path.states[j as int].cfg.net,a).actor==Process::FirstClient {tail} else {seq![a]+tail}
    }
}

// Construct the target prefix. C1-only steps stutter. Every other step,
// including a mandatory service send or receipt, is run with its actual
// payload. The final read result is taken from the independent client's memory.
pub proof fn project_response<S>(src:Program<S>,dst:Program<S>,res:spec_fn(S)->Option<int>,
    path:crate::promotion_wait::Path<State<S>,Event>, j:nat, start:Net, ids:Set<nat>, l:Log, held:nat)
    -> (out:Log)
    requires src.accept==dst.accept,src.update==dst.update,
        path.states.len()==path.actions.len()+1,j<=path.actions.len(),
        crate::promotion_wait::valid_edges(service_step(src),path),crate::promotion_wait::pending_before(returned(res),path),
        returned(res)(path.states.last()),covers(path.states[j as int],at_end(dst,l.nets,l.actions)),
        requested_prefix(dst,res,start,ids,l.nets,l.actions),
        ids.subset_of(path.states[j as int].reserved),path.states[j as int].reserved.contains(held),
        !path.states[j as int].cfg.net.pending.contains_key(held),
        forall|i:int| 0<=i<l.actions.len() ==> #[trigger] l.actions[i]!=Action::<Wire>::Deliver(held),
    ensures response_path(dst,res,start,ids,out.nets,out.actions,
            res((at_end(dst,out.nets,out.actions).private)(Process::SecondClient)).unwrap()),
        (at_end(dst,out.nets,out.actions).private)(Process::SecondClient)==(path.states.last().cfg.private)(Process::SecondClient),
        out.actions==l.actions+retained_actions(path,j),
        out.actions.len()>=l.actions.len(),out.actions.take(l.actions.len() as int)==l.actions,
        forall|i:int| 0<=i<out.actions.len() ==> #[trigger] out.actions[i]!=Action::<Wire>::Deliver(held),
    decreases path.actions.len()-j,
{
    hide(covers); hide(requested_prefix); hide(response_path);
    let x=path.states[j as int];
    let t=at_end(dst,l.nets,l.actions);
    assert((x.cfg.private)(Process::SecondClient)==(t.private)(Process::SecondClient)) by {reveal(covers);}
    if j==path.actions.len() {
        assert(l.actions+retained_actions(path,j) =~= l.actions);
        assert(l.actions.take(l.actions.len() as int) =~= l.actions);
        assert(response_path(dst,res,start,ids,l.nets,l.actions,res((t.private)(Process::SecondClient)).unwrap())) by {
            reveal(response_path); reveal(requested_prefix);
        }
        l
    } else {
        let a=path.actions[j as int];let y=path.states[j as int+1];
        assert(service_step(src)(x,a,y));assert(!returned(res)(x));
        project_step(src,dst,x,y,t,a);
        assert(a!=Action::<Wire>::Deliver(held));
        assert(!y.cfg.net.pending.contains_key(held));
        let skipped=process_step(x.cfg.net,a).actor==Process::FirstClient;
        let u=if skipped { l } else { call::append(l,a) };
        if !skipped {
            assert(crate::confirmation::fresh_send(a,ids));
            push_event(dst,res,start,ids,l.nets,l.actions,a);
            assert forall|i:int| 0<=i<u.actions.len() implies #[trigger] u.actions[i]!=Action::<Wire>::Deliver(held)
                by { if i<l.actions.len() {assert(u.actions[i]==l.actions[i]);} }
        }
        let o=project_response(src,dst,res,path,j+1,start,ids,u,held);
        assert(l.actions+retained_actions(path,j) =~= u.actions+retained_actions(path,j+1));
        assert(o.actions.take(l.actions.len() as int) =~= l.actions) by {
            assert forall|i:int| 0<=i<l.actions.len() implies #[trigger] o.actions.take(l.actions.len() as int)[i]==l.actions[i]
                by { assert(o.actions.take(u.actions.len() as int)[i]==u.actions[i]); }
        }
        o
    }
}

}
