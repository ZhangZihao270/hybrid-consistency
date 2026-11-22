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
