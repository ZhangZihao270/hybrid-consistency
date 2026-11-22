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
