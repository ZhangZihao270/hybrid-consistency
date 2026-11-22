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
