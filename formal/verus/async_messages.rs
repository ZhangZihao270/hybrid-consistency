// A send proposes a message, including its application-supplied ID. Only
// the scheduler selects a queue occurrence for delivery.
use vstd::prelude::*;
use crate::checkpoint::Wire;
use crate::delivery::{Action, Packet, Path, Process, enabled, live, process_step};
use crate::first_assembly as asm;
use crate::first_splice::{Observation, slot};
use crate::guarded_comparison::weak_work;
use crate::independent_read::{self as read, State};
use crate::native_fork as native;
use crate::protocol::LocalProtocol;
use crate::read_call::{Event, Net, Program};

verus! {

pub struct Message { pub id: nat, pub body: Packet<Wire> }
pub enum Command { Send(Message), Deliver(nat), Other(Event) }

// A representation of (message ID, occurrence) in the existing nat-keyed
// queue. Every ID has arbitrarily many representations. Finite overrides
// allow the existing workload prefix to carry any chosen application IDs.
pub type Headers = Map<nat, spec_fn(Packet<Wire>) -> nat>;

pub closed spec fn unpack(h: nat) -> nat
    decreases h,
{
    if h % 2 == 0 { h / 2 } else { unpack(h / 2) }
}

pub open spec fn message(headers: Headers, h: nat, body: Packet<Wire>) -> Message {
    Message { id: if headers.contains_key(h) { (headers[h])(body) } else { unpack(h) }, body }
}

pub open spec fn queue(headers: Headers, n: Net) -> Map<nat, Message> {
    Map::new(n.pending.dom(), |h: nat| message(headers, h, n.pending[h]))
}

proof fn above(set: Set<nat>) -> (n: nat)
    ensures forall|i: nat| #[trigger] set.contains(i) ==> i < n,
    decreases set.len(),
{
    if set.is_empty() { 0 } else {
        let h = set.choose();
        let b = above(set.remove(h));
        b + h + 1
    }
}

proof fn encode_above(id: nat, bound: nat) -> (h: nat)
    ensures h >= bound, unpack(h) == id,
    decreases bound,
{
    if bound == 0 { 2 * id } else {
        let j = encode_above(id, (bound - 1) as nat);
        let h = 2 * j + 1;
        assert(h / 2 == j && h % 2 == 1);
        h
    }
}

// The program uses the original callback data types. Their message number
// now comes from the payload for both the send and the actual receipt.
pub open spec fn callback(headers: Headers, e: Observation) -> Observation {
    Observation { action: match e.action {
        Action::Send(h, p) => Action::Send(message(headers, h, p).id, p),
        Action::Deliver(h) if e.incoming.is_some() =>
            Action::Deliver(message(headers, h, e.incoming.unwrap()).id),
        _ => e.action,
    }, ..e }
}

pub open spec fn implementation<S>(headers: Headers, p: Program<S>) -> Program<S> {
    LocalProtocol { initial: p.initial, done: p.done,
        accept: |s: S, e: Observation| (p.accept)(s, callback(headers, e)),
        update: |s: S, e: Observation| (p.update)(s, callback(headers, e)) }
}

pub open spec fn command(headers: Headers, a: Event) -> Command {
    match a {
        Action::Send(h, p) => Command::Send(message(headers, h, p)),
        Action::Deliver(h) => Command::Deliver(h),
        _ => Command::Other(a),
    }
}

// Independent store specification. Its entries carry the complete public
// message. In particular, receipt chooses h but passes msg.id to the code.
pub open spec fn public_input(n: Net, packets: Map<nat, Message>, c: Command) -> Observation {
    match c {
        Command::Send(msg) => process_step(n, Action::Send(msg.id, msg.body)),
        Command::Deliver(h) => {
            let msg = packets[h]; let actor = msg.body.to;
            Observation { actor, action: Action::Deliver(msg.id), incoming: Some(msg.body),
                own_local: match actor { Process::At(r) => Some((n.locals)(r)), _ => None } }
        },
        Command::Other(a) => process_step(n, a),
    }
}

pub open spec fn permitted<S>(p: Program<S>, x: State<S>, packets: Map<nat, Message>, c: Command, quiet: bool) -> bool {
    let n = x.cfg.net;
    let e = public_input(n, packets, c);
    let accepts = (p.accept)((x.cfg.private)(e.actor), e);
    (!quiet || !weak_work(e)) && match c {
        Command::Send(msg) => live(n, msg.body.from)
            && (msg.body.path != Path::FirstReadReply || msg.body.to == Process::FirstClient)
            && read::initial_send(x, Action::Send(msg.id, msg.body)) && accepts,
        Command::Deliver(h) => packets.contains_key(h) && live(n, packets[h].body.to) && accepts,
        Command::Other(a) => slot(a).is_none() && match a {
            Action::CrashR3 => enabled(n, a) && n.unavailable.is_none(),
            Action::StartSecondClient => !n.second_started && accepts,
            _ => enabled(n, a) && accepts,
        },
    }
}

pub open spec fn input(headers: Headers, n: Net, c: Command) -> Observation {
    public_input(n, queue(headers, n), c)
}
pub open spec fn ready<S>(p: Program<S>, headers: Headers, x: State<S>, c: Command, quiet: bool) -> bool {
    permitted(p, x, queue(headers, x.cfg.net), c, quiet)
}

pub open spec fn allocatable<S>(x: State<S>, a: Event) -> bool {
    match a {
        Action::Send(h, _) => !x.cfg.net.pending.contains_key(h) && !x.reserved.contains(h) && read::names_sender(x, a),
        _ => true,
    }
}

// Exact guarded projection, with the actual post-queue and local update.
pub proof fn project_step<S>(p: Program<S>, headers: Headers, x: State<S>, a: Event, quiet: bool)
    ensures ({
        let m = implementation(headers, p); let y = read::next(m, x, a);
        let c = command(headers, a); let e = input(headers, x.cfg.net, c);
        (native::step(m, quiet)(x, a, y) == (ready(p, headers, x, c, quiet) && allocatable(x, a)))
        && (native::step(m, quiet)(x, a, y) ==>
            e == callback(headers, process_step(x.cfg.net, a))
            && (y.cfg.private)(e.actor) == (p.update)((x.cfg.private)(e.actor), e)
            && queue(headers, y.cfg.net) == match a {
                Action::Send(h, body) => queue(headers, x.cfg.net).insert(h, message(headers, h, body)),
                Action::Deliver(h) => queue(headers, x.cfg.net).remove(h),
                _ => queue(headers, x.cfg.net),
            })
    }),
{
    let m = implementation(headers, p); let y = read::next(m, x, a);
    match a {
        Action::Send(h, body) => {
            assert(queue(headers, y.cfg.net) =~= queue(headers, x.cfg.net).insert(h, message(headers, h, body)));
        },
        Action::Deliver(h) => { assert(queue(headers, y.cfg.net) =~= queue(headers, x.cfg.net).remove(h)); },
        _ => { assert(queue(headers, y.cfg.net) =~= queue(headers, x.cfg.net)); },
    }
}

// A logical send has a real implementation outside ANY finite set of
// handles. Receipts keep the selected occurrence, even if it is in avoid.
pub proof fn realize_step<S>(p: Program<S>, headers: Headers, x: State<S>, c: Command, quiet: bool,
    avoid: Set<nat>) -> (a: Event)
    requires ready(p, headers, x, c, quiet),
    ensures ({
        let m = implementation(headers, p);
        command(headers, a) == c && !native::masks_send(avoid, a)
            && native::step(m, quiet)(x, a, read::next(m, x, a))
            && callback(headers, process_step(x.cfg.net, a)) == input(headers, x.cfg.net, c)
    }),
{
    let a = match c {
        Command::Send(msg) => {
            let used = x.cfg.net.pending.dom().union(x.reserved).union(x.owners.dom()).union(headers.dom()).union(avoid);
            let bound = above(used);
            let h = encode_above(msg.id, bound);
            assert(!used.contains(h));
            Action::Send(h, msg.body)
        },
        Command::Deliver(h) => Action::Deliver(h),
        Command::Other(a) => a,
    };
    project_step(p, headers, x, a, quiet);
    a
}

pub open spec fn queue_after(q: Map<nat, Message>, c: Command, handle: nat) -> Map<nat, Message> {
    match c { Command::Send(msg) => q.insert(handle, msg), Command::Deliver(h) => q.remove(h), _ => q }
}

// Use the existing cell, client and process transitions for the selected
// callback. All queued packets live in packets. The auxiliary State
// carries only process state, liveness and invocation data across turns.
pub struct Channel<S> { pub local: State<S>, pub packets: Map<nat, Message> }
pub type Turn = (Command, nat); // The second component allocates a Send.

pub open spec fn control<S>(x: State<S>) -> State<S> {
    State { owners: Map::empty(), reserved: Set::empty(),
        cfg: crate::ordinary_service::Configuration { net: Net { pending: Map::empty(), ..x.cfg.net }, ..x.cfg }, ..x }
}
pub open spec fn snapshot<S>(k: Headers, x: State<S>) -> Channel<S> {
    Channel { local: control(x), packets: queue(k, x.cfg.net) }
}

pub open spec fn apply_turn<S>(p: Program<S>, x: Channel<S>, t: Turn) -> Channel<S> {
    let e = public_input(x.local.cfg.net, x.packets, t.0);
    // Give the cell transition exactly the received body at the callback's
    // public ID. This temporary map describes one input to read::next.
    let incoming = match t.0 {
        Command::Deliver(h) => map![x.packets[h].id => x.packets[h].body],
        _ => Map::empty(),
    };
    let one = State { cfg: crate::ordinary_service::Configuration {
        net: Net { pending: incoming, ..x.local.cfg.net }, ..x.local.cfg }, ..x.local };
    Channel { local: control(read::next(p, one, e.action)), packets: queue_after(x.packets, t.0, t.1) }
}

pub open spec fn turn_enabled<S>(p: Program<S>, x: Channel<S>, t: Turn, original: bool) -> bool {
    (t.0 is Send ==> !x.packets.contains_key(t.1)) && if original && t.0 == Command::Other(Action::StopFirstClient) {
        !x.local.cfg.net.first_stopped && crate::first_mailbox::posted(p)(x.local)
    } else { permitted(p, x.local, x.packets, t.0, false) }
}

pub open spec fn printed(headers: Headers, a: Event) -> Turn {
    (command(headers, a), if a is Send { a->Send_0 } else { 0 })
}

pub open spec fn trace<S>(p: Program<S>, x: Channel<S>, turns: Seq<Turn>, original: bool) -> bool
    decreases turns.len(),
{
    turns.len() == 0 || (turn_enabled(p, x, turns[0], original)
        && trace(p, apply_turn(p, x, turns[0]), turns.drop_first(), original))
}
pub open spec fn end<S>(p: Program<S>, x: Channel<S>, turns: Seq<Turn>) -> Channel<S>
    decreases turns.len(),
{
    if turns.len() == 0 { x } else { end(p, apply_turn(p, x, turns[0]), turns.drop_first()) }
}
pub open spec fn turns(headers: Headers, s: Seq<Event>) -> Seq<Turn> {
    s.map_values(|a: Event| printed(headers, a))
}

pub open spec fn quiet_return<S>(p: Program<S>, res: spec_fn(S) -> Option<int>, x: Channel<S>, ts: Seq<Turn>) -> bool
    decreases ts.len(),
{
    if ts.len() == 0 { read::returned(res)(x.local) } else {
        let (c, h) = ts[0];
        !read::returned(res)(x.local) && (c is Send ==> !x.packets.contains_key(h))
            && permitted(p, x.local, x.packets, c, true) && quiet_return(p, res, apply_turn(p, x, ts[0]), ts.drop_first())
    }
}

proof fn same_control_step<S>(p: Program<S>, k: Headers, x: State<S>, public: Channel<S>, c: Command,
    handle: nat, a: Event)
    requires public.local == control(x),
        callback(k, process_step(x.cfg.net, a)) == public_input(public.local.cfg.net, public.packets, c),
        match c {
            Command::Send(msg) => a is Send && message(k, a->Send_0, a->Send_1) == msg,
            Command::Deliver(h) => a is Deliver && public.packets.contains_key(h)
                && queue(k, x.cfg.net).get(a->Deliver_0) == Some(public.packets[h]),
            Command::Other(event) => event == a && slot(event).is_none(),
        },
    ensures apply_turn(p, public, (c, handle)).local == control(read::next(implementation(k, p), x, a)),
{
    let y = read::next(implementation(k, p), x, a); let v = apply_turn(p, public, (c, handle)).local;
    assert(v.cfg.private =~= y.cfg.private);
    assert(v.cfg.net.locals =~= y.cfg.net.locals);
}

pub proof fn project_prefix<S>(p: Program<S>, k: Headers, x: State<S>, s: Seq<Event>, original: bool,
    res: spec_fn(S) -> Option<int>)
    requires asm::prefix(implementation(k, p), x, s, original),
    ensures trace(p, snapshot(k, x), turns(k, s), original),
        end(p, snapshot(k, x), turns(k, s)) == snapshot(k, asm::drive(implementation(k, p), x, s)),
        quiet_return(p, res, snapshot(k, x), turns(k, s)) == native::completes(implementation(k, p), res, x, s, true),
    decreases s.len(),
{
    if s.len() > 0 {
        let a = s[0]; let m = implementation(k, p); let y = read::next(m, x, a);
        let c = command(k, a); let t = printed(k, a); let initial = snapshot(k, x);
        if !original || a != Action::StopFirstClient { project_step(p, k, x, a, false); }
        project_step(p, k, x, a, true);
        assert(turn_enabled(p, initial, t, original));
        assert(public_input(initial.local.cfg.net, initial.packets, c) == callback(k, process_step(x.cfg.net, a)));
        same_control_step(p, k, x, initial, c, t.1, a);
        assert(apply_turn(p, initial, t).packets =~= queue(k, y.cfg.net));
        assert(turns(k, s).drop_first() =~= turns(k, s.drop_first()));
        project_prefix(p, k, y, s.drop_first(), original, res);
    }
}

}
