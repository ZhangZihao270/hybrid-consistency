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

// The observations include the actual recipient, local cell, message body
// and protocol-visible ID. They can be compared across queue representations.
pub open spec fn same_callbacks<S>(p: Program<S>, k: Headers, x: State<S>, s: Seq<Event>,
    public: Channel<S>, ts: Seq<Turn>) -> bool
    decreases s.len(),
{
    if s.len() == 0 { ts.len() == 0 } else {
        ts.len() > 0 && callback(k,process_step(x.cfg.net,s[0])) == public_input(public.local.cfg.net,public.packets,ts[0].0)
            && same_callbacks(p,k,read::next(implementation(k,p),x,s[0]),s.drop_first(),
                apply_turn(p,public,ts[0]),ts.drop_first())
    }
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

pub proof fn return_is_trace<S>(p: Program<S>, res: spec_fn(S) -> Option<int>, x: Channel<S>, ts: Seq<Turn>)
    requires quiet_return(p, res, x, ts),
    ensures trace(p, x, ts, false),
    decreases ts.len(),
{
    if ts.len() > 0 { return_is_trace(p, res, apply_turn(p, x, ts[0]), ts.drop_first()); }
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

// The correspondence tracks occurrences individually, including equal
// messages with equal IDs. A waiting occurrence keeps its own image.
pub open spec fn represents(q: Map<nat, Message>, keys: Map<nat, nat>, encoded: Map<nat, Message>) -> bool {
    keys.dom() == q.dom() && keys.is_injective()
        && (forall|i: nat| #[trigger] keys.contains_key(i) ==> encoded.get(keys[i]) == Some(q[i]))
        && (forall|h: nat| #[trigger] encoded.contains_key(h) ==> exists|i: nat| #[trigger] keys.get(i) == Some(h))
}

pub open spec fn keys_after(keys: Map<nat, nat>, c: Command, handle: nat, a: Event) -> Map<nat, nat> {
    match c { Command::Send(_) => keys.insert(handle, a->Send_0), Command::Deliver(h) => keys.remove(h), _ => keys }
}

// Lift one step from a separately stored queue, with any independently
// chosen free enqueue handle. Receipts must consume the mapped occurrence.
pub proof fn independent_queue_step<S>(p: Program<S>, headers: Headers, x: State<S>, q: Map<nat, Message>,
    keys: Map<nat, nat>, c: Command, handle: nat, quiet: bool) -> (a: Event)
    requires represents(q, keys, queue(headers, x.cfg.net)), permitted(p, x, q, c, quiet),
        c is Send ==> !q.contains_key(handle),
    ensures ({
        let m = implementation(headers, p); let y = read::next(m, x, a);
        let e = public_input(x.cfg.net, q, c);
        native::step(m, quiet)(x, a, y) && callback(headers, process_step(x.cfg.net, a)) == e
            && (y.cfg.private)(e.actor) == (p.update)((x.cfg.private)(e.actor), e)
            && (match c {
                Command::Send(msg) => a is Send && message(headers, a->Send_0, a->Send_1) == msg,
                Command::Deliver(h) => a == Action::<Wire>::Deliver(keys[h]),
                Command::Other(event) => a == event,
            })
            && apply_turn(p, Channel { local: control(x), packets: q }, (c, handle)).local == control(y)
            && represents(queue_after(q, c, handle), keys_after(keys, c, handle, a), queue(headers, y.cfg.net))
    }),
{
    let old = queue(headers, x.cfg.net);
    let d = match c {
        Command::Deliver(i) => {
            assert(keys.contains_key(i)); assert(old.get(keys[i]) == Some(q[i]));
            Command::Deliver(keys[i])
        },
        _ => c,
    };
    let a = realize_step(p, headers, x, d, quiet, Set::empty());
    let m = implementation(headers, p); let y = read::next(m, x, a);
    project_step(p, headers, x, a, quiet);
    same_control_step(p, headers, x, Channel { local: control(x), packets: q }, c, handle, a);
    let next = queue(headers, y.cfg.net); let r = keys_after(keys, c, handle, a);
    assert forall|h: nat| #[trigger] next.contains_key(h) implies exists|i: nat| #[trigger] r.get(i) == Some(h) by {
        if a is Send && h == a->Send_0 { assert(r.get(handle) == Some(h)); }
        else {
            assert(old.contains_key(h));
            let i = choose|i: nat| #[trigger] keys.get(i) == Some(h);
            assert(r.get(i) == Some(h));
        }
    }
    assert forall|i: nat| #[trigger] r.contains_key(i) implies next.get(r[i]) == Some(queue_after(q, c, handle)[i]) by {
        if keys.contains_key(i) { assert(old.get(keys[i]) == Some(q[i])); }
    }
    assert(r.is_injective()) by {
        assert forall|i: nat, j: nat| #![auto] r.contains_key(i) && r.contains_key(j) && i != j implies r[i] != r[j] by {
            if keys.contains_key(i) { assert(old.get(keys[i]) == Some(q[i])); }
            if keys.contains_key(j) { assert(old.get(keys[j]) == Some(q[j])); }
        }
    }
    assert(r.dom() =~= queue_after(q, c, handle).dom());
    a
}

// The independent store can pick every enqueue and delivery handle in its
// finite schedule. The implementation preserves the full local endpoint
// and a bijection on every packet still in flight.
pub proof fn lift_prefix<S>(p: Program<S>, k: Headers, x: State<S>, public: Channel<S>, keys: Map<nat, nat>,
    ts: Seq<Turn>, original: bool, res: spec_fn(S) -> Option<int>) -> (result: (Seq<Event>, Map<nat, nat>))
    requires public.local == control(x), represents(public.packets, keys, queue(k, x.cfg.net)),
        trace(p, public, ts, original),
    ensures ({
        let (s, remaining) = result; let m = implementation(k, p);
        let y = asm::drive(m, x, s); let v = end(p, public, ts);
        s.len() == ts.len() && asm::prefix(m, x, s, original) && v.local == control(y)
            && represents(v.packets, remaining, queue(k, y.cfg.net))
            && same_callbacks(p,k,x,s,public,ts)
            && (native::completes(m, res, x, s, true) == quiet_return(p, res, public, ts))
    }),
    decreases ts.len(),
{
    if ts.len() == 0 { (seq![], keys) } else {
        let (c, h) = ts[0]; let m = implementation(k, p);
        let a = if original && c == Command::Other(Action::StopFirstClient) {
            let a = Action::StopFirstClient;
            same_control_step(p, k, x, public, c, h, a);
            assert(queue(k, read::next(m, x, a).cfg.net) == queue(k, x.cfg.net));
            a
        } else {
            assert(permitted(p, x, public.packets, c, false));
            independent_queue_step(p, k, x, public.packets, keys, c, h, false)
        };
        project_step(p, k, x, a, true);
        assert(public_input(public.local.cfg.net, public.packets, c) == callback(k, process_step(x.cfg.net, a)));
        let next_keys = keys_after(keys, c, h, a);
        let (tail, rest) = lift_prefix(p, k, read::next(m, x, a), apply_turn(p, public, ts[0]),
            next_keys, ts.drop_first(), original, res);
        let s = seq![a] + tail; assert(s.drop_first() =~= tail);
        (s, rest)
    }
}

// In the projection of a fair execution the obligation is for the actual
// queued occurrence, including its original recipient. The runnable-process
// predicate and process turns are those of the existing scheduler.
pub open spec fn fair_receipts<S>(k: Headers, e: crate::fair_read::Run<S>) -> bool {
    forall|i: nat, h: nat| #[trigger] queue(k, (e.state)(i).cfg.net).contains_key(h) ==> exists|j: nat| j >= i
        && (#[trigger] command(k, (e.action)(j)) == Command::Deliver(h)
            || !live((e.state)(j).cfg.net, queue(k, (e.state)(i).cfg.net)[h].body.to))
}

pub proof fn projected_fairness<S>(k: Headers, e: crate::fair_read::Run<S>, run: crate::fair_read::Runnable)
    ensures crate::fair_read::fair(e, run) == (fair_receipts(k, e) && crate::progress::process_fair(crate::fair_read::physical(e), run)),
{
    let phys = crate::fair_read::physical(e);
    if crate::progress::delivery_fair(phys) {
        assert forall|i: nat, h: nat| #[trigger] queue(k, (e.state)(i).cfg.net).contains_key(h) implies exists|j: nat| j >= i
            && (#[trigger] command(k, (e.action)(j)) == Command::Deliver(h)
                || !live((e.state)(j).cfg.net, queue(k, (e.state)(i).cfg.net)[h].body.to)) by {
            assert((phys.state)(i).pending.contains_key(h));
            let j = choose|j: nat| j >= i && (#[trigger] (phys.action)(j) == Action::Deliver(h)
                || !live((phys.state)(j), (phys.state)(i).pending[h].to));
            assert(command(k, (e.action)(j)) == Command::Deliver(h) || !live((phys.state)(j), (phys.state)(i).pending[h].to));
        }
    } else if fair_receipts(k, e) {
        assert forall|i: nat, h: nat| #[trigger] (phys.state)(i).pending.contains_key(h) implies exists|j: nat| j >= i
            && (#[trigger] (phys.action)(j) == Action::Deliver(h) || !live((phys.state)(j), (phys.state)(i).pending[h].to)) by {
            assert(queue(k, (e.state)(i).cfg.net).contains_key(h));
            let j = choose|j: nat| j >= i && (#[trigger] command(k, (e.action)(j)) == Command::Deliver(h)
                || !live((e.state)(j).cfg.net, queue(k, (e.state)(i).cfg.net)[h].body.to));
            assert((phys.action)(j) == Action::Deliver(h) || !live((phys.state)(j), (phys.state)(i).pending[h].to));
        }
    }
}

// A finite old trace embeds with its literal callback numbers as message
// IDs. The corrected transport can also admit overlapping equal IDs.
pub open spec fn literal_headers(ids: Set<nat>) -> Headers {
    Map::new(ids, |h: nat| |_body: Packet<Wire>| h)
}

pub proof fn legacy_prefix<S>(p: Program<S>, x: State<S>, s: Seq<Event>, ids: Set<nat>, original: bool)
    requires forall|j: int| 0 <= j < s.len() && slot(#[trigger] s[j]).is_some() ==> ids.contains(slot(s[j]).unwrap()),
    ensures ({
        let m = implementation(literal_headers(ids), p);
        asm::prefix(m, x, s, original) == asm::prefix(p, x, s, original)
            && asm::drive(m, x, s) == asm::drive(p, x, s)
    }),
    decreases s.len(),
{
    if s.len() > 0 {
        let a = s[0]; let e = process_step(x.cfg.net, a);
        let k = literal_headers(ids); let m = implementation(k, p);
        if slot(a).is_some() { assert(ids.contains(slot(a).unwrap())); }
        assert(callback(k, e) == e);
        assert(read::next(m, x, a).cfg.private =~= read::next(p, x, a).cfg.private);
        let tail = s.drop_first();
        assert forall|j: int| 0 <= j < tail.len() && slot(#[trigger] tail[j]).is_some()
            implies ids.contains(slot(tail[j]).unwrap()) by { assert(tail[j] == s[j+1]); }
        legacy_prefix(p, read::next(p, x, a), tail, ids, original);
    }
}

pub proof fn embed_legacy_trace<S>(p: Program<S>, x: State<S>, s: Seq<Event>, original: bool) -> (k: Headers)
    requires asm::prefix(p, x, s, original),
    ensures trace(p, snapshot(k, x), turns(k, s), original),
        end(p, snapshot(k, x), turns(k, s)) == snapshot(k, asm::drive(p, x, s)),
        forall|j: int| 0 <= j < s.len() ==> {
            let a = #[trigger] s[j]; let state = asm::drive(p, x, s.take(j));
            callback(k, process_step(state.cfg.net, a)) == process_step(state.cfg.net, a)
        },
{
    let names = s.map_values(|a: Event| if slot(a).is_some() { slot(a).unwrap() } else { 0nat });
    names.to_set_ensures();
    let ids = names.to_set(); let k = literal_headers(ids);
    assert forall|j: int| 0 <= j < s.len() && slot(#[trigger] s[j]).is_some() implies ids.contains(slot(s[j]).unwrap()) by {
        assert(ids.contains(names[j]));
    }
    legacy_prefix(p, x, s, ids, original); project_prefix(p, k, x, s, original, |_s: S| None);
    k
}

}
