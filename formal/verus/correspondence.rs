use vstd::prelude::*;
use crate::checkpoint::*;
use crate::confirmation::*;
use crate::delivery::*;
use crate::protocol::*;
use crate::service::*;
use crate::survivors::sr2_result;

verus! {

pub type Decode = spec_fn(Wire) -> Wire;
pub type Encode<S> = spec_fn(S, Wire) -> Wire;
pub type Rel<S, D> = spec_fn(Process, S, D) -> bool;

// Only ordinary strong packets sent by replicas can have a different encoding.
// The client invocation and every weak packet (including evidence) stay exact.
pub open spec fn map_packet(f: Decode, p: Packet<Wire>) -> Packet<Wire> {
    if p.from is At && p.path == Path::Strong && !crate::sr2::weak_item(p.input)
        && !crate::sr2::weak_item(f(p.input)) { Packet { input: f(p.input), ..p } } else { p }
}

pub open spec fn map_action(f: Decode, a: Action<Wire>) -> Action<Wire> {
    match a { Action::Send(id, p) => Action::Send(id, map_packet(f, p)), _ => a }
}

pub open spec fn map_incoming(f: Decode, incoming: Option<Packet<Wire>>) -> Option<Packet<Wire>> {
    match incoming { Some(p) => Some(map_packet(f, p)), None => None }
}

pub open spec fn local_event(f: Decode, e: ProcessStep<int, Wire>) -> ProcessStep<int, Wire> {
    ProcessStep { action: map_action(f, e.action), incoming: map_incoming(f, e.incoming), ..e }
}

pub open spec fn corresponding_net(f: Decode, a: Network<int, Wire>, b: Network<int, Wire>) -> bool {
    a.locals == b.locals && a.first_stopped == b.first_stopped && a.r3_crashed == b.r3_crashed
        && a.second_started == b.second_started && a.unavailable == b.unavailable
        && forall|id: nat| map_incoming(f, packet_at(a, id)) == #[trigger] map_incoming(f, packet_at(b, id))
}

pub open spec fn same_body<S>(f: Decode, encode: Encode<S>, s: S, p: Packet<Wire>) -> bool {
    map_packet(f, map_packet(|w| encode(s, w), p)) == map_packet(f, p)
}

// A sender can choose its own representation of the same logical message.
// Every accepted source event has a permitted local counterpart, including
// an actual receive with the corresponding payload. Only local handlers occur.
pub open spec fn handler_correspondence<S, D>(
    src: LocalProtocol<S, int, Wire>, dst: LocalProtocol<D, int, Wire>, f: Decode, encode: Encode<D>, rel: Rel<S, D>,
) -> bool {
    (forall|s: D, p: Packet<Wire>| #[trigger] same_body(f, encode, s, p))
    && forall|s: S, t: D, e: ProcessStep<int, Wire>, h: ProcessStep<int, Wire>|
        transport_event(e) && transport_event(h) && #[trigger] rel(e.actor, s, t) && #[trigger] (src.accept)(s, e)
            && h.action == map_action(|w| encode(t, w), e.action)
            && local_event(f, e) == #[trigger] local_event(f, h)
        ==> (dst.accept)(t, h) && rel(e.actor, (src.update)(s, e), (dst.update)(t, h))
}

pub open spec fn exact_relation<S>(
    r: crate::Replica, covers: spec_fn(S, S) -> bool, p: Process, x: S, y: S,
) -> bool {
    x == y || (p == at(r) && covers(x, y))
}

// Every old exact-event simulation embeds using the identity codec. The
// reflexive alternative handles identical states at the other processes.
pub proof fn exact_handlers_are_a_correspondence<S>(
    m: LocalProtocol<S, int, Wire>, r: crate::Replica, covers: spec_fn(S, S) -> bool,
)
    requires simulates_handlers(m, at(r), covers),
    ensures handler_correspondence(m, m, |w| w, |s, w| w, |p, x, y| exact_relation(r, covers, p, x, y)),
{
    let f = |w| w;
    assert forall|e: ProcessStep<int, Wire>| #[trigger] local_event(f, e) == e by {
        match e.action { Action::Send(_, _) => {}, _ => {} }
        match e.incoming { Some(_) => {}, None => {} }
    }
    assert forall|x: S, y: S, e: ProcessStep<int, Wire>, h: ProcessStep<int, Wire>|
        transport_event(e) && transport_event(h) && #[trigger] exact_relation(r, covers, e.actor, x, y)
        && #[trigger] (m.accept)(x, e) && local_event(f, e) == #[trigger] local_event(f, h)
        implies (m.accept)(y, h) && exact_relation(r, covers, e.actor, (m.update)(x, e), (m.update)(y, h)) by {
        assert(e == h);
    }
}

proof fn corresponding_transport_step(
    f: Decode, enc: Decode, a: Network<int, Wire>, b: Network<int, Wire>, x: Action<Wire>,
)
    requires corresponding_net(f, a, b), enabled(a, x),
        forall|p: Packet<Wire>| map_packet(f, #[trigger] map_packet(enc, p)) == map_packet(f, p),
    ensures ({
        let y = map_action(enc, x);
        enabled(b, y) && local_event(f, process_step(a, x)) == local_event(f, process_step(b, y))
            && corresponding_net(f, advance(|v, w| cell(v, w), a, x), advance(|v, w| cell(v, w), b, y))
    }),
{
    let y = map_action(enc, x);
    match x {
        Action::Send(id, _) | Action::Deliver(id) => {
            assert(map_incoming(f, packet_at(a, id)) == map_incoming(f, packet_at(b, id)));
            assert(a.pending.contains_key(id) == b.pending.contains_key(id));
        },
        _ => {},
    }
    let u = |v, w| cell(v, w);
    let post = advance(u, a, x); let post2 = advance(u, b, y);
    assert(post.locals =~= post2.locals) by {
        assert forall|r: crate::Replica| #[trigger] local_input(a, x, r) == local_input(b, y, r) by {
            if let Action::Deliver(id) = x {
                assert(map_incoming(f, packet_at(a, id)) == map_incoming(f, packet_at(b, id)));
            }
        }
    }
    assert forall|id: nat| map_incoming(f, packet_at(post, id)) == #[trigger] map_incoming(f, packet_at(post2, id)) by {
        assert(map_incoming(f, packet_at(a, id)) == map_incoming(f, packet_at(b, id)));
        match x { Action::Send(_, _) | Action::Deliver(_) => {}, _ => {} }
    }
}

proof fn memory_before_append<S>(
    m: LocalProtocol<S, int, Wire>, p: Process, es: Seq<ProcessStep<int, Wire>>, e: ProcessStep<int, Wire>, k: nat,
)
    requires k <= es.len(),
    ensures memory(m, p, es.push(e), k) == memory(m, p, es, k),
    decreases k,
{
    if k > 0 {
        memory_before_append(m, p, es, e, (k - 1) as nat);
        assert(es.push(e)[k - 1] == es[k - 1]);
    }
}

// Induct on the actual accepted source trace. Both deliver from their own
// queues. The target sender's private state supplies its outgoing header.
pub proof fn lift_handler_trace<S, D>(
    src: LocalProtocol<S, int, Wire>, dst: LocalProtocol<D, int, Wire>, f: Decode, encode: Encode<D>, rel: Rel<S, D>,
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, start: Network<int, Wire>, k: nat,
) -> (out: (Seq<Network<int, Wire>>, Seq<Action<Wire>>))
    requires k <= a.len(), trace(|v, w| cell(v, w), s, a), accepted(src, observations(s, a)),
        corresponding_net(f, s[0], start),
        handler_correspondence(src, dst, f, encode, rel),
        forall|p: Process| #[trigger] rel(p, (src.initial)(p), (dst.initial)(p)),
    ensures ({
        let (t, b) = out; let es = observations(s, a); let hs = observations(t, b);
        b.len() == k && t[0] == start && trace(|v, w| cell(v, w), t, b) && accepted(dst, hs)
            && corresponding_net(f, s[k as int], t.last())
            && (forall|i: int| 0 <= i < k ==> local_event(f, es[i]) == #[trigger] local_event(f, hs[i]))
            && (forall|p: Process| #[trigger] rel(p, memory(src, p, es, k), memory(dst, p, hs, k)))
            && (forall|i: nat| i <= k ==> #[trigger] rel(Process::SecondClient,
                memory(src, Process::SecondClient, es, i), memory(dst, Process::SecondClient, hs, i)))
    }),
    decreases k,
{
    let es = observations(s, a);
    if k == 0 {
        (seq![start], Seq::empty())
    } else {
        let j = (k - 1) as nat;
        let (t, b) = lift_handler_trace(src, dst, f, encode, rel, s, a, start, j);
        let hs = observations(t, b);
        let e = es[j as int]; let who = e.actor;
        let a0 = memory(src, who, es, j); let b0 = memory(dst, who, hs, j);
        let enc = |w| encode(b0, w);
        let raw = a[j as int]; let new = map_action(enc, raw);
        let h = process_step(t.last(), new);
        assert(enabled(s[j as int], raw) && s[k as int] == advance(|v, w| cell(v, w), s[j as int], raw));
        assert forall|p: Packet<Wire>| map_packet(f, #[trigger] map_packet(enc, p)) == map_packet(f, p) by { assert(same_body(f, encode, b0, p)); }
        corresponding_transport_step(f, enc, s[j as int], t.last(), raw);
        assert(transport_event(e) && transport_event(h)) by {
            assert(process_step(s[j as int], raw) == e && enabled(s[j as int], raw));
            assert(process_step(t.last(), new) == h && enabled(t.last(), new));
        }
        assert(rel(who, a0, b0) && (src.accept)(a0, e));
        assert((dst.accept)(b0, h) && rel(who, (src.update)(a0, e), (dst.update)(b0, h)));
        let next = advance(|v, w| cell(v, w), t.last(), new);
        let t2 = t.push(next); let b2 = b.push(new);
        let hs2 = observations(t2, b2);
        assert(hs2 =~= hs.push(h));
        assert forall|i: int| 0 <= i < k implies {
            let step = #[trigger] b2[i];
            enabled(t2[i], step) && t2[i + 1] == advance(|v, w| cell(v, w), t2[i], step)
        } by {
            if i < j { assert(b2[i] == b[i] && enabled(t[i], b[i])); }
        }
        assert forall|i: int| 0 <= i < k implies {
            let ev = #[trigger] hs2[i];
            (dst.accept)(memory(dst, ev.actor, hs2, i as nat), ev)
        } by {
            let ev = hs2[i];
            memory_before_append(dst, ev.actor, hs, h, i as nat);
            if i < j { assert(ev == hs[i]); assert((dst.accept)(memory(dst, ev.actor, hs, i as nat), ev)); }
        }
        assert forall|p: Process| #[trigger] rel(p, memory(src, p, es, k), memory(dst, p, hs2, k)) by {
            memory_before_append(dst, p, hs, h, j);
            assert(rel(p, memory(src, p, es, j), memory(dst, p, hs, j)));
            assert(hs2[j as int] == h);
        }
        let c = Process::SecondClient;
        assert forall|i: nat| i <= k implies #[trigger] rel(c, memory(src, c, es, i), memory(dst, c, hs2, i)) by {
            if i <= j {
                memory_before_append(dst, c, hs, h, i);
                assert(rel(c, memory(src, c, es, i), memory(dst, c, hs, i)));
            }
        }
        assert forall|i: int| 0 <= i < k implies local_event(f, es[i]) == #[trigger] local_event(f, hs2[i]) by {
            if i < j { assert(hs2[i] == hs[i]); assert(local_event(f, es[i]) == local_event(f, hs[i])); }
        }
        (t2, b2)
    }
}

// A legitimate one-time client invocation and the reserved slot allocation
// contract depend on roles and slots. Neither can acquire new sends in a lift.
pub(crate) proof fn lifting_preserves_invocation(
    f: Decode, s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, t: Seq<Network<int, Wire>>, b: Seq<Action<Wire>>,
    reserved: Set<nat>,
)
    requires second_invocation(s, a), a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> local_event(f, observations(s, a)[i]) == #[trigger] local_event(f, observations(t, b)[i]),
        forall|i: int| 0 <= i < a.len() ==> fresh_send(#[trigger] a[i], reserved),
    ensures second_invocation(t, b), forall|i: int| 0 <= i < b.len() ==> fresh_send(#[trigger] b[i], reserved),
{
    let es = observations(s, a); let hs = observations(t, b); let c = Process::SecondClient;
    assert forall|i: int| 0 <= i < b.len() implies
        map_action(f, a[i]) == #[trigger] map_action(f, b[i])
        && es[i].actor == hs[i].actor && es[i].incoming.is_none() == hs[i].incoming.is_none() by {
        assert(local_event(f, es[i]) == local_event(f, hs[i]));
    }
    assert forall|i: int, r: crate::Replica| 0 <= i < a.len() implies
        client_sends_to(a[i], c, r) == #[trigger] client_sends_to(b[i], c, r) by { assert(map_action(f, a[i]) == map_action(f, b[i])); }
    assert forall|i: int| 0 <= i < b.len() implies {
        let x = #[trigger] b[i];
        fresh_send(x, reserved) && match x {
            Action::Send(_, p) if p.from == c => invocation_packet(p) && live_pair().contains(p.to->At_0)
                && (forall|j: int| 0 <= j < i ==> !client_sends_to(#[trigger] b[j], c, p.to->At_0)),
            _ => true,
        }
    } by {
        assert(map_action(f, a[i]) == map_action(f, b[i]));
        if let Action::Send(_, p) = b[i] {
            if p.from == c { assert(a[i] == b[i]); }
        }
    }
    assert forall|r: crate::Replica| #[trigger] live_pair().contains(r) implies exists|i: int|
        0 <= i < b.len() && client_sends_to(#[trigger] b[i], c, r) by {
        let i = choose|i: int| 0 <= i < a.len() && client_sends_to(#[trigger] a[i], c, r);
        assert(client_sends_to(b[i], c, r));
    }
    assert forall|j: int, i: int| 0 <= j < i < hs.len() implies match (#[trigger] hs[i]).action {
        Action::Send(_, p) if p.from == c => (#[trigger] hs[j]).actor != c || hs[j].incoming.is_none(),
        _ => true,
    } by {
        assert(map_action(f, a[i]) == map_action(f, b[i]));
        assert(map_action(f, a[j]) == map_action(f, b[j]));
        assert(local_event(f, es[j]) == local_event(f, hs[j]));
        if let Action::Send(_, p) = b[i] {
            if p.from == c { assert(es[i].action == b[i]); assert(es[j].actor != c || es[j].incoming.is_none()); }
        }
    }
}

pub proof fn translate_response<S, D>(
    src: LocalProtocol<S, int, Wire>, dst: LocalProtocol<D, int, Wire>, f: Decode, encode: Encode<D>, rel: Rel<S, D>,
    net: Network<int, Wire>, reserved: Set<nat>, source_result: spec_fn(S) -> Option<int>, target_result: spec_fn(D) -> Option<int>,
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
) -> (out: (Seq<Network<int, Wire>>, Seq<Action<Wire>>, int))
    requires response_path(src, source_result, net, reserved, s, a, v),
        handler_correspondence(src, dst, f, encode, rel),
        forall|p: Process| #[trigger] rel(p, (src.initial)(p), (dst.initial)(p)),
        target_result((dst.initial)(Process::SecondClient)).is_none(),
        forall|x: S, y: D| #[trigger] rel(Process::SecondClient, x, y) ==> source_result(x).is_some() == target_result(y).is_some(),
    ensures ({
        let (t, b, value) = out; let es = observations(s, a); let hs = observations(t, b);
        response_path(dst, target_result, net, reserved, t, b, value) && b.len() == a.len()
            && rel(Process::SecondClient, memory(src, Process::SecondClient, es, es.len()), memory(dst, Process::SecondClient, hs, hs.len()))
            && (forall|i: int| 0 <= i < a.len() ==> local_event(f, es[i]) == #[trigger] local_event(f, hs[i]))
            && (forall|p: Process| #[trigger] rel(p, memory(src, p, es, es.len()), memory(dst, p, hs, hs.len())))
    }),
{
    let (t, b) = lift_handler_trace(src, dst, f, encode, rel, s, a, net, a.len());
    lifting_preserves_invocation(f, s, a, t, b, reserved);
    let c = Process::SecondClient;
    assert(rel(c, memory(src, c, observations(s, a), a.len()), memory(dst, c, observations(t, b), b.len())));
    let es = observations(s, a); let hs = observations(t, b);
    assert forall|i: nat| i < hs.len() implies target_result(#[trigger] memory(dst, c, hs, i)).is_none() by {
        assert(rel(c, memory(src, c, es, i), memory(dst, c, hs, i)));
        assert(source_result(memory(src, c, es, i)).is_none());
    }
    let value = sr2_result(dst, target_result, observations(t, b)).unwrap();
    (t, b, value)
}

pub proof fn local_correspondence_preserves_service<S, D>(
    src: LocalProtocol<S, int, Wire>, dst: LocalProtocol<D, int, Wire>, f: Decode, encode: Encode<D>, rel: Rel<S, D>,
    net: Network<int, Wire>, reserved: Set<nat>, source_result: spec_fn(S) -> Option<int>, target_result: spec_fn(D) -> Option<int>,
)
    requires can_respond(src, source_result, net, reserved),
        handler_correspondence(src, dst, f, encode, rel),
        forall|p: Process| #[trigger] rel(p, (src.initial)(p), (dst.initial)(p)),
        target_result((dst.initial)(Process::SecondClient)).is_none(),
        forall|x: S, y: D| #[trigger] rel(Process::SecondClient, x, y) ==> source_result(x).is_some() == target_result(y).is_some(),
    ensures can_respond(dst, target_result, net, reserved),
{
    let (s, a, v) = choose|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
        #[trigger] response_path(src, source_result, net, reserved, s, a, v);
    let (t, b, value) = translate_response(src, dst, f, encode, rel, net, reserved, source_result, target_result, s, a, v);
    assert(response_path(dst, target_result, net, reserved, t, b, value));
}

// For this stepwise correspondence only the pending/returned phase is shared. Any value of the translated held response will do: H compares
// that actual response with its replay in the other held run.
pub proof fn fair_quorum_with_corresponding_messages<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    f: Decode, encode: Encode<S>, rel: Rel<S, S>, e: crate::progress::Execution<int, Wire>,
    runnable: spec_fn(Network<int, Wire>, Process) -> bool,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        ({
            let before = resume_at(m, checkpoint_observations(alpha(n)));
            let ack = receipt_event(n); let local = (before.initial)(ack.actor);
            (m.accept)(local, ack) && rel(ack.actor, (m.update)(local, ack), local)
        }),
        forall|p: Process, s: S| #[trigger] rel(p, s, s),
        handler_correspondence(m, m, f, encode, rel),
        forall|x: S, y: S| #[trigger] rel(Process::SecondClient, x, y) ==> result(x).is_some() == result(y).is_some(),
        admissible_reference(n, m, result, e), crate::progress::delivery_fair(e), crate::progress::process_fair(e, runnable),
        crate::progress::eventually_responds(e, runnable, |s, a| reference_response(n, m, result, s, a).is_some()),
    ensures exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v),
{
    let pre = resume_at(m, checkpoint_observations(alpha(n)));
    let post = reference_machine(m, n);
    let (k, v) = finite_fair_reference_response(n, m, result, e, runnable);
    let s = crate::progress::states_through(e, k); let a = crate::progress::actions_before(e, k);
    assert(response_path(post, result, after_receipt(n), delayed_slots(), s, a, v));
    alpha_receipt_cut(n);
    assert forall|p: Process| #[trigger] rel(p, (post.initial)(p), (pre.initial)(p)) by { reveal_with_fuel(memory, 2); }
    assert((pre.initial)(Process::SecondClient) == (post.initial)(Process::SecondClient)) by { reveal_with_fuel(memory, 2); }
    local_correspondence_preserves_service(post, pre, f, encode, rel, after_receipt(n), delayed_slots(), result, result);
    service_before_receipt_yields_actual_pair(n, m, first, result);
}

}
