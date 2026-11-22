use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::*;
use crate::correspondence::*;
use crate::delivery::*;
use crate::progress::*;
use crate::protocol::*;
use crate::service::*;
use crate::survivors::*;

verus! {

// Read-only stock service may issue and receive its mandatory protocol
// traffic, use clocks and run local steps. No other application write or
// weak background delivery is needed in this reference.
pub open spec fn stock_work(e: ProcessStep<int, Wire>) -> bool {
    match e.action {
        Action::Send(_, p) => crate::sr2::ordinary_packet(p),
        Action::Deliver(_) => e.incoming.is_some() && crate::sr2::ordinary_packet(e.incoming.unwrap()),
        Action::Local(_, w) | Action::ClientInput(_, w) => !crate::sr2::weak_item(w),
        _ => true,
    }
}

// Incoming weak data, status and application inputs stay outside the
// translated read on both actual transports. The other queue entries
// remain in flight.
pub open spec fn ordinary_suffix(b: Fork, a: Seq<Action<Wire>>) -> bool {
    let t = replay(|x, w| cell(x, w), checkpoint_end(b), a);
    forall|i: int| 0 <= i < a.len() ==> stock_work(#[trigger] observations(t, a)[i])
}

proof fn codec_preserves_work(f: Decode, e: ProcessStep<int, Wire>)
    ensures stock_work(local_event(f, e)) == stock_work(e),
{
    match e.action {
        Action::Send(_, _) => {},
        Action::Deliver(_) => { match e.incoming { Some(_) => {}, None => {} } },
        _ => {},
    }
}

pub open spec fn stock_cut(stock: Network<int, Wire>, ordinary: Network<int, Wire>) -> bool {
    after_crash(stock)
        && (forall|id: nat| #[trigger] delayed_slots().contains(id) ==> absent_or_dead(stock, id))
        && (forall|id: nat| !delayed_slots().contains(id) ==> packet_at(stock, id) == #[trigger] packet_at(ordinary, id))
}

pub open spec fn with_cells(net: Network<int, Wire>, value: spec_fn(Replica) -> int) -> Network<int, Wire> {
    Network { locals: value, ..net }
}

pub open spec fn cell_at_actor(e: ProcessStep<int, Wire>, value: spec_fn(Replica) -> int) -> ProcessStep<int, Wire> {
    ProcessStep { own_local: match e.actor { Process::At(r) => Some(value(r)), _ => None }, ..e }
}

// This wrapper represents the source on the common transport used by the
// local correspondence. Only the source sees its stock register values.
pub open spec fn stock_source<S>(m: LocalProtocol<S, int, Wire>, value: spec_fn(Replica) -> int, actual: spec_fn(Replica) -> int)
    -> LocalProtocol<S, int, Wire>
{
    LocalProtocol {
        accept: |s, e| stock_work(e) && cell_at_actor(e, actual) == e && (m.accept)(s, cell_at_actor(e, value)),
        update: |s, e| (m.update)(s, cell_at_actor(e, value)),
        ..m
    }
}

proof fn stationary_cells(
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, k: nat,
)
    requires trace(|x, w| cell(x, w), s, a), k <= a.len(),
        forall|i: int| 0 <= i < a.len() ==> stock_work(#[trigger] observations(s, a)[i]),
    ensures s[k as int].locals == s[0].locals,
    decreases k,
{
    if k > 0 {
        let j = (k - 1) as nat; stationary_cells(s, a, j);
        assert(stock_work(observations(s, a)[j as int]));
        assert(s[k as int] == advance(|x, w| cell(x, w), s[j as int], a[j as int]));
        assert(s[k as int].locals =~= s[j as int].locals) by {
            match a[j as int] { Action::Local(_, _) | Action::Deliver(_) => {}, _ => {} }
        }
    }
}

proof fn source_memory<S>(
    m: LocalProtocol<S, int, Wire>, cells: spec_fn(Replica) -> int, actual: spec_fn(Replica) -> int, es: Seq<ProcessStep<int, Wire>>, hs: Seq<ProcessStep<int, Wire>>,
    p: Process, k: nat,
)
    requires es.len() == hs.len(), k <= es.len(),
        forall|i: int| 0 <= i < es.len() ==> #[trigger] cell_at_actor(hs[i], cells) == es[i],
    ensures memory(stock_source(m, cells, actual), p, hs, k) == memory(m, p, es, k),
    decreases k,
{
    if k > 0 { source_memory(m, cells, actual, es, hs, p, (k - 1) as nat); assert(cell_at_actor(hs[k - 1], cells) == es[k - 1]); }
}

// Move an ordinary stock read onto the actual comparison transport. Keep
// all source actions and wire contents here. The later handler induction
// lets the hybrid sender issue different bytes and real shared-cell values.
pub proof fn put_stock_read_on_transport<S>(
    m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, n: Notice,
    s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires response_path(m, result, s[0], delayed_slots(), s, a, v), stock_cut(s[0], after_receipt(n)),
        forall|i: int| 0 <= i < a.len() ==> stock_work(#[trigger] observations(s, a)[i]),
    ensures ({
        let net = after_receipt(n);
        let t = replay(|x, w| cell(x, w), net, a);
        response_path(stock_source(m, s[0].locals, net.locals), result, net, delayed_slots(), t, a, v)
    }),
{
    hide(memory); hide(replay); hide(accepted);
    let up = |x, w| cell(x, w);
    let net = after_receipt(n);
    let old = s[0].locals;
    let src = stock_source(m, old, net.locals);
    let t = Seq::new(s.len(), |i: int| with_cells(s[i], net.locals));
    let es = observations(s, a);
    let hs = observations(t, a);
    assert forall|i: int| 0 <= i < a.len() implies {
        let x = #[trigger] a[i]; enabled(t[i], x) && t[i + 1] == advance(up, t[i], x)
            && cell_at_actor(hs[i], old) == es[i] && stock_work(hs[i]) && cell_at_actor(hs[i], net.locals) == hs[i]
    } by {
        stationary_cells(s, a, i as nat);
        assert(stock_work(es[i]) && enabled(s[i], a[i]) && s[i + 1] == advance(up, s[i], a[i]));
        let post = advance(up, t[i], a[i]);
        assert(post.locals =~= t[i + 1].locals) by { match a[i] { Action::Local(_, _) | Action::Deliver(_) => {}, _ => {} } }
    }
    assert forall|i: int| 0 <= i < hs.len() implies {
        let e = #[trigger] hs[i]; (src.accept)(memory(src, e.actor, hs, i as nat), e)
    } by {
        assert(cell_at_actor(hs[i], old) == es[i]);
        assert((m.accept)(memory(m, es[i].actor, es, i as nat), es[i])) by { reveal(accepted); }
        source_memory(m, old, net.locals, es, hs, hs[i].actor, i as nat);
    }
    assert forall|k: nat| k < hs.len() implies result(#[trigger] memory(src, Process::SecondClient, hs, k)).is_none() by {
        source_memory(m, old, net.locals, es, hs, Process::SecondClient, k); assert(result(memory(m, Process::SecondClient, es, k)).is_none());
    }
    source_memory(m, old, net.locals, es, hs, Process::SecondClient, a.len());
    assert forall|j: int, i: int| 0 <= j < i < hs.len() implies match (#[trigger] hs[i]).action {
        Action::Send(_, p) if p.from == Process::SecondClient => (#[trigger] hs[j]).actor != p.from || hs[j].incoming.is_none(),
        _ => true,
    } by {
        assert(cell_at_actor(hs[i], old) == es[i] && cell_at_actor(hs[j], old) == es[j]);
        if let Action::Send(_, p) = hs[i].action { if p.from == Process::SecondClient {
            assert(es[j].actor != p.from || es[j].incoming.is_none());
        } }
    }
    assert forall|i: int| 0 <= i < a.len() implies keeps_delayed_slots(#[trigger] a[i], delayed_slots()) by {
        assert forall|id: nat| #[trigger] delayed_slots().contains(id) implies crate::scheduling::untouched_slot(a[i], id)
            by { stale_slot_cannot_be_delivered(up, s, a, delayed_slots(), id, i as nat); }
    }
    alpha_receipt_cut(n);
    assert(outside_delays(t[0], net, delayed_slots()));
    replay_sr2_without_touching_delayed_slots(up, t, net, a, delayed_slots());
    assert(replay(up, net, a)[0] == net) by { reveal(replay); }
    assert(accepted(src, hs)) by { reveal(accepted); }
}

pub open spec fn read_only_until_return<S>(
    base: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, e: Execution<int, Wire>,
) -> bool {
    forall|i: nat| (forall|j: nat| j <= i ==> sr2_result(base, result,
        #[trigger] observations(states_through(e, j), actions_before(e, j))).is_none())
        ==> stock_work(process_step((e.state)(i), #[trigger] (e.action)(i)))
}

// Stock liveness is used only on the supplied stock execution. Application
// to the paper requires it to start at a reachable state of the underlying
// SMR. The extra operation-level refinement transfers a finite first return;
// the hybrid registers and the returned value may differ from the stock ones.
pub proof fn stock_availability_gives_held_response<B, S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>,
    base: LocalProtocol<B, int, Wire>, base_result: spec_fn(B) -> Option<int>, start: Network<int, Wire>,
    e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
    f: Decode, encode: Encode<S>, rel: Rel<B, S>,
) -> (answer: (Seq<Action<Wire>>, int))
    requires stock_cut(start, after_receipt(n)), admissible_service(start, base, base_result, e),
        delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| sr2_result(base, base_result, observations(s, a)).is_some()),
        read_only_until_return(base, base_result, e),
        handler_correspondence(stock_source(base, start.locals, after_receipt(n).locals), m, f, encode, rel),
        forall|p: Process| #[trigger] rel(p, (base.initial)(p), (m.initial)(p)),
        forall|x: B, y: S| #[trigger] rel(Process::SecondClient, x, y) ==> base_result(x).is_some() == result(y).is_some(),
    ensures ({
        let (a, v) = answer;
        let net = checkpoint_end(alpha(n));
        let t = replay(|x, w| cell(x, w), net, a);
        response_path(m, result, net, delayed_slots(), t, a, v) && can_release(alpha(n), a) && ordinary_suffix(alpha(n), a)
            && forall|i: int| 0 <= i<a.len() ==> keeps_delayed_slots(#[trigger] a[i], delayed_slots())
    }),
{
    hide(accepted); hide(trace); hide(eventually_responds); hide(memory); hide(admissible_service);
    hide(process_fair); hide(delivery_fair); hide(incompatible_completions);
    let (k, v) = finite_fair_service(start, base, base_result, e, runnable);
    let s = states_through(e, k);
    let a = actions_before(e, k);
    let net = after_receipt(n);
    assert(response_path(base, base_result, start, delayed_slots(), s, a, v));
    assert forall|i: int| 0 <= i < a.len() implies stock_work(#[trigger] observations(s, a)[i]) by {
        assert(a[i] == (e.action)(i as nat) && s[i] == (e.state)(i as nat));
        let es = observations(s, a);
        assert forall|j: nat| j <= i implies sr2_result(base, base_result,
            #[trigger] observations(states_through(e, j), actions_before(e, j))).is_none() by {
            let short = observations(states_through(e, j), actions_before(e, j));
            assert forall|h: int| 0 <= h<j implies #[trigger] short[h] == #[trigger] es[h] by {};
            memory_on_common_prefix(base, Process::SecondClient, short, es, j);
            assert(base_result(memory(base, Process::SecondClient, es, j)).is_none());
        }
    }
    put_stock_read_on_transport(base, base_result, n, s, a, v);
    let src = stock_source(base, start.locals, net.locals);
    let dst = m;
    let t = replay(|x, w| cell(x, w), net, a);
    assert(response_path(src, base_result, net, delayed_slots(), t, a, v));
    assert(rel(Process::SecondClient, (base.initial)(Process::SecondClient), (dst.initial)(Process::SecondClient)));
    let (hs, ha, hv) = translate_response(src, dst, f, encode, rel, net, delayed_slots(), base_result, result, t, a, v);
    let source = observations(t, a);
    let target = observations(hs, ha);
    assert forall|i: int| 0 <= i < ha.len() implies stock_work(#[trigger] target[i]) by {
        let ev = source[i];
        assert((src.accept)(memory(src, ev.actor, source, i as nat), ev)) by { reveal(accepted); }
        assert(local_event(f, ev) == local_event(f, target[i]));
        codec_preserves_work(f, ev);
        codec_preserves_work(f, target[i]);
    }
    existing_notice_is_the_only_extra_opportunity(n, dst, result, hs, ha, hv);
    (ha, hv)
}

// Preserve the whole ordinary suffix, including any mandatory strong
// protocol traffic. Neither execution processes new weak work before SR2.
pub(crate) proof fn ordinary_path_is_hot_pair<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    t: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        response_path(resume_at(m, checkpoint_observations(alpha(n))), result, checkpoint_end(alpha(n)), delayed_slots(), t, a, v),
        forall|i: int| 0 <= i < a.len() ==> stock_work(#[trigger] observations(t, a)[i]),
    ensures incompatible_completions(n, m, first, result, a, v), ordinary_suffix(alpha(n), a), ordinary_suffix(beta(n), a),
{
    hide(accepted); hide(memory); hide(incompatible_completions); hide(replay);
    let net = checkpoint_end(alpha(n));
    let dst = resume_at(m, checkpoint_observations(alpha(n)));
    if consumed_issue(net, 2, t, a) {
        let i = choose|i: int| 0 <= i < a.len() && #[trigger] a[i] == Action::Deliver(2)
            && observations(t, a)[i].incoming == Some(net.pending[2]);
        assert(stock_work(observations(t, a)[i]));
    }
    path_without_notice_preserves_delays(n, dst, result, t, a, v);
    let up = |x, w| cell(x, w);
    held_path_is_an_ordinary_opportunity(n, dst, result, t, a, v);
    pair_from_ordinary_path(n, m, first, result, replay(up, after_receipt(n), a), a, v);
    surviving_checkpoint_agreement(n);
    replay_sr2_without_touching_delayed_slots(up, t, net, a, delayed_slots());
    replay_sr2_without_touching_delayed_slots(up, t, checkpoint_end(beta(n)), a, delayed_slots());
}

pub open spec fn needs_other_weak_traffic<S>(
    pre: LocalProtocol<S, int, Wire>, result: spec_fn(S) -> Option<int>, net: Network<int, Wire>, id: nat, reserved: Set<nat>,
) -> bool {
    (exists|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
        #[trigger] response_path(pre, result, net, reserved, s, a, v) && !consumed_issue(net, id, s, a))
        && forall|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
            #[trigger] response_path(pre, result, net, reserved, s, a, v) && !consumed_issue(net, id, s, a)
            ==> exists|i: int| 0 <= i < a.len() && !stock_work(#[trigger] observations(s, a)[i])
}

// A path avoiding a single reserved confirmation could still deliver a
// fresh weak update. Keep that case separate from the paper's held runs.
// Crossing the ordinary interface alone does not attribute a T effect.
pub proof fn ordinary_pair_or_required_traffic<S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        can_respond(resume_at(m, checkpoint_observations(alpha(n))), result, checkpoint_end(alpha(n)), delayed_slots()),
    ensures ({
        let pre = resume_at(m, checkpoint_observations(alpha(n))); let net = checkpoint_end(alpha(n));
        (exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v)
            && ordinary_suffix(alpha(n), a) && ordinary_suffix(beta(n), a))
        || receipt_prerequisite(pre, result, net, delayed_slots(), 2)
        || needs_other_weak_traffic(pre, result, net, 2, delayed_slots())
    }),
{
    hide(response_path); hide(accepted); hide(ordinary_suffix); hide(incompatible_completions);
    let pre = resume_at(m, checkpoint_observations(alpha(n)));
    let net = checkpoint_end(alpha(n));
    let reserved = delayed_slots();
    if !(exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v)
        && ordinary_suffix(alpha(n), a) && ordinary_suffix(beta(n), a)) {
        assert forall|s: Seq<Network<int, Wire>>, a: Seq<Action<Wire>>, v: int|
            #[trigger] response_path(pre, result, net, reserved, s, a, v) && !consumed_issue(net, 2, s, a)
            implies exists|i: int| 0 <= i < a.len() && !stock_work(#[trigger] observations(s, a)[i]) by {
            if forall|i: int| 0 <= i < a.len() ==> stock_work(#[trigger] observations(s, a)[i]) {
                ordinary_path_is_hot_pair(n, m, first, result, s, a, v);
            }
        }
    }
}

pub proof fn stock_availability_gives_held_pair<B, S>(
    n: Notice, m: LocalProtocol<S, int, Wire>, first: spec_fn(S) -> int, result: spec_fn(S) -> Option<int>,
    base: LocalProtocol<B, int, Wire>, base_result: spec_fn(B) -> Option<int>, start: Network<int, Wire>,
    e: Execution<int, Wire>, runnable: spec_fn(Network<int, Wire>, Process) -> bool,
    f: Decode, encode: Encode<S>, rel: Rel<B, S>,
)
    requires accepted(m, checkpoint_observations(alpha(n))), accepted(m, checkpoint_observations(beta(n))),
        completed_quorum_sample(m, first, alpha(n)), completed_quorum_sample(m, first, beta(n)),
        stock_cut(start, after_receipt(n)), admissible_service(start, base, base_result, e),
        delivery_fair(e), process_fair(e, runnable),
        eventually_responds(e, runnable, |s, a| sr2_result(base, base_result, observations(s, a)).is_some()),
        read_only_until_return(base, base_result, e),
        handler_correspondence(stock_source(base, start.locals, after_receipt(n).locals), m, f, encode, rel),
        forall|p: Process| #[trigger] rel(p, (base.initial)(p), (resume_at(m, checkpoint_observations(alpha(n))).initial)(p)),
        forall|x: B, y: S| #[trigger] rel(Process::SecondClient, x, y) ==> base_result(x).is_some() == result(y).is_some(),
    ensures exists|a: Seq<Action<Wire>>, v: int| #[trigger] incompatible_completions(n, m, first, result, a, v)
        && ordinary_suffix(alpha(n), a) && ordinary_suffix(beta(n), a),
{
    hide(accepted); hide(handler_correspondence); hide(incompatible_completions); hide(response_path);
    let dst = resume_at(m, checkpoint_observations(alpha(n)));
    assert(handler_correspondence(stock_source(base, start.locals, after_receipt(n).locals), dst, f, encode, rel))
        by { reveal(handler_correspondence); }
    let (a, v) = stock_availability_gives_held_response(n, dst, result, base, base_result, start, e, runnable, f, encode, rel);
    let t = replay(|x, w| cell(x, w), checkpoint_end(alpha(n)), a);
    ordinary_path_is_hot_pair(n, m, first, result, t, a, v);
}

}
