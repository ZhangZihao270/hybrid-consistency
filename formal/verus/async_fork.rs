// The original two-execution proof on messages with independent queue handles.
use vstd::prelude::*;
use crate::{Op, Replica, checkpoint::*, delivery::*, precedence};
use crate::async_messages::{self as net, Command, Headers, Message, implementation};
use crate::first_assembly::Service;
use crate::first_mailbox as mail;
use crate::first_splice::{self as tape, Observation};
use crate::fork_information::caller2;
use crate::guarded_comparison::weak_work;
use crate::independent_read::{self as read, State};
use crate::native_fork::{self as fork, ReadPair};
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

pub(crate) proof fn represented_view<S>(k: Headers, x: State<S>, public: net::Channel<S>, keys: Map<nat,nat>)
    requires public.local==net::control(x), net::represents(public.packets,keys,net::queue(k,x.cfg.net)),
    ensures channel_view(public)==view(k,x),
{
    let q=public.packets;
    let m=net::queue(k,x.cfg.net);
    assert forall|msg:Message| (#[trigger] (channel_view(public).copies)(msg))==(view(k,x).copies)(msg) by {
        if msg.body.path!=Path::Weak && survivor_actor(msg.body.to) {
            let source=q.dom().filter(|i:nat| q[i]==msg);
            let target=occurrences(k,x.cfg.net,msg);
            let bij=keys.restrict(source);
            assert(bij.dom() =~= source);
            assert(bij.is_injective());
            assert(bij.values() =~= target) by {
                assert forall|h:nat| #[trigger] bij.values().contains(h)==target.contains(h) by {
                    if target.contains(h) {
                        let i=choose|i:nat| #[trigger] keys.get(i)==Some(h);
                        assert(q.contains_key(i) && m.get(keys[i])==Some(q[i]));
                        assert(bij.contains_key(i) && bij[i]==h);
                    } else if bij.values().contains(h) {
                        let i=choose|i:nat| #[trigger] bij.dom().contains(i) && bij[i]==h;
                        assert(m.get(keys[i])==Some(q[i]));
                    }
                }
            }
            bij.lemma_injective_values_len();
        }
    }
    assert(channel_view(public).copies =~= view(k,x).copies);
}

pub(crate) proof fn visible_count<S>(k: Headers, x: State<S>, msg: Message)
    requires msg.body.path != Path::Weak, survivor_actor(msg.body.to),
    ensures (view(k, x).copies)(msg) == occurrences(k, x.cfg.net, msg).len(),
{}

proof fn record_projects<S>(k: Headers, x: State<S>, y: State<S>, mask: Set<nat>)
    requires fork::record(x, mask) == fork::record(y, mask),
    ensures view(k, x) == view(k, y),
{
    assert forall|msg: Message| #[trigger] (view(k, x).copies)(msg) == (view(k, y).copies)(msg) by {
        if msg.body.path != Path::Weak && survivor_actor(msg.body.to) {
            assert(occurrences(k, x.cfg.net, msg) =~= occurrences(k, y.cfg.net, msg)) by {
                assert forall|h: nat| #[trigger] occurrences(k, x.cfg.net, msg).contains(h)
                    == #[trigger] occurrences(k, y.cfg.net, msg).contains(h) by {
                    assert((fork::record(x, mask).packets)(h) == (fork::record(y, mask).packets)(h));
                }
            }
        }
    }
    assert(view(k, x).copies =~= view(k, y).copies);
}

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

// Select a replica transition which installed the final application-level
// view. A change confined to allocation bookkeeping does not pass this test.
pub open spec fn installed<S>(k: Headers, s: Service<S>, j: int) -> bool {
    let e = net::callback(k, tape::record(s, 0)[j]);
    0 <= j < s.actions.len() && e.actor is At && !weak_work(e)
        && view(k, s.states[j]) != view(k, s.states[j+1])
        && view(k, s.states[j+1]) == view(k, s.states.last())
}

proof fn last_install<S>(m: Program<S>, k: Headers, first: spec_fn(S) -> int, b: Fork, s: Service<S>, i: nat)
    -> (j: int)
    requires fork::admitted(m, first, b, s), i < s.states.len(),
        view(k, s.states[i as int]) == view(k, s.states.last()), view(k, s.states[0]) != view(k, s.states.last()),
    ensures installed(k, s, j),
    decreases i,
{
    assert(i > 0);
    let j = i as int - 1; let x = s.states[j]; let y = s.states[j+1]; let a = s.actions[j];
    if view(k, x) == view(k, y) { last_install(m, k, first, b, s, (i-1) as nat) } else {
        fork::first_frame(m, first, b, s, (i-1) as nat);
        assert(mail::active_step(m)(x, a, y) && !mail::posted(m)(x));
        let e = process_step(x.cfg.net, a);
        if e.actor == Process::FirstClient {
            fork::silent_callback(m, x, a, y, Set::empty());
            record_projects(k, x, y, Set::empty());
        }
        assert(!crate::original_application::weak_replica_step()(x, a, y));
        j
    }
}

pub open spec fn attributed<S>(m: Program<S>, k: Headers, a: Service<S>, b: Service<S>) -> bool {
    let x = fork::invocation(m, a); let y = fork::invocation(m, b);
    view(k, a.states[0]) == view(k, b.states[0]) && view(k, x) != view(k, y)
        && view(k, a.states.last()) == view(k, x) && view(k, b.states.last()) == view(k, y)
        && ((exists|j: int| #[trigger] installed(k, a, j)) || (exists|j: int| #[trigger] installed(k, b, j)))
}

pub open spec fn after_offers<S>(p: Program<S>, k: Headers) -> Program<S> {
    crate::independent_preparations::after_offers(implementation(k, p), crate::original_application::lanes())
}

// Writer options in the independent store quantify over actual first
// returns and all queue handles. The functional T rule sees these sets.
pub open spec fn options<S>(p: Program<S>, res: spec_fn(S) -> Option<int>, x: net::Channel<S>) -> Set<Op> {
    set![Op::W1, Op::W2].filter(|w: Op| exists|ts: Seq<net::Turn>| #[trigger] net::quiet_return(p, res, x, ts)
        && res(caller2(net::end(p, x, ts).local)) == Some(crate::next(w, 1)))
}

pub proof fn exact_options<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>, x: State<S>)
    requires after_crash(x.cfg.net),
    ensures options(p, res, net::snapshot(k, x)) == fork::writers(implementation(k, p), res, x, Set::empty()),
{
    let m = implementation(k, p); let public = net::snapshot(k, x);
    let a = options(p, res, public); let b = fork::writers(m, res, x, Set::empty());
    assert forall|w: Op| #[trigger] a.contains(w) == #[trigger] b.contains(w) by {
        if a.contains(w) && !b.contains(w) {
            let ts = choose|ts: Seq<net::Turn>| #[trigger] net::quiet_return(p, res, public, ts)
                && res(caller2(net::end(p, public, ts).local)) == Some(crate::next(w, 1));
            let ids = Map::new(public.packets.dom(), |i: nat| i);
            assert forall|h: nat| #[trigger] public.packets.contains_key(h) implies
                exists|i: nat| #[trigger] ids.get(i) == Some(h) by { assert(ids.get(h) == Some(h)); }
            assert(net::represents(public.packets, ids, public.packets));
            net::return_is_trace(p, res, public, ts);
            let (s, _) = net::lift_prefix(p, k, x, public, ids, ts, false, res);
            assert(!fork::uses_name(Set::empty(), s));
            assert(fork::value(m, res, x, s) == Some(crate::next(w, 1)));
        } else if b.contains(w) && !a.contains(w) {
            let s = choose|s: Seq<Event>| !fork::uses_name(Set::empty(), s) && #[trigger] fork::completes(m, res, x, s, true)
                && fork::value(m, res, x, s) == Some(crate::next(w, 1));
            fork::completion_facts(m, res, x, s); net::project_prefix(p, k, x, s, true, res);
            assert(net::quiet_return(p, res, public, net::turns(k, s)));
            assert(res(caller2(net::end(p, public, net::turns(k, s)).local)) == Some(crate::next(w, 1)));
        }
    }
    assert(a =~= b);
}

pub open spec fn public_history<S>(p: Program<S>, k: Headers, b: Fork, h: ReadPair<S>) -> bool {
    let m = after_offers(p, k);
    let start = crate::independent_preparations::before_offers(implementation(k, p), crate::original_application::lanes());
    let actions = crate::independent_preparations::offers()
        + ((crate::first_assembly::boot(Some(b)) + h.first.actions) + (crate::fork_alternatives::wake() + h.second));
    let ts = net::turns(k, actions); let x = net::snapshot(k, start);
    net::trace(p, x, ts, true) && net::end(p, x, ts) ==
        net::snapshot(k, crate::first_assembly::drive(m, fork::invocation(m, h.first), h.second))
}

pub(crate) proof fn publish_history<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, b: Fork, h: ReadPair<S>)
    requires fork::completed_history(implementation(k, p), after_offers(p, k), first, res, b, h),
    ensures public_history(p, k, b, h),
{
    let start = crate::independent_preparations::before_offers(implementation(k, p), crate::original_application::lanes());
    let actions = crate::independent_preparations::offers()
        + ((crate::first_assembly::boot(Some(b)) + h.first.actions) + (crate::fork_alternatives::wake() + h.second));
    net::project_prefix(p, k, start, actions, true, res);
}

// Private startup memory has already been installed at an SR2 cut.
pub(crate) proof fn same_started_machine<S>(p: Program<S>, q: Program<S>, res: spec_fn(S) -> Option<int>, x: State<S>, s: Seq<Event>)
    requires p.accept == q.accept, p.update == q.update,
    ensures fork::completes(p, res, x, s, true) == fork::completes(q, res, x, s, true),
        fork::value(p, res, x, s) == fork::value(q, res, x, s),
    decreases s.len(),
{
    if s.len() > 0 { same_started_machine(p, q, res, read::next(p, x, s[0]), s.drop_first()); }
}
pub(crate) proof fn started_options<S>(p: Program<S>, k: Headers, res: spec_fn(S) -> Option<int>, x: State<S>)
    requires after_crash(x.cfg.net),
    ensures options(p, res, net::snapshot(k, x)) == fork::writers(after_offers(p, k), res, x, Set::empty()),
{
    let m = after_offers(p, k); let raw = implementation(k, p);
    exact_options(p, k, res, x);
    let all = Set::<nat>::empty();
    let a = fork::writers(m, res, x, all); let b = fork::writers(raw, res, x, all);
    assert forall|w: Op| #[trigger] a.contains(w) == #[trigger] b.contains(w) by {
        if a.contains(w) != b.contains(w) {
            let src = if a.contains(w) { m } else { raw };
            assert(fork::writers(src, res, x, all).contains(w));
            let s = choose|s: Seq<Event>| !fork::uses_name(all, s) && #[trigger] fork::completes(src, res, x, s, true)
                && fork::value(src, res, x, s) == Some(crate::next(w, 1));
            same_started_machine(m, raw, res, x, s);
            assert(fork::completes(m, res, x, s, true) && fork::completes(raw, res, x, s, true));
        }
    }
    assert(a =~= b);
}

pub(crate) proof fn attribute_pair<S>(handler: Program<S>, k: Headers, first: spec_fn(S) -> int, res: spec_fn(S) -> Option<int>,
    n: Notice, a: Service<S>, b: Service<S>, source: Fork, s: Seq<Event>)
    requires ({
        let m = implementation(k, handler); let x = fork::invocation(m, a); let y = fork::invocation(m, b);
        let (u,v) = if source == alpha(n) { (x,y) } else { (y,x) };
        source.notice == n && crate::first_schedule::startup(m) && fork::candidate(m, first, n, a, b)
            && fork::completes(m, res, u, s, true) && fork::value(m, res, u, s) == Some(first_value(source))
            && !fork::writers(m, res, v, Set::empty()).contains(observed_writer(source))
    }),
    ensures attributed(implementation(k, handler), k, a, b),
{
    let m = implementation(k, handler); let x = fork::invocation(m, a); let y = fork::invocation(m, b);
    let all = Set::<nat>::empty(); let l = alpha(n); let r = beta(n);
    fork::actual_handoff(m, first, l, a, all); fork::actual_handoff(m, first, r, b, all);
    record_projects(k, a.states.last(), x, all); record_projects(k, b.states.last(), y, all);
    fork::common_fanout(m, n);
    record_projects(k, a.states[0], b.states[0], fork::frozen_names(a.states[0], b.states[0]));
    if view(k, x) == view(k, y) {
        assert(fork::same_reader(x, y));
        let (u,v) = if source == l { (x,y) } else { (y,x) };
        let t = replay_return(handler, k, res, u, v, s, all);
        let w = observed_writer(source);
        assert(fork::value(m, res, v, t) == Some(crate::next(w, 1)));
        assert(fork::writers(m, res, v, all).contains(w));
    }
    if view(k, a.states[0]) != view(k, a.states.last()) {
        last_install(m, k, first, l, a, a.actions.len());
    } else {
        last_install(m, k, first, r, b, b.actions.len());
    }
}

// All hypotheses belong to the original workload, availability, scheduling
// and no-await premises. The application handler is arbitrary. The two
// records in the attribution conclusion contain no internal queue names.
pub proof fn original_async_application<S>(p: Program<S>, k: Headers, first: spec_fn(S) -> int,
    res: spec_fn(S) -> Option<int>, n: Notice, run: crate::fair_read::Runnable, aa: bool, ab: bool)
    -> (histories: (ReadPair<S>, ReadPair<S>))
    requires fork::original_premises(implementation(k, p), after_offers(p, k), first, res, n, run, aa, ab),
    ensures ({
        let raw = implementation(k, p); let m = after_offers(p, k);
        let (a, b) = histories; let l = alpha(n); let r = beta(n);
        let x = fork::invocation(m, a.first); let y = fork::invocation(m, b.first);
        let wa = options(p, res, net::snapshot(k, x)); let wb = options(p, res, net::snapshot(k, y));
        let orders = precedence::actual_cuts(n, aa, ab);
        let bad = !fork::legal_history(m, first, res, a) || !fork::legal_history(m, first, res, b);
        let weak = crate::guarded_history::weak_end();
        weak.answers.get(crate::weak_round::request(Op::W1).id) == Some(1)
            && weak.answers.get(crate::weak_round::request(Op::W2).id) == Some(1)
            && truthful_notice(l, weak_assignment(l, aa).ops) && truthful_notice(r, weak_assignment(r, ab).ops)
            && fork::candidate(m, first, n, a.first, b.first)
            && fork::completed_history(raw, m, first, res, l, a) && fork::completed_history(raw, m, first, res, r, b)
            && public_history(p, k, l, a) && public_history(p, k, r, b)
            && ((crate::original_application::preserves_extension_option(l, wa, wb, orders)
                || crate::original_application::preserves_extension_option(r, wb, wa, orders)) ==> bad)
            && (bad || (fork::value(m, res, x, a.second) == Some(5) && fork::value(m, res, y, b.second) == Some(2)
                && wa == set![Op::W2] && wb == set![Op::W1]
                && attributed(m, k, a.first, b.first)))
    }),
{
    hide(fork::completed_history); hide(fork::writers); hide(fork::legal_history);
    hide(fork::strong_record_changes_options); hide(fork::requires_other_slot);
    let raw = implementation(k, p); let m = after_offers(p, k);
    let handler = Program { initial: m.initial, ..p };
    assert(m == implementation(k, handler));
    let (a, b) = fork::original_hot_application(raw, m, first, res, n, run, aa, ab);
    publish_history(p, k, first, res, alpha(n), a); publish_history(p, k, first, res, beta(n), b);
    let x = fork::invocation(m, a.first); let y = fork::invocation(m, b.first);
    assert(after_crash(x.cfg.net) && after_crash(y.cfg.net)) by { reveal(fork::completed_history); }
    started_options(p, k, res, x); started_options(p, k, res, y);
    if fork::legal_history(m, first, res, a) && fork::legal_history(m, first, res, b) {
        assert(fork::completes(m, res, x, a.second, true)) by { reveal(fork::completed_history); }
        attribute_pair(handler, k, first, res, n, a.first, b.first, alpha(n), a.second);
    }
    (a, b)
}

}
