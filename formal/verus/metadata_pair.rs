use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::{fresh_send, after_receipt};
use crate::delivery::*;
use crate::metadata_stock::*;
use crate::mixed_read::pair;
use crate::mixed_sources::{actual_disk_before_sr2, cut_store};
use crate::ordered_store::{Command, Stamp, initial_store, sample, majority};
use crate::protocol::*;
use crate::quorum_rpc::{Resolver, fair, rpc};
use crate::service::*;
use crate::sr2::{queries, query_packet};
use crate::stock_availability::eventual;
use crate::survivors::*;

// One physical request and sampled reply per selected site. The header
// in the *issued packet* is the number of locally applied ordinary
// commands. C2 has no access to the sender's later state.
verus! {

pub struct Local {
    pub first: Control,
    pub applied: Seq<Command>,
    pub backup: Option<Stamp>,
    pub requested: bool,
    pub answered: bool,
    pub rows: Rows,
    pub returned: Option<int>,
}

pub open spec fn startup(p: Process, archives: Set<Replica>) -> Local {
    let original = initial_store();
    Local {
        first: initial_control(), applied: original.log,
        backup: match p { Process::At(r) if archives.contains(r) => Some(sample(original, r)), _ => None },
        requested: false, answered: false, rows: Map::empty(), returned: None,
    }
}

pub open spec fn replica_answer(p: Packet<Wire>) -> bool {
    p.from is At && p.to == Process::SecondClient && p.path == Path::Strong && p.input is StampedAnswer
}

pub open spec fn signed_row(p: Packet<Wire>) -> Stamp {
    Stamp { value: p.input->StampedAnswer_0.value, version: p.input->StampedAnswer_1 }
}

// The command workload has no ordinary application writes. Locally
// reinstalling a value requires an available ordinary image at the
// current position. Background weak data can only be the two issued
// writes, sent by a live replica currently holding the transmitted value.
pub open spec fn permits(s: Local, e: ProcessStep<int, Wire>) -> bool {
    // Both clients may poll or receive a reply before they have a majority.
    // Stopping C1 requires its own completed read.
    let ordinary = if e.action == Action::StopFirstClient { s.returned.is_some() }
        else if e.action == Action::Strong(Process::FirstClient)
            || (e.incoming.is_some() && first_reply(e.incoming.unwrap())) { true }
        else { permits_step(s.first, e) };
    ordinary && match e.action {
        Action::Local(_, Wire::Copy(v)) =>
            s.backup == Some(Stamp { value: v, version: s.applied.len() }) && e.own_local != Some(v),
        Action::Send(_, p) => match p.input {
            Wire::Copy(v) => p.path == Path::Weak && p.from is At && p.to is At && p.from != p.to
                && (v == 2 || v == 5) && e.own_local == Some(v),
            Wire::StampedAnswer(report, pos) => replica_answer(p) && s.requested && !s.answered
                && e.own_local == Some(report.value) && pos == s.applied.len() && report.answered_first == s.first.answered_first,
            // Reply(v) is the compact encoding of an ordinary position-zero
            // sample in the selected first-read transport.
            Wire::Reply(_) => s.applied.len() == 0,
            Wire::Answer2(_) => false,
            _ => true,
        },
        _ => true,
    }
}

pub open spec fn collect(s: Local, p: Packet<Wire>) -> Rows {
    let row = if replica_answer(p) { Some(signed_row(p)) }
        else if first_reply(p) { Some(Stamp { version: 0, value: p.input->Reply_0 }) }
        else { None };
    if row.is_some() && !s.rows.contains_key(p.from->At_0) { s.rows.insert(p.from->At_0, row.unwrap()) } else { s.rows }
}

pub open spec fn step(rho: Resolver, s: Local, e: ProcessStep<int, Wire>) -> Local {
    let next = Local { first: change_control(s.first, e), ..s };
    match e.incoming {
        Some(p) => Local {
            requested: s.requested || (p.to is At && p == query_packet(p.to->At_0)),
            rows: collect(s, p), ..next
        },
        None => match e.action {
            Action::Send(_, p) if replica_answer(p) => Local { answered: true, ..next },
            Action::Strong(client) if outside_replica(client) && s.returned.is_none() && majority(s.rows.dom()) =>
                Local { returned: rho(s.rows), ..next },
            _ => next,
        },
    }
}

pub open spec fn duplex(first: Resolver, second: Resolver, archives: Set<Replica>) -> LocalProtocol<Local, int, Wire> {
    LocalProtocol {
        initial: |p| startup(p, archives), accept: |s, e| permits(s, e),
        update: |s, e: ProcessStep<int, Wire>| step(if e.actor == Process::FirstClient { first } else { second }, s, e),
        done: |s: Local| s.returned.is_some(),
    }
}

pub open spec fn machine(rho: Resolver, archives: Set<Replica>) -> LocalProtocol<Local, int, Wire> {
    duplex(|rows| crate::quorum_rpc::latest(rows), rho, archives)
}

pub open spec fn first_rows(b: Fork, k: nat) -> Rows {
    let row = Stamp { value: first_value(b), version: 0 };
    let rows = if k >= 12 { Map::empty().insert(crate::origin(b.branch), row) } else { Map::empty() };
    if k >= 13 { rows.insert(Replica::R3, row) } else { rows }
}

pub open spec fn prefix_local(first: Resolver, b: Fork, p: Process, k: nat, archives: Set<Replica>) -> Local {
    let rows = if p == Process::FirstClient { first_rows(b,k) } else { Map::empty() };
    Local { first: expected_control(b, p, k), rows,
        returned: if p == Process::FirstClient && k >= 14 { first(rows) } else { None }, ..startup(p,archives) }
}

pub open spec fn at_cut(b: Fork, p: Process, archives: Set<Replica>) -> Local {
    prefix_local(|rows| crate::quorum_rpc::latest(rows), b, p, 17, archives)
}

pub proof fn prefix_control(first: Resolver, second: Resolver, b: Fork, archives: Set<Replica>, p: Process, k: nat)
    requires k <= 17,
    ensures memory(duplex(first,second,archives), p, checkpoint_observations(b), k) == prefix_local(first,b,p,k,archives),
    decreases k,
{
    if k > 0 { let j = (k - 1) as nat; prefix_control(first,second,b,archives,p,j); prefix_index(j as int); }
}

pub proof fn real_first_with(first: Resolver, second: Resolver, b: Fork, archives: Set<Replica>)
    requires first(first_rows(b,13)) == Some(first_value(b)),
    ensures ({
        let m = duplex(first,second,archives); let es = checkpoint_observations(b);
        accepted(m, es) && completed_quorum_sample(m, |s: Local| s.returned.unwrap(), b)
            && first_result(m, |s: Local| s.returned.unwrap(), b) == first_value(b)
            && (forall|p: Process| #[trigger] (resume_at(m,es).initial)(p) == at_cut(b,p,archives))
    }),
{
    hide(memory);
    let m = duplex(first,second,archives); let es = checkpoint_observations(b); let c = Process::FirstClient;
    fanout_and_reply_deliveries(b);
    assert forall|i: int| 0 <= i < es.len() implies {
        let e = #[trigger] es[i]; (m.accept)(memory(m,e.actor,es,i as nat),e)
    } by {
        prefix_index(i); prefix_control(first,second,b,archives,es[i].actor,i as nat);
        prefix_memory_tracks_actual_messages(b,es[i].actor,i as nat);
        assert((checkpoint_machine().accept)(memory(checkpoint_machine(),es[i].actor,es,i as nat),es[i]));
    }
    assert forall|k: nat| k <= 12 implies !(m.done)(#[trigger] first_client_at(m,b,k))
        by { prefix_control(first,second,b,archives,c,k); }
    prefix_control(first,second,b,archives,c,13); prefix_control(first,second,b,archives,c,14);
    assert(crate::first_quorum(b.branch).contains(crate::origin(b.branch)));
    assert(during_sr1(b,10,crate::origin(b.branch)) == first_value(b));
    assert forall|p: Process| #[trigger] (resume_at(m,es).initial)(p) == at_cut(b,p,archives) by {
        prefix_control(first,second,b,archives,p,17);
    }
}

pub proof fn real_first_read(b: Fork, rho: Resolver, archives: Set<Replica>)
    ensures ({
        let m = machine(rho, archives); let es = checkpoint_observations(b);
        accepted(m, es) && completed_quorum_sample(m, |s: Local| s.first.reply.unwrap(), b)
            && first_result(m, |s: Local| s.first.reply.unwrap(), b) == first_value(b)
            && (forall|p: Process| #[trigger] (resume_at(m, es).initial)(p) == at_cut(b, p, archives))
    }),
{
    let first = |rows| crate::quorum_rpc::latest(rows); let c = Process::FirstClient;
    real_first_with(first,rho,b,archives);
    prefix_control(first,rho,b,archives,c,13); prefix_control(first,rho,b,archives,c,14);
    assert(crate::first_quorum(b.branch).contains(crate::origin(b.branch)));
    assert(during_sr1(b,10,crate::origin(b.branch)) == first_value(b));
}

pub enum BeforeSample { Unchanged, RestoreImages, DeliverW1 }

// The background dissemination case is an alternative opportunity. The
// direct unchanged and ordinary-repair schedules need no replica exchange.
pub open spec fn weak_offer(slot: nat) -> Action<Wire> {
    send(slot, Path::Weak, at(Replica::R1), at(Replica::R2), Wire::Copy(2))
}

pub open spec fn sampled(b: Fork, r: Replica, work: BeforeSample) -> Stamp {
    let d = (cut_store(b).disk)(r);
    Stamp { version: d.applied, value: match work {
        BeforeSample::RestoreImages => sample(initial_store(), r).value,
        BeforeSample::DeliverW1 if r == Replica::R2 => (cut_store(b).disk)(Replica::R1).value,
        _ => d.value,
    } }
}

pub open spec fn sample_rows(b: Fork, work: BeforeSample) -> Rows {
    Map::empty().insert(Replica::R1, sampled(b, Replica::R1, work))
        .insert(Replica::R2, sampled(b, Replica::R2, work))
}

pub open spec fn physical_answer(b: Fork, r: Replica, work: BeforeSample) -> Packet<Wire> {
    let d = sampled(b, r, work);
    let p = crate::sr2::answer_packet(r, Report { value: d.value, answered_first: checkpoint_control(b, at(r)).answered_first });
    Packet { input: Wire::StampedAnswer(p.input->Answer2_0, d.version), ..p }
}

pub open spec fn read_actions(b: Fork, work: BeforeSample) -> Seq<Action<Wire>> {
    let r1 = Replica::R1; let r2 = Replica::R2;
    let middle = match work {
        BeforeSample::RestoreImages => seq![Action::Local(r1, Wire::Copy(sample(initial_store(), r1).value)),
            Action::Local(r2, Wire::Copy(sample(initial_store(), r2).value))],
        BeforeSample::DeliverW1 => seq![weak_offer(15), Action::Deliver(15)],
        BeforeSample::Unchanged => Seq::empty(),
    };
    queries() + middle + seq![Action::Send(13, physical_answer(b, r1, work)), Action::Send(14, physical_answer(b, r2, work)),
        Action::Deliver(13), Action::Deliver(14), Action::Strong(Process::SecondClient)]
}

pub open spec fn read_net(b: Fork, work: BeforeSample, k: nat) -> Network<int, Wire> {
    let cut = checkpoint_end(b); let r1 = Replica::R1; let r2 = Replica::R2;
    let offset: nat = if work is Unchanged { 0 } else { 2 };
    let p = if 1 <= k < 3 { cut.pending.insert(11, query_packet(r1)) } else { cut.pending };
    let p = if 2 <= k < 4 { p.insert(12, query_packet(r2)) } else { p };
    let p = if work is DeliverW1 && k == 5 { p.insert(15, weak_offer(15)->Send_1) } else { p };
    let p = if 5 + offset <= k < 7 + offset { p.insert(13, physical_answer(b, r1, work)) } else { p };
    let p = if 6 + offset <= k < 8 + offset { p.insert(14, physical_answer(b, r2, work)) } else { p };
    Network { pending: p, locals: |r| if work is RestoreImages && ((r == r1 && k >= 5) || (r == r2 && k >= 6)) {
        sample(initial_store(), r).value
    } else if work is DeliverW1 && r == r2 && k >= 6 { (cut.locals)(r1) } else { (cut.locals)(r) }, ..cut }
}

pub open spec fn read_states(b: Fork, work: BeforeSample) -> Seq<Network<int, Wire>> {
    Seq::new(read_actions(b, work).len() + 1, |i: int| read_net(b, work, i as nat))
}

pub open spec fn during(b: Fork, rho: Resolver, archives: Set<Replica>, work: BeforeSample, p: Process, k: nat) -> Local {
    let start = at_cut(b, p, archives); let offset: nat = if work is Unchanged { 0 } else { 2 };
    let c2 = p == Process::SecondClient; let r1 = Replica::R1; let r2 = Replica::R2;
    let rows = if c2 && k >= 7 + offset { Map::empty().insert(r1, sampled(b, r1, work)) } else { Map::empty() };
    Local {
        first: if c2 && k >= 1 { Control { sent_requests: if k == 1 { set![r1] } else { live_pair() }, ..start.first } }
            else if work is DeliverW1 && p == at(r2) && k >= 6 { Control { weak_copy: Some(2), ..start.first } } else { start.first },
        requested: (p == at(r1) && k >= 3) || (p == at(r2) && k >= 4),
        answered: (p == at(r1) && k >= 5 + offset) || (p == at(r2) && k >= 6 + offset),
        rows: if !c2 { start.rows } else if k >= 8 + offset { rows.insert(r2, sampled(b, r2, work)) } else { rows },
        returned: if c2 && k >= 9 + offset { rho(sample_rows(b, work)) } else { start.returned }, ..start
    }
}

pub open spec fn resumed(b: Fork, rho: Resolver, archives: Set<Replica>) -> LocalProtocol<Local, int, Wire> {
    resume_at(machine(rho, archives), checkpoint_observations(b))
}

pub proof fn read_memory(b: Fork, rho: Resolver, archives: Set<Replica>, work: BeforeSample, p: Process, k: nat)
    requires k <= read_actions(b, work).len(),
    ensures memory(resumed(b, rho, archives), p, observations(read_states(b, work), read_actions(b, work)), k)
        == during(b, rho, archives, work, p, k),
    decreases k,
{
    actual_disk_before_sr2(b, 17, Replica::R1);
    if k == 0 { real_first_read(b, rho, archives); }
    else {
        let j = (k - 1) as nat; read_memory(b, rho, archives, work, p, j); prefix_index(j as int);
        prefix_memory_tracks_actual_messages(b, Process::SecondClient, 17);
    }
}

proof fn same_c2_invocation(b: Fork, work: BeforeSample)
    ensures second_invocation(read_states(b, work), read_actions(b, work)),
        invocation_only(read_actions(b, work), Process::FirstClient, Set::empty()),
{
    let a = read_actions(b, work); let c = Process::SecondClient; let es = observations(read_states(b, work), a);
    assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
        Action::Send(_, p) if p.from == c => invocation_packet(p) && live_pair().contains(p.to->At_0)
            && (forall|j: int| 0 <= j < i ==> !client_sends_to(#[trigger] a[j], c, p.to->At_0)),
        _ => true,
    } by { prefix_index(i); }
    assert forall|r: Replica| #[trigger] live_pair().contains(r) implies
        exists|i: int| 0 <= i < a.len() && client_sends_to(#[trigger] a[i], c, r) by {
        let i: int = if r == Replica::R1 { 0 } else { 1 };
        assert(client_sends_to(a[i], c, r));
    }
    assert forall|i: int, j: int| 0 <= j < i < es.len() implies match (#[trigger] es[i]).action {
        Action::Send(_, p) if p.from == c => (#[trigger] es[j]).actor != c || es[j].incoming.is_none(),
        _ => true,
    } by { prefix_index(i); }
    assert forall|i: int| 0 <= i < a.len() implies match #[trigger] a[i] {
        Action::Send(_, p) => p.from != Process::FirstClient, _ => true,
    } by { prefix_index(i); }
}

pub proof fn sampled_exchange(b: Fork, rho: Resolver, archives: Set<Replica>, work: BeforeSample)
    requires work is RestoreImages ==> live_pair().subset_of(archives),
    ensures ({
        let a = read_actions(b, work); let t = read_states(b, work); let es = observations(t, a);
        let m = resumed(b, rho, archives); let c = Process::SecondClient;
        t[0] == checkpoint_end(b) && trace(|x, w| cell(x, w), t, a) && accepted(m, es) && second_invocation(t, a)
            && invocation_only(a, Process::FirstClient, Set::empty())
            && pending_before_end(m, |s: Local| s.returned, es)
            && sr2_result(m, |s: Local| s.returned, es) == rho(sample_rows(b, work))
            && memory(m, c, es, (a.len() - 1) as nat).rows == sample_rows(b, work)
            && (forall|i: int| 0 <= i < a.len() ==> keeps_delayed_slots(#[trigger] a[i], delayed_slots()) && fresh_send(a[i], delayed_slots()))
            && (forall|k: int, id: nat| 0 <= k < t.len() && delayed_slots().contains(id)
                ==> #[trigger] packet_at(t[k], id) == packet_at(checkpoint_end(b), id))
    }),
{
    hide(memory);
    let t = read_states(b, work); let a = read_actions(b, work); let es = observations(t, a);
    let m = resumed(b, rho, archives); let c = Process::SecondClient;
    same_c2_invocation(b, work); real_first_read(b, rho, archives);
    actual_disk_before_sr2(b, 17, Replica::R1); actual_disk_before_sr2(b, 17, Replica::R2);
    assert(t[0].locals =~= checkpoint_end(b).locals);
    assert forall|i: int| 0 <= i < a.len() implies {
        let step = #[trigger] a[i]; enabled(t[i], step) && t[i+1] == advance(|x, w| cell(x, w), t[i], step)
            && keeps_delayed_slots(step, delayed_slots()) && fresh_send(step, delayed_slots())
    } by {
        prefix_index(i); let post = advance(|x, w| cell(x, w), t[i], a[i]);
        assert(post.locals =~= t[i+1].locals); assert(post.pending =~= t[i+1].pending);
    }
    assert forall|i: int| 0 <= i < es.len() implies {
        let e = #[trigger] es[i]; (m.accept)(memory(m, e.actor, es, i as nat), e)
    } by {
        prefix_index(i); read_memory(b, rho, archives, work, es[i].actor, i as nat);
        prefix_memory_tracks_actual_messages(b, at(Replica::R1), 17); prefix_memory_tracks_actual_messages(b, at(Replica::R2), 17);
        prefix_memory_tracks_actual_messages(b, c, 17);
    }
    assert forall|k: nat| k < es.len() implies (#[trigger] memory(m, c, es, k)).returned.is_none()
        by {read_memory(b, rho, archives, work, c, k);}
    read_memory(b, rho, archives, work, c, es.len());
    read_memory(b, rho, archives, work, c, (es.len() - 1) as nat);
    assert forall|k: int, id: nat| 0 <= k < t.len() && delayed_slots().contains(id) implies
        #[trigger] packet_at(t[k], id) == packet_at(checkpoint_end(b), id) by { prefix_index(k); }
}

// This compares the real histories, including physical headers and packet
// slots. Any deterministic private computation on one process's complete
// local event history is covered. A stock comparison is only needed to
// establish an opportunity for a return.
pub proof fn same_survivor_transcripts<S>(n: Notice, audit: LocalProtocol<S, int, Wire>, p: Process, work: BeforeSample, k: nat)
    requires survivor_actor(p), k <= read_actions(alpha(n), work).len(),
    ensures ({
        let b = beta(n); let a = alpha(n);
        let actions = read_actions(a, work);
        let t = read_states(a, work); let u = read_states(b, work);
        let x = observations(t, actions); let y = observations(u, read_actions(b, work));
        actions == read_actions(b, work) && x == y
            && outside_delays(t[k as int], u[k as int], delayed_slots())
            && memory(resume_at(audit, checkpoint_observations(a)), p, x, k)
                == memory(resume_at(audit, checkpoint_observations(b)), p, y, k)
    }),
{
    let a = alpha(n); let b = beta(n);
    let t = read_states(a, work); let u = read_states(b, work);
    let actions = read_actions(a, work);
    let x = observations(t, actions); let y = observations(u, read_actions(b, work));
    surviving_checkpoint_agreement(n);
    actual_disk_before_sr2(a,17,Replica::R1); actual_disk_before_sr2(b,17,Replica::R1);
    assert forall|r: Replica| #[trigger] live_pair().contains(r) implies physical_answer(a,r,work)==physical_answer(b,r,work) by {
        actual_disk_before_sr2(a, 17, r); actual_disk_before_sr2(b, 17, r);
        assert(survivor_actor(at(r)));
        assert(checkpoint_control(a, at(r)) == checkpoint_control(b, at(r)));
    }
    assert(live_pair().contains(Replica::R1) && live_pair().contains(Replica::R2));
    assert(physical_answer(a, Replica::R1, work) == physical_answer(b, Replica::R1, work));
    assert(physical_answer(a, Replica::R2, work) == physical_answer(b, Replica::R2, work));
    assert(actions =~= read_actions(b, work));
    assert forall|i: int| 0 <= i < x.len() implies #[trigger] x[i] == y[i] by {prefix_index(i);}
    assert(x =~= y);
    assert forall|id: nat| !delayed_slots().contains(id) implies packet_at(t[k as int], id) == #[trigger] packet_at(u[k as int], id) by {
        assert(packet_at(checkpoint_end(a), id) == packet_at(checkpoint_end(b), id));
    }
    arbitrary_survivor_memory_agrees(n, audit, p, 17);
    memory_from_same_local_state(resume_at(audit, checkpoint_observations(a)), resume_at(audit, checkpoint_observations(b)), p, x, k);
}

// A survivor can retain its own earlier send, even if an ordinary restore
// later makes its current cell look exactly like stock. An authentic stock
// origin for this *past* sample is impossible in the audited log.
pub proof fn remembered_first_sample_has_no_stock_origin(
    b: Fork, r: Replica, rho: Resolver, archives: Set<Replica>, stock_log: Seq<Command>,
)
    requires live_pair().contains(r),
    ensures ({
        let i: nat=if r==Replica::R1 {8} else {9};
        let es=checkpoint_observations(b); let ev=es[i as int];
        let local=memory(machine(rho,archives),at(r),es,i);
        let stamp=Stamp { version: local.applied.len(), value: ev.own_local.unwrap() };
        ev.actor==at(r) && ev.action is Send && first_reply(ev.action->Send_1)
            && ev.action->Send_1.input==Wire::Reply(stamp.value) && stamp.version==0
            && !crate::ordered_store::authentic(stock_log,stamp)
    }),
{
    let i: nat=if r==Replica::R1 {8} else {9};
    prefix_control(|m| crate::quorum_rpc::latest(m),rho,b,archives,at(r),i);
}

pub proof fn returning_samples_contradict_h(n: Notice, rho: Resolver, archives: Set<Replica>, work: BeforeSample)
    requires work is RestoreImages ==> live_pair().subset_of(archives), rho(sample_rows(alpha(n), work)).is_some(),
    ensures incompatible_completions(n, machine(rho, archives), |s: Local| s.first.reply.unwrap(), |s: Local| s.returned,
        read_actions(alpha(n), work), rho(sample_rows(alpha(n), work)).unwrap()),
{
    hide(memory); hide(replay); hide(accepted);
    let b = alpha(n); let t = read_states(b, work); let a = read_actions(b, work);
    let m = machine(rho, archives); let pre = resumed(b, rho, archives);
    let result = |s: Local| s.returned; let first = |s: Local| s.first.reply.unwrap();
    let v = rho(sample_rows(b, work)).unwrap();
    real_first_read(b, rho, archives); real_first_read(beta(n), rho, archives);
    sampled_exchange(b, rho, archives, work);
    assert(response_path(pre, result, checkpoint_end(b), delayed_slots(), t, a, v));
    held_path_is_an_ordinary_opportunity(n, pre, result, t, a, v);
    pair_from_ordinary_path(n, m, first, result, replay(|x,w| cell(x,w), after_receipt(n), a), a, v);
}

pub proof fn covered_metadata_gives_real_hot_pair<K>(
    n: Notice, field: Inspect<K>, ready: Ready<K>, pick: ChooseValue, menu: Set<Replica>, archives: Set<Replica>,
)
    requires pair().subset_of(menu), eventual(rpc(menu, resolve(field, ready, pick)), |e| fair(menu, e)),
        stock_compatible(field, inspect(field, unadvanced_rows())),
    ensures ({
        let rho = resolve(field, ready, pick); let a = read_actions(alpha(n), BeforeSample::Unchanged);
        incompatible_completions(n, machine(rho, archives), |s: Local| s.first.reply.unwrap(), |s: Local| s.returned,
            a, pick(unadvanced_rows()))
    }),
{
    stock_progress_enables_inspected_gate(field, ready, pick, menu);
    actual_disk_before_sr2(alpha(n), 17, Replica::R1); actual_disk_before_sr2(alpha(n), 17, Replica::R2);
    assert(sample_rows(alpha(n), BeforeSample::Unchanged) =~= unadvanced_rows());
    returning_samples_contradict_h(n, resolve(field, ready, pick), archives, BeforeSample::Unchanged);
}

}
