use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::metadata_pair::*;
use crate::metadata_stock::*;
use crate::metadata_repair::{genesis_rows, stock_reads_its_genesis_image};
use crate::mixed_sources::{actual_disk_before_sr2, checked_latest};
use crate::quorum_rpc::fair;
use crate::rpc_majority::rpc_stock;
use crate::stock_availability::read_a;
use crate::stock_reports::consistent_versions;
use crate::ordered_store::{Stamp, majority, initial_store, sample};
use crate::protocol::*;
use crate::quorum_rpc::Resolver;
use crate::service::{response_path, can_respond};
use crate::survivors::postcrash_schedule_has_only_live_actors;

verus! {

pub type States = Seq<Network<int, Wire>>;
pub type Actions = Seq<Action<Wire>>;

pub open spec fn own(r: Replica) -> int { if r == Replica::R1 { 2 } else { 5 } }
pub open spec fn foreign(r: Replica) -> int { if r == Replica::R1 { 5 } else { 2 } }

pub open spec fn restore_at(t: States, a: Actions, i: int, r: Replica) -> bool {
    a[i] == Action::Local(r, Wire::Copy(1)) && (t[i].locals)(r) != 1 && (t[i+1].locals)(r) == 1
}

pub open spec fn new_copy_at(t: States, a: Actions, i: int, r: Replica) -> bool {
    match a[i] {
        Action::Deliver(id) => {
            let p = t[i].pending[id];
            t[i].pending.contains_key(id) && p.path == Path::Weak && p.to == at(r)
                && p.input == Wire::Copy(foreign(r)) && (t[i].locals)(r) != foreign(r)
                && (t[i+1].locals)(r) == foreign(r)
        },
        _ => false,
    }
}

// Each cause precedes the send at which this value was sampled.
pub open spec fn explains(t: States, a: Actions, k: nat, r: Replica, v: int, archives: Set<Replica>) -> bool {
    v == own(r)
        || (v == 1 && archives.contains(r) && exists|i: int| 0 <= i < k && #[trigger] restore_at(t, a, i, r))
        || (v == foreign(r) && exists|i: int| 0 <= i < k && #[trigger] new_copy_at(t, a, i, r))
}

pub open spec fn sent_sample(t: States, a: Actions, k: nat, id: nat, p: Packet<Wire>, archives: Set<Replica>) -> bool {
    let r = p.from->At_0;
    exists|h: int| 0 <= h < k && #[trigger] a[h] == Action::Send(id, p)
        && (t[h].locals)(r) == signed_row(p).value && explains(t, a, h as nat, r, signed_row(p).value, archives)
}

pub open spec fn took_sample(t: States, a: Actions, k: nat, r: Replica, row: Stamp, archives: Set<Replica>) -> bool {
    exists|d: int| 0 <= d < k && match #[trigger] a[d] {
        Action::Deliver(id) => {
            let p = t[d].pending[id];
            t[d].pending.contains_key(id) && replica_answer(p) && p.from == at(r) && signed_row(p) == row
                && sent_sample(t, a, d as nat, id, p, archives)
        },
        _ => false,
    }
}

pub open spec fn authentic_copy(p: Packet<Wire>) -> bool {
    p.path == Path::Weak && p.from is At && p.to is At && p.from != p.to && (p.input == Wire::Copy(2) || p.input == Wire::Copy(5))
}

pub open spec fn local_at(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, k: nat, p: Process) -> Local {
    memory(resumed(b, rho, archives), p, observations(t, a), k)
}

pub open spec fn accounts(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, k: nat) -> bool {
    let n = t[k as int]; let c = local_at(b, rho, archives, t, a, k, Process::SecondClient);
    (forall|r: Replica| {
        let s = #[trigger] local_at(b, rho, archives, t, a, k, at(r));
        s.applied.len() == 0 && s.backup == startup(at(r), archives).backup
            && (live_pair().contains(r) ==> explains(t, a, k, r, (n.locals)(r), archives))
    })
    && (forall|id: nat| #[trigger] n.pending.contains_key(id) ==> {
        let p = n.pending[id];
        (p.input is Copy ==> authentic_copy(p))
            && (replica_answer(p) ==> live_pair().contains(p.from->At_0) && signed_row(p).version == 0
                && sent_sample(t, a, k, id, p, archives))
    })
    && (forall|r: Replica| #[trigger] c.rows.contains_key(r) ==>
        live_pair().contains(r) && c.rows[r].version == 0 && took_sample(t, a, k, r, c.rows[r], archives))
}

// Isolate the physical fork description from the local induction.
proof fn initial_sources(b: Fork)
    ensures crate::survivors::after_crash(checkpoint_end(b)),
        forall|r: Replica| live_pair().contains(r) ==> #[trigger] (checkpoint_end(b).locals)(r) == own(r),
        forall|id: nat| #[trigger] checkpoint_end(b).pending.contains_key(id) ==> {
            let p = checkpoint_end(b).pending[id];
            !replica_answer(p) && (p.input is Copy ==> authentic_copy(p) && p.to == at(Replica::R3))
        },
{}

proof fn advance_clock(t: States, a: Actions, k: nat, archives: Set<Replica>)
    ensures
        forall|r: Replica, v: int| #[trigger] explains(t, a, k, r, v, archives) ==> explains(t, a, k+1, r, v, archives),
        forall|id: nat, p: Packet<Wire>| #[trigger] sent_sample(t, a, k, id, p, archives) ==> sent_sample(t, a, k+1, id, p, archives),
        forall|r: Replica, row: Stamp| #[trigger] took_sample(t, a, k, r, row, archives) ==> took_sample(t, a, k+1, r, row, archives),
{}

pub proof fn account_for_each_message(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, k: nat)
    requires t[0] == checkpoint_end(b), trace(|x,w| cell(x,w), t, a),
        accepted(resumed(b, rho, archives), observations(t, a)), k <= a.len(),
    ensures accounts(b, rho, archives, t, a, k),
    decreases k,
{
    hide(checkpoint_end); hide(checkpoint_control); hide(checkpoint_observations); hide(change_control);
    initial_sources(b);
    let c = Process::SecondClient;
    let m = resumed(b, rho, archives); let es = observations(t, a);
    if k == 0 {
        real_first_read(b, rho, archives);
        assert((m.initial)(c) == at_cut(b,c,archives));
        assert(local_at(b,rho,archives,t,a,k,c).rows == Map::<Replica, Stamp>::empty());
        assert forall|r: Replica| {
            let s = #[trigger] local_at(b, rho, archives, t, a, k, at(r));
            s.applied.len() == 0 && s.backup == startup(at(r), archives).backup
                && (live_pair().contains(r) ==> explains(t, a, k, r, (t[0].locals)(r), archives))
        } by { assert((m.initial)(at(r)) == at_cut(b, at(r), archives)); }
    } else {
        let h = (k - 1) as nat; let i = h as int;
        account_for_each_message(b, rho, archives, t, a, h);
        advance_clock(t, a, h, archives);
        let n = t[i]; let u = t[k as int]; let ac = a[i]; let ev = es[i];
        let actor = local_at(b, rho, archives, t, a, h, ev.actor);
        assert(enabled(n, ac) && u == advance(|x,w| cell(x,w), n, ac));
        assert((m.accept)(actor, ev));
        postcrash_schedule_has_only_live_actors(|x,w| cell(x,w), t, a, h);
        assert forall|r: Replica| {
            let s = #[trigger] local_at(b, rho, archives, t, a, k, at(r));
            s.applied.len() == 0 && s.backup == startup(at(r), archives).backup
                && (live_pair().contains(r) ==> explains(t, a, k, r, (u.locals)(r), archives))
        } by {
            let prev = local_at(b, rho, archives, t, a, h, at(r));
            assert(prev.applied.len() == 0 && prev.backup == startup(at(r), archives).backup);
            if live_pair().contains(r) {
                assert(explains(t, a, h, r, (n.locals)(r), archives));
                if (u.locals)(r) != (n.locals)(r) {
                    match ac {
                        Action::Local(site, Wire::Copy(v)) => {
                            assert(site == r && archives.contains(r) && v == 1 && restore_at(t, a, i, r));
                        },
                        Action::Deliver(id) => {
                            assert(n.pending.contains_key(id) && authentic_copy(n.pending[id]));
                            if (u.locals)(r) != own(r) { assert(new_copy_at(t, a, i, r)); }
                        },
                        _ => {},
                    }
                }
            }
        }
        assert forall|id: nat| #[trigger] u.pending.contains_key(id) implies {
            let p = u.pending[id];
            (p.input is Copy ==> authentic_copy(p)) && (replica_answer(p) ==> live_pair().contains(p.from->At_0)
                && signed_row(p).version == 0 && sent_sample(t, a, k, id, p, archives))
        } by {
            let p = u.pending[id];
            if ac == Action::Send(id,p) {
                if replica_answer(p) {
                    let r = p.from->At_0;
                    assert(live_pair().contains(r));
                    assert(actor.applied.len() == 0) by { assert(ev.actor == at(r)); assert(local_at(b,rho,archives,t,a,h,at(r)).applied.len()==0); }
                    assert(explains(t, a, h, r, (n.locals)(r), archives));
                    assert(a[i] == Action::Send(id,p));
                }
            } else { assert(n.pending.contains_key(id) && n.pending[id] == p); }
        }
        let old = local_at(b, rho, archives, t, a, h, c);
        let next = local_at(b, rho, archives, t, a, k, c);
        assert forall|r: Replica| #[trigger] next.rows.contains_key(r) implies
            live_pair().contains(r) && next.rows[r].version == 0 && took_sample(t,a,k,r,next.rows[r],archives) by {
            if old.rows.contains_key(r) { assert(old.rows[r] == next.rows[r]); }
            else {
                let id = ac->Deliver_0; let p = n.pending[id];
                assert(ac == Action::Deliver(id) && n.pending.contains_key(id) && replica_answer(p) && p.from == at(r));
                assert(sent_sample(t, a, h, id, p, archives));
            }
        }
    }
}

pub proof fn authenticated_result(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, v: int) -> (rows: Rows)
    requires response_path(resumed(b, rho, archives), |s: Local| s.returned, checkpoint_end(b), delayed_slots(), t, a, v),
    ensures rows.dom() == live_pair(), rho(rows) == Some(v),
        forall|r: Replica| #[trigger] rows.contains_key(r) ==> rows[r].version == 0
            && took_sample(t, a, a.len(), r, rows[r], archives) && explains(t, a, a.len(), r, rows[r].value, archives),
{
    hide(checkpoint_end); hide(checkpoint_observations); hide(change_control); hide(at_cut); hide(permits);
    let m = resumed(b, rho, archives); let es = observations(t, a); let c = Process::SecondClient;
    assert(a.len() > 0); let h = (a.len() - 1) as nat;
    let done = memory(m, c, es, a.len()); let s = memory(m, c, es, h);
    assert(s.returned.is_none() && done.returned == Some(v));
    assert(es[h as int].actor == c && es[h as int].action == Action::Strong(c));
    assert(majority(s.rows.dom()) && rho(s.rows) == Some(v));
    account_for_each_message(b, rho, archives, t, a, a.len());
    assert(s.rows == done.rows);
    assert(s.rows.dom() =~= live_pair());
    assert forall|r: Replica| #[trigger] s.rows.contains_key(r) implies s.rows[r].version == 0
        && took_sample(t, a, a.len(), r, s.rows[r], archives) && explains(t, a, a.len(), r, s.rows[r].value, archives) by {
        let row = s.rows[r]; assert(took_sample(t, a, a.len(), r, row, archives));
        let d = choose|d: int| 0 <= d < a.len() && match #[trigger] a[d] {
            Action::Deliver(id) => { let p = t[d].pending[id]; t[d].pending.contains_key(id) && replica_answer(p)
                && p.from == at(r) && signed_row(p) == row && sent_sample(t, a, d as nat, id, p, archives) }, _ => false,
        };
        let id = a[d]->Deliver_0; let p = t[d].pending[id];
        let h = choose|h: int| 0 <= h < d && #[trigger] a[h] == Action::Send(id,p)
            && (t[h].locals)(r) == signed_row(p).value && explains(t,a,h as nat,r,signed_row(p).value,archives);
        assert(explains(t,a,h as nat,r,row.value,archives));
    }
    s.rows
}

// A genuine weak installation is distinguished from a status receipt and
// an ordinary snapshot repair. Its packet came from an actual survivor
// still holding this write at the time of its offer.
pub proof fn weak_install_has_issuer(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, i: int, r: Replica)
    requires t[0] == checkpoint_end(b), trace(|x,w| cell(x,w), t, a), accepted(resumed(b, rho, archives), observations(t,a)),
        live_pair().contains(r), 0 <= i < a.len(), new_copy_at(t,a,i,r),
    ensures ({
        let id = a[i]->Deliver_0; let p = t[i].pending[id];
        live_pair().contains(p.from->At_0) && p.from != at(r)
            && exists|j: int| 0 <= j < i && #[trigger] a[j] == Action::Send(id,p) && (t[j].locals)(p.from->At_0) == foreign(r)
    }),
{
    hide(checkpoint_end); hide(checkpoint_observations); hide(memory); hide(response_path);
    hide(step); hide(change_control); hide(permits_step);
    initial_sources(b);
    let id = a[i]->Deliver_0; let p = t[i].pending[id];
    pending_packet_has_live_origin(|x,w| cell(x,w), t, a, i, id);
    assert(!(t[0].pending.contains_key(id) && t[0].pending[id] == p));
    let j = choose|j: int| 0 <= j < i && #[trigger] a[j] == Action::Send(id,p) && live(t[j],p.from);
    let es = observations(t,a);
    assert((resumed(b,rho,archives).accept)(memory(resumed(b,rho,archives),es[j].actor,es,j as nat),es[j]));
    postcrash_schedule_has_only_live_actors(|x,w| cell(x,w),t,a,(j+1) as nat);
    assert(a[j] == Action::Send(id,p) && (t[j].locals)(p.from->At_0) == foreign(r));
}

pub open spec fn checks_genesis(rho: Resolver) -> bool {
    forall|m: Rows, r: Replica| #[trigger] rho(m).is_some() && majority(m.dom()) && #[trigger] m.contains_key(r)
        && m[r].version == 0 ==> m[r].value == sample(initial_store(), r).value
}

pub open spec fn checks_genesis_at(rho: Resolver, quorum: Set<Replica>) -> bool {
    forall|m: Rows,r: Replica| #[trigger] rho(m).is_some() && m.dom()==quorum && #[trigger] m.contains_key(r)
        && m[r].version==0 ==> m[r].value==sample(initial_store(),r).value
}

pub proof fn full_position_validator_checks_genesis()
    ensures checks_genesis(stock_validator(|m: Rows| m)),
{
    let field = |m: Rows| m; let rho = stock_validator(field);
    assert forall|m: Rows, r: Replica| #[trigger] rho(m).is_some() && majority(m.dom()) && #[trigger] m.contains_key(r)
        && m[r].version == 0 implies m[r].value == sample(initial_store(), r).value by {
        assert(stock_compatible(field, inspect(field,m)));
        let (log, source) = choose|log: Seq<crate::ordered_store::Command>, source: Rows|
            #[trigger] crate::stock_reports::from_log(log,source) && inspect(field,source) == inspect(field,m);
        assert(source == m && crate::ordered_store::authentic(log,source[r]));
        assert(crate::ordered_store::value_at(log,0)==1);
    }
}

pub proof fn zero_checked_return_needs_both_images(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, v: int)
    requires checks_genesis_at(rho,live_pair()), response_path(resumed(b,rho,archives), |s: Local| s.returned, checkpoint_end(b), delayed_slots(),t,a,v),
    ensures live_pair().subset_of(archives),
        forall|r: Replica| #[trigger] live_pair().contains(r) ==> exists|i: int| 0 <= i < a.len() && #[trigger] restore_at(t,a,i,r),
{
    hide(response_path); hide(checkpoint_end); hide(observations); hide(took_sample); hide(resumed);
    let m = authenticated_result(b,rho,archives,t,a,v);
    assert(majority(m.dom()) && rho(m).is_some());
    assert forall|r: Replica| #[trigger] live_pair().contains(r) implies archives.contains(r) && exists|i: int|
        0 <= i < a.len() && #[trigger] restore_at(t,a,i,r) by {
        assert(m.contains_key(r) && m[r].version==0);
        assert(m[r].value==1 && explains(t,a,a.len(),r,1,archives));
    }
}


// A complete characterization in this local transition system. Every
// allowed interleaving, including an actual delivery of the old G notice,
// is covered on the necessary side. A finite ordinary path suffices on
// the possible side; it leaves the notice queued.
pub proof fn when_genesis_validation_can_complete(b: Fork, rho: Resolver, archives: Set<Replica>)
    requires checks_genesis_at(rho,live_pair()), read_a(rpc_stock(rho), |e| fair(all_replicas(), e)),
    ensures can_respond(resumed(b,rho,archives), |s: Local| s.returned, checkpoint_end(b), delayed_slots())
        == live_pair().subset_of(archives),
{
    hide(checkpoint_end); hide(checkpoint_observations); hide(resumed); hide(accepted); hide(trace);
    let m = resumed(b,rho,archives); let res = |s: Local| s.returned;
    let start = checkpoint_end(b); let reserved = delayed_slots();
    if live_pair().subset_of(archives) {
        let work = BeforeSample::RestoreImages;
        let t = read_states(b,work); let a = read_actions(b,work);
        stock_reads_its_genesis_image(rho);
        actual_disk_before_sr2(b,17,Replica::R1); actual_disk_before_sr2(b,17,Replica::R2);
        assert(sample_rows(b,work) =~= genesis_rows());
        real_first_read(b,rho,archives);
        assert((m.initial)(Process::SecondClient) == at_cut(b,Process::SecondClient,archives)) by { reveal(resumed); }
        sampled_exchange(b,rho,archives,work);
        assert(response_path(m,res,start,reserved,t,a,1));
    } else if can_respond(m,res,start,reserved) {
        let (t,a,v) = choose|t: States,a: Actions,v: int| #[trigger] response_path(m,res,start,reserved,t,a,v);
        zero_checked_return_needs_both_images(b,rho,archives,t,a,v);
    }
}

// Coherence is an ordinary stock property of admitted reports. The next
// theorem derives the possible sources of the values, without labeling the
// validation code itself as a weak action.
pub open spec fn requires_coherent_versions(rho: Resolver) -> bool {
    forall|rows: Rows| #[trigger] rho(rows).is_some() && majority(rows.dom()) ==> consistent_versions(rows)
}

pub open spec fn issued_install(t: States, a: Actions, i: int, r: Replica) -> bool {
    new_copy_at(t,a,i,r) && {
        let id = a[i]->Deliver_0; let p = t[i].pending[id];
        live_pair().contains(p.from->At_0) && p.from != at(r) && exists|j: int|
            0 <= j < i && #[trigger] a[j] == Action::Send(id,p) && (t[j].locals)(p.from->At_0) == foreign(r)
    }
}

pub proof fn coherence_requires_a_physical_cause(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, v: int)
    requires requires_coherent_versions(rho),
        response_path(resumed(b,rho,archives), |s: Local| s.returned, checkpoint_end(b), delayed_slots(), t,a,v),
    ensures (live_pair().subset_of(archives) && forall|r: Replica| #[trigger] live_pair().contains(r) ==>
            exists|i: int| 0 <= i < a.len() && #[trigger] restore_at(t,a,i,r))
        || exists|i: int,r: Replica| 0 <= i < a.len() && live_pair().contains(r) && #[trigger] issued_install(t,a,i,r),
{
    hide(checkpoint_end); hide(checkpoint_observations); hide(resumed); hide(accepted); hide(trace); hide(took_sample);
    let m = authenticated_result(b,rho,archives,t,a,v); let r1 = Replica::R1; let r2 = Replica::R2;
    assert(majority(m.dom()) && rho(m).is_some());
    assert(m.contains_key(r1) && m.contains_key(r2) && consistent_versions(m));
    let x = m[r1].value;
    assert(m[r1].version==0 && m[r2].version==0 && m[r2].value==x);
    assert(explains(t,a,a.len(),r1,x,archives) && explains(t,a,a.len(),r2,x,archives));
    if x == 1 {
        assert forall|r: Replica| #[trigger] live_pair().contains(r) implies archives.contains(r)
            && exists|i: int| 0 <= i < a.len() && #[trigger] restore_at(t,a,i,r) by {
            assert(m.contains_key(r) && m[r].value==1);
            assert(explains(t,a,a.len(),r,1,archives));
        }
    } else {
        let r = if x==2 { r2 } else { r1 };
        assert(x==foreign(r) && x!=own(r));
        assert(explains(t,a,a.len(),r,x,archives));
        let i = choose|i: int| 0 <= i < a.len() && #[trigger] new_copy_at(t,a,i,r);
        weak_install_has_issuer(b,rho,archives,t,a,i,r);
        assert(issued_install(t,a,i,r));
    }
}

// Nonvacuous causal test over all first returns, independent of H and of
// the answer. It concerns installing a weak payload, not an ordinary
// message, a CPU poll, a snapshot restore, or confirmation of a past copy.
pub open spec fn needs_foreign_install(b: Fork, rho: Resolver, archives: Set<Replica>) -> bool {
    let m = resumed(b,rho,archives); let res = |s: Local| s.returned;
    can_respond(m,res,checkpoint_end(b),delayed_slots()) && forall|t: States,a: Actions,v: int|
        #[trigger] response_path(m,res,checkpoint_end(b),delayed_slots(),t,a,v) ==>
        exists|i: int,r: Replica| 0 <= i < a.len() && live_pair().contains(r) && #[trigger] issued_install(t,a,i,r)
}

pub proof fn coherence_and_genesis_have_different_dependencies(b: Fork)
    ensures ({
        let c = |rows: Rows| checked_latest(rows); let g = stock_validator(|rows: Rows| rows); let none = Set::empty();
        read_a(rpc_stock(c), |e| fair(all_replicas(),e)) && read_a(rpc_stock(g), |e| fair(all_replicas(),e))
            && pre_sr1_g(b,weak_assignment(b,true).ops) && truthful_notice(b,weak_assignment(b,true).ops)
            && needs_foreign_install(b,c,none) && !needs_foreign_install(b,g,none)
            && !can_respond(resumed(b,g,none), |s: Local| s.returned, checkpoint_end(b), delayed_slots())
    }),
{
    hide(resumed); hide(accepted); hide(trace); hide(checkpoint_end); hide(checkpoint_observations);
    let c = |rows: Rows| checked_latest(rows); let none = Set::empty(); let res = |s: Local| s.returned;
    crate::mixed_sources::stock_available_validator_separates_both_cuts(b);
    weak_assignment_at_delivery(b,true);
    let g = stock_validator(|m: Rows| m);
    validator_has_stock_availability(|m: Rows| m);
    full_position_validator_checks_genesis();
    assert(checks_genesis_at(g,live_pair()));
    when_genesis_validation_can_complete(b,g,none);
    let work = BeforeSample::DeliverW1; let t = read_states(b,work); let a = read_actions(b,work);
    actual_disk_before_sr2(b,17,Replica::R1); actual_disk_before_sr2(b,17,Replica::R2);
    let rows = sample_rows(b,work);
    assert forall|i: Replica,j: Replica| #[trigger] rows.contains_key(i) && #[trigger] rows.contains_key(j)
        && rows[i].version==rows[j].version implies rows[i].value==rows[j].value by {};
    assert(c(rows)==Some(2));
    sampled_exchange(b,c,none,work); real_first_read(b,c,none);
    assert((resumed(b,c,none).initial)(Process::SecondClient)==at_cut(b,Process::SecondClient,none)) by {reveal(resumed);}
    assert(response_path(resumed(b,c,none),res,checkpoint_end(b),delayed_slots(),t,a,2));
    assert(requires_coherent_versions(c));
    assert forall|t: States,a: Actions,v: int| #[trigger] response_path(resumed(b,c,none),res,checkpoint_end(b),delayed_slots(),t,a,v)
        implies exists|i: int,r: Replica| 0 <= i < a.len() && live_pair().contains(r) && #[trigger] issued_install(t,a,i,r) by {
        coherence_requires_a_physical_cause(b,c,none,t,a,v);
    }
}

}
