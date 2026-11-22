use vstd::prelude::*;
use crate::{Replica, first_quorum};
use crate::checkpoint::*;
use crate::confirmation::after_receipt;
use crate::delivery::*;
use crate::metadata_pair::*;
use crate::metadata_provenance::*;
use crate::metadata_stock::*;
use crate::mixed_read::two_rows;
use crate::mixed_sources::actual_disk_before_sr2;
use crate::ordered_store::*;
use crate::protocol::*;
use crate::quorum_rpc::{Resolver, fair, latest};
use crate::rpc_majority::{rpc_stock, any_majority_stock_read};
use crate::service::*;
use crate::stock_availability::*;
use crate::stock_reports::{Evidence, Observable, audited_stock, authentic_guard_preserves_stock, return_guard, from_log, has_log};
use crate::survivors::postcrash_schedule_has_only_live_actors;

verus! {

// One decoder, mailbox, majority test and resolver for both clients. A
// first-read compact report is only issued at ordinary log position zero.
pub open spec fn single(rho: Resolver, archives: Set<Replica>) -> LocalProtocol<Local,int,Wire> {
    duplex(rho,rho,archives)
}

pub open spec fn starts_sr2(b: Fork, rho: Resolver, archives: Set<Replica>) -> LocalProtocol<Local,int,Wire> {
    resume_at(single(rho,archives),checkpoint_observations(b))
}

pub(crate) proof fn compare_after_first(b: Fork, rho: Resolver, archives: Set<Replica>, t: States, a: Actions, v: int)
    requires rho(first_rows(b,13)) == Some(first_value(b)), t[0] == checkpoint_end(b), trace(|x,w| cell(x,w),t,a),
    ensures ({
        let res = |s: Local| s.returned;
        response_path(starts_sr2(b,rho,archives),res,checkpoint_end(b),delayed_slots(),t,a,v)
            == response_path(resumed(b,rho,archives),res,checkpoint_end(b),delayed_slots(),t,a,v)
    }),
{
    hide(memory); hide(accepted); hide(crate::metadata_pair::step); hide(permits); hide(at_cut); hide(checkpoint_observations);
    let es = observations(t,a); let m = starts_sr2(b,rho,archives); let old = resumed(b,rho,archives);
    real_first_with(rho,rho,b,archives); real_first_read(b,rho,archives);
    assert(m.initial =~= old.initial);
    postcrash_schedule_has_only_live_actors(|x,w|cell(x,w),t,a,a.len());
    assert forall|i: int,x: Local| 0 <= i < a.len() implies #[trigger] same_callbacks(m,old,x,es[i]) by {
        assert(es[i].actor != Process::FirstClient);
    }
    response_uses_local_callbacks(m,old,|s: Local| s.returned,checkpoint_end(b),delayed_slots(),t,a,v);
}

pub proof fn same_reader_pair(n: Notice, rho: Resolver, archives: Set<Replica>, work: BeforeSample)
    requires rho(first_rows(alpha(n),13)) == Some(5), rho(first_rows(beta(n),13)) == Some(2),
        work is RestoreImages ==> live_pair().subset_of(archives), rho(sample_rows(alpha(n),work)).is_some(),
    ensures incompatible_completions(n,single(rho,archives),|s: Local| s.returned.unwrap(),|s: Local| s.returned,
        read_actions(alpha(n),work),rho(sample_rows(alpha(n),work)).unwrap()),
{
    hide(memory); hide(replay); hide(accepted);
    let b=alpha(n); let m=single(rho,archives); let pre=starts_sr2(b,rho,archives); let res=|s: Local| s.returned;
    let v=rho(sample_rows(b,work)).unwrap(); let a=read_actions(b,work); let t=read_states(b,work);
    real_first_with(rho,rho,b,archives); real_first_with(rho,rho,beta(n),archives);
    real_first_read(b,rho,archives); sampled_exchange(b,rho,archives,work);
    assert(response_path(resumed(b,rho,archives),res,checkpoint_end(b),delayed_slots(),t,a,v));
    compare_after_first(b,rho,archives,t,a,v);
    held_path_is_an_ordinary_opportunity(n,pre,res,t,a,v);
    pair_from_ordinary_path(n,m,|s: Local| s.returned.unwrap(),res,replay(|x,w| cell(x,w),after_receipt(n),a),a,v);
}

// A checkpoint-number inspection can be a genuine readiness condition,
// while the decision still selects by full raw position (including ties).
pub open spec fn epochs(m: Rows) -> Map<Replica,nat> {
    Map::new(m.dom(), |r: Replica| m[r].version / 8)
}

proof fn unanimous_in_epoch_zero(b: Fork)
    ensures stock_validator(|m: Rows| epochs(m))(first_rows(b,13)) == Some(first_value(b)),
{
    let first = first_rows(b,13); let q = first_quorum(b.branch);
    let pos: nat = if b.branch == crate::Branch::Alpha { 4 } else { 1 };
    let log = crate::ordered_store::split_stock().log;
    let rows = Map::new(q, |r: Replica| Stamp { version: pos, value: first_value(b) });
    crate::ordered_store::reachable_mixed_stock();
    reveal_with_fuel(value_at,5);
    assert(from_log(log,rows));
    assert(inspect(|m: Rows| epochs(m),rows).values =~= inspect(|m: Rows| epochs(m),first).values);
    assert(epochs(rows) =~= epochs(first));
    assert(stock_compatible(|m: Rows| epochs(m),inspect(|m: Rows| epochs(m),first)));
}

pub proof fn stock_epoch_reader_returns_on_the_direct_pair(n: Notice, archives: Set<Replica>)
    ensures ({
        let rho = stock_validator(|m: Rows| epochs(m));
        read_a(rpc_stock(rho),|e| fair(all_replicas(),e)) && rho(two_rows(false))==Some(5)
            && incompatible_completions(n,single(rho,archives),|s: Local| s.returned.unwrap(),|s: Local| s.returned,
                read_actions(alpha(n),BeforeSample::Unchanged),2)
    }),
{
    let field = |m: Rows| epochs(m); let rho = stock_validator(field);
    validator_has_stock_availability(field);
    assert(epochs(unadvanced_rows()) =~= epochs(two_rows(false)));
    assert(inspect(field,unadvanced_rows()).values =~= inspect(field,two_rows(false)).values);
    exact_split_comparison(field);
    stock_progress_enables_inspected_gate(field,|x|stock_compatible(field,x),|m|latest_value(m),all_replicas());
    let b = alpha(n); actual_disk_before_sr2(b,17,Replica::R1); actual_disk_before_sr2(b,17,Replica::R2);
    assert(sample_rows(b,BeforeSample::Unchanged) =~= unadvanced_rows());
    unanimous_in_epoch_zero(b); unanimous_in_epoch_zero(beta(n));
    same_reader_pair(n,rho,archives,BeforeSample::Unchanged);
}

pub open spec fn equal_reports(q: Set<Replica>, row: Stamp) -> Rows {
    Map::new(q, |_r: Replica| row)
}

// Allows arbitrary identity-dependent results and arbitrary metadata checks
// on disagreements. It constrains only readiness on a unanimous stamped
// quorum; this off-stock property is independent of H.
pub open spec fn ready_on_any_unanimous_quorum(rho: Resolver) -> bool {
    forall|q: Set<Replica>, p: Set<Replica>, row: Stamp| majority(q) && majority(p)
        ==> (#[trigger] rho(equal_reports(q,row))).is_some() == (#[trigger] rho(equal_reports(p,row))).is_some()
}

pub(crate) proof fn actual_first_decision(b: Fork, rho: Resolver, archives: Set<Replica>)
    requires completed_quorum_sample(single(rho,archives),|s: Local| s.returned.unwrap(),b),
    ensures rho(first_rows(b,13))==Some(first_value(b)),
{
    let m=single(rho,archives);
    prefix_control(rho,rho,b,archives,Process::FirstClient,13); prefix_control(rho,rho,b,archives,Process::FirstClient,14);
    stable_responder_cells_fix_first_sample(m,|s: Local| s.returned.unwrap(),b);
}

// For this route a stock match is unnecessary. The independently completed
// beta SR1 supplies readiness at exactly the same stamp as a real W1 copy
// can produce at R2. The data send here is a weak-path capability of this
// machine, separate from any ordinary strong request/reply rounds.
pub proof fn unanimous_quorum_transfer(n: Notice, rho: Resolver, archives: Set<Replica>)
    requires ready_on_any_unanimous_quorum(rho),
        completed_quorum_sample(single(rho,archives),|s: Local| s.returned.unwrap(),alpha(n)),
        completed_quorum_sample(single(rho,archives),|s: Local| s.returned.unwrap(),beta(n)),
    ensures ({
        let work=BeforeSample::DeliverW1; let rows=sample_rows(alpha(n),work);
        rho(rows).is_some() && incompatible_completions(n,single(rho,archives),|s: Local| s.returned.unwrap(),
            |s: Local| s.returned,read_actions(alpha(n),work),rho(rows).unwrap())
    }),
{
    let a=alpha(n); let b=beta(n); let row=Stamp { version: 0, value: 2 };
    actual_first_decision(a,rho,archives); actual_first_decision(b,rho,archives);
    actual_disk_before_sr2(a,17,Replica::R1); actual_disk_before_sr2(a,17,Replica::R2);
    assert(equal_reports(first_quorum(b.branch),row) =~= first_rows(b,13));
    assert(equal_reports(live_pair(),row) =~= sample_rows(a,BeforeSample::DeliverW1));
    assert(rho(equal_reports(first_quorum(b.branch),row)).is_some() == rho(equal_reports(live_pair(),row)).is_some());
    same_reader_pair(n,rho,archives,BeforeSample::DeliverW1);
}

pub proof fn coherence_read_on_the_two_actual_forks(n: Notice)
    ensures ({
        let rho=|m: Rows| crate::mixed_sources::checked_latest(m); let empty=Set::empty(); let res=|s: Local| s.returned;
        read_a(rpc_stock(rho),|e|fair(all_replicas(),e))
            && incompatible_completions(n,single(rho,empty),|s: Local| s.returned.unwrap(),res,
                read_actions(alpha(n),BeforeSample::DeliverW1),2)
            && (forall|b: Fork,t: States,a: Actions,v: int|
                b.notice==n && #[trigger] response_path(starts_sr2(b,rho,empty),res,checkpoint_end(b),delayed_slots(),t,a,v)
                ==> exists|i: int,r: Replica| 0<=i<a.len() && live_pair().contains(r) && #[trigger] issued_install(t,a,i,r))
    }),
{
    hide(checkpoint_observations); hide(memory); hide(accepted); hide(resumed);
    let rho=|m: Rows| crate::mixed_sources::checked_latest(m); let empty=Set::empty(); let res=|s: Local| s.returned;
    crate::mixed_sources::stock_available_validator_separates_both_cuts(alpha(n));
    assert forall|q: Set<Replica>, p: Set<Replica>, row: Stamp| majority(q) && majority(p) implies
        (#[trigger] rho(equal_reports(q,row))).is_some() == (#[trigger] rho(equal_reports(p,row))).is_some() by {
        assert(crate::stock_reports::consistent_versions(equal_reports(q,row)));
        assert(crate::stock_reports::consistent_versions(equal_reports(p,row)));
    }
    assert(crate::stock_reports::consistent_versions(first_rows(alpha(n),13))
        && crate::stock_reports::consistent_versions(first_rows(beta(n),13)));
    real_first_with(rho,rho,alpha(n),empty); real_first_with(rho,rho,beta(n),empty);
    unanimous_quorum_transfer(n,rho,empty);
    actual_disk_before_sr2(alpha(n),17,Replica::R1); actual_disk_before_sr2(alpha(n),17,Replica::R2);
    assert forall|b: Fork,t: States,a: Actions,v: int| b.notice==n
        && #[trigger] response_path(starts_sr2(b,rho,empty),res,checkpoint_end(b),delayed_slots(),t,a,v)
        implies exists|i: int,r: Replica| 0<=i<a.len() && live_pair().contains(r) && #[trigger] issued_install(t,a,i,r) by {
        assert(b==alpha(n) || b==beta(n));
        compare_after_first(b,rho,empty,t,a,v);
        coherence_requires_a_physical_cause(b,rho,empty,t,a,v);
    }
}

// A designated reference site can permit a cheaper unanimous-read check.
// Without that site, position zero is validated against the ordinary
// initial image. This remains an any-majority protocol on stock states.
pub open spec fn unanimous(m: Rows) -> bool {
    forall|i: Replica,j: Replica| #[trigger] m.contains_key(i) && #[trigger] m.contains_key(j) ==> m[i].value==m[j].value
}

pub open spec fn valid_root(m: Rows) -> bool {
    forall|r: Replica| #[trigger] m.contains_key(r) && m[r].version==0 ==> m[r].value==sample(initial_store(),r).value
}

pub open spec fn root_or_reference(reference: Replica, m: Rows) -> bool {
    (m.contains_key(reference) && unanimous(m)) || valid_root(m)
}

pub open spec fn reference_read(reference: Replica) -> Resolver {
    |m: Rows| if root_or_reference(reference,m) { latest(m) } else { None }
}

proof fn authentic_roots_pass(reference: Replica)
    ensures forall|m: Rows| #[trigger] has_log(m) ==> root_or_reference(reference,m),
{
    assert forall|m: Rows| #[trigger] has_log(m) implies root_or_reference(reference,m) by {
        let log=choose|log: Seq<Command>| #[trigger] from_log(log,m);
        assert forall|r: Replica| #[trigger] m.contains_key(r) && m[r].version==0 implies m[r].value==sample(initial_store(),r).value by {
            assert(authentic(log,m[r]));
        }
    }
}

pub proof fn reference_validation_keeps_full_stock_histories<X,E>(reference: Replica,
    p: ReadSystem<X,E>, fair: spec_fn(Stream<X,E>)->bool, view: spec_fn(X)->Evidence, event: spec_fn(X,E,X)->Observable)
    requires audited_stock(p,view,event),
    ensures ({
        let q=guarded(p,|s,e,t| return_guard(p,view,|m| root_or_reference(reference,m),s,t));
        (read_a(p,fair) ==> read_a(q,fair))
            && (forall|t: Seq<X>,a: Seq<E>| #[trigger] finite_stock_run(p,t,a)==finite_stock_run(q,t,a))
            && (forall|e: Stream<X,E>| #[trigger] infinite_stock_run(p,e)==infinite_stock_run(q,e))
    }),
{
    authentic_roots_pass(reference);
    authentic_guard_preserves_stock(p,fair,view,event,|m| root_or_reference(reference,m));
}

pub proof fn reference_serves_all_stock_majorities(reference: Replica)
    ensures read_a(rpc_stock(reference_read(reference)),|e| fair(all_replicas(),e)),
{
    let rho = reference_read(reference);
    authentic_roots_pass(reference);
    assert forall|m: Rows| majority(m.dom()) && has_log(m) implies {
        let v = #[trigger] rho(m);
        v.is_some() && exists|r: Replica| #[trigger] m.contains_key(r) && v==Some(m[r].value)
    } by {
        crate::quorum_rpc::latest_is_a_sample(m);
    }
    any_majority_stock_read(rho);
}

// A returns no verdict on off-stock histories. Both SR1s *really finish*
// with this same read code. After R3 fails, even processing every possible
// weak data or status input cannot substitute for a missing ordinary image.
pub proof fn reference_reader_after_actual_sr1(b: Fork, archives: Set<Replica>)
    ensures ({
        let rho=reference_read(Replica::R3); let m=single(rho,archives); let pre=starts_sr2(b,rho,archives);
        read_a(rpc_stock(rho),|e|fair(all_replicas(),e)) && accepted(m,checkpoint_observations(b))
            && completed_quorum_sample(m,|s: Local| s.returned.unwrap(),b)
            && first_result(m,|s: Local| s.returned.unwrap(),b)==first_value(b)
            && pre_sr1_g(b,weak_assignment(b,true).ops) && truthful_notice(b,weak_assignment(b,true).ops)
            && (can_respond(pre,|s: Local| s.returned,checkpoint_end(b),delayed_slots()) == live_pair().subset_of(archives))
    }),
{
    hide(accepted); hide(memory); hide(checkpoint_observations); hide(resumed);
    let rho=reference_read(Replica::R3); let res=|s: Local| s.returned; let net=checkpoint_end(b); let ids=delayed_slots();
    let pre=starts_sr2(b,rho,archives); let old=resumed(b,rho,archives);
    assert(unanimous(first_rows(b,13)));
    real_first_with(rho,rho,b,archives); reference_serves_all_stock_majorities(Replica::R3);
    weak_assignment_at_delivery(b,true);
    assert(checks_genesis_at(rho,live_pair()));
    when_genesis_validation_can_complete(b,rho,archives);
    assert forall|t: States,a: Actions,v: int| #[trigger] response_path(pre,res,net,ids,t,a,v)
        == #[trigger] response_path(old,res,net,ids,t,a,v) by {
        if trace(|x,w|cell(x,w),t,a) && t[0] == net { compare_after_first(b,rho,archives,t,a,v); }
    }
    if can_respond(old,res,net,ids) {
        let (t,a,v)=choose|t: States,a: Actions,v: int| #[trigger] response_path(old,res,net,ids,t,a,v);
        assert(response_path(pre,res,net,ids,t,a,v));
    }
    if can_respond(pre,res,net,ids) {
        let (t,a,v)=choose|t: States,a: Actions,v: int| #[trigger] response_path(pre,res,net,ids,t,a,v);
        assert(response_path(old,res,net,ids,t,a,v));
    }
    assert(can_respond(pre,res,net,ids) == live_pair().subset_of(archives));

}


// The scheduled C2 poll is always enabled for a live C2. Its only possible
// change is local completion from the saved samples. In particular the poll
// neither reads the weak-status field nor creates an update or a packet.
pub proof fn poll_on_saved_samples(rho: Resolver, s: Local, net: Network<int,Wire>)
    requires live(net,Process::SecondClient),
    ensures ({
        let a=Action::Strong(Process::SecondClient); let e=process_step(net,a);
        let result=if s.returned.is_none() && majority(s.rows.dom()) {rho(s.rows)} else {s.returned};
        enabled(net,a) && permits(s,e) && crate::metadata_pair::step(rho,s,e)==(Local { returned: result, ..s })
            && advance(|x,w|cell(x,w),net,a)==net
    }),
{
    let a=Action::Strong(Process::SecondClient);
    assert(advance(|x,w|cell(x,w),net,a).locals =~= net.locals);
}

pub proof fn reference_pair_by_repair_availability(n: Notice, archives: Set<Replica>)
    ensures ({
        let rho=reference_read(Replica::R3); let m=single(rho,archives); let res=|s: Local|s.returned;
        if live_pair().subset_of(archives) {
            incompatible_completions(n,m,|s: Local|s.returned.unwrap(),res,
                read_actions(alpha(n),BeforeSample::RestoreImages),1)
        } else {
            !can_respond(starts_sr2(alpha(n),rho,archives),res,checkpoint_end(alpha(n)),delayed_slots())
                && !can_respond(starts_sr2(beta(n),rho,archives),res,checkpoint_end(beta(n)),delayed_slots())
        }
    }),
{
    hide(incompatible_completions); hide(response_path); hide(can_respond); hide(accepted); hide(completed_quorum_sample);
    hide(starts_sr2); hide(single); hide(checkpoint_end); hide(checkpoint_observations); hide(read_actions); hide(memory);
    let rho=reference_read(Replica::R3); let b=alpha(n);
    reference_reader_after_actual_sr1(b,archives); reference_reader_after_actual_sr1(beta(n),archives);
    if live_pair().subset_of(archives) {
        actual_disk_before_sr2(b,17,Replica::R1); actual_disk_before_sr2(b,17,Replica::R2);
        let rows=sample_rows(b,BeforeSample::RestoreImages);
        assert(valid_root(rows) && rho(rows)==Some(1));
        assert(unanimous(first_rows(b,13)) && unanimous(first_rows(beta(n),13)));
        same_reader_pair(n,rho,archives,BeforeSample::RestoreImages);
    }
}

}
