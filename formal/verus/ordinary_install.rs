use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::{all_replicas,at,cell,checkpoint_end,state_after,Fork,Wire};
use crate::delivery::{self,Action,Network,Path};
use crate::facade_linear::{CommandSemantics,base_linearizable};
use crate::facade_quorum::Used;
use crate::facade_progress::{Run,StockRun,execution,project,front_fair,live_from};
use crate::stock_facade::*;
use crate::facade_contract::{stock_a,any_read_quorum,read_values_valid,outer_linearizable};
use crate::validator_block::{possible_leg,weak_value};

verus! {

// Ordinary storage exposes the application cell separately from all other
// local state and transport. The adapter adds no backup. Any actual
// backend snapshot remains part of the untouched backend memory.
pub struct Image<M> { pub cells: spec_fn(Replica)->int, pub other: M }
pub open spec fn physical<M,E>(p: Engine<Image<M>,E>) -> bool {
    forall|s: Image<M>,r:Replica| #[trigger] (p.cell)(s,r)==(s.cells)(r)
}

// A local integrity check on the ordinary installation, including an
// ordinary snapshot if the backend offers one. At genesis an inconsistent
// current image refuses installation until authorized by an ordinary
// command fence. Weak applications are separate writes to the SAME cell.
pub open spec fn install<M,E>(p: Engine<Image<M>,E>,s: State<Image<M>>,ev: Event<E>) -> State<Image<M>> {
    let next=step(p,s,ev);
    let cells=|r:Replica| if !s.closed.contains(r) && (s.base.cells)(r)!=1 {
        (s.base.cells)(r)
    } else {(next.base.cells)(r)};
    let changed=all_replicas().filter(|r| cells(r)!=(s.base.cells)(r));
    let closed=match ev {
        Event::Rpc(id,r,Stage::DeliverRequest) if s.calls[id].method is Command=>s.closed.union(changed).insert(r),
        _=>s.closed.union(changed),
    };
    State {base:Image {cells,..next.base},closed,..next}
}
pub proof fn stock_installation_is_identical<M,E>(p: Engine<Image<M>,E>,x: State<Image<M>>,ev: Event<E>)
    requires ports(p),physical(p),reachable(p,x),
    ensures install(p,x,ev)==step(p,x,ev),
{
    reachable_good(p,x);let y=step(p,x,ev);
    assert(install(p,x,ev).base.cells =~= y.base.cells) by {
        assert forall|r:Replica| #[trigger] (install(p,x,ev).base.cells)(r)==(y.base.cells)(r) by {
            assert((p.cell)(x.base,r)==(x.base.cells)(r));
            if !x.closed.contains(r) {assert((p.cell)(x.base,r)==1);}
        }
    }
    assert(install(p,x,ev).closed =~= y.closed);
}

pub open spec fn install_path<M,E>(p: Engine<Image<M>,E>,t: Seq<State<Image<M>>>,a: Seq<Event<E>>) -> bool {
    t.len()==a.len()+1 && forall|i:int| 0<=i<a.len() ==>
        enabled(p,t[i],#[trigger] a[i]) && t[i+1]==install(p,t[i],a[i])
}
proof fn at_ordinary_index<M,E>(p: Engine<Image<M>,E>,t: Seq<State<Image<M>>>,a: Seq<Event<E>>,i:nat)
    requires physical(p),ports(p),reachable(p,t[0]),path(p,t,a) || install_path(p,t,a),i<=a.len(),
    ensures reachable(p,t[i as int]),
    decreases i,
{
    if i>0 {
        let j=(i-1) as nat;at_ordinary_index(p,t,a,j);stock_installation_is_identical(p,t[j as int],a[j as int]);
        let pair=seq![t[j as int],t[i as int]];let action=seq![a[j as int]];
        crate::facade_quorum::extend_reach(p,t[j as int],pair,action);
    }
}
pub proof fn same_finite_executions<M,E>(p: Engine<Image<M>,E>,t: Seq<State<Image<M>>>,a: Seq<Event<E>>)
    requires physical(p),ports(p),reachable(p,t[0]),
    ensures install_path(p,t,a)==path(p,t,a),
{
    if install_path(p,t,a) || path(p,t,a) {
        assert forall|i:int| 0<=i<a.len() implies {
            let ev=#[trigger] a[i]; enabled(p,t[i],ev) && t[i+1]==install(p,t[i],ev) && t[i+1]==step(p,t[i],ev)
        } by {at_ordinary_index(p,t,a,i as nat);stock_installation_is_identical(p,t[i],a[i]);}
    }
}
pub open spec fn installed_execution<M,E>(p: Engine<Image<M>,E>,e: Run<Image<M>,E>) -> bool {
    (e.state)(0)==initial(p) && forall|i:nat| {
        let a=#[trigger] (e.event)(i); enabled(p,(e.state)(i),a) && (e.state)(i+1)==install(p,(e.state)(i),a)
    }
}
pub proof fn same_infinite_executions<M,E>(p: Engine<Image<M>,E>,e: Run<Image<M>,E>)
    requires physical(p),ports(p),
    ensures installed_execution(p,e)==execution(p,e),
{
    let s=initial(p);assert(path(p,seq![s],Seq::empty()));assert(reachable(p,s));
    if installed_execution(p,e) || execution(p,e) {
        assert forall|k:nat| {
            let a=#[trigger] (e.event)(k);let t=(e.state)(k);
            enabled(p,t,a) && (e.state)(k+1)==install(p,t,a) && (e.state)(k+1)==step(p,t,a)
        } by {
            let xs=Seq::new(k+1,|i:int|(e.state)(i as nat));let es=Seq::new(k,|i:int|(e.event)(i as nat));
            assert(path(p,xs,es) || install_path(p,xs,es)) by {
                if installed_execution(p,e) {
                    assert forall|i:int| 0<=i<k implies enabled(p,xs[i],#[trigger] es[i]) && xs[i+1]==install(p,xs[i],es[i]) by {};
                } else {
                    assert forall|i:int| 0<=i<k implies enabled(p,xs[i],#[trigger] es[i]) && xs[i+1]==step(p,xs[i],es[i]) by {};
                }
            }
            at_ordinary_index(p,xs,es,k);stock_installation_is_identical(p,(e.state)(k),(e.event)(k));
        }
    }
}
// Stock A and safety carry over because even the set of enabled events
// and the actual states agree on every finite and infinite stock schedule.
pub proof fn integrity_check_preserves_stock_smr<M,E>(p: Engine<Image<M>,E>,f: CommandSemantics,
    fair: spec_fn(StockRun<Image<M>,E>)->bool,used: Used<Image<M>,E>)
    requires physical(p),ports(p),stock_a(p,fair,used),base_linearizable(p,f),
    ensures any_read_quorum(p,used),read_values_valid(p,used),outer_linearizable(p,f),
        (forall|t: Seq<State<Image<M>>>,a: Seq<Event<E>>| reachable(p,t[0]) ==> #[trigger] install_path(p,t,a)==path(p,t,a)),
        forall|e: Run<Image<M>,E>,i:nat,id:nat| #[trigger] installed_execution(p,e) && fair(project(e)) && front_fair(p,e)
            && (#[trigger] (e.state)(i)).calls.contains_key(id) && #[trigger] live_from(p,project(e),i,id)
            ==> exists|k:nat| k>=i && (#[trigger] crate::facade_history::answer((e.state)(k),id)).is_some(),
{
    hide(any_read_quorum);hide(read_values_valid);hide(outer_linearizable);hide(path);hide(install_path);
    crate::facade_contract::construction_preserves_full_a_and_safety(p,f,fair,used);
    assert forall|t: Seq<State<Image<M>>>,a: Seq<Event<E>>| reachable(p,t[0]) implies
        #[trigger] install_path(p,t,a)==path(p,t,a) by {same_finite_executions(p,t,a);}
    assert forall|e: Run<Image<M>,E>| #[trigger] installed_execution(p,e) implies execution(p,e) by {same_infinite_executions(p,e);}
}

// Offstock the metadata, pending ordinary requests, and the results of all
// background backend computations are unconstrained. The validator gets its
// reports through its own physical RPC slots. An unauthorized ordinary
// attempt to install an image leaves the shared invalid genesis cell alone.
pub open spec fn invalid_cut<M>(s: State<Image<M>>) -> bool {
    s.closed.is_empty() && s.calls.dom()==set![1nat,2nat]
    && s.calls[1].method is Read && s.calls[1].answer.is_some()
    && s.calls[2].method is Read && s.calls[2].answer.is_none() && !s.calls[2].submitted
    && (forall|r:Replica| #[trigger] possible_leg(r,(s.calls[2].legs)(r)))
    && forall|r:Replica| weak_value((#[trigger] (s.base.cells)(r)))
}
pub proof fn ordinary_work_including_repairs<M,E>(p: Engine<Image<M>,E>,s: State<Image<M>>,ev: Event<E>)
    requires physical(p),invalid_cut(s),!(ev is Invoke),enabled(p,s,ev),!(p.up)(s.base).contains(Replica::R3),
    ensures invalid_cut(install(p,s,ev)),!(input(s,ev) is Submit),
        install(p,s,ev).base.other==((p.step)(s.base,input(s,ev))).other,
        install(p,s,ev).base.cells==s.base.cells,
{
    crate::validator_block::invalid_mailbox(s.calls[2]);
    let u=install(p,s,ev);assert(u.base.cells =~= s.base.cells);assert(u.closed =~= s.closed);assert(u.calls.dom() =~= s.calls.dom());
    assert forall|r:Replica| #[trigger] possible_leg(r,(u.calls[2].legs)(r)) by {
        assert(possible_leg(r,(s.calls[2].legs)(r)));assert(weak_value((s.base.cells)(r)));
    }
}

// Keep the two physical call mailboxes of the real cut. The untouched
// backend portion can contain any private memories and in-flight traffic.
pub open spec fn at_checkpoint<M>(b: Fork,other:M) -> State<Image<M>> {
    let cut=crate::facade_hybrid::prefix(b,17);
    State {base:Image{cells:state_after(b,17).locals,other},closed:cut.closed,calls:cut.calls}
}
pub open spec fn receive_copy<M>(s: State<Image<M>>,n: Network<int,Wire>,a: Action<Wire>) -> State<Image<M>> {
    match a {
        Action::Deliver(id) if n.pending.contains_key(id) && n.pending[id].path==Path::Weak
            && n.pending[id].to is At && n.pending[id].input is Copy=>{
            let pkt=n.pending[id]; let cells=|r:Replica|if pkt.to==at(r){pkt.input->Copy_0}else{(s.base.cells)(r)};
            State {base:Image {cells,..s.base},..s}
        }, _=>s,
    }
}
pub proof fn all_ordinary_continuations<M,E>(p: Engine<Image<M>,E>,b: Fork,other:M,t: Seq<State<Image<M>>>,
    ev: Seq<Event<E>>,n: Seq<Network<int,Wire>>,a: Seq<Action<Wire>>,k:nat)
    requires physical(p), t[0]==at_checkpoint(b,other),n[0]==checkpoint_end(b),delivery::trace(|v,w|cell(v,w),n,a),
        k<=a.len(), t.len()==a.len()+1, ev.len()==a.len(),
        forall|i:int| 0<=i<a.len() ==> {
            let ordinary=#[trigger] ev[i];
            !(ordinary is Invoke) && enabled(p,t[i],ordinary) && !(p.up)(t[i].base).contains(Replica::R3)
                && crate::validator_block::application_copy(n[i],a[i])
                && t[i+1]==receive_copy(install(p,t[i],ordinary),n[i],a[i])
        },
    ensures invalid_cut(t[k as int]), t[k as int].calls[2].answer.is_none() && !t[k as int].calls[2].submitted,
    decreases k,
{
    if k==0 {
        crate::validator_block::at_the_real_cut(b);
        assert forall|r:Replica| weak_value((#[trigger] (t[0].base.cells)(r))) by {match r {_=>{}}}
    } else {
        let h=(k-1) as nat;all_ordinary_continuations(p,b,other,t,ev,n,a,h);
        let s=t[h as int];let ordinary=ev[h as int];let u=install(p,s,ordinary);
        ordinary_work_including_repairs(p,s,ordinary);
        assert forall|r:Replica| weak_value((#[trigger] (t[k as int].base.cells)(r))) by {assert(weak_value((u.base.cells)(r)));}
    }
}

}
