use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{Action,Network};
use crate::facade_linear::CommandSemantics;
use crate::facade_hybrid::{prefix,weak_part};
use crate::metadata_reader::reference_read;
use crate::ordered_round::{engine,Store,Work};
use crate::stock_facade::*;
use crate::read_recovery::{compatible,history_accepts_exactly_observed_value,LocalRebuild,restore};

verus! {

// A storage operation can change the materialized value AND disk metadata.
// These four fields delimit this family of repairs. In particular a real
// generation change or a new backend submission is a different service path.
pub open spec fn image_only(s:State<Store>,u:State<Store>) -> bool {
    s.closed==u.closed && s.calls==u.calls && s.base.calls==u.base.calls && s.base.live==u.base.live
}
pub proof fn concrete_installations(s:LocalRebuild,n:Network<int,Wire>,a:Action<Wire>,r:Replica)
    ensures image_only(s.core,weak_part(s.core,n,a)),
        image_only(s.core,crate::genesis_service::rebuild(s.core,r)),
        image_only(s.core,restore(s,r).core),
{}

pub open spec fn ordinary_slot(r:Replica,l:Leg) -> bool {
    match l {
        Leg::InFlight(row) | Leg::Received(row)=>r!=Replica::R3 && row.version==0,
        Leg::AtServer=>r!=Replica::R3,_=>true,
    }
}
pub open spec fn audit(s:State<Store>) -> bool {
    s.base.live==live_pair() && s.base.calls.is_empty() && s.closed.is_empty()
        && s.calls.dom()==set![1nat,2nat] && s.calls[1].method is Read && s.calls[1].answer.is_some()
        && s.calls[2].method is Read && !s.calls[2].submitted
        && (s.calls[2].answer.is_some() ==> s.calls[2].answer==Some(1))
        && forall|r:Replica| #[trigger] ordinary_slot(r,(s.calls[2].legs)(r))
}
proof fn verify_poll(c:Call)
    requires c.method is Read,!c.submitted,c.answer.is_none() || c.answer==Some(1),
        forall|r:Replica| #[trigger] ordinary_slot(r,(c.legs)(r)),
    ensures !delegate(c), !local_poll(c,None).submitted,
        local_poll(c,None).answer.is_none() || local_poll(c,None).answer==Some(1),
{
    let m=rows(c);
    assert forall|r:Replica| #[trigger] m.contains_key(r) implies r!=Replica::R3 && m[r].version==0 by {
        assert(ordinary_slot(r,(c.legs)(r)));
    }
    if crate::ordered_store::majority(m.dom()) && reference_read(Replica::R3)(m).is_some() {
        crate::quorum_rpc::latest_is_a_sample(m);
        let r=crate::quorum_rpc::latest_site(m);
        assert(m.contains_key(r) && m[r].version==0);
    }
}
pub(crate) proof fn preserved(f:CommandSemantics,s:State<Store>,a:Event<Work>,u:State<Store>)
    requires audit(s),!(a is Invoke),enabled(engine(f),s,a),image_only(step(engine(f),s,a),u),
    ensures audit(u),
{
    let p=engine(f);let v=step(p,s,a);let c=s.calls[2];verify_poll(c);
    if let Event::Poll(id)=a {assert(id==2);}
    if let Event::Work(w)=a {match w {
        Work::Serve(id,_)=>{assert(!s.base.calls.contains_key(id));},
        Work::Crash(r)=>{match r {_=>{}}},_=>{},
    }}
    assert(v.base.disk =~= s.base.disk);assert(v.closed =~= s.closed);assert(v.calls.dom() =~= s.calls.dom());
    assert forall|r:Replica| #[trigger] ordinary_slot(r,(u.calls[2].legs)(r))
        by {assert(ordinary_slot(r,(c.legs)(r)));}
}
// A necessary condition, so it is safe to overapproximate storage work.
// The result gives no implementation authority to invent an image. It
// covers both real cuts and arbitrarily many interventions between polls,
// including weak copies or delivery of every outstanding confirmation.
pub proof fn image_repairs_cannot_serve_h(f:CommandSemantics,b:Fork,t:Seq<State<Store>>,a:Seq<Event<Work>>,k:nat)
    requires t.len()==a.len()+1,t[0]==prefix(b,17),k<=a.len(),
        forall|i:int| 0<=i<a.len() ==> {
            let ev=#[trigger] a[i];!(ev is Invoke) && enabled(engine(f),t[i],ev) && image_only(step(engine(f),t[i],ev),t[i+1])
        },
    ensures audit(t[k as int]), match t[k as int].calls[2].answer {
        Some(v)=>v==1 && !compatible(b,v),None=>true,
    },
    decreases k,
{
    if k==0 {
        crate::validator_block::at_the_real_cut(b);
        assert forall|r:Replica| #[trigger] ordinary_slot(r,(t[0].calls[2].legs)(r)) by {};
    } else {
        let i=(k-1) as nat;image_repairs_cannot_serve_h(f,b,t,a,i);
        preserved(f,t[i as int],a[i as int],t[k as int]);
    }
    history_accepts_exactly_observed_value(b,1);
}
}
