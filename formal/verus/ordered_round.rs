use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::all_replicas;
use crate::ordered_store::{Stamp,majority};
use crate::quorum_rpc::latest_site;
use crate::stock_facade::*;
use crate::facade_linear::CommandSemantics;

verus! {

// A nonempty instance of the backend contract at the atomic ordered-quorum
// interface. Serving a command on Q is one atomic service round here.
// Implementing that primitive by asynchronous consensus is external to this
// instance; the wrapper proof above accepts arbitrary real backend steps.
pub enum Work { Serve(nat,Set<Replica>), Crash(Replica), Tick(Replica), StopClient(nat) }
pub struct Store {
    pub calls: Map<nat,Method>, pub done: Map<nat,int>, pub stopped: Set<nat>, pub live: Set<Replica>,
    pub disk: spec_fn(Replica)->Stamp,
    pub tip: Stamp, // ghost proof of the newest published ordinary state
}
pub open spec fn start() -> Store {
    let root=Stamp{version:0,value:1};
    Store {calls:Map::empty(),done:Map::empty(),stopped:Set::empty(),live:all_replicas(),disk:|_r|root,tip:root}
}
pub open spec fn current(s: Store,q: Set<Replica>) -> Replica { latest_site(Map::new(q,s.disk)) }
pub open spec fn ready(s: Store,a: Input<Work>) -> bool {
    match a {
        Input::Idle=>true, Input::Submit(id,_)=>!s.calls.contains_key(id),
        Input::Work(Work::Tick(r))=>s.live.contains(r),
        Input::Work(Work::StopClient(id))=>!s.stopped.contains(id),
        Input::Work(Work::Crash(r))=>s.live.contains(r) && majority(s.live.remove(r)),
        Input::Work(Work::Serve(id,q))=>s.calls.contains_key(id) && !s.done.contains_key(id) && majority(q) && q.subset_of(s.live),
    }
}
pub open spec fn advance(f: CommandSemantics,s: Store,a: Input<Work>) -> Store {
    match a {
        Input::Submit(id,m)=>Store {calls:s.calls.insert(id,m),..s},
        Input::Work(Work::StopClient(id))=>Store{stopped:s.stopped.insert(id),..s},
        Input::Work(Work::Crash(r))=>Store {live:s.live.remove(r),..s},
        Input::Work(Work::Serve(id,q))=>{
            let d=(s.disk)(current(s,q));
            match s.calls[id] {
                Method::Read=>Store {done:s.done.insert(id,d.value),..s},
                Method::Command(code)=>{
                    let (new,ret)=f(code,d.value); let entry=Stamp{version:d.version+1,value:new};
                    Store {disk:|r|if q.contains(r){entry}else{(s.disk)(r)},tip:entry,done:s.done.insert(id,ret),..s}
                },
            }
        },
        _=>s,
    }
}
pub open spec fn engine(f: CommandSemantics) -> Engine<Store,Work> {
    Engine {initial:start(),ready:|s,a|ready(s,a),step:|s,a|advance(f,s,a),up:|s: Store|s.live,client:|s: Store,id|!s.stopped.contains(id),
        cell:|s: Store,r|(s.disk)(r).value,submitted:|s: Store,id|s.calls.get(id),reply:|s: Store,id|s.done.get(id)}
}

}
