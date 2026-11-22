use vstd::prelude::*;
use crate::{Op,Replica};
use crate::facade_linear::CommandSemantics;
use crate::facade_hybrid::weak_rmw;
use crate::ordered_round::{self as engine,Store};
use crate::stock_facade::{State,initial};

verus! {

// An alternative local recovery service with actual retained RMW records.
// The journal is per site. Keeping a record says nothing about its total-
// order position or its inclusion in another site's strong history.
pub struct Record { pub op:Op,pub returned:int,pub installed:int }
pub type Journals = spec_fn(Replica)->Seq<Record>;
pub struct Storage { pub core:State<Store>,pub records:Journals }

pub open spec fn save_call(s:Storage,site:Replica,w:Op) -> Storage {
    let (post,old)=weak_rmw(s.core,site,w);
    let record=Record {op:w,returned:old,installed:(post.base.disk)(site).value};
    Storage {core:post,records:|r|if r==site {(s.records)(r).push(record)} else {(s.records)(r)}}
}
pub open spec fn origin_records(f:CommandSemantics) -> Storage {
    let start=Storage {core:initial(engine::engine(f)),records:|_site|Seq::empty()};
    save_call(save_call(start,Replica::R1,Op::W1),Replica::R2,Op::W2)
}
}
