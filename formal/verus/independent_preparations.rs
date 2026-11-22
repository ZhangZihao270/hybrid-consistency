use vstd::prelude::*;
use crate::{Replica, checkpoint::*, delivery::*};
use crate::first_assembly::{self as asm, Lanes};
use crate::independent_read::State;
use crate::read_call::{Event, Program};

verus! {

pub open spec fn offers() -> Seq<Event> {
    seq![send(0,Path::Weak,at(Replica::R1),at(Replica::R3),Wire::Copy(2)),
         send(1,Path::Weak,at(Replica::R2),at(Replica::R3),Wire::Copy(5))]
}
pub open spec fn before_offers<S>(m:Program<S>,l:Lanes) -> State<S> {
    let x=asm::entry(m,l);State{cfg:crate::ordinary_service::Configuration{net:local_rmw_cells(),..x.cfg},..x}
}
pub open spec fn after_offers<S>(m:Program<S>,l:Lanes) -> Program<S> {
    crate::protocol::LocalProtocol{initial:asm::drive(m,before_offers(m,l),offers()).cfg.private,..m}
}
}
