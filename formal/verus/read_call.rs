use vstd::prelude::*;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;

verus! {

pub type Program<S> = LocalProtocol<S,int,Wire>;
pub type Net = Network<int,Wire>;
pub type Event = Action<Wire>;

}
