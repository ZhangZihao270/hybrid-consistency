use vstd::prelude::*;
use crate::delivery::*;
use crate::checkpoint::*;

verus! {

// Once both queries have gone out, clocks and other private inputs also
// preserve the invocation. Only another client send needs scrutiny here.
pub open spec fn no_client_send(event:Action<Wire>) -> bool {
    match event { Action::Send(_,p) => p.from is At, _ => true }
}

}
