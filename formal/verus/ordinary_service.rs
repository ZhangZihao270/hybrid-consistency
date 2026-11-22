use vstd::prelude::*;
use crate::checkpoint::*;
use crate::delivery::*;
use crate::protocol::*;

verus! {

pub struct Configuration<S> {
    pub net: Network<int,Wire>,
    pub private: spec_fn(Process)->S,
}
pub open spec fn allowed<S>(m: LocalProtocol<S,int,Wire>,s: Configuration<S>,a: Action<Wire>) -> bool {
    let ev=process_step(s.net,a);
    enabled(s.net,a) && (m.accept)((s.private)(ev.actor),ev)
}
pub open spec fn apply<S>(m: LocalProtocol<S,int,Wire>,s: Configuration<S>,a: Action<Wire>) -> Configuration<S> {
    let ev=process_step(s.net,a);
    Configuration {net:advance(|x,w|cell(x,w),s.net,a),
        private:|p| if p==ev.actor {(m.update)((s.private)(p),ev)} else {(s.private)(p)} }
}
pub open spec fn pending<S>(s: Configuration<S>,result: spec_fn(S)->Option<int>) -> bool {
    result((s.private)(Process::SecondClient)).is_none()
}

}
