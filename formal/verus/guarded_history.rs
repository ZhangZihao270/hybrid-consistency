use vstd::prelude::*;
use crate::weak_round as weak;

verus! {

pub open spec fn weak_end() -> weak::World {
    let f=weak::paper_ops();let one=weak::step(f,weak::start(),weak::Action::Send(0,weak::request(crate::Op::W1)));
    let both=weak::step(f,one,weak::Action::Send(1,weak::request(crate::Op::W2)));
    let left=weak::step(f,both,weak::Action::Handle(0));let right=weak::step(f,left,weak::Action::Handle(1));
    weak::step(f,weak::step(f,right,weak::Action::Receive(0)),weak::Action::Receive(1))
}

}
