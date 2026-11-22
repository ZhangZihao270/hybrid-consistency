// Erasing passive instrumentation is justified by guards and updates. The
// record may be arbitrarily large and depend on every payload and sender.
use vstd::prelude::*;
use crate::promotion_wait::Relation;
use crate::read_nonblocking as nb;

verus! {

pub type Record<S,A,M> = spec_fn(S,A,S,M)->M;
pub open spec fn instrument<S,A,M>(step:Relation<S,A>,record:Record<S,A,M>) -> Relation<(S,M),A> {
    |x:(S,M),a,y:(S,M)| step(x.0,a,y.0) && y.1==record(x.0,a,y.0,x.1)
}
pub open spec fn observe<S,M>(p:nb::Region<S>) -> nb::Region<(S,M)> { |x:(S,M)| p(x.0) }
pub open spec fn effect<S,A,M>(p:Relation<S,A>) -> Relation<(S,M),A> { |x:(S,M),a,y:(S,M)| p(x.0,a,y.0) }

proof fn same_layer<S,A,M>(step:Relation<S,A>,posted:nb::Region<S>,promotion:Relation<S,A>,record:Record<S,A,M>,
    x:S,m:M,k:nat)
    ensures nb::within(nb::ordinary(step,promotion),posted,x,k) ==
        nb::within(nb::ordinary(instrument(step,record),effect(promotion)),observe(posted),(x,m),k),
    decreases k,
{
    let base=nb::ordinary(step,promotion);let extra=nb::ordinary(instrument(step,record),effect(promotion));
    let seen=observe(posted);let start=(x,m);
    if !posted(x) && k>0 {
        if nb::within(base,posted,x,k) {
            let (a,y)=choose|a:A,y:S| #[trigger] base(x,a,y) && nb::within(base,posted,y,(k-1) as nat);
            let next=record(x,a,y,m);same_layer(step,posted,promotion,record,y,next,(k-1) as nat);
            assert(extra(start,a,(y,next)));
        } else if nb::within(extra,seen,start,k) {
            let (a,y)=choose|a:A,y:(S,M)| #[trigger] extra(start,a,y) && nb::within(extra,seen,y,(k-1) as nat);
            same_layer(step,posted,promotion,record,y.0,y.1,(k-1) as nat);assert(base(x,a,y.0));
        }
    }
}
pub proof fn same_capacity<S,A,M>(step:Relation<S,A>,posted:nb::Region<S>,promotion:Relation<S,A>,record:Record<S,A,M>,x:S,m:M)
    ensures nb::possible(nb::ordinary(step,promotion),posted,x) ==
        nb::possible(nb::ordinary(instrument(step,record),effect(promotion)),observe(posted),(x,m)),
{
    let b=nb::ordinary(step,promotion);let r=nb::ordinary(instrument(step,record),effect(promotion));let d=observe(posted);
    if nb::possible(b,posted,x) {same_layer(step,posted,promotion,record,x,m,choose|k:nat| #[trigger] nb::within(b,posted,x,k));}
    else if nb::possible(r,d,(x,m)) {same_layer(step,posted,promotion,record,x,m,choose|k:nat| #[trigger] nb::within(r,d,(x,m),k));}
}
pub proof fn logging_preserves_waits<S,A,M>(step:Relation<S,A>,posted:nb::Region<S>,promotion:Relation<S,A>,record:Record<S,A,M>,
    x:(S,M),a:A,y:(S,M))
    requires instrument(step,record)(x,a,y),
    ensures nb::unlocks(instrument(step,record),observe(posted),effect(promotion),x,a,y)
        ==nb::unlocks(step,posted,promotion,x.0,a,y.0),
{
    same_capacity(step,posted,promotion,record,x.0,x.1);same_capacity(step,posted,promotion,record,y.0,y.1);
}

}
