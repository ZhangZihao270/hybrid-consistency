// Compare the actual observations that survive two independently returning
// preparations. The C1 mailboxes and the replica work needed to fill them
// may have different traces.
use vstd::prelude::*;
use crate::{Op,checkpoint::*,delivery::*,protocol::survivor_actor};
use crate::coupled_construction as build;
use crate::coupled_reads as calls;
use crate::coupled_traffic::{self as traffic,Encoding};
use crate::first_assembly::{self as asm,Lanes,Service};
use crate::fork_alternatives::{self as fork,Tapes};
use crate::fork_information as info;
use crate::guarded_comparison::{self as cmp,prepare,end,fired};
use crate::independent_read::{self as read,State};
use crate::promotion_wait as wait;
use crate::read_call::{Program,Event};

verus! {

// Only the shared prefix is fixed. The remainder of each fully admitted
// tape executes with its own mandatory inputs. Compare the usable physical
// record before and after those native tails, independently of any result.
pub open spec fn prefix_of<S>(m:Program<S>,l:Lanes,b:Fork,t:Tapes,s:Seq<Event>) -> bool {
    let u=fired(m,prepare(),build::root(m,l,b),s);
    u.len()<=t.replicas.len() && t.replicas.take(u.len() as int)==u
}
pub open spec fn retains_prefix<S>(m:Program<S>,l:Lanes,b:Fork,t:Tapes,s:Seq<Event>) -> bool {
    prefix_of(m,l,b,t,s) && info::retained(end(m,prepare(),build::root(m,l,b),s))==info::live_view(fork::cut(m,l,b,t))
}

pub open spec fn remaining_proposals<S>(m:Program<S>,l:Lanes,b:Fork,t:Tapes,s:Seq<Event>) -> Seq<Event> {
    let k=fired(m,prepare(),build::root(m,l,b),s).len();
    asm::actions(t.replicas.skip(k as int))
}
pub open spec fn stable_on<S>(m:Program<S>,l:Lanes,b:Fork,s:Seq<Event>,tail:Seq<Event>) -> bool {
    let x=build::root(m,l,b);
    info::retained(end(m,prepare(),x,s+tail))==info::retained(end(m,prepare(),x,s))
}

// Native endpoint agreement alone could be caused by the choice of tail.
// Test both crossed preparations on the real guards and queues too. A
// crossed preparation is never assumed to complete C1 or to issue C2.
pub open spec fn matched_tails<S>(m:Program<S>,l:Lanes,n:Notice,a:Tapes,b:Tapes,s:Seq<Event>) -> bool {
    let left=alpha(n);let right=beta(n);
    retains_prefix(m,l,left,a,s) && retains_prefix(m,l,right,b,s)
        && stable_on(m,l,right,s,remaining_proposals(m,l,left,a,s))
        && stable_on(m,l,left,s,remaining_proposals(m,l,right,b,s))
}

proof fn native_tail<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,t:Tapes,s:Seq<Event>)
    requires fork::admitted(m,first,res,l,b,t),prefix_of(m,l,b,t,s),
    ensures ({
        let z=build::root(m,l,b);let tail=remaining_proposals(m,l,b,t,s);
        fired(m,prepare(),z,s+tail)==t.replicas
            && info::retained(end(m,prepare(),z,s+tail))==info::live_view(fork::cut(m,l,b,t))
    }),
{
    let z=build::root(m,l,b);let g=prepare();let u=fired(m,g,z,s);let v=t.replicas.skip(u.len() as int);
    let y=end(m,g,z,s);let tail=asm::actions(v);
    assert(u+v =~= t.replicas);crate::first_splice::concat(m,z,u,v);
    assert forall|i:int| 0<=i<v.len() implies crate::independent_preparations::ordinary_input(#[trigger] v[i])
        by {assert(v[i]==t.replicas[u.len()+i]);}
    crate::mailbox_preparation::propose_native(m,y,v);cmp::append_script(m,g,z,s,tail);
    info::private_first_return_cannot_signal(m,first,res,l,b,t.replicas,t.caller);
}

pub open spec fn fixed_tail_use<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,a:Tapes,b:Tapes,
    script:Seq<Event>,post:Seq<Event>) -> bool {
    let x=fork::cut(m,l,alpha(n),a);let y=fork::cut(m,l,beta(n),b);let c=info::caller2(x);
    let ax=info::installed(m,alpha(n));let by=info::installed(m,beta(n));
    info::channel(m,l,n,script,ax)==info::live_view(x) && info::channel(m,l,n,script,by)==info::live_view(y)
        && fork::probe(quiet,m,res,l,n,c,script,post,ax)==fork::outcome(quiet,m,res,x,post)
        && fork::probe(quiet,m,res,l,n,c,script,post,by)==fork::outcome(quiet,m,res,y,post)
}

// The export and distinguishing C2 delivery belong to the measured runs.
// The R3 event is in their common proposal prefix. The completed native
// preparations need not be realizable by a single proposal list.
pub open spec fn prefix_use<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,l:Lanes,n:Notice,a:Tapes,b:Tapes,
    pre:Seq<Event>,post:Seq<Event>) -> bool {
    matched_tails(m,l,n,a,b,pre)
        && fixed_tail_use(quiet,m,res,l,n,a,b,pre+remaining_proposals(m,l,alpha(n),a,pre),post)
        && fixed_tail_use(quiet,m,res,l,n,a,b,pre+remaining_proposals(m,l,beta(n),b,pre),post)
        && fork::retained_use(quiet,m,res,l,n,a,b,pre,post)
}

pub proof fn independent_tails_use_r3<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,pre:Seq<Event>,post:Seq<Event>)
    requires fork::candidate(m,first,res,l,n,a,b),matched_tails(m,l,n,a,b,pre),
        cmp::second_return(quiet,m,res,alpha(n),fork::cut(m,l,alpha(n),a),post),
        cmp::second_return(quiet,m,res,beta(n),fork::cut(m,l,beta(n),b),post),
        calls::legal_returns(5,fork::outcome(quiet,m,res,fork::cut(m,l,alpha(n),a),post).unwrap()),
        calls::legal_returns(2,fork::outcome(quiet,m,res,fork::cut(m,l,beta(n),b),post).unwrap()),
    ensures prefix_use(quiet,m,res,l,n,a,b,pre,post),
{
    hide(info::used_receipt);hide(info::exported);hide(info::channel);hide(fork::selects);
    let left=alpha(n);let right=beta(n);let x=fork::cut(m,l,left,a);let y=fork::cut(m,l,right,b);
    let va=fork::outcome(quiet,m,res,x,post);let vb=fork::outcome(quiet,m,res,y,post);
    fork::history_completion(left,va);fork::history_completion(right,vb);
    if info::live_view(x)==info::live_view(y) {info::same_residual_replays_sr2(quiet,m,res,x,y,post);}
    info::channel_at_prefix(m,l,left,pre);info::channel_at_prefix(m,l,right,pre);
    native_tail(m,first,res,l,left,a,pre);native_tail(m,first,res,l,right,b,pre);
    let sa=pre+remaining_proposals(m,l,left,a,pre);let sb=pre+remaining_proposals(m,l,right,b,pre);
    info::channel_at_prefix(m,l,left,sa);info::channel_at_prefix(m,l,right,sa);
    info::channel_at_prefix(m,l,left,sb);info::channel_at_prefix(m,l,right,sb);
    let j=info::retained_difference_leaves_r3(m,l,n,pre);assert(fork::export_at(m,l,n,pre,j));
    info::distinguishing_delivery(quiet,m,res,n,x,y,post);
    fork::real_selection(quiet,m,res,x,post);fork::real_selection(quiet,m,res,y,post);
    crate::order_extension::canonical_orders_exist(left);crate::order_extension::canonical_orders_exist(right);
    crate::order_extension::extension_iff_writer(left,crate::order_extension::at_first(left),Op::W1);
    crate::order_extension::extension_iff_writer(right,crate::order_extension::at_first(right),Op::W2);
    assert(fork::gain(left,va,vb) && fork::gain(right,vb,va));
}

pub proof fn full_preparation_retains_prefix<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,l:Lanes,b:Fork,t:Tapes,s:Seq<Event>)
    requires fork::admitted(m,first,res,l,b,t),fired(m,prepare(),build::root(m,l,b),s)==t.replicas,
    ensures retains_prefix(m,l,b,t,s),
{
    assert(t.replicas.take(t.replicas.len() as int) =~= t.replicas);
    info::private_first_return_cannot_signal(m,first,res,l,b,t.replicas,t.caller);
}

pub proof fn aligned_has_matched_tails<S>(m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,s:Seq<Event>)
    requires fork::candidate(m,first,res,l,n,a,b),fork::aligned(m,l,n,a,b,s),
    ensures matched_tails(m,l,n,a,b,s),
{
    let left=alpha(n);let right=beta(n);
    full_preparation_retains_prefix(m,first,res,l,left,a,s);full_preparation_retains_prefix(m,first,res,l,right,b,s);
    assert(remaining_proposals(m,l,left,a,s) =~= Seq::empty() && remaining_proposals(m,l,right,b,s) =~= Seq::empty());
    assert(s+Seq::<Event>::empty() =~= s);
}

// Neutral encodings need only agree on receipts actually taken. Locate
// the first guard or update that distinguishes a changed R3 header.
pub open spec fn matched_prefix<S>(m:Program<S>,n:Notice,f:Encoding,x:State<S>,y:State<S>,s:Seq<Event>) -> bool
    decreases s.len(),
{
    calls::issued_pair(x,y,n,f) && (s.len()==0 || {
        let a=s[0];let u=read::next(m,x,a);let v=read::next(m,y,a);
        read::service_step(m)(x,a,u) && read::service_step(m)(y,a,v)
            && process_step(y.cfg.net,a)==traffic::observation(f,process_step(x.cfg.net,a),2)
            && matched_prefix(m,n,f,u,v,s.drop_first())
    })
}

pub open spec fn distinguished_header<S>(m:Program<S>,f:Encoding,x:State<S>,y:State<S>,a:Event) -> bool {
    let e=process_step(x.cfg.net,a);let h=process_step(y.cfg.net,a);let v=(x.cfg.private)(e.actor);
    a is Deliver && enabled(y.cfg.net,a) && e.incoming.is_some() && h.incoming.is_some()
        && e.incoming.unwrap().from==at(crate::Replica::R3) && e.incoming.unwrap().path!=Path::Weak
        && h.incoming.unwrap()==traffic::image(f,e.incoming.unwrap()) && e.incoming!=h.incoming
        && e.actor==h.actor && v==(y.cfg.private)(h.actor) && (m.accept)(v,e)
        && (!(m.accept)(v,h) || (m.update)(v,e)!=(m.update)(v,h))
}

pub open spec fn header_at<S>(m:Program<S>,n:Notice,f:Encoding,x:State<S>,y:State<S>,s:Seq<Event>,i:int) -> bool {
    let u=s.take(i);let v=asm::drive(m,x,u);let w=asm::drive(m,y,u);
    0<=i<s.len() && matched_prefix(m,n,f,x,y,u) && calls::issued_pair(v,w,n,f) && distinguished_header(m,f,v,w,s[i])
}

proof fn distinguish_at_cut<S>(m:Program<S>,n:Notice,f:Encoding,x:State<S>,y:State<S>,a:Event,u:State<S>)
    requires calls::issued_pair(x,y,n,f),read::service_step(m)(x,a,u),!calls::evidence(alpha(n))(x,a,u),
        !calls::compatible_receipt(m,f,x,a),
    ensures distinguished_header(m,f,x,y,a),
{
    let i=a->Deliver_0;let e=process_step(x.cfg.net,a);let h=process_step(y.cfg.net,a);
    assert(i>2 && calls::live_slot(x,y,i,f));assert(!calls::for_stopped(x.cfg.net.pending.get(i)));
    assert(h==traffic::observation(f,e,0));assert(survivor_actor(e.actor));
    assert((x.cfg.private)(e.actor)==(y.cfg.private)(h.actor));
    assert(e.incoming.unwrap()!=h.incoming.unwrap());
}

proof fn replay_or_sensitive_header<S>(m:Program<S>,res:spec_fn(S)->Option<int>,n:Notice,f:Encoding,p:Service<S>,j:nat,y:State<S>)
    requires p.states.len()==p.actions.len()+1,wait::valid_edges(read::service_step(m),p),!wait::uses(p,calls::evidence(alpha(n))),
        wait::pending_before(read::returned(res),p),read::returned(res)(p.states.last()),j<=p.actions.len(),
        calls::issued_pair(p.states[j as int],y,n,f),calls::distinct_weak_names(m),
    ensures ({
        let x=p.states[j as int];let s=p.actions.skip(j as int);
        calls::suffix(m,res,n,f,x,y,s) || exists|i:int| #[trigger] header_at(m,n,f,x,y,s,i)
    }),
    decreases p.actions.len()-j,
{
    let x=p.states[j as int];let s=p.actions.skip(j as int);
    if j==p.actions.len() {
        assert(s =~= Seq::<Event>::empty());
        let v=res(info::caller2(x)).unwrap();
        if calls::legal_returns(5,v) && calls::legal_returns(2,v) {
            let (a,b)=choose|a:Seq<Op>,b:Seq<int>| #[trigger] crate::legal(a,b,5,v);
            let (c,d)=choose|c:Seq<Op>,d:Seq<int>| #[trigger] crate::legal(c,d,2,v);
            crate::conditional_history_contradiction(a,b,c,d,v);
        }
    } else {
        let a=s[0];let u=p.states[j as int+1];let v=read::next(m,y,a);
        assert(s[0]==p.actions[j as int] && s.drop_first() =~= p.actions.skip(j as int+1));
        assert(read::service_step(m)(x,a,u) && !calls::evidence(alpha(n))(x,a,u));
        if !calls::compatible_receipt(m,f,x,a) {
            distinguish_at_cut(m,n,f,x,y,a,u);assert(s.take(0) =~= Seq::empty());
            assert(header_at(m,n,f,x,y,s,0));
        } else {
            calls::replay_compatible_step(m,n,f,x,y,a,u);
            replay_or_sensitive_header(m,res,n,f,p,j+1,v);
            if !calls::suffix(m,res,n,f,u,v,s.drop_first()) {
                let k=choose|k:int| #[trigger] header_at(m,n,f,u,v,s.drop_first(),k);
                assert(s.take(k+1)[0]==a && s.take(k+1).drop_first() =~= s.drop_first().take(k) && s[k+1]==s.drop_first()[k]);
                assert(header_at(m,n,f,x,y,s,k+1));
            }
        }
    }
}

// Run the matched service with the original weak deferrals. Only the
// accepted alpha actions are proposed to beta during this replay.
proof fn execute_matched<S>(quiet:bool,m:Program<S>,res:spec_fn(S)->Option<int>,f:Encoding,
    x:State<S>,y:State<S>,t:crate::first_splice::Tape)
    requires cmp::admissible_tape(m,cmp::second(quiet,res),x,t),crate::fork_delivery::service_prefix(m,y,asm::actions(t)),
        calls::matching_steps(m,res,f,x,y,asm::actions(t)),
    ensures ({
        let s=asm::actions(t);let g=cmp::second(quiet,res);
        end(m,g,x,s)==asm::drive(m,x,s) && end(m,g,y,s)==asm::drive(m,y,s)
    }),
    decreases t.len(),
{
    let s=asm::actions(t);let g=cmp::second(quiet,res);
    if t.len()>0 {
        let a=t[0].action;let u=read::next(m,x,a);let v=read::next(m,y,a);
        assert(s[0]==a && s.drop_first() =~= asm::actions(t.drop_first()));
        let e=process_step(x.cfg.net,a);let h=process_step(y.cfg.net,a);
        assert(h==traffic::observation(f,e,2));assert(cmp::weak_work(h)==cmp::weak_work(e));
        assert(cmp::ready(m,g,x,a) && cmp::ready(m,g,y,a));
        cmp::scan_step(m,g,x,s);cmp::scan_step(m,g,y,s);execute_matched(quiet,m,res,f,u,v,t.drop_first());
    }
}

// No constraint on the relative orders of the two admitted SR1 arms and
// no global recipient-use hypothesis. The target gets its own bytes.
pub proof fn independent_arms_encoding_test<S>(quiet:bool,m:Program<S>,first:spec_fn(S)->int,res:spec_fn(S)->Option<int>,
    l:Lanes,n:Notice,a:Tapes,b:Tapes,post:Seq<Event>,f:Encoding)
    requires fork::candidate(m,first,res,l,n,a,b),calls::distinct_weak_names(m),
        cmp::second_return(quiet,m,res,alpha(n),fork::cut(m,l,alpha(n),a),post),
        calls::issued_pair(fork::cut(m,l,alpha(n),a),fork::cut(m,l,beta(n),b),n,f),
    ensures ({
        let x=fork::cut(m,l,alpha(n),a);let y=fork::cut(m,l,beta(n),b);
        let s=asm::actions(fired(m,cmp::second(quiet,res),x,post));
        (calls::suffix(m,res,n,f,x,y,s) && cmp::second_return(quiet,m,res,alpha(n),x,s)
            && cmp::second_return(quiet,m,res,beta(n),y,s) && fork::outcome(quiet,m,res,x,s)==fork::outcome(quiet,m,res,y,s)
            && (!calls::legal_returns(5,fork::outcome(quiet,m,res,x,s).unwrap()) || !calls::legal_returns(2,fork::outcome(quiet,m,res,y,s).unwrap())))
            || exists|i:int| #[trigger] header_at(m,n,f,x,y,s,i)
    }),
{
    let x=fork::cut(m,l,alpha(n),a);let y=fork::cut(m,l,beta(n),b);let p=cmp::path(m,x,fired(m,cmp::second(quiet,res),x,post));
    assert(!wait::uses(p,calls::evidence(alpha(n)))) by {
        assert forall|k:int| 0<=k<p.actions.len() implies !calls::evidence(alpha(n))(p.states[k],#[trigger] p.actions[k],p.states[k+1])
            by {assert(!cmp::postponed(alpha(n),quiet)(p.states[k],p.actions[k],p.states[k+1]));}
    }
    replay_or_sensitive_header(m,res,n,f,p,0,y);assert(p.actions.skip(0) =~= p.actions);
    let g=cmp::second(quiet,res);let t=fired(m,g,x,post);let s=asm::actions(t);
    if calls::suffix(m,res,n,f,x,y,s) {
        cmp::firing_is_native(m,g,x,post);execute_matched(quiet,m,res,f,x,y,t);
        cmp::returned_run(quiet,m,res,alpha(n),x,s);cmp::returned_run(quiet,m,res,beta(n),y,s);
    }
}

}
