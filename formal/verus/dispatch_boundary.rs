use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::delivery::{self,Action,Process};
use crate::facade_linear::CommandSemantics;
use crate::facade_hybrid as hybrid;
use crate::facade_progress::{front_fair,project};
use crate::fallback_program as front;
use crate::first_copy_wait::Cut;
use crate::metadata_stock::Rows;
use crate::mixed_service_transfer::reference_sample;
use crate::ordered_round::{self as base,engine,Store,Work};
use crate::quorum_rpc::Resolver;
use crate::read_dispatch as jobs;
use crate::promotion_wait as wait;
use crate::stock_facade::*;
use crate::validator_block as validator;

verus! {

// This is the client's actual one-shot RPC state. Test its own received
// replies and admission code; nobody reads a registry of possible futures.
pub open spec fn sealed(c:Call,rho:Resolver,g:jobs::Admission) -> bool {
    c.method==Method::Read && !c.submitted && c.answer.is_none() &&
        (c.legs)(Replica::R1) is Received && (c.legs)(Replica::R2) is Received && (c.legs)(Replica::R3)==Leg::Unsent &&
        early(c) && rho(rows(c)).is_none() && !jobs::dispatch(c,rho,g)
}

// Includes competing application requests, ordinary repairs, and changes
// to queues, clocks, working values or weak order outside the client call.
// After its own enabled handler, no other actor edits this private call.
pub open spec fn step<X,E>(p:Engine<X,E>,rho:Resolver,g:jobs::Admission,id:nat) -> wait::Relation<State<X>,Event<E>> {
    |s:State<X>,a,u:State<X>| jobs::permitted(p,s,a,rho,g) &&
        u.calls.get(id)==jobs::advance(p,s,a,rho,g).calls.get(id)
}
proof fn stays_sealed<X,E>(p:Engine<X,E>,rho:Resolver,g:jobs::Admission,id:nat,s:State<X>,a:Event<E>,u:State<X>)
    requires s.calls.contains_key(id),sealed(s.calls[id],rho,g),step(p,rho,g,id)(s,a,u),
    ensures u.calls.get(id)==s.calls.get(id),
{
    let c=s.calls[id];assert(crate::ordered_store::majority(rows(c).dom()));
    if let Event::Rpc(i,r,st)=a {if i==id {match r {Replica::R1=>{},Replica::R2=>{},Replica::R3=>{}}}}
}
proof fn sealed_at<X,E>(p:Engine<X,E>,rho:Resolver,g:jobs::Admission,id:nat,path:wait::Path<State<X>,Event<E>>,k:nat)
    requires wait::valid_edges(step(p,rho,g,id),path),path.states.len()==path.actions.len()+1,k<=path.actions.len(),
        path.states[0].calls.contains_key(id),sealed(path.states[0].calls[id],rho,g),
    ensures path.states[k as int].calls.get(id)==path.states[0].calls.get(id),
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat;sealed_at(p,rho,g,id,path,i);
        assert(step(p,rho,g,id)(path.states[i as int],path.actions[i as int],path.states[k as int]));
        stays_sealed(p,rho,g,id,path.states[i as int],path.actions[i as int],path.states[k as int]);
    }
}
pub open spec fn done<X>(id:nat) -> spec_fn(State<X>)->bool {
    |s:State<X>|s.calls.contains_key(id) && s.calls[id].answer.is_some()
}
pub proof fn sealed_has_no_service<X,E>(p:Engine<X,E>,rho:Resolver,g:jobs::Admission,s:State<X>,id:nat)
    requires s.calls.contains_key(id),sealed(s.calls[id],rho,g),
    ensures !wait::can_finish(step(p,rho,g,id),done(id),s),
        forall|effect:wait::Relation<State<X>,Event<E>>| !#[trigger] wait::needs_class(step(p,rho,g,id),done(id),s,effect),
{
    let edge=step(p,rho,g,id);
    if wait::can_finish(edge,done(id),s) {
        let path=choose|w:wait::Path<State<X>,Event<E>>| #[trigger] wait::first_return(edge,done(id),s,w);
        sealed_at(p,rho,g,id,path,path.actions.len());
    }
}

// Exact opportunity after collecting this majority, for every deterministic
// direct resolver and every ordinary admission policy in this interface.
// An Execute here uses only the immutable replies held at C2.
pub proof fn exact_after_intake(f:CommandSemantics,b:Fork,rho:Resolver,g:jobs::Admission)
    requires crate::sender_forks::firsts(rho,b.notice),
    ensures ({
        let h=jobs::collected(b,rho);let p=engine(f);let m=rows(h.core.calls[2]);
        jobs::original_prefix(f,b,rho,g) && jobs::physical_intake(f,b,rho,g) && jobs::suffix(f,b,rho,g) &&
            wait::can_finish(step(p,rho,g,2),done(2),h.core)==(rho(m).is_some() || g(m)) &&
            ((rho(m).is_some() || g(m)) ==> done::<Store>(2)(jobs::service_states(f,b,rho,g).last()))
    }),
{
    hide(jobs::original_prefix);hide(jobs::physical_intake);hide(jobs::suffix);
    jobs::two_real_reads(f,b.notice,rho,g);
    match b.branch {crate::Branch::Alpha=>{assert(b==alpha(b.notice));},crate::Branch::Beta=>{assert(b==beta(b.notice));}}
    let h=jobs::collected(b,rho);let s=h.core;let m=rows(s.calls[2]);let p=engine(f);let edge=step(p,rho,g,2);
    assert(m==crate::metadata_stock::unadvanced_rows()) by {reveal(jobs::physical_intake);}
    if rho(m).is_some() || g(m) {
        let w=wait::Path{states:jobs::service_states(f,b,rho,g),actions:jobs::completion_events(rho,g)};
        assert(jobs::path(p,rho,g,w.states,w.actions)) by {reveal(jobs::suffix);}
        assert forall|i:int| 0<=i<w.actions.len() implies edge(w.states[i],#[trigger] w.actions[i],w.states[i+1]) by {};
        assert forall|i:int| 0<=i<w.actions.len() implies !done(2)(#[trigger] w.states[i]) by {prefix_index(i);}
        assert(wait::first_return(edge,done(2),s,w));
    } else {
        assert(sealed(s.calls[2],rho,g));sealed_has_no_service(p,rho,g,s,2);
    }
}

pub open spec fn off() -> jobs::Admission { |_m:Rows|false }
pub open spec fn on() -> jobs::Admission { |_m:Rows|true }

// Before replies are sealed, a real install may still affect their value.
// Here all future weak writes in the fixed workload carry 2 or 5. Include
// every enabled ordinary work event, even ordinary jobs unrelated to C2.
proof fn same_at_block(f:CommandSemantics,s:State<Store>,ev:Event<Work>)
    requires validator::blocked(s),!(ev is Invoke),enabled(engine(f),s,ev),
    ensures jobs::advance(engine(f),s,ev,reference_sample(),off())==crate::stock_facade::step(engine(f),s,ev),
{
    if let Event::Poll(id)=ev {
        assert(id==2);let c=s.calls[id];validator::invalid_mailbox(c);
        if front::direct(c) {
            let m=rows(c);
            assert(validator::possible_leg(Replica::R3,(c.legs)(Replica::R3)));
            assert(!m.contains_key(Replica::R3));assert(m.contains_key(Replica::R1));
            assert(validator::possible_leg(Replica::R1,(c.legs)(Replica::R1)));
            assert(!crate::metadata_reader::valid_root(m));
            assert(jobs::advance(engine(f),s,ev,reference_sample(),off()).calls =~= crate::stock_facade::step(engine(f),s,ev).calls);
        }
    }
}
pub open spec fn continuation(f:CommandSemantics,t:Seq<State<Store>>,e:Seq<Event<Work>>,
    ns:Seq<RpcNet>,a:Seq<Action<Wire>>) -> bool {
    t.len()==a.len()+1 && e.len()==a.len() && delivery::trace(|v,w|cell(v,w),ns,a) &&
        forall|i:int| 0<=i<a.len() ==> {
            let ev=#[trigger] e[i];!(ev is Invoke) && jobs::permitted(engine(f),t[i],ev,reference_sample(),off()) &&
                validator::application_copy(ns[i],a[i]) && t[i+1]==hybrid::weak_part(jobs::advance(engine(f),t[i],ev,reference_sample(),off()),ns[i],a[i])
        }
}
pub type RpcNet=delivery::Network<int,Wire>;
pub proof fn no_job_from_original_cut(f:CommandSemantics,b:Fork,t:Seq<State<Store>>,e:Seq<Event<Work>>,
    ns:Seq<RpcNet>,a:Seq<Action<Wire>>,k:nat)
    requires continuation(f,t,e,ns,a),t[0]==hybrid::prefix(b,17),ns[0]==checkpoint_end(b),k<=a.len(),
    ensures validator::blocked(t[k as int]),!t[k as int].calls[2].submitted && t[k as int].calls[2].answer.is_none(),
        forall|id:nat,q:Set<Replica>| !#[trigger] base::ready(t[k as int].base,Input::Work(Work::Serve(id,q))),
    decreases k,
{
    if k==0 {validator::at_the_real_cut(b);} else {
        let i=(k-1) as nat;no_job_from_original_cut(f,b,t,e,ns,a,i);
        let x=t[i as int];let ev=e[i as int];let w=a[i as int];
        assert(!(ev is Invoke) && enabled(engine(f),x,ev));same_at_block(f,x,ev);
        validator::ordinary_step_cannot_unlock(f,x,ev);
        let u=crate::stock_facade::step(engine(f),x,ev);let next=t[k as int];
        assert(next==hybrid::weak_part(u,ns[i as int],w));
        assert forall|r:Replica| validator::weak_value((#[trigger] (next.base.disk)(r)).value) by {
            assert(validator::weak_value((u.base.disk)(r).value));
            if let Action::Deliver(slot)=w {assert(validator::application_copy(ns[i as int],a[i as int]));}
        }
    }
}
}
