// Operational admission of one read at the R1/R2 checkpoint. The finite
// log monitors the client's request discipline. Handlers still see only
// their own memory and the current local input. The return observer reads C2's memory.
use vstd::prelude::*;
use crate::Replica;
use crate::checkpoint::*;
use crate::confirmation::fresh_send;
use crate::delivery::*;
use crate::finite_service::{at_end,append_delivery,append_observation};
use crate::ordinary_service::{allowed,pending};
use crate::protocol::*;
use crate::promotion_wait::{self as wait, Relation};
use crate::read_nonblocking as nb;
use crate::service::{response_path,can_respond};
use crate::survivors::sr2_result;

verus! {

pub type Program<S> = LocalProtocol<S,int,Wire>;
pub type Net = Network<int,Wire>;
pub type Event = Action<Wire>;
pub struct Log { pub nets:Seq<Net>,pub actions:Seq<Event> }
pub open spec fn launch(net:Net) -> Log { Log{nets:seq![net],actions:seq![]} }
pub open spec fn append(l:Log,a:Event) -> Log {
    Log{nets:l.nets.push(advance(|x,w|cell(x,w),l.nets.last(),a)),actions:l.actions.push(a)}
}
pub open spec fn obs(l:Log) -> Seq<ProcessStep<int,Wire>> { observations(l.nets,l.actions) }
pub open spec fn driver(l:Log) -> bool {
    only_request_sends(l.actions,Process::SecondClient,live_pair()) && fanout_before_receiving(obs(l),Process::SecondClient)
}
pub open spec fn posted<S>(m:Program<S>,res:spec_fn(S)->Option<int>) -> spec_fn(Log)->bool {
    |l:Log| sr2_result(m,res,obs(l)).is_some() && second_invocation(l.nets,l.actions)
}
pub open spec fn step<S>(m:Program<S>,res:spec_fn(S)->Option<int>,reserved:Set<nat>) -> Relation<Log,Event> {
    |l:Log,a,u:Log| {
        let c=at_end(m,l.nets,l.actions);
        pending(c,res) && allowed(m,c,a) && fresh_send(a,reserved) && u==append(l,a) && driver(u)
    }
}
pub open spec fn consistent<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>,l:Log) -> bool {
    l.nets[0]==net && trace(|x,w|cell(x,w),l.nets,l.actions) && accepted(m,obs(l))
      && pending_before_end(m,res,obs(l)) && driver(l)
      && forall|i:int| 0<=i<l.actions.len() ==> fresh_send(#[trigger] l.actions[i],reserved)
}
pub(crate) proof fn step_consistent<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>,l:Log,a:Event,u:Log)
    requires consistent(m,res,net,reserved,l),step(m,res,reserved)(l,a,u),
    ensures consistent(m,res,net,reserved,u),
{
    let act=process_step(l.nets.last(),a);let es=obs(l);
    append_delivery(l.nets,l.actions,a);append_observation(m,res,es,act);
    assert forall|i:int| 0<=i<u.actions.len() implies fresh_send(#[trigger] u.actions[i],reserved) by {
        if i<l.actions.len() {assert(fresh_send(l.actions[i],reserved));}
    }
}
pub proof fn run_prefix<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>,
    path:wait::Path<Log,Event>,k:nat)
    requires path.states.len()==path.actions.len()+1,path.states[0]==launch(net),k<=path.actions.len(),
        wait::valid_edges(step(m,res,reserved),path),
    ensures consistent(m,res,net,reserved,path.states[k as int]),path.states[k as int].actions==path.actions.take(k as int),
    decreases k,
{
    let l=path.states[k as int];
    if k==0 {assert(l.actions =~= path.actions.take(0));}
    else {
        let i=(k-1) as nat;run_prefix(m,res,net,reserved,path,i);
        let x=path.states[i as int];let a=path.actions[i as int];assert(step(m,res,reserved)(x,a,l));
        step_consistent(m,res,net,reserved,x,a,l);
        assert(l.actions =~= path.actions.take(k as int));
    }
}
pub proof fn real_response<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>,path:wait::Path<Log,Event>)
    requires wait::first_return(step(m,res,reserved),posted(m,res),launch(net),path),
    ensures ({
        let l=path.states.last();
        response_path(m,res,net,reserved,l.nets,l.actions,sr2_result(m,res,obs(l)).unwrap()) && l.actions==path.actions
    }),
{
    run_prefix(m,res,net,reserved,path,path.actions.len());let l=path.states.last();
    assert(path.actions.take(path.actions.len() as int) =~= path.actions);
    if l.actions.len()==0 {
        assert(!invocation_only(l.actions,Process::SecondClient,live_pair())) by {
            assert(live_pair().contains(Replica::R1));
            assert(!(exists|i:int| 0<=i<l.actions.len() && client_sends_to(#[trigger] l.actions[i],Process::SecondClient,Replica::R1)));
        }
    }
    assert(res(memory(m,Process::SecondClient,obs(l),0)).is_none());
}

pub open spec fn prefix(s:Seq<Net>,a:Seq<Event>,k:nat) -> Log {
    Log{nets:s.take(k as int+1),actions:a.take(k as int)}
}
pub open spec fn history(s:Seq<Net>,a:Seq<Event>) -> wait::Path<Log,Event> {
    wait::Path{states:Seq::new(a.len()+1,|k:int|prefix(s,a,k as nat)),actions:a}
}
proof fn prefix_events(s:Seq<Net>,a:Seq<Event>,k:nat)
    requires s.len()==a.len()+1,k<=a.len(),
    ensures obs(prefix(s,a,k))==observations(s,a).take(k as int),
{
    assert(obs(prefix(s,a,k)) =~= observations(s,a).take(k as int));
}
proof fn prefix_driver(s:Seq<Net>,a:Seq<Event>,k:nat)
    requires s.len()==a.len()+1,k<=a.len(),second_invocation(s,a),
    ensures driver(prefix(s,a,k)),
{
    let l=prefix(s,a,k);let c=Process::SecondClient;let q=live_pair();let es=observations(s,a);
    prefix_events(s,a,k);
    assert forall|i:int| 0<=i<l.actions.len() implies match #[trigger] l.actions[i] {
        Action::Send(_,p) if p.from==c=>invocation_packet(p) && q.contains(p.to->At_0) &&
            (forall|j:int| 0<=j<i ==> !client_sends_to(#[trigger] l.actions[j],c,p.to->At_0)),_=>true,
    } by {assert(l.actions[i]==a[i]);}
    assert forall|i:int,j:int| 0<=j<i<obs(l).len() implies match (#[trigger] obs(l)[i]).action {
        Action::Send(_,p) if p.from==c=>(#[trigger] obs(l)[j]).actor!=c || obs(l)[j].incoming.is_none(),_=>true,
    } by {assert(obs(l)[i]==es[i] && obs(l)[j]==es[j]);}
}
// Isolate the two prefix arguments from the first-return quantifiers.
proof fn actual_edge<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>,
    s:Seq<Net>,a:Seq<Event>,v:int,i:nat)
    requires response_path(m,res,net,reserved,s,a,v),i<a.len(),
    ensures step(m,res,reserved)(prefix(s,a,i),a[i as int],prefix(s,a,i+1)),
        !posted(m,res)(prefix(s,a,i)),
{
    let c=Process::SecondClient;let es=observations(s,a);
    let l=prefix(s,a,i);let u=prefix(s,a,i+1);let ev=es[i as int];let act=a[i as int];
    prefix_events(s,a,i);prefix_driver(s,a,i+1);
    memory_on_common_prefix(m,c,obs(l),es,i); memory_on_common_prefix(m,ev.actor,obs(l),es,i);
    assert(res(memory(m,c,es,i)).is_none());
    assert((m.accept)(memory(m,ev.actor,es,i),ev));
    assert(enabled(s[i as int],act) && s[i as int+1]==advance(|x,w|cell(x,w),s[i as int],act));
    assert(u.nets =~= append(l,act).nets && u.actions =~= append(l,act).actions);
}
pub proof fn lift_response<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>,
    s:Seq<Net>,a:Seq<Event>,v:int)
    requires response_path(m,res,net,reserved,s,a,v),
    ensures wait::first_return(step(m,res,reserved),posted(m,res),launch(net),history(s,a)),
        history(s,a).states.last()==(Log{nets:s,actions:a}),
{
    hide(step);hide(posted);hide(accepted);hide(pending_before_end);hide(second_invocation);hide(trace);
    let t=history(s,a);let k=a.len();
    assert(s.len()==k+1) by {reveal(trace);}
    assert(t.states[0].nets =~= seq![net]);assert(t.states[0].actions =~= Seq::<Event>::empty());
    assert(t.states.last().nets =~= s);assert(t.states.last().actions =~= a);
    assert forall|i:int| 0<=i<k implies step(m,res,reserved)(t.states[i],#[trigger] a[i],t.states[i+1]) by {
        actual_edge(m,res,net,reserved,s,a,v,i as nat);
    }
    assert forall|i:int| 0<=i<k implies !posted(m,res)(#[trigger] t.states[i]) by {
        actual_edge(m,res,net,reserved,s,a,v,i as nat);
    }
    assert(posted(m,res)(t.states.last())) by {reveal(posted);}
    assert(!posted(m,res)(launch(net))) by { reveal(posted); }
}
pub proof fn exact_service<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>)
    ensures nb::possible(step(m,res,reserved),posted(m,res),launch(net))==can_respond(m,res,net,reserved),
{
    let r=step(m,res,reserved);let d=posted(m,res);let x=launch(net);
    assert(!d(x)) by {assert(live_pair().contains(Replica::R1));}
    nb::first_response_iff(r,d,x);
    if can_respond(m,res,net,reserved) {
        let (s,a,v)=choose|s:Seq<Net>,a:Seq<Event>,v:int| #[trigger] response_path(m,res,net,reserved,s,a,v);
        lift_response(m,res,net,reserved,s,a,v);assert(wait::can_finish(r,d,x));
    } else if nb::possible(r,d,x) {
        let path=choose|p:wait::Path<Log,Event>| #[trigger] wait::first_return(r,d,x,p);
        real_response(m,res,net,reserved,path);let l=path.states.last();
        assert(response_path(m,res,net,reserved,l.nets,l.actions,sr2_result(m,res,obs(l)).unwrap()));
    }
}

// This is a physical receipt in the current queue. Interpreting its arrival
// as evidence of copying is a separate obligation on the issuing protocol.
pub open spec fn receipt(owner:Replica) -> Relation<Log,Event> {
    |l:Log,a,u:Log| match a {
        Action::Deliver(id)=> {
            let n=l.nets.last(); n.pending.contains_key(id) && notice_to(n.pending[id],at(owner))
        },
        _=>false,
    }
}
pub open spec fn avoids(l:Log,owner:Replica) -> bool {
    forall|i:int| 0<=i<l.actions.len() ==> match #[trigger] l.actions[i] {
        Action::Deliver(id)=> !(l.nets[i].pending.contains_key(id) && notice_to(l.nets[i].pending[id],at(owner))),
        _=>true,
    }
}
pub proof fn no_receipt_in_log<S>(m:Program<S>,res:spec_fn(S)->Option<int>,net:Net,reserved:Set<nat>,
    owner:Replica,t:wait::Path<Log,Event>,k:nat)
    requires t.states.len()==t.actions.len()+1,t.states[0]==launch(net),k<=t.actions.len(),
        wait::valid_edges(nb::ordinary(step(m,res,reserved),receipt(owner)),t),
    ensures avoids(t.states[k as int],owner),
    decreases k,
{
    if k>0 {
        let i=(k-1) as nat;no_receipt_in_log(m,res,net,reserved,owner,t,i);
        let l=t.states[i as int];let a=t.actions[i as int];let u=t.states[k as int];let r=step(m,res,reserved);
        assert(nb::ordinary(r,receipt(owner))(l,a,u));
        assert forall|j:int| 0<=j<t.actions.len() implies r(t.states[j],#[trigger] t.actions[j],t.states[j+1]) by {
            assert(nb::ordinary(r,receipt(owner))(t.states[j],t.actions[j],t.states[j+1]));
        }
        run_prefix(m,res,net,reserved,t,i);assert(l.nets.len()==l.actions.len()+1);
        assert forall|j:int| 0<=j<u.actions.len() implies match #[trigger] u.actions[j] {
            Action::Deliver(id)=> !(u.nets[j].pending.contains_key(id) && notice_to(u.nets[j].pending[id],at(owner))), _=>true,
        } by {if j<l.actions.len() {assert(u.actions[j]==l.actions[j]);}}
    }
}

}
