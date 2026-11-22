use vstd::prelude::*;
use crate::stock_facade::*;
use crate::facade_history::*;

verus! {

// A finite linearization witness with an arbitrary finite number of slots
// per physical transition. The witness may depend on the whole prefix.
// Each committed ID has a unique slot inside its call interval.
pub struct Entry { pub id: nat, pub method: Method, pub result: int }
pub struct Grid {
    pub width: spec_fn(nat)->nat,
    pub op: spec_fn(nat,nat)->Option<Entry>,
    pub value: spec_fn(nat,nat)->int,
    pub location: spec_fn(nat)->(nat,nat),
}
pub type CommandSemantics = spec_fn(nat,int)->(int,int); // new state, return value
pub type Begin = spec_fn(nat,nat,Method)->bool;
pub type Answers = spec_fn(nat,nat)->Option<int>;

pub open spec fn effect(f: CommandSemantics, x: int, op: Option<Entry>, y: int) -> bool {
    match op {
        None => x==y, Some(item) => match item.method {
            Method::Read => x==y && item.result==x,
            Method::Command(c) => (y,item.result)==f(c,x),
        },
    }
}
pub open spec fn ordered(g: Grid,f: CommandSemantics,n: nat) -> bool {
    (g.value)(0,0)==1
    && (forall|i: nat| i<n ==> #[trigger] (g.value)(i+1,0)==(g.value)(i,(g.width)(i)))
    && forall|i: nat,j: nat| i<n && j<(g.width)(i) ==> effect(f,(g.value)(i,j),#[trigger] (g.op)(i,j),(g.value)(i,j+1))
}
pub open spec fn slot_matches(g: Grid,i: nat,j: nat,begin: Begin) -> bool {
    match (g.op)(i,j) {
        None=>true, Some(op)=>(g.location)(op.id)==(i,j)
            && exists|h: nat| h<=i && #[trigger] begin(h,op.id,op.method),
    }
}
pub open spec fn accounted(g: Grid,k: nat,id: nat,result: int) -> bool {
    let (i,j)=(g.location)(id); let op=(g.op)(i,j);
    i<k && j<(g.width)(i) && op.is_some() && op.unwrap().id==id && op.unwrap().result==result
}
pub open spec fn certifies(g: Grid,n: nat,begin: Begin,out: Answers) -> bool {
    (forall|i: nat,j: nat| i<n && j<(g.width)(i) ==> #[trigger] slot_matches(g,i,j,begin))
    && forall|k: nat,id: nat| k<=n && (#[trigger] out(k,id)).is_some() ==> accounted(g,k,id,out(k,id).unwrap())
}
pub open spec fn submitted<X,E>(t: Seq<State<X>>,a: Seq<Event<E>>) -> Begin {
    |i: nat,id: nat,m: Method| base_events(t,a)[i as int]==Input::Submit(id,m)
}
pub open spec fn base_linearizable<X,E>(p: Engine<X,E>,f: CommandSemantics) -> bool {
    forall|t: Seq<X>,a: Seq<Input<E>>| #[trigger] backend_path(p,t,a) && t[0]==p.initial ==>
        exists|g: Grid| #[trigger] ordered(g,f,a.len()) && certifies(g,a.len(),
            |i: nat,id: nat,m: Method|a[i as int]==Input::Submit(id,m),|i: nat,id: nat|(p.reply)(t[i as int],id))
}

proof fn read_only_block(g: Grid,f: CommandSemantics,n: nat,i: nat,j: nat)
    requires ordered(g,f,n),i<n,j<=(g.width)(i),
        forall|s: nat| s<j && (#[trigger] (g.op)(i,s)).is_some() ==> ((g.op)(i,s).unwrap().method is Read),
    ensures (g.value)(i,j)==(g.value)(i,0),
    decreases j,
{
    if j>0 { let h=(j-1) as nat; read_only_block(g,f,n,i,h); assert(effect(f,(g.value)(i,h),(g.op)(i,h),(g.value)(i,j))); }
}
proof fn before_any_command(g: Grid,f: CommandSemantics,n: nat,begin: Begin,out: Answers,k: nat)
    requires ordered(g,f,n),certifies(g,n,begin,out),k<=n,
        forall|i: nat,code: nat,id: nat| i<k ==> !(#[trigger] begin(i,id,Method::Command(code))),
    ensures (g.value)(k,0)==1,
    decreases k,
{
    if k>0 {
        let h=(k-1) as nat; before_any_command(g,f,n,begin,out,h);
        assert forall|s: nat| s<(g.width)(h) && (#[trigger] (g.op)(h,s)).is_some() implies (g.op)(h,s).unwrap().method is Read by {
            assert(slot_matches(g,h,s,begin)); let op=(g.op)(h,s).unwrap();
            let i=choose|i:nat| i<=h && #[trigger] begin(i,op.id,op.method);
            if op.method is Command {assert(!begin(i,op.id,Method::Command(op.method->Command_0)));}
        }
        read_only_block(g,f,n,h,(g.width)(h));
        assert((g.value)(h+1,0)==(g.value)(h,(g.width)(h)));
    }
}
pub open spec fn fast<X>(s: State<X>,id: nat) -> bool {
    s.calls.contains_key(id) && s.calls[id].answer.is_some() && !s.calls[id].submitted
}
pub open spec fn inserted<X,E>(end: State<X>,a: Event<E>) -> Option<Entry> {
    match a {
        Event::Invoke(id,Method::Read) if fast(end,id) => Some(Entry {id,method:Method::Read,result:end.calls[id].answer.unwrap()}),
        _=>None,
    }
}
pub open spec fn expanded<X,E>(g: Grid,end: State<X>,a: Seq<Event<E>>) -> Grid {
    Grid { width: |i| (g.width)(i)+1,
        op: |i: nat,j: nat| if j==0 {inserted(end,a[i as int])} else {(g.op)(i,(j-1) as nat)},
        value: |i: nat,j: nat| (g.value)(i,if j==0 {0} else {(j-1) as nat}),
        location: |id| if fast(end,id) {
            (choose|i: nat| i<a.len() && #[trigger] a[i as int]==Event::Invoke(id,Method::Read),0)
        } else { let (i,j)=(g.location)(id); (i,j+1) },
    }
}
proof fn knows_fast_location<X,E>(p: Engine<X,E>,t: Seq<State<X>>,a: Seq<Event<E>>,id: nat,i: nat,g: Grid)
    requires path(p,t,a),i<a.len(),a[i as int]==Event::Invoke(id,Method::Read),fast(t.last(),id),
    ensures (expanded(g,t.last(),a).location)(id)==(i,0),
{
    let j=choose|j: nat| j<a.len() && #[trigger] a[j as int]==Event::Invoke(id,Method::Read);
    if i<j { one_invocation(p,t,a,i,j,id); } else if j<i { one_invocation(p,t,a,j,i,id); }
}

pub proof fn wrap_linearization<X,E>(p: Engine<X,E>,f: CommandSemantics,t: Seq<State<X>>,a: Seq<Event<E>>,g: Grid)
    requires ports(p),path(p,t,a),t[0]==initial(p),ordered(g,f,a.len()),
        certifies(g,a.len(),submitted(t,a),|i: nat,id: nat|(p.reply)(base_states(t)[i as int],id)),
    ensures ({
        let u=expanded(g,t.last(),a);
        ordered(u,f,a.len()) && certifies(u,a.len(),|i: nat,id: nat,m: Method| a[i as int]==Event::Invoke(id,m),
            |i: nat,id: nat|answer(t[i as int],id))
    }),
{
    hide(step); hide(rows); hide(early); hide(delegate);
    let n=a.len(); let end=t.last(); let u=expanded(g,end,a);
    let begin=submitted(t,a); let out=|i: nat,id: nat|(p.reply)(base_states(t)[i as int],id);
    let outer=|i: nat,id: nat,m: Method| a[i as int]==Event::Invoke(id,m);
    assert forall|i: nat,j: nat| i<n && j<(u.width)(i) implies effect(f,(u.value)(i,j),#[trigger] (u.op)(i,j),(u.value)(i,j+1)) by {
        if j==0 {
            if inserted(end,a[i as int]).is_some() {
                let id=a[i as int]->Invoke_0; fast_invoked_before_commands(p,t,a,n,id,i);
                assert forall|h: nat,code: nat,id2: nat| h<i implies !(#[trigger] begin(h,id2,Method::Command(code))) by {
                    assert(!(input(t[h as int],a[h as int]) is Submit && input(t[h as int],a[h as int])->Submit_1 is Command));
                }
                before_any_command(g,f,n,begin,out,i);
            }
        } else { let h=(j-1) as nat; assert(effect(f,(g.value)(i,h),(g.op)(i,h),(g.value)(i,j))); }
    }
    assert forall|i: nat| i<n implies #[trigger] (u.value)(i+1,0)==(u.value)(i,(u.width)(i)) by {
        assert((g.value)(i+1,0)==(g.value)(i,(g.width)(i)));
    }
    assert forall|i: nat,j: nat| i<n && j<(u.width)(i) implies #[trigger] slot_matches(u,i,j,outer) by {
        if j==0 {
            if inserted(end,a[i as int]).is_some() {
                let id=a[i as int]->Invoke_0; knows_fast_location(p,t,a,id,i,g); assert(outer(i,id,Method::Read));
            }
        } else {
            let k=(j-1) as nat; assert(slot_matches(g,i,k,begin));
            if (g.op)(i,k).is_some() {
                let op=(g.op)(i,k).unwrap(); let id=op.id;
                let h=choose|h:nat|h<=i && #[trigger] begin(h,id,op.method);
                let s=t[h as int]; let e=a[h as int]; assert(enabled(p,s,e) && t[h as int+1]==step(p,s,e));
                assert(s.calls.contains_key(id) && s.calls[id].method==op.method && t[h as int+1].calls.contains_key(id) && t[h as int+1].calls[id].submitted) by {
                    reveal(step); reveal(delegate);
                }
                persists(p,t,a,h+1,n,id); let inv=birth(p,t,a,h,id);
                assert(t.last()==t[n as int] && t.last().calls[id].submitted);
                assert(a[inv as int]==Event::Invoke(id,op.method));
                assert(!fast(end,id) && outer(inv,id,op.method));
            }
        }
    }
    assert forall|k: nat,id: nat| k<=n && (#[trigger] answer(t[k as int],id)).is_some() implies
        accounted(u,k,id,answer(t[k as int],id).unwrap()) by {
        let d=decision(p,t,a,k,id); let v=answer(t[k as int],id).unwrap();
        persists(p,t,a,k,n,id);
        if fast(end,id) {
            let i=birth(p,t,a,k,id); assert(t[k as int].calls[id].method is Read) by {reveal(early);}
            knows_fast_location(p,t,a,id,i,g);
        } else {
            assert(out(d,id)==Some(v)); assert(accounted(g,d,id,v));
        }
    }
}

pub proof fn all_outer_histories_linearize<X,E>(p: Engine<X,E>,f: CommandSemantics,t: Seq<State<X>>,a: Seq<Event<E>>)
    requires ports(p),base_linearizable(p,f),path(p,t,a),t[0]==initial(p),
    ensures exists|u: Grid| #[trigger] ordered(u,f,a.len()) && certifies(u,a.len(),
        |i: nat,id: nat,m: Method| a[i as int]==Event::Invoke(id,m),|i: nat,id: nat|answer(t[i as int],id)),
{
    projection(p,t,a);
    let xs=base_states(t); let es=base_events(t,a);
    let g=choose|g: Grid| #[trigger] ordered(g,f,es.len()) && certifies(g,es.len(),
        |i: nat,id: nat,m: Method|es[i as int]==Input::Submit(id,m),|i: nat,id: nat|(p.reply)(xs[i as int],id));
    assert(submitted(t,a) =~= (|i: nat,id: nat,m: Method| es[i as int]==Input::Submit(id,m)));
    assert((|i: nat,id: nat|(p.reply)(xs[i as int],id)) =~= (|i: nat,id: nat|(p.reply)(base_states(t)[i as int],id)));
    wrap_linearization(p,f,t,a,g);
}

}
