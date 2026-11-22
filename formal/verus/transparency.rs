use vstd::prelude::*;

verus! {

pub enum StrongEffect<W> {
    StrongOnly,
    AwaitWeak(W),
    ReplicateWeak(W),
    OrderWeak(W),
    MaintainWeak(W),
}

// A transition policy on effects, independent of the operation result,
// the history proof, and the particular schedules under comparison.
pub open spec fn permitted<W>(effect: StrongEffect<W>) -> bool {
    match effect {
        StrongEffect::StrongOnly => true,
        _ => false,
    }
}

pub open spec fn effects_transparent<W>(effects: Set<StrongEffect<W>>) -> bool {
    forall|e: StrongEffect<W>| #[trigger] effects.contains(e) ==> permitted(e)
}

// An audit obligation on a model's effect labels. For a prior observed
// weak write, loss of its order under an admissible replacement of prior
// strong information is reported as a MaintainWeak effect of the actual
// trace. The tracked order witness need not be the returned register value.
pub open spec fn reports_retained_order<B, F, D, W>(
    resume: spec_fn(B, F) -> D,
    effects: spec_fn(B, F) -> Set<StrongEffect<W>>,
    maintains: spec_fn(D, W) -> bool,
    eligible: spec_fn(B, F, F, W) -> bool,
) -> bool {
    forall|context: B, actual: F, alternate: F, w: W|
        #[trigger] eligible(context, actual, alternate, w)
            && maintains(resume(context, actual), w)
            && !maintains(resume(context, alternate), w)
        ==> effects(context, actual).contains(StrongEffect::MaintainWeak(w))
}

pub proof fn transparent_effects_exclude_retained_order<B, F, D, W>(
    resume: spec_fn(B, F) -> D,
    effects: spec_fn(B, F) -> Set<StrongEffect<W>>,
    maintains: spec_fn(D, W) -> bool,
    eligible: spec_fn(B, F, F, W) -> bool,
    context: B, actual: F, alternate: F, w: W,
)
    requires
        reports_retained_order(resume, effects, maintains, eligible),
        eligible(context, actual, alternate, w),
        effects_transparent(effects(context, actual)),
        maintains(resume(context, actual), w),
    ensures maintains(resume(context, alternate), w),
{
    if !maintains(resume(context, alternate), w) {
        let e = StrongEffect::MaintainWeak(w);
        assert(effects(context, actual).contains(e));
        assert(permitted(e));
    }
}

pub proof fn strong_only_permitted_even_when_metadata_changes(before: int, after: int)
    ensures
        effects_transparent(Set::<StrongEffect<int>>::empty().insert(StrongEffect::StrongOnly)),
        after != before ==> permitted::<int>(StrongEffect::StrongOnly),
{}

pub proof fn ordinary_strong_metadata_passes_the_audit()
    ensures
        reports_retained_order(
            |value: int, counter: nat| (value, counter + 1),
            |value: int, counter: nat| Set::empty().insert(StrongEffect::StrongOnly),
            |decision: (int, nat), writer: int| decision.0 == writer,
            |value: int, actual: nat, alternate: nat, writer: int| true,
        ),
        effects_transparent(Set::<StrongEffect<int>>::empty().insert(StrongEffect::StrongOnly)),
{}

pub proof fn actual_weak_promotion_is_rejected<W>(w: W)
    ensures
        !permitted(StrongEffect::AwaitWeak(w)),
        !permitted(StrongEffect::ReplicateWeak(w)),
        !permitted(StrongEffect::OrderWeak(w)),
        !permitted(StrongEffect::MaintainWeak(w)),
{}

// Unchecked effect labels alone would let an order-preserving selector
// describe itself as doing ordinary strong work.
pub proof fn unaudited_strong_only_label_is_insufficient()
    ensures
        effects_transparent(Set::<StrongEffect<int>>::empty().insert(StrongEffect::StrongOnly)),
        !reports_retained_order(
            |context: (), bit: bool| if bit { 2int } else { 5int },
            |context: (), bit: bool| Set::empty().insert(StrongEffect::StrongOnly),
            |decision: int, w: int| decision == w,
            |context: (), actual: bool, alternate: bool, writer: int| true,
        ),
{
    let resume = |context: (), bit: bool| if bit { 2int } else { 5int };
    let effects = |context: (), bit: bool| Set::empty().insert(StrongEffect::<int>::StrongOnly);
    let maintains = |decision: int, w: int| decision == w;
    let eligible = |context: (), actual: bool, alternate: bool, writer: int| true;
    if reports_retained_order(resume, effects, maintains, eligible) {
        assert(eligible((), false, true, 5));
        assert(effects((), false).contains(StrongEffect::MaintainWeak(5)));
    }
}

pub enum OrderOrigin { Unordered, WeakG, Strong }

pub enum OrderAction {
    WeakPathStabilizes,
    StrongEstablishes,
    StrongReads,
    StrongMetadata,
}

pub open spec fn order_origin_after(before: OrderOrigin, action: OrderAction) -> OrderOrigin {
    match action {
        OrderAction::WeakPathStabilizes => OrderOrigin::WeakG,
        OrderAction::StrongEstablishes if before != OrderOrigin::WeakG => OrderOrigin::Strong,
        _ => before,
    }
}

pub open spec fn transition_effect<W>(
    before: OrderOrigin, action: OrderAction, w: W,
) -> StrongEffect<W> {
    match action {
        OrderAction::StrongEstablishes if before != OrderOrigin::WeakG =>
            StrongEffect::OrderWeak(w),
        _ => StrongEffect::StrongOnly,
    }
}

pub proof fn read_of_weak_g_is_not_promotion<W>(w: W)
    ensures
        order_origin_after(OrderOrigin::WeakG, OrderAction::StrongReads) == OrderOrigin::WeakG,
        permitted(transition_effect(OrderOrigin::WeakG, OrderAction::StrongReads, w)),
        !permitted(transition_effect(OrderOrigin::Unordered, OrderAction::StrongEstablishes, w)),
        order_origin_after(OrderOrigin::Unordered, OrderAction::StrongEstablishes)
            == OrderOrigin::Strong,
{}

pub open spec fn reachable_footprint<F, W>(histories: Set<(F, W)>, footprint: F) -> bool {
    exists|writer: W| #[trigger] histories.contains((footprint, writer))
}

pub open spec fn reachable_with_observation<F, W>(
    histories: Set<(F, W)>, footprint: F, writer: W,
) -> bool {
    histories.contains((footprint, writer))
}

pub proof fn reachable_swap_need_not_preserve_observed_history()
    ensures ({
        let histories = Set::empty().insert((false, 5int)).insert((true, 2int));
        reachable_with_observation(histories, false, 5)
            && reachable_footprint(histories, true)
            && !reachable_with_observation(histories, true, 5)
    }),
{
    let histories = Set::empty().insert((false, 5int)).insert((true, 2int));
    assert(histories.contains((true, 2int)));
}

// Semantic completion effects. Unlike an externally supplied audit,
// maintenance effects are generated from the decision semantics for every
// eligible replacement. Direct effects still come from the transition model.
#[verifier::reject_recursive_types(B)]
#[verifier::reject_recursive_types(F)]
#[verifier::reject_recursive_types(D)]
#[verifier::reject_recursive_types(W)]
pub struct OrderSemantics<B, F, D, W> {
    pub resume: spec_fn(B, F) -> D,
    pub maintains: spec_fn(D, W) -> bool,
    pub eligible: spec_fn(B, F, F, W) -> bool,
    pub before_sr1: spec_fn(B, W) -> OrderOrigin,
}

pub open spec fn semantic_effects<B, F, D, W>(
    m: OrderSemantics<B, F, D, W>, direct: Set<StrongEffect<W>>, context: B, actual: F,
) -> spec_fn(StrongEffect<W>) -> bool {
    |effect: StrongEffect<W>| direct.contains(effect) || match effect {
        StrongEffect::MaintainWeak(w) =>
            (m.before_sr1)(context, w) != OrderOrigin::WeakG
                && (m.maintains)((m.resume)(context, actual), w)
                && exists|alternate: F| #[trigger] (m.eligible)(context, actual, alternate, w)
                    && !(m.maintains)((m.resume)(context, alternate), w),
        _ => false,
    }
}

pub open spec fn semantic_transparent<W>(effect: spec_fn(StrongEffect<W>) -> bool) -> bool {
    forall|e: StrongEffect<W>| #[trigger] effect(e) ==> permitted(e)
}

pub proof fn semantic_policy_guards_order<B, F, D, W>(
    m: OrderSemantics<B, F, D, W>, direct: Set<StrongEffect<W>>,
    context: B, actual: F, alternate: F, w: W,
)
    requires
        (m.eligible)(context, actual, alternate, w),
        (m.before_sr1)(context, w) != OrderOrigin::WeakG,
        semantic_transparent(semantic_effects(m, direct, context, actual)),
        (m.maintains)((m.resume)(context, actual), w),
    ensures (m.maintains)((m.resume)(context, alternate), w),
{
    if !(m.maintains)((m.resume)(context, alternate), w) {
        let e = StrongEffect::MaintainWeak(w);
        assert(semantic_effects(m, direct, context, actual)(e));
        assert(permitted(e));
    }
}

pub open spec fn metadata_only() -> OrderSemantics<int, nat, (int, nat), int> {
    OrderSemantics {
        resume: |value: int, counter: nat| (value, counter + 1),
        maintains: |decision: (int, nat), writer: int| decision.0 == writer,
        eligible: |value: int, actual: nat, alternate: nat, writer: int| true,
        before_sr1: |value: int, writer: int| OrderOrigin::Unordered,
    }
}

pub proof fn semantic_policy_allows_metadata_change(value: int, counter: nat)
    ensures semantic_transparent(semantic_effects(metadata_only(),
        Set::empty().insert(StrongEffect::StrongOnly), value, counter)),
{
    let effects = semantic_effects(metadata_only(),
        Set::empty().insert(StrongEffect::StrongOnly), value, counter);
    assert forall|e: StrongEffect<int>| #[trigger] effects(e) implies permitted(e) by {
        match e {
            StrongEffect::MaintainWeak(w) => {
                assert forall|alt: nat| (metadata_only().maintains)(
                    #[trigger] (metadata_only().resume)(value, alt), w)
                    == (value == w) by {};
            },
            _ => {},
        }
    }
}

pub open spec fn selecting_retained_writer() -> OrderSemantics<(), bool, int, int> {
    OrderSemantics {
        resume: |context: (), bit: bool| if bit { 2int } else { 5int },
        maintains: |decision: int, writer: int| decision == writer,
        eligible: |context: (), actual: bool, alternate: bool, writer: int| writer == 5,
        before_sr1: |context: (), writer: int| OrderOrigin::Unordered,
    }
}

// The semantic policy detects a promotion even if every directly declared
// effect was ordinary strong work.
pub proof fn semantic_policy_rejects_implicit_order_maintenance()
    ensures
        effects_transparent(Set::<StrongEffect<int>>::empty().insert(StrongEffect::StrongOnly)),
        !semantic_transparent(semantic_effects(selecting_retained_writer(),
            Set::empty().insert(StrongEffect::StrongOnly), (), false)),
{
    let m = selecting_retained_writer();
    let effects = semantic_effects(m, Set::empty().insert(StrongEffect::StrongOnly), (), false);
    let e = StrongEffect::MaintainWeak(5int);
    assert((m.eligible)((), false, true, 5int));
    assert(!(m.maintains)((m.resume)((), true), 5int));
    assert(effects(e));
    if semantic_transparent(effects) {
        assert(permitted(e));
    }
}

pub proof fn semantic_policy_rejects_direct_replication<B, F, D, W>(
    m: OrderSemantics<B, F, D, W>, context: B, actual: F, w: W,
)
    ensures !semantic_transparent(semantic_effects(m,
        Set::empty().insert(StrongEffect::ReplicateWeak(w)), context, actual)),
{
    let effect = StrongEffect::ReplicateWeak(w);
    let direct = Set::empty().insert(effect);
    let effects = semantic_effects(m, direct, context, actual);
    assert(direct.contains(effect));
    assert(effects(effect));
    if semantic_transparent(effects) {
        assert(permitted(effect));
    }
}

// The semantic test does not infer new ordering work for an already-G
// observation. An explicit prohibited effect still fails independently.
pub proof fn stabilized_observation_needs_no_new_maintenance<B, F, D, W>(
    m: OrderSemantics<B, F, D, W>, context: B, actual: F, w: W,
)
    requires (m.before_sr1)(context, w) == OrderOrigin::WeakG,
    ensures !semantic_effects(m, Set::empty(), context, actual)(StrongEffect::MaintainWeak(w)),
{}

// Project actual trace records. A cross-history comparison does not
// certify that the alternative executed the actual writer's history.
pub open spec fn real_trace_alternative<B, F, W>(
    histories: Set<(B, F, W)>, context: B, actual: F, other: F, observed: W,
) -> bool {
    histories.contains((context, actual, observed))
        && exists|other_observed: W| #[trigger] histories.contains((context, other, other_observed))
}

pub open spec fn same_history_alternative<B, F, W>(
    histories: Set<(B, F, W)>, context: B, actual: F, other: F, observed: W,
) -> bool {
    histories.contains((context, actual, observed))
        && histories.contains((context, other, observed))
}

pub proof fn real_trace_alternative_from_actual_runs<B, F, W>(
    histories: Set<(B, F, W)>, context: B, actual: F, other: F, observed: W, other_observed: W,
)
    requires
        histories.contains((context, actual, observed)),
        histories.contains((context, other, other_observed)),
    ensures real_trace_alternative(histories, context, actual, other, observed),
{}

// A general inter-trace consequence of the semantic policy under the
// cross-history interpretation. H is neither a definition nor a premise
// here; in HOT it establishes that each actual run maintains its writer.
pub proof fn semantic_policy_compares_two_actual_runs<B, F, D, W>(
    m: OrderSemantics<B, F, D, W>, direct: Set<StrongEffect<W>>,
    histories: Set<(B, F, W)>, context: B, actual: F, other: F, observed: W, other_observed: W,
)
    requires
        m.eligible == (|b, a, c, w| real_trace_alternative(histories, b, a, c, w)),
        histories.contains((context, actual, observed)),
        histories.contains((context, other, other_observed)),
        (m.before_sr1)(context, observed) != OrderOrigin::WeakG,
        semantic_transparent(semantic_effects(m, direct, context, actual)),
        (m.maintains)((m.resume)(context, actual), observed),
    ensures (m.maintains)((m.resume)(context, other), observed),
{
    real_trace_alternative_from_actual_runs(histories, context, actual, other, observed, other_observed);
    semantic_policy_guards_order(m, direct, context, actual, other, observed);
}

pub proof fn different_writers_separate_real_trace_eligibility_rules()
    ensures ({
        let histories = Set::empty().insert(((), false, 5int)).insert(((), true, 2int));
        real_trace_alternative(histories, (), false, true, 5)
            && real_trace_alternative(histories, (), true, false, 2)
            && !same_history_alternative(histories, (), false, true, 5)
            && !same_history_alternative(histories, (), true, false, 2)
    }),
{
    let histories = Set::empty().insert(((), false, 5int)).insert(((), true, 2int));
    real_trace_alternative_from_actual_runs(histories, (), false, true, 5, 2);
    real_trace_alternative_from_actual_runs(histories, (), true, false, 2, 5);
}

// This context carries an independently durable weak-path decision.
// The strong reader consumes it without using its retained strong counter.
pub open spec fn reads_certified_order() -> OrderSemantics<int, nat, int, int> {
    OrderSemantics {
        resume: |certificate: int, counter: nat| certificate,
        maintains: |decision: int, writer: int| decision == writer,
        eligible: |certificate: int, actual: nat, other: nat, writer: int| true,
        before_sr1: |certificate: int, writer: int|
            if certificate == writer { OrderOrigin::WeakG } else { OrderOrigin::Unordered },
    }
}

pub proof fn ordinary_reads_can_report_different_surviving_certificates(a: nat, b: nat)
    ensures
        (reads_certified_order().resume)(5, a) == 5,
        (reads_certified_order().resume)(2, b) == 2,
        semantic_transparent(semantic_effects(reads_certified_order(),
            Set::empty().insert(StrongEffect::StrongOnly), 5, a)),
        semantic_transparent(semantic_effects(reads_certified_order(),
            Set::empty().insert(StrongEffect::StrongOnly), 2, b)),
{
    certified_read_is_transparent(5, a);
    certified_read_is_transparent(2, b);
}

proof fn certified_read_is_transparent(certificate: int, counter: nat)
    ensures semantic_transparent(semantic_effects(reads_certified_order(),
        Set::empty().insert(StrongEffect::StrongOnly), certificate, counter)),
{
    let effects = semantic_effects(reads_certified_order(),
        Set::empty().insert(StrongEffect::StrongOnly), certificate, counter);
    assert forall|e: StrongEffect<int>| #[trigger] effects(e) implies permitted(e) by {
        match e {
            StrongEffect::MaintainWeak(w) => {
                if w == certificate {
                    assert((reads_certified_order().before_sr1)(certificate, w) == OrderOrigin::WeakG);
                } else {
                    assert(!(reads_certified_order().maintains)(
                        (reads_certified_order().resume)(certificate, counter), w));
                }
            },
            _ => {},
        }
    }
}

}
