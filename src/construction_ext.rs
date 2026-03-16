use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas;
use verus_algebra::lemmas::ring_lemmas;
use verus_algebra::lemmas::ordered_ring_lemmas;
use verus_algebra::quadratic::lemma_div_congruence;
use verus_quadratic_extension::lemmas::lemma_square_zero;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::line_intersection::*;
use verus_geometry::circle_line::*;
use verus_geometry::circle_circle::*;
use verus_geometry::constructed_scalar::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::radicand::*;
use verus_linalg::vec2::ops::lemma_norm_sq_congruence as lemma_vec2_norm_sq_congruence;
use verus_linalg::vec2::ops::lemma_dot_congruence as lemma_vec2_dot_congruence;
use crate::entities::*;
use crate::constraints::*;
use crate::locus::*;
use crate::construction::*;
use crate::runtime::solver::{step_geometrically_valid, step_has_positive_discriminant};
use crate::runtime::construction::step_radicand_matches;

verus! {

// ===========================================================================
//  Phase 2: Constraint lifting
// ===========================================================================

/// Lift a single constraint from F to SpecQuadExt<F, R>.
/// Only DistanceSq, FixedX, FixedY have T-typed fields needing embedding;
/// all others just copy EntityIds.
pub open spec fn lift_constraint<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
) -> Constraint<SpecQuadExt<F, R>> {
    match c {
        Constraint::Coincident { a, b } =>
            Constraint::Coincident { a, b },
        Constraint::DistanceSq { a, b, dist_sq } =>
            Constraint::DistanceSq { a, b, dist_sq: qext_from_rational(dist_sq) },
        Constraint::FixedX { point, x } =>
            Constraint::FixedX { point, x: qext_from_rational(x) },
        Constraint::FixedY { point, y } =>
            Constraint::FixedY { point, y: qext_from_rational(y) },
        Constraint::SameX { a, b } =>
            Constraint::SameX { a, b },
        Constraint::SameY { a, b } =>
            Constraint::SameY { a, b },
        Constraint::PointOnLine { point, line_a, line_b } =>
            Constraint::PointOnLine { point, line_a, line_b },
        Constraint::EqualLengthSq { a1, a2, b1, b2 } =>
            Constraint::EqualLengthSq { a1, a2, b1, b2 },
        Constraint::Midpoint { mid, a, b } =>
            Constraint::Midpoint { mid, a, b },
        Constraint::Perpendicular { a1, a2, b1, b2 } =>
            Constraint::Perpendicular { a1, a2, b1, b2 },
        Constraint::Parallel { a1, a2, b1, b2 } =>
            Constraint::Parallel { a1, a2, b1, b2 },
        Constraint::Collinear { a, b, c } =>
            Constraint::Collinear { a, b, c },
        Constraint::PointOnCircle { point, center, radius_point } =>
            Constraint::PointOnCircle { point, center, radius_point },
        Constraint::Symmetric { point, original, axis_a, axis_b } =>
            Constraint::Symmetric { point, original, axis_a, axis_b },
        Constraint::FixedPoint { point, x, y } =>
            Constraint::FixedPoint { point, x: qext_from_rational(x), y: qext_from_rational(y) },
        Constraint::Ratio { a1, a2, b1, b2, ratio_sq } =>
            Constraint::Ratio { a1, a2, b1, b2, ratio_sq: qext_from_rational(ratio_sq) },
        Constraint::Tangent { line_a, line_b, center, radius_point } =>
            Constraint::Tangent { line_a, line_b, center, radius_point },
        Constraint::CircleTangent { c1, rp1, c2, rp2 } =>
            Constraint::CircleTangent { c1, rp1, c2, rp2 },
        Constraint::Angle { a1, a2, b1, b2, cos_sq } =>
            Constraint::Angle { a1, a2, b1, b2, cos_sq: qext_from_rational(cos_sq) },
    }
}

/// Lift a sequence of constraints.
pub open spec fn lift_constraints<F: OrderedField, R: PositiveRadicand<F>>(
    cs: Seq<Constraint<F>>,
) -> Seq<Constraint<SpecQuadExt<F, R>>> {
    cs.map(|_i, c: Constraint<F>| lift_constraint::<F, R>(c))
}

// ===========================================================================
//  Phase 2: Preservation lemmas
// ===========================================================================

/// Lifting preserves constraint_entities (all EntityId-based, field-independent).
pub proof fn lemma_lift_constraint_entities<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
)
    ensures
        constraint_entities(lift_constraint::<F, R>(c)) == constraint_entities(c),
{
    // Each variant preserves the same EntityId fields.
}

/// Lifting preserves constraint_locus_entities.
pub proof fn lemma_lift_constraint_locus_entities<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
)
    ensures
        constraint_locus_entities(lift_constraint::<F, R>(c)) == constraint_locus_entities(c),
{
    // Each variant preserves the same EntityId fields.
}

/// Lifting preserves constraint_well_formed.
pub proof fn lemma_lift_constraint_well_formed<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
)
    requires
        constraint_well_formed(c),
    ensures
        constraint_well_formed(lift_constraint::<F, R>(c)),
{
    // Well-formedness is purely about EntityId distinctness — field-independent.
}

/// Lifting preserves is_verification_constraint.
pub proof fn lemma_lift_is_verification_constraint<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
)
    ensures
        is_verification_constraint(lift_constraint::<F, R>(c))
            == is_verification_constraint(c),
{
    // Same variant tag after lifting — Tangent/CircleTangent/Angle are preserved.
}

// ===========================================================================
//  Phase 3: Plan lifting & domain preservation
// ===========================================================================

/// Lift a construction plan from F to SpecQuadExt<F, R>.
pub open spec fn lift_plan<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
) -> ConstructionPlan<SpecQuadExt<F, R>> {
    plan.map(|_i, s: ConstructionStep<F>| lift_construction_step::<F, R>(s))
}

/// Lifting preserves the domain of execute_plan.
/// Key insight: step_target(lift_step(s)) == step_target(s), so each insertion
/// uses the same key.
pub proof fn lemma_lift_plan_domain<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
)
    ensures
        execute_plan(lift_plan::<F, R>(plan)).dom() == execute_plan(plan).dom(),
    decreases plan.len(),
{
    if plan.len() == 0 {
        // Both empty maps
    } else {
        let prefix = plan.drop_last();
        let step = plan.last();

        // Recurse on prefix
        lemma_lift_plan_domain::<F, R>(prefix);

        // Key fact: step_target is preserved
        lemma_lift_step_target::<F, R>(step);

        // lift_plan(plan) = lift_plan(prefix).push(lift_step(step))
        // Need to show lift_plan(plan).drop_last() == lift_plan(prefix)
        // and lift_plan(plan).last() == lift_step(step)
        assert(lift_plan::<F, R>(plan).len() == plan.len());
        assert(lift_plan::<F, R>(plan).drop_last() =~= lift_plan::<F, R>(prefix));
        assert(lift_plan::<F, R>(plan).last() == lift_construction_step::<F, R>(step));

        // Both maps insert with the same key into domains that are equal (by IH)
    }
}

/// Lifting preserves distinct targets.
pub proof fn lemma_lift_plan_distinct_targets<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
)
    requires
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
    ensures
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(#[trigger] lift_plan::<F, R>(plan)[i])
                != step_target(#[trigger] lift_plan::<F, R>(plan)[j]),
{
    assert forall|i: int, j: int|
        0 <= i < plan.len() && 0 <= j < plan.len() && i != j
    implies
        step_target(#[trigger] lift_plan::<F, R>(plan)[i])
            != step_target(#[trigger] lift_plan::<F, R>(plan)[j])
    by {
        lemma_lift_step_target::<F, R>(plan[i]);
        lemma_lift_step_target::<F, R>(plan[j]);
        // lift_plan(plan)[i] == lift_construction_step(plan[i])
        // step_target(lift(plan[i])) == step_target(plan[i]) != step_target(plan[j]) == step_target(lift(plan[j]))
    }
}

// ===========================================================================
//  Phase 4: Deterministic execution model
// ===========================================================================

/// Execute a plan in the extension field Q(√R), using deterministic
/// circle intersection formulas instead of `choose|p|`.
pub open spec fn execute_plan_in_ext<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
) -> ResolvedPoints<SpecQuadExt<F, R>>
    decreases plan.len(),
{
    if plan.len() == 0 {
        Map::empty()
    } else {
        let prefix = plan.drop_last();
        let step = plan.last();
        execute_plan_in_ext::<F, R>(prefix)
            .insert(step_target(step), execute_step_in_ext::<F, R>(step))
    }
}

/// Domain of execute_plan_in_ext equals domain of execute_plan.
pub proof fn lemma_execute_plan_in_ext_domain<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
)
    ensures
        execute_plan_in_ext::<F, R>(plan).dom() == execute_plan(plan).dom(),
    decreases plan.len(),
{
    if plan.len() == 0 {
        // Both empty
    } else {
        let prefix = plan.drop_last();
        let step = plan.last();
        lemma_execute_plan_in_ext_domain::<F, R>(prefix);
        // Both insert step_target(step) into maps with equal domains
    }
}

/// A step is "rational" if it resolves to a purely rational position
/// (Fixed, LineLine, or Determined — no circle intersections).
pub open spec fn is_rational_step<F: OrderedField>(step: ConstructionStep<F>) -> bool {
    match step {
        ConstructionStep::PointStep { .. } => true,
        ConstructionStep::LineLine { .. } => true,
        ConstructionStep::CircleLine { .. } => false,
        ConstructionStep::CircleCircle { .. } => false,
    }
}

/// The set of circle step targets in a plan.
pub open spec fn circle_targets<F: OrderedField>(
    plan: ConstructionPlan<F>,
) -> Set<EntityId> {
    Set::new(|id: EntityId|
        exists|i: int| 0 <= i < plan.len()
            && !is_rational_step(#[trigger] plan[i])
            && step_target(plan[i]) == id)
}

/// A plan has "independent circles": for every circle step, every constraint
/// referencing its target has no OTHER entities that are also circle targets.
/// This means circle steps don't depend on each other's results, so the
/// lifted plan data matches the extension field positions.
pub open spec fn is_independent_circle_plan<F: OrderedField>(
    plan: ConstructionPlan<F>,
    constraints: Seq<Constraint<F>>,
) -> bool {
    forall|i: int| #![trigger plan[i]]
        0 <= i < plan.len() && !is_rational_step(plan[i]) ==> {
        let target = step_target(plan[i]);
        forall|ci: int| #![trigger constraints[ci]]
            0 <= ci < constraints.len()
            && constraint_entities(constraints[ci]).contains(target)
            ==> forall|e: EntityId|
                constraint_entities(constraints[ci]).contains(e) && e != target
                ==> !circle_targets(plan).contains(e)
    }
}

/// A plan is "fully independent": for EVERY step (not just circle steps),
/// every constraint referencing the step's target has no OTHER entities
/// that are circle targets. This ensures that all constraint inputs at
/// any step are rational entries, so the extension-level resolved map
/// agrees with the lifted base map at those entries.
///
/// Implies `is_independent_circle_plan` (strictly stronger).
/// A plan is "domain-independent" if, at each step si, every constraint
/// referencing the step target has no OTHER entities that are BOTH
/// (a) in the resolved map at step si, AND (b) circle targets.
///
/// This is weaker than requiring ALL other entities to be non-circle-targets,
/// which would fail for full plans (with initial PointSteps) when a constraint
/// references both an initial entity and a circle target that comes later.
/// With initial-first ordering, circle targets are NOT yet in the domain at
/// initial steps, so the condition is vacuously satisfied for those steps.
pub open spec fn is_fully_independent_plan<F: OrderedField>(
    plan: ConstructionPlan<F>,
    constraints: Seq<Constraint<F>>,
) -> bool {
    forall|i: int| #![trigger plan[i]]
        0 <= i < plan.len() ==> {
        let target = step_target(plan[i]);
        forall|ci: int| #![trigger constraints[ci]]
            0 <= ci < constraints.len()
            && constraint_entities(constraints[ci]).contains(target)
            ==> forall|e: EntityId|
                constraint_entities(constraints[ci]).contains(e) && e != target
                && execute_plan(plan.take(i)).dom().contains(e)
                ==> !circle_targets(plan).contains(e)
    }
}

// ===========================================================================
//  Phase 5: Sign variant soundness
// ===========================================================================

/// Each step in a feasible variant has step_well_formed at the extension field level.
/// This bridges the runtime's geometric validity + positive discriminant checks
/// to the spec-level well-formedness required by plan_valid.
pub proof fn lemma_feasible_variant_steps_well_formed<R: PositiveRadicand<RationalModel>>(
    variant: Seq<ConstructionStep<RationalModel>>,
)
    requires
        forall|j: int| #![trigger variant[j]]
            0 <= j < variant.len() ==> step_geometrically_valid(variant[j]),
        forall|j: int| #![trigger variant[j]]
            0 <= j < variant.len() ==> step_has_positive_discriminant(variant[j]),
        forall|j: int| #![trigger variant[j]]
            0 <= j < variant.len() ==> step_radicand_matches::<R>(variant[j]),
    ensures
        forall|j: int| #![trigger variant[j]]
            0 <= j < variant.len() ==>
            step_well_formed(lift_construction_step::<RationalModel, R>(variant[j])),
{
    assert forall|j: int| #![trigger variant[j]]
        0 <= j < variant.len()
    implies
        step_well_formed(lift_construction_step::<RationalModel, R>(variant[j]))
    by {
        let step = variant[j];
        // step_geometrically_valid + step_has_positive_discriminant + step_radicand_matches
        // together imply the preconditions of lemma_lifted_step_well_formed
        lemma_lifted_step_well_formed::<RationalModel, R>(step);
    }
}

type RationalModel = verus_rational::rational::Rational;

/// A lifted plan is valid when:
/// - Original plan has distinct targets
/// - Each step is geometrically valid with positive discriminant and matching radicand
pub proof fn lemma_lift_plan_valid<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
)
    requires
        // Original plan has distinct targets
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        // Each step geometrically valid + positive disc + radicand matches
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_has_positive_discriminant(plan[j]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_radicand_matches::<R>(plan[j]),
    ensures
        plan_valid(
            lift_plan::<RationalModel, R>(plan),
            lift_constraints::<RationalModel, R>(constraints),
        ),
{
    // 1. Distinct targets preserved
    lemma_lift_plan_distinct_targets::<RationalModel, R>(plan);

    // 2. Each step well-formed
    // We need: forall|i| step_well_formed(lift_plan(plan)[i])
    // lift_plan(plan)[i] == lift_construction_step(plan[i])
    assert forall|i: int|
        0 <= i < plan.len()
    implies
        step_well_formed(#[trigger] lift_plan::<RationalModel, R>(plan)[i])
    by {
        lemma_lifted_step_well_formed::<RationalModel, R>(plan[i]);
    }
}

// ===========================================================================
//  Phase 5b: Lifting preserves plan_locus_ordered
// ===========================================================================

/// Lifting a plan and constraints preserves plan_locus_ordered.
pub proof fn lemma_lift_plan_locus_ordered<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
    constraints: Seq<Constraint<F>>,
)
    requires
        plan_locus_ordered(plan, constraints),
    ensures
        plan_locus_ordered(
            lift_plan::<F, R>(plan),
            lift_constraints::<F, R>(constraints),
        ),
{
    let lp = lift_plan::<F, R>(plan);
    let lc = lift_constraints::<F, R>(constraints);

    assert forall|ci: int, si: int|
        #![trigger lp[si], lc[ci]]
        0 <= ci < lc.len() && 0 <= si < lp.len() &&
        constraint_entities(lc[ci]).contains(step_target(lp[si])) &&
        !constraint_locus_entities(lc[ci]).contains(step_target(lp[si]))
    implies (
        is_verification_constraint(lc[ci])
        || exists|si_loc: int|
            si < si_loc < lp.len() &&
            constraint_locus_entities(lc[ci]).contains(step_target(lp[si_loc]))
    )
    by {
        // Lifting preserves entities, locus_entities, step_target
        lemma_lift_constraint_entities::<F, R>(constraints[ci]);
        lemma_lift_constraint_locus_entities::<F, R>(constraints[ci]);
        lemma_lift_step_target::<F, R>(plan[si]);
        lemma_lift_is_verification_constraint::<F, R>(constraints[ci]);

        // Now the preconditions match the original plan_locus_ordered
        // constraint_entities(constraints[ci]).contains(step_target(plan[si]))
        // !constraint_locus_entities(constraints[ci]).contains(step_target(plan[si]))
        // So either is_verification_constraint(constraints[ci]) or exists si_loc

        if is_verification_constraint(constraints[ci]) {
            // is_verification_constraint is preserved
        } else {
            // Get witness from original
            let si_loc = choose|si_loc: int|
                si < si_loc < plan.len() &&
                constraint_locus_entities(constraints[ci]).contains(step_target(plan[si_loc]));
            // Show it works for lifted plan
            lemma_lift_step_target::<F, R>(plan[si_loc]);
            assert(si_loc < lp.len());
            assert(constraint_locus_entities(lc[ci]).contains(step_target(lp[si_loc])));
        }
    };
}

// ===========================================================================
//  Phase 5c: Independence soundness bridge
// ===========================================================================

/// In an independent circle plan, all constraint inputs to each circle step
/// are rational, so locus geometry lifts exactly to the extension field.
/// This is a specification-level statement of the key insight: the loci
/// computed at the extension level from lifted resolved points agree with
/// the loci computed from the base-field resolved points and then lifted.
///
/// Stated as: for circle step i and constraint ci referencing step_target(plan[i]),
/// the locus at the extension level equals the lifted base-field locus.
/// The proof requires: constraint inputs are rational, and qext_from_rational
/// preserves all arithmetic operations used in constraint_to_locus.
///
/// This lemma captures the *requirement* for extension field soundness.
/// The full proof (showing lifted locus equals extension locus) relies on
/// the correspondence lemma (lemma_lift_constraint_to_locus) which already
/// exists for each constraint variant.
pub proof fn lemma_independent_plan_locus_preservation<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
    constraints: Seq<Constraint<F>>,
)
    requires
        is_independent_circle_plan(plan, constraints),
    ensures
        // For every circle step, its target is not a circle target of any
        // other constraint's entities (besides itself). This ensures the
        // constraint geometry is computed from purely rational inputs.
        forall|i: int, ci: int|
            #![trigger plan[i], constraints[ci]]
            0 <= i < plan.len() && !is_rational_step(plan[i])
            && 0 <= ci < constraints.len()
            && constraint_entities(constraints[ci]).contains(step_target(plan[i]))
            ==> forall|e: EntityId|
                constraint_entities(constraints[ci]).contains(e) && e != step_target(plan[i])
                ==> !circle_targets(plan).contains(e),
{
    // Direct from the definition of is_independent_circle_plan
}

// ===========================================================================
//  Phase 6: Locus correspondence for rational-prefix steps
// ===========================================================================

/// Lift a resolved points map from F to SpecQuadExt<F, R>.
/// Each point is embedded coordinate-wise.
pub open spec fn lift_resolved_map<F: OrderedField, R: PositiveRadicand<F>>(
    resolved: ResolvedPoints<F>,
) -> ResolvedPoints<SpecQuadExt<F, R>> {
    Map::new(
        |id: EntityId| resolved.dom().contains(id),
        |id: EntityId| lift_point2::<F, R>(resolved[id]),
    )
}

/// Domain of lift_resolved_map equals domain of original.
pub proof fn lemma_lift_resolved_map_dom<F: OrderedField, R: PositiveRadicand<F>>(
    resolved: ResolvedPoints<F>,
)
    ensures
        lift_resolved_map::<F, R>(resolved).dom() == resolved.dom(),
{
    assert(lift_resolved_map::<F, R>(resolved).dom() =~= resolved.dom());
}

/// Lift a locus from F to SpecQuadExt<F, R>.
pub open spec fn lift_locus<F: OrderedField, R: PositiveRadicand<F>>(
    locus: Locus2d<F>,
) -> Locus2d<SpecQuadExt<F, R>> {
    match locus {
        Locus2d::FullPlane => Locus2d::FullPlane,
        Locus2d::OnLine(line) => Locus2d::OnLine(lift_line2(line)),
        Locus2d::OnCircle(circle) => Locus2d::OnCircle(lift_circle2(circle)),
        Locus2d::AtPoint(p) => Locus2d::AtPoint(lift_point2(p)),
    }
}

// ===========================================================================
//  Phase 6b: locus_eqv — equivalence of loci up to field eqv
// ===========================================================================

/// Two loci are equivalent if they have the same variant and their
/// geometric data is component-wise eqv.
pub open spec fn locus_eqv<T: OrderedField>(l1: Locus2d<T>, l2: Locus2d<T>) -> bool {
    match (l1, l2) {
        (Locus2d::FullPlane, Locus2d::FullPlane) => true,
        (Locus2d::OnLine(a), Locus2d::OnLine(b)) =>
            a.a.eqv(b.a) && a.b.eqv(b.b) && a.c.eqv(b.c),
        (Locus2d::OnCircle(a), Locus2d::OnCircle(b)) =>
            a.center.x.eqv(b.center.x) && a.center.y.eqv(b.center.y)
            && a.radius_sq.eqv(b.radius_sq),
        (Locus2d::AtPoint(a), Locus2d::AtPoint(b)) =>
            a.x.eqv(b.x) && a.y.eqv(b.y),
        _ => false,
    }
}

// ===========================================================================
//  Bridge: point_on_circle2 congruence + locus_eqv preserves satisfaction
// ===========================================================================

/// Transferring point_on_circle2 across eqv-equivalent circles.
proof fn lemma_point_on_circle2_congruence<T: OrderedField>(
    c1: Circle2<T>, c2: Circle2<T>, p: Point2<T>,
)
    requires
        point_on_circle2(c1, p),
        c1.center.x.eqv(c2.center.x),
        c1.center.y.eqv(c2.center.y),
        c1.radius_sq.eqv(c2.radius_sq),
    ensures
        point_on_circle2(c2, p),
{
    // point_on_circle2(c, p) = sq_dist_2d(p, c.center).eqv(c.radius_sq)
    // sq_dist_2d = norm_sq(sub2(p, center))
    // Step 1: sub2(p, c1.center) ≡ sub2(p, c2.center) as Vec2
    T::axiom_eqv_reflexive(p.x);
    T::axiom_eqv_reflexive(p.y);
    additive_group_lemmas::lemma_sub_congruence::<T>(p.x, p.x, c1.center.x, c2.center.x);
    additive_group_lemmas::lemma_sub_congruence::<T>(p.y, p.y, c1.center.y, c2.center.y);
    // Step 2: norm_sq congruence → sq_dist_2d congruence
    lemma_vec2_norm_sq_congruence::<T>(sub2(p, c1.center), sub2(p, c2.center));
    // Step 3: chain: sq_dist_2d(p,c2) ≡ sq_dist_2d(p,c1) ≡ c1.r² ≡ c2.r²
    T::axiom_eqv_symmetric(sq_dist_2d(p, c1.center), sq_dist_2d(p, c2.center));
    T::axiom_eqv_transitive(sq_dist_2d(p, c2.center), sq_dist_2d(p, c1.center), c1.radius_sq);
    T::axiom_eqv_transitive(sq_dist_2d(p, c2.center), c1.radius_sq, c2.radius_sq);
}

/// If two loci are eqv, point satisfaction transfers.
pub proof fn lemma_point_satisfies_locus_eqv<T: OrderedField>(
    l1: Locus2d<T>, l2: Locus2d<T>, p: Point2<T>,
)
    requires
        point_satisfies_locus(l1, p),
        locus_eqv(l1, l2),
    ensures
        point_satisfies_locus(l2, p),
{
    match (l1, l2) {
        (Locus2d::FullPlane, Locus2d::FullPlane) => {}
        (Locus2d::OnLine(a), Locus2d::OnLine(b)) => {
            verus_geometry::circle_circle_proofs::lemma_point_on_line2_congruence::<T>(a, b, p);
        }
        (Locus2d::OnCircle(a), Locus2d::OnCircle(b)) => {
            lemma_point_on_circle2_congruence::<T>(a, b, p);
        }
        (Locus2d::AtPoint(a), Locus2d::AtPoint(b)) => {
            T::axiom_eqv_transitive(p.x, a.x, b.x);
            T::axiom_eqv_transitive(p.y, a.y, b.y);
        }
        _ => {}
    }
}

/// locus_eqv is transitive.
pub proof fn lemma_locus_eqv_transitive<T: OrderedField>(
    l1: Locus2d<T>, l2: Locus2d<T>, l3: Locus2d<T>,
)
    requires locus_eqv(l1, l2), locus_eqv(l2, l3),
    ensures locus_eqv(l1, l3),
{
    match (l1, l2, l3) {
        (Locus2d::FullPlane, Locus2d::FullPlane, Locus2d::FullPlane) => {}
        (Locus2d::OnLine(a), Locus2d::OnLine(b), Locus2d::OnLine(c)) => {
            T::axiom_eqv_transitive(a.a, b.a, c.a);
            T::axiom_eqv_transitive(a.b, b.b, c.b);
            T::axiom_eqv_transitive(a.c, b.c, c.c);
        }
        (Locus2d::OnCircle(a), Locus2d::OnCircle(b), Locus2d::OnCircle(c)) => {
            T::axiom_eqv_transitive(a.center.x, b.center.x, c.center.x);
            T::axiom_eqv_transitive(a.center.y, b.center.y, c.center.y);
            T::axiom_eqv_transitive(a.radius_sq, b.radius_sq, c.radius_sq);
        }
        (Locus2d::AtPoint(a), Locus2d::AtPoint(b), Locus2d::AtPoint(c)) => {
            T::axiom_eqv_transitive(a.x, b.x, c.x);
            T::axiom_eqv_transitive(a.y, b.y, c.y);
        }
        _ => {}
    }
}

/// locus_eqv is symmetric.
pub proof fn lemma_locus_eqv_symmetric<T: OrderedField>(
    l1: Locus2d<T>, l2: Locus2d<T>,
)
    requires locus_eqv(l1, l2),
    ensures locus_eqv(l2, l1),
{
    match (l1, l2) {
        (Locus2d::FullPlane, Locus2d::FullPlane) => {}
        (Locus2d::OnLine(a), Locus2d::OnLine(b)) => {
            T::axiom_eqv_symmetric(a.a, b.a);
            T::axiom_eqv_symmetric(a.b, b.b);
            T::axiom_eqv_symmetric(a.c, b.c);
        }
        (Locus2d::OnCircle(a), Locus2d::OnCircle(b)) => {
            T::axiom_eqv_symmetric(a.center.x, b.center.x);
            T::axiom_eqv_symmetric(a.center.y, b.center.y);
            T::axiom_eqv_symmetric(a.radius_sq, b.radius_sq);
        }
        (Locus2d::AtPoint(a), Locus2d::AtPoint(b)) => {
            T::axiom_eqv_symmetric(a.x, b.x);
            T::axiom_eqv_symmetric(a.y, b.y);
        }
        _ => {}
    }
}

/// lift_locus preserves locus_eqv: if l1 ≈ l2 then lift(l1) ≈ lift(l2).
pub proof fn lemma_lift_locus_preserves_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    l1: Locus2d<F>, l2: Locus2d<F>,
)
    requires locus_eqv(l1, l2),
    ensures locus_eqv(
        lift_locus::<F, R>(l1),
        lift_locus::<F, R>(l2)),
{
    match (l1, l2) {
        (Locus2d::FullPlane, Locus2d::FullPlane) => {}
        (Locus2d::OnLine(a), Locus2d::OnLine(b)) => {
            lemma_rational_congruence::<F, R>(a.a, b.a);
            lemma_rational_congruence::<F, R>(a.b, b.b);
            lemma_rational_congruence::<F, R>(a.c, b.c);
        }
        (Locus2d::OnCircle(a), Locus2d::OnCircle(b)) => {
            lemma_rational_congruence::<F, R>(a.center.x, b.center.x);
            lemma_rational_congruence::<F, R>(a.center.y, b.center.y);
            lemma_rational_congruence::<F, R>(a.radius_sq, b.radius_sq);
        }
        (Locus2d::AtPoint(a), Locus2d::AtPoint(b)) => {
            lemma_rational_congruence::<F, R>(a.x, b.x);
            lemma_rational_congruence::<F, R>(a.y, b.y);
        }
        _ => {}
    }
}

/// Point congruence for locus satisfaction: if p ≡ q and p satisfies locus,
/// then q satisfies locus.
pub proof fn lemma_point_satisfies_locus_congruent<T: OrderedField>(
    locus: Locus2d<T>, p: Point2<T>, q: Point2<T>,
)
    requires
        point_satisfies_locus(locus, p),
        p.eqv(q),
    ensures
        point_satisfies_locus(locus, q),
{
    match locus {
        Locus2d::FullPlane => {}
        Locus2d::OnLine(line) => {
            // point_on_line2(line, p) = a*px + b*py + c ≡ 0
            // Need: a*qx + b*qy + c ≡ 0
            // p ≡ q means px ≡ qx, py ≡ qy
            T::axiom_eqv_reflexive(line.a);
            T::axiom_eqv_reflexive(line.b);
            T::axiom_eqv_reflexive(line.c);
            ring_lemmas::lemma_mul_congruence::<T>(line.a, line.a, p.x, q.x);
            ring_lemmas::lemma_mul_congruence::<T>(line.b, line.b, p.y, q.y);
            additive_group_lemmas::lemma_add_congruence::<T>(
                line.a.mul(p.x), line.a.mul(q.x),
                line.b.mul(p.y), line.b.mul(q.y),
            );
            additive_group_lemmas::lemma_add_congruence::<T>(
                line.a.mul(p.x).add(line.b.mul(p.y)),
                line.a.mul(q.x).add(line.b.mul(q.y)),
                line.c, line.c,
            );
            // chain: a*qx + b*qy + c ≡ a*px + b*py + c ≡ 0
            T::axiom_eqv_symmetric(
                line.a.mul(p.x).add(line.b.mul(p.y)).add(line.c),
                line.a.mul(q.x).add(line.b.mul(q.y)).add(line.c),
            );
            T::axiom_eqv_transitive(
                line.a.mul(q.x).add(line.b.mul(q.y)).add(line.c),
                line.a.mul(p.x).add(line.b.mul(p.y)).add(line.c),
                T::zero(),
            );
        }
        Locus2d::OnCircle(circle) => {
            // point_on_circle2 = sq_dist_2d(p, center) ≡ radius_sq
            // Need: sq_dist_2d(q, center) ≡ radius_sq
            // sub2(q, center) ≡ sub2(p, center) componentwise? No...
            // sub2(q, center).x = q.x - center.x
            // sub2(p, center).x = p.x - center.x
            // q.x ≡ p.x → q.x - center.x ≡ p.x - center.x
            T::axiom_eqv_symmetric(p.x, q.x);
            T::axiom_eqv_symmetric(p.y, q.y);
            T::axiom_eqv_reflexive(circle.center.x);
            T::axiom_eqv_reflexive(circle.center.y);
            additive_group_lemmas::lemma_sub_congruence::<T>(
                q.x, p.x, circle.center.x, circle.center.x);
            additive_group_lemmas::lemma_sub_congruence::<T>(
                q.y, p.y, circle.center.y, circle.center.y);
            // sub2(q, center) ≡ sub2(p, center)
            lemma_vec2_norm_sq_congruence::<T>(
                sub2(q, circle.center), sub2(p, circle.center));
            // norm_sq(sub2(q,center)) ≡ norm_sq(sub2(p,center)) = sq_dist
            // sq_dist(q,center) ≡ sq_dist(p,center) ≡ radius_sq
            T::axiom_eqv_transitive(
                sq_dist_2d(q, circle.center),
                sq_dist_2d(p, circle.center),
                circle.radius_sq,
            );
        }
        Locus2d::AtPoint(r) => {
            // p ≡ r, p ≡ q, need q ≡ r
            T::axiom_eqv_symmetric(p.x, q.x);
            T::axiom_eqv_symmetric(p.y, q.y);
            T::axiom_eqv_transitive(q.x, p.x, r.x);
            T::axiom_eqv_transitive(q.y, p.y, r.y);
        }
    }
}

// ===========================================================================
//  Lifting helpers: field ops commute with qext_from_rational (up to eqv)
// ===========================================================================

/// qext_from_rational(v.neg()) ≡ qext_from_rational(v).neg()
/// No precondition needed — uses lemma_neg_zero for the im component.
proof fn lemma_qext_from_rational_neg_eqv<F: OrderedField, R: PositiveRadicand<F>>(v: F)
    ensures
        qext_from_rational::<F, R>(v.neg()).eqv(qext_from_rational::<F, R>(v).neg()),
{
    // LHS = qext(v.neg(), 0), RHS = qext(v.neg(), 0.neg())
    F::axiom_eqv_reflexive(v.neg());
    additive_group_lemmas::lemma_neg_zero::<F>();
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
}

/// sub2(lift_point2(p), lift_point2(q)) components ≡ qext(sub2(p, q) components).
proof fn lemma_lift_sub2_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    p: Point2<F>, q: Point2<F>,
)
    ensures
        sub2(lift_point2::<F, R>(p), lift_point2::<F, R>(q)).x.eqv(
            qext_from_rational::<F, R>(sub2(p, q).x)),
        sub2(lift_point2::<F, R>(p), lift_point2::<F, R>(q)).y.eqv(
            qext_from_rational::<F, R>(sub2(p, q).y)),
{
    // sub2(lp, lq).x = qext(p.x) - qext(q.x)
    // qext(sub2(p,q).x) = qext(p.x - q.x)
    // lemma_rational_sub: qext(a-b) ≡ qext(a)-qext(b), symmetric gives what we need
    lemma_rational_sub::<F, R>(p.x, q.x);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(p.x.sub(q.x)),
        qext_from_rational::<F, R>(p.x).sub(qext_from_rational::<F, R>(q.x)),
    );
    lemma_rational_sub::<F, R>(p.y, q.y);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(p.y.sub(q.y)),
        qext_from_rational::<F, R>(p.y).sub(qext_from_rational::<F, R>(q.y)),
    );
}

/// line2_from_points(lift_point2(p), lift_point2(q)) has coefficients
/// eqv to lift_line2(line2_from_points(p, q)).
proof fn lemma_lift_line2_from_points_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    p: Point2<F>, q: Point2<F>,
)
    ensures ({
        let l1 = line2_from_points(lift_point2::<F, R>(p), lift_point2::<F, R>(q));
        let l2 = lift_line2::<F, R>(line2_from_points(p, q));
        l1.a.eqv(l2.a) && l1.b.eqv(l2.b) && l1.c.eqv(l2.c)
    }),
{
    // Abbreviations:
    // a_base = (q.y - p.y).neg(), b_base = q.x - p.x
    // a_r = qext(a_base), b_r = qext(b_base)   [from lift_line2]
    // a_l = (qext(q.y) - qext(p.y)).neg()       [from line2_from_points at lifted level]
    // b_l = qext(q.x) - qext(p.x)
    let a_base = q.y.sub(p.y).neg();
    let b_base = q.x.sub(p.x);

    // === a coefficient: a_l ≡ a_r ===
    // Step 1: qext(q.y-p.y) ≡ qext(q.y)-qext(p.y) → neg both → qext(q.y-p.y).neg() ≡ a_l
    lemma_rational_sub::<F, R>(q.y, p.y);
    SpecQuadExt::<F, R>::axiom_neg_congruence(
        qext_from_rational::<F, R>(q.y.sub(p.y)),
        qext_from_rational::<F, R>(q.y).sub(qext_from_rational::<F, R>(p.y)),
    );
    // Step 2: qext(v.neg()) ≡ qext(v).neg() where v = q.y-p.y
    lemma_qext_from_rational_neg_eqv::<F, R>(q.y.sub(p.y));
    // Chain: a_r = qext(v.neg()) ≡ qext(v).neg() ≡ (qext(q.y)-qext(p.y)).neg() = a_l
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(a_base),
        qext_from_rational::<F, R>(q.y.sub(p.y)).neg(),
        qext_from_rational::<F, R>(q.y).sub(qext_from_rational::<F, R>(p.y)).neg(),
    );
    // Symmetric for ensures direction: l1.a.eqv(l2.a) i.e. a_l.eqv(a_r)
    let lp = lift_point2::<F, R>(p);
    let lq = lift_point2::<F, R>(q);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a_base),
        lq.y.sub(lp.y).neg(),
    );

    // === b coefficient: b_l ≡ b_r ===
    lemma_rational_sub::<F, R>(q.x, p.x);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(b_base),
        qext_from_rational::<F, R>(q.x).sub(qext_from_rational::<F, R>(p.x)),
    );

    // === c coefficient ===
    // c_l = (a_l*qext(p.x) + b_l*qext(p.y)).neg()
    // c_r = qext((a_base*p.x + b_base*p.y).neg())
    let a_l = lq.y.sub(lp.y).neg();
    let b_l = lq.x.sub(lp.x);
    let a_r = qext_from_rational::<F, R>(a_base);
    let b_r = qext_from_rational::<F, R>(b_base);
    let px = qext_from_rational::<F, R>(p.x);
    let py = qext_from_rational::<F, R>(p.y);

    // a_r ≡ a_l (proved above), need a_r*px ≡ a_l*px
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(px);
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(a_r, a_l, px, px);
    // b_r ≡ b_l (proved above, via symmetric of symmetric = original direction)
    // We have b_l.eqv(b_r) from the b section. Need b_r.eqv(b_l) for mul_congruence.
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(b_l, b_r);
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(py);
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(b_r, b_l, py, py);

    // qext(a_base*p.x) ≡ a_r*px by lemma_rational_mul
    lemma_rational_mul::<F, R>(a_base, p.x);
    lemma_rational_mul::<F, R>(b_base, p.y);
    // qext(a_base*p.x + b_base*p.y) ≡ qext(a_base*p.x) + qext(b_base*p.y)
    lemma_rational_add::<F, R>(a_base.mul(p.x), b_base.mul(p.y));

    // Chain: qext(sum) ≡ qext(a_base*p.x)+qext(b_base*p.y) ≡ a_r*px+b_r*py ≡ a_l*px+b_l*py
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(a_base.mul(p.x)), a_r.mul(px),
        qext_from_rational::<F, R>(b_base.mul(p.y)), b_r.mul(py),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(a_base.mul(p.x).add(b_base.mul(p.y))),
        qext_from_rational::<F, R>(a_base.mul(p.x)).add(qext_from_rational::<F, R>(b_base.mul(p.y))),
        a_r.mul(px).add(b_r.mul(py)),
    );
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        a_r.mul(px), a_l.mul(px),
        b_r.mul(py), b_l.mul(py),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(a_base.mul(p.x).add(b_base.mul(p.y))),
        a_r.mul(px).add(b_r.mul(py)),
        a_l.mul(px).add(b_l.mul(py)),
    );

    // Neg: qext(sum.neg()) ≡ qext(sum).neg() ≡ (a_l*px+b_l*py).neg()
    lemma_qext_from_rational_neg_eqv::<F, R>(a_base.mul(p.x).add(b_base.mul(p.y)));
    SpecQuadExt::<F, R>::axiom_neg_congruence(
        qext_from_rational::<F, R>(a_base.mul(p.x).add(b_base.mul(p.y))),
        a_l.mul(px).add(b_l.mul(py)),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(a_base.mul(p.x).add(b_base.mul(p.y)).neg()),
        qext_from_rational::<F, R>(a_base.mul(p.x).add(b_base.mul(p.y))).neg(),
        a_l.mul(px).add(b_l.mul(py)).neg(),
    );
    // Symmetric for ensures: c_l.eqv(c_r)
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a_base.mul(p.x).add(b_base.mul(p.y)).neg()),
        a_l.mul(px).add(b_l.mul(py)).neg(),
    );
}

/// sq_dist_2d(lift_point2(p), lift_point2(q)) ≡ qext(sq_dist_2d(p, q)).
proof fn lemma_lift_sq_dist_2d_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    p: Point2<F>, q: Point2<F>,
)
    ensures
        sq_dist_2d(lift_point2::<F, R>(p), lift_point2::<F, R>(q)).eqv(
            qext_from_rational::<F, R>(sq_dist_2d(p, q))),
{
    // sq_dist_2d = norm_sq(sub2(p,q)) = (p.x-q.x)²+(p.y-q.y)²
    // LHS components: dx_l = qext(p.x)-qext(q.x), dy_l = qext(p.y)-qext(q.y)
    // RHS: qext(dx²+dy²) where dx = p.x-q.x, dy = p.y-q.y

    let dx = p.x.sub(q.x);
    let dy = p.y.sub(q.y);

    // dx_l ≡ qext(dx), dy_l ≡ qext(dy) [from lemma_lift_sub2_eqv]
    lemma_lift_sub2_eqv::<F, R>(p, q);
    let lp = lift_point2::<F, R>(p);
    let lq = lift_point2::<F, R>(q);
    let dx_l = sub2(lp, lq).x;
    let dy_l = sub2(lp, lq).y;
    let dx_r = qext_from_rational::<F, R>(dx);
    let dy_r = qext_from_rational::<F, R>(dy);

    // dx_l² ≡ dx_r² = qext(dx)² ≡ qext(dx²)
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(dx_l, dx_r, dx_l, dx_r);
    lemma_rational_mul::<F, R>(dx, dx);
    // lemma_rational_mul gives qext(dx²).eqv(dx_r²), need dx_r².eqv(qext(dx²))
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(dx.mul(dx)), dx_r.mul(dx_r),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        dx_l.mul(dx_l), dx_r.mul(dx_r), qext_from_rational::<F, R>(dx.mul(dx)),
    );

    // dy_l² ≡ qext(dy²) (same pattern)
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(dy_l, dy_r, dy_l, dy_r);
    lemma_rational_mul::<F, R>(dy, dy);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(dy.mul(dy)), dy_r.mul(dy_r),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        dy_l.mul(dy_l), dy_r.mul(dy_r), qext_from_rational::<F, R>(dy.mul(dy)),
    );

    // dx_l²+dy_l² ≡ qext(dx²)+qext(dy²) ≡ qext(dx²+dy²)
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        dx_l.mul(dx_l), qext_from_rational::<F, R>(dx.mul(dx)),
        dy_l.mul(dy_l), qext_from_rational::<F, R>(dy.mul(dy)),
    );
    lemma_rational_add::<F, R>(dx.mul(dx), dy.mul(dy));
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(dx.mul(dx).add(dy.mul(dy))),
        qext_from_rational::<F, R>(dx.mul(dx)).add(qext_from_rational::<F, R>(dy.mul(dy))),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        dx_l.mul(dx_l).add(dy_l.mul(dy_l)),
        qext_from_rational::<F, R>(dx.mul(dx)).add(qext_from_rational::<F, R>(dy.mul(dy))),
        qext_from_rational::<F, R>(dx.mul(dx).add(dy.mul(dy))),
    );
}

/// Helper for Perpendicular/Parallel: prove the c coefficient of a line built
/// from sub2 components. Given db = sub2(b2, b1), other = resolved[a2]:
/// (db_l.x * qext(other.x) + db_l.y * qext(other.y)).neg() ≡
/// qext((db.x * other.x + db.y * other.y).neg())
proof fn lemma_lift_dot_neg_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    dbx: F, dby: F, ox: F, oy: F,
    dbx_l: SpecQuadExt<F, R>, dby_l: SpecQuadExt<F, R>,
)
    requires
        dbx_l.eqv(qext_from_rational::<F, R>(dbx)),
        dby_l.eqv(qext_from_rational::<F, R>(dby)),
    ensures
        dbx_l.mul(qext_from_rational::<F, R>(ox))
            .add(dby_l.mul(qext_from_rational::<F, R>(oy))).neg()
            .eqv(qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy)).neg())),
{
    let qox = qext_from_rational::<F, R>(ox);
    let qoy = qext_from_rational::<F, R>(oy);
    let qdbx = qext_from_rational::<F, R>(dbx);
    let qdby = qext_from_rational::<F, R>(dby);

    // dbx_l*qox ≡ qdbx*qox ≡ qext(dbx*ox)
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(qox);
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(dbx_l, qdbx, qox, qox);
    lemma_rational_mul::<F, R>(dbx, ox);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(dbx.mul(ox)), qdbx.mul(qox),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        dbx_l.mul(qox), qdbx.mul(qox), qext_from_rational::<F, R>(dbx.mul(ox)),
    );

    // dby_l*qoy ≡ qext(dby*oy)
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(qoy);
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(dby_l, qdby, qoy, qoy);
    lemma_rational_mul::<F, R>(dby, oy);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(dby.mul(oy)), qdby.mul(qoy),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        dby_l.mul(qoy), qdby.mul(qoy), qext_from_rational::<F, R>(dby.mul(oy)),
    );

    // sum ≡ qext(dbx*ox) + qext(dby*oy) ≡ qext(sum_base)
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        dbx_l.mul(qox), qext_from_rational::<F, R>(dbx.mul(ox)),
        dby_l.mul(qoy), qext_from_rational::<F, R>(dby.mul(oy)),
    );
    lemma_rational_add::<F, R>(dbx.mul(ox), dby.mul(oy));
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy))),
        qext_from_rational::<F, R>(dbx.mul(ox)).add(qext_from_rational::<F, R>(dby.mul(oy))),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        dbx_l.mul(qox).add(dby_l.mul(qoy)),
        qext_from_rational::<F, R>(dbx.mul(ox)).add(qext_from_rational::<F, R>(dby.mul(oy))),
        qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy))),
    );

    // neg: sum.neg() ≡ qext(sum_base).neg() ≡ qext(sum_base.neg())
    SpecQuadExt::<F, R>::axiom_neg_congruence(
        dbx_l.mul(qox).add(dby_l.mul(qoy)),
        qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy))),
    );
    lemma_qext_from_rational_neg_eqv::<F, R>(dbx.mul(ox).add(dby.mul(oy)));
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy)).neg()),
        qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy))).neg(),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        dbx_l.mul(qox).add(dby_l.mul(qoy)).neg(),
        qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy))).neg(),
        qext_from_rational::<F, R>(dbx.mul(ox).add(dby.mul(oy)).neg()),
    );
}

/// In an OrderedField, 1+1 ≢ 0.
proof fn lemma_two_ne_zero<F: OrderedField>()
    ensures
        !F::one().add(F::one()).eqv(F::zero()),
{
    // 0 < 1
    ordered_ring_lemmas::lemma_zero_lt_one::<F>();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), F::one());
    // 0.le(1) follows from 0.lt(1)
    // 0+1 ≤ 1+1
    F::axiom_le_add_monotone(F::zero(), F::one(), F::one());
    // 0+1 ≡ 1
    additive_group_lemmas::lemma_add_zero_left::<F>(F::one());
    // 1 ≤ 1+1
    ordered_ring_lemmas::lemma_le_congruence_left::<F>(
        F::zero().add(F::one()), F::one(), F::one().add(F::one()),
    );
    // 0 < 1 and 1 ≤ 2 → 0 < 2
    ordered_ring_lemmas::lemma_lt_le_transitive::<F>(
        F::zero(), F::one(), F::one().add(F::one()),
    );
    // 0 < 2 → !0.eqv(2)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), F::one().add(F::one()));
    // !2.eqv(0) by contradiction with eqv symmetry
    if F::one().add(F::one()).eqv(F::zero()) {
        F::axiom_eqv_symmetric(F::one().add(F::one()), F::zero());
    }
}

/// qext(one+one) ≡ QE::one()+QE::one()
proof fn lemma_lift_two_eqv<F: OrderedField, R: PositiveRadicand<F>>()
    ensures
        qext_from_rational::<F, R>(F::one().add(F::one())).eqv(
            SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one())
        ),
{
    lemma_rational_one::<F, R>();
    // qext(1) ≡ QE::one()
    // qext(1+1) ≡ qext(1)+qext(1) by rational_add
    lemma_rational_add::<F, R>(F::one(), F::one());
    // qext(1)+qext(1) ≡ QE::one()+QE::one() by add_congruence
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(F::one()), SpecQuadExt::<F, R>::one(),
        qext_from_rational::<F, R>(F::one()), SpecQuadExt::<F, R>::one(),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(F::one().add(F::one())),
        qext_from_rational::<F, R>(F::one()).add(qext_from_rational::<F, R>(F::one())),
        SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one()),
    );
}

/// Lift the pattern 2*a - b: two_QE * qext(a) - qext(b) ≡ qext(two_F * a - b)
proof fn lemma_lift_two_mul_sub_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    a: F, b: F,
)
    ensures ({
        let two_f = F::one().add(F::one());
        let two_qe = SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one());
        two_qe.mul(qext_from_rational::<F, R>(a)).sub(qext_from_rational::<F, R>(b)).eqv(
            qext_from_rational::<F, R>(two_f.mul(a).sub(b))
        )
    }),
{
    let two_f = F::one().add(F::one());
    let two_qe = SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one());
    let qa = qext_from_rational::<F, R>(a);
    let qb = qext_from_rational::<F, R>(b);

    // qext(two_F) ≡ two_QE
    lemma_lift_two_eqv::<F, R>();

    // qext(two_F * a) ≡ qext(two_F) * qext(a)
    lemma_rational_mul::<F, R>(two_f, a);
    // qext(two_F) * qext(a) ≡ two_QE * qext(a) by mul_congruence
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(qa);
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(two_f), two_qe,
        qa, qa,
    );
    // Chain: qext(two_F*a) ≡ two_QE * qext(a)
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(two_f.mul(a)),
        qext_from_rational::<F, R>(two_f).mul(qa),
        two_qe.mul(qa),
    );
    // Symmetric: two_QE * qext(a) ≡ qext(two_F*a)
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(two_f.mul(a)), two_qe.mul(qa),
    );

    // qext(two_F*a - b) ≡ qext(two_F*a) - qext(b)
    lemma_rational_sub::<F, R>(two_f.mul(a), b);

    // two_QE*qext(a) - qext(b) ≡ qext(two_F*a) - qext(b) by sub_congruence
    SpecQuadExt::<F, R>::axiom_eqv_reflexive(qb);
    additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
        two_qe.mul(qa), qext_from_rational::<F, R>(two_f.mul(a)),
        qb, qb,
    );

    // qext(two_F*a) - qext(b) ≡ qext(two_F*a - b) (symmetric of rational_sub)
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(two_f.mul(a).sub(b)),
        qext_from_rational::<F, R>(two_f.mul(a)).sub(qb),
    );

    // Chain: two_QE*qext(a) - qext(b) ≡ qext(two_F*a) - qext(b) ≡ qext(two_F*a-b)
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        two_qe.mul(qa).sub(qb),
        qext_from_rational::<F, R>(two_f.mul(a)).sub(qb),
        qext_from_rational::<F, R>(two_f.mul(a).sub(b)),
    );
}

/// Lift the pattern (a+b)/2: (qext(a)+qext(b)).div(two_QE) ≡ qext((a+b).div(two_F))
proof fn lemma_lift_add_div_two_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    a: F, b: F,
)
    ensures ({
        let two_f = F::one().add(F::one());
        let two_qe = SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one());
        qext_from_rational::<F, R>(a).add(qext_from_rational::<F, R>(b))
            .div(two_qe).eqv(
                qext_from_rational::<F, R>(a.add(b).div(two_f))
            )
    }),
{
    let two_f = F::one().add(F::one());
    let two_qe = SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one());
    let qa = qext_from_rational::<F, R>(a);
    let qb = qext_from_rational::<F, R>(b);
    let qtwo = qext_from_rational::<F, R>(two_f);

    // !two_F.eqv(F::zero())
    lemma_two_ne_zero::<F>();

    // qext(two_F) ≡ two_QE
    lemma_lift_two_eqv::<F, R>();

    // !qtwo.eqv(QE::zero()) via injectivity
    if qtwo.eqv(SpecQuadExt::<F, R>::zero()) {
        lemma_qext_from_rational_injective::<F, R>(two_f, F::zero());
    }

    // qext(a+b) ≡ qext(a) + qext(b)
    lemma_rational_add::<F, R>(a, b);

    // qext((a+b)/two_F) ≡ qext(a+b) / qext(two_F)
    lemma_rational_div::<F, R>(a.add(b), two_f);

    // div_congruence: qext(a+b)/qext(two_F) ≡ (qa+qb)/two_QE
    // needs: qext(a+b) ≡ qa+qb, qext(two_F) ≡ two_QE, !qext(two_F).eqv(zero)
    lemma_div_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(a.add(b)),
        qa.add(qb),
        qtwo,
        two_qe,
    );

    // Chain: qext((a+b)/two_F) ≡ qext(a+b)/qext(two_F) ≡ (qa+qb)/two_QE
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        qext_from_rational::<F, R>(a.add(b).div(two_f)),
        qext_from_rational::<F, R>(a.add(b)).div(qtwo),
        qa.add(qb).div(two_qe),
    );

    // Symmetric: (qa+qb)/two_QE ≡ qext((a+b)/two_F)
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a.add(b).div(two_f)),
        qa.add(qb).div(two_qe),
    );
}

/// In an ordered field, a² + b² ≡ 0 implies a ≡ 0 and b ≡ 0.
proof fn lemma_sum_of_squares_zero<F: OrderedField>(a: F, b: F)
    requires
        a.mul(a).add(b.mul(b)).eqv(F::zero()),
    ensures
        a.eqv(F::zero()),
        b.eqv(F::zero()),
{
    // a² ≥ 0 and b² ≥ 0
    ordered_ring_lemmas::lemma_square_nonneg::<F>(a);
    ordered_ring_lemmas::lemma_square_nonneg::<F>(b);
    let aa = a.mul(a);
    let bb = b.mul(b);
    // From b² ≥ 0: 0 + a² ≤ b² + a²
    F::axiom_le_add_monotone(F::zero(), bb, aa);
    // 0 + a² ≡ a²
    additive_group_lemmas::lemma_add_zero_left::<F>(aa);
    // b² + a² ≡ a² + b² ≡ 0
    F::axiom_add_commutative(bb, aa);
    F::axiom_eqv_transitive(bb.add(aa), aa.add(bb), F::zero());
    // So a² ≤ 0
    F::axiom_le_congruence(F::zero().add(aa), aa, bb.add(aa), F::zero());
    // a² ≡ 0
    F::axiom_le_antisymmetric(aa, F::zero());
    // a ≡ 0
    lemma_square_zero::<F>(a);
    // Similarly: from a² ≥ 0: 0 + b² ≤ a² + b²
    F::axiom_le_add_monotone(F::zero(), aa, bb);
    additive_group_lemmas::lemma_add_zero_left::<F>(bb);
    // a² + b² ≡ 0 already given
    F::axiom_le_congruence(F::zero().add(bb), bb, aa.add(bb), F::zero());
    F::axiom_le_antisymmetric(bb, F::zero());
    lemma_square_zero::<F>(b);
}

/// Lifting a 2D dot product: given component-wise eqv,
/// ax_l*bx_l + ay_l*by_l ≡ qext(ax*bx + ay*by_f).
proof fn lemma_lift_dot2_eqv<F: Field, R: Radicand<F>>(
    ax: F, ay: F, bx: F, by_f: F,
    ax_l: SpecQuadExt<F, R>, ay_l: SpecQuadExt<F, R>,
    bx_l: SpecQuadExt<F, R>, by_l: SpecQuadExt<F, R>,
)
    requires
        ax_l.eqv(qext_from_rational::<F, R>(ax)),
        ay_l.eqv(qext_from_rational::<F, R>(ay)),
        bx_l.eqv(qext_from_rational::<F, R>(bx)),
        by_l.eqv(qext_from_rational::<F, R>(by_f)),
    ensures
        ax_l.mul(bx_l).add(ay_l.mul(by_l)).eqv(
            qext_from_rational::<F, R>(ax.mul(bx).add(ay.mul(by_f)))),
{
    // ax_l * bx_l ≡ qext(ax) * qext(bx)
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
        ax_l, qext_from_rational::<F, R>(ax), bx_l, qext_from_rational::<F, R>(bx));
    // qext(ax*bx) ≡ qext(ax)*qext(bx), flip to get qext(ax)*qext(bx) ≡ qext(ax*bx)
    lemma_rational_mul::<F, R>(ax, bx);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(ax.mul(bx)),
        qext_from_rational::<F, R>(ax).mul(qext_from_rational::<F, R>(bx)));
    // Transitive: ax_l*bx_l ≡ qext(ax)*qext(bx) ≡ qext(ax*bx)
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        ax_l.mul(bx_l),
        qext_from_rational::<F, R>(ax).mul(qext_from_rational::<F, R>(bx)),
        qext_from_rational::<F, R>(ax.mul(bx)));
    // ay_l * by_l ≡ qext(ay*by_f) — same pattern
    ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
        ay_l, qext_from_rational::<F, R>(ay), by_l, qext_from_rational::<F, R>(by_f));
    lemma_rational_mul::<F, R>(ay, by_f);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(ay.mul(by_f)),
        qext_from_rational::<F, R>(ay).mul(qext_from_rational::<F, R>(by_f)));
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        ay_l.mul(by_l),
        qext_from_rational::<F, R>(ay).mul(qext_from_rational::<F, R>(by_f)),
        qext_from_rational::<F, R>(ay.mul(by_f)));
    // Sum: ≡ qext(ax*bx) + qext(ay*by_f)
    additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
        ax_l.mul(bx_l), qext_from_rational::<F, R>(ax.mul(bx)),
        ay_l.mul(by_l), qext_from_rational::<F, R>(ay.mul(by_f)));
    // qext(ax*bx) + qext(ay*by_f) ≡ qext(ax*bx + ay*by_f)
    lemma_rational_add::<F, R>(ax.mul(bx), ay.mul(by_f));
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(ax.mul(bx).add(ay.mul(by_f))),
        qext_from_rational::<F, R>(ax.mul(bx)).add(qext_from_rational::<F, R>(ay.mul(by_f))));
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        ax_l.mul(bx_l).add(ay_l.mul(by_l)),
        qext_from_rational::<F, R>(ax.mul(bx)).add(qext_from_rational::<F, R>(ay.mul(by_f))),
        qext_from_rational::<F, R>(ax.mul(bx).add(ay.mul(by_f))));
}

/// Reflect-point lifting: reflect at lifted level ≡ lift(reflect at base level).
proof fn lemma_lift_reflect_point_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    p: Point2<F>, la: Point2<F>, lb: Point2<F>,
)
    ensures
        reflect_point_across_line(
            lift_point2::<F, R>(p), lift_point2::<F, R>(la), lift_point2::<F, R>(lb),
        ).x.eqv(qext_from_rational::<F, R>(
            reflect_point_across_line(p, la, lb).x)),
        reflect_point_across_line(
            lift_point2::<F, R>(p), lift_point2::<F, R>(la), lift_point2::<F, R>(lb),
        ).y.eqv(qext_from_rational::<F, R>(
            reflect_point_across_line(p, la, lb).y)),
{
    // Base-level intermediates
    let d = sub2(lb, la);
    let pa = sub2(p, la);
    let dot_dd = d.x.mul(d.x).add(d.y.mul(d.y));
    let dot_pad = pa.x.mul(d.x).add(pa.y.mul(d.y));
    let t = dot_pad.div(dot_dd);
    let two = F::one().add(F::one());
    let proj_x = la.x.add(t.mul(d.x));
    let proj_y = la.y.add(t.mul(d.y));
    // Lifted-level intermediates
    let lp = lift_point2::<F, R>(p);
    let lla = lift_point2::<F, R>(la);
    let llb = lift_point2::<F, R>(lb);
    let d_l = sub2(llb, lla);
    let pa_l = sub2(lp, lla);
    let dot_dd_l = d_l.x.mul(d_l.x).add(d_l.y.mul(d_l.y));
    let dot_pad_l = pa_l.x.mul(d_l.x).add(pa_l.y.mul(d_l.y));
    let t_l = dot_pad_l.div(dot_dd_l);
    let two_l = SpecQuadExt::<F, R>::one().add(SpecQuadExt::<F, R>::one());
    let proj_x_l = lla.x.add(t_l.mul(d_l.x));
    let proj_y_l = lla.y.add(t_l.mul(d_l.y));

    // Step 1: d_l components ≡ qext(d components)
    lemma_lift_sub2_eqv::<F, R>(lb, la);

    // Step 2: pa_l components ≡ qext(pa components)
    lemma_lift_sub2_eqv::<F, R>(p, la);

    // Step 3: dot_dd_l ≡ qext(dot_dd)
    lemma_lift_dot2_eqv::<F, R>(d.x, d.y, d.x, d.y, d_l.x, d_l.y, d_l.x, d_l.y);

    // Step 4: dot_pad_l ≡ qext(dot_pad)
    lemma_lift_dot2_eqv::<F, R>(pa.x, pa.y, d.x, d.y, pa_l.x, pa_l.y, d_l.x, d_l.y);

    // Step 5: two_l ≡ qext(two)
    lemma_lift_two_eqv::<F, R>();

    // Case split on dot_dd
    ordered_ring_lemmas::lemma_trichotomy::<F>(dot_dd, F::zero());
    if dot_dd.eqv(F::zero()) {
        // === DEGENERATE CASE: dot_dd ≡ 0, so d.x ≡ 0 and d.y ≡ 0 ===
        lemma_sum_of_squares_zero::<F>(d.x, d.y);

        // d_l.x ≡ qext(0) = QE::zero()
        lemma_rational_congruence::<F, R>(d.x, F::zero());
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            d_l.x, qext_from_rational::<F, R>(d.x), qext_from_rational::<F, R>(F::zero()));

        // d_l.y ≡ QE::zero()
        lemma_rational_congruence::<F, R>(d.y, F::zero());
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            d_l.y, qext_from_rational::<F, R>(d.y), qext_from_rational::<F, R>(F::zero()));

        // --- Base level: t*d.x ≡ 0, proj_x ≡ la.x ---
        ring_lemmas::lemma_mul_congruence_right::<F>(t, d.x, F::zero());
        F::axiom_mul_zero_right(t);
        F::axiom_eqv_transitive(t.mul(d.x), t.mul(F::zero()), F::zero());
        additive_group_lemmas::lemma_add_congruence_right::<F>(la.x, t.mul(d.x), F::zero());
        F::axiom_add_zero_right(la.x);
        F::axiom_eqv_transitive(proj_x, la.x.add(F::zero()), la.x);

        // t*d.y ≡ 0, proj_y ≡ la.y
        ring_lemmas::lemma_mul_congruence_right::<F>(t, d.y, F::zero());
        F::axiom_mul_zero_right(t);
        F::axiom_eqv_transitive(t.mul(d.y), t.mul(F::zero()), F::zero());
        additive_group_lemmas::lemma_add_congruence_right::<F>(la.y, t.mul(d.y), F::zero());
        F::axiom_add_zero_right(la.y);
        F::axiom_eqv_transitive(proj_y, la.y.add(F::zero()), la.y);

        // --- Lifted level: t_l*d_l.x ≡ QE::zero(), proj_x_l ≡ qext(la.x) ---
        ring_lemmas::lemma_mul_congruence_right::<SpecQuadExt<F, R>>(
            t_l, d_l.x, SpecQuadExt::<F, R>::zero());
        SpecQuadExt::<F, R>::axiom_mul_zero_right(t_l);
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            t_l.mul(d_l.x), t_l.mul(SpecQuadExt::<F, R>::zero()), SpecQuadExt::<F, R>::zero());
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(la.x));
        additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
            qext_from_rational::<F, R>(la.x), qext_from_rational::<F, R>(la.x),
            t_l.mul(d_l.x), SpecQuadExt::<F, R>::zero());
        SpecQuadExt::<F, R>::axiom_add_zero_right(qext_from_rational::<F, R>(la.x));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            proj_x_l,
            qext_from_rational::<F, R>(la.x).add(SpecQuadExt::<F, R>::zero()),
            qext_from_rational::<F, R>(la.x));

        // t_l*d_l.y ≡ QE::zero(), proj_y_l ≡ qext(la.y)
        ring_lemmas::lemma_mul_congruence_right::<SpecQuadExt<F, R>>(
            t_l, d_l.y, SpecQuadExt::<F, R>::zero());
        SpecQuadExt::<F, R>::axiom_mul_zero_right(t_l);
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            t_l.mul(d_l.y), t_l.mul(SpecQuadExt::<F, R>::zero()), SpecQuadExt::<F, R>::zero());
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(la.y));
        additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
            qext_from_rational::<F, R>(la.y), qext_from_rational::<F, R>(la.y),
            t_l.mul(d_l.y), SpecQuadExt::<F, R>::zero());
        SpecQuadExt::<F, R>::axiom_add_zero_right(qext_from_rational::<F, R>(la.y));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            proj_y_l,
            qext_from_rational::<F, R>(la.y).add(SpecQuadExt::<F, R>::zero()),
            qext_from_rational::<F, R>(la.y));

        // --- Result x: two_l*proj_x_l - Q(p.x) ≡ two_l*Q(la.x) - Q(p.x) ≡ Q(two*la.x - p.x) ---
        ring_lemmas::lemma_mul_congruence_right::<SpecQuadExt<F, R>>(
            two_l, proj_x_l, qext_from_rational::<F, R>(la.x));
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(p.x));
        additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
            two_l.mul(proj_x_l), two_l.mul(qext_from_rational::<F, R>(la.x)),
            qext_from_rational::<F, R>(p.x), qext_from_rational::<F, R>(p.x));
        lemma_lift_two_mul_sub_eqv::<F, R>(la.x, p.x);
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_x_l).sub(qext_from_rational::<F, R>(p.x)),
            two_l.mul(qext_from_rational::<F, R>(la.x)).sub(qext_from_rational::<F, R>(p.x)),
            qext_from_rational::<F, R>(two.mul(la.x).sub(p.x)));

        // Bridge to qext(result.x): result.x = two*proj_x - p.x ≡ two*la.x - p.x
        ring_lemmas::lemma_mul_congruence_right::<F>(two, proj_x, la.x);
        F::axiom_eqv_reflexive(p.x);
        additive_group_lemmas::lemma_sub_congruence::<F>(
            two.mul(proj_x), two.mul(la.x), p.x, p.x);
        F::axiom_eqv_symmetric(two.mul(proj_x).sub(p.x), two.mul(la.x).sub(p.x));
        lemma_rational_congruence::<F, R>(two.mul(la.x).sub(p.x), two.mul(proj_x).sub(p.x));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_x_l).sub(qext_from_rational::<F, R>(p.x)),
            qext_from_rational::<F, R>(two.mul(la.x).sub(p.x)),
            qext_from_rational::<F, R>(two.mul(proj_x).sub(p.x)));

        // --- Result y: same pattern ---
        ring_lemmas::lemma_mul_congruence_right::<SpecQuadExt<F, R>>(
            two_l, proj_y_l, qext_from_rational::<F, R>(la.y));
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(p.y));
        additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
            two_l.mul(proj_y_l), two_l.mul(qext_from_rational::<F, R>(la.y)),
            qext_from_rational::<F, R>(p.y), qext_from_rational::<F, R>(p.y));
        lemma_lift_two_mul_sub_eqv::<F, R>(la.y, p.y);
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_y_l).sub(qext_from_rational::<F, R>(p.y)),
            two_l.mul(qext_from_rational::<F, R>(la.y)).sub(qext_from_rational::<F, R>(p.y)),
            qext_from_rational::<F, R>(two.mul(la.y).sub(p.y)));
        ring_lemmas::lemma_mul_congruence_right::<F>(two, proj_y, la.y);
        F::axiom_eqv_reflexive(p.y);
        additive_group_lemmas::lemma_sub_congruence::<F>(
            two.mul(proj_y), two.mul(la.y), p.y, p.y);
        F::axiom_eqv_symmetric(two.mul(proj_y).sub(p.y), two.mul(la.y).sub(p.y));
        lemma_rational_congruence::<F, R>(two.mul(la.y).sub(p.y), two.mul(proj_y).sub(p.y));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_y_l).sub(qext_from_rational::<F, R>(p.y)),
            qext_from_rational::<F, R>(two.mul(la.y).sub(p.y)),
            qext_from_rational::<F, R>(two.mul(proj_y).sub(p.y)));

    } else {
        // === NON-DEGENERATE CASE: !dot_dd ≡ 0 ===

        // Prove !dot_dd_l ≡ QE::zero() by contradiction (for div_congruence)
        if dot_dd_l.eqv(SpecQuadExt::<F, R>::zero()) {
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                dot_dd_l, qext_from_rational::<F, R>(dot_dd));
            SpecQuadExt::<F, R>::axiom_eqv_transitive(
                qext_from_rational::<F, R>(dot_dd), dot_dd_l,
                SpecQuadExt::<F, R>::zero());
            lemma_qext_from_rational_injective::<F, R>(dot_dd, F::zero());
        }

        // Step 6: t_l ≡ qext(t) via div_congruence + rational_div
        lemma_div_congruence::<SpecQuadExt<F, R>>(
            dot_pad_l, qext_from_rational::<F, R>(dot_pad),
            dot_dd_l, qext_from_rational::<F, R>(dot_dd));
        // t_l ≡ qext(dot_pad).div(qext(dot_dd))
        // rational_div: qext(t) ≡ qext(dot_pad).div(qext(dot_dd)), flip it
        lemma_rational_div::<F, R>(dot_pad, dot_dd);
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(dot_pad.div(dot_dd)),
            qext_from_rational::<F, R>(dot_pad).div(qext_from_rational::<F, R>(dot_dd)));
        // t_l ≡ qext(dot_pad)/qext(dot_dd) ≡ qext(t)
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            t_l,
            qext_from_rational::<F, R>(dot_pad).div(qext_from_rational::<F, R>(dot_dd)),
            qext_from_rational::<F, R>(t));

        // Step 7x: t_l*d_l.x ≡ qext(t*d.x)
        ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
            t_l, qext_from_rational::<F, R>(t),
            d_l.x, qext_from_rational::<F, R>(d.x));
        lemma_rational_mul::<F, R>(t, d.x);
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(t.mul(d.x)),
            qext_from_rational::<F, R>(t).mul(qext_from_rational::<F, R>(d.x)));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            t_l.mul(d_l.x),
            qext_from_rational::<F, R>(t).mul(qext_from_rational::<F, R>(d.x)),
            qext_from_rational::<F, R>(t.mul(d.x)));

        // Step 8x: proj_x_l ≡ qext(proj_x)
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(la.x));
        additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
            qext_from_rational::<F, R>(la.x), qext_from_rational::<F, R>(la.x),
            t_l.mul(d_l.x), qext_from_rational::<F, R>(t.mul(d.x)));
        lemma_rational_add::<F, R>(la.x, t.mul(d.x));
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(proj_x),
            qext_from_rational::<F, R>(la.x).add(qext_from_rational::<F, R>(t.mul(d.x))));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            proj_x_l,
            qext_from_rational::<F, R>(la.x).add(qext_from_rational::<F, R>(t.mul(d.x))),
            qext_from_rational::<F, R>(proj_x));

        // Step 9x: result_l.x ≡ qext(result.x)
        ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
            two_l, qext_from_rational::<F, R>(two),
            proj_x_l, qext_from_rational::<F, R>(proj_x));
        lemma_rational_mul::<F, R>(two, proj_x);
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(two.mul(proj_x)),
            qext_from_rational::<F, R>(two).mul(qext_from_rational::<F, R>(proj_x)));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_x_l),
            qext_from_rational::<F, R>(two).mul(qext_from_rational::<F, R>(proj_x)),
            qext_from_rational::<F, R>(two.mul(proj_x)));
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(p.x));
        additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
            two_l.mul(proj_x_l), qext_from_rational::<F, R>(two.mul(proj_x)),
            qext_from_rational::<F, R>(p.x), qext_from_rational::<F, R>(p.x));
        lemma_rational_sub::<F, R>(two.mul(proj_x), p.x);
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(two.mul(proj_x).sub(p.x)),
            qext_from_rational::<F, R>(two.mul(proj_x)).sub(qext_from_rational::<F, R>(p.x)));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_x_l).sub(qext_from_rational::<F, R>(p.x)),
            qext_from_rational::<F, R>(two.mul(proj_x)).sub(qext_from_rational::<F, R>(p.x)),
            qext_from_rational::<F, R>(two.mul(proj_x).sub(p.x)));

        // Step 7y-9y: same for y
        ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
            t_l, qext_from_rational::<F, R>(t),
            d_l.y, qext_from_rational::<F, R>(d.y));
        lemma_rational_mul::<F, R>(t, d.y);
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(t.mul(d.y)),
            qext_from_rational::<F, R>(t).mul(qext_from_rational::<F, R>(d.y)));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            t_l.mul(d_l.y),
            qext_from_rational::<F, R>(t).mul(qext_from_rational::<F, R>(d.y)),
            qext_from_rational::<F, R>(t.mul(d.y)));
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(la.y));
        additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
            qext_from_rational::<F, R>(la.y), qext_from_rational::<F, R>(la.y),
            t_l.mul(d_l.y), qext_from_rational::<F, R>(t.mul(d.y)));
        lemma_rational_add::<F, R>(la.y, t.mul(d.y));
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(proj_y),
            qext_from_rational::<F, R>(la.y).add(qext_from_rational::<F, R>(t.mul(d.y))));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            proj_y_l,
            qext_from_rational::<F, R>(la.y).add(qext_from_rational::<F, R>(t.mul(d.y))),
            qext_from_rational::<F, R>(proj_y));
        ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
            two_l, qext_from_rational::<F, R>(two),
            proj_y_l, qext_from_rational::<F, R>(proj_y));
        lemma_rational_mul::<F, R>(two, proj_y);
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(two.mul(proj_y)),
            qext_from_rational::<F, R>(two).mul(qext_from_rational::<F, R>(proj_y)));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_y_l),
            qext_from_rational::<F, R>(two).mul(qext_from_rational::<F, R>(proj_y)),
            qext_from_rational::<F, R>(two.mul(proj_y)));
        SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(p.y));
        additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
            two_l.mul(proj_y_l), qext_from_rational::<F, R>(two.mul(proj_y)),
            qext_from_rational::<F, R>(p.y), qext_from_rational::<F, R>(p.y));
        lemma_rational_sub::<F, R>(two.mul(proj_y), p.y);
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            qext_from_rational::<F, R>(two.mul(proj_y).sub(p.y)),
            qext_from_rational::<F, R>(two.mul(proj_y)).sub(qext_from_rational::<F, R>(p.y)));
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            two_l.mul(proj_y_l).sub(qext_from_rational::<F, R>(p.y)),
            qext_from_rational::<F, R>(two.mul(proj_y)).sub(qext_from_rational::<F, R>(p.y)),
            qext_from_rational::<F, R>(two.mul(proj_y).sub(p.y)));
    }
}

// ===========================================================================
//  Main locus correspondence lemma (updated with locus_eqv ensures)
// ===========================================================================

/// For constraints where all referenced entities (other than target) are in a
/// purely rational resolved map, lifting commutes with locus construction
/// up to locus_eqv.
pub proof fn lemma_lift_constraint_to_locus<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
    resolved: ResolvedPoints<F>,
    target: EntityId,
)
    requires
        constraint_entities(c).contains(target),
        constraint_entities(c).remove(target).subset_of(resolved.dom()),
        !resolved.dom().contains(target),
    ensures
        locus_eqv(
            constraint_to_locus(lift_constraint::<F, R>(c), lift_resolved_map::<F, R>(resolved), target),
            lift_locus::<F, R>(constraint_to_locus(c, resolved, target)),
        ),
{
    lemma_lift_resolved_map_dom::<F, R>(resolved);

    match c {
        Constraint::Coincident { a, b } => {
            // AtPoint(lift_point2(resolved[x])) vs AtPoint(lift_point2(resolved[x])) — equal
            if target == a && resolved.dom().contains(b) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[b].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[b].y));
            } else if target == b && resolved.dom().contains(a) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a].y));
            }
        }
        Constraint::DistanceSq { a, b, dist_sq } => {
            // OnCircle: center and radius_sq are syntactically equal after lifting
            if target == a && resolved.dom().contains(b) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[b].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[b].y));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(dist_sq));
            } else if target == b && resolved.dom().contains(a) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a].y));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(dist_sq));
            }
        }
        Constraint::FixedX { point, x } => {
            // OnLine: a=1, b=0 (syntactically equal), c = qext(x).neg() vs qext(x.neg())
            SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::one());
            SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::zero());
            lemma_qext_from_rational_neg_eqv::<F, R>(x);
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                qext_from_rational::<F, R>(x.neg()),
                qext_from_rational::<F, R>(x).neg(),
            );
        }
        Constraint::FixedY { point, y } => {
            SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::one());
            SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::zero());
            lemma_qext_from_rational_neg_eqv::<F, R>(y);
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                qext_from_rational::<F, R>(y.neg()),
                qext_from_rational::<F, R>(y).neg(),
            );
        }
        Constraint::SameX { a, b } => {
            if target == a && resolved.dom().contains(b) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::one());
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::zero());
                lemma_qext_from_rational_neg_eqv::<F, R>(resolved[b].x);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(resolved[b].x.neg()),
                    qext_from_rational::<F, R>(resolved[b].x).neg(),
                );
            } else if target == b && resolved.dom().contains(a) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::one());
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::zero());
                lemma_qext_from_rational_neg_eqv::<F, R>(resolved[a].x);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(resolved[a].x.neg()),
                    qext_from_rational::<F, R>(resolved[a].x).neg(),
                );
            }
        }
        Constraint::SameY { a, b } => {
            if target == a && resolved.dom().contains(b) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::one());
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::zero());
                lemma_qext_from_rational_neg_eqv::<F, R>(resolved[b].y);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(resolved[b].y.neg()),
                    qext_from_rational::<F, R>(resolved[b].y).neg(),
                );
            } else if target == b && resolved.dom().contains(a) {
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::one());
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(SpecQuadExt::<F, R>::zero());
                lemma_qext_from_rational_neg_eqv::<F, R>(resolved[a].y);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(resolved[a].y.neg()),
                    qext_from_rational::<F, R>(resolved[a].y).neg(),
                );
            }
        }
        Constraint::PointOnLine { point, line_a, line_b } => {
            if target == point && resolved.dom().contains(line_a) && resolved.dom().contains(line_b) {
                lemma_lift_line2_from_points_eqv::<F, R>(resolved[line_a], resolved[line_b]);
            }
            // else: both FullPlane
        }
        Constraint::Collinear { a, b, c } => {
            if target == c && resolved.dom().contains(a) && resolved.dom().contains(b) {
                lemma_lift_line2_from_points_eqv::<F, R>(resolved[a], resolved[b]);
            } else if target == a && resolved.dom().contains(b) && resolved.dom().contains(c) {
                lemma_lift_line2_from_points_eqv::<F, R>(resolved[b], resolved[c]);
            } else if target == b && resolved.dom().contains(a) && resolved.dom().contains(c) {
                lemma_lift_line2_from_points_eqv::<F, R>(resolved[a], resolved[c]);
            }
        }
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            // OnCircle with radius = sq_dist_2d(b1, b2)
            if target == a1 && resolved.dom().contains(a2) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                lemma_lift_sq_dist_2d_eqv::<F, R>(resolved[b1], resolved[b2]);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2])),
                    qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2])),
                );
                // center: lift_point2(resolved[a2]) components reflexive
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a2].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a2].y));
            } else if target == a2 && resolved.dom().contains(a1) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                lemma_lift_sq_dist_2d_eqv::<F, R>(resolved[b1], resolved[b2]);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2])),
                    qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2])),
                );
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a1].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a1].y));
            }
        }
        Constraint::PointOnCircle { point, center, radius_point } => {
            if target == point && resolved.dom().contains(center) && resolved.dom().contains(radius_point) {
                lemma_lift_sq_dist_2d_eqv::<F, R>(resolved[radius_point], resolved[center]);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    sq_dist_2d(lift_point2::<F, R>(resolved[radius_point]), lift_point2::<F, R>(resolved[center])),
                    qext_from_rational::<F, R>(sq_dist_2d(resolved[radius_point], resolved[center])),
                );
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[center].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[center].y));
            }
        }
        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            // OnLine with a=db.x, b=db.y, c=(db.x*other.x+db.y*other.y).neg()
            // where db = sub2(b2, b1)
            if target == a1 && resolved.dom().contains(a2) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                lemma_lift_sub2_eqv::<F, R>(resolved[b2], resolved[b1]);
                let db = sub2(resolved[b2], resolved[b1]);
                let db_l = sub2(lift_point2::<F, R>(resolved[b2]), lift_point2::<F, R>(resolved[b1]));
                lemma_lift_dot_neg_eqv::<F, R>(db.x, db.y, resolved[a2].x, resolved[a2].y, db_l.x, db_l.y);
            } else if target == a2 && resolved.dom().contains(a1) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                lemma_lift_sub2_eqv::<F, R>(resolved[b2], resolved[b1]);
                let db = sub2(resolved[b2], resolved[b1]);
                let db_l = sub2(lift_point2::<F, R>(resolved[b2]), lift_point2::<F, R>(resolved[b1]));
                lemma_lift_dot_neg_eqv::<F, R>(db.x, db.y, resolved[a1].x, resolved[a1].y, db_l.x, db_l.y);
            }
        }
        Constraint::Parallel { a1, a2, b1, b2 } => {
            // OnLine with a=db.y, b=db.x.neg(), c=(db.y*other.x+db.x.neg()*other.y).neg()
            if target == a1 && resolved.dom().contains(a2) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                lemma_lift_sub2_eqv::<F, R>(resolved[b2], resolved[b1]);
                let db = sub2(resolved[b2], resolved[b1]);
                let db_l = sub2(lift_point2::<F, R>(resolved[b2]), lift_point2::<F, R>(resolved[b1]));
                // a=db_l.y ≡ qext(db.y) — from lift_sub2_eqv
                // b=db_l.x.neg() ≡ qext(db.x).neg() ≡ qext(db.x.neg()) — neg_congruence + neg_eqv
                SpecQuadExt::<F, R>::axiom_neg_congruence(
                    db_l.x, qext_from_rational::<F, R>(db.x),
                );
                lemma_qext_from_rational_neg_eqv::<F, R>(db.x);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(db.x.neg()),
                    qext_from_rational::<F, R>(db.x).neg(),
                );
                SpecQuadExt::<F, R>::axiom_eqv_transitive(
                    db_l.x.neg(),
                    qext_from_rational::<F, R>(db.x).neg(),
                    qext_from_rational::<F, R>(db.x.neg()),
                );
                // c: use dot_neg_eqv with (db.y, db.x.neg()) as the direction
                lemma_lift_dot_neg_eqv::<F, R>(
                    db.y, db.x.neg(), resolved[a2].x, resolved[a2].y,
                    db_l.y, db_l.x.neg(),
                );
            } else if target == a2 && resolved.dom().contains(a1) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                lemma_lift_sub2_eqv::<F, R>(resolved[b2], resolved[b1]);
                let db = sub2(resolved[b2], resolved[b1]);
                let db_l = sub2(lift_point2::<F, R>(resolved[b2]), lift_point2::<F, R>(resolved[b1]));
                SpecQuadExt::<F, R>::axiom_neg_congruence(
                    db_l.x, qext_from_rational::<F, R>(db.x),
                );
                lemma_qext_from_rational_neg_eqv::<F, R>(db.x);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(db.x.neg()),
                    qext_from_rational::<F, R>(db.x).neg(),
                );
                SpecQuadExt::<F, R>::axiom_eqv_transitive(
                    db_l.x.neg(),
                    qext_from_rational::<F, R>(db.x).neg(),
                    qext_from_rational::<F, R>(db.x.neg()),
                );
                lemma_lift_dot_neg_eqv::<F, R>(
                    db.y, db.x.neg(), resolved[a1].x, resolved[a1].y,
                    db_l.y, db_l.x.neg(),
                );
            }
        }
        Constraint::Midpoint { mid, a, b } => {
            if target == mid && resolved.dom().contains(a) && resolved.dom().contains(b) {
                // AtPoint((ax+bx)/2, (ay+by)/2) — uses div by two
                lemma_lift_add_div_two_eqv::<F, R>(resolved[a].x, resolved[b].x);
                lemma_lift_add_div_two_eqv::<F, R>(resolved[a].y, resolved[b].y);
            } else if target == a && resolved.dom().contains(mid) && resolved.dom().contains(b) {
                // AtPoint(2*mid.x - b.x, 2*mid.y - b.y)
                lemma_lift_two_mul_sub_eqv::<F, R>(resolved[mid].x, resolved[b].x);
                lemma_lift_two_mul_sub_eqv::<F, R>(resolved[mid].y, resolved[b].y);
            } else if target == b && resolved.dom().contains(mid) && resolved.dom().contains(a) {
                // AtPoint(2*mid.x - a.x, 2*mid.y - a.y)
                lemma_lift_two_mul_sub_eqv::<F, R>(resolved[mid].x, resolved[a].x);
                lemma_lift_two_mul_sub_eqv::<F, R>(resolved[mid].y, resolved[a].y);
            }
        }
        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            if target == point && resolved.dom().contains(original)
                && resolved.dom().contains(axis_a) && resolved.dom().contains(axis_b)
            {
                lemma_lift_reflect_point_eqv::<F, R>(
                    resolved[original], resolved[axis_a], resolved[axis_b]);
            }
            // else: both FullPlane
        }
        Constraint::FixedPoint { point, x, y } => {
            if target == point {
                // AtPoint(Point2{qext(x), qext(y)}) vs AtPoint(lift_point2(Point2{x,y}))
                // lift_point2(Point2{x,y}) = Point2{qext(x), qext(y)} — syntactically equal
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(y));
            }
        }
        Constraint::Ratio { a1, a2, b1, b2, ratio_sq } => {
            if target == a1 && resolved.dom().contains(a2) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                // OnCircle(center=lift_point2(resolved[a2]), radius_sq=qext(ratio_sq)*sq_dist_lifted)
                // vs lift of OnCircle(center=resolved[a2], radius_sq=ratio_sq*sq_dist(b1,b2))
                // center: reflexive
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a2].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a2].y));
                // radius: qext(ratio_sq)*sq_dist_lifted ≡ qext(ratio_sq*sq_dist(b1,b2))
                lemma_lift_sq_dist_2d_eqv::<F, R>(resolved[b1], resolved[b2]);
                // sq_dist_lifted ≡ qext(sq_dist_base), flip
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2])),
                    qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2])),
                );
                // qext(ratio_sq) * sq_dist_lifted ≡ qext(ratio_sq) * qext(sq_dist_base)
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(ratio_sq));
                ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
                    qext_from_rational::<F, R>(ratio_sq), qext_from_rational::<F, R>(ratio_sq),
                    sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2])),
                    qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2])),
                );
                // qext(ratio_sq) * qext(sq_dist_base) ≡ qext(ratio_sq * sq_dist_base)
                lemma_rational_mul::<F, R>(ratio_sq, sq_dist_2d(resolved[b1], resolved[b2]));
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(ratio_sq.mul(sq_dist_2d(resolved[b1], resolved[b2]))),
                    qext_from_rational::<F, R>(ratio_sq).mul(qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2]))),
                );
                // Chain
                SpecQuadExt::<F, R>::axiom_eqv_transitive(
                    qext_from_rational::<F, R>(ratio_sq).mul(
                        sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2]))),
                    qext_from_rational::<F, R>(ratio_sq).mul(
                        qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2]))),
                    qext_from_rational::<F, R>(ratio_sq.mul(sq_dist_2d(resolved[b1], resolved[b2]))),
                );
            } else if target == a2 && resolved.dom().contains(a1) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                // Same pattern with a1 as center
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a1].x));
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(resolved[a1].y));
                lemma_lift_sq_dist_2d_eqv::<F, R>(resolved[b1], resolved[b2]);
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2])),
                    qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2])),
                );
                SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(ratio_sq));
                ring_lemmas::lemma_mul_congruence::<SpecQuadExt<F, R>>(
                    qext_from_rational::<F, R>(ratio_sq), qext_from_rational::<F, R>(ratio_sq),
                    sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2])),
                    qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2])),
                );
                lemma_rational_mul::<F, R>(ratio_sq, sq_dist_2d(resolved[b1], resolved[b2]));
                SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                    qext_from_rational::<F, R>(ratio_sq.mul(sq_dist_2d(resolved[b1], resolved[b2]))),
                    qext_from_rational::<F, R>(ratio_sq).mul(qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2]))),
                );
                SpecQuadExt::<F, R>::axiom_eqv_transitive(
                    qext_from_rational::<F, R>(ratio_sq).mul(
                        sq_dist_2d(lift_point2::<F, R>(resolved[b1]), lift_point2::<F, R>(resolved[b2]))),
                    qext_from_rational::<F, R>(ratio_sq).mul(
                        qext_from_rational::<F, R>(sq_dist_2d(resolved[b1], resolved[b2]))),
                    qext_from_rational::<F, R>(ratio_sq.mul(sq_dist_2d(resolved[b1], resolved[b2]))),
                );
            }
        }
        Constraint::Tangent { .. } => {
            // Both sides are FullPlane — trivially eqv
        }
        Constraint::CircleTangent { .. } => {
            // Both sides are FullPlane
        }
        Constraint::Angle { .. } => {
            // Both sides are FullPlane
        }
    }
}

// ===========================================================================
//  Round 2: Core lifting lemmas
// ===========================================================================

/// Lifting a rational point preserves locus satisfaction.
/// If p satisfies locus at the base field, then lift_point2(p) satisfies lift_locus(locus)
/// at the extension field.
pub proof fn lemma_lift_preserves_satisfaction<F: OrderedField, R: PositiveRadicand<F>>(
    locus: Locus2d<F>, p: Point2<F>,
)
    requires point_satisfies_locus(locus, p),
    ensures point_satisfies_locus(lift_locus::<F, R>(locus), lift_point2::<F, R>(p)),
{
    match locus {
        Locus2d::FullPlane => {
            // trivial: FullPlane lifts to FullPlane, always satisfied
        }
        Locus2d::AtPoint(q) => {
            // p.eqv(q) means p.x.eqv(q.x) && p.y.eqv(q.y)
            // Need: lift_point2(p).eqv(lift_point2(q))
            //     = qext(p.x).eqv(qext(q.x)) && qext(p.y).eqv(qext(q.y))
            lemma_rational_congruence::<F, R>(p.x, q.x);
            lemma_rational_congruence::<F, R>(p.y, q.y);
        }
        Locus2d::OnLine(line) => {
            // point_on_line2(line, p) means:
            //   line.a * p.x + line.b * p.y + line.c ≡ 0
            // Need: point_on_line2(lift_line2(line), lift_point2(p))
            //   = qext(a)*qext(px) + qext(b)*qext(py) + qext(c) ≡ qext(0) = 0
            //
            // Strategy: show each term lifts, then chain additions
            let a = line.a;
            let b = line.b;
            let c = line.c;
            let px = p.x;
            let py = p.y;

            // Step 1: qext(a*px) ≡ qext(a)*qext(px)
            lemma_rational_mul::<F, R>(a, px);
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                qext_from_rational::<F, R>(a.mul(px)),
                qext_from_rational::<F, R>(a).mul(qext_from_rational::<F, R>(px)),
            );

            // Step 2: qext(b*py) ≡ qext(b)*qext(py)
            lemma_rational_mul::<F, R>(b, py);
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                qext_from_rational::<F, R>(b.mul(py)),
                qext_from_rational::<F, R>(b).mul(qext_from_rational::<F, R>(py)),
            );

            // Step 3: qext(a*px + b*py) ≡ qext(a*px) + qext(b*py)
            lemma_rational_add::<F, R>(a.mul(px), b.mul(py));
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py))),
                qext_from_rational::<F, R>(a.mul(px)).add(qext_from_rational::<F, R>(b.mul(py))),
            );

            // Step 4: chain: qext(a)*qext(px) + qext(b)*qext(py) ≡ qext(a*px) + qext(b*py) ≡ qext(a*px + b*py)
            additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
                qext_from_rational::<F, R>(a).mul(qext_from_rational::<F, R>(px)),
                qext_from_rational::<F, R>(a.mul(px)),
                qext_from_rational::<F, R>(b).mul(qext_from_rational::<F, R>(py)),
                qext_from_rational::<F, R>(b.mul(py)),
            );
            SpecQuadExt::<F, R>::axiom_eqv_transitive(
                qext_from_rational::<F, R>(a).mul(qext_from_rational::<F, R>(px))
                    .add(qext_from_rational::<F, R>(b).mul(qext_from_rational::<F, R>(py))),
                qext_from_rational::<F, R>(a.mul(px)).add(qext_from_rational::<F, R>(b.mul(py))),
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py))),
            );

            // Step 5: qext(a*px+b*py+c) ≡ qext(a*px+b*py) + qext(c)
            lemma_rational_add::<F, R>(a.mul(px).add(b.mul(py)), c);
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py)).add(c)),
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py))).add(
                    qext_from_rational::<F, R>(c)),
            );

            // Step 6: chain full expression ≡ qext(a*px + b*py + c)
            // Need reflexivity for qext(c) ≡ qext(c) as precondition
            SpecQuadExt::<F, R>::axiom_eqv_reflexive(qext_from_rational::<F, R>(c));
            additive_group_lemmas::lemma_add_congruence::<SpecQuadExt<F, R>>(
                qext_from_rational::<F, R>(a).mul(qext_from_rational::<F, R>(px))
                    .add(qext_from_rational::<F, R>(b).mul(qext_from_rational::<F, R>(py))),
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py))),
                qext_from_rational::<F, R>(c),
                qext_from_rational::<F, R>(c),
            );

            SpecQuadExt::<F, R>::axiom_eqv_transitive(
                qext_from_rational::<F, R>(a).mul(qext_from_rational::<F, R>(px))
                    .add(qext_from_rational::<F, R>(b).mul(qext_from_rational::<F, R>(py)))
                    .add(qext_from_rational::<F, R>(c)),
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py))).add(
                    qext_from_rational::<F, R>(c)),
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py)).add(c)),
            );

            // Step 7: base field says a*px + b*py + c ≡ 0, so qext(a*px+b*py+c) ≡ qext(0) = QE::zero()
            lemma_rational_congruence::<F, R>(
                a.mul(px).add(b.mul(py)).add(c),
                F::zero(),
            );

            // Step 8: final chain
            SpecQuadExt::<F, R>::axiom_eqv_transitive(
                qext_from_rational::<F, R>(a).mul(qext_from_rational::<F, R>(px))
                    .add(qext_from_rational::<F, R>(b).mul(qext_from_rational::<F, R>(py)))
                    .add(qext_from_rational::<F, R>(c)),
                qext_from_rational::<F, R>(a.mul(px).add(b.mul(py)).add(c)),
                qext_from_rational::<F, R>(F::zero()),
            );

            // qext_from_rational(F::zero()) is the zero of SpecQuadExt by definition
            // (re = F::zero(), im = F::zero()) which is SpecQuadExt::zero()
            // So point_on_line2 is satisfied.
        }
        Locus2d::OnCircle(circle) => {
            // point_on_circle2(circle, p) means sq_dist_2d(p, center) ≡ radius_sq
            // Need: sq_dist_2d(lift_point2(p), lift_point2(center)) ≡ qext(radius_sq)
            //
            // By lemma_lift_sq_dist_2d_eqv:
            //   sq_dist_2d(lift(p), lift(center)) ≡ qext(sq_dist_2d(p, center))
            // By base field: sq_dist_2d(p, center) ≡ radius_sq
            // So qext(sq_dist_2d(p, center)) ≡ qext(radius_sq) by congruence
            // Chain gives the result.
            lemma_lift_sq_dist_2d_eqv::<F, R>(p, circle.center);
            lemma_rational_congruence::<F, R>(
                sq_dist_2d(p, circle.center),
                circle.radius_sq,
            );
            SpecQuadExt::<F, R>::axiom_eqv_transitive(
                sq_dist_2d(lift_point2::<F, R>(p), lift_point2::<F, R>(circle.center)),
                qext_from_rational::<F, R>(sq_dist_2d(p, circle.center)),
                qext_from_rational::<F, R>(circle.radius_sq),
            );
        }
    }
}

/// Line-line intersection commutes with embedding (up to eqv):
/// line_line_intersection_2d(lift(l1), lift(l2)) ≡ lift(line_line_intersection_2d(l1, l2))
pub proof fn lemma_ll_intersection_lift_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    l1: Line2<F>, l2: Line2<F>,
)
    requires !line_det(l1, l2).eqv(F::zero()),
    ensures line_line_intersection_2d(lift_line2::<F, R>(l1), lift_line2::<F, R>(l2))
        .eqv(lift_point2::<F, R>(line_line_intersection_2d(l1, l2))),
{
    let a1 = l1.a;
    let b1 = l1.b;
    let c1 = l1.c;
    let a2 = l2.a;
    let b2 = l2.b;
    let c2 = l2.c;
    let det = line_det(l1, l2);

    // x component: (b1*c2 - b2*c1) / det
    // Need: qext(b1)*qext(c2) - qext(b2)*qext(c1)) / line_det(lift(l1), lift(l2))
    //     ≡ qext((b1*c2 - b2*c1) / det)

    // Step 1: line_det(lift(l1), lift(l2)) ≡ qext(det), and !qext(det).eqv(QE::zero())
    lemma_lift_line_det::<F, R>(l1, l2);
    // Need !qext(det).eqv(zero) for div. We have !det.eqv(F::zero()).
    // qext is injective on eqv (contra: if qext(det)≡0 then det≡0).
    // Use lemma_square_zero: SpecQuadExt zero has re=F::zero(), im=F::zero().
    // qext(det) = (det, 0). If (det,0) ≡ (0,0) then det ≡ 0, contradiction.

    // Step 2: numerator x: b1*c2 - b2*c1
    // qext(b1)*qext(c2) ≡ qext(b1*c2)
    lemma_rational_mul::<F, R>(b1, c2);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(b1.mul(c2)),
        qext_from_rational::<F, R>(b1).mul(qext_from_rational::<F, R>(c2)),
    );
    // qext(b2)*qext(c1) ≡ qext(b2*c1)
    lemma_rational_mul::<F, R>(b2, c1);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(b2.mul(c1)),
        qext_from_rational::<F, R>(b2).mul(qext_from_rational::<F, R>(c1)),
    );
    // subtraction: ... ≡ qext(b1*c2 - b2*c1)
    additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(b1).mul(qext_from_rational::<F, R>(c2)),
        qext_from_rational::<F, R>(b1.mul(c2)),
        qext_from_rational::<F, R>(b2).mul(qext_from_rational::<F, R>(c1)),
        qext_from_rational::<F, R>(b2.mul(c1)),
    );
    lemma_rational_sub::<F, R>(b1.mul(c2), b2.mul(c1));
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(b1.mul(c2).sub(b2.mul(c1))),
        qext_from_rational::<F, R>(b1.mul(c2)).sub(qext_from_rational::<F, R>(b2.mul(c1))),
    );
    // chain numerator_x
    let num_x_l = qext_from_rational::<F, R>(b1).mul(qext_from_rational::<F, R>(c2))
        .sub(qext_from_rational::<F, R>(b2).mul(qext_from_rational::<F, R>(c1)));
    let num_x_r = qext_from_rational::<F, R>(b1.mul(c2).sub(b2.mul(c1)));
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        num_x_l,
        qext_from_rational::<F, R>(b1.mul(c2)).sub(qext_from_rational::<F, R>(b2.mul(c1))),
        num_x_r,
    );

    // Step 3: numerator y: a2*c1 - a1*c2
    lemma_rational_mul::<F, R>(a2, c1);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a2.mul(c1)),
        qext_from_rational::<F, R>(a2).mul(qext_from_rational::<F, R>(c1)),
    );
    lemma_rational_mul::<F, R>(a1, c2);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a1.mul(c2)),
        qext_from_rational::<F, R>(a1).mul(qext_from_rational::<F, R>(c2)),
    );
    additive_group_lemmas::lemma_sub_congruence::<SpecQuadExt<F, R>>(
        qext_from_rational::<F, R>(a2).mul(qext_from_rational::<F, R>(c1)),
        qext_from_rational::<F, R>(a2.mul(c1)),
        qext_from_rational::<F, R>(a1).mul(qext_from_rational::<F, R>(c2)),
        qext_from_rational::<F, R>(a1.mul(c2)),
    );
    lemma_rational_sub::<F, R>(a2.mul(c1), a1.mul(c2));
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a2.mul(c1).sub(a1.mul(c2))),
        qext_from_rational::<F, R>(a2.mul(c1)).sub(qext_from_rational::<F, R>(a1.mul(c2))),
    );
    let num_y_l = qext_from_rational::<F, R>(a2).mul(qext_from_rational::<F, R>(c1))
        .sub(qext_from_rational::<F, R>(a1).mul(qext_from_rational::<F, R>(c2)));
    let num_y_r = qext_from_rational::<F, R>(a2.mul(c1).sub(a1.mul(c2)));
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        num_y_l,
        qext_from_rational::<F, R>(a2.mul(c1)).sub(qext_from_rational::<F, R>(a1.mul(c2))),
        num_y_r,
    );

    // Step 4: division: num/det at both levels
    let det_l = line_det(lift_line2::<F, R>(l1), lift_line2::<F, R>(l2));
    let det_r = qext_from_rational::<F, R>(det);

    // Prove !det_l.eqv(QE::zero()): needed for division precondition.
    // det_l ≡ det_r = qext(det). qext(det) = (det, 0). QE::zero() = (0, 0).
    // eqv for QE is component-wise, so qext(det).eqv(zero) iff det.eqv(F::zero()),
    // which is false by precondition.
    // But det_l ≡ det_r, so if det_l ≡ 0 then det_r ≡ 0 by sym+trans, contradiction.
    assert(!det_r.eqv(SpecQuadExt::<F, R>::zero()));
    // For det_l: det_l ≡ det_r and !det_r ≡ 0, so !det_l ≡ 0
    // (if det_l ≡ 0, then 0 ≡ det_l (sym) ≡ det_r (trans) → det_r ≡ 0, contradiction)
    assert(!det_l.eqv(SpecQuadExt::<F, R>::zero())) by {
        if det_l.eqv(SpecQuadExt::<F, R>::zero()) {
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                det_l, SpecQuadExt::<F, R>::zero());
            // Now: zero ≡ det_l
            // And: det_l ≡ det_r
            SpecQuadExt::<F, R>::axiom_eqv_transitive(
                SpecQuadExt::<F, R>::zero(), det_l, det_r);
            // zero ≡ det_r
            SpecQuadExt::<F, R>::axiom_eqv_symmetric(
                SpecQuadExt::<F, R>::zero(), det_r);
            // det_r ≡ zero — contradiction!
        }
    };

    // x: num_x_l / det_l ≡ num_x_r / det_r ≡ qext(num_x / det)
    lemma_div_congruence::<SpecQuadExt<F, R>>(
        num_x_l, num_x_r, det_l, det_r,
    );
    lemma_rational_div::<F, R>(b1.mul(c2).sub(b2.mul(c1)), det);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(b1.mul(c2).sub(b2.mul(c1)).div(det)),
        num_x_r.div(det_r),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        num_x_l.div(det_l),
        num_x_r.div(det_r),
        qext_from_rational::<F, R>(b1.mul(c2).sub(b2.mul(c1)).div(det)),
    );

    // y: num_y_l / det_l ≡ qext(num_y / det)
    lemma_div_congruence::<SpecQuadExt<F, R>>(
        num_y_l, num_y_r, det_l, det_r,
    );
    lemma_rational_div::<F, R>(a2.mul(c1).sub(a1.mul(c2)), det);
    SpecQuadExt::<F, R>::axiom_eqv_symmetric(
        qext_from_rational::<F, R>(a2.mul(c1).sub(a1.mul(c2)).div(det)),
        num_y_r.div(det_r),
    );
    SpecQuadExt::<F, R>::axiom_eqv_transitive(
        num_y_l.div(det_l),
        num_y_r.div(det_r),
        qext_from_rational::<F, R>(a2.mul(c1).sub(a1.mul(c2)).div(det)),
    );
    // Now: ll_intersect(lift(l1), lift(l2)).x ≡ qext(ll_intersect(l1,l2).x)
    //  and ll_intersect(lift(l1), lift(l2)).y ≡ qext(ll_intersect(l1,l2).y)
    // which is exactly Point2::eqv (component-wise)
}

/// For rational steps (PointStep and LineLine), execution commutes with lifting:
/// execute_step(lift_step(step)) ≡ lift_point2(execute_step(step))
pub proof fn lemma_rational_step_execute_lift_eqv<F: OrderedField, R: PositiveRadicand<F>>(
    step: ConstructionStep<F>,
)
    requires
        is_rational_step(step),
        step_geometrically_valid(step),
    ensures
        execute_step(lift_construction_step::<F, R>(step))
            .eqv(lift_point2::<F, R>(execute_step(step))),
{
    match step {
        ConstructionStep::PointStep { id, position } => {
            Point2::<SpecQuadExt<F, R>>::axiom_eqv_reflexive(
                lift_point2::<F, R>(position),
            );
        }
        ConstructionStep::LineLine { id, line1, line2 } => {
            // step_geometrically_valid guarantees !line_det(line1, line2).eqv(F::zero())
            lemma_ll_intersection_lift_eqv::<F, R>(line1, line2);
        }
        _ => {
            // CircleLine and CircleCircle are not rational steps
            // is_rational_step precludes these
        }
    }
}

// ===========================================================================
//  Round 3: Resolved map correspondence
// ===========================================================================

/// For all rational step entries in plan[0..si), the extension-level resolved map
/// agrees with the lifted base map (up to eqv).
///
/// Formally: if step j (j < si) is a rational step with target e, then
///   execute_plan(lift_plan(plan).take(si))[e] ≡ lift_point2(execute_plan(plan.take(si))[e])
///
/// This is the key fact bridging base-field execution to extension-field execution
/// for the inputs to constraint locus computation.
pub proof fn lemma_resolved_maps_agree_rational_entries<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
    si: int,
)
    requires
        0 <= si <= plan.len(),
        // Distinct targets
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        // All steps are geometrically valid
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
    ensures
        forall|e: EntityId|
            execute_plan(plan.take(si)).dom().contains(e)
            && (exists|j: int| 0 <= j < si && step_target(plan[j]) == e && is_rational_step(plan[j]))
            ==> execute_plan(lift_plan::<F, R>(plan).take(si))[e]
                .eqv(lift_point2::<F, R>(execute_plan(plan.take(si))[e])),
    decreases si,
{
    if si == 0 {
        // Empty prefix: no entries, vacuously true
    } else {
        // Inductive step
        lemma_resolved_maps_agree_rational_entries::<F, R>(plan, si - 1);

        let step = plan[si - 1];
        let target = step_target(step);

        // Key structural facts about take/lift
        assert(plan.take(si) == plan.take(si - 1).push(plan[si - 1]));
        assert(lift_plan::<F, R>(plan).take(si)
            =~= lift_plan::<F, R>(plan.take(si - 1)).push(
                lift_construction_step::<F, R>(plan[si - 1])));

        // The resolved maps after si steps
        let base_resolved = execute_plan(plan.take(si));
        let base_prev = execute_plan(plan.take(si - 1));
        let ext_resolved = execute_plan(lift_plan::<F, R>(plan).take(si));
        let ext_prev = execute_plan(lift_plan::<F, R>(plan.take(si - 1)));

        // lift_plan(plan).take(si) has same structure as lift of plan.take(si)
        // so ext_resolved inserts at the same target as base_resolved

        lemma_lift_step_target::<F, R>(step);

        // Help Z3 unfold execute_plan on the si-length prefix
        // plan.take(si) = plan.take(si-1).push(step), so:
        //   execute_plan(plan.take(si)) = base_prev.insert(target, execute_step(step))
        assert(plan.take(si).drop_last() =~= plan.take(si - 1));
        assert(plan.take(si).last() == step);
        assert(base_resolved =~= base_prev.insert(target, execute_step(step)));

        // Same for extension level
        let lift_step = lift_construction_step::<F, R>(step);
        assert(lift_plan::<F, R>(plan).take(si).drop_last()
            =~= lift_plan::<F, R>(plan.take(si - 1)));
        assert(lift_plan::<F, R>(plan).take(si).last() == lift_step);
        assert(ext_resolved =~= ext_prev.insert(
            step_target(lift_step), execute_step(lift_step)));

        // Domain correspondence
        lemma_lift_plan_domain::<F, R>(plan.take(si - 1));

        // Key identity: lift_plan(plan).take(si-1) =~= lift_plan(plan.take(si-1))
        // The IH is stated in terms of the former, ext_prev uses the latter.
        assert(lift_plan::<F, R>(plan).take(si - 1)
            =~= lift_plan::<F, R>(plan.take(si - 1)));

        // For any entity e with a witnessing rational step j:
        assert forall|e: EntityId|
            base_resolved.dom().contains(e)
            && (exists|j: int| 0 <= j < si && step_target(plan[j]) == e && is_rational_step(plan[j]))
        implies
            ext_resolved[e].eqv(lift_point2::<F, R>(base_resolved[e]))
        by {
            let j = choose|j: int| 0 <= j < si && step_target(plan[j]) == e && is_rational_step(plan[j]);

            if j == si - 1 {
                // e == target (since step_target(plan[si-1]) == target == e)
                assert(e == target);
                // base_resolved[target] == execute_step(step)  (Map::insert at target)
                // ext_resolved[target] == execute_step(lift_step)
                assert(base_resolved[e] == execute_step(step));
                assert(ext_resolved[e] == execute_step(lift_step));
                lemma_rational_step_execute_lift_eqv::<F, R>(step);
            } else {
                // j < si - 1: this entry was in the previous prefix
                assert(step_target(plan[j]) != step_target(plan[si - 1]));
                assert(e != target);
                // e != target, so insert at target doesn't change e's entry
                assert(base_resolved[e] == base_prev[e]);
                assert(ext_resolved[e] == ext_prev[e]);
                // base_prev.dom().contains(e) from Map::insert semantics
                assert(base_prev.dom().contains(e));
                // Witness for IH
                assert(step_target(plan[j]) == e && is_rational_step(plan[j]) && 0 <= j < si - 1);
                // IH gives: ext_prev[e] ≡ lift_point2(base_prev[e])
                // which equals ext_resolved[e] ≡ lift_point2(base_resolved[e])
            }
        };
    }
}

// ===========================================================================
//  Round 4: Per-step ext satisfaction
// ===========================================================================

// --- Helper: line2_from_points congruence ---

/// If p1 ≡ p2 and q1 ≡ q2, then line2_from_points produces eqv line coefficients.
proof fn lemma_line2_from_points_congruence<T: OrderedField>(
    p1: Point2<T>, q1: Point2<T>, p2: Point2<T>, q2: Point2<T>,
)
    requires p1.eqv(p2), q1.eqv(q2),
    ensures {
        let l1 = line2_from_points(p1, q1);
        let l2 = line2_from_points(p2, q2);
        l1.a.eqv(l2.a) && l1.b.eqv(l2.b) && l1.c.eqv(l2.c)
    },
{
    // a = (q.y - p.y).neg()
    additive_group_lemmas::lemma_sub_congruence(q1.y, q2.y, p1.y, p2.y);
    additive_group_lemmas::lemma_neg_congruence(q1.y.sub(p1.y), q2.y.sub(p2.y));
    // b = q.x - p.x
    additive_group_lemmas::lemma_sub_congruence(q1.x, q2.x, p1.x, p2.x);
    // c = (a * p.x + b * p.y).neg()
    let a1 = q1.y.sub(p1.y).neg();
    let a2 = q2.y.sub(p2.y).neg();
    let b1v = q1.x.sub(p1.x);
    let b2v = q2.x.sub(p2.x);
    ring_lemmas::lemma_mul_congruence(a1, a2, p1.x, p2.x);
    ring_lemmas::lemma_mul_congruence(b1v, b2v, p1.y, p2.y);
    additive_group_lemmas::lemma_add_congruence(
        a1.mul(p1.x), a2.mul(p2.x), b1v.mul(p1.y), b2v.mul(p2.y));
    additive_group_lemmas::lemma_neg_congruence(
        a1.mul(p1.x).add(b1v.mul(p1.y)),
        a2.mul(p2.x).add(b2v.mul(p2.y)));
}

// --- Helper: sq_dist_2d congruence ---

/// If p1 ≡ p2 and q1 ≡ q2, then sq_dist_2d(p1,q1) ≡ sq_dist_2d(p2,q2).
proof fn lemma_sq_dist_congruence<T: OrderedField>(
    p1: Point2<T>, q1: Point2<T>, p2: Point2<T>, q2: Point2<T>,
)
    requires p1.eqv(p2), q1.eqv(q2),
    ensures sq_dist_2d(p1, q1).eqv(sq_dist_2d(p2, q2)),
{
    // sq_dist_2d(p, q) = norm_sq(sub2(p, q))
    // sub2 components: p.x-q.x, p.y-q.y
    additive_group_lemmas::lemma_sub_congruence(p1.x, p2.x, q1.x, q2.x);
    additive_group_lemmas::lemma_sub_congruence(p1.y, p2.y, q1.y, q2.y);
    // Vec2 eqv is component-wise
    let v1 = sub2(p1, q1);
    let v2 = sub2(p2, q2);
    assert(v1.eqv(v2));
    lemma_vec2_norm_sq_congruence(v1, v2);
}

// --- Helper: reflect_point_across_line congruence ---

/// For non-degenerate axis, reflect_point_across_line is congruent in all inputs.
proof fn lemma_reflect_congruence<T: OrderedField>(
    p1: Point2<T>, a1: Point2<T>, b1: Point2<T>,
    p2: Point2<T>, a2: Point2<T>, b2: Point2<T>,
)
    requires
        p1.eqv(p2), a1.eqv(a2), b1.eqv(b2),
        // Non-degeneracy: axis has nonzero length
        {
            let d = sub2(b1, a1);
            !d.x.mul(d.x).add(d.y.mul(d.y)).eqv(T::zero())
        },
    ensures
        reflect_point_across_line(p1, a1, b1).eqv(
            reflect_point_across_line(p2, a2, b2)),
{
    // d = sub2(line_b, line_a): eqv from sub_congruence
    additive_group_lemmas::lemma_sub_congruence(b1.x, b2.x, a1.x, a2.x);
    additive_group_lemmas::lemma_sub_congruence(b1.y, b2.y, a1.y, a2.y);
    let d1 = sub2(b1, a1);
    let d2 = sub2(b2, a2);

    // pa = sub2(p, line_a)
    additive_group_lemmas::lemma_sub_congruence(p1.x, p2.x, a1.x, a2.x);
    additive_group_lemmas::lemma_sub_congruence(p1.y, p2.y, a1.y, a2.y);
    let pa1 = sub2(p1, a1);
    let pa2 = sub2(p2, a2);

    // dot_dd = d.x*d.x + d.y*d.y = norm_sq(d)
    assert(d1.eqv(d2));
    lemma_vec2_norm_sq_congruence(d1, d2);
    let dd1 = d1.x.mul(d1.x).add(d1.y.mul(d1.y));
    let dd2 = d2.x.mul(d2.x).add(d2.y.mul(d2.y));

    // dot_pad = pa.x*d.x + pa.y*d.y = dot(pa, d)
    assert(pa1.eqv(pa2));
    lemma_vec2_dot_congruence(pa1, pa2, d1, d2);
    let pad1 = pa1.x.mul(d1.x).add(pa1.y.mul(d1.y));
    let pad2 = pa2.x.mul(d2.x).add(pa2.y.mul(d2.y));

    // !dd1.eqv(zero) — from precondition
    // !dd2.eqv(zero) — from dd1 ≡ dd2, if dd2 ≡ 0 then dd1 ≡ 0 contradiction
    assert(!dd2.eqv(T::zero())) by {
        if dd2.eqv(T::zero()) {
            // dd1 ≡ dd2 (from norm_sq_congruence), dd2 ≡ zero
            T::axiom_eqv_transitive(dd1, dd2, T::zero());
            // dd1 ≡ zero — contradicts precondition
        }
    };

    // t = dot_pad / dot_dd
    lemma_div_congruence(pad1, pad2, dd1, dd2);
    let t1 = pad1.div(dd1);
    let t2 = pad2.div(dd2);

    // proj_x = line_a.x + t * d.x
    ring_lemmas::lemma_mul_congruence(t1, t2, d1.x, d2.x);
    additive_group_lemmas::lemma_add_congruence(a1.x, a2.x, t1.mul(d1.x), t2.mul(d2.x));
    // proj_y = line_a.y + t * d.y
    ring_lemmas::lemma_mul_congruence(t1, t2, d1.y, d2.y);
    additive_group_lemmas::lemma_add_congruence(a1.y, a2.y, t1.mul(d1.y), t2.mul(d2.y));

    let proj_x1 = a1.x.add(t1.mul(d1.x));
    let proj_x2 = a2.x.add(t2.mul(d2.x));
    let proj_y1 = a1.y.add(t1.mul(d1.y));
    let proj_y2 = a2.y.add(t2.mul(d2.y));

    // two = one + one — same for both
    let two = T::one().add(T::one());
    T::axiom_eqv_reflexive(two);

    // result.x = two * proj_x - p.x
    ring_lemmas::lemma_mul_congruence(two, two, proj_x1, proj_x2);
    additive_group_lemmas::lemma_sub_congruence(
        two.mul(proj_x1), two.mul(proj_x2), p1.x, p2.x);
    // result.y = two * proj_y - p.y
    ring_lemmas::lemma_mul_congruence(two, two, proj_y1, proj_y2);
    additive_group_lemmas::lemma_sub_congruence(
        two.mul(proj_y1), two.mul(proj_y2), p1.y, p2.y);
}

// --- Non-degeneracy predicate for Symmetric constraints ---

/// For Symmetric constraints, the axis must be non-degenerate (axis_a ≠ axis_b
/// position-wise) for locus congruence to hold. True for all other constraints.
pub open spec fn constraint_locus_nondegenerate<T: OrderedField>(
    c: Constraint<T>, resolved: ResolvedPoints<T>, target: EntityId,
) -> bool {
    match c {
        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            if target == point && resolved.dom().contains(axis_a)
                && resolved.dom().contains(axis_b) {
                let d = sub2(resolved[axis_b], resolved[axis_a]);
                !d.x.mul(d.x).add(d.y.mul(d.y)).eqv(T::zero())
            } else { true }
        }
        _ => true,
    }
}

// --- Main resolved map congruence lemma ---

/// Two resolved maps with the same domain and eqv values at all non-target
/// constraint entities produce locus_eqv constraint_to_locus results.
pub proof fn lemma_constraint_to_locus_resolved_congruence<T: OrderedField>(
    c: Constraint<T>,
    r1: ResolvedPoints<T>,
    r2: ResolvedPoints<T>,
    target: EntityId,
)
    requires
        r1.dom() =~= r2.dom(),
        constraint_well_formed(c),
        forall|e: EntityId|
            constraint_entities(c).contains(e) && e != target && r1.dom().contains(e)
            ==> #[trigger] r1[e].eqv(r2[e]),
        constraint_locus_nondegenerate(c, r1, target),
    ensures
        locus_eqv(constraint_to_locus(c, r1, target), constraint_to_locus(c, r2, target)),
{
    match c {
        Constraint::Coincident { a, b } => {
            if target == a && r1.dom().contains(b) {
                assert(r1[b].eqv(r2[b]));
            } else if target == b && r1.dom().contains(a) {
                assert(r1[a].eqv(r2[a]));
            }
        }
        Constraint::DistanceSq { a, b, dist_sq } => {
            if target == a && r1.dom().contains(b) {
                assert(r1[b].eqv(r2[b]));
                T::axiom_eqv_reflexive(dist_sq);
            } else if target == b && r1.dom().contains(a) {
                assert(r1[a].eqv(r2[a]));
                T::axiom_eqv_reflexive(dist_sq);
            }
        }
        Constraint::FixedX { point, x } => {
            if target == point {
                T::axiom_eqv_reflexive(T::one());
                T::axiom_eqv_reflexive(T::zero());
                T::axiom_eqv_reflexive(x.neg());
            }
        }
        Constraint::FixedY { point, y } => {
            if target == point {
                T::axiom_eqv_reflexive(T::zero());
                T::axiom_eqv_reflexive(T::one());
                T::axiom_eqv_reflexive(y.neg());
            }
        }
        Constraint::SameX { a, b } => {
            if target == a && r1.dom().contains(b) {
                assert(r1[b].eqv(r2[b]));
                T::axiom_eqv_reflexive(T::one());
                T::axiom_eqv_reflexive(T::zero());
                additive_group_lemmas::lemma_neg_congruence(r1[b].x, r2[b].x);
            } else if target == b && r1.dom().contains(a) {
                assert(r1[a].eqv(r2[a]));
                T::axiom_eqv_reflexive(T::one());
                T::axiom_eqv_reflexive(T::zero());
                additive_group_lemmas::lemma_neg_congruence(r1[a].x, r2[a].x);
            }
        }
        Constraint::SameY { a, b } => {
            if target == a && r1.dom().contains(b) {
                assert(r1[b].eqv(r2[b]));
                T::axiom_eqv_reflexive(T::zero());
                T::axiom_eqv_reflexive(T::one());
                additive_group_lemmas::lemma_neg_congruence(r1[b].y, r2[b].y);
            } else if target == b && r1.dom().contains(a) {
                assert(r1[a].eqv(r2[a]));
                T::axiom_eqv_reflexive(T::zero());
                T::axiom_eqv_reflexive(T::one());
                additive_group_lemmas::lemma_neg_congruence(r1[a].y, r2[a].y);
            }
        }
        Constraint::PointOnLine { point, line_a, line_b } => {
            if target == point && r1.dom().contains(line_a) && r1.dom().contains(line_b) {
                assert(r1[line_a].eqv(r2[line_a]));
                assert(r1[line_b].eqv(r2[line_b]));
                lemma_line2_from_points_congruence(
                    r1[line_a], r1[line_b], r2[line_a], r2[line_b]);
            }
        }
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            if target == a1 && r1.dom().contains(a2) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a2].eqv(r2[a2]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                lemma_sq_dist_congruence(r1[b1], r1[b2], r2[b1], r2[b2]);
            } else if target == a2 && r1.dom().contains(a1) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a1].eqv(r2[a1]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                lemma_sq_dist_congruence(r1[b1], r1[b2], r2[b1], r2[b2]);
            }
        }
        Constraint::Midpoint { mid, a, b } => {
            lemma_two_ne_zero::<T>();
            let two = T::one().add(T::one());
            T::axiom_eqv_reflexive(two);
            if target == mid && r1.dom().contains(a) && r1.dom().contains(b) {
                assert(r1[a].eqv(r2[a]));
                assert(r1[b].eqv(r2[b]));
                additive_group_lemmas::lemma_add_congruence(r1[a].x, r2[a].x, r1[b].x, r2[b].x);
                lemma_div_congruence(
                    r1[a].x.add(r1[b].x), r2[a].x.add(r2[b].x), two, two);
                additive_group_lemmas::lemma_add_congruence(r1[a].y, r2[a].y, r1[b].y, r2[b].y);
                lemma_div_congruence(
                    r1[a].y.add(r1[b].y), r2[a].y.add(r2[b].y), two, two);
            } else if target == a && r1.dom().contains(mid) && r1.dom().contains(b) {
                assert(r1[mid].eqv(r2[mid]));
                assert(r1[b].eqv(r2[b]));
                ring_lemmas::lemma_mul_congruence(two, two, r1[mid].x, r2[mid].x);
                additive_group_lemmas::lemma_sub_congruence(
                    two.mul(r1[mid].x), two.mul(r2[mid].x), r1[b].x, r2[b].x);
                ring_lemmas::lemma_mul_congruence(two, two, r1[mid].y, r2[mid].y);
                additive_group_lemmas::lemma_sub_congruence(
                    two.mul(r1[mid].y), two.mul(r2[mid].y), r1[b].y, r2[b].y);
            } else if target == b && r1.dom().contains(mid) && r1.dom().contains(a) {
                assert(r1[mid].eqv(r2[mid]));
                assert(r1[a].eqv(r2[a]));
                ring_lemmas::lemma_mul_congruence(two, two, r1[mid].x, r2[mid].x);
                additive_group_lemmas::lemma_sub_congruence(
                    two.mul(r1[mid].x), two.mul(r2[mid].x), r1[a].x, r2[a].x);
                ring_lemmas::lemma_mul_congruence(two, two, r1[mid].y, r2[mid].y);
                additive_group_lemmas::lemma_sub_congruence(
                    two.mul(r1[mid].y), two.mul(r2[mid].y), r1[a].y, r2[a].y);
            }
        }
        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            if target == a1 && r1.dom().contains(a2) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a2].eqv(r2[a2]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                additive_group_lemmas::lemma_sub_congruence(r1[b2].x, r2[b2].x, r1[b1].x, r2[b1].x);
                additive_group_lemmas::lemma_sub_congruence(r1[b2].y, r2[b2].y, r1[b1].y, r2[b1].y);
                let db1 = sub2(r1[b2], r1[b1]);
                let db2 = sub2(r2[b2], r2[b1]);
                ring_lemmas::lemma_mul_congruence(db1.x, db2.x, r1[a2].x, r2[a2].x);
                ring_lemmas::lemma_mul_congruence(db1.y, db2.y, r1[a2].y, r2[a2].y);
                additive_group_lemmas::lemma_add_congruence(
                    db1.x.mul(r1[a2].x), db2.x.mul(r2[a2].x),
                    db1.y.mul(r1[a2].y), db2.y.mul(r2[a2].y));
                additive_group_lemmas::lemma_neg_congruence(
                    db1.x.mul(r1[a2].x).add(db1.y.mul(r1[a2].y)),
                    db2.x.mul(r2[a2].x).add(db2.y.mul(r2[a2].y)));
            } else if target == a2 && r1.dom().contains(a1) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a1].eqv(r2[a1]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                additive_group_lemmas::lemma_sub_congruence(r1[b2].x, r2[b2].x, r1[b1].x, r2[b1].x);
                additive_group_lemmas::lemma_sub_congruence(r1[b2].y, r2[b2].y, r1[b1].y, r2[b1].y);
                let db1 = sub2(r1[b2], r1[b1]);
                let db2 = sub2(r2[b2], r2[b1]);
                ring_lemmas::lemma_mul_congruence(db1.x, db2.x, r1[a1].x, r2[a1].x);
                ring_lemmas::lemma_mul_congruence(db1.y, db2.y, r1[a1].y, r2[a1].y);
                additive_group_lemmas::lemma_add_congruence(
                    db1.x.mul(r1[a1].x), db2.x.mul(r2[a1].x),
                    db1.y.mul(r1[a1].y), db2.y.mul(r2[a1].y));
                additive_group_lemmas::lemma_neg_congruence(
                    db1.x.mul(r1[a1].x).add(db1.y.mul(r1[a1].y)),
                    db2.x.mul(r2[a1].x).add(db2.y.mul(r2[a1].y)));
            }
        }
        Constraint::Parallel { a1, a2, b1, b2 } => {
            if target == a1 && r1.dom().contains(a2) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a2].eqv(r2[a2]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                additive_group_lemmas::lemma_sub_congruence(r1[b2].x, r2[b2].x, r1[b1].x, r2[b1].x);
                additive_group_lemmas::lemma_sub_congruence(r1[b2].y, r2[b2].y, r1[b1].y, r2[b1].y);
                let db1 = sub2(r1[b2], r1[b1]);
                let db2 = sub2(r2[b2], r2[b1]);
                additive_group_lemmas::lemma_neg_congruence(db1.x, db2.x);
                ring_lemmas::lemma_mul_congruence(db1.y, db2.y, r1[a2].x, r2[a2].x);
                ring_lemmas::lemma_mul_congruence(db1.x.neg(), db2.x.neg(), r1[a2].y, r2[a2].y);
                additive_group_lemmas::lemma_add_congruence(
                    db1.y.mul(r1[a2].x), db2.y.mul(r2[a2].x),
                    db1.x.neg().mul(r1[a2].y), db2.x.neg().mul(r2[a2].y));
                additive_group_lemmas::lemma_neg_congruence(
                    db1.y.mul(r1[a2].x).add(db1.x.neg().mul(r1[a2].y)),
                    db2.y.mul(r2[a2].x).add(db2.x.neg().mul(r2[a2].y)));
            } else if target == a2 && r1.dom().contains(a1) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a1].eqv(r2[a1]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                additive_group_lemmas::lemma_sub_congruence(r1[b2].x, r2[b2].x, r1[b1].x, r2[b1].x);
                additive_group_lemmas::lemma_sub_congruence(r1[b2].y, r2[b2].y, r1[b1].y, r2[b1].y);
                let db1 = sub2(r1[b2], r1[b1]);
                let db2 = sub2(r2[b2], r2[b1]);
                additive_group_lemmas::lemma_neg_congruence(db1.x, db2.x);
                ring_lemmas::lemma_mul_congruence(db1.y, db2.y, r1[a1].x, r2[a1].x);
                ring_lemmas::lemma_mul_congruence(db1.x.neg(), db2.x.neg(), r1[a1].y, r2[a1].y);
                additive_group_lemmas::lemma_add_congruence(
                    db1.y.mul(r1[a1].x), db2.y.mul(r2[a1].x),
                    db1.x.neg().mul(r1[a1].y), db2.x.neg().mul(r2[a1].y));
                additive_group_lemmas::lemma_neg_congruence(
                    db1.y.mul(r1[a1].x).add(db1.x.neg().mul(r1[a1].y)),
                    db2.y.mul(r2[a1].x).add(db2.x.neg().mul(r2[a1].y)));
            }
        }
        Constraint::Collinear { a, b, c } => {
            if target == c && r1.dom().contains(a) && r1.dom().contains(b) {
                assert(r1[a].eqv(r2[a]));
                assert(r1[b].eqv(r2[b]));
                lemma_line2_from_points_congruence(r1[a], r1[b], r2[a], r2[b]);
            } else if target == a && r1.dom().contains(b) && r1.dom().contains(c) {
                assert(r1[b].eqv(r2[b]));
                assert(r1[c].eqv(r2[c]));
                lemma_line2_from_points_congruence(r1[b], r1[c], r2[b], r2[c]);
            } else if target == b && r1.dom().contains(a) && r1.dom().contains(c) {
                assert(r1[a].eqv(r2[a]));
                assert(r1[c].eqv(r2[c]));
                lemma_line2_from_points_congruence(r1[a], r1[c], r2[a], r2[c]);
            }
        }
        Constraint::PointOnCircle { point, center, radius_point } => {
            if target == point && r1.dom().contains(center) && r1.dom().contains(radius_point) {
                assert(r1[center].eqv(r2[center]));
                assert(r1[radius_point].eqv(r2[radius_point]));
                lemma_sq_dist_congruence(r1[radius_point], r1[center], r2[radius_point], r2[center]);
            }
        }
        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            if target == point && r1.dom().contains(original)
                && r1.dom().contains(axis_a) && r1.dom().contains(axis_b) {
                assert(r1[original].eqv(r2[original]));
                assert(r1[axis_a].eqv(r2[axis_a]));
                assert(r1[axis_b].eqv(r2[axis_b]));
                lemma_reflect_congruence(
                    r1[original], r1[axis_a], r1[axis_b],
                    r2[original], r2[axis_a], r2[axis_b]);
            }
        }
        Constraint::FixedPoint { point, x, y } => {
            if target == point {
                T::axiom_eqv_reflexive(x);
                T::axiom_eqv_reflexive(y);
            }
        }
        Constraint::Ratio { a1, a2, b1, b2, ratio_sq } => {
            if target == a1 && r1.dom().contains(a2) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a2].eqv(r2[a2]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                lemma_sq_dist_congruence(r1[b1], r1[b2], r2[b1], r2[b2]);
                T::axiom_eqv_reflexive(ratio_sq);
                ring_lemmas::lemma_mul_congruence(ratio_sq, ratio_sq,
                    sq_dist_2d(r1[b1], r1[b2]), sq_dist_2d(r2[b1], r2[b2]));
            } else if target == a2 && r1.dom().contains(a1) && r1.dom().contains(b1) && r1.dom().contains(b2) {
                assert(r1[a1].eqv(r2[a1]));
                assert(r1[b1].eqv(r2[b1]));
                assert(r1[b2].eqv(r2[b2]));
                lemma_sq_dist_congruence(r1[b1], r1[b2], r2[b1], r2[b2]);
                T::axiom_eqv_reflexive(ratio_sq);
                ring_lemmas::lemma_mul_congruence(ratio_sq, ratio_sq,
                    sq_dist_2d(r1[b1], r1[b2]), sq_dist_2d(r2[b1], r2[b2]));
            }
        }
        Constraint::Tangent { .. } => {}
        Constraint::CircleTangent { .. } => {}
        Constraint::Angle { .. } => {}
    }
}

// --- Per-constraint ext satisfaction for rational steps ---

/// Per-constraint satisfaction at extension level for rational steps.
/// Chains: base satisfaction → lift preserves → point congruence → resolved
/// map congruence → lift_constraint_to_locus → locus_eqv transfer.
proof fn lemma_rational_step_ext_locus_single<R: PositiveRadicand<RationalModel>>(
    step: ConstructionStep<RationalModel>,
    c: Constraint<RationalModel>,
    base_resolved: ResolvedPoints<RationalModel>,
    ext_resolved: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        is_rational_step(step),
        step_geometrically_valid(step),
        constraint_well_formed(c),
        // Base satisfaction
        point_satisfies_locus(
            constraint_to_locus(c, base_resolved, step_target(step)),
            execute_step(step)),
        // Domain equality
        ext_resolved.dom() =~= lift_resolved_map::<RationalModel, R>(base_resolved).dom(),
        // Entry-wise eqv at non-target constraint entities
        forall|e: EntityId|
            constraint_entities(c).contains(e) && e != step_target(step)
            && ext_resolved.dom().contains(e)
            ==> ext_resolved[e].eqv(
                lift_resolved_map::<RationalModel, R>(base_resolved)[e]),
        // For lemma_lift_constraint_to_locus
        constraint_entities(c).contains(step_target(step)),
        constraint_entities(c).remove(step_target(step)).subset_of(base_resolved.dom()),
        !base_resolved.dom().contains(step_target(step)),
        // Non-degeneracy for Symmetric at ext level
        constraint_locus_nondegenerate(
            lift_constraint::<RationalModel, R>(c), ext_resolved, step_target(step)),
    ensures
        point_satisfies_locus(
            constraint_to_locus(
                lift_constraint::<RationalModel, R>(c), ext_resolved,
                step_target(lift_construction_step::<RationalModel, R>(step))),
            execute_step(lift_construction_step::<RationalModel, R>(step))),
{
    let target = step_target(step);
    lemma_lift_step_target::<RationalModel, R>(step);

    let lift_step = lift_construction_step::<RationalModel, R>(step);
    let ext_locus = constraint_to_locus(
        lift_constraint::<RationalModel, R>(c), ext_resolved, target);
    let lift_resolved_locus = constraint_to_locus(
        lift_constraint::<RationalModel, R>(c),
        lift_resolved_map::<RationalModel, R>(base_resolved), target);
    let lifted_base_locus = lift_locus::<RationalModel, R>(
        constraint_to_locus(c, base_resolved, target));

    // 1. Resolved map congruence: ext_locus locus_eqv lift_resolved_locus
    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);
    lemma_lift_constraint_well_formed::<RationalModel, R>(c);
    lemma_constraint_to_locus_resolved_congruence(
        lift_constraint::<RationalModel, R>(c),
        ext_resolved,
        lift_resolved_map::<RationalModel, R>(base_resolved),
        target);

    // 2. lift_resolved_locus locus_eqv lifted_base_locus
    lemma_lift_constraint_to_locus::<RationalModel, R>(c, base_resolved, target);

    // 3. ext_locus locus_eqv lifted_base_locus (by transitivity)
    lemma_locus_eqv_transitive(ext_locus, lift_resolved_locus, lifted_base_locus);

    // 4. Base satisfaction → lift preserves → execute_step(lift_step) satisfies lifted_base_locus
    lemma_lift_preserves_satisfaction::<RationalModel, R>(
        constraint_to_locus(c, base_resolved, target), execute_step(step));
    lemma_rational_step_execute_lift_eqv::<RationalModel, R>(step);
    lemma_point_satisfies_locus_congruent(
        lifted_base_locus,
        lift_point2::<RationalModel, R>(execute_step(step)),
        execute_step(lift_step));

    // 5. Transfer: lifted_base_locus → ext_locus
    lemma_locus_eqv_symmetric(ext_locus, lifted_base_locus);
    lemma_point_satisfies_locus_eqv(
        lifted_base_locus, ext_locus, execute_step(lift_step));
}

// --- Helper: in an independent plan, constraint inputs agree with lifted base ---

/// For a step si in a fully independent plan, any constraint entity e (e != target)
/// that's resolved before step si has its extension-level value eqv to the
/// lifted base value. This is because e is a rational entry (not a circle target).
proof fn lemma_independent_entry_agrees<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
    ci: int,
    e: EntityId,
)
    requires
        0 <= si < plan.len(),
        0 <= ci < constraints.len(),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        is_fully_independent_plan(plan, constraints),
        constraint_entities(constraints[ci]).contains(step_target(plan[si])),
        constraint_entities(constraints[ci]).contains(e),
        e != step_target(plan[si]),
        execute_plan(plan.take(si as int)).dom().contains(e),
    ensures
        execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int))[e]
            .eqv(lift_point2::<RationalModel, R>(
                execute_plan(plan.take(si as int))[e])),
{
    // e is in the domain of plan.take(si), so some step j < si placed it
    lemma_execute_plan_dom::<RationalModel>(plan.take(si as int), e);
    let j = choose|j: int| 0 <= j < (plan.take(si as int)).len()
        && step_target(plan.take(si as int)[j]) == e;
    assert(0 <= j < si);
    assert(step_target(plan[j]) == e);

    // From is_fully_independent_plan: e is not a circle target
    // (ci has target plan[si], e is another entity of ci)
    assert(!circle_targets(plan).contains(e));

    // Since e is not a circle target and plan[j] targets e, plan[j] is rational
    if !is_rational_step(plan[j]) {
        // Contradiction: e would be in circle_targets
        assert(circle_targets(plan).contains(e));
    }
    assert(is_rational_step(plan[j]));

    // From Round 3: rational entries agree
    lemma_resolved_maps_agree_rational_entries::<RationalModel, R>(plan, si);
}

// --- Circle step: execute_step satisfies built-in loci ---

/// For a well-formed circle step, execute_step satisfies the step's built-in
/// geometric loci (from the choose axiom).
proof fn lemma_circle_step_built_in_satisfied<T: OrderedField>(
    step: ConstructionStep<T>,
)
    requires
        !is_rational_step(step),
        step_well_formed(step),
    ensures
        match step {
            ConstructionStep::CircleLine { circle, line, .. } =>
                point_satisfies_locus(Locus2d::OnCircle(circle), execute_step(step))
                && point_satisfies_locus(Locus2d::OnLine(line), execute_step(step)),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                point_satisfies_locus(Locus2d::OnCircle(circle1), execute_step(step))
                && point_satisfies_locus(Locus2d::OnCircle(circle2), execute_step(step)),
            _ => true,
        },
{
    // step_well_formed gives exists|p| on_circle && on_line (or on_c1 && on_c2)
    // execute_step returns choose|p| with same predicate
    // By choose axiom: if exists|p| P(p), then P(choose|p| P(p))
    // Z3 should handle this automatically from the definitions
}

// --- Nontrivial locus implies entity coverage ---

/// If constraint_to_locus produces a nontrivial locus, then target is a
/// constraint entity and all other constraint entities are resolved.
proof fn lemma_nontrivial_implies_entity_coverage<T: OrderedField>(
    c: Constraint<T>,
    resolved: ResolvedPoints<T>,
    target: EntityId,
)
    requires
        locus_is_nontrivial(constraint_to_locus(c, resolved, target)),
    ensures
        constraint_entities(c).contains(target),
        constraint_entities(c).remove(target).subset_of(resolved.dom()),
{
    // Each variant: nontrivial means the non-FullPlane branch fired,
    // which implies target matches an entity and all others are in dom.
    match c {
        Constraint::Coincident { a, b } => {}
        Constraint::DistanceSq { a, b, .. } => {}
        Constraint::FixedX { point, .. } => {}
        Constraint::FixedY { point, .. } => {}
        Constraint::SameX { a, b } => {}
        Constraint::SameY { a, b } => {}
        Constraint::PointOnLine { point, line_a, line_b } => {}
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {}
        Constraint::Midpoint { mid, a, b } => {}
        Constraint::Perpendicular { a1, a2, b1, b2 } => {}
        Constraint::Parallel { a1, a2, b1, b2 } => {}
        Constraint::Collinear { .. } => {}
        Constraint::PointOnCircle { point, center, radius_point } => {}
        Constraint::Symmetric { point, original, axis_a, axis_b } => {}
        Constraint::FixedPoint { point, .. } => {}
        Constraint::Ratio { a1, a2, b1, b2, .. } => {}
        Constraint::Tangent { .. } => {}
        Constraint::CircleTangent { .. } => {}
        Constraint::Angle { .. } => {}
    }
}

// --- Lifting preserves locus nontriviality ---

/// Lifting a constraint and resolved map preserves locus nontriviality.
/// Cross-type result: base-field and lifted locus have same FullPlane/nontrivial classification.
proof fn lemma_lift_preserves_nontriviality<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
    resolved: ResolvedPoints<F>,
    target: EntityId,
)
    ensures
        locus_is_nontrivial(constraint_to_locus(c, resolved, target))
        == locus_is_nontrivial(constraint_to_locus(
            lift_constraint::<F, R>(c),
            lift_resolved_map::<F, R>(resolved), target)),
{
    lemma_lift_resolved_map_dom::<F, R>(resolved);
    // Both calls make the same entity/domain checks (lift preserves IDs and domain).
    match c {
        Constraint::Coincident { a, b } => {}
        Constraint::DistanceSq { a, b, .. } => {}
        Constraint::FixedX { point, .. } => {}
        Constraint::FixedY { point, .. } => {}
        Constraint::SameX { a, b } => {}
        Constraint::SameY { a, b } => {}
        Constraint::PointOnLine { point, line_a, line_b } => {}
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {}
        Constraint::Midpoint { mid, a, b } => {}
        Constraint::Perpendicular { a1, a2, b1, b2 } => {}
        Constraint::Parallel { a1, a2, b1, b2 } => {}
        Constraint::Collinear { .. } => {}
        Constraint::PointOnCircle { point, center, radius_point } => {}
        Constraint::Symmetric { point, original, axis_a, axis_b } => {}
        Constraint::FixedPoint { point, .. } => {}
        Constraint::Ratio { a1, a2, b1, b2, .. } => {}
        Constraint::Tangent { .. } => {}
        Constraint::CircleTangent { .. } => {}
        Constraint::Angle { .. } => {}
    }
}

// --- Non-degeneracy transfer from base to extension level ---

/// Transfers constraint_locus_nondegenerate from base to extension level.
/// For non-Symmetric: trivially true at ext level.
/// For Symmetric: uses entry-wise eqv to transfer norm_sq ≢ 0.
proof fn lemma_nondegen_transfers_to_ext<R: PositiveRadicand<RationalModel>>(
    c: Constraint<RationalModel>,
    base_resolved: ResolvedPoints<RationalModel>,
    ext_resolved: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    target: EntityId,
)
    requires
        constraint_locus_nondegenerate(c, base_resolved, target),
        constraint_well_formed(c),
        ext_resolved.dom() =~= base_resolved.dom(),
        forall|e: EntityId|
            constraint_entities(c).contains(e) && e != target
            && ext_resolved.dom().contains(e)
            ==> ext_resolved[e].eqv(
                lift_resolved_map::<RationalModel, R>(base_resolved)[e]),
    ensures
        constraint_locus_nondegenerate(
            lift_constraint::<RationalModel, R>(c), ext_resolved, target),
{
    match c {
        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            if target == point && base_resolved.dom().contains(axis_a)
                && base_resolved.dom().contains(axis_b)
            {
                // constraint_locus_nondegenerate's norm is sq_dist_2d(axis_b, axis_a)
                let base_norm = sq_dist_2d(base_resolved[axis_b], base_resolved[axis_a]);

                // Help Z3 trigger the quantified entry-eqv precondition
                assert(constraint_entities(c).contains(axis_a));
                assert(constraint_entities(c).contains(axis_b));
                assert(axis_a != target);
                assert(axis_b != target);
                assert(ext_resolved.dom().contains(axis_a));
                assert(ext_resolved.dom().contains(axis_b));

                let ext_b = ext_resolved[axis_b];
                let ext_a = ext_resolved[axis_a];
                let lift_b = lift_point2::<RationalModel, R>(base_resolved[axis_b]);
                let lift_a = lift_point2::<RationalModel, R>(base_resolved[axis_a]);

                // Step 1: sq_dist(ext_b, ext_a) ≡ sq_dist(lift_b, lift_a)
                lemma_sq_dist_congruence::<SpecQuadExt<RationalModel, R>>(
                    ext_b, ext_a, lift_b, lift_a);

                // Step 2: sq_dist(lift_b, lift_a) ≡ qext(base_norm)
                lemma_lift_sq_dist_2d_eqv::<RationalModel, R>(
                    base_resolved[axis_b], base_resolved[axis_a]);

                // Step 3: sq_dist(ext_b, ext_a) ≡ qext(base_norm)
                let ext_norm = sq_dist_2d(ext_b, ext_a);
                SpecQuadExt::<RationalModel, R>::axiom_eqv_transitive(
                    ext_norm,
                    sq_dist_2d(lift_b, lift_a),
                    qext_from_rational::<RationalModel, R>(base_norm));

                // Step 4: qext(base_norm) ≢ QExt::zero() → ext_norm ≢ QExt::zero()
                // If ext_norm ≡ 0, then qext(base_norm) ≡ 0 (transitivity),
                // then base_norm ≡ 0 (from re component), contradiction.
                if ext_norm.eqv(SpecQuadExt::<RationalModel, R>::zero()) {
                    SpecQuadExt::<RationalModel, R>::axiom_eqv_symmetric(
                        ext_norm,
                        qext_from_rational::<RationalModel, R>(base_norm));
                    SpecQuadExt::<RationalModel, R>::axiom_eqv_transitive(
                        qext_from_rational::<RationalModel, R>(base_norm),
                        ext_norm,
                        SpecQuadExt::<RationalModel, R>::zero());
                    // qext(base_norm) ≡ 0 → base_norm.eqv(0) from re component
                    lemma_qext_from_rational_re::<RationalModel, R>(base_norm);
                }
            }
        }
        _ => {
            // Non-Symmetric: trivially true at ext level
        }
    }
}

// --- Entry-wise eqv for constraint entities ---

/// In an independent plan, constraint entities at step si have their
/// extension-level values eqv to the lifted base values.
proof fn lemma_constraint_entry_eqv<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
    ci: int,
)
    requires
        0 <= si < plan.len(),
        0 <= ci < constraints.len(),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        is_fully_independent_plan(plan, constraints),
        constraint_entities(constraints[ci]).contains(step_target(plan[si])),
        // Domain equality between ext and base
        execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int)).dom()
            =~= execute_plan(plan.take(si as int)).dom(),
    ensures
        forall|e: EntityId|
            constraint_entities(
                lift_constraint::<RationalModel, R>(constraints[ci])).contains(e)
            && e != step_target(plan[si])
            && execute_plan(
                lift_plan::<RationalModel, R>(plan).take(si as int)).dom().contains(e)
            ==> execute_plan(
                lift_plan::<RationalModel, R>(plan).take(si as int))[e].eqv(
                lift_resolved_map::<RationalModel, R>(
                    execute_plan(plan.take(si as int)))[e]),
{
    lemma_lift_constraint_entities::<RationalModel, R>(constraints[ci]);
    assert forall|e: EntityId|
        constraint_entities(
            lift_constraint::<RationalModel, R>(constraints[ci])).contains(e)
        && e != step_target(plan[si])
        && execute_plan(
            lift_plan::<RationalModel, R>(plan).take(si as int)).dom().contains(e)
    implies execute_plan(
        lift_plan::<RationalModel, R>(plan).take(si as int))[e].eqv(
        lift_resolved_map::<RationalModel, R>(
            execute_plan(plan.take(si as int)))[e])
    by {
        // Domain equality lets us convert ext domain → base domain
        assert(execute_plan(plan.take(si as int)).dom().contains(e));
        lemma_independent_entry_agrees::<R>(plan, constraints, si, ci, e);
    };
}

// --- Rational step: per-ci wrapper ---

/// Complete per-constraint proof for rational steps at the extension level.
/// Uses base satisfaction + entry-wise eqv + nondegen transfer.
proof fn lemma_rational_step_ext_ci<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
    ci: int,
)
    requires
        0 <= si < plan.len(),
        0 <= ci < constraints.len(),
        is_rational_step(plan[si]),
        // Individual conjuncts
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        constraint_well_formed(constraints[ci]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        is_fully_independent_plan(plan, constraints),
        // Base satisfaction for this specific constraint
        point_satisfies_locus(
            constraint_to_locus(constraints[ci],
                execute_plan(plan.take(si as int)), step_target(plan[si])),
            execute_step(plan[si])),
        // Base non-degeneracy for this constraint at this step
        constraint_locus_nondegenerate(
            constraints[ci], execute_plan(plan.take(si as int)), step_target(plan[si])),
        // Domain facts
        execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int)).dom()
            =~= execute_plan(plan.take(si as int)).dom(),
        !execute_plan(plan.take(si as int)).dom().contains(step_target(plan[si])),
        step_well_formed(lift_construction_step::<RationalModel, R>(plan[si])),
        // Nontrivial ext locus
        locus_is_nontrivial(constraint_to_locus(
            lift_constraint::<RationalModel, R>(constraints[ci]),
            execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int)),
            step_target(plan[si]))),
    ensures
        point_satisfies_locus(
            constraint_to_locus(
                lift_constraint::<RationalModel, R>(constraints[ci]),
                execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int)),
                step_target(plan[si])),
            execute_step(lift_construction_step::<RationalModel, R>(plan[si]))),
{
    let target = step_target(plan[si]);
    let base_step = plan[si];
    let lift_step = lift_construction_step::<RationalModel, R>(base_step);
    let base_c = constraints[ci];
    let lift_c = lift_constraint::<RationalModel, R>(base_c);
    let base_resolved = execute_plan(plan.take(si as int));
    let ext_resolved = execute_plan(
        lift_plan::<RationalModel, R>(plan).take(si as int));

    lemma_lift_step_target::<RationalModel, R>(base_step);
    lemma_lift_constraint_entities::<RationalModel, R>(base_c);
    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);

    // 1. Derive base nontriviality from ext nontriviality
    lemma_locus_nontrivial_depends_on_domain(
        lift_c, ext_resolved,
        lift_resolved_map::<RationalModel, R>(base_resolved), target);
    lemma_lift_preserves_nontriviality::<RationalModel, R>(
        base_c, base_resolved, target);

    // 2. Entity coverage from base nontriviality
    lemma_nontrivial_implies_entity_coverage(base_c, base_resolved, target);

    // 3. Entry-wise eqv (extracted to avoid rlimit)
    lemma_constraint_entry_eqv::<R>(plan, constraints, si, ci);

    // 4. Transfer non-degeneracy from base to ext level
    lemma_nondegen_transfers_to_ext::<R>(base_c, base_resolved, ext_resolved, target);

    // 5. Delegate to ext_locus_single
    lemma_rational_step_ext_locus_single::<R>(
        base_step, base_c, base_resolved, ext_resolved);
}

// --- Rational step: ext loci satisfaction ---

/// For a rational step in a structurally sound plan, the lifted step satisfies
/// all constraint loci at the extension level.
proof fn lemma_rational_step_satisfies_ext_loci<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
)
    requires
        0 <= si < plan.len(),
        is_rational_step(plan[si]),
        plan_structurally_sound::<R>(plan, constraints),
    ensures
        step_satisfies_all_constraint_loci(
            lift_plan::<RationalModel, R>(plan)[si],
            lift_constraints::<RationalModel, R>(constraints),
            execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int))),
{
    let target = step_target(plan[si]);
    let base_step = plan[si];
    let lift_step = lift_construction_step::<RationalModel, R>(base_step);
    let base_resolved = execute_plan(plan.take(si as int));
    let ext_resolved = execute_plan(
        lift_plan::<RationalModel, R>(plan).take(si as int));
    let lift_constraints_val = lift_constraints::<RationalModel, R>(constraints);

    assert(lift_plan::<RationalModel, R>(plan)[si] == lift_step);
    lemma_lift_step_target::<RationalModel, R>(base_step);
    lemma_lifted_step_well_formed::<RationalModel, R>(base_step);

    // Domain preservation
    assert(lift_plan::<RationalModel, R>(plan).take(si as int)
        =~= lift_plan::<RationalModel, R>(plan.take(si as int)));
    lemma_lift_plan_domain::<RationalModel, R>(plan.take(si as int));
    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);
    lemma_step_target_not_in_prefix::<RationalModel>(plan, si);

    // Per-constraint satisfaction
    assert forall|ci: int| 0 <= ci < lift_constraints_val.len()
        && locus_is_nontrivial(
            constraint_to_locus(
                #[trigger] lift_constraints_val[ci], ext_resolved,
                step_target(lift_step)))
    implies point_satisfies_locus(
        constraint_to_locus(lift_constraints_val[ci], ext_resolved,
            step_target(lift_step)),
        execute_step(lift_step))
    by {
        assert(lift_constraints_val[ci]
            == lift_constraint::<RationalModel, R>(constraints[ci]));
        assert(constraint_well_formed(constraints[ci]));
        // Extract base satisfaction for this specific ci from
        // step_satisfies_all_constraint_loci (nontrivial → point_satisfies_locus)
        assert(step_satisfies_all_constraint_loci(
            plan[si], constraints, base_resolved));
        lemma_lift_preserves_nontriviality::<RationalModel, R>(
            constraints[ci], base_resolved, target);
        lemma_locus_nontrivial_depends_on_domain(
            lift_constraint::<RationalModel, R>(constraints[ci]),
            ext_resolved,
            lift_resolved_map::<RationalModel, R>(base_resolved), target);
        // Extract base non-degeneracy from plan_structurally_sound
        assert(constraint_locus_nondegenerate(
            constraints[ci], base_resolved, target));
        lemma_rational_step_ext_ci::<R>(plan, constraints, si, ci);
    };

    lemma_nontrivial_loci_imply_all_satisfied(
        lift_step, lift_constraints_val, ext_resolved);
}

// --- Circle step: per-constraint helper ---

/// For a single constraint at a circle step, if the base locus matches the
/// step geometry and we have entry-wise eqv, the ext locus is satisfied.
proof fn lemma_circle_step_ext_single<R: PositiveRadicand<RationalModel>>(
    base_step: ConstructionStep<RationalModel>,
    base_c: Constraint<RationalModel>,
    base_resolved: ResolvedPoints<RationalModel>,
    ext_resolved: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        !is_rational_step(base_step),
        step_well_formed(lift_construction_step::<RationalModel, R>(base_step)),
        constraint_well_formed(base_c),
        // Domain match
        ext_resolved.dom() =~= lift_resolved_map::<RationalModel, R>(base_resolved).dom(),
        !base_resolved.dom().contains(step_target(base_step)),
        // Entry-wise eqv for constraint entities
        forall|e: EntityId|
            constraint_entities(lift_constraint::<RationalModel, R>(base_c)).contains(e)
            && e != step_target(base_step) && ext_resolved.dom().contains(e)
            ==> ext_resolved[e].eqv(
                lift_resolved_map::<RationalModel, R>(base_resolved)[e]),
        // Ext locus is nontrivial
        locus_is_nontrivial(constraint_to_locus(
            lift_constraint::<RationalModel, R>(base_c), ext_resolved,
            step_target(base_step))),
        // Base locus matches step geometry (up to eqv)
        {
            let base_locus = constraint_to_locus(base_c, base_resolved, step_target(base_step));
            match base_step {
                ConstructionStep::CircleLine { circle, line, .. } =>
                    locus_eqv(base_locus, Locus2d::OnCircle(circle))
                    || locus_eqv(base_locus, Locus2d::OnLine(line)),
                ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                    locus_eqv(base_locus, Locus2d::OnCircle(circle1))
                    || locus_eqv(base_locus, Locus2d::OnCircle(circle2)),
                _ => false,
            }
        },
        // For lift_constraint_to_locus
        constraint_entities(base_c).contains(step_target(base_step)),
        constraint_entities(base_c).remove(step_target(base_step))
            .subset_of(base_resolved.dom()),
        // Non-degeneracy
        constraint_locus_nondegenerate(
            lift_constraint::<RationalModel, R>(base_c),
            ext_resolved, step_target(base_step)),
    ensures
        point_satisfies_locus(
            constraint_to_locus(
                lift_constraint::<RationalModel, R>(base_c), ext_resolved,
                step_target(lift_construction_step::<RationalModel, R>(base_step))),
            execute_step(lift_construction_step::<RationalModel, R>(base_step))),
{
    let target = step_target(base_step);
    let lift_step = lift_construction_step::<RationalModel, R>(base_step);
    let lift_c = lift_constraint::<RationalModel, R>(base_c);
    let base_locus = constraint_to_locus(base_c, base_resolved, target);
    let ext_locus = constraint_to_locus(lift_c, ext_resolved, target);

    lemma_lift_step_target::<RationalModel, R>(base_step);
    lemma_circle_step_built_in_satisfied(lift_step);

    // Correspondence: ext_locus ≈ lift_locus(base_locus)
    lemma_lift_constraint_well_formed::<RationalModel, R>(base_c);
    lemma_constraint_to_locus_resolved_congruence(
        lift_c, ext_resolved,
        lift_resolved_map::<RationalModel, R>(base_resolved), target);
    lemma_lift_constraint_to_locus::<RationalModel, R>(
        base_c, base_resolved, target);
    let lift_res_locus = constraint_to_locus(
        lift_c,
        lift_resolved_map::<RationalModel, R>(base_resolved), target);
    let lifted_base = lift_locus::<RationalModel, R>(base_locus);
    lemma_locus_eqv_transitive(ext_locus, lift_res_locus, lifted_base);
    // ext_locus ≈ lifted_base

    // lifted_base matches step's ext locus; execute_step satisfies it
    // Now step_loci_match_geometry gives locus_eqv, so we chain:
    //   ext_locus ≈ lifted_base ≈ lift(step_geom) → step satisfies ext_locus
    match base_step {
        ConstructionStep::CircleLine { circle, line, .. } => {
            if locus_eqv(base_locus, Locus2d::OnCircle(circle)) {
                let step_locus = Locus2d::<RationalModel>::OnCircle(circle);
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnCircle(
                    lift_circle2::<RationalModel, R>(circle));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(base_locus, step_locus);
                // lift(base_locus) ≈ lift(OnCircle(circle)) == sl
                lemma_locus_eqv_transitive(ext_locus, lifted_base, sl);
                lemma_locus_eqv_symmetric(ext_locus, sl);
                lemma_point_satisfies_locus_eqv(
                    sl, ext_locus, execute_step(lift_step));
            } else {
                let step_locus = Locus2d::<RationalModel>::OnLine(line);
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnLine(
                    lift_line2::<RationalModel, R>(line));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(base_locus, step_locus);
                lemma_locus_eqv_transitive(ext_locus, lifted_base, sl);
                lemma_locus_eqv_symmetric(ext_locus, sl);
                lemma_point_satisfies_locus_eqv(
                    sl, ext_locus, execute_step(lift_step));
            }
        }
        ConstructionStep::CircleCircle { circle1, circle2, .. } => {
            if locus_eqv(base_locus, Locus2d::OnCircle(circle1)) {
                let step_locus = Locus2d::<RationalModel>::OnCircle(circle1);
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnCircle(
                    lift_circle2::<RationalModel, R>(circle1));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(base_locus, step_locus);
                lemma_locus_eqv_transitive(ext_locus, lifted_base, sl);
                lemma_locus_eqv_symmetric(ext_locus, sl);
                lemma_point_satisfies_locus_eqv(
                    sl, ext_locus, execute_step(lift_step));
            } else {
                let step_locus = Locus2d::<RationalModel>::OnCircle(circle2);
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnCircle(
                    lift_circle2::<RationalModel, R>(circle2));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(base_locus, step_locus);
                lemma_locus_eqv_transitive(ext_locus, lifted_base, sl);
                lemma_locus_eqv_symmetric(ext_locus, sl);
                lemma_point_satisfies_locus_eqv(
                    sl, ext_locus, execute_step(lift_step));
            }
        }
        _ => {}
    }
}

// --- Circle step: complete per-ci wrapper ---

/// Complete per-constraint proof for circle steps at the extension level.
/// Derives entity coverage from nontriviality, entry agreement from independence,
/// non-degeneracy from variant analysis, and delegates to lemma_circle_step_ext_single.
proof fn lemma_circle_step_ext_ci<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
    ci: int,
)
    requires
        0 <= si < plan.len(),
        0 <= ci < constraints.len(),
        !is_rational_step(plan[si]),
        // Individual conjuncts (avoids unfolding plan_structurally_sound)
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        constraint_well_formed(constraints[ci]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        is_fully_independent_plan(plan, constraints),
        step_loci_match_geometry(
            plan[si], constraints, execute_plan(plan.take(si as int))),
        // Pre-computed domain facts
        execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int)).dom()
            =~= execute_plan(plan.take(si as int)).dom(),
        !execute_plan(plan.take(si as int)).dom().contains(step_target(plan[si])),
        step_well_formed(lift_construction_step::<RationalModel, R>(plan[si])),
        // Nontrivial ext locus
        locus_is_nontrivial(constraint_to_locus(
            lift_constraint::<RationalModel, R>(constraints[ci]),
            execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int)),
            step_target(plan[si]))),
    ensures
        point_satisfies_locus(
            constraint_to_locus(
                lift_constraint::<RationalModel, R>(constraints[ci]),
                execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int)),
                step_target(plan[si])),
            execute_step(lift_construction_step::<RationalModel, R>(plan[si]))),
{
    let target = step_target(plan[si]);
    let base_step = plan[si];
    let lift_step = lift_construction_step::<RationalModel, R>(base_step);
    let base_c = constraints[ci];
    let lift_c = lift_constraint::<RationalModel, R>(base_c);
    let base_resolved = execute_plan(plan.take(si as int));
    let ext_resolved = execute_plan(
        lift_plan::<RationalModel, R>(plan).take(si as int));

    lemma_lift_step_target::<RationalModel, R>(base_step);
    lemma_lift_constraint_entities::<RationalModel, R>(base_c);
    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);

    // 1. Derive base nontriviality from ext nontriviality
    lemma_locus_nontrivial_depends_on_domain(
        lift_c, ext_resolved,
        lift_resolved_map::<RationalModel, R>(base_resolved), target);
    lemma_lift_preserves_nontriviality::<RationalModel, R>(
        base_c, base_resolved, target);

    // 2. Entity coverage from base nontriviality
    lemma_nontrivial_implies_entity_coverage(base_c, base_resolved, target);

    // 3. Entry-wise eqv for constraint entities
    assert forall|e: EntityId|
        constraint_entities(lift_c).contains(e) && e != target
        && ext_resolved.dom().contains(e)
    implies ext_resolved[e].eqv(
        lift_resolved_map::<RationalModel, R>(base_resolved)[e])
    by {
        lemma_independent_entry_agrees::<R>(plan, constraints, si, ci, e);
    };

    // 4. Non-degeneracy + delegation
    match base_c {
        Constraint::Symmetric { .. } => {
            // Symmetric nontrivial base locus is AtPoint.
            // step_loci_match_geometry says OnCircle or OnLine → contradiction.
            assert(locus_is_nontrivial(
                constraint_to_locus(base_c, base_resolved, target)));
        }
        _ => {
            // Non-Symmetric: constraint_locus_nondegenerate trivially true
            lemma_circle_step_ext_single::<R>(
                base_step, base_c, base_resolved, ext_resolved);
        }
    }
}

// --- Circle step: ext loci satisfaction ---

/// For a circle step in a structurally sound plan, the lifted step satisfies
/// all constraint loci at the extension level.
proof fn lemma_circle_step_satisfies_ext_loci<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
)
    requires
        0 <= si < plan.len(),
        !is_rational_step(plan[si]),
        plan_structurally_sound::<R>(plan, constraints),
    ensures
        step_satisfies_all_constraint_loci(
            lift_plan::<RationalModel, R>(plan)[si],
            lift_constraints::<RationalModel, R>(constraints),
            execute_plan(lift_plan::<RationalModel, R>(plan).take(si as int))),
{
    let target = step_target(plan[si]);
    let base_step = plan[si];
    let lift_step = lift_construction_step::<RationalModel, R>(base_step);
    let base_resolved = execute_plan(plan.take(si as int));
    let ext_resolved = execute_plan(
        lift_plan::<RationalModel, R>(plan).take(si as int));
    let lift_constraints_val = lift_constraints::<RationalModel, R>(constraints);

    assert(lift_plan::<RationalModel, R>(plan)[si] == lift_step);
    lemma_lift_step_target::<RationalModel, R>(base_step);
    lemma_lifted_step_well_formed::<RationalModel, R>(base_step);

    // Domain preservation
    assert(lift_plan::<RationalModel, R>(plan).take(si as int)
        =~= lift_plan::<RationalModel, R>(plan.take(si as int)));
    lemma_lift_plan_domain::<RationalModel, R>(plan.take(si as int));
    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);
    lemma_step_target_not_in_prefix::<RationalModel>(plan, si);

    // Per-constraint satisfaction, delegated to lemma_circle_step_ext_ci
    assert forall|ci: int| 0 <= ci < lift_constraints_val.len()
        && locus_is_nontrivial(
            constraint_to_locus(
                #[trigger] lift_constraints_val[ci], ext_resolved,
                step_target(lift_step)))
    implies point_satisfies_locus(
        constraint_to_locus(lift_constraints_val[ci], ext_resolved,
            step_target(lift_step)),
        execute_step(lift_step))
    by {
        assert(lift_constraints_val[ci]
            == lift_constraint::<RationalModel, R>(constraints[ci]));
        // Extract individual conjuncts for lemma_circle_step_ext_ci
        assert(constraint_well_formed(constraints[ci]));
        assert(step_loci_match_geometry(
            plan[si], constraints, base_resolved));
        lemma_circle_step_ext_ci::<R>(plan, constraints, si, ci);
    };

    lemma_nontrivial_loci_imply_all_satisfied(
        lift_step, lift_constraints_val, ext_resolved);
}

// ===========================================================================
//  Nontrivial locus counting (domain-only classification)
// ===========================================================================

/// Whether constraint `c` imposes a nontrivial locus on `target` given that
/// entities in `resolved_dom` are resolved. This depends ONLY on entity IDs
/// and domain membership — no point values needed.
///
/// Defined per-variant to avoid universal quantifiers (`subset_of`) that
/// impede Z3 automation.
pub open spec fn is_nontrivial_for_target<T: OrderedField>(
    c: Constraint<T>,
    target: EntityId,
    resolved_dom: Set<EntityId>,
) -> bool {
    !resolved_dom.contains(target) && match c {
        Constraint::Coincident { a, b } =>
            (target == a && resolved_dom.contains(b))
            || (target == b && resolved_dom.contains(a)),
        Constraint::DistanceSq { a, b, .. } =>
            (target == a && resolved_dom.contains(b))
            || (target == b && resolved_dom.contains(a)),
        Constraint::FixedX { point, .. } =>
            target == point,
        Constraint::FixedY { point, .. } =>
            target == point,
        Constraint::SameX { a, b } =>
            (target == a && resolved_dom.contains(b))
            || (target == b && resolved_dom.contains(a)),
        Constraint::SameY { a, b } =>
            (target == a && resolved_dom.contains(b))
            || (target == b && resolved_dom.contains(a)),
        Constraint::PointOnLine { point, line_a, line_b } =>
            target == point && resolved_dom.contains(line_a) && resolved_dom.contains(line_b),
        Constraint::EqualLengthSq { a1, a2, b1, b2 } =>
            (target == a1 && resolved_dom.contains(a2) && resolved_dom.contains(b1) && resolved_dom.contains(b2))
            || (target == a2 && resolved_dom.contains(a1) && resolved_dom.contains(b1) && resolved_dom.contains(b2)),
        Constraint::Midpoint { mid, a, b } =>
            (target == mid && resolved_dom.contains(a) && resolved_dom.contains(b))
            || (target == a && resolved_dom.contains(mid) && resolved_dom.contains(b))
            || (target == b && resolved_dom.contains(mid) && resolved_dom.contains(a)),
        Constraint::Perpendicular { a1, a2, b1, b2 } =>
            (target == a1 && resolved_dom.contains(a2) && resolved_dom.contains(b1) && resolved_dom.contains(b2))
            || (target == a2 && resolved_dom.contains(a1) && resolved_dom.contains(b1) && resolved_dom.contains(b2)),
        Constraint::Parallel { a1, a2, b1, b2 } =>
            (target == a1 && resolved_dom.contains(a2) && resolved_dom.contains(b1) && resolved_dom.contains(b2))
            || (target == a2 && resolved_dom.contains(a1) && resolved_dom.contains(b1) && resolved_dom.contains(b2)),
        Constraint::Collinear { a, b, c } =>
            (target == a && resolved_dom.contains(b) && resolved_dom.contains(c))
            || (target == b && resolved_dom.contains(a) && resolved_dom.contains(c))
            || (target == c && resolved_dom.contains(a) && resolved_dom.contains(b)),
        Constraint::PointOnCircle { point, center, radius_point } =>
            target == point && resolved_dom.contains(center) && resolved_dom.contains(radius_point),
        Constraint::Symmetric { point, original, axis_a, axis_b } =>
            target == point && resolved_dom.contains(original) && resolved_dom.contains(axis_a) && resolved_dom.contains(axis_b),
        Constraint::FixedPoint { point, .. } =>
            target == point,
        Constraint::Ratio { a1, a2, b1, b2, .. } =>
            (target == a1 && resolved_dom.contains(a2) && resolved_dom.contains(b1) && resolved_dom.contains(b2))
            || (target == a2 && resolved_dom.contains(a1) && resolved_dom.contains(b1) && resolved_dom.contains(b2)),
        Constraint::Tangent { .. } => false,
        Constraint::CircleTangent { .. } => false,
        Constraint::Angle { .. } => false,
    }
}

/// At most two constraints impose nontrivial loci on `target`.
/// This is a domain-only check — no point values needed.
pub open spec fn at_most_two_nontrivial_loci<T: OrderedField>(
    target: EntityId,
    constraints: Seq<Constraint<T>>,
    resolved_dom: Set<EntityId>,
) -> bool {
    // Count of nontrivial constraints ≤ 2, expressed as:
    // there do NOT exist three distinct indices i < j < k all nontrivial.
    !(exists|i: int, j: int, k: int|
        0 <= i < j && j < k && k < constraints.len()
        && is_nontrivial_for_target(#[trigger] constraints[i], target, resolved_dom)
        && is_nontrivial_for_target(#[trigger] constraints[j], target, resolved_dom)
        && is_nontrivial_for_target(#[trigger] constraints[k], target, resolved_dom))
}

// ===========================================================================
//  Step-constraint locus correspondence
// ===========================================================================

/// For circle steps, every nontrivial constraint locus is exactly one of the
/// step's built-in loci (OnCircle or OnLine). This provenance relationship
/// holds because the solver constructs steps from constraint loci.
pub open spec fn step_loci_match_geometry<T: OrderedField>(
    step: ConstructionStep<T>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
) -> bool {
    let target = step_target(step);
    match step {
        ConstructionStep::CircleLine { circle, line, .. } =>
            forall|ci: int| 0 <= ci < constraints.len()
                && locus_is_nontrivial(
                    constraint_to_locus(#[trigger] constraints[ci], resolved, target))
                ==> locus_eqv(
                        constraint_to_locus(constraints[ci], resolved, target),
                        Locus2d::OnCircle(circle))
                    || locus_eqv(
                        constraint_to_locus(constraints[ci], resolved, target),
                        Locus2d::OnLine(line)),
        ConstructionStep::CircleCircle { circle1, circle2, .. } =>
            forall|ci: int| 0 <= ci < constraints.len()
                && locus_is_nontrivial(
                    constraint_to_locus(#[trigger] constraints[ci], resolved, target))
                ==> locus_eqv(
                        constraint_to_locus(constraints[ci], resolved, target),
                        Locus2d::OnCircle(circle1))
                    || locus_eqv(
                        constraint_to_locus(constraints[ci], resolved, target),
                        Locus2d::OnCircle(circle2)),
        _ => true,
    }
}

// ===========================================================================
//  Composite structural soundness predicate — sub-predicates
// ===========================================================================

/// Conjuncts 1-4: distinct targets, well-formed constraints, entity coverage,
/// locus ordering.
pub open spec fn plan_valid_structure(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
) -> bool {
    // 1. Distinct targets
    &&& forall|i: int, j: int|
        0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
        step_target(plan[i]) != step_target(plan[j])

    // 2. All constraints well-formed
    &&& forall|ci: int| 0 <= ci < constraints.len() ==>
        constraint_well_formed(#[trigger] constraints[ci])

    // 3. All constraint entities covered by the plan
    &&& forall|ci: int| 0 <= ci < constraints.len() ==>
        constraint_entities(constraints[ci]).subset_of(execute_plan(plan).dom())

    // 4. Plan is locus-ordered
    &&& plan_locus_ordered(plan, constraints)
}

/// Conjunct 5: no constraint input is a circle target.
pub open spec fn plan_independence(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
) -> bool {
    is_fully_independent_plan(plan, constraints)
}

/// Conjuncts 6-8: geometric validity, positive discriminant, radicand match.
pub open spec fn plan_geometric_validity<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
) -> bool {
    // 6. Each step geometrically valid
    &&& forall|j: int| #![trigger plan[j]]
        0 <= j < plan.len() ==> step_geometrically_valid(plan[j])

    // 7. Each step has positive discriminant
    &&& forall|j: int| #![trigger plan[j]]
        0 <= j < plan.len() ==> step_has_positive_discriminant(plan[j])

    // 8. Each step's radicand matches
    &&& forall|j: int| #![trigger plan[j]]
        0 <= j < plan.len() ==> step_radicand_matches::<R>(plan[j])
}

/// Conjuncts 9-12: nontrivial loci count, step satisfaction, geometry match,
/// nondegeneracy.
pub open spec fn plan_dynamic_satisfaction(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
) -> bool {
    // 9. At most two nontrivial loci per step
    &&& forall|si: int| #![trigger plan[si]]
        0 <= si < plan.len() ==>
        at_most_two_nontrivial_loci(
            step_target(plan[si]),
            constraints,
            execute_plan(plan.take(si as int)).dom(),
        )

    // 10. Rational steps satisfy all constraint loci
    &&& forall|si: int| #![trigger plan[si]]
        0 <= si < plan.len() && is_rational_step(plan[si]) ==>
        step_satisfies_all_constraint_loci(
            plan[si], constraints, execute_plan(plan.take(si as int)))

    // 11. Circle steps: nontrivial loci match step geometry
    &&& forall|si: int| #![trigger plan[si]]
        0 <= si < plan.len() && !is_rational_step(plan[si]) ==>
        step_loci_match_geometry(
            plan[si], constraints, execute_plan(plan.take(si as int)))

    // 12. Non-degeneracy (axis non-degenerate for Symmetric constraints)
    &&& forall|si: int, ci: int|
        #![trigger plan[si], constraints[ci]]
        0 <= si < plan.len() && 0 <= ci < constraints.len() ==>
        constraint_locus_nondegenerate(
            constraints[ci], execute_plan(plan.take(si as int)), step_target(plan[si]))
}

// ===========================================================================
//  Composite structural soundness predicate
// ===========================================================================

/// All conditions needed for the master bridge lemma.
/// Conjunction of the 4 sub-predicates: valid_structure, independence,
/// geometric_validity, dynamic_satisfaction.
pub open spec fn plan_structurally_sound<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
) -> bool {
    &&& plan_valid_structure(plan, constraints)
    &&& plan_independence(plan, constraints)
    &&& plan_geometric_validity::<R>(plan)
    &&& plan_dynamic_satisfaction(plan, constraints)
}

// ===========================================================================
//  Round 5: Master bridge lemma
// ===========================================================================

/// Master bridge: for a structurally sound plan where verification constraints
/// are satisfied at the extension level, ALL constraints are satisfied at the
/// extension level.
///
/// Composes:
/// 1. lemma_lift_plan_valid → plan validity at ext level
/// 2. lemma_lift_plan_locus_ordered → locus ordering at ext level
/// 3. Per-step loci satisfaction (rational: lemma_rational_step_satisfies_ext_loci,
///    circle: lemma_circle_step_satisfies_ext_loci)
/// 4. lemma_end_to_end at extension level
pub proof fn lemma_solver_to_soundness<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
)
    requires
        plan_structurally_sound::<R>(plan, constraints),
        // Verification constraints satisfied at extension level
        forall|ci: int| 0 <= ci < constraints.len()
            && is_verification_constraint(#[trigger] constraints[ci])
            ==> constraint_satisfied(
                lift_constraint::<RationalModel, R>(constraints[ci]),
                execute_plan(lift_plan::<RationalModel, R>(plan))),
    ensures
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_satisfied(
                #[trigger] lift_constraints::<RationalModel, R>(constraints)[ci],
                execute_plan(lift_plan::<RationalModel, R>(plan))),
{
    let lift_plan_val = lift_plan::<RationalModel, R>(plan);
    let lift_constraints_val = lift_constraints::<RationalModel, R>(constraints);

    // 1. Plan validity at ext level
    lemma_lift_plan_valid::<R>(plan, constraints);

    // 2. Locus ordering at ext level
    lemma_lift_plan_locus_ordered::<RationalModel, R>(plan, constraints);

    // 3. Constraint well-formedness at ext level
    assert forall|ci: int| 0 <= ci < lift_constraints_val.len() implies
        constraint_well_formed(#[trigger] lift_constraints_val[ci])
    by {
        assert(lift_constraints_val[ci]
            == lift_constraint::<RationalModel, R>(constraints[ci]));
        lemma_lift_constraint_well_formed::<RationalModel, R>(constraints[ci]);
    };

    // 4. Entity coverage at ext level
    lemma_lift_plan_domain::<RationalModel, R>(plan);
    assert forall|ci: int| 0 <= ci < lift_constraints_val.len() implies
        constraint_entities(lift_constraints_val[ci]).subset_of(
            execute_plan(lift_plan_val).dom())
    by {
        assert(lift_constraints_val[ci]
            == lift_constraint::<RationalModel, R>(constraints[ci]));
        lemma_lift_constraint_entities::<RationalModel, R>(constraints[ci]);
    };

    // 5. Per-step loci satisfaction at ext level
    assert forall|si: int| 0 <= si < lift_plan_val.len() implies
        step_satisfies_all_constraint_loci(
            #[trigger] lift_plan_val[si],
            lift_constraints_val,
            execute_plan(lift_plan_val.take(si as int)))
    by {
        assert(lift_plan_val[si]
            == lift_construction_step::<RationalModel, R>(plan[si]));
        if is_rational_step(plan[si]) {
            lemma_rational_step_satisfies_ext_loci::<R>(plan, constraints, si);
        } else {
            lemma_circle_step_satisfies_ext_loci::<R>(plan, constraints, si);
        }
    };

    // 6. Verification constraints at ext level
    assert forall|ci: int| 0 <= ci < lift_constraints_val.len()
        && is_verification_constraint(#[trigger] lift_constraints_val[ci])
    implies constraint_satisfied(
        lift_constraints_val[ci], execute_plan(lift_plan_val))
    by {
        assert(lift_constraints_val[ci]
            == lift_constraint::<RationalModel, R>(constraints[ci]));
        lemma_lift_is_verification_constraint::<RationalModel, R>(constraints[ci]);
    };

    // 7. Apply lemma_end_to_end at the extension level
    lemma_end_to_end(lift_plan_val, lift_constraints_val);
}

// ===========================================================================
//  Deterministic plan bridge (det_plan trick)
// ===========================================================================

/// Convert all plan steps to PointStep with deterministic positions from execute_step_in_ext.
/// `execute_plan(det_plan(plan))` equals `execute_plan_in_ext(plan)`.
pub open spec fn det_plan<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
) -> ConstructionPlan<SpecQuadExt<F, R>> {
    Seq::new(plan.len() as nat, |i: int| ConstructionStep::PointStep {
        id: step_target(plan[i]),
        position: execute_step_in_ext::<F, R>(plan[i]),
    })
}

/// execute_plan(det_plan(plan)) == execute_plan_in_ext(plan).
pub proof fn lemma_det_plan_agrees<F: OrderedField, R: PositiveRadicand<F>>(
    plan: ConstructionPlan<F>,
)
    ensures execute_plan(det_plan::<F, R>(plan)) =~= execute_plan_in_ext::<F, R>(plan),
    decreases plan.len(),
{
    if plan.len() == 0 {
        // Both empty maps
    } else {
        let prefix = plan.drop_last();
        let step = plan.last();
        let dp = det_plan::<F, R>(plan);

        // Recurse on prefix
        lemma_det_plan_agrees::<F, R>(prefix);

        // Structural facts about det_plan
        assert(dp.len() == plan.len());
        assert(dp.drop_last() =~= det_plan::<F, R>(prefix));
        assert(dp.last() == ConstructionStep::<SpecQuadExt<F, R>>::PointStep {
            id: step_target(step),
            position: execute_step_in_ext::<F, R>(step),
        });

        // execute_step(PointStep) = position = execute_step_in_ext(step)
        // step_target(PointStep) = id = step_target(step)
        // Both sides insert (step_target(step), execute_step_in_ext(step)) into equal maps
    }
}

/// det_plan preserves plan_valid: all steps are well-formed PointSteps with distinct targets.
/// Only needs distinct targets (from plan_valid_structure); step_well_formed is trivial
/// for PointStep.
proof fn lemma_det_plan_valid<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
)
    requires plan_valid_structure(plan, constraints),
    ensures plan_valid(
        det_plan::<RationalModel, R>(plan),
        lift_constraints::<RationalModel, R>(constraints)),
{
    let dp = det_plan::<RationalModel, R>(plan);
    let lc = lift_constraints::<RationalModel, R>(constraints);

    // 1. Distinct targets: step_target(dp[i]) = step_target(plan[i])
    assert forall|i: int, j: int|
        0 <= i < dp.len() && 0 <= j < dp.len() && i != j
    implies step_target(dp[i]) != step_target(dp[j])
    by {
        // dp[i].id = step_target(plan[i]), dp[j].id = step_target(plan[j])
        // Distinct by plan_structurally_sound
    };

    // 2. Each step well-formed: step_well_formed(PointStep{..}) = true
    assert forall|i: int| 0 <= i < dp.len()
    implies step_well_formed(#[trigger] dp[i])
    by {};
}

/// det_plan preserves plan_locus_ordered: targets match, so ordering transfers.
proof fn lemma_det_plan_locus_ordered<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
)
    requires
        plan_locus_ordered(plan, constraints),
    ensures
        plan_locus_ordered(
            det_plan::<RationalModel, R>(plan),
            lift_constraints::<RationalModel, R>(constraints)),
{
    let dp = det_plan::<RationalModel, R>(plan);
    let lc = lift_constraints::<RationalModel, R>(constraints);

    assert forall|ci: int, si: int|
        #![trigger dp[si], lc[ci]]
        0 <= ci < lc.len() && 0 <= si < dp.len() &&
        constraint_entities(lc[ci]).contains(step_target(dp[si])) &&
        !constraint_locus_entities(lc[ci]).contains(step_target(dp[si]))
    implies (
        is_verification_constraint(lc[ci])
        || exists|si_loc: int|
            si < si_loc < dp.len() &&
            constraint_locus_entities(lc[ci]).contains(step_target(dp[si_loc]))
    )
    by {
        // step_target(dp[k]) = step_target(plan[k]) for all k
        lemma_lift_constraint_entities::<RationalModel, R>(constraints[ci]);
        lemma_lift_constraint_locus_entities::<RationalModel, R>(constraints[ci]);
        lemma_lift_is_verification_constraint::<RationalModel, R>(constraints[ci]);

        // Preconditions match original plan_locus_ordered
        if is_verification_constraint(constraints[ci]) {
        } else {
            let si_loc = choose|si_loc: int|
                si < si_loc < plan.len() &&
                constraint_locus_entities(constraints[ci]).contains(
                    step_target(plan[si_loc]));
            // step_target(dp[si_loc]) = step_target(plan[si_loc])
            assert(si_loc < dp.len());
            assert(constraint_locus_entities(lc[ci]).contains(
                step_target(dp[si_loc])));
        }
    };
}

/// For entries placed by rational steps, execute_plan_in_ext gives exactly lift_point2 of the
/// base entry. This is structural equality (==), not just eqv.
proof fn lemma_det_entries_eq_lift<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    si: int,
)
    requires
        0 <= si <= plan.len(),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
    ensures
        forall|e: EntityId|
            execute_plan_in_ext::<RationalModel, R>(plan.take(si)).dom().contains(e)
            && (exists|j: int| 0 <= j < si && step_target(plan[j]) == e
                && is_rational_step(plan[j]))
            ==> execute_plan_in_ext::<RationalModel, R>(plan.take(si))[e]
                == lift_point2::<RationalModel, R>(execute_plan(plan.take(si))[e]),
    decreases si,
{
    if si == 0 {
        // Empty prefix, vacuously true
    } else {
        lemma_det_entries_eq_lift::<R>(plan, si - 1);

        let step = plan[si - 1];
        let target = step_target(step);

        assert(plan.take(si) == plan.take(si - 1).push(plan[si - 1]));
        assert(plan.take(si).drop_last() =~= plan.take(si - 1));
        assert(plan.take(si).last() == step);

        lemma_execute_plan_in_ext_domain::<RationalModel, R>(plan.take(si - 1));

        assert forall|e: EntityId|
            execute_plan_in_ext::<RationalModel, R>(plan.take(si)).dom().contains(e)
            && (exists|j: int| 0 <= j < si && step_target(plan[j]) == e
                && is_rational_step(plan[j]))
        implies execute_plan_in_ext::<RationalModel, R>(plan.take(si))[e]
            == lift_point2::<RationalModel, R>(execute_plan(plan.take(si))[e])
        by {
            let j = choose|j: int| 0 <= j < si && step_target(plan[j]) == e
                && is_rational_step(plan[j]);

            if j == si - 1 {
                // e == target: newly inserted entry
                assert(e == target);
                // execute_step_in_ext(step) == lift_point2(execute_step(step))
                // for PointStep and LineLine (structural equality by definition)
            } else {
                // j < si - 1: entry from previous prefix
                assert(step_target(plan[j]) != step_target(plan[si - 1]));
                assert(e != target);
                // Map::insert at target doesn't change entry at e
                assert(execute_plan_in_ext::<RationalModel, R>(plan.take(si - 1))
                    .dom().contains(e));
                // By IH
            }
        };
    }
}

/// For constraint-relevant entries, det_ext_resolved agrees with lift_resolved_map(base_resolved).
proof fn lemma_det_entry_eqv<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
    ci: int,
)
    requires
        0 <= si < plan.len(),
        0 <= ci < constraints.len(),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        is_fully_independent_plan(plan, constraints),
        constraint_entities(constraints[ci]).contains(step_target(plan[si])),
        execute_plan_in_ext::<RationalModel, R>(plan.take(si as int)).dom()
            =~= execute_plan(plan.take(si as int)).dom(),
    ensures
        forall|e: EntityId|
            constraint_entities(
                lift_constraint::<RationalModel, R>(constraints[ci])).contains(e)
            && e != step_target(plan[si])
            && execute_plan_in_ext::<RationalModel, R>(plan.take(si as int)).dom().contains(e)
            ==> execute_plan_in_ext::<RationalModel, R>(plan.take(si as int))[e].eqv(
                lift_resolved_map::<RationalModel, R>(
                    execute_plan(plan.take(si as int)))[e]),
{
    let target = step_target(plan[si]);
    let base_resolved = execute_plan(plan.take(si as int));
    let det_ext_resolved = execute_plan_in_ext::<RationalModel, R>(plan.take(si as int));

    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);
    lemma_lift_constraint_entities::<RationalModel, R>(constraints[ci]);
    lemma_det_entries_eq_lift::<R>(plan, si);

    assert forall|e: EntityId|
        constraint_entities(
            lift_constraint::<RationalModel, R>(constraints[ci])).contains(e)
        && e != target
        && det_ext_resolved.dom().contains(e)
    implies det_ext_resolved[e].eqv(
        lift_resolved_map::<RationalModel, R>(base_resolved)[e])
    by {
        assert(constraint_entities(constraints[ci]).contains(e));
        assert(base_resolved.dom().contains(e));

        // e is not a circle target (by is_fully_independent_plan)
        lemma_execute_plan_dom::<RationalModel>(plan.take(si as int), e);
        let j_witness = choose|j: int| 0 <= j < plan.take(si as int).len()
            && step_target(plan.take(si as int)[j]) == e;
        assert(0 <= j_witness < si);
        assert(step_target(plan[j_witness]) == e);
        assert(!circle_targets(plan).contains(e));
        if !is_rational_step(plan[j_witness]) {
            assert(circle_targets(plan).contains(e));
        }
        assert(is_rational_step(plan[j_witness]));

        // Structural equality from lemma_det_entries_eq_lift
        assert(det_ext_resolved[e]
            == lift_point2::<RationalModel, R>(base_resolved[e]));
        assert(lift_resolved_map::<RationalModel, R>(base_resolved)[e]
            == lift_point2::<RationalModel, R>(base_resolved[e]));
        Point2::<SpecQuadExt<RationalModel, R>>::axiom_eqv_reflexive(det_ext_resolved[e]);
    };
}

/// Per-ci helper for rational steps: proves locus satisfaction via base-level lift.
proof fn lemma_det_step_rational_ci<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
    ci: int,
)
    requires
        0 <= si < plan.len(),
        0 <= ci < constraints.len(),
        is_rational_step(plan[si]),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        constraint_well_formed(constraints[ci]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        is_fully_independent_plan(plan, constraints),
        // Base satisfaction for this ci
        point_satisfies_locus(
            constraint_to_locus(constraints[ci],
                execute_plan(plan.take(si as int)), step_target(plan[si])),
            execute_step(plan[si])),
        // Non-degeneracy
        constraint_locus_nondegenerate(
            constraints[ci], execute_plan(plan.take(si as int)), step_target(plan[si])),
        // Domain + target
        execute_plan_in_ext::<RationalModel, R>(plan.take(si as int)).dom()
            =~= execute_plan(plan.take(si as int)).dom(),
        !execute_plan(plan.take(si as int)).dom().contains(step_target(plan[si])),
        // Entity coverage
        constraint_entities(constraints[ci]).contains(step_target(plan[si])),
        constraint_entities(constraints[ci]).remove(step_target(plan[si])).subset_of(
            execute_plan(plan.take(si as int)).dom()),
    ensures
        point_satisfies_locus(
            constraint_to_locus(
                lift_constraint::<RationalModel, R>(constraints[ci]),
                execute_plan_in_ext::<RationalModel, R>(plan.take(si as int)),
                step_target(plan[si])),
            execute_step_in_ext::<RationalModel, R>(plan[si])),
{
    let target = step_target(plan[si]);
    let base_resolved = execute_plan(plan.take(si as int));
    let det_ext_resolved = execute_plan_in_ext::<RationalModel, R>(plan.take(si as int));
    let lift_c = lift_constraint::<RationalModel, R>(constraints[ci]);
    let base_locus = constraint_to_locus(constraints[ci], base_resolved, target);
    let lifted_base_locus = lift_locus::<RationalModel, R>(base_locus);
    let det_locus = constraint_to_locus(lift_c, det_ext_resolved, target);
    let p = execute_step_in_ext::<RationalModel, R>(plan[si]);

    // Entry agreement
    lemma_lift_constraint_entities::<RationalModel, R>(constraints[ci]);
    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);
    lemma_det_entry_eqv::<R>(plan, constraints, si, ci);

    // Non-degeneracy at ext level
    lemma_nondegen_transfers_to_ext::<R>(
        constraints[ci], base_resolved, det_ext_resolved, target);

    // Locus chain: det_locus ≈ lift_resolved_locus ≈ lifted_base_locus
    lemma_constraint_to_locus_resolved_congruence(
        lift_c, det_ext_resolved,
        lift_resolved_map::<RationalModel, R>(base_resolved), target);
    lemma_lift_constraint_to_locus::<RationalModel, R>(
        constraints[ci], base_resolved, target);
    let lift_res_locus = constraint_to_locus(
        lift_c, lift_resolved_map::<RationalModel, R>(base_resolved), target);
    lemma_locus_eqv_transitive(det_locus, lift_res_locus, lifted_base_locus);

    // Base satisfaction → lifted satisfaction
    lemma_lift_preserves_satisfaction::<RationalModel, R>(base_locus, execute_step(plan[si]));
    // execute_step_in_ext == lift_point2(execute_step) for rational steps
    assert(p == lift_point2::<RationalModel, R>(execute_step(plan[si])));

    // Transfer via locus_eqv
    lemma_locus_eqv_symmetric(det_locus, lifted_base_locus);
    lemma_point_satisfies_locus_eqv(lifted_base_locus, det_locus, p);
}

/// Per-ci helper for circle steps: proves locus satisfaction via geometric loci.
proof fn lemma_det_step_circle_ci<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
    ci: int,
)
    requires
        0 <= si < plan.len(),
        0 <= ci < constraints.len(),
        !is_rational_step(plan[si]),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        constraint_well_formed(constraints[ci]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_geometrically_valid(plan[j]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_has_positive_discriminant(plan[j]),
        forall|j: int| #![trigger plan[j]]
            0 <= j < plan.len() ==> step_radicand_matches::<R>(plan[j]),
        is_fully_independent_plan(plan, constraints),
        step_loci_match_geometry(
            plan[si], constraints, execute_plan(plan.take(si as int))),
        // Non-degeneracy
        constraint_locus_nondegenerate(
            constraints[ci], execute_plan(plan.take(si as int)), step_target(plan[si])),
        // Base nontriviality (for step_loci_match_geometry to apply)
        locus_is_nontrivial(constraint_to_locus(
            constraints[ci], execute_plan(plan.take(si as int)), step_target(plan[si]))),
        // Domain + target
        execute_plan_in_ext::<RationalModel, R>(plan.take(si as int)).dom()
            =~= execute_plan(plan.take(si as int)).dom(),
        !execute_plan(plan.take(si as int)).dom().contains(step_target(plan[si])),
        // Entity coverage
        constraint_entities(constraints[ci]).contains(step_target(plan[si])),
        constraint_entities(constraints[ci]).remove(step_target(plan[si])).subset_of(
            execute_plan(plan.take(si as int)).dom()),
    ensures
        point_satisfies_locus(
            constraint_to_locus(
                lift_constraint::<RationalModel, R>(constraints[ci]),
                execute_plan_in_ext::<RationalModel, R>(plan.take(si as int)),
                step_target(plan[si])),
            execute_step_in_ext::<RationalModel, R>(plan[si])),
{
    let target = step_target(plan[si]);
    let base_resolved = execute_plan(plan.take(si as int));
    let det_ext_resolved = execute_plan_in_ext::<RationalModel, R>(plan.take(si as int));
    let lift_c = lift_constraint::<RationalModel, R>(constraints[ci]);
    let base_locus = constraint_to_locus(constraints[ci], base_resolved, target);
    let lifted_base_locus = lift_locus::<RationalModel, R>(base_locus);
    let det_locus = constraint_to_locus(lift_c, det_ext_resolved, target);
    let p = execute_step_in_ext::<RationalModel, R>(plan[si]);

    // Entry agreement
    lemma_lift_constraint_entities::<RationalModel, R>(constraints[ci]);
    lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);
    lemma_det_entry_eqv::<R>(plan, constraints, si, ci);

    // Non-degeneracy at ext level
    lemma_nondegen_transfers_to_ext::<R>(
        constraints[ci], base_resolved, det_ext_resolved, target);

    // Locus chain: det_locus ≈ lift_resolved_locus ≈ lifted_base_locus
    lemma_constraint_to_locus_resolved_congruence(
        lift_c, det_ext_resolved,
        lift_resolved_map::<RationalModel, R>(base_resolved), target);
    lemma_lift_constraint_to_locus::<RationalModel, R>(
        constraints[ci], base_resolved, target);
    let lift_res_locus = constraint_to_locus(
        lift_c, lift_resolved_map::<RationalModel, R>(base_resolved), target);
    lemma_locus_eqv_transitive(det_locus, lift_res_locus, lifted_base_locus);

    // Geometric loci satisfaction
    lemma_execute_step_in_ext_satisfies_loci::<RationalModel, R>(plan[si]);

    // base_locus ≈ OnCircle/OnLine matching the step (by step_loci_match_geometry)
    // Chain: det_locus ≈ lifted_base ≈ lift(step_geom) = sl, then transfer from sl
    match plan[si] {
        ConstructionStep::CircleLine { circle, line, .. } => {
            if locus_eqv(base_locus, Locus2d::OnCircle(circle)) {
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnCircle(
                    lift_circle2::<RationalModel, R>(circle));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(
                    base_locus, Locus2d::OnCircle(circle));
                lemma_locus_eqv_transitive(det_locus, lifted_base_locus, sl);
                lemma_locus_eqv_symmetric(det_locus, sl);
                lemma_point_satisfies_locus_eqv(sl, det_locus, p);
            } else {
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnLine(
                    lift_line2::<RationalModel, R>(line));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(
                    base_locus, Locus2d::OnLine(line));
                lemma_locus_eqv_transitive(det_locus, lifted_base_locus, sl);
                lemma_locus_eqv_symmetric(det_locus, sl);
                lemma_point_satisfies_locus_eqv(sl, det_locus, p);
            }
        }
        ConstructionStep::CircleCircle { circle1, circle2, .. } => {
            if locus_eqv(base_locus, Locus2d::OnCircle(circle1)) {
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnCircle(
                    lift_circle2::<RationalModel, R>(circle1));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(
                    base_locus, Locus2d::OnCircle(circle1));
                lemma_locus_eqv_transitive(det_locus, lifted_base_locus, sl);
                lemma_locus_eqv_symmetric(det_locus, sl);
                lemma_point_satisfies_locus_eqv(sl, det_locus, p);
            } else {
                let sl = Locus2d::<SpecQuadExt<RationalModel, R>>::OnCircle(
                    lift_circle2::<RationalModel, R>(circle2));
                lemma_lift_locus_preserves_eqv::<RationalModel, R>(
                    base_locus, Locus2d::OnCircle(circle2));
                lemma_locus_eqv_transitive(det_locus, lifted_base_locus, sl);
                lemma_locus_eqv_symmetric(det_locus, sl);
                lemma_point_satisfies_locus_eqv(sl, det_locus, p);
            }
        }
        _ => {} // Not reached
    }
}

/// Each step of det_plan satisfies all constraint loci.
proof fn lemma_det_step_satisfies_loci<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
    si: int,
)
    requires
        0 <= si < plan.len(),
        plan_structurally_sound::<R>(plan, constraints),
    ensures
        step_satisfies_all_constraint_loci(
            det_plan::<RationalModel, R>(plan)[si],
            lift_constraints::<RationalModel, R>(constraints),
            execute_plan(det_plan::<RationalModel, R>(plan).take(si as int))),
{
    let target = step_target(plan[si]);
    let dp = det_plan::<RationalModel, R>(plan);
    let lc = lift_constraints::<RationalModel, R>(constraints);
    let base_resolved = execute_plan(plan.take(si as int));
    let det_ext_resolved = execute_plan_in_ext::<RationalModel, R>(plan.take(si as int));

    // Key equalities
    assert(dp.take(si as int) =~= det_plan::<RationalModel, R>(plan.take(si as int)));
    lemma_det_plan_agrees::<RationalModel, R>(plan.take(si as int));
    assert(execute_plan(dp.take(si as int)) =~= det_ext_resolved);

    lemma_execute_plan_in_ext_domain::<RationalModel, R>(plan.take(si as int));
    lemma_step_target_not_in_prefix::<RationalModel>(plan, si);

    // Per-constraint nontrivial satisfaction
    assert forall|ci: int| 0 <= ci < lc.len()
        && locus_is_nontrivial(
            constraint_to_locus(
                #[trigger] lc[ci],
                execute_plan(dp.take(si as int)),
                step_target(dp[si])))
    implies point_satisfies_locus(
        constraint_to_locus(lc[ci],
            execute_plan(dp.take(si as int)),
            step_target(dp[si])),
        execute_step(dp[si]))
    by {
        assert(lc[ci] == lift_constraint::<RationalModel, R>(constraints[ci]));
        assert(step_target(dp[si]) == target);
        assert(constraint_well_formed(constraints[ci]));

        // Transfer nontriviality to base
        lemma_lift_resolved_map_dom::<RationalModel, R>(base_resolved);
        lemma_locus_nontrivial_depends_on_domain(
            lift_constraint::<RationalModel, R>(constraints[ci]),
            det_ext_resolved,
            lift_resolved_map::<RationalModel, R>(base_resolved), target);
        lemma_lift_preserves_nontriviality::<RationalModel, R>(
            constraints[ci], base_resolved, target);

        // Entity coverage
        lemma_nontrivial_implies_entity_coverage(constraints[ci], base_resolved, target);

        if is_rational_step(plan[si]) {
            assert(step_satisfies_all_constraint_loci(
                plan[si], constraints, base_resolved));
            assert(constraint_locus_nondegenerate(
                constraints[ci], base_resolved, target));
            lemma_det_step_rational_ci::<R>(plan, constraints, si, ci);
        } else {
            assert(constraint_locus_nondegenerate(
                constraints[ci], base_resolved, target));
            assert(step_loci_match_geometry(plan[si], constraints, base_resolved));
            lemma_det_step_circle_ci::<R>(plan, constraints, si, ci);
        }
    };

    lemma_nontrivial_loci_imply_all_satisfied(dp[si], lc, execute_plan(dp.take(si as int)));
}

/// Master theorem: if plan is structurally sound and verification constraints are satisfied
/// against execute_plan_in_ext, then ALL constraints are satisfied against execute_plan_in_ext.
pub proof fn lemma_solver_to_soundness_det<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
    constraints: Seq<Constraint<RationalModel>>,
)
    requires
        plan_structurally_sound::<R>(plan, constraints),
        // Verification constraints satisfied at extension level against deterministic map
        forall|ci: int| 0 <= ci < constraints.len()
            && is_verification_constraint(#[trigger] constraints[ci])
            ==> constraint_satisfied(
                lift_constraint::<RationalModel, R>(constraints[ci]),
                execute_plan_in_ext::<RationalModel, R>(plan)),
    ensures
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_satisfied(
                #[trigger] lift_constraints::<RationalModel, R>(constraints)[ci],
                execute_plan_in_ext::<RationalModel, R>(plan)),
{
    let dp = det_plan::<RationalModel, R>(plan);
    let lc = lift_constraints::<RationalModel, R>(constraints);

    // Key identity: execute_plan(det_plan(plan)) == execute_plan_in_ext(plan)
    lemma_det_plan_agrees::<RationalModel, R>(plan);

    // 1. Plan validity
    lemma_det_plan_valid::<R>(plan, constraints);

    // 2. Locus ordering
    lemma_det_plan_locus_ordered::<R>(plan, constraints);

    // 3. Constraint well-formedness at ext level
    assert forall|ci: int| 0 <= ci < lc.len() implies
        constraint_well_formed(#[trigger] lc[ci])
    by {
        assert(lc[ci] == lift_constraint::<RationalModel, R>(constraints[ci]));
        lemma_lift_constraint_well_formed::<RationalModel, R>(constraints[ci]);
    };

    // 4. Entity coverage at ext level
    lemma_execute_plan_in_ext_domain::<RationalModel, R>(plan);
    assert forall|ci: int| 0 <= ci < lc.len() implies
        constraint_entities(lc[ci]).subset_of(execute_plan(dp).dom())
    by {
        assert(lc[ci] == lift_constraint::<RationalModel, R>(constraints[ci]));
        lemma_lift_constraint_entities::<RationalModel, R>(constraints[ci]);
        // execute_plan(dp).dom() =~= execute_plan_in_ext(plan).dom()
        //   == execute_plan(plan).dom() (by lemma_execute_plan_in_ext_domain)
    };

    // 5. Per-step loci satisfaction
    assert forall|si: int| 0 <= si < dp.len() implies
        step_satisfies_all_constraint_loci(
            #[trigger] dp[si], lc,
            execute_plan(dp.take(si as int)))
    by {
        lemma_det_step_satisfies_loci::<R>(plan, constraints, si);
    };

    // 6. Verification constraints
    assert forall|ci: int| 0 <= ci < lc.len()
        && is_verification_constraint(#[trigger] lc[ci])
    implies constraint_satisfied(lc[ci], execute_plan(dp))
    by {
        assert(lc[ci] == lift_constraint::<RationalModel, R>(constraints[ci]));
        lemma_lift_is_verification_constraint::<RationalModel, R>(constraints[ci]);
        // execute_plan(dp) =~= execute_plan_in_ext(plan)
    };

    // 7. Apply lemma_end_to_end with det_plan
    lemma_end_to_end(dp, lc);

    // Rewrite: execute_plan(dp) =~= execute_plan_in_ext(plan)
    assert forall|ci: int| 0 <= ci < constraints.len() implies
        constraint_satisfied(#[trigger] lc[ci], execute_plan_in_ext::<RationalModel, R>(plan))
    by {
        assert(lc[ci] == lift_constraint::<RationalModel, R>(constraints[ci]));
    };
}

} // verus!
