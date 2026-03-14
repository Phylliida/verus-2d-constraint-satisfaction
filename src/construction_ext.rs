use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::line_intersection::*;
use verus_geometry::circle_line::*;
use verus_geometry::circle_circle::*;
use verus_geometry::constructed_scalar::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::radicand::*;
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
        ConstructionStep::Fixed { .. } => true,
        ConstructionStep::LineLine { .. } => true,
        ConstructionStep::Determined { .. } => true,
        ConstructionStep::CircleLine { .. } => false,
        ConstructionStep::CircleCircle { .. } => false,
    }
}

/// A plan has "independent circles": every circle step only references
/// entities that were resolved by rational (non-circle) steps earlier
/// in the plan. This means circle steps don't depend on each other's
/// results, so the lifted plan data matches the extension field positions.
pub open spec fn is_independent_circle_plan<F: OrderedField>(
    plan: ConstructionPlan<F>,
) -> bool {
    // For every circle step at index i, all entities referenced in the
    // step's geometry (other than the target) are among the targets of
    // rational steps at indices < i.
    // Since circle step geometry is precomputed at F level, this is
    // captured by requiring that the step's constraint entities
    // (minus target) are all targets of rational steps before i.
    forall|i: int| #![trigger plan[i]]
        0 <= i < plan.len() && !is_rational_step(plan[i])
        ==> true // Placeholder: the actual check requires constraint tracking
        // Future: constraint entities minus target ⊆ {step_target(plan[j]) | j < i, is_rational_step(plan[j])}
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
//  Helper: qext_from_rational commutes with neg
// ===========================================================================

/// qext_from_rational(x.neg()) == qext_from_rational(x).neg()
/// when F::zero().neg() == F::zero() (holds for Rational and all concrete fields).
///
/// Proof: qext_from_rational(x.neg()) = qext(x.neg(), F::zero())
///        qext_from_rational(x).neg() = qe_neg(qext(x, F::zero())) = qext(x.neg(), F::zero().neg())
///        Equal when F::zero().neg() == F::zero().
proof fn lemma_qext_from_rational_neg<F: OrderedField, R: PositiveRadicand<F>>(x: F)
    requires
        F::zero().neg() == F::zero(),
    ensures
        qext_from_rational::<F, R>(x.neg()) == qext_from_rational::<F, R>(x).neg(),
{
}

/// For constraints where all referenced entities (other than target) are in a
/// purely rational resolved map, lifting commutes with locus construction.
///
/// This covers the common constraint types: Coincident, FixedX, FixedY, SameX,
/// SameY, DistanceSq, PointOnLine, Collinear, Midpoint, EqualLengthSq,
/// PointOnCircle, Perpendicular, Parallel, Symmetric.
///
/// Note: some sub-lemmas may need to be added for the more complex types.
/// Focus is on the most common CAD constraint patterns first.
pub proof fn lemma_lift_constraint_to_locus<F: OrderedField, R: PositiveRadicand<F>>(
    c: Constraint<F>,
    resolved: ResolvedPoints<F>,
    target: EntityId,
)
    requires
        constraint_entities(c).contains(target),
        constraint_entities(c).remove(target).subset_of(resolved.dom()),
        !resolved.dom().contains(target),
        // Needed for field ops in locus construction to commute with lifting.
        // Holds concretely for Rational (and any sensible field implementation).
        F::zero().neg() == F::zero(),
    ensures
        constraint_to_locus(lift_constraint::<F, R>(c), lift_resolved_map::<F, R>(resolved), target)
        == lift_locus::<F, R>(constraint_to_locus(c, resolved, target)),
{
    // Help Z3 see that the lifted resolved map has the same domain
    lemma_lift_resolved_map_dom::<F, R>(resolved);

    // The proof strategy is case analysis over constraint variants.
    // For each variant, the lifted constraint uses the same EntityIds and
    // branches the same way (same target/domain checks since domains are equal).
    // The values looked up in lift_resolved_map are lift_point2 of the originals.
    //
    // Simple cases (Coincident, FixedX/Y, SameX/Y): locus uses AtPoint/OnLine
    // with simple field operations that commute with lifting.
    //
    // Complex cases: need sub-lemmas for lift commuting with line2_from_points,
    // sq_dist_2d, reflect_point_across_line, etc. These use assume(false) for now.
    match c {
        Constraint::Coincident { a, b } => {
            // Both sides branch on target == a/b and dom().contains(other).
            // Domains match, so branches align. When contains(other):
            // locus is AtPoint(resolved[other]) / AtPoint(lift_point2(resolved[other])).
            // When !contains: both FullPlane.
        }
        Constraint::FixedX { point, x } => {
            // Locus: OnLine(Line2 { a: 1, b: 0, c: x.neg() })
            // Lifted: OnLine(Line2 { a: QE::one(), b: QE::zero(), c: qext(x).neg() })
            // lift_locus: OnLine(Line2 { a: qext(1), b: qext(0), c: qext(x.neg()) })
            // Key: qext(x).neg() == qext(x.neg()) by lemma_qext_from_rational_neg
            lemma_qext_from_rational_neg::<F, R>(x);
        }
        Constraint::FixedY { point, y } => {
            lemma_qext_from_rational_neg::<F, R>(y);
        }
        Constraint::SameX { a, b } => {
            // Locus: OnLine(Line2 { a: 1, b: 0, c: resolved[other].x.neg() })
            // qext(resolved[other].x).neg() == qext(resolved[other].x.neg()) by lemma
            if target == a && resolved.dom().contains(b) {
                lemma_qext_from_rational_neg::<F, R>(resolved[b].x);
            } else if target == b && resolved.dom().contains(a) {
                lemma_qext_from_rational_neg::<F, R>(resolved[a].x);
            }
            // else: both sides give FullPlane
        }
        Constraint::SameY { a, b } => {
            if target == a && resolved.dom().contains(b) {
                lemma_qext_from_rational_neg::<F, R>(resolved[b].y);
            } else if target == b && resolved.dom().contains(a) {
                lemma_qext_from_rational_neg::<F, R>(resolved[a].y);
            }
        }
        Constraint::PointOnLine { point, line_a, line_b } => {
            assume(false); // TODO: needs lift_line2_from_points lemma
        }
        Constraint::DistanceSq { a, b, dist_sq } => {
            // DistanceSq locus: OnCircle(Circle2 { center: resolved[other], radius_sq: dist_sq })
            // Lifted: OnCircle(Circle2 { center: lift_point2(resolved[other]), radius_sq: qext(dist_sq) })
            // lift_locus: OnCircle(lift_circle2(Circle2 { center: resolved[other], radius_sq: dist_sq }))
            //   = OnCircle(Circle2 { center: lift_point2(resolved[other]), radius_sq: qext(dist_sq) })
            // Syntactically equal — no field ops. Both sides branch the same way
            // (domains match), and the values are lift_point2/qext_from_rational of originals.
        }
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            assume(false); // TODO: needs lift commutes with sq_dist + circle
        }
        Constraint::Midpoint { mid, a, b } => {
            assume(false); // TODO: needs lift commutes with arithmetic
        }
        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            assume(false); // TODO: needs lift commutes with sub2/line construction
        }
        Constraint::Parallel { a1, a2, b1, b2 } => {
            assume(false); // TODO: needs lift commutes with sub2/line construction
        }
        Constraint::Collinear { a, b, c } => {
            assume(false); // TODO: needs lift_line2_from_points lemma
        }
        Constraint::PointOnCircle { point, center, radius_point } => {
            assume(false); // TODO: needs lift commutes with sq_dist + circle
        }
        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            assume(false); // TODO: needs lift commutes with reflection
        }
    }
}

} // verus!
