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
    }
}

} // verus!
