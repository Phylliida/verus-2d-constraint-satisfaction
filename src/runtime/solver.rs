use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::circle_line::cl_discriminant;
use verus_geometry::circle_circle::cc_discriminant;
use verus_geometry::line_intersection::*;
use verus_geometry::runtime::point2::*;
use verus_geometry::runtime::line2::{RuntimeLine2, line2_eval_exec};
use verus_geometry::runtime::circle2::*;
use verus_geometry::runtime::line_intersection::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use crate::entities::*;
use crate::constraints::*;
use crate::locus::*;
use crate::construction::*;
use crate::runtime::constraint::*;
use crate::runtime::locus::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::runtime::voronoi::sq_dist_2d_exec;
use verus_geometry::runtime::circle_line::cl_discriminant_exec;
use verus_geometry::runtime::circle_circle::cc_discriminant_exec;
use verus_quadratic_extension::radicand::PositiveRadicand;
use verus_quadratic_extension::runtime::RuntimeRadicand;
use crate::runtime::construction::{RuntimeStepData, execute_line_line_step, step_radicand_matches};
use crate::construction_ext::{
    at_most_two_nontrivial_loci, is_nontrivial_for_target,
    is_fully_independent_plan, circle_targets, is_rational_step,
    plan_structurally_sound, constraint_locus_nondegenerate,
    step_loci_match_geometry,
};

type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Spec helpers
// ===========================================================================

/// Convert a runtime plan Vec to spec-level ConstructionPlan.
pub open spec fn plan_to_spec(plan: Seq<RuntimeStepData>) -> ConstructionPlan<RationalModel> {
    Seq::new(plan.len() as nat, |i: int| plan[i].spec_step())
}

/// Convert a runtime constraints Vec to spec-level Seq<Constraint>.
pub open spec fn constraints_to_spec(constraints: Seq<RuntimeConstraint>) -> Seq<Constraint<RationalModel>> {
    Seq::new(constraints.len() as nat, |i: int| runtime_constraint_model(constraints[i]))
}

/// Whether a construction step's geometric preconditions are met.
/// This is `step_well_formed` minus the existential witness requirement
/// for circle steps (which needs a base-field intersection point that
/// may not exist at T=Rational for circle intersections in Q(sqrt(D))).
pub open spec fn step_geometrically_valid<T: OrderedField>(step: ConstructionStep<T>) -> bool {
    match step {
        ConstructionStep::PointStep { .. } => true,
        ConstructionStep::LineLine { line1, line2, .. } =>
            !line_det(line1, line2).eqv(T::zero()),
        ConstructionStep::CircleLine { line, .. } =>
            line2_nondegenerate(line),
        ConstructionStep::CircleCircle { circle1, circle2, .. } =>
            !circle1.center.eqv(circle2.center),
    }
}

/// Whether a construction step's circle discriminant is positive.
/// Non-circle steps are trivially true.
pub open spec fn step_has_positive_discriminant<T: OrderedField>(step: ConstructionStep<T>) -> bool {
    match step {
        ConstructionStep::CircleLine { circle, line, .. } =>
            T::zero().lt(cl_discriminant(circle, line)),
        ConstructionStep::CircleCircle { circle1, circle2, .. } =>
            T::zero().lt(cc_discriminant(circle1, circle2)),
        _ => true,
    }
}

// ===========================================================================
//  Runtime locus intersection
// ===========================================================================

/// Check if a RuntimeLine2 is non-degenerate (normal vector is nonzero).
fn line2_nondegenerate_exec(line: &RuntimeLine2) -> (out: bool)
    requires line.wf_spec(),
    ensures out == line2_nondegenerate::<RationalModel>(line@),
{
    !line.a.is_zero() || !line.b.is_zero()
}

/// Check if two RuntimePoint2 centers are not equivalent.
fn centers_not_eqv(p: &RuntimePoint2, q: &RuntimePoint2) -> (out: bool)
    requires p.wf_spec(), q.wf_spec(),
    ensures out == !p@.eqv(q@),
{
    let x_eq = p.x.le(&q.x) && q.x.le(&p.x);
    let y_eq = p.y.le(&q.y) && q.y.le(&p.y);
    proof {
        // le antisymmetry: le both ways → eqv
        if p@.x.le(q@.x) && q@.x.le(p@.x) {
            RationalModel::axiom_le_antisymmetric(p@.x, q@.x);
        }
        if p@.y.le(q@.y) && q@.y.le(p@.y) {
            RationalModel::axiom_le_antisymmetric(p@.y, q@.y);
        }
        // eqv → le both ways
        if p@.x.eqv(q@.x) {
            verus_algebra::lemmas::partial_order_lemmas::lemma_le_eqv_implies_le::<RationalModel>(p@.x, q@.x);
            RationalModel::axiom_eqv_symmetric(p@.x, q@.x);
            verus_algebra::lemmas::partial_order_lemmas::lemma_le_eqv_implies_le::<RationalModel>(q@.x, p@.x);
        }
        if p@.y.eqv(q@.y) {
            verus_algebra::lemmas::partial_order_lemmas::lemma_le_eqv_implies_le::<RationalModel>(p@.y, q@.y);
            RationalModel::axiom_eqv_symmetric(p@.y, q@.y);
            verus_algebra::lemmas::partial_order_lemmas::lemma_le_eqv_implies_le::<RationalModel>(q@.y, p@.y);
        }
    }
    !(x_eq && y_eq)
}

/// Intersect two runtime loci to produce a construction step.
/// Mirrors spec-level `intersect_loci`.
/// Returns None if the intersection is underdetermined (FullPlane),
/// the lines are parallel, or the resulting step would be degenerate.
/// Sound but incomplete: may return None when the spec returns Some
/// (e.g., degenerate line in circle-line, or coincident centers in circle-circle).
pub fn intersect_loci_exec(
    id: usize,
    l1: RuntimeLocus,
    l2: RuntimeLocus,
) -> (out: Option<RuntimeStepData>)
    requires
        l1.wf_spec(),
        l2.wf_spec(),
    ensures
        match out {
            Some(step) => step.wf_spec()
                && step.spec_step() == intersect_loci(
                    id as nat, l1.spec_locus(), l2.spec_locus(),
                ).unwrap()
                && step_target(step.spec_step()) == id as nat,
            None => true,
        },
{
    match (l1, l2) {
        // AtPoint overrides everything
        (RuntimeLocus::AtPoint { point }, _) => {
            let ghost spec_step = ConstructionStep::<RationalModel>::PointStep {
                id: id as nat, position: point@,
            };
            Some(RuntimeStepData::PointStep {
                target: id,
                x: point.x,
                y: point.y,
                model: Ghost(spec_step),
            })
        }
        (_, RuntimeLocus::AtPoint { point }) => {
            let ghost spec_step = ConstructionStep::<RationalModel>::PointStep {
                id: id as nat, position: point@,
            };
            Some(RuntimeStepData::PointStep {
                target: id,
                x: point.x,
                y: point.y,
                model: Ghost(spec_step),
            })
        }

        // Line-line
        (RuntimeLocus::OnLine { line: l1 }, RuntimeLocus::OnLine { line: l2 }) => {
            let det = line_det_exec(&l1, &l2);
            if det.is_zero() {
                None // Parallel or coincident lines
            } else {
                let ghost spec_step = ConstructionStep::<RationalModel>::LineLine {
                    id: id as nat, line1: l1@, line2: l2@,
                };
                Some(RuntimeStepData::LineLine {
                    target: id,
                    l1, l2,
                    model: Ghost(spec_step),
                })
            }
        }

        // Circle-line: check line is non-degenerate
        (RuntimeLocus::OnCircle { circle }, RuntimeLocus::OnLine { line }) => {
            if !line2_nondegenerate_exec(&line) {
                None
            } else {
                let ghost spec_step = ConstructionStep::<RationalModel>::CircleLine {
                    id: id as nat, circle: circle@, line: line@, plus: true,
                };
                Some(RuntimeStepData::CircleLine {
                    target: id,
                    circle, line, plus: true,
                    model: Ghost(spec_step),
                })
            }
        }
        (RuntimeLocus::OnLine { line }, RuntimeLocus::OnCircle { circle }) => {
            if !line2_nondegenerate_exec(&line) {
                None
            } else {
                let ghost spec_step = ConstructionStep::<RationalModel>::CircleLine {
                    id: id as nat, circle: circle@, line: line@, plus: true,
                };
                Some(RuntimeStepData::CircleLine {
                    target: id,
                    circle, line, plus: true,
                    model: Ghost(spec_step),
                })
            }
        }

        // Circle-circle: check centers are not equivalent
        (RuntimeLocus::OnCircle { circle: c1 }, RuntimeLocus::OnCircle { circle: c2 }) => {
            if !centers_not_eqv(&c1.center, &c2.center) {
                None
            } else {
                let ghost spec_step = ConstructionStep::<RationalModel>::CircleCircle {
                    id: id as nat, circle1: c1@, circle2: c2@, plus: true,
                };
                Some(RuntimeStepData::CircleCircle {
                    target: id,
                    c1, c2, plus: true,
                    model: Ghost(spec_step),
                })
            }
        }

        // FullPlane doesn't constrain
        (RuntimeLocus::FullPlane, _) => None,
        (_, RuntimeLocus::FullPlane) => None,
    }
}

// ===========================================================================
//  Greedy solver loop
// ===========================================================================

/// Collect loci for a target entity from all constraints.
/// Returns a Vec of RuntimeLocus values, one per constraint.
pub fn collect_loci_exec(
    constraints: &Vec<RuntimeConstraint>,
    points: &Vec<RuntimePoint2>,
    resolved_flags: &Vec<bool>,
    target: usize,
) -> (out: Vec<RuntimeLocus>)
    requires
        all_points_wf(points@),
        resolved_flags@.len() == points@.len(),
        (target as int) < points@.len(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) ==
            partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
    ensures
        out@.len() == constraints@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==>
            (#[trigger] out@[i]).spec_locus() == constraint_to_locus(
                runtime_constraint_model(constraints@[i]),
                partial_resolved_map(points_view(points@), resolved_flags@),
                target as nat,
            ),
{
    let mut result: Vec<RuntimeLocus> = Vec::new();
    let mut ci: usize = 0;
    while ci < constraints.len()
        invariant
            0 <= ci <= constraints@.len(),
            result@.len() == ci as int,
            all_points_wf(points@),
            resolved_flags@.len() == points@.len(),
            (target as int) < points@.len(),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
            forall|i: int| 0 <= i < resolved_flags@.len() ==>
                (#[trigger] resolved_flags@[i]) ==
                partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==>
                (#[trigger] result@[j]).spec_locus() == constraint_to_locus(
                    runtime_constraint_model(constraints@[j]),
                    partial_resolved_map(points_view(points@), resolved_flags@),
                    target as nat,
                ),
        decreases constraints@.len() - ci,
    {
        let locus = constraint_to_locus_exec(&constraints[ci], points, resolved_flags, target);
        result.push(locus);
        ci = ci + 1;
    }
    result
}

/// Find two non-trivial loci and intersect them to produce a step.
/// Returns None if fewer than two non-trivial loci exist or intersection fails.
pub fn find_and_intersect_loci(
    target: usize,
    loci: Vec<RuntimeLocus>,
) -> (out: Option<RuntimeStepData>)
    requires
        forall|i: int| 0 <= i < loci@.len() ==> (#[trigger] loci@[i]).wf_spec(),
    ensures
        match out {
            Some(step) => step.wf_spec()
                && step_target(step.spec_step()) == target as nat,
            None => true,
        },
{
    // First pass: find first nontrivial locus
    let mut first_idx: usize = 0;
    let mut found_first = false;
    while first_idx < loci.len()
        invariant_except_break
            0 <= first_idx <= loci@.len(),
            !found_first,
        invariant
            forall|i: int| 0 <= i < loci@.len() ==> (#[trigger] loci@[i]).wf_spec(),
            0 <= first_idx <= loci@.len(),
        ensures
            found_first ==> (first_idx as int) < loci@.len(),
        decreases loci@.len() - first_idx,
    {
        match &loci[first_idx] {
            RuntimeLocus::FullPlane => {
                first_idx = first_idx + 1;
            }
            _ => {
                found_first = true;
                break;
            }
        }
    }

    if !found_first {
        return None;
    }

    assert((first_idx as int) < loci@.len());
    assert(first_idx < loci.len()); // guarantees first_idx + 1 doesn't overflow

    // Second pass: find second nontrivial locus
    let mut second_idx: usize = first_idx + 1;
    let mut found_second = false;
    while second_idx < loci.len()
        invariant_except_break
            first_idx < second_idx && second_idx <= loci@.len(),
            !found_second,
        invariant
            forall|i: int| 0 <= i < loci@.len() ==> (#[trigger] loci@[i]).wf_spec(),
            (first_idx as int) < loci@.len(),
            first_idx < second_idx && second_idx <= loci@.len(),
        ensures
            found_second ==> (second_idx as int) < loci@.len(),
        decreases loci@.len() - second_idx,
    {
        match &loci[second_idx] {
            RuntimeLocus::FullPlane => {
                second_idx = second_idx + 1;
            }
            _ => {
                found_second = true;
                break;
            }
        }
    }

    if !found_second {
        // Only one nontrivial locus — check if it's AtPoint
        match &loci[first_idx] {
            RuntimeLocus::AtPoint { point } => {
                let ghost spec_step = ConstructionStep::<RationalModel>::PointStep {
                    id: target as nat, position: point@,
                };
                return Some(RuntimeStepData::PointStep {
                    target,
                    x: copy_rational(&point.x),
                    y: copy_rational(&point.y),
                    model: Ghost(spec_step),
                });
            }
            _ => {
                return None;
            }
        }
    }

    // Extract the two loci by swapping out of the Vec
    // We need to consume them for intersect_loci_exec
    let mut loci_mut = loci;
    let mut dummy = RuntimeLocus::FullPlane;
    let mut dummy2 = RuntimeLocus::FullPlane;

    // Swap out the second first (to preserve indexing since second_idx > first_idx)
    loci_mut.set_and_swap(second_idx, &mut dummy);
    // Now dummy holds the second locus
    let l2 = dummy;

    // Swap out the first
    loci_mut.set_and_swap(first_idx, &mut dummy2);
    let l1 = dummy2;

    intersect_loci_exec(target, l1, l2)
}

// ===========================================================================
//  Copy helpers
// ===========================================================================

/// Deep-copy a RuntimePoint2.
fn copy_point(p: &RuntimePoint2) -> (out: RuntimePoint2)
    requires p.wf_spec(),
    ensures out.wf_spec(), out@ == p@,
{
    RuntimePoint2::new(copy_rational(&p.x), copy_rational(&p.y))
}

/// Deep-copy a RuntimeLine2.
fn copy_line(l: &RuntimeLine2) -> (out: RuntimeLine2)
    requires l.wf_spec(),
    ensures out.wf_spec(), out@ == l@,
{
    RuntimeLine2::new(copy_rational(&l.a), copy_rational(&l.b), copy_rational(&l.c))
}

/// Deep-copy a RuntimeCircle2.
fn copy_circle(c: &RuntimeCircle2) -> (out: RuntimeCircle2)
    requires c.wf_spec(),
    ensures out.wf_spec(), out@ == c@,
{
    let center = copy_point(&c.center);
    let r_sq = copy_rational(&c.radius_sq);
    RuntimeCircle2::from_center_radius_sq(center, r_sq)
}

/// Deep-copy a RuntimeStepData.
pub fn copy_step(s: &RuntimeStepData) -> (out: RuntimeStepData)
    requires s.wf_spec(),
    ensures out.wf_spec(), out.spec_step() == s.spec_step(),
{
    match s {
        RuntimeStepData::PointStep { target, x, y, model } => {
            RuntimeStepData::PointStep {
                target: *target,
                x: copy_rational(x),
                y: copy_rational(y),
                model: Ghost(model@),
            }
        }
        RuntimeStepData::LineLine { target, l1, l2, model } => {
            RuntimeStepData::LineLine {
                target: *target,
                l1: copy_line(l1),
                l2: copy_line(l2),
                model: Ghost(model@),
            }
        }
        RuntimeStepData::CircleLine { target, circle, line, plus, model } => {
            RuntimeStepData::CircleLine {
                target: *target,
                circle: copy_circle(circle),
                line: copy_line(line),
                plus: *plus,
                model: Ghost(model@),
            }
        }
        RuntimeStepData::CircleCircle { target, c1, c2, plus, model } => {
            RuntimeStepData::CircleCircle {
                target: *target,
                c1: copy_circle(c1),
                c2: copy_circle(c2),
                plus: *plus,
                model: Ghost(model@),
            }
        }
    }
}

// ===========================================================================
//  Greedy solver
// ===========================================================================

/// Greedy solver: iteratively resolve free entities by collecting loci
/// from constraints and intersecting them.
///
/// On each iteration, scans free_ids for a resolvable entity (one with
/// at least two non-trivial loci, or a single AtPoint locus).
/// For circle intersection steps, no coordinate is written to the points
/// array (the plan records the step but coordinates live in Q(sqrt(D))).
/// For line-line and determined steps, the rational coordinates are written.
///
/// Returns the construction plan (sequence of steps).
pub fn greedy_solve_exec(
    free_ids: &Vec<usize>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: Vec<RuntimeStepData>)
    requires
        old(points)@.len() == old(resolved_flags)@.len(),
        all_points_wf(old(points)@),
        forall|i: int| 0 <= i < free_ids@.len() ==>
            (free_ids@[i] as int) < old(points)@.len(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], old(points)@.len() as nat),
        forall|i: int| 0 <= i < old(resolved_flags)@.len() ==>
            (#[trigger] old(resolved_flags)@[i]) ==
            partial_resolved_map(points_view(old(points)@), old(resolved_flags)@)
                .dom().contains(i as nat),
    ensures
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        // All targets are distinct
        forall|i: int, j: int|
            0 <= i < out@.len() && 0 <= j < out@.len() && i != j ==>
            step_target(#[trigger] out@[i].spec_step()) != step_target(#[trigger] out@[j].spec_step()),
        // Each target is a valid entity
        forall|i: int| 0 <= i < out@.len() ==>
            (step_target(#[trigger] out@[i].spec_step()) as int) < old(points)@.len(),
        points@.len() == old(points)@.len(),
        resolved_flags@.len() == old(resolved_flags)@.len(),
        all_points_wf(points@),
{
    let mut plan: Vec<RuntimeStepData> = Vec::new();
    let n = free_ids.len();
    let mut iter: usize = 0;
    assert(resolved_flags@.len() == points@.len());

    while iter < n
        invariant
            0 <= iter <= n,
            n == free_ids@.len(),
            points@.len() == old(points)@.len(),
            resolved_flags@.len() == old(resolved_flags)@.len(),
            resolved_flags@.len() == points@.len(),
            all_points_wf(points@),
            forall|i: int| 0 <= i < free_ids@.len() ==>
                (free_ids@[i] as int) < points@.len(),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
            forall|i: int| 0 <= i < resolved_flags@.len() ==>
                (#[trigger] resolved_flags@[i]) ==
                partial_resolved_map(points_view(points@), resolved_flags@)
                    .dom().contains(i as nat),
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            // All plan targets are currently resolved (flags == true)
            forall|j: int| 0 <= j < plan@.len() ==>
                (step_target(#[trigger] plan@[j].spec_step()) as int) < resolved_flags@.len()
                && resolved_flags@[step_target(plan@[j].spec_step()) as int] == true,
            // All targets are distinct
            forall|i: int, j: int|
                0 <= i < plan@.len() && 0 <= j < plan@.len() && i != j ==>
                step_target(#[trigger] plan@[i].spec_step()) != step_target(#[trigger] plan@[j].spec_step()),
            // Each target is valid
            forall|j: int| 0 <= j < plan@.len() ==>
                (step_target(#[trigger] plan@[j].spec_step()) as int) < points@.len(),
        decreases n - iter,
    {
        let mut found = false;
        let mut fi: usize = 0;
        assert(resolved_flags@.len() == points@.len());
        while fi < n
            invariant_except_break
                !found,
            invariant
                0 <= fi <= n,
                n == free_ids@.len(),
                points@.len() == old(points)@.len(),
                resolved_flags@.len() == old(resolved_flags)@.len(),
                resolved_flags@.len() == points@.len(),
                all_points_wf(points@),
                forall|i: int| 0 <= i < free_ids@.len() ==>
                    (free_ids@[i] as int) < points@.len(),
                forall|i: int| 0 <= i < constraints@.len() ==>
                    runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
                forall|i: int| 0 <= i < resolved_flags@.len() ==>
                    (#[trigger] resolved_flags@[i]) ==
                    partial_resolved_map(points_view(points@), resolved_flags@)
                        .dom().contains(i as nat),
                forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
                forall|j: int| 0 <= j < plan@.len() ==>
                    (step_target(#[trigger] plan@[j].spec_step()) as int) < resolved_flags@.len()
                    && resolved_flags@[step_target(plan@[j].spec_step()) as int] == true,
                forall|i: int, j: int|
                    0 <= i < plan@.len() && 0 <= j < plan@.len() && i != j ==>
                    step_target(#[trigger] plan@[i].spec_step()) != step_target(#[trigger] plan@[j].spec_step()),
                forall|j: int| 0 <= j < plan@.len() ==>
                    (step_target(#[trigger] plan@[j].spec_step()) as int) < points@.len(),
            ensures
                points@.len() == old(points)@.len(),
                resolved_flags@.len() == old(resolved_flags)@.len(),
                resolved_flags@.len() == points@.len(),
                all_points_wf(points@),
                forall|i: int| 0 <= i < free_ids@.len() ==>
                    (free_ids@[i] as int) < points@.len(),
                forall|i: int| 0 <= i < constraints@.len() ==>
                    runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
                forall|i: int| 0 <= i < resolved_flags@.len() ==>
                    (#[trigger] resolved_flags@[i]) ==
                    partial_resolved_map(points_view(points@), resolved_flags@)
                        .dom().contains(i as nat),
                forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
                forall|j: int| 0 <= j < plan@.len() ==>
                    (step_target(#[trigger] plan@[j].spec_step()) as int) < resolved_flags@.len()
                    && resolved_flags@[step_target(plan@[j].spec_step()) as int] == true,
                forall|i: int, j: int|
                    0 <= i < plan@.len() && 0 <= j < plan@.len() && i != j ==>
                    step_target(#[trigger] plan@[i].spec_step()) != step_target(#[trigger] plan@[j].spec_step()),
                forall|j: int| 0 <= j < plan@.len() ==>
                    (step_target(#[trigger] plan@[j].spec_step()) as int) < points@.len(),
            decreases n - fi,
        {
            let target = free_ids[fi];
            assert((free_ids@[fi as int] as int) < points@.len());
            assert((target as int) < points@.len());
            assert((target as int) < resolved_flags@.len());
            if resolved_flags[target] {
                fi = fi + 1;
            } else {
                let loci = collect_loci_exec(constraints, points, resolved_flags, target);
                let step_opt = find_and_intersect_loci(target, loci);
                match step_opt {
                    Some(step) => {
                        // For rational steps, update the points array
                        match &step {
                            RuntimeStepData::PointStep { x, y, .. } => {
                                let mut pt = RuntimePoint2::new(
                                    copy_rational(x), copy_rational(y),
                                );
                                points.set_and_swap(target, &mut pt);
                            }
                            RuntimeStepData::LineLine { l1, l2, .. } => {
                                let mut pt = execute_line_line_step(l1, l2);
                                points.set_and_swap(target, &mut pt);
                            }
                            // Circle steps: don't update coordinates (live in Q(sqrt(D)))
                            RuntimeStepData::CircleLine { .. } => {}
                            RuntimeStepData::CircleCircle { .. } => {}
                        }
                        // Before flipping the flag: target is unresolved, all plan
                        // targets are resolved — so the new target is distinct.
                        proof {
                            assert(resolved_flags@[target as int] == false);
                            assert forall|j: int| 0 <= j < plan@.len() implies
                                step_target(#[trigger] plan@[j].spec_step()) != target as nat
                            by {
                                assert(resolved_flags@[step_target(plan@[j].spec_step()) as int] == true);
                            }
                        }

                        // Mark resolved
                        let mut flag = true;
                        resolved_flags.set_and_swap(target, &mut flag);

                        // Re-establish the partial_resolved_map invariant
                        // and the resolved-targets invariant after set_and_swap
                        proof {
                            // After set_and_swap, resolved_flags@[target] == true
                            // and points@[target] is the new point (wf_spec)
                            // For all i != target, nothing changed
                            assert forall|i: int| 0 <= i < resolved_flags@.len() implies
                                (#[trigger] resolved_flags@[i]) ==
                                partial_resolved_map(points_view(points@), resolved_flags@)
                                    .dom().contains(i as nat)
                            by {
                                // partial_resolved_map.dom().contains(i as nat)
                                // == (i < points.len() && i < flags.len() && flags[i])
                                // == flags[i]  (since both lens are the same and i < len)
                            }
                        }

                        // The new step's target == target, which was proved distinct
                        // from all existing plan targets above. After set_and_swap,
                        // resolved_flags[target] == true, so the invariant is maintained.
                        assert(step_target(step.spec_step()) == target as nat);
                        assert(resolved_flags@[target as int] == true);

                        plan.push(step);
                        found = true;
                        break;
                    }
                    None => {
                        fi = fi + 1;
                    }
                }
            }
        }

        if !found {
            break;
        }
        iter = iter + 1;
    }
    plan
}

// ===========================================================================
//  Sign variant enumeration
// ===========================================================================

/// Count the number of circle intersection steps in a plan.
pub fn count_circle_steps(plan: &Vec<RuntimeStepData>) -> (out: usize)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
    ensures
        out <= plan@.len(),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < plan.len()
        invariant
            0 <= i <= plan@.len(),
            count <= i,
        decreases plan@.len() - i,
    {
        match &plan[i] {
            RuntimeStepData::CircleLine { .. } => { count = count + 1; }
            RuntimeStepData::CircleCircle { .. } => { count = count + 1; }
            _ => {}
        }
        i = i + 1;
    }
    count
}

/// Flip the `plus` sign of a circle step. Non-circle steps are returned unchanged.
/// Takes ownership and returns a new step with the sign flipped.
fn flip_step_sign(s: RuntimeStepData) -> (out: RuntimeStepData)
    requires s.wf_spec(),
    ensures
        out.wf_spec(),
        step_target(out.spec_step()) == step_target(s.spec_step()),
        step_has_positive_discriminant(s.spec_step()) ==
            step_has_positive_discriminant(out.spec_step()),
{
    match s {
        RuntimeStepData::CircleLine { target, circle, line, plus, model } => {
            let ghost new_model = match model@ {
                ConstructionStep::CircleLine { id, circle: c, line: l, .. } =>
                    ConstructionStep::<RationalModel>::CircleLine {
                        id, circle: c, line: l, plus: !plus,
                    },
                _ => model@, // unreachable
            };
            RuntimeStepData::CircleLine {
                target, circle, line, plus: !plus,
                model: Ghost(new_model),
            }
        }
        RuntimeStepData::CircleCircle { target, c1, c2, plus, model } => {
            let ghost new_model = match model@ {
                ConstructionStep::CircleCircle { id, circle1, circle2, .. } =>
                    ConstructionStep::<RationalModel>::CircleCircle {
                        id, circle1, circle2, plus: !plus,
                    },
                _ => model@, // unreachable
            };
            RuntimeStepData::CircleCircle {
                target, c1, c2, plus: !plus,
                model: Ghost(new_model),
            }
        }
        _ => s,
    }
}

/// Create a sign variant of a plan by flipping the k-th circle step
/// when bit k of sign_mask is 1.
fn make_sign_variant(
    plan: &Vec<RuntimeStepData>,
    sign_mask: u64,
) -> (out: Vec<RuntimeStepData>)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
    ensures
        out@.len() == plan@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        // Target preservation
        forall|i: int| 0 <= i < out@.len() ==>
            step_target((#[trigger] out@[i]).spec_step()) ==
            step_target(plan@[i].spec_step()),
        // Discriminant preservation
        forall|i: int| 0 <= i < out@.len() ==>
            step_has_positive_discriminant((#[trigger] out@[i]).spec_step()) ==
            step_has_positive_discriminant(plan@[i].spec_step()),
{
    let mut result: Vec<RuntimeStepData> = Vec::new();
    let mut circle_idx: u64 = 0;
    let mut i: usize = 0;
    while i < plan.len()
        invariant
            0 <= i <= plan@.len(),
            result@.len() == i as int,
            circle_idx <= i as u64,
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==>
                step_target((#[trigger] result@[j]).spec_step()) ==
                step_target(plan@[j].spec_step()),
            forall|j: int| 0 <= j < result@.len() ==>
                step_has_positive_discriminant((#[trigger] result@[j]).spec_step()) ==
                step_has_positive_discriminant(plan@[j].spec_step()),
        decreases plan@.len() - i,
    {
        let s = copy_step(&plan[i]);
        match &plan[i] {
            RuntimeStepData::CircleLine { .. } => {
                if circle_idx < 64 && (sign_mask >> circle_idx) & 1 == 1 {
                    result.push(flip_step_sign(s));
                } else {
                    result.push(s);
                }
                circle_idx = circle_idx + 1;
            }
            RuntimeStepData::CircleCircle { .. } => {
                if circle_idx < 64 && (sign_mask >> circle_idx) & 1 == 1 {
                    result.push(flip_step_sign(s));
                } else {
                    result.push(s);
                }
                circle_idx = circle_idx + 1;
            }
            _ => {
                result.push(s);
            }
        }
        i = i + 1;
    }
    result
}

/// Check if a plan variant is feasible: all circle steps have positive discriminant.
fn check_variant_feasible(plan: &Vec<RuntimeStepData>) -> (out: bool)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
    ensures
        out ==> forall|i: int| 0 <= i < plan@.len() ==>
            step_has_positive_discriminant((#[trigger] plan@[i]).spec_step()),
{
    let mut i: usize = 0;
    let zero = RuntimeRational::from_int(0);
    while i < plan.len()
        invariant
            0 <= i <= plan@.len(),
            zero.wf_spec(),
            zero@ == RationalModel::from_int_spec(0),
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            // All checked steps so far have positive discriminant
            forall|j: int| 0 <= j < i ==>
                step_has_positive_discriminant((#[trigger] plan@[j]).spec_step()),
        decreases plan@.len() - i,
    {
        match &plan[i] {
            RuntimeStepData::CircleLine { circle, line, .. } => {
                let disc = verus_geometry::runtime::circle_line::cl_discriminant_exec(circle, line);
                if !zero.lt(&disc) {
                    return false;
                }
            }
            RuntimeStepData::CircleCircle { c1, c2, .. } => {
                let disc = verus_geometry::runtime::circle_circle::cc_discriminant_exec(c1, c2);
                if !zero.lt(&disc) {
                    return false;
                }
            }
            _ => {}
        }
        i = i + 1;
    }
    true
}

/// Solve all sign variants: run the greedy solver, then enumerate
/// all 2^k sign combinations (where k = number of circle steps).
/// Returns all feasible plan variants.
pub fn solve_all_variants(
    free_ids: &Vec<usize>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: Vec<Vec<RuntimeStepData>>)
    requires
        old(points)@.len() == old(resolved_flags)@.len(),
        all_points_wf(old(points)@),
        forall|i: int| 0 <= i < free_ids@.len() ==>
            (free_ids@[i] as int) < old(points)@.len(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], old(points)@.len() as nat),
        forall|i: int| 0 <= i < old(resolved_flags)@.len() ==>
            (#[trigger] old(resolved_flags)@[i]) ==
            partial_resolved_map(points_view(old(points)@), old(resolved_flags)@)
                .dom().contains(i as nat),
    ensures
        // All steps well-formed
        forall|si: int| 0 <= si < out@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] out@[si])@.len() ==>
                (#[trigger] out@[si]@[j]).wf_spec(),
        // Distinct targets within each variant
        forall|si: int| 0 <= si < out@.len() ==>
            forall|i: int, j: int|
                0 <= i < (#[trigger] out@[si])@.len()
                && 0 <= j < out@[si]@.len() && i != j ==>
                step_target(#[trigger] out@[si]@[i].spec_step()) !=
                step_target(#[trigger] out@[si]@[j].spec_step()),
        // All circle discriminants positive
        forall|si: int| 0 <= si < out@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] out@[si])@.len() ==>
                step_has_positive_discriminant((#[trigger] out@[si]@[j]).spec_step()),
        // All targets are valid entity indices
        forall|si: int| 0 <= si < out@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] out@[si])@.len() ==>
                (step_target((#[trigger] out@[si]@[j]).spec_step()) as int) < old(points)@.len(),
        // All variants have equal length
        out@.len() > 0 ==>
            forall|si: int| 0 <= si < out@.len() ==>
                (#[trigger] out@[si])@.len() == out@[0]@.len(),
        // All steps satisfy geometric preconditions (step_well_formed minus
        // the existential witness for circle steps)
        forall|si: int| 0 <= si < out@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] out@[si])@.len() ==>
                step_geometrically_valid((#[trigger] out@[si]@[j]).spec_step()),
{
    let plan = greedy_solve_exec(free_ids, constraints, points, resolved_flags);
    let k = count_circle_steps(&plan);

    if k == 0 || k > 63 {
        // No circle steps, or too many to enumerate — return base plan
        // if feasible (all discriminants positive).
        let mut results: Vec<Vec<RuntimeStepData>> = Vec::new();
        if check_variant_feasible(&plan) {
            results.push(plan);
        }
        return results;
    }

    let n: u64 = 1u64 << (k as u64);
    let mut results: Vec<Vec<RuntimeStepData>> = Vec::new();
    let mut mask: u64 = 0;
    while mask < n
        invariant
            0 <= mask <= n,
            n == 1u64 << (k as u64),
            k <= 63,
            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
            // Base plan has distinct targets
            forall|i: int, j: int|
                0 <= i < plan@.len() && 0 <= j < plan@.len() && i != j ==>
                step_target(#[trigger] plan@[i].spec_step()) != step_target(#[trigger] plan@[j].spec_step()),
            // Base plan targets are valid
            forall|i: int| 0 <= i < plan@.len() ==>
                (step_target(#[trigger] plan@[i].spec_step()) as int) < old(points)@.len(),
            forall|si: int| 0 <= si < results@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] results@[si])@.len() ==>
                    (#[trigger] results@[si]@[j]).wf_spec(),
            forall|si: int| 0 <= si < results@.len() ==>
                forall|i: int, j: int|
                    0 <= i < (#[trigger] results@[si])@.len()
                    && 0 <= j < results@[si]@.len() && i != j ==>
                    step_target(#[trigger] results@[si]@[i].spec_step()) !=
                    step_target(#[trigger] results@[si]@[j].spec_step()),
            forall|si: int| 0 <= si < results@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] results@[si])@.len() ==>
                    step_has_positive_discriminant((#[trigger] results@[si]@[j]).spec_step()),
            // Target validity for results
            forall|si: int| 0 <= si < results@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] results@[si])@.len() ==>
                    (step_target((#[trigger] results@[si]@[j]).spec_step()) as int) < old(points)@.len(),
            // All result variants have same length as base plan
            forall|si: int| 0 <= si < results@.len() ==>
                (#[trigger] results@[si])@.len() == plan@.len(),
            // Geometric validity for results
            forall|si: int| 0 <= si < results@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] results@[si])@.len() ==>
                    step_geometrically_valid((#[trigger] results@[si]@[j]).spec_step()),
        decreases n - mask,
    {
        let variant = make_sign_variant(&plan, mask);
        // Derive properties for variant from base plan via target preservation
        proof {
            assert forall|i: int, j: int|
                0 <= i < variant@.len() && 0 <= j < variant@.len() && i != j
            implies
                step_target(#[trigger] variant@[i].spec_step()) !=
                step_target(#[trigger] variant@[j].spec_step())
            by {
                assert(step_target(variant@[i].spec_step()) == step_target(plan@[i].spec_step()));
                assert(step_target(variant@[j].spec_step()) == step_target(plan@[j].spec_step()));
            }
            // Target validity: variant targets == plan targets < old(points).len()
            assert forall|j: int| 0 <= j < variant@.len()
            implies
                (step_target((#[trigger] variant@[j]).spec_step()) as int) < old(points)@.len()
            by {
                assert(step_target(variant@[j].spec_step()) == step_target(plan@[j].spec_step()));
            }
            // Geometric validity: wf_spec() implies step_geometrically_valid
            assert forall|j: int| 0 <= j < variant@.len()
            implies
                step_geometrically_valid((#[trigger] variant@[j]).spec_step())
            by {
                assert(variant@[j].wf_spec());
            }
        }
        if check_variant_feasible(&variant) {
            results.push(variant);
        }
        mask = mask + 1;
    }
    results
}

// ===========================================================================
//  Verification constraint checker
// ===========================================================================

/// Check whether a runtime constraint is a verification constraint.
/// Requires runtime_constraint_wf so that model@ is known to match the variant.
fn is_verification_constraint_exec(rc: &RuntimeConstraint, n_points: usize) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, n_points as nat),
    ensures
        out == is_verification_constraint(runtime_constraint_model(*rc)),
{
    match rc {
        RuntimeConstraint::Tangent { .. } => true,
        RuntimeConstraint::CircleTangent { .. } => true,
        RuntimeConstraint::Angle { .. } => true,
        _ => false,
    }
}

/// Check all verification constraints are satisfied by the final resolved points.
/// Returns true if every verification constraint in the list is satisfied.
pub fn check_verification_constraints_exec(
    constraints: &Vec<RuntimeConstraint>,
    points: &Vec<RuntimePoint2>,
) -> (out: bool)
    requires
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
        all_points_wf(points@),
    ensures
        out ==> forall|ci: int|
            0 <= ci < constraints@.len()
            && is_verification_constraint(runtime_constraint_model(#[trigger] constraints@[ci]))
            ==> constraint_satisfied(
                runtime_constraint_model(constraints@[ci]),
                vec_to_resolved_map(points_view(points@)),
            ),
{
    let mut i: usize = 0;
    while i < constraints.len()
        invariant
            i <= constraints@.len(),
            forall|j: int| 0 <= j < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[j], points@.len() as nat),
            all_points_wf(points@),
            forall|ci: int|
                0 <= ci < i
                && is_verification_constraint(runtime_constraint_model(#[trigger] constraints@[ci]))
                ==> constraint_satisfied(
                    runtime_constraint_model(constraints@[ci]),
                    vec_to_resolved_map(points_view(points@)),
                ),
        decreases constraints@.len() - i,
    {
        if is_verification_constraint_exec(&constraints[i], points.len()) {
            if !check_constraint_satisfied_exec(&constraints[i], points) {
                return false;
            }
        }
        i = i + 1;
    }
    true
}

// ===========================================================================
//  Runtime nontrivial locus counting
// ===========================================================================

/// Check if a single runtime constraint imposes a nontrivial locus on `target`.
/// A constraint is nontrivial for target when:
/// 1. target is a locus entity of the constraint
/// 2. all other entities of the constraint are resolved
/// 3. target itself is not resolved
fn is_nontrivial_for_target_exec(
    rc: &RuntimeConstraint,
    target: usize,
    resolved_flags: &Vec<bool>,
    n_points: usize,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, n_points as nat),
        resolved_flags@.len() == n_points,
        (target as int) < n_points,
    ensures
        out == is_nontrivial_for_target(
            runtime_constraint_model(*rc),
            target as nat,
            Set::new(|id: nat| (id as int) < n_points && resolved_flags@[id as int]),
        ),
{
    let ghost dom = Set::new(|id: nat| (id as int) < n_points && resolved_flags@[id as int]);
    let ghost model = runtime_constraint_model(*rc);

    // target must not be resolved
    if resolved_flags[target] {
        proof {
            assert(dom.contains(target as nat));
            assert(!is_nontrivial_for_target(model, target as nat, dom));
        }
        return false;
    }

    // The spec is now defined per-variant with explicit membership checks,
    // matching the runtime branching directly. Z3 unfolds both in parallel.
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => {
            if target == *a {
                resolved_flags[*b]
            } else if target == *b {
                resolved_flags[*a]
            } else {
                false
            }
        }
        RuntimeConstraint::DistanceSq { a, b, .. } => {
            if target == *a {
                resolved_flags[*b]
            } else if target == *b {
                resolved_flags[*a]
            } else {
                false
            }
        }
        RuntimeConstraint::FixedX { point, .. } => {
            target == *point
        }
        RuntimeConstraint::FixedY { point, .. } => {
            target == *point
        }
        RuntimeConstraint::SameX { a, b, .. } => {
            if target == *a {
                resolved_flags[*b]
            } else if target == *b {
                resolved_flags[*a]
            } else {
                false
            }
        }
        RuntimeConstraint::SameY { a, b, .. } => {
            if target == *a {
                resolved_flags[*b]
            } else if target == *b {
                resolved_flags[*a]
            } else {
                false
            }
        }
        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } => {
            if target == *point {
                resolved_flags[*line_a] && resolved_flags[*line_b]
            } else {
                false
            }
        }
        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } => {
            if target == *a1 {
                resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2]
            } else if target == *a2 {
                resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2]
            } else {
                false
            }
        }
        RuntimeConstraint::Midpoint { mid, a, b, .. } => {
            if target == *mid {
                resolved_flags[*a] && resolved_flags[*b]
            } else if target == *a {
                resolved_flags[*mid] && resolved_flags[*b]
            } else if target == *b {
                resolved_flags[*mid] && resolved_flags[*a]
            } else {
                false
            }
        }
        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } => {
            if target == *a1 {
                resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2]
            } else if target == *a2 {
                resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2]
            } else {
                false
            }
        }
        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } => {
            if target == *a1 {
                resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2]
            } else if target == *a2 {
                resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2]
            } else {
                false
            }
        }
        RuntimeConstraint::Collinear { a, b, c, .. } => {
            if target == *a {
                resolved_flags[*b] && resolved_flags[*c]
            } else if target == *b {
                resolved_flags[*a] && resolved_flags[*c]
            } else if target == *c {
                resolved_flags[*a] && resolved_flags[*b]
            } else {
                false
            }
        }
        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } => {
            if target == *point {
                resolved_flags[*center] && resolved_flags[*radius_point]
            } else {
                false
            }
        }
        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
            if target == *point {
                resolved_flags[*original] && resolved_flags[*axis_a] && resolved_flags[*axis_b]
            } else {
                false
            }
        }
        RuntimeConstraint::FixedPoint { point, .. } => {
            target == *point
        }
        RuntimeConstraint::Ratio { a1, a2, b1, b2, .. } => {
            if target == *a1 {
                resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2]
            } else if target == *a2 {
                resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2]
            } else {
                false
            }
        }
        RuntimeConstraint::Tangent { .. } => {
            false
        }
        RuntimeConstraint::CircleTangent { .. } => {
            false
        }
        RuntimeConstraint::Angle { .. } => {
            false
        }
    }
}

/// Spec: count nontrivial constraints for target in constraints[0..n).
spec fn count_nontrivial<T: OrderedField>(
    constraints: Seq<Constraint<T>>,
    target: EntityId,
    dom: Set<EntityId>,
    n: int,
) -> nat
    decreases n,
{
    if n <= 0 { 0 }
    else {
        let prev = count_nontrivial(constraints, target, dom, n - 1);
        if is_nontrivial_for_target(constraints[n - 1], target, dom) {
            prev + 1
        } else {
            prev
        }
    }
}

/// If count_nontrivial <= 2, then at_most_two_nontrivial_loci holds.
proof fn lemma_count_implies_at_most_two<T: OrderedField>(
    constraints: Seq<Constraint<T>>,
    target: EntityId,
    dom: Set<EntityId>,
)
    requires
        count_nontrivial(constraints, target, dom, constraints.len() as int) <= 2,
    ensures
        at_most_two_nontrivial_loci(target, constraints, dom),
    decreases constraints.len(),
{
    // By contradiction: if there exist i < j < k all nontrivial,
    // then count >= 3. We prove count_nontrivial >= 3 in presence of such triple.
    if exists|ii: int, jj: int, kk: int|
        0 <= ii < jj && jj < kk && kk < constraints.len()
        && is_nontrivial_for_target(#[trigger] constraints[ii], target, dom)
        && is_nontrivial_for_target(#[trigger] constraints[jj], target, dom)
        && is_nontrivial_for_target(#[trigger] constraints[kk], target, dom)
    {
        let ii = choose|ii: int| exists|jj: int, kk: int|
            0 <= ii < jj && jj < kk && kk < constraints.len()
            && is_nontrivial_for_target(#[trigger] constraints[ii], target, dom)
            && is_nontrivial_for_target(#[trigger] constraints[jj], target, dom)
            && is_nontrivial_for_target(#[trigger] constraints[kk], target, dom);
        let jj = choose|jj: int| exists|kk: int|
            0 <= ii < jj && jj < kk && kk < constraints.len()
            && is_nontrivial_for_target(constraints[ii], target, dom)
            && is_nontrivial_for_target(#[trigger] constraints[jj], target, dom)
            && is_nontrivial_for_target(#[trigger] constraints[kk], target, dom);
        let kk = choose|kk: int|
            0 <= ii < jj && jj < kk && kk < constraints.len()
            && is_nontrivial_for_target(constraints[ii], target, dom)
            && is_nontrivial_for_target(constraints[jj], target, dom)
            && is_nontrivial_for_target(#[trigger] constraints[kk], target, dom);
        // count >= 3 because each of ii, jj, kk adds 1
        lemma_count_monotone::<T>(constraints, target, dom, kk + 1, constraints.len() as int);
        lemma_count_at_least_one::<T>(constraints, target, dom, kk);
        lemma_count_monotone::<T>(constraints, target, dom, jj + 1, kk);
        lemma_count_at_least_one::<T>(constraints, target, dom, jj);
        lemma_count_monotone::<T>(constraints, target, dom, ii + 1, jj);
        lemma_count_at_least_one::<T>(constraints, target, dom, ii);
        // Chain: count(n) >= count(kk+1) >= count(kk) + 1 >= count(jj+1) + 1 >= count(jj) + 2
        //        >= count(ii+1) + 2 >= count(ii) + 3 >= 3
        assert(count_nontrivial(constraints, target, dom, constraints.len() as int) >= 3);
    }
}

/// Count is monotonically non-decreasing.
proof fn lemma_count_monotone<T: OrderedField>(
    constraints: Seq<Constraint<T>>,
    target: EntityId,
    dom: Set<EntityId>,
    a: int, b: int,
)
    requires 0 <= a <= b, b <= constraints.len(),
    ensures count_nontrivial(constraints, target, dom, a) <= count_nontrivial(constraints, target, dom, b),
    decreases b - a,
{
    if a == b {
    } else {
        lemma_count_monotone::<T>(constraints, target, dom, a, b - 1);
    }
}

/// If constraint[n] is nontrivial, count(n+1) >= count(n) + 1.
proof fn lemma_count_at_least_one<T: OrderedField>(
    constraints: Seq<Constraint<T>>,
    target: EntityId,
    dom: Set<EntityId>,
    n: int,
)
    requires
        0 <= n < constraints.len(),
        is_nontrivial_for_target(constraints[n], target, dom),
    ensures
        count_nontrivial(constraints, target, dom, n + 1) >=
        count_nontrivial(constraints, target, dom, n) + 1,
{
    // Direct from definition: count(n+1) = count(n) + (if nontrivial(n) then 1 else 0)
}

/// Runtime check: at most two constraints impose nontrivial loci on `target`.
fn check_at_most_two_nontrivial_exec(
    target: usize,
    constraints: &Vec<RuntimeConstraint>,
    resolved_flags: &Vec<bool>,
    n_points: usize,
) -> (out: bool)
    requires
        (target as int) < n_points,
        resolved_flags@.len() == n_points,
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
    ensures
        out ==> at_most_two_nontrivial_loci(
            target as nat,
            Seq::new(constraints@.len(), |i: int| runtime_constraint_model(constraints@[i])),
            Set::new(|id: nat| (id as int) < n_points && resolved_flags@[id as int]),
        ),
{
    let ghost dom = Set::new(|id: nat| (id as int) < n_points && resolved_flags@[id as int]);
    let n = constraints.len();
    let ghost spec_cs: Seq<Constraint<RationalModel>> = Seq::new(n as nat, |j: int| runtime_constraint_model(constraints@[j]));

    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n == constraints@.len(),
            i <= n,
            count <= 2,
            (target as int) < n_points,
            resolved_flags@.len() == n_points,
            dom == Set::new(|id: nat| (id as int) < n_points && resolved_flags@[id as int]),
            forall|j: int| 0 <= j < n ==>
                runtime_constraint_wf(#[trigger] constraints@[j], n_points as nat),
            spec_cs.len() == n as int,
            forall|j: int| 0 <= j < n ==>
                spec_cs[j] == runtime_constraint_model(#[trigger] constraints@[j]),
            // count == spec count of nontrivial in [0, i)
            count as nat == count_nontrivial(spec_cs, target as nat, dom, i as int),
        decreases n - i,
    {
        let is_nt = is_nontrivial_for_target_exec(&constraints[i], target, resolved_flags, n_points);
        proof {
            // is_nt == is_nontrivial_for_target(runtime_constraint_model(constraints@[i]), target, dom)
            //       == is_nontrivial_for_target(spec_cs[i], target, dom)
            // So we need: count_nontrivial(spec_cs, target, dom, i+1)
            //           = count_nontrivial(spec_cs, target, dom, i) + (if is_nt then 1 else 0)
            // This is the one-step unfolding of the recursive definition
            let ii = (i + 1) as int;
            // Unfold: count_nontrivial(spec_cs, target, dom, ii)
            //       = let prev = count_nontrivial(spec_cs, target, dom, ii - 1) [= count]
            //         if is_nontrivial_for_target(spec_cs[ii - 1], target, dom) { prev + 1 } else { prev }
            // ii - 1 == i, spec_cs[i] == runtime_constraint_model(constraints@[i])
            // is_nontrivial_for_target(spec_cs[i], target, dom) == is_nt
            // From is_nontrivial_for_target_exec postcondition:
            // is_nt == is_nontrivial_for_target(runtime_constraint_model(constraints@[i as int]), target as nat, dom)
            // From invariant forall:
            // spec_cs[i as int] == runtime_constraint_model(constraints@[i as int])
            // The postcondition of is_nontrivial_for_target_exec gives us:
            // is_nt == is_nontrivial_for_target(runtime_constraint_model(constraints@[i]),
            //          target as nat, Set::new(...))
            // The invariant carries dom == Set::new(...), so these match.
            // spec_cs[i] == runtime_constraint_model(constraints@[i]) from invariant forall.
            // Therefore: is_nt == is_nontrivial_for_target(spec_cs[i], target, dom).
        }
        if is_nt {
            if count >= 2 {
                return false;
            }
            count = count + 1;
        }
        i = i + 1;
    }
    proof {
        // count == count_nontrivial(spec_cs, target, dom, len) <= 2
        lemma_count_implies_at_most_two(spec_cs, target as nat, dom);
    }
    true
}

// ===========================================================================
//  Round 1: Runtime plan soundness checks
// ===========================================================================

/// Helper: get all entity IDs of a runtime constraint as a small Vec.
pub fn constraint_entity_ids(rc: &RuntimeConstraint, n_points: usize) -> (out: Vec<usize>)
    requires runtime_constraint_wf(*rc, n_points as nat),
    ensures
        // Forward: all Vec elements are in constraint_entities
        forall|j: int| 0 <= j < out@.len() ==>
            constraint_entities(runtime_constraint_model(*rc)).contains(#[trigger] out@[j] as nat),
        // Backward: all constraint_entities elements are in the Vec
        forall|e: nat| constraint_entities(runtime_constraint_model(*rc)).contains(e) ==>
            exists|j: int| 0 <= j < out@.len() && out@[j] as nat == e,
        // All elements < n_points
        forall|j: int| 0 <= j < out@.len() ==> (#[trigger] out@[j] as int) < n_points,
{
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => {
            let mut v = Vec::new(); v.push(*a); v.push(*b);
            proof { assert(v@[0] == *a); assert(v@[1] == *b); } v
        }
        RuntimeConstraint::DistanceSq { a, b, .. } => {
            let mut v = Vec::new(); v.push(*a); v.push(*b);
            proof { assert(v@[0] == *a); assert(v@[1] == *b); } v
        }
        RuntimeConstraint::FixedX { point, .. } => {
            let mut v = Vec::new(); v.push(*point);
            proof { assert(v@[0] == *point); } v
        }
        RuntimeConstraint::FixedY { point, .. } => {
            let mut v = Vec::new(); v.push(*point);
            proof { assert(v@[0] == *point); } v
        }
        RuntimeConstraint::SameX { a, b, .. } => {
            let mut v = Vec::new(); v.push(*a); v.push(*b);
            proof { assert(v@[0] == *a); assert(v@[1] == *b); } v
        }
        RuntimeConstraint::SameY { a, b, .. } => {
            let mut v = Vec::new(); v.push(*a); v.push(*b);
            proof { assert(v@[0] == *a); assert(v@[1] == *b); } v
        }
        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } => {
            let mut v = Vec::new(); v.push(*point); v.push(*line_a); v.push(*line_b);
            proof { assert(v@[0] == *point); assert(v@[1] == *line_a); assert(v@[2] == *line_b); } v
        }
        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } => {
            let mut v = Vec::new(); v.push(*a1); v.push(*a2); v.push(*b1); v.push(*b2);
            proof { assert(v@[0] == *a1); assert(v@[1] == *a2); assert(v@[2] == *b1); assert(v@[3] == *b2); } v
        }
        RuntimeConstraint::Midpoint { mid, a, b, .. } => {
            let mut v = Vec::new(); v.push(*mid); v.push(*a); v.push(*b);
            proof { assert(v@[0] == *mid); assert(v@[1] == *a); assert(v@[2] == *b); } v
        }
        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } => {
            let mut v = Vec::new(); v.push(*a1); v.push(*a2); v.push(*b1); v.push(*b2);
            proof { assert(v@[0] == *a1); assert(v@[1] == *a2); assert(v@[2] == *b1); assert(v@[3] == *b2); } v
        }
        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } => {
            let mut v = Vec::new(); v.push(*a1); v.push(*a2); v.push(*b1); v.push(*b2);
            proof { assert(v@[0] == *a1); assert(v@[1] == *a2); assert(v@[2] == *b1); assert(v@[3] == *b2); } v
        }
        RuntimeConstraint::Collinear { a, b, c, .. } => {
            let mut v = Vec::new(); v.push(*a); v.push(*b); v.push(*c);
            proof { assert(v@[0] == *a); assert(v@[1] == *b); assert(v@[2] == *c); } v
        }
        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } => {
            let mut v = Vec::new(); v.push(*point); v.push(*center); v.push(*radius_point);
            proof { assert(v@[0] == *point); assert(v@[1] == *center); assert(v@[2] == *radius_point); } v
        }
        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
            let mut v = Vec::new(); v.push(*point); v.push(*original); v.push(*axis_a); v.push(*axis_b);
            proof { assert(v@[0] == *point); assert(v@[1] == *original); assert(v@[2] == *axis_a); assert(v@[3] == *axis_b); } v
        }
        RuntimeConstraint::FixedPoint { point, .. } => {
            let mut v = Vec::new(); v.push(*point);
            proof { assert(v@[0] == *point); } v
        }
        RuntimeConstraint::Ratio { a1, a2, b1, b2, .. } => {
            let mut v = Vec::new(); v.push(*a1); v.push(*a2); v.push(*b1); v.push(*b2);
            proof { assert(v@[0] == *a1); assert(v@[1] == *a2); assert(v@[2] == *b1); assert(v@[3] == *b2); } v
        }
        RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, .. } => {
            let mut v = Vec::new(); v.push(*line_a); v.push(*line_b); v.push(*center); v.push(*radius_point);
            proof { assert(v@[0] == *line_a); assert(v@[1] == *line_b); assert(v@[2] == *center); assert(v@[3] == *radius_point); } v
        }
        RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, .. } => {
            let mut v = Vec::new(); v.push(*c1); v.push(*rp1); v.push(*c2); v.push(*rp2);
            proof { assert(v@[0] == *c1); assert(v@[1] == *rp1); assert(v@[2] == *c2); assert(v@[3] == *rp2); } v
        }
        RuntimeConstraint::Angle { a1, a2, b1, b2, .. } => {
            let mut v = Vec::new(); v.push(*a1); v.push(*a2); v.push(*b1); v.push(*b2);
            proof { assert(v@[0] == *a1); assert(v@[1] == *a2); assert(v@[2] == *b1); assert(v@[3] == *b2); } v
        }
    }
}

// --- 1a: check_is_fully_independent_exec ---

/// Build a boolean flag array where flags[e] == true iff e is a circle step target.
fn build_circle_flags(
    plan: &Vec<RuntimeStepData>,
    n_points: usize,
) -> (out: Vec<bool>)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < plan@.len() ==>
            (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
    ensures
        out@.len() == n_points as int,
        forall|e: int| 0 <= e < n_points ==>
            (out@[e] == circle_targets(plan_to_spec(plan@)).contains(e as nat)),
{
    let ghost plan_spec = plan_to_spec(plan@);

    let mut flags: Vec<bool> = Vec::new();
    let mut k: usize = 0;
    while k < n_points
        invariant k <= n_points, flags@.len() == k as int,
            forall|e: int| 0 <= e < k ==> flags@[e] == false,
        decreases n_points - k,
    {
        flags.push(false);
        k = k + 1;
    }

    let mut si: usize = 0;
    while si < plan.len()
        invariant
            si <= plan@.len(),
            flags@.len() == n_points as int,
            plan_spec == plan_to_spec(plan@),
            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
            forall|i: int| 0 <= i < plan@.len() ==>
                (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
            // Forward: flagged → is circle target
            forall|e: int| 0 <= e < n_points && flags@[e] ==>
                circle_targets(plan_spec).contains(e as nat),
            // Backward partial: circle steps [0, si) have targets flagged
            forall|k: int| 0 <= k < si && !is_rational_step(plan_spec[k]) ==>
                flags@[step_target(plan_spec[k]) as int] == true,
        decreases plan@.len() - si,
    {
        if plan[si].is_circle_step() {
            let t = plan[si].target_id();
            proof {
                assert(!is_rational_step(plan_spec[si as int]));
                assert(step_target(plan_spec[si as int]) == t as nat);
            }
            flags.set(t, true);
        }
        si = si + 1;
    }

    proof {
        // Backward: if e ∈ circle_targets(plan_spec), then flags[e] is true
        assert forall|e: int| 0 <= e < n_points &&
            circle_targets(plan_spec).contains(e as nat)
        implies flags@[e] == true
        by {
            let k = choose|k: int| 0 <= k < plan_spec.len() &&
                !is_rational_step(#[trigger] plan_spec[k]) &&
                step_target(plan_spec[k]) == e as nat;
            assert(!is_rational_step(plan_spec[k]));
            assert(flags@[step_target(plan_spec[k]) as int] == true);
        }
        // Combine into biconditional
        assert forall|e: int| 0 <= e < n_points implies
            flags@[e] == circle_targets(plan_spec).contains(e as nat)
        by {
            if flags@[e] {
                assert(circle_targets(plan_spec).contains(e as nat));
            }
            if circle_targets(plan_spec).contains(e as nat) {
                assert(flags@[e] == true);
            }
        }
    }
    flags
}

/// Check one constraint is independent w.r.t. target and circle_flags.
/// Returns true if: either target is not in the constraint's entities,
/// or all other entities are not flagged as circle targets.
fn check_one_constraint_independent(
    rc: &RuntimeConstraint,
    target: usize,
    circle_flags: &Vec<bool>,
    n_points: usize,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, n_points as nat),
        circle_flags@.len() == n_points as int,
        (target as int) < n_points,
    ensures
        out && constraint_entities(runtime_constraint_model(*rc)).contains(target as nat) ==>
            forall|e: EntityId|
                constraint_entities(runtime_constraint_model(*rc)).contains(e) && e != (target as nat)
                ==> (e as int) < n_points && !circle_flags@[e as int],
{
    let entities = constraint_entity_ids(rc, n_points);

    // Check if target is among entities
    let mut has_target = false;
    let mut ei: usize = 0;
    while ei < entities.len()
        invariant
            ei <= entities@.len(),
            !has_target ==> forall|j: int| 0 <= j < ei ==> entities@[j] != target,
        decreases entities@.len() - ei,
    {
        if entities[ei] == target { has_target = true; }
        ei = ei + 1;
    }

    if !has_target {
        // target not in constraint entities → postcondition vacuously true
        proof {
            if constraint_entities(runtime_constraint_model(*rc)).contains(target as nat) {
                // By backward ensures of constraint_entity_ids, there is a j
                let j = choose|j: int| 0 <= j < entities@.len()
                    && entities@[j] as nat == (target as nat);
                // entities@[j] as nat == target as nat means entities@[j] == target (both usize)
                assert(entities@[j] != target); // from !has_target invariant
                assert(false); // contradiction
            }
        }
        return true;
    }

    // has_target: check all other entities are not flagged
    let mut ei2: usize = 0;
    while ei2 < entities.len()
        invariant
            ei2 <= entities@.len(),
            circle_flags@.len() == n_points as int,
            forall|j: int| 0 <= j < ei2 && entities@[j] != target ==>
                !circle_flags@[entities@[j] as int],
            forall|j: int| 0 <= j < entities@.len() ==>
                constraint_entities(runtime_constraint_model(*rc)).contains(entities@[j] as nat),
            forall|j: int| 0 <= j < entities@.len() ==>
                (entities@[j] as int) < n_points,
        decreases entities@.len() - ei2,
    {
        let e = entities[ei2];
        if e != target && circle_flags[e] {
            return false;
        }
        ei2 = ei2 + 1;
    }

    // All other entities are not flagged → prove postcondition
    proof {
        assert forall|e_nat: EntityId|
            constraint_entities(runtime_constraint_model(*rc)).contains(e_nat)
            && e_nat != (target as nat)
        implies (e_nat as int) < n_points && !circle_flags@[e_nat as int]
        by {
            let j = choose|j: int| 0 <= j < entities@.len()
                && entities@[j] as nat == e_nat;
            // entities@[j] as nat == e_nat != target as nat, so entities@[j] != target
            assert(entities@[j] != target);
            assert(!circle_flags@[entities@[j] as int]);
            assert((entities@[j] as int) < n_points);
            // entities@[j] as int == e_nat as int since both < n_points
        }
    }
    true
}

/// Check all constraints are independent for a given step target.
fn check_all_constraints_for_target(
    constraints: &Vec<RuntimeConstraint>,
    target: usize,
    circle_flags: &Vec<bool>,
    n_points: usize,
) -> (out: bool)
    requires
        circle_flags@.len() == n_points as int,
        (target as int) < n_points,
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
    ensures
        out ==> forall|ci: int| #![trigger constraints@[ci]]
            0 <= ci < constraints@.len()
            && constraint_entities(runtime_constraint_model(constraints@[ci])).contains(target as nat)
            ==> forall|e: EntityId|
                constraint_entities(runtime_constraint_model(constraints@[ci])).contains(e) && e != (target as nat)
                ==> (e as int) < n_points && !circle_flags@[e as int],
{
    let mut ci: usize = 0;
    while ci < constraints.len()
        invariant
            ci <= constraints@.len(),
            circle_flags@.len() == n_points as int,
            (target as int) < n_points,
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
            forall|ci_idx: int| #![trigger constraints@[ci_idx]]
                0 <= ci_idx < ci
                && constraint_entities(runtime_constraint_model(constraints@[ci_idx])).contains(target as nat)
                ==> forall|e: EntityId|
                    constraint_entities(runtime_constraint_model(constraints@[ci_idx])).contains(e) && e != (target as nat)
                    ==> (e as int) < n_points && !circle_flags@[e as int],
        decreases constraints@.len() - ci,
    {
        let ok = check_one_constraint_independent(&constraints[ci], target, circle_flags, n_points);
        if !ok { return false; }
        ci = ci + 1;
    }
    true
}

/// Check that a plan is fully independent: for every step's target, every
/// constraint referencing that target has no OTHER entities that are circle targets.
fn check_is_fully_independent_exec(
    plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    n_points: usize,
) -> (out: bool)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < plan@.len() ==>
            (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
    ensures
        out ==> is_fully_independent_plan(plan_to_spec(plan@), constraints_to_spec(constraints@)),
{
    let ghost plan_spec = plan_to_spec(plan@);
    let ghost cstr_spec = constraints_to_spec(constraints@);

    let circle_flags = build_circle_flags(plan, n_points);

    let mut si: usize = 0;
    while si < plan.len()
        invariant
            si <= plan@.len(),
            circle_flags@.len() == n_points as int,
            plan_spec == plan_to_spec(plan@),
            cstr_spec == constraints_to_spec(constraints@),
            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
            forall|i: int| 0 <= i < plan@.len() ==>
                (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
            forall|e: int| 0 <= e < n_points ==>
                (circle_flags@[e] == circle_targets(plan_spec).contains(e as nat)),
            // Independence holds for all si' < si
            forall|si_idx: int| #![trigger plan_spec[si_idx]]
                0 <= si_idx < si ==>
                forall|ci_idx: int| #![trigger cstr_spec[ci_idx]]
                    0 <= ci_idx < cstr_spec.len()
                    && constraint_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_idx]))
                    ==> forall|e: EntityId|
                        constraint_entities(cstr_spec[ci_idx]).contains(e) && e != step_target(plan_spec[si_idx])
                        ==> !circle_targets(plan_spec).contains(e),
        decreases plan@.len() - si,
    {
        let target = plan[si].target_id();
        let ok = check_all_constraints_for_target(constraints, target, &circle_flags, n_points);
        if !ok { return false; }
        // Extend invariant: check_all_constraints_for_target ensures independence
        // for all ci w.r.t. target in terms of circle_flags.
        // Convert to circle_targets via flag correspondence.
        proof {
            let target_nat: nat = target as nat;
            assert(target_nat == step_target(plan_spec[si as int]));
            assert forall|ci_idx: int, e: EntityId|
                0 <= ci_idx < cstr_spec.len()
                && constraint_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si as int]))
                && constraint_entities(cstr_spec[ci_idx]).contains(e)
                && e != step_target(plan_spec[si as int])
            implies !circle_targets(plan_spec).contains(e)
            by {
                // Unfold: cstr_spec[ci_idx] == runtime_constraint_model(constraints@[ci_idx])
                assert(cstr_spec[ci_idx] == runtime_constraint_model(constraints@[ci_idx]));
                // Trigger the ensures of check_all_constraints_for_target:
                // constraint_entities(runtime_constraint_model(constraints@[ci_idx])).contains(target as nat)
                // → for all e' != target_nat: (e' as int) < n_points && !circle_flags@[e' as int]
                assert(constraint_entities(runtime_constraint_model(constraints@[ci_idx]))
                    .contains(target_nat));
                assert(constraint_entities(runtime_constraint_model(constraints@[ci_idx]))
                    .contains(e));
                assert(e != target_nat);
                // From check_all_constraints_for_target ensures:
                assert((e as int) < n_points);
                assert(!circle_flags@[e as int]);
                // From flag correspondence:
                assert(!circle_targets(plan_spec).contains(e));
            }
        }
        si = si + 1;
    }
    true
}

// --- 1b: check_constraint_well_formed_exec ---

/// Check that all constraints are well-formed (distinct entity IDs where required).
fn check_constraint_well_formed_exec(
    constraints: &Vec<RuntimeConstraint>,
    n_points: usize,
) -> (out: bool)
    requires
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
    ensures
        out ==> forall|ci: int| 0 <= ci < constraints@.len() ==>
            constraint_well_formed(
                runtime_constraint_model(#[trigger] constraints@[ci])),
{
    let mut i: usize = 0;
    while i < constraints.len()
        invariant
            i <= constraints@.len(),
            forall|j: int| 0 <= j < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[j], n_points as nat),
            forall|ci: int| 0 <= ci < i ==>
                constraint_well_formed(
                    runtime_constraint_model(#[trigger] constraints@[ci])),
        decreases constraints@.len() - i,
    {
        let ok = match &constraints[i] {
            RuntimeConstraint::Coincident { a, b, .. } => *a != *b,
            RuntimeConstraint::DistanceSq { a, b, .. } => *a != *b,
            RuntimeConstraint::FixedX { .. } => true,
            RuntimeConstraint::FixedY { .. } => true,
            RuntimeConstraint::SameX { a, b, .. } => *a != *b,
            RuntimeConstraint::SameY { a, b, .. } => *a != *b,
            RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } =>
                *point != *line_a && *point != *line_b && *line_a != *line_b,
            RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } =>
                *a1 != *a2 && *a1 != *b1 && *a1 != *b2 && *a2 != *b1 && *a2 != *b2,
            RuntimeConstraint::Midpoint { mid, a, b, .. } =>
                *mid != *a && *mid != *b && *a != *b,
            RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } =>
                *a1 != *a2 && *b1 != *b2 && *a1 != *b1 && *a1 != *b2 && *a2 != *b1 && *a2 != *b2,
            RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } =>
                *a1 != *a2 && *b1 != *b2 && *a1 != *b1 && *a1 != *b2 && *a2 != *b1 && *a2 != *b2,
            RuntimeConstraint::Collinear { a, b, c, .. } =>
                *a != *b && *a != *c && *b != *c,
            RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } =>
                *point != *center && *point != *radius_point && *center != *radius_point,
            RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } =>
                *point != *original && *point != *axis_a && *point != *axis_b
                && *original != *axis_a && *original != *axis_b && *axis_a != *axis_b,
            RuntimeConstraint::FixedPoint { .. } => true,
            RuntimeConstraint::Ratio { a1, a2, b1, b2, .. } =>
                *a1 != *a2 && *a1 != *b1 && *a1 != *b2 && *a2 != *b1 && *a2 != *b2,
            RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, .. } =>
                *line_a != *line_b && *line_a != *center && *line_a != *radius_point
                && *line_b != *center && *line_b != *radius_point && *center != *radius_point,
            RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, .. } =>
                *c1 != *rp1 && *c2 != *rp2 && *c1 != *c2,
            RuntimeConstraint::Angle { a1, a2, b1, b2, .. } =>
                *a1 != *a2 && *b1 != *b2 && *a1 != *b1 && *a1 != *b2 && *a2 != *b1 && *a2 != *b2,
        };
        if !ok {
            return false;
        }
        i = i + 1;
    }
    true
}

// --- 1c: check_step_radicand_matches_exec ---

/// Check that all circle steps' discriminants equal R::value().
fn check_step_radicand_matches_exec<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    plan: &Vec<RuntimeStepData>,
) -> (out: bool)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < plan@.len() ==>
            step_has_positive_discriminant((#[trigger] plan@[i]).spec_step()),
    ensures
        out ==> forall|j: int| 0 <= j < plan@.len() ==>
            step_radicand_matches::<R>((#[trigger] plan@[j]).spec_step()),
{
    let mut i: usize = 0;
    while i < plan.len()
        invariant
            i <= plan@.len(),
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            forall|j: int| 0 <= j < plan@.len() ==>
                step_has_positive_discriminant((#[trigger] plan@[j]).spec_step()),
            forall|j: int| 0 <= j < i ==>
                step_radicand_matches::<R>((#[trigger] plan@[j]).spec_step()),
        decreases plan@.len() - i,
    {
        match &plan[i] {
            RuntimeStepData::CircleLine { circle, line, .. } => {
                let disc = cl_discriminant_exec(circle, line);
                let rad_val = RR::exec_value();
                if !disc.eq(&rad_val) {
                    return false;
                }
            }
            RuntimeStepData::CircleCircle { c1, c2, .. } => {
                let disc = cc_discriminant_exec(c1, c2);
                let rad_val = RR::exec_value();
                if !disc.eq(&rad_val) {
                    return false;
                }
            }
            _ => {
                // Rational steps: radicand matches trivially
            }
        }
        i = i + 1;
    }
    true
}

// --- 1d: check_constraint_locus_nondegenerate_exec ---

/// Check Symmetric constraint axis non-degeneracy.
/// For non-Symmetric constraints, always non-degenerate.
fn check_constraint_locus_nondegenerate_exec(
    constraints: &Vec<RuntimeConstraint>,
    points: &Vec<RuntimePoint2>,
    n_points: usize,
) -> (out: bool)
    requires
        n_points == points@.len(),
        all_points_wf(points@),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
{
    let mut ci: usize = 0;
    while ci < constraints.len()
        invariant
            ci <= constraints@.len(),
            n_points == points@.len(),
            all_points_wf(points@),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
        decreases constraints@.len() - ci,
    {
        match &constraints[ci] {
            RuntimeConstraint::Symmetric { axis_a, axis_b, .. } => {
                let d = sq_dist_2d_exec(&points[*axis_a], &points[*axis_b]);
                let zero = RuntimeRational::from_int(0);
                if d.eq(&zero) {
                    return false;
                }
            }
            _ => {}
        }
        ci = ci + 1;
    }
    true
}

// --- 1b_helper: is_locus_entity_exec ---

/// Check if target is in constraint_locus_entities for a given constraint.
fn is_locus_entity_exec(rc: &RuntimeConstraint, target: usize, n_points: usize) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, n_points as nat),
        (target as int) < n_points,
    ensures
        out == constraint_locus_entities(
            runtime_constraint_model(*rc)).contains(target as nat),
{
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::DistanceSq { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::FixedX { point, .. } => *point == target,
        RuntimeConstraint::FixedY { point, .. } => *point == target,
        RuntimeConstraint::SameX { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::SameY { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::PointOnLine { point, .. } => *point == target,
        RuntimeConstraint::EqualLengthSq { a1, a2, .. } => *a1 == target || *a2 == target,
        RuntimeConstraint::Midpoint { mid, a, b, .. } =>
            *mid == target || *a == target || *b == target,
        RuntimeConstraint::Perpendicular { a1, a2, .. } => *a1 == target || *a2 == target,
        RuntimeConstraint::Parallel { a1, a2, .. } => *a1 == target || *a2 == target,
        RuntimeConstraint::Collinear { a, b, c, .. } =>
            *a == target || *b == target || *c == target,
        RuntimeConstraint::PointOnCircle { point, .. } => *point == target,
        RuntimeConstraint::Symmetric { point, .. } => *point == target,
        RuntimeConstraint::FixedPoint { point, .. } => *point == target,
        RuntimeConstraint::Ratio { a1, a2, .. } => *a1 == target || *a2 == target,
        RuntimeConstraint::Tangent { .. } => false,
        RuntimeConstraint::CircleTangent { .. } => false,
        RuntimeConstraint::Angle { .. } => false,
    }
}

// --- 1b_helper: is_entity_of_constraint_exec ---

/// Check if target is in constraint_entities for a given constraint.
fn is_entity_of_constraint_exec(rc: &RuntimeConstraint, target: usize, n_points: usize) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, n_points as nat),
        (target as int) < n_points,
    ensures
        out == constraint_entities(
            runtime_constraint_model(*rc)).contains(target as nat),
{
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::DistanceSq { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::FixedX { point, .. } => *point == target,
        RuntimeConstraint::FixedY { point, .. } => *point == target,
        RuntimeConstraint::SameX { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::SameY { a, b, .. } => *a == target || *b == target,
        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } =>
            *point == target || *line_a == target || *line_b == target,
        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } =>
            *a1 == target || *a2 == target || *b1 == target || *b2 == target,
        RuntimeConstraint::Midpoint { mid, a, b, .. } =>
            *mid == target || *a == target || *b == target,
        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } =>
            *a1 == target || *a2 == target || *b1 == target || *b2 == target,
        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } =>
            *a1 == target || *a2 == target || *b1 == target || *b2 == target,
        RuntimeConstraint::Collinear { a, b, c, .. } =>
            *a == target || *b == target || *c == target,
        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } =>
            *point == target || *center == target || *radius_point == target,
        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } =>
            *point == target || *original == target || *axis_a == target || *axis_b == target,
        RuntimeConstraint::FixedPoint { point, .. } => *point == target,
        RuntimeConstraint::Ratio { a1, a2, b1, b2, .. } =>
            *a1 == target || *a2 == target || *b1 == target || *b2 == target,
        RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, .. } =>
            *line_a == target || *line_b == target || *center == target || *radius_point == target,
        RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, .. } =>
            *c1 == target || *rp1 == target || *c2 == target || *rp2 == target,
        RuntimeConstraint::Angle { a1, a2, b1, b2, .. } =>
            *a1 == target || *a2 == target || *b1 == target || *b2 == target,
    }
}

// --- 1b: check_plan_locus_ordered_exec ---

/// Check that the plan is locus-ordered for all constraints.
/// For every (ci, si) where step target is in constraint_entities but NOT in
/// constraint_locus_entities: either it's a verification constraint, or there
/// exists a later step whose target IS in constraint_locus_entities.
pub fn check_plan_locus_ordered_exec(
    plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    n_points: usize,
) -> (out: bool)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < plan@.len() ==>
            (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
    ensures
        out ==> plan_locus_ordered(plan_to_spec(plan@), constraints_to_spec(constraints@)),
{
    let ghost plan_spec = plan_to_spec(plan@);
    let ghost cstr_spec = constraints_to_spec(constraints@);

    let mut si: usize = 0;
    while si < plan.len()
        invariant
            si <= plan@.len(),
            plan_spec == plan_to_spec(plan@),
            cstr_spec == constraints_to_spec(constraints@),
            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
            forall|i: int| 0 <= i < plan@.len() ==>
                (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
            // Spec: locus-ordered property holds for all si' < si
            forall|ci_idx: int, si_idx: int|
                #![trigger plan_spec[si_idx], cstr_spec[ci_idx]]
                0 <= ci_idx < cstr_spec.len() && 0 <= si_idx < si &&
                constraint_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_idx])) &&
                !constraint_locus_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_idx]))
                ==> (
                    is_verification_constraint(cstr_spec[ci_idx])
                    || exists|si_loc: int|
                        si_idx < si_loc < plan_spec.len() &&
                        constraint_locus_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_loc]))
                ),
        decreases plan@.len() - si,
    {
        let target = plan[si].target_id();
        let mut ci: usize = 0;
        while ci < constraints.len()
            invariant
                ci <= constraints@.len(),
                (target as int) < n_points,
                target as nat == step_target(plan_spec[si as int]),
                plan_spec == plan_to_spec(plan@),
                cstr_spec == constraints_to_spec(constraints@),
                forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
                forall|i: int| 0 <= i < plan@.len() ==>
                    (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
                forall|i: int| 0 <= i < constraints@.len() ==>
                    runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
                si < plan@.len(),
                // Spec: for all si' < si, all ci': property holds (from outer)
                forall|ci_idx: int, si_idx: int|
                    #![trigger plan_spec[si_idx], cstr_spec[ci_idx]]
                    0 <= ci_idx < cstr_spec.len() && 0 <= si_idx < si &&
                    constraint_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_idx])) &&
                    !constraint_locus_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_idx]))
                    ==> (
                        is_verification_constraint(cstr_spec[ci_idx])
                        || exists|si_loc: int|
                            si_idx < si_loc < plan_spec.len() &&
                            constraint_locus_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_loc]))
                    ),
                // Spec: for si and all ci' < ci: property holds
                forall|ci_idx: int|
                    #![trigger cstr_spec[ci_idx]]
                    0 <= ci_idx < ci &&
                    constraint_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si as int])) &&
                    !constraint_locus_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si as int]))
                    ==> (
                        is_verification_constraint(cstr_spec[ci_idx])
                        || exists|si_loc: int|
                            (si as int) < si_loc < plan_spec.len() &&
                            constraint_locus_entities(cstr_spec[ci_idx]).contains(step_target(plan_spec[si_loc]))
                    ),
            decreases constraints@.len() - ci,
        {
            let in_entities = is_entity_of_constraint_exec(&constraints[ci], target, n_points);
            let in_locus = is_locus_entity_exec(&constraints[ci], target, n_points);

            if in_entities && !in_locus {
                let is_verif = is_verification_constraint_exec(&constraints[ci], n_points);
                if !is_verif {
                    // Search forward for a later step with target in locus_entities
                    let mut found_later = false;
                    let ghost mut witness: int = 0;
                    assert(si < plan.len()); // ensures si + 1 fits in usize
                    let mut si_loc: usize = si + 1;
                    while si_loc < plan.len()
                        invariant
                            si < plan@.len(),
                            si + 1 <= si_loc <= plan@.len(),
                            plan_spec == plan_to_spec(plan@),
                            cstr_spec == constraints_to_spec(constraints@),
                            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
                            forall|i: int| 0 <= i < plan@.len() ==>
                                (step_target((#[trigger] plan@[i]).spec_step()) as int) < n_points,
                            forall|i: int| 0 <= i < constraints@.len() ==>
                                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
                            ci < constraints@.len(),
                            // found_later: explicit witness tracked
                            found_later ==> (
                                (si as int) < witness < (si_loc as int) &&
                                constraint_locus_entities(cstr_spec[ci as int]).contains(
                                    step_target(plan_spec[witness]))),
                        decreases plan@.len() - si_loc,
                    {
                        let loc_target = plan[si_loc].target_id();
                        if is_locus_entity_exec(&constraints[ci], loc_target, n_points) {
                            found_later = true;
                            proof { witness = si_loc as int; }
                        }
                        si_loc = si_loc + 1;
                    }
                    if !found_later {
                        return false;
                    }
                }
            }
            ci = ci + 1;
        }
        si = si + 1;
    }
    true
}

// --- 1e_helper: point_satisfies_locus_exec ---

/// Check if a point satisfies a locus at runtime.
fn point_satisfies_locus_exec(
    locus: &RuntimeLocus,
    p: &RuntimePoint2,
) -> (out: bool)
    requires
        locus.wf_spec(),
        p.wf_spec(),
    ensures
        out ==> point_satisfies_locus(locus.spec_locus(), p@),
{
    match locus {
        RuntimeLocus::FullPlane => true,
        RuntimeLocus::OnLine { line } => {
            let val = line2_eval_exec(line, p);
            let zero = RuntimeRational::from_int(0);
            val.eq(&zero)
        }
        RuntimeLocus::OnCircle { circle } => {
            let d = sq_dist_2d_exec(p, &circle.center);
            d.eq(&circle.radius_sq)
        }
        RuntimeLocus::AtPoint { point } => {
            point.x.eq(&p.x) && point.y.eq(&p.y)
        }
    }
}

// --- 1e: check_step_satisfaction_replay_exec ---

/// Replay the plan and check:
/// - For rational steps: all constraint loci are satisfied by the executed point
/// - For circle steps: all nontrivial loci match the step's built-in circle/line
///   (checked via field-wise eqv comparison of the RuntimeLocus with step geometry)
/// - At each step: Symmetric constraint axis non-degeneracy
///
/// Takes the solver's plan + constraints + a COPY of the initial points/flags
/// (state before the solver ran). The function replays by executing rational steps
/// and updating the running state, mirroring what greedy_solve_exec does.
fn check_step_satisfaction_replay_exec(
    plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: bool)
    requires
        old(points)@.len() == old(resolved_flags)@.len(),
        all_points_wf(old(points)@),
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < plan@.len() ==>
            (step_target((#[trigger] plan@[i]).spec_step()) as int) < old(points)@.len(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], old(points)@.len() as nat),
        forall|i: int| 0 <= i < old(resolved_flags)@.len() ==>
            (#[trigger] old(resolved_flags)@[i]) ==
            partial_resolved_map(points_view(old(points)@), old(resolved_flags)@)
                .dom().contains(i as nat),
        // Each step geometrically valid (from solver ensures)
        forall|i: int| 0 <= i < plan@.len() ==>
            step_geometrically_valid((#[trigger] plan@[i]).spec_step()),
    ensures
        points@.len() == old(points)@.len(),
        resolved_flags@.len() == old(resolved_flags)@.len(),
{
    let n_points = points.len();
    let mut si: usize = 0;

    while si < plan.len()
        invariant
            si <= plan@.len(),
            points@.len() == old(points)@.len(),
            resolved_flags@.len() == old(resolved_flags)@.len(),
            resolved_flags@.len() == points@.len(),
            n_points == points@.len(),
            all_points_wf(points@),
            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
            forall|i: int| 0 <= i < plan@.len() ==>
                (step_target((#[trigger] plan@[i]).spec_step()) as int) < points@.len(),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
            forall|i: int| 0 <= i < resolved_flags@.len() ==>
                (#[trigger] resolved_flags@[i]) ==
                partial_resolved_map(points_view(points@), resolved_flags@)
                    .dom().contains(i as nat),
            forall|i: int| 0 <= i < plan@.len() ==>
                step_geometrically_valid((#[trigger] plan@[i]).spec_step()),
        decreases plan@.len() - si,
    {
        let target = plan[si].target_id();

        // Check at most two nontrivial loci for this target
        if !check_at_most_two_nontrivial_exec(target, constraints, resolved_flags, n_points) {
            return false;
        }

        // Compute all loci for this step's target
        let loci = collect_loci_exec(constraints, points, resolved_flags, target);

        match &plan[si] {
            RuntimeStepData::PointStep { target: _, x, y, .. } => {
                // Execute: point is (x, y)
                let pt = RuntimePoint2::new(copy_rational(x), copy_rational(y));
                // Check all loci satisfied
                let mut ci: usize = 0;
                while ci < loci.len()
                    invariant
                        ci <= loci@.len(),
                        loci@.len() == constraints@.len(),
                        pt.wf_spec(),
                        forall|j: int| 0 <= j < loci@.len() ==> (#[trigger] loci@[j]).wf_spec(),
                        // Length preservation for early returns
                        points@.len() == old(points)@.len(),
                        resolved_flags@.len() == old(resolved_flags)@.len(),
                    decreases loci@.len() - ci,
                {
                    if !point_satisfies_locus_exec(&loci[ci], &pt) {
                        return false;
                    }
                    ci = ci + 1;
                }
                // Update running state
                let mut swap_pt = pt;
                points.set_and_swap(target, &mut swap_pt);
            }
            RuntimeStepData::LineLine { target: _, l1, l2, .. } => {
                // Execute the intersection
                let pt = execute_line_line_step(l1, l2);
                // Check all loci satisfied
                let mut ci: usize = 0;
                while ci < loci.len()
                    invariant
                        ci <= loci@.len(),
                        loci@.len() == constraints@.len(),
                        pt.wf_spec(),
                        forall|j: int| 0 <= j < loci@.len() ==> (#[trigger] loci@[j]).wf_spec(),
                        points@.len() == old(points)@.len(),
                        resolved_flags@.len() == old(resolved_flags)@.len(),
                    decreases loci@.len() - ci,
                {
                    if !point_satisfies_locus_exec(&loci[ci], &pt) {
                        return false;
                    }
                    ci = ci + 1;
                }
                // Update running state
                let mut swap_pt = pt;
                points.set_and_swap(target, &mut swap_pt);
            }
            RuntimeStepData::CircleLine { target: _, circle, line, .. } => {
                // Check nontrivial loci match step geometry
                let mut ci: usize = 0;
                while ci < loci.len()
                    invariant
                        ci <= loci@.len(),
                        loci@.len() == constraints@.len(),
                        circle.wf_spec(),
                        line.wf_spec(),
                        forall|j: int| 0 <= j < loci@.len() ==> (#[trigger] loci@[j]).wf_spec(),
                        points@.len() == old(points)@.len(),
                        resolved_flags@.len() == old(resolved_flags)@.len(),
                    decreases loci@.len() - ci,
                {
                    match &loci[ci] {
                        RuntimeLocus::FullPlane => { /* trivial, ok */ }
                        RuntimeLocus::OnCircle { circle: locus_circle } => {
                            if !locus_circle.center.x.eq(&circle.center.x)
                                || !locus_circle.center.y.eq(&circle.center.y)
                                || !locus_circle.radius_sq.eq(&circle.radius_sq) {
                                return false;
                            }
                        }
                        RuntimeLocus::OnLine { line: locus_line } => {
                            if !locus_line.a.eq(&line.a)
                                || !locus_line.b.eq(&line.b)
                                || !locus_line.c.eq(&line.c) {
                                return false;
                            }
                        }
                        RuntimeLocus::AtPoint { .. } => {
                            return false;
                        }
                    }
                    ci = ci + 1;
                }
            }
            RuntimeStepData::CircleCircle { target: _, c1, c2, .. } => {
                // Check nontrivial loci match step geometry
                let mut ci: usize = 0;
                while ci < loci.len()
                    invariant
                        ci <= loci@.len(),
                        loci@.len() == constraints@.len(),
                        c1.wf_spec(),
                        c2.wf_spec(),
                        forall|j: int| 0 <= j < loci@.len() ==> (#[trigger] loci@[j]).wf_spec(),
                        points@.len() == old(points)@.len(),
                        resolved_flags@.len() == old(resolved_flags)@.len(),
                    decreases loci@.len() - ci,
                {
                    match &loci[ci] {
                        RuntimeLocus::FullPlane => { /* trivial, ok */ }
                        RuntimeLocus::OnCircle { circle: locus_circle } => {
                            let match_c1 =
                                locus_circle.center.x.eq(&c1.center.x)
                                && locus_circle.center.y.eq(&c1.center.y)
                                && locus_circle.radius_sq.eq(&c1.radius_sq);
                            let match_c2 =
                                locus_circle.center.x.eq(&c2.center.x)
                                && locus_circle.center.y.eq(&c2.center.y)
                                && locus_circle.radius_sq.eq(&c2.radius_sq);
                            if !match_c1 && !match_c2 {
                                return false;
                            }
                        }
                        _ => {
                            return false;
                        }
                    }
                    ci = ci + 1;
                }
            }
        }

        // Check Symmetric constraint nondegeneracy at this step
        let mut ci2: usize = 0;
        while ci2 < constraints.len()
            invariant
                ci2 <= constraints@.len(),
                n_points == points@.len(),
                resolved_flags@.len() == n_points,
                all_points_wf(points@),
                forall|i: int| 0 <= i < constraints@.len() ==>
                    runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
                points@.len() == old(points)@.len(),
                resolved_flags@.len() == old(resolved_flags)@.len(),
            decreases constraints@.len() - ci2,
        {
            match &constraints[ci2] {
                RuntimeConstraint::Symmetric { point, axis_a, axis_b, .. } => {
                    if *point == target {
                        if resolved_flags[*axis_a] && resolved_flags[*axis_b] {
                            let d = sq_dist_2d_exec(&points[*axis_a], &points[*axis_b]);
                            let zero = RuntimeRational::from_int(0);
                            if d.eq(&zero) {
                                return false;
                            }
                        }
                    }
                }
                _ => {}
            }
            ci2 = ci2 + 1;
        }

        // Mark target as resolved (mirroring solver behavior)
        let mut flag = true;
        resolved_flags.set_and_swap(target, &mut flag);

        proof {
            assert forall|i: int| 0 <= i < resolved_flags@.len() implies
                (#[trigger] resolved_flags@[i]) ==
                partial_resolved_map(points_view(points@), resolved_flags@)
                    .dom().contains(i as nat)
            by { }
        }

        si = si + 1;
    }
    true
}

// --- 1f: verify_plan_soundness_exec ---

/// Assembly: check all plan_structurally_sound conjuncts not already ensured
/// by solve_all_variants. Returns true if all checks pass.
///
/// Preconditions come from solve_all_variants ensures (wf_spec, distinct targets,
/// geometric validity, positive discriminant, valid entity IDs).
///
/// This performs runtime checks for:
/// - constraint_well_formed (all constraints)
/// - is_fully_independent_plan
/// - step_radicand_matches (circle discriminants match R::value())
/// - plan_locus_ordered
/// - step satisfaction replay (rational step loci + circle step geometry match + nondegeneracy)
pub fn verify_plan_soundness_exec<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: bool)
    requires
        old(points)@.len() == old(resolved_flags)@.len(),
        all_points_wf(old(points)@),
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int, j: int|
            0 <= i < plan@.len() && 0 <= j < plan@.len() && i != j ==>
            step_target(#[trigger] plan@[i].spec_step()) != step_target(#[trigger] plan@[j].spec_step()),
        forall|i: int| 0 <= i < plan@.len() ==>
            (step_target((#[trigger] plan@[i]).spec_step()) as int) < old(points)@.len(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], old(points)@.len() as nat),
        forall|i: int| 0 <= i < old(resolved_flags)@.len() ==>
            (#[trigger] old(resolved_flags)@[i]) ==
            partial_resolved_map(points_view(old(points)@), old(resolved_flags)@)
                .dom().contains(i as nat),
        forall|i: int| 0 <= i < plan@.len() ==>
            step_has_positive_discriminant((#[trigger] plan@[i]).spec_step()),
        forall|i: int| 0 <= i < plan@.len() ==>
            step_geometrically_valid((#[trigger] plan@[i]).spec_step()),
    ensures
        points@.len() == old(points)@.len(),
        resolved_flags@.len() == old(resolved_flags)@.len(),
        out ==> forall|j: int| 0 <= j < plan@.len() ==>
            step_radicand_matches::<R>((#[trigger] plan@[j]).spec_step()),
        out ==> forall|ci: int| 0 <= ci < constraints@.len() ==>
            constraint_well_formed(
                runtime_constraint_model(#[trigger] constraints@[ci])),
        out ==> is_fully_independent_plan(
            plan_to_spec(plan@), constraints_to_spec(constraints@)),
        out ==> plan_locus_ordered(
            plan_to_spec(plan@), constraints_to_spec(constraints@)),
{
    let n_points = points.len();

    // 1b: constraint well-formedness
    let cwf = check_constraint_well_formed_exec(constraints, n_points);
    if !cwf {
        return false;
    }

    // 1a: independence
    let indep = check_is_fully_independent_exec(plan, constraints, n_points);
    if !indep {
        return false;
    }

    // 1c: radicand matching
    let radicand_ok = check_step_radicand_matches_exec::<R, RR>(plan);
    if !radicand_ok {
        return false;
    }

    // 1d: locus ordering
    let locus_ord = check_plan_locus_ordered_exec(plan, constraints, n_points);
    if !locus_ord {
        return false;
    }

    // 1e + 1f: step satisfaction replay (includes nondegeneracy checks)
    if !check_step_satisfaction_replay_exec(plan, constraints, points, resolved_flags) {
        return false;
    }

    true
}

} // verus!
