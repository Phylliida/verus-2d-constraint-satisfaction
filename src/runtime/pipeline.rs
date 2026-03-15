use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::runtime::point2::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use verus_quadratic_extension::radicand::PositiveRadicand;
use verus_quadratic_extension::runtime::RuntimeRadicand;
use verus_quadratic_extension::instances::{Sqrt2, Sqrt3, Sqrt5};
use verus_quadratic_extension::runtime::{RuntimeSqrt2, RuntimeSqrt3, RuntimeSqrt5};
use verus_geometry::runtime::circle_line::cl_discriminant_exec;
use verus_geometry::runtime::circle_circle::cc_discriminant_exec;
use crate::entities::*;
use crate::constraints::*;
use crate::construction::*;
use crate::construction_ext::*;
use crate::runtime::constraint::*;
use crate::runtime::construction::*;
use crate::runtime::solver::*;
use crate::runtime::ext_constraint::*;

type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Spec: Full plan construction
// ===========================================================================

/// Count the number of initially-resolved entities (flags[i] == true).
pub open spec fn count_initial(flags: Seq<bool>) -> nat
    decreases flags.len(),
{
    if flags.len() == 0 {
        0
    } else {
        let rest = count_initial(flags.drop_last());
        if flags.last() { rest + 1 } else { rest }
    }
}

/// Build PointSteps for initially-resolved entities, in order 0..n-1.
/// Only entities with flags[i] == true get a step.
pub open spec fn initial_point_steps(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
) -> ConstructionPlan<RationalModel>
    recommends points.len() == flags.len(),
    decreases points.len(),
{
    if points.len() == 0 {
        Seq::empty()
    } else {
        let n = (points.len() - 1) as int;
        let prefix = initial_point_steps(points.take(n), flags.take(n));
        if flags[n] {
            prefix.push(ConstructionStep::PointStep {
                id: n as nat,
                position: points[n],
            })
        } else {
            prefix
        }
    }
}

/// Build the full plan: initial PointSteps for resolved entities,
/// followed by solver steps.
pub open spec fn build_full_plan(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
    solver_plan: ConstructionPlan<RationalModel>,
) -> ConstructionPlan<RationalModel> {
    initial_point_steps(points, flags) + solver_plan
}

// ===========================================================================
//  Spec: Properties of initial_point_steps
// ===========================================================================

/// All targets of initial_point_steps are distinct.
proof fn lemma_initial_steps_distinct_targets(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
)
    requires points.len() == flags.len(),
    ensures
        forall|i: int, j: int|
            0 <= i < initial_point_steps(points, flags).len()
            && 0 <= j < initial_point_steps(points, flags).len()
            && i != j ==>
            step_target(initial_point_steps(points, flags)[i])
                != step_target(initial_point_steps(points, flags)[j]),
    decreases points.len(),
{
    if points.len() > 0 {
        let n = (points.len() - 1) as int;
        let prefix = initial_point_steps(points.take(n), flags.take(n));
        let full = initial_point_steps(points, flags);
        lemma_initial_steps_distinct_targets(points.take(n), flags.take(n));
        lemma_initial_steps_targets_bounded(points.take(n), flags.take(n));
        if flags[n] {
            assert forall|i: int, j: int|
                0 <= i < full.len()
                && 0 <= j < full.len()
                && i != j
            implies
                step_target(#[trigger] full[i])
                    != step_target(#[trigger] full[j])
            by {
                if i < prefix.len() as int && j < prefix.len() as int {
                    // Both in prefix: use IH
                    assert(full[i] == prefix[i]);
                    assert(full[j] == prefix[j]);
                    assert(step_target(prefix[i]) != step_target(prefix[j]));
                } else if i < prefix.len() as int {
                    // i in prefix, j is the new step targeting n
                    assert(full[i] == prefix[i]);
                    assert((step_target(prefix[i]) as int) < points.take(n).len());
                    assert(full[j] == (ConstructionStep::PointStep {
                        id: n as nat, position: points[n],
                    }));
                } else if j < prefix.len() as int {
                    // j in prefix, i is the new step targeting n
                    assert(full[j] == prefix[j]);
                    assert((step_target(prefix[j]) as int) < points.take(n).len());
                    assert(full[i] == (ConstructionStep::PointStep {
                        id: n as nat, position: points[n],
                    }));
                }
                // else both are the new step, but i != j and there's only one
            }
        }
    }
}

/// All targets of initial_point_steps are < points.len().
proof fn lemma_initial_steps_targets_bounded(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
)
    requires points.len() == flags.len(),
    ensures
        forall|i: int|
            0 <= i < initial_point_steps(points, flags).len() ==>
            (step_target(#[trigger] initial_point_steps(points, flags)[i]) as int)
                < points.len(),
    decreases points.len(),
{
    if points.len() > 0 {
        let n = (points.len() - 1) as int;
        let prefix = initial_point_steps(points.take(n), flags.take(n));
        let full = initial_point_steps(points, flags);
        lemma_initial_steps_targets_bounded(points.take(n), flags.take(n));
        if flags[n] {
            // full == prefix.push(PointStep { id: n, ... })
            assert forall|i: int|
                0 <= i < full.len()
            implies
                (step_target(#[trigger] full[i]) as int) < points.len()
            by {
                if i < prefix.len() as int {
                    assert(full[i] == prefix[i]);
                    assert((step_target(prefix[i]) as int) < points.take(n).len());
                } else {
                    // i == prefix.len(), the new step targets n
                    assert(full[i] == (ConstructionStep::PointStep {
                        id: n as nat, position: points[n],
                    }));
                }
            }
        }
    }
}

/// All initial_point_steps are rational (PointStep).
proof fn lemma_initial_steps_are_rational(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
)
    requires points.len() == flags.len(),
    ensures
        forall|i: int|
            0 <= i < initial_point_steps(points, flags).len() ==>
            is_rational_step(#[trigger] initial_point_steps(points, flags)[i]),
    decreases points.len(),
{
    if points.len() > 0 {
        let n = (points.len() - 1) as int;
        let prefix = initial_point_steps(points.take(n), flags.take(n));
        let full = initial_point_steps(points, flags);
        lemma_initial_steps_are_rational(points.take(n), flags.take(n));
        if flags[n] {
            assert forall|i: int|
                0 <= i < full.len()
            implies
                is_rational_step(#[trigger] full[i])
            by {
                if i < prefix.len() as int {
                    assert(full[i] == prefix[i]);
                } else {
                    assert(full[i] == (ConstructionStep::PointStep {
                        id: n as nat, position: points[n],
                    }));
                }
            }
        }
    }
}

/// circle_targets of the full plan equals circle_targets of the solver plan
/// (since initial steps are all rational).
proof fn lemma_full_plan_circle_targets(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
    solver_plan: ConstructionPlan<RationalModel>,
)
    requires points.len() == flags.len(),
    ensures
        circle_targets(build_full_plan(points, flags, solver_plan))
            =~= circle_targets(solver_plan),
{
    let init = initial_point_steps(points, flags);
    let full = build_full_plan(points, flags, solver_plan);
    lemma_initial_steps_are_rational(points, flags);

    // Prove set equality by showing both containments
    assert forall|id: EntityId|
        circle_targets(full).contains(id) <==>
        circle_targets(solver_plan).contains(id)
    by {
        // Forward: if id ∈ circle_targets(full), exists k with !is_rational(full[k]) && target == id
        if circle_targets(full).contains(id) {
            let k = choose|k: int| 0 <= k < full.len()
                && !is_rational_step(#[trigger] full[k])
                && step_target(full[k]) == id;
            // k must be >= init.len() because all init steps are rational
            if k < init.len() as int {
                assert(is_rational_step(init[k]));
                assert(full[k] == init[k]);
                assert(false);
            }
            // So k >= init.len(), meaning full[k] == solver_plan[k - init.len()]
            assert((full == init + solver_plan));
            assert(full[k] == solver_plan[k - init.len() as int]);
            assert(!is_rational_step(solver_plan[k - init.len() as int]));
            assert(step_target(solver_plan[k - init.len() as int]) == id);
        }
        // Backward: if id ∈ circle_targets(solver_plan), exists k with !is_rational(solver_plan[k])
        if circle_targets(solver_plan).contains(id) {
            let k = choose|k: int| 0 <= k < solver_plan.len()
                && !is_rational_step(#[trigger] solver_plan[k])
                && step_target(solver_plan[k]) == id;
            let fk = k + init.len() as int;
            assert(full[fk] == solver_plan[k]);
        }
    }
}

// ===========================================================================
//  Exec: Build initial PointSteps at runtime
// ===========================================================================

/// Build a Vec<RuntimeStepData> for the initially-resolved entities.
/// Iterates 0..n, creating a PointStep for each i where flags[i] == true.
pub fn build_initial_steps_exec(
    points: &Vec<RuntimePoint2>,
    flags: &Vec<bool>,
) -> (out: Vec<RuntimeStepData>)
    requires
        points@.len() == flags@.len(),
        all_points_wf(points@),
    ensures
        forall|j: int| 0 <= j < out@.len() ==> (#[trigger] out@[j]).wf_spec(),
        plan_to_spec(out@) =~= initial_point_steps(points_view(points@), flags@),
{
    let n = points.len();
    let ghost pts_spec = points_view(points@);
    let mut steps: Vec<RuntimeStepData> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            i <= n,
            n == points@.len(),
            n == flags@.len(),
            all_points_wf(points@),
            pts_spec == points_view(points@),
            forall|j: int| 0 <= j < steps@.len() ==> (#[trigger] steps@[j]).wf_spec(),
            plan_to_spec(steps@) =~= initial_point_steps(pts_spec.take(i as int), flags@.take(i as int)),
        decreases n - i,
    {
        proof {
            // Help Z3 with take(i+1) decomposition
            assert(pts_spec.take(i as int + 1).take(i as int) =~= pts_spec.take(i as int));
            assert(flags@.take(i as int + 1).take(i as int) =~= flags@.take(i as int));
        }

        if flags[i] {
            let x = copy_rational(&points[i].x);
            let y = copy_rational(&points[i].y);
            let ghost spec_pos: Point2<RationalModel> = pts_spec[i as int];
            let ghost spec_step = ConstructionStep::<RationalModel>::PointStep {
                id: i as nat,
                position: spec_pos,
            };
            let step = RuntimeStepData::PointStep {
                target: i,
                x,
                y,
                model: Ghost(spec_step),
            };

            proof {
                // Show the new step is well-formed
                assert(step.wf_spec());
                // Show plan_to_spec correspondence after push
                let old_spec = plan_to_spec(steps@);
                let new_step_spec = step.spec_step();
                assert(new_step_spec == (ConstructionStep::PointStep {
                    id: i as nat, position: pts_spec[i as int],
                }));
                // initial_point_steps(take(i+1), take(i+1)) = take(i) version .push(...)
                // since flags@.take(i+1)[i] == flags@[i] == true
                assert(flags@.take(i as int + 1)[i as int] == flags@[i as int]);
                assert(pts_spec.take(i as int + 1)[i as int] == pts_spec[i as int]);
            }

            steps.push(step);

            proof {
                // After push, plan_to_spec(steps@) should equal
                // initial_point_steps(pts_spec.take(i+1), flags@.take(i+1))
                assert(plan_to_spec(steps@) =~=
                    plan_to_spec(steps@.drop_last()).push(steps@.last().spec_step()));
                assert(plan_to_spec(steps@.drop_last()) =~=
                    initial_point_steps(pts_spec.take(i as int), flags@.take(i as int)));
            }
        } else {
            proof {
                // flags[i] == false, so initial_point_steps unchanged
                assert(flags@.take(i as int + 1)[i as int] == flags@[i as int]);
            }
        }

        i = i + 1;
    }

    proof {
        assert(pts_spec.take(n as int) =~= pts_spec);
        assert(flags@.take(n as int) =~= flags@);
    }

    steps
}

/// Concatenate initial steps with solver steps.
pub fn concat_plans(
    initial: Vec<RuntimeStepData>,
    solver: &Vec<RuntimeStepData>,
) -> (out: Vec<RuntimeStepData>)
    requires
        forall|j: int| 0 <= j < initial@.len() ==> (#[trigger] initial@[j]).wf_spec(),
        forall|j: int| 0 <= j < solver@.len() ==> (#[trigger] solver@[j]).wf_spec(),
    ensures
        out@.len() == initial@.len() + solver@.len(),
        forall|j: int| 0 <= j < out@.len() ==> (#[trigger] out@[j]).wf_spec(),
        plan_to_spec(out@) =~= plan_to_spec(initial@) + plan_to_spec(solver@),
{
    let mut result = initial;
    let mut i: usize = 0;
    let ghost old_result = result@;

    while i < solver.len()
        invariant
            i <= solver@.len(),
            result@.len() == old_result.len() + i,
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < solver@.len() ==> (#[trigger] solver@[j]).wf_spec(),
            // First part matches initial
            forall|j: int| 0 <= j < old_result.len() ==>
                (#[trigger] result@[j]).spec_step() == old_result[j].spec_step(),
            // Appended part matches solver
            forall|j: int| 0 <= j < i ==>
                (#[trigger] result@[old_result.len() + j]).spec_step() == solver@[j].spec_step(),
        decreases solver@.len() - i,
    {
        let step = copy_step(&solver[i]);
        result.push(step);
        i = i + 1;
    }

    proof {
        // Show plan_to_spec distributes over concatenation
        assert(plan_to_spec(result@) =~=
            plan_to_spec(old_result) + plan_to_spec(solver@)) by {
            assert forall|j: int| 0 <= j < result@.len()
            implies (#[trigger] plan_to_spec(result@)[j]) ==
                (plan_to_spec(old_result) + plan_to_spec(solver@))[j]
            by {
                if j < old_result.len() as int {
                    // result@[j].spec_step() == old_result[j].spec_step()
                    assert(result@[j].spec_step() == old_result[j].spec_step());
                } else {
                    let k = j - old_result.len() as int;
                    assert(result@[old_result.len() + k].spec_step()
                        == solver@[k].spec_step());
                }
            }
        }
    }

    result
}

// ===========================================================================
//  Helpers: copy points and flags
// ===========================================================================

fn copy_point2(p: &RuntimePoint2) -> (out: RuntimePoint2)
    requires p.wf_spec(),
    ensures out.wf_spec(), out@ == p@,
{
    RuntimePoint2::new(copy_rational(&p.x), copy_rational(&p.y))
}

fn copy_points_vec(points: &Vec<RuntimePoint2>) -> (out: Vec<RuntimePoint2>)
    requires all_points_wf(points@),
    ensures
        out@.len() == points@.len(),
        all_points_wf(out@),
        points_view(out@) =~= points_view(points@),
{
    let mut result: Vec<RuntimePoint2> = Vec::new();
    let mut i: usize = 0;
    while i < points.len()
        invariant
            i <= points@.len(),
            result@.len() == i,
            all_points_wf(points@),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==>
                (#[trigger] result@[j])@ == points@[j]@,
        decreases points@.len() - i,
    {
        let pt = copy_point2(&points[i]);
        result.push(pt);
        i = i + 1;
    }
    proof {
        assert(all_points_wf(result@));
        assert(points_view(result@) =~= points_view(points@)) by {
            assert forall|j: int| 0 <= j < result@.len()
            implies (#[trigger] points_view(result@)[j]) == points_view(points@)[j]
            by {
                assert(result@[j]@ == points@[j]@);
            }
        }
    }
    result
}

fn copy_flags_vec(flags: &Vec<bool>) -> (out: Vec<bool>)
    ensures
        out@.len() == flags@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]) == flags@[i],
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < flags.len()
        invariant
            i <= flags@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]) == flags@[j],
        decreases flags@.len() - i,
    {
        result.push(flags[i]);
        i = i + 1;
    }
    result
}

// ===========================================================================
//  Pipeline: solve_and_verify
// ===========================================================================

/// A verified solution: the plan, execution results, and ghost constraints.
pub struct VerifiedSolution<R: PositiveRadicand<RationalModel>> {
    /// The solver plan (steps for free entities only).
    pub plan: Vec<RuntimeStepData>,
    /// Execution results from execute_plan_runtime.
    pub results: Vec<RuntimeConstructionResult<R>>,
    /// Extension-level resolved points for all entities.
    pub ext_points: Vec<RuntimeQExtPoint2<R>>,
    /// Ghost constraints for the soundness theorem.
    pub ghost_constraints: Ghost<Seq<Constraint<RationalModel>>>,
}

/// A type-erased solution containing rational approximations.
/// Used by solve_and_verify_auto which dispatches across radicand types.
pub struct SolvedPoints {
    /// The solver plan (steps for free entities only).
    pub plan: Vec<RuntimeStepData>,
    /// Rational (re) components of the solved points for ALL entities.
    /// For rational entities, this is the exact position.
    /// For irrational entities, this is the rational part (re of a + b*sqrt(d)).
    pub points_re: Vec<RuntimePoint2>,
}

/// Extract rational parts from ext_points into a Vec<RuntimePoint2>.
fn extract_rational_parts<R: PositiveRadicand<RationalModel>>(
    ext_points: &Vec<RuntimeQExtPoint2<R>>,
) -> (out: Vec<RuntimePoint2>)
    requires
        forall|i: int| 0 <= i < ext_points@.len() ==> (#[trigger] ext_points@[i]).wf_spec(),
    ensures
        out@.len() == ext_points@.len(),
        all_points_wf(out@),
{
    let mut result: Vec<RuntimePoint2> = Vec::new();
    let mut i: usize = 0;
    while i < ext_points.len()
        invariant
            i <= ext_points@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < ext_points@.len() ==> (#[trigger] ext_points@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
        decreases ext_points@.len() - i,
    {
        let x_re = copy_rational(&ext_points[i].x.re);
        let y_re = copy_rational(&ext_points[i].y.re);
        let pt = RuntimePoint2::new(x_re, y_re);
        result.push(pt);
        i = i + 1;
    }
    proof {
        assert(all_points_wf(result@));
    }
    result
}

/// Convert a VerifiedSolution to SolvedPoints by extracting rational parts.
fn to_solved_points<R: PositiveRadicand<RationalModel>>(
    solution: &VerifiedSolution<R>,
) -> (out: SolvedPoints)
    requires
        forall|i: int| 0 <= i < solution.ext_points@.len() ==>
            (#[trigger] solution.ext_points@[i]).wf_spec(),
        forall|j: int| 0 <= j < solution.plan@.len() ==>
            (#[trigger] solution.plan@[j]).wf_spec(),
{
    let plan = copy_plan(&solution.plan);
    let points_re = extract_rational_parts(&solution.ext_points);
    SolvedPoints { plan, points_re }
}

/// Verify pre-computed plan variants against constraints.
/// For each variant: check plan soundness, execute, check ext constraints.
/// Returns all verified solutions.
fn verify_variants<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    variants: &Vec<Vec<RuntimeStepData>>,
    constraints: &Vec<RuntimeConstraint>,
    initial_points: &Vec<RuntimePoint2>,
    initial_flags: &Vec<bool>,
) -> (out: Vec<VerifiedSolution<R>>)
    requires
        initial_points@.len() == initial_flags@.len(),
        all_points_wf(initial_points@),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], initial_points@.len() as nat),
        forall|i: int| 0 <= i < initial_flags@.len() ==>
            (#[trigger] initial_flags@[i]) ==
            partial_resolved_map(points_view(initial_points@), initial_flags@)
                .dom().contains(i as nat),
        forall|si: int| 0 <= si < variants@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                (#[trigger] variants@[si]@[j]).wf_spec(),
        forall|si: int| 0 <= si < variants@.len() ==>
            forall|i: int, j: int|
                0 <= i < (#[trigger] variants@[si])@.len()
                && 0 <= j < variants@[si]@.len() && i != j ==>
                step_target(#[trigger] variants@[si]@[i].spec_step()) !=
                step_target(#[trigger] variants@[si]@[j].spec_step()),
        forall|si: int| 0 <= si < variants@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                step_has_positive_discriminant((#[trigger] variants@[si]@[j]).spec_step()),
        forall|si: int| 0 <= si < variants@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                (step_target((#[trigger] variants@[si]@[j]).spec_step()) as int)
                    < initial_points@.len(),
        forall|si: int| 0 <= si < variants@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                step_geometrically_valid((#[trigger] variants@[si]@[j]).spec_step()),
    ensures
        forall|si: int| 0 <= si < out@.len() ==>
            forall|i: int| 0 <= i < (#[trigger] out@[si]).ext_points@.len() ==>
                (#[trigger] out@[si].ext_points@[i]).wf_spec(),
        forall|si: int| 0 <= si < out@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] out@[si]).plan@.len() ==>
                (#[trigger] out@[si].plan@[j]).wf_spec(),
{
    let n_points = initial_points.len();
    let mut solutions: Vec<VerifiedSolution<R>> = Vec::new();
    let mut vi: usize = 0;

    while vi < variants.len()
        invariant
            vi <= variants@.len(),
            n_points == initial_points@.len(),
            initial_flags@.len() == n_points,
            all_points_wf(initial_points@),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
            forall|i: int| 0 <= i < initial_flags@.len() ==>
                (#[trigger] initial_flags@[i]) ==
                partial_resolved_map(points_view(initial_points@), initial_flags@)
                    .dom().contains(i as nat),
            forall|si: int| 0 <= si < variants@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                    (#[trigger] variants@[si]@[j]).wf_spec(),
            forall|si: int| 0 <= si < variants@.len() ==>
                forall|i: int, j: int|
                    0 <= i < (#[trigger] variants@[si])@.len()
                    && 0 <= j < variants@[si]@.len() && i != j ==>
                    step_target(#[trigger] variants@[si]@[i].spec_step()) !=
                    step_target(#[trigger] variants@[si]@[j].spec_step()),
            forall|si: int| 0 <= si < variants@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                    step_has_positive_discriminant((#[trigger] variants@[si]@[j]).spec_step()),
            forall|si: int| 0 <= si < variants@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                    (step_target((#[trigger] variants@[si]@[j]).spec_step()) as int)
                        < n_points,
            forall|si: int| 0 <= si < variants@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                    step_geometrically_valid((#[trigger] variants@[si]@[j]).spec_step()),
            // Output solutions have well-formed fields
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|i: int| 0 <= i < (#[trigger] solutions@[si]).ext_points@.len() ==>
                    (#[trigger] solutions@[si].ext_points@[i]).wf_spec(),
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] solutions@[si]).plan@.len() ==>
                    (#[trigger] solutions@[si].plan@[j]).wf_spec(),
        decreases variants@.len() - vi,
    {
        // Copy initial state for this variant
        let mut work_points = copy_points_vec(initial_points);
        let mut work_flags = copy_flags_vec(initial_flags);

        // Step 1: Runtime plan soundness check
        let sound = verify_plan_soundness_exec::<R, RR>(
            &variants[vi], constraints, &mut work_points, &mut work_flags,
        );

        if !sound {
            vi = vi + 1;
            continue;
        }

        // Step 2: Execute the solver plan to get results
        let results = execute_plan_runtime::<R>(&variants[vi]);

        // Step 3: Build extension-level resolved points and check verification constraints
        let ext_points = build_ext_resolved_vec::<R, RR>(
            &results, &variants[vi], initial_points,
        );
        let ext_ok = check_all_verification_constraints_ext::<R, RR>(
            constraints, &ext_points, n_points,
        );

        if !ext_ok {
            vi = vi + 1;
            continue;
        }

        // Step 3b: Formal bridge — all constraints satisfied at extension level.
        // The det_plan trick (lemma_solver_to_soundness_det) proves that if
        // plan_structurally_sound holds and verification constraints pass,
        // then ALL constraints are satisfied against execute_plan_in_ext.
        proof {
            let plan_spec = plan_to_spec(variants@[vi as int]@);
            let cstr_spec = constraints_to_spec(constraints@);
            let pts_spec = points_view(initial_points@);
            let full_plan = build_full_plan(pts_spec, initial_flags@, plan_spec);

            // PROOF DEBT: These assumes bridge the gap between runtime validation
            // and the spec-level predicates. The runtime checks in
            // verify_plan_soundness_exec + check_step_satisfaction_replay_exec
            // verify all 12 conjuncts of plan_structurally_sound, and
            // check_all_verification_constraints_ext verifies constraint satisfaction,
            // but their ensures don't yet propagate these facts to spec level.
            //
            // Eliminating these assumes requires:
            //   (a) Connecting partial_resolved_map to execute_plan(full_plan.take(si))
            //   (b) Propagating check_step_satisfaction_replay_exec results to spec
            //   (c) Connecting build_ext_resolved_vec output to execute_plan_in_ext
            assume(plan_structurally_sound::<R>(full_plan, cstr_spec));
            assume(forall|ci: int| 0 <= ci < cstr_spec.len()
                && is_verification_constraint(#[trigger] cstr_spec[ci])
                ==> constraint_satisfied(
                    lift_constraint::<RationalModel, R>(cstr_spec[ci]),
                    execute_plan_in_ext::<RationalModel, R>(full_plan)));

            // Formal bridge: derives ALL constraints satisfied from the two assumes above
            lemma_solver_to_soundness_det::<R>(full_plan, cstr_spec);

            // Conclusion (available here, not yet propagated to ensures):
            // forall|ci| 0 <= ci < cstr_spec.len() ==>
            //     constraint_satisfied(
            //         lift_constraints::<RationalModel, R>(cstr_spec)[ci],
            //         execute_plan_in_ext::<RationalModel, R>(full_plan))
        }

        // Step 4: Package into VerifiedSolution
        let ghost cstr_spec = constraints_to_spec(constraints@);
        let solution = VerifiedSolution {
            plan: copy_plan(&variants[vi]),
            results,
            ext_points,
            ghost_constraints: Ghost(cstr_spec),
        };
        solutions.push(solution);

        vi = vi + 1;
    }

    solutions
}

/// Solve all sign variants, verify plan soundness and constraint satisfaction.
/// Returns all verified solutions (runtime-validated, not yet formally certified).
pub fn solve_and_verify<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    free_ids: &Vec<usize>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: Vec<VerifiedSolution<R>>)
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
{
    // Save initial state
    let initial_points = copy_points_vec(points);
    let initial_flags = copy_flags_vec(resolved_flags);

    // Solve all sign variants
    let variants = solve_all_variants(free_ids, constraints, points, resolved_flags);

    // Verify each variant
    verify_variants::<R, RR>(&variants, constraints, &initial_points, &initial_flags)
}

/// Copy an entire plan (Vec<RuntimeStepData>).
fn copy_plan(plan: &Vec<RuntimeStepData>) -> (out: Vec<RuntimeStepData>)
    requires
        forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
    ensures
        out@.len() == plan@.len(),
        forall|j: int| 0 <= j < out@.len() ==> (#[trigger] out@[j]).wf_spec(),
        plan_to_spec(out@) =~= plan_to_spec(plan@),
{
    let mut result: Vec<RuntimeStepData> = Vec::new();
    let mut i: usize = 0;
    while i < plan.len()
        invariant
            i <= plan@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==>
                (#[trigger] result@[j]).spec_step() == plan@[j].spec_step(),
        decreases plan@.len() - i,
    {
        let step = copy_step(&plan[i]);
        result.push(step);
        i = i + 1;
    }
    proof {
        assert(plan_to_spec(result@) =~= plan_to_spec(plan@)) by {
            assert forall|j: int| 0 <= j < result@.len()
            implies (#[trigger] plan_to_spec(result@)[j]) == plan_to_spec(plan@)[j]
            by {
                assert(result@[j].spec_step() == plan@[j].spec_step());
            }
        }
    }
    result
}

// ===========================================================================
//  Radicand detection + concrete dispatch
// ===========================================================================

/// Detect the common discriminant of all circle steps in a plan variant set.
/// Returns 0 if no circle steps, or if discriminants are mixed/unrecognized.
/// Returns 2, 3, or 5 if all circle steps share that discriminant.
fn detect_discriminant(
    variants: &Vec<Vec<RuntimeStepData>>,
) -> (out: u8)
    requires
        variants@.len() > 0,
        forall|si: int| 0 <= si < variants@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] variants@[si])@.len() ==>
                (#[trigger] variants@[si]@[j]).wf_spec(),
{
    let plan = &variants[0];
    let d2 = RuntimeRational::from_int(2);
    let d3 = RuntimeRational::from_int(3);
    let d5 = RuntimeRational::from_int(5);
    let mut found: u8 = 0; // 0 = none seen yet
    let mut i: usize = 0;

    while i < plan.len()
        invariant
            i <= plan@.len(),
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            d2.wf_spec(), d3.wf_spec(), d5.wf_spec(),
        decreases plan@.len() - i,
    {
        let disc_val: u8 = match &plan[i] {
            RuntimeStepData::CircleLine { circle, line, .. } => {
                let disc = cl_discriminant_exec(circle, line);
                if disc.eq(&d2) { 2u8 }
                else if disc.eq(&d3) { 3u8 }
                else if disc.eq(&d5) { 5u8 }
                else { return 0; } // Unrecognized discriminant
            }
            RuntimeStepData::CircleCircle { c1, c2, .. } => {
                let disc = cc_discriminant_exec(c1, c2);
                if disc.eq(&d2) { 2u8 }
                else if disc.eq(&d3) { 3u8 }
                else if disc.eq(&d5) { 5u8 }
                else { return 0; }
            }
            _ => { 0u8 } // Rational step, skip
        };

        if disc_val > 0 {
            if found == 0 {
                found = disc_val;
            } else if found != disc_val {
                return 0; // Mixed discriminants
            }
        }
        i = i + 1;
    }

    found
}

/// Convert all verified solutions to erased SolvedPoints.
fn collect_solved_points<R: PositiveRadicand<RationalModel>>(
    solutions: &Vec<VerifiedSolution<R>>,
) -> (out: Vec<SolvedPoints>)
    requires
        forall|si: int| 0 <= si < solutions@.len() ==>
            forall|i: int| 0 <= i < (#[trigger] solutions@[si]).ext_points@.len() ==>
                (#[trigger] solutions@[si].ext_points@[i]).wf_spec(),
        forall|si: int| 0 <= si < solutions@.len() ==>
            forall|j: int| 0 <= j < (#[trigger] solutions@[si]).plan@.len() ==>
                (#[trigger] solutions@[si].plan@[j]).wf_spec(),
{
    let mut result: Vec<SolvedPoints> = Vec::new();
    let mut i: usize = 0;
    while i < solutions.len()
        invariant
            i <= solutions@.len(),
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|k: int| 0 <= k < (#[trigger] solutions@[si]).ext_points@.len() ==>
                    (#[trigger] solutions@[si].ext_points@[k]).wf_spec(),
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] solutions@[si]).plan@.len() ==>
                    (#[trigger] solutions@[si].plan@[j]).wf_spec(),
        decreases solutions@.len() - i,
    {
        let sp = to_solved_points(&solutions[i]);
        result.push(sp);
        i = i + 1;
    }
    result
}

/// Top-level solve-and-verify with automatic radicand detection.
/// Detects whether all circle steps share discriminant 2, 3, or 5,
/// then dispatches to the appropriate generic instantiation.
/// Returns solved point sets (rational approximations) for each valid variant.
pub fn solve_and_verify_auto(
    free_ids: &Vec<usize>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: Vec<SolvedPoints>)
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
{
    // Save initial state before solve_all_variants mutates it
    let initial_points = copy_points_vec(points);
    let initial_flags = copy_flags_vec(resolved_flags);

    // Solve all sign variants (mutates points/resolved_flags)
    let variants = solve_all_variants(free_ids, constraints, points, resolved_flags);

    if variants.len() == 0 {
        return Vec::new();
    }

    // Detect discriminant from variants (no mutation)
    let disc = detect_discriminant(&variants);

    // Dispatch to the appropriate generic instantiation
    match disc {
        2 => {
            let solutions = verify_variants::<Sqrt2, RuntimeSqrt2>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
        3 => {
            let solutions = verify_variants::<Sqrt3, RuntimeSqrt3>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
        5 => {
            let solutions = verify_variants::<Sqrt5, RuntimeSqrt5>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
        _ => {
            // No circle steps (pure rational) or unrecognized discriminant.
            // Use Sqrt2 — radicand check passes trivially for rational-only plans.
            let solutions = verify_variants::<Sqrt2, RuntimeSqrt2>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
    }
}

} // verus!
