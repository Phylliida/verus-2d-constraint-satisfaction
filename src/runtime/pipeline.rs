use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::runtime::point2::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use verus_quadratic_extension::radicand::PositiveRadicand;
use verus_quadratic_extension::spec::SpecQuadExt;
use verus_geometry::constructed_scalar::lift_point2;
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

/// Initial steps are all PointSteps, hence trivially geometrically valid,
/// have positive discriminant, and match any radicand.
proof fn lemma_initial_steps_trivial_properties<R: PositiveRadicand<RationalModel>>(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
)
    requires points.len() == flags.len(),
    ensures
        forall|i: int|
            0 <= i < initial_point_steps(points, flags).len() ==> {
                let step = #[trigger] initial_point_steps(points, flags)[i];
                step_geometrically_valid(step)
                && step_has_positive_discriminant(step)
                && step_radicand_matches::<R>(step)
            },
    decreases points.len(),
{
    if points.len() > 0 {
        let n = (points.len() - 1) as int;
        let prefix = initial_point_steps(points.take(n), flags.take(n));
        let full = initial_point_steps(points, flags);
        lemma_initial_steps_trivial_properties::<R>(points.take(n), flags.take(n));
        if flags[n] {
            assert forall|i: int| 0 <= i < full.len()
            implies {
                let step = #[trigger] full[i];
                step_geometrically_valid(step)
                && step_has_positive_discriminant(step)
                && step_radicand_matches::<R>(step)
            } by {
                if i < prefix.len() as int {
                    assert(full[i] == prefix[i]);
                }
            }
        }
    }
}

/// For each initial step, execute_step_in_ext gives lift_point2(points[target]).
/// This holds because every initial step is a PointStep with position = points[id].
proof fn lemma_initial_steps_execute_in_ext<R: PositiveRadicand<RationalModel>>(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
)
    requires points.len() == flags.len(),
    ensures
        forall|i: int|
            0 <= i < initial_point_steps(points, flags).len() ==> {
                let step = #[trigger] initial_point_steps(points, flags)[i];
                execute_step_in_ext::<RationalModel, R>(step)
                    == lift_point2::<RationalModel, R>(points[step_target(step) as int])
            },
    decreases points.len(),
{
    if points.len() > 0 {
        let n = (points.len() - 1) as int;
        let prefix = initial_point_steps(points.take(n), flags.take(n));
        let full = initial_point_steps(points, flags);
        lemma_initial_steps_execute_in_ext::<R>(points.take(n), flags.take(n));
        lemma_initial_steps_targets_bounded(points.take(n), flags.take(n));

        if flags[n] {
            assert forall|i: int|
                0 <= i < full.len()
            implies {
                let step = #[trigger] full[i];
                execute_step_in_ext::<RationalModel, R>(step)
                    == lift_point2::<RationalModel, R>(points[step_target(step) as int])
            }
            by {
                if i < prefix.len() as int {
                    assert(full[i] == prefix[i]);
                    // From IH: execute_step_in_ext(prefix[i])
                    //   == lift_point2(points.take(n)[step_target(prefix[i])])
                    // step_target(prefix[i]) < n from targets_bounded
                    // points.take(n)[j] == points[j] for j < n
                } else {
                    // full[i] == PointStep { id: n, position: points[n] }
                    // execute_step_in_ext = lift_point2(points[n])
                    // step_target = n
                }
            }
        }
        // !flags[n]: full == prefix, IH applies (with take/full equiv)
    }
}

/// Initial step targets always have flags[target] == true.
proof fn lemma_initial_steps_flags_true(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
)
    requires points.len() == flags.len(),
    ensures
        forall|i: int|
            0 <= i < initial_point_steps(points, flags).len() ==>
            flags[step_target(#[trigger] initial_point_steps(points, flags)[i]) as int],
    decreases points.len(),
{
    if points.len() > 0 {
        let n = (points.len() - 1) as int;
        let prefix = initial_point_steps(points.take(n), flags.take(n));
        let full = initial_point_steps(points, flags);
        lemma_initial_steps_flags_true(points.take(n), flags.take(n));
        lemma_initial_steps_targets_bounded(points.take(n), flags.take(n));

        if flags[n] {
            assert forall|i: int| 0 <= i < full.len()
            implies flags[step_target(#[trigger] full[i]) as int]
            by {
                if i < prefix.len() as int {
                    assert(full[i] == prefix[i]);
                    // IH: flags.take(n)[step_target(prefix[i])] == true
                    // step_target(prefix[i]) < n, so flags.take(n)[target] == flags[target]
                }
                // else: full[i] = PointStep { id: n, .. }, flags[n] == true
            }
        }
        // !flags[n]: full == prefix, IH applies
    }
}

/// Runtime check: all solver step targets have initial_flags[target] == false.
/// Needed to prove distinct_targets(full_plan) (no overlap between init and solver targets).
fn check_solver_targets_unresolved(
    plan: &Vec<RuntimeStepData>,
    flags: &Vec<bool>,
) -> (out: bool)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < plan@.len() ==>
            (step_target((#[trigger] plan@[i]).spec_step()) as int) < flags@.len(),
    ensures
        out ==> forall|j: int| 0 <= j < plan@.len() ==>
            !(#[trigger] flags@[step_target(plan@[j].spec_step()) as int]),
{
    let mut j: usize = 0;
    while j < plan.len()
        invariant
            j <= plan@.len(),
            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
            forall|i: int| 0 <= i < plan@.len() ==>
                (step_target((#[trigger] plan@[i]).spec_step()) as int) < flags@.len(),
            forall|k: int| 0 <= k < j ==>
                !(#[trigger] flags@[step_target(plan@[k].spec_step()) as int]),
        decreases plan@.len() - j,
    {
        let tid = plan[j].target_id();
        if flags[tid] {
            return false;
        }
        j = j + 1;
    }
    true
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

// ===========================================================================
//  Proof: execute_plan_in_ext map lookup for distinct-target plans
// ===========================================================================

/// For a plan with distinct targets, execute_plan_in_ext(plan)[target_k] == execute_step_in_ext(plan[k]).
proof fn lemma_execute_plan_in_ext_at_target<R: PositiveRadicand<RationalModel>>(
    plan: ConstructionPlan<RationalModel>,
)
    requires
        forall|i: int, j: int| 0 <= i < plan.len() && 0 <= j < plan.len() && i != j
            ==> step_target(plan[i]) != step_target(plan[j]),
    ensures
        forall|k: int| 0 <= k < plan.len()
            ==> execute_plan_in_ext::<RationalModel, R>(plan).dom().contains(
                step_target(#[trigger] plan[k])),
        forall|k: int| 0 <= k < plan.len()
            ==> (#[trigger] execute_plan_in_ext::<RationalModel, R>(plan)[step_target(plan[k])])
                == execute_step_in_ext::<RationalModel, R>(plan[k]),
    decreases plan.len(),
{
    if plan.len() > 0 {
        let prefix = plan.drop_last();
        let step = plan.last();
        let target = step_target(step);

        // Prefix has distinct targets
        assert forall|i: int, j: int|
            0 <= i < prefix.len() && 0 <= j < prefix.len() && i != j
        implies step_target(prefix[i]) != step_target(prefix[j])
        by {
            assert(prefix[i] == plan[i]);
            assert(prefix[j] == plan[j]);
        }

        lemma_execute_plan_in_ext_at_target::<R>(prefix);

        // result_map == prefix_map.insert(target, execute_step_in_ext(step))
        assert forall|k: int| 0 <= k < plan.len()
        implies execute_plan_in_ext::<RationalModel, R>(plan).dom().contains(
            step_target(#[trigger] plan[k]))
        by {
            if k < prefix.len() as int {
                assert(plan[k] == prefix[k]);
            }
        }

        assert forall|k: int| 0 <= k < plan.len()
        implies (#[trigger] execute_plan_in_ext::<RationalModel, R>(plan)[step_target(plan[k])])
            == execute_step_in_ext::<RationalModel, R>(plan[k])
        by {
            if k < prefix.len() as int {
                assert(plan[k] == prefix[k]);
                // step_target(plan[k]) != target (distinct targets)
                assert(step_target(plan[k]) != step_target(plan[(plan.len() - 1) as int]));
            }
        }
    }
}

/// For a plan with distinct targets, ext_vec_to_resolved_map agrees with
/// execute_plan_in_ext on all plan targets.
proof fn lemma_ext_vec_agrees_with_plan<R: PositiveRadicand<RationalModel>>(
    ext_points: Seq<RuntimeQExtPoint2<R>>,
    plan: ConstructionPlan<RationalModel>,
)
    requires
        // Distinct targets
        forall|i: int, j: int| 0 <= i < plan.len() && 0 <= j < plan.len() && i != j
            ==> step_target(plan[i]) != step_target(plan[j]),
        // All targets < ext_points.len()
        forall|k: int| 0 <= k < plan.len() ==>
            (step_target(#[trigger] plan[k]) as int) < ext_points.len(),
        // ext_points matches execute_step_in_ext at each target
        forall|k: int| 0 <= k < plan.len() ==>
            ext_points[step_target(#[trigger] plan[k]) as int]@
                == execute_step_in_ext::<RationalModel, R>(plan[k]),
    ensures
        forall|id: EntityId|
            execute_plan_in_ext::<RationalModel, R>(plan).dom().contains(id) ==>
            ext_vec_to_resolved_map::<R>(ext_points)[id]
                == execute_plan_in_ext::<RationalModel, R>(plan)[id],
    decreases plan.len(),
{
    if plan.len() > 0 {
        let prefix = plan.drop_last();
        let step = plan.last();
        let target = step_target(step);
        let last_idx = (plan.len() - 1) as int;

        // Prefix has distinct targets
        assert forall|i: int, j: int|
            0 <= i < prefix.len() && 0 <= j < prefix.len() && i != j
        implies step_target(prefix[i]) != step_target(prefix[j])
        by { assert(prefix[i] == plan[i]); assert(prefix[j] == plan[j]); }

        // Prefix satisfies ext_points match precondition
        assert forall|k: int| 0 <= k < prefix.len()
        implies ext_points[step_target(#[trigger] prefix[k]) as int]@
            == execute_step_in_ext::<RationalModel, R>(prefix[k])
        by { assert(prefix[k] == plan[k]); }

        assert forall|k: int| 0 <= k < prefix.len()
        implies (step_target(#[trigger] prefix[k]) as int) < ext_points.len()
        by { assert(prefix[k] == plan[k]); }

        // Inductive hypothesis
        lemma_ext_vec_agrees_with_plan::<R>(ext_points, prefix);

        let result_map = execute_plan_in_ext::<RationalModel, R>(plan);
        let prefix_map = execute_plan_in_ext::<RationalModel, R>(prefix);

        assert forall|id: EntityId|
            result_map.dom().contains(id)
        implies
            ext_vec_to_resolved_map::<R>(ext_points)[id] == result_map[id]
        by {
            if id == target {
                // result_map[target] == execute_step_in_ext(step)
                // plan.last() == plan[last_idx]
                assert(plan[last_idx] == step);
                assert(ext_points[target as int]@
                    == execute_step_in_ext::<RationalModel, R>(step));
                assert((target as int) < ext_points.len());
            } else {
                // id in prefix_map domain, use IH
            }
        }
    }
}

/// Extend is_fully_independent_plan from solver plan to full plan.
/// Key idea: circle_targets(full_plan) == circle_targets(solver_plan),
/// and entities in the domain at any step are either init targets (not circle targets,
/// since they're PointSteps) or solver targets (covered by solver independence).
proof fn lemma_full_plan_independent(
    pts: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
    solver_plan: ConstructionPlan<RationalModel>,
    cstr_spec: Seq<Constraint<RationalModel>>,
)
    requires
        pts.len() == flags.len(),
        is_fully_independent_plan(solver_plan, cstr_spec),
        // Full plan has distinct targets
        forall|i: int, j: int|
            0 <= i < build_full_plan(pts, flags, solver_plan).len()
            && 0 <= j < build_full_plan(pts, flags, solver_plan).len()
            && i != j ==>
            step_target(build_full_plan(pts, flags, solver_plan)[i])
                != step_target(build_full_plan(pts, flags, solver_plan)[j]),
        // Solver targets have flags == false
        forall|j: int| 0 <= j < solver_plan.len() ==>
            !(#[trigger] flags[step_target(solver_plan[j]) as int]),
        // Init targets have flags == true
        forall|i: int|
            0 <= i < initial_point_steps(pts, flags).len() ==>
            flags[step_target(#[trigger] initial_point_steps(pts, flags)[i]) as int],
        // All init steps are rational
        forall|i: int|
            0 <= i < initial_point_steps(pts, flags).len() ==>
            is_rational_step(#[trigger] initial_point_steps(pts, flags)[i]),
        // Solver targets bounded
        forall|j: int| 0 <= j < solver_plan.len() ==>
            (step_target(#[trigger] solver_plan[j]) as int) < flags.len(),
        // Init targets bounded
        forall|i: int|
            0 <= i < initial_point_steps(pts, flags).len() ==>
            (step_target(#[trigger] initial_point_steps(pts, flags)[i]) as int) < flags.len(),
    ensures
        is_fully_independent_plan(build_full_plan(pts, flags, solver_plan), cstr_spec),
{
    let full_plan = build_full_plan(pts, flags, solver_plan);
    let init_steps = initial_point_steps(pts, flags);
    let init_len: int = init_steps.len() as int;

    lemma_full_plan_circle_targets(pts, flags, solver_plan);
    // Now: circle_targets(full_plan) =~= circle_targets(solver_plan)

    assert forall|i: int| #![trigger full_plan[i]]
        0 <= i < full_plan.len()
    implies {
        let target = step_target(full_plan[i]);
        forall|ci: int| #![trigger cstr_spec[ci]]
            0 <= ci < cstr_spec.len()
            && constraint_entities(cstr_spec[ci]).contains(target)
            ==> forall|e: EntityId|
                constraint_entities(cstr_spec[ci]).contains(e) && e != target
                && execute_plan(full_plan.take(i)).dom().contains(e)
                ==> !circle_targets(full_plan).contains(e)
    } by {
        let target = step_target(full_plan[i]);
        assert forall|ci: int| #![trigger cstr_spec[ci]]
            0 <= ci < cstr_spec.len()
            && constraint_entities(cstr_spec[ci]).contains(target)
        implies forall|e: EntityId|
            constraint_entities(cstr_spec[ci]).contains(e) && e != target
            && execute_plan(full_plan.take(i)).dom().contains(e)
            ==> !circle_targets(full_plan).contains(e)
        by {
            assert forall|e: EntityId|
                constraint_entities(cstr_spec[ci]).contains(e) && e != target
                && execute_plan(full_plan.take(i)).dom().contains(e)
            implies !circle_targets(full_plan).contains(e)
            by {
                // e is in the domain: there exists j < i with step_target(full_plan[j]) == e
                lemma_execute_plan_dom::<RationalModel>(full_plan.take(i), e);
                let j = choose|j: int| 0 <= j < full_plan.take(i).len()
                    && step_target(#[trigger] full_plan.take(i)[j]) == e;
                assert(full_plan.take(i)[j] == full_plan[j]);
                assert(step_target(full_plan[j]) == e);

                if j < init_len {
                    // e is an init target → flags[e] == true
                    assert(full_plan[j] == init_steps[j]);
                    assert(flags[e as int]);
                    // circle targets are solver targets → flags == false
                    // So e ∉ circle_targets
                    if circle_targets(full_plan).contains(e) {
                        // exists k with !is_rational(full_plan[k]) && target(full_plan[k]) == e
                        let k = choose|k: int| 0 <= k < full_plan.len()
                            && !is_rational_step(#[trigger] full_plan[k])
                            && step_target(full_plan[k]) == e;
                        // k must be >= init_len (all init steps are rational)
                        if k < init_len {
                            assert(full_plan[k] == init_steps[k]);
                        }
                        // So k >= init_len → solver step → flags[e] == false
                        assert(full_plan[k] == solver_plan[k - init_len]);
                        assert(!flags[e as int]); // contradiction with flags[e] == true
                    }
                } else {
                    // e is a solver target. j >= init_len, j' = j - init_len.
                    let j_solver = j - init_len;
                    assert(full_plan[j] == solver_plan[j_solver]);

                    if i < init_len {
                        // impossible: j < i < init_len, but we're in j >= init_len case
                        assert(false);
                    }

                    // i >= init_len, solver step at i' = i - init_len
                    let i_solver = i - init_len;
                    // e in execute_plan(solver_plan.take(i_solver)).dom()
                    assert(j_solver < i_solver);
                    assert(solver_plan.take(i_solver)[j_solver] == solver_plan[j_solver]);
                    lemma_execute_plan_dom::<RationalModel>(solver_plan.take(i_solver), e);

                    // From solver independence: e ∉ circle_targets(solver_plan)
                    // circle_targets(full_plan) =~= circle_targets(solver_plan)
                }
            }
        }
    }
}

/// Transfer constraint_satisfied for verification constraints between
/// two resolved maps that agree on all constraint entity IDs.
proof fn lemma_verification_constraint_transfer<R: PositiveRadicand<RationalModel>>(
    c: Constraint<RationalModel>,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        is_verification_constraint(c),
        constraint_satisfied(lift_constraint::<RationalModel, R>(c), resolved1),
        forall|e: EntityId| constraint_entities(c).contains(e) ==>
            resolved2.dom().contains(e) && resolved1[e] == resolved2[e],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(c), resolved2),
{
    // Explicitly match to guide Z3 through only 3 arms.
    match c {
        Constraint::Tangent { line_a, line_b, center, radius_point } => {
            assert(resolved1[line_a] == resolved2[line_a]);
            assert(resolved1[line_b] == resolved2[line_b]);
            assert(resolved1[center] == resolved2[center]);
            assert(resolved1[radius_point] == resolved2[radius_point]);
        }
        Constraint::CircleTangent { c1, rp1, c2, rp2 } => {
            assert(resolved1[c1] == resolved2[c1]);
            assert(resolved1[rp1] == resolved2[rp1]);
            assert(resolved1[c2] == resolved2[c2]);
            assert(resolved1[rp2] == resolved2[rp2]);
        }
        Constraint::Angle { a1, a2, b1, b2, cos_sq } => {
            assert(resolved1[a1] == resolved2[a1]);
            assert(resolved1[a2] == resolved2[a2]);
            assert(resolved1[b1] == resolved2[b1]);
            assert(resolved1[b2] == resolved2[b2]);
        }
        _ => {} // impossible by is_verification_constraint
    }
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

        // Step 1b: Check solver targets are unresolved (for distinct_targets proof)
        let targets_unresolved = check_solver_targets_unresolved(
            &variants[vi], initial_flags,
        );
        if !targets_unresolved {
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
        proof {
            let plan_spec = plan_to_spec(variants@[vi as int]@);
            let cstr_spec = constraints_to_spec(constraints@);
            let pts_spec = points_view(initial_points@);
            let full_plan = build_full_plan(pts_spec, initial_flags@, plan_spec);
            let init_steps = initial_point_steps(pts_spec, initial_flags@);
            let init_len = init_steps.len() as int;

            // === Prove structural conjuncts 1, 2, 6, 7, 8 ===

            // Conjunct 1: distinct_targets(full_plan)
            lemma_initial_steps_distinct_targets(pts_spec, initial_flags@);
            lemma_initial_steps_flags_true(pts_spec, initial_flags@);
            lemma_initial_steps_targets_bounded(pts_spec, initial_flags@);
            assert forall|i: int, j: int|
                0 <= i < full_plan.len() && 0 <= j < full_plan.len() && i != j
            implies step_target(full_plan[i]) != step_target(full_plan[j])
            by {
                if i < init_len && j < init_len {
                    // Both init: from lemma_initial_steps_distinct_targets
                    assert(full_plan[i] == init_steps[i]);
                    assert(full_plan[j] == init_steps[j]);
                } else if i >= init_len && j >= init_len {
                    // Both solver: from precondition (solver distinct targets)
                    assert(full_plan[i] == plan_spec[i - init_len]);
                    assert(full_plan[j] == plan_spec[j - init_len]);
                    assert(plan_spec[i - init_len]
                        == variants@[vi as int]@[i - init_len].spec_step());
                    assert(plan_spec[j - init_len]
                        == variants@[vi as int]@[j - init_len].spec_step());
                } else {
                    // Cross: init target has flags == true, solver target has flags == false
                    let (init_idx, solver_idx) = if i < init_len {
                        (i, j - init_len)
                    } else {
                        (j, i - init_len)
                    };
                    let init_target = step_target(init_steps[init_idx]);
                    let solver_step = plan_spec[solver_idx];
                    assert(solver_step == variants@[vi as int]@[solver_idx].spec_step());
                    // init target: flags[init_target] == true
                    // solver target: flags[step_target(solver_step)] == false
                    // (from check_solver_targets_unresolved)
                    // So they can't be equal.
                }
            }

            // Conjunct 2: constraint_well_formed
            // (from verify_plan_soundness_exec ensures)

            // Conjuncts 6, 7, 8: geometrically valid, positive discriminant, radicand matches
            lemma_initial_steps_trivial_properties::<R>(pts_spec, initial_flags@);

            // Prove each step property for the full plan
            assert forall|j: int| #![trigger full_plan[j]]
                0 <= j < full_plan.len()
            implies step_geometrically_valid(full_plan[j])
                && step_has_positive_discriminant(full_plan[j])
                && step_radicand_matches::<R>(full_plan[j])
            by {
                if j < init_len {
                    assert(full_plan[j] == init_steps[j]);
                } else {
                    assert(full_plan[j] == plan_spec[j - init_len]);
                    assert(plan_spec[j - init_len]
                        == variants@[vi as int]@[j - init_len].spec_step());
                }
            }

            // Conjunct 5: is_fully_independent_plan(full_plan, cstr_spec)
            lemma_initial_steps_are_rational(pts_spec, initial_flags@);
            // Solver targets have flags == false: connect plan_spec to solver_plan
            assert forall|j: int| 0 <= j < plan_spec.len()
            implies !(#[trigger] initial_flags@[step_target(plan_spec[j]) as int])
            by {
                assert(plan_spec[j] == variants@[vi as int]@[j].spec_step());
            }
            lemma_full_plan_independent(
                pts_spec, initial_flags@, plan_spec, cstr_spec);

            // PROOF DEBT: remaining conjuncts (3, 4, 9-12)
            // 3: entity coverage, 4: locus ordered,
            // 9: at_most_two_nontrivial_loci, 10: step satisfaction,
            // 11: step loci match geometry, 12: nondegeneracy
            assume(forall|ci: int| 0 <= ci < cstr_spec.len() ==>
                constraint_entities(#[trigger] cstr_spec[ci])
                    .subset_of(execute_plan(full_plan).dom()));
            assume(plan_locus_ordered(full_plan, cstr_spec));
            assume(forall|si: int| #![trigger full_plan[si]]
                0 <= si < full_plan.len() ==>
                at_most_two_nontrivial_loci(
                    step_target(full_plan[si]), cstr_spec,
                    execute_plan(full_plan.take(si as int)).dom()));
            assume(forall|si: int| #![trigger full_plan[si]]
                0 <= si < full_plan.len() && is_rational_step(full_plan[si]) ==>
                step_satisfies_all_constraint_loci(
                    full_plan[si], cstr_spec, execute_plan(full_plan.take(si as int))));
            assume(forall|si: int| #![trigger full_plan[si]]
                0 <= si < full_plan.len() && !is_rational_step(full_plan[si]) ==>
                step_loci_match_geometry(
                    full_plan[si], cstr_spec, execute_plan(full_plan.take(si as int))));
            assume(forall|si: int, ci: int|
                #![trigger full_plan[si], cstr_spec[ci]]
                0 <= si < full_plan.len() && 0 <= ci < cstr_spec.len() ==>
                constraint_locus_nondegenerate(
                    cstr_spec[ci], execute_plan(full_plan.take(si as int)),
                    step_target(full_plan[si])));

            // Combine proved + assumed conjuncts into plan_structurally_sound
            assert(plan_structurally_sound::<R>(full_plan, cstr_spec));

            // === Phase A: Prove verification constraint satisfaction ===

            // Helper facts about initial steps
            lemma_initial_steps_execute_in_ext::<R>(pts_spec, initial_flags@);
            lemma_initial_steps_targets_bounded(pts_spec, initial_flags@);

            // Key precondition: ext_points matches execute_step_in_ext at every
            // full_plan target. Split into initial steps vs solver steps.
            assert forall|k: int| 0 <= k < full_plan.len()
            implies
                ext_points@[step_target(#[trigger] full_plan[k]) as int]@
                    == execute_step_in_ext::<RationalModel, R>(full_plan[k])
            by {
                if k < init_len {
                    // Initial step: full_plan[k] == init_steps[k]
                    assert(full_plan[k] == init_steps[k]);
                    let target = step_target(init_steps[k]);
                    let target_int: int = target as int;

                    // Show target is NOT overwritten by any solver result
                    assert forall|j: int| 0 <= j < results@.len()
                    implies (#[trigger] results@[j]).entity_id() != target as nat
                    by {
                        let si = init_len + j;
                        assert(full_plan[si] == plan_spec[j]);
                        // results[j].entity_id() == step_target(plan_spec[j])
                        //   == step_target(full_plan[si])
                        // distinct_targets: step_target(full_plan[k]) != step_target(full_plan[si])
                    }

                    // A3 non-overwritten: ext_points[target]@ == lift_point2(initial_points[target]@)
                    assert(ext_points@[target_int]@
                        == lift_point2::<RationalModel, R>(initial_points@[target_int]@));

                    // execute_step_in_ext(init_steps[k]) == lift_point2(pts_spec[target])
                    // pts_spec[target] == initial_points@[target]@ (by Seq::new in points_view)
                    assert(pts_spec[target_int] == initial_points@[target_int]@);
                } else {
                    // Solver step: full_plan[k] == plan_spec[k - init_len]
                    let j = k - init_len;
                    assert(full_plan[k] == plan_spec[j]);

                    // plan_spec[j] == variants@[vi]@[j].spec_step()
                    assert(plan_spec[j] == variants@[vi as int]@[j].spec_step());

                    // A2: results[j].entity_id() == step_target(plan_spec[j])
                    assert(results@[j].entity_id()
                        == step_target(variants@[vi as int]@[j].spec_step()));
                    assert(results@[j].entity_id() == step_target(plan_spec[j]));

                    // A2: results[j].ext_point_value() == execute_step_in_ext(plan_spec[j])
                    assert(results@[j].ext_point_value()
                        == execute_step_in_ext::<RationalModel, R>(plan_spec[j]));

                    // A3 overwritten: ext_points[entity_id]@ == results[j].ext_point_value()
                    assert(ext_points@[results@[j].entity_id() as int]@
                        == results@[j].ext_point_value());
                }
            }

            // All targets < ext_points.len()
            assert forall|k: int| 0 <= k < full_plan.len()
            implies (step_target(#[trigger] full_plan[k]) as int) < ext_points@.len()
            by {
                if k < init_len {
                    assert(full_plan[k] == init_steps[k]);
                } else {
                    let j = k - init_len;
                    assert(full_plan[k] == plan_spec[j]);
                    // step_target(variants@[vi]@[j].spec_step()) < n_points (from invariant)
                }
            }

            // Agreement: ext_vec_to_resolved_map agrees with execute_plan_in_ext
            lemma_ext_vec_agrees_with_plan::<R>(ext_points@, full_plan);

            // Domain equivalence for entity coverage
            lemma_execute_plan_in_ext_domain::<RationalModel, R>(full_plan);

            // Transfer: A5 gives satisfaction against ext_vec_to_resolved_map.
            // Map agreement + entity coverage lets us transfer to execute_plan_in_ext.
            assert forall|ci: int| 0 <= ci < cstr_spec.len()
                && is_verification_constraint(#[trigger] cstr_spec[ci])
            implies constraint_satisfied(
                lift_constraint::<RationalModel, R>(cstr_spec[ci]),
                execute_plan_in_ext::<RationalModel, R>(full_plan))
            by {
                // cstr_spec[ci] == runtime_constraint_model(constraints@[ci])
                assert(cstr_spec[ci] == runtime_constraint_model(constraints@[ci]));
                // A5: constraint_satisfied(..., ext_vec_to_resolved_map(ext_points@))
                // plan_structurally_sound: entity coverage => all entities in execute_plan.dom()
                // domain lemma: execute_plan_in_ext.dom() == execute_plan.dom()
                // agreement: on execute_plan_in_ext domain, maps agree
                lemma_verification_constraint_transfer::<R>(
                    cstr_spec[ci],
                    ext_vec_to_resolved_map::<R>(ext_points@),
                    execute_plan_in_ext::<RationalModel, R>(full_plan),
                );
            }

            // Formal bridge: derives ALL constraints satisfied
            lemma_solver_to_soundness_det::<R>(full_plan, cstr_spec);
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
