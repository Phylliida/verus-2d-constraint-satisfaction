use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::runtime::point2::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use verus_quadratic_extension::radicand::PositiveRadicand;
use verus_quadratic_extension::runtime::RuntimeRadicand;
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
//  Pipeline: solve_and_verify
// ===========================================================================

/// A verified solution: the plan, execution results, and ghost constraints.
/// When `soundness_certified()` holds, all constraints are provably satisfied.
pub struct VerifiedSolution<R: PositiveRadicand<RationalModel>> {
    pub plan: Vec<RuntimeStepData>,
    pub results: Vec<RuntimeConstructionResult<R>>,
    pub ghost_constraints: Ghost<Seq<Constraint<RationalModel>>>,
}

} // verus!
