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
use verus_quadratic_extension::instances::{Sqrt2, Sqrt3, Sqrt5, Sqrt6, Sqrt7, Sqrt10, Sqrt11, Sqrt13};
use verus_quadratic_extension::runtime::{RuntimeSqrt2, RuntimeSqrt3, RuntimeSqrt5, RuntimeSqrt6, RuntimeSqrt7, RuntimeSqrt10, RuntimeSqrt11, RuntimeSqrt13};
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
use crate::runtime::pipeline_proofs::*;
use crate::runtime::abstract_plan::{extract_abstract_plan, compute_step_levels, extract_constraint_pairs};
use crate::runtime::dyn_pipeline::{execute_all_levels_dyn, check_all_constraints_dyn, extract_rational_points_dyn, constraint_satisfied_dts, all_dyn_points_wf, DynRtPoint2, wrap_rationals_as_dyn};

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

/// Converse of lemma_initial_steps_flags_true: if flags[id] == true, then id
/// is a target of some initial step. Together with the forward direction, this
/// gives: flags[id] <==> id is an init step target.
proof fn lemma_initial_steps_cover_flags(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
    id: nat,
)
    requires
        points.len() == flags.len(),
        (id as int) < points.len(),
        flags[id as int],
    ensures
        exists|i: int| 0 <= i < initial_point_steps(points, flags).len()
            && step_target(initial_point_steps(points, flags)[i]) == id,
    decreases points.len(),
{
    let n = (points.len() - 1) as int;
    let full = initial_point_steps(points, flags);
    let prefix = initial_point_steps(points.take(n), flags.take(n));

    if id as int == n {
        // flags[n] == true, so full = prefix.push(PointStep { id: n, ... })
        // The last step has target n == id
        assert(full == prefix.push(ConstructionStep::PointStep {
            id: n as nat, position: points[n],
        }));
        let last = full.len() - 1;
        assert(step_target(full[last]) == id);
    } else {
        // id < n, recurse on prefix
        assert(flags.take(n)[id as int] == flags[id as int]);
        lemma_initial_steps_cover_flags(points.take(n), flags.take(n), id);
        let i = choose|i: int| 0 <= i < prefix.len()
            && step_target(prefix[i]) == id;
        if flags[n] {
            // full = prefix.push(...)  → full[i] == prefix[i]
            assert(full[i] == prefix[i]);
        } else {
            // full == prefix (no new step added)
            assert(full =~= prefix);
        }
        assert(step_target(full[i]) == id);
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

/// Runtime check: every constraint entity is either resolved (initial_flags)
/// or a solver step target. Ensures entity coverage for the full plan.
fn check_entity_coverage_exec(
    plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    initial_flags: &Vec<bool>,
) -> (out: bool)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < plan@.len() ==>
            (step_target((#[trigger] plan@[i]).spec_step()) as int) < initial_flags@.len(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], initial_flags@.len() as nat),
    ensures
        out ==> forall|ci: int| 0 <= ci < constraints@.len() ==>
            forall|id: EntityId|
                constraint_entities(
                    runtime_constraint_model(#[trigger] constraints@[ci])).contains(id) ==>
                ((id as int) < initial_flags@.len() && (
                    initial_flags@[id as int]
                    || exists|j: int| 0 <= j < plan@.len()
                        && step_target(plan@[j].spec_step()) == id
                )),
{
    let n = initial_flags.len();

    // Build coverage vector: starts as copy of initial_flags
    let mut covered: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == initial_flags@.len(),
            covered@.len() == i as int,
            forall|k: int| 0 <= k < i ==> #[trigger] covered@[k] == initial_flags@[k],
        decreases n - i,
    {
        covered.push(initial_flags[i]);
        i = i + 1;
    }

    // Mark all solver step targets as covered
    let mut j: usize = 0;
    while j < plan.len()
        invariant
            j <= plan@.len(),
            covered@.len() == n as int,
            forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
            forall|i: int| 0 <= i < plan@.len() ==>
                (step_target((#[trigger] plan@[i]).spec_step()) as int) < n,
            // Every covered entry is justified
            forall|k: int| 0 <= k < n ==>
                #[trigger] covered@[k] ==> (
                    initial_flags@[k]
                    || exists|jj: int| 0 <= jj < j
                        && step_target(plan@[jj].spec_step()) == k as nat),
            // All step targets so far are covered
            forall|jj: int| 0 <= jj < j ==>
                covered@[step_target(plan@[jj].spec_step()) as int],
        decreases plan@.len() - j,
    {
        let target = plan[j].target_id();
        let mut old_val = true;
        covered.set_and_swap(target, &mut old_val);
        proof {
            // The new covered[target] is justified by step j
            assert(step_target(plan@[j as int].spec_step()) == target as nat);
        }
        j = j + 1;
    }

    // Check all constraint entities are covered
    let mut ci: usize = 0;
    while ci < constraints.len()
        invariant
            ci <= constraints@.len(),
            covered@.len() == n as int,
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n as nat),
            forall|k: int| 0 <= k < n ==>
                #[trigger] covered@[k] ==> (
                    initial_flags@[k]
                    || exists|jj: int| 0 <= jj < plan@.len()
                        && step_target(plan@[jj].spec_step()) == k as nat),
            // All constraints checked so far have coverage
            forall|ci2: int| 0 <= ci2 < ci ==>
                forall|id: EntityId|
                    constraint_entities(
                        runtime_constraint_model(#[trigger] constraints@[ci2])).contains(id) ==>
                    ((id as int) < n && (
                        initial_flags@[id as int]
                        || exists|j: int| 0 <= j < plan@.len()
                            && step_target(plan@[j].spec_step()) == id
                    )),
        decreases constraints@.len() - ci,
    {
        let ids = constraint_entity_ids(&constraints[ci], n);
        let mut k: usize = 0;
        while k < ids.len()
            invariant
                k <= ids@.len(),
                covered@.len() == n as int,
                forall|j: int| 0 <= j < ids@.len() ==>
                    constraint_entities(runtime_constraint_model(constraints@[ci as int]))
                        .contains(#[trigger] ids@[j] as nat),
                forall|j: int| 0 <= j < ids@.len() ==>
                    (#[trigger] ids@[j] as int) < n,
                forall|kk: int| 0 <= kk < n ==>
                    #[trigger] covered@[kk] ==> (
                        initial_flags@[kk]
                        || exists|jj: int| 0 <= jj < plan@.len()
                            && step_target(plan@[jj].spec_step()) == kk as nat),
                // All checked entity IDs so far are covered
                forall|j: int| 0 <= j < k ==>
                    covered@[ids@[j] as int],
            decreases ids@.len() - k,
        {
            if !covered[ids[k]] {
                return false;
            }
            k = k + 1;
        }
        // Now we know all entity IDs in the Vec are covered.
        // Transfer from Vec coverage to constraint_entities coverage.
        proof {
            assert forall|id: EntityId|
                constraint_entities(
                    runtime_constraint_model(constraints@[ci as int])).contains(id)
            implies
                ((id as int) < n && (
                    initial_flags@[id as int]
                    || exists|j: int| 0 <= j < plan@.len()
                        && step_target(plan@[j].spec_step()) == id
                ))
            by {
                // constraint_entity_ids backward: e ∈ constraint_entities → exists j, ids[j] == e
                let j = choose|j: int| 0 <= j < ids@.len() && ids@[j] as nat == id;
                // covered[ids[j]] == true → covered[id] == true
                assert(covered@[ids@[j] as int]);
            }
        }
        ci = ci + 1;
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
    /// Ghost full plan (initial PointSteps + solver steps) for the soundness theorem.
    pub ghost_full_plan: Ghost<ConstructionPlan<RationalModel>>,
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
    /// Ghost: number of constraints verified at the extension level.
    /// When this equals the input constraint count, all constraints were satisfied.
    pub ghost_n_constraints_verified: Ghost<nat>,
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
    ensures
        out.ghost_n_constraints_verified@ == solution.ghost_constraints@.len(),
{
    let plan = copy_plan(&solution.plan);
    let points_re = extract_rational_parts(&solution.ext_points);
    let ghost n = solution.ghost_constraints@.len();
    SolvedPoints { plan, points_re, ghost_n_constraints_verified: Ghost(n) }
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

/// Transfer constraint_satisfied for a Tangent constraint.
proof fn lemma_transfer_tangent<R: PositiveRadicand<RationalModel>>(
    line_a: EntityId, line_b: EntityId, center: EntityId, radius_point: EntityId,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::Tangent { line_a, line_b, center, radius_point }), resolved1),
        resolved2.dom().contains(line_a) && resolved1[line_a] == resolved2[line_a],
        resolved2.dom().contains(line_b) && resolved1[line_b] == resolved2[line_b],
        resolved2.dom().contains(center) && resolved1[center] == resolved2[center],
        resolved2.dom().contains(radius_point) && resolved1[radius_point] == resolved2[radius_point],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::Tangent { line_a, line_b, center, radius_point }), resolved2),
{}

/// Transfer constraint_satisfied for a CircleTangent constraint.
proof fn lemma_transfer_circle_tangent<R: PositiveRadicand<RationalModel>>(
    c1: EntityId, rp1: EntityId, c2: EntityId, rp2: EntityId,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::CircleTangent { c1, rp1, c2, rp2 }), resolved1),
        resolved2.dom().contains(c1) && resolved1[c1] == resolved2[c1],
        resolved2.dom().contains(rp1) && resolved1[rp1] == resolved2[rp1],
        resolved2.dom().contains(c2) && resolved1[c2] == resolved2[c2],
        resolved2.dom().contains(rp2) && resolved1[rp2] == resolved2[rp2],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::CircleTangent { c1, rp1, c2, rp2 }), resolved2),
{}

/// Transfer constraint_satisfied for an Angle constraint.
proof fn lemma_transfer_angle<R: PositiveRadicand<RationalModel>>(
    a1: EntityId, a2: EntityId, b1: EntityId, b2: EntityId, cos_sq: RationalModel,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::Angle { a1, a2, b1, b2, cos_sq }), resolved1),
        resolved2.dom().contains(a1) && resolved1[a1] == resolved2[a1],
        resolved2.dom().contains(a2) && resolved1[a2] == resolved2[a2],
        resolved2.dom().contains(b1) && resolved1[b1] == resolved2[b1],
        resolved2.dom().contains(b2) && resolved1[b2] == resolved2[b2],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::Angle { a1, a2, b1, b2, cos_sq }), resolved2),
{}

/// Transfer constraint_satisfied for a NotCoincident constraint.
proof fn lemma_transfer_not_coincident<R: PositiveRadicand<RationalModel>>(
    a: EntityId, b: EntityId,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::NotCoincident { a, b }), resolved1),
        resolved2.dom().contains(a) && resolved1[a] == resolved2[a],
        resolved2.dom().contains(b) && resolved1[b] == resolved2[b],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::NotCoincident { a, b }), resolved2),
{}

/// Transfer constraint_satisfied for a NormalToCircle constraint.
proof fn lemma_transfer_normal_to_circle<R: PositiveRadicand<RationalModel>>(
    line_a: EntityId, line_b: EntityId, center: EntityId, radius_point: EntityId,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::NormalToCircle { line_a, line_b, center, radius_point }), resolved1),
        resolved2.dom().contains(line_a) && resolved1[line_a] == resolved2[line_a],
        resolved2.dom().contains(line_b) && resolved1[line_b] == resolved2[line_b],
        resolved2.dom().contains(center) && resolved1[center] == resolved2[center],
        resolved2.dom().contains(radius_point) && resolved1[radius_point] == resolved2[radius_point],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::NormalToCircle { line_a, line_b, center, radius_point }), resolved2),
{}

/// Transfer constraint_satisfied for a PointOnEllipse constraint.
proof fn lemma_transfer_point_on_ellipse<R: PositiveRadicand<RationalModel>>(
    point: EntityId, center: EntityId, semi_a: EntityId, semi_b: EntityId,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::PointOnEllipse { point, center, semi_a, semi_b }), resolved1),
        resolved2.dom().contains(point) && resolved1[point] == resolved2[point],
        resolved2.dom().contains(center) && resolved1[center] == resolved2[center],
        resolved2.dom().contains(semi_a) && resolved1[semi_a] == resolved2[semi_a],
        resolved2.dom().contains(semi_b) && resolved1[semi_b] == resolved2[semi_b],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::PointOnEllipse { point, center, semi_a, semi_b }), resolved2),
{}

/// Transfer constraint_satisfied for a PointOnArc constraint.
proof fn lemma_transfer_point_on_arc<R: PositiveRadicand<RationalModel>>(
    point: EntityId, center: EntityId, radius_point: EntityId,
    arc_start: EntityId, arc_end: EntityId,
    resolved1: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
    resolved2: ResolvedPoints<SpecQuadExt<RationalModel, R>>,
)
    requires
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::PointOnArc { point, center, radius_point, arc_start, arc_end }), resolved1),
        resolved2.dom().contains(point) && resolved1[point] == resolved2[point],
        resolved2.dom().contains(center) && resolved1[center] == resolved2[center],
        resolved2.dom().contains(radius_point) && resolved1[radius_point] == resolved2[radius_point],
        resolved2.dom().contains(arc_start) && resolved1[arc_start] == resolved2[arc_start],
        resolved2.dom().contains(arc_end) && resolved1[arc_end] == resolved2[arc_end],
    ensures
        constraint_satisfied(lift_constraint::<RationalModel, R>(
            Constraint::PointOnArc { point, center, radius_point, arc_start, arc_end }), resolved2),
{}

/// Transfer constraint_satisfied for verification constraints between
/// two resolved maps that agree on all constraint entity IDs.
#[verifier::rlimit(40)]
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
    match c {
        Constraint::Tangent { line_a, line_b, center, radius_point } => {
            assert(constraint_entities(c).contains(line_a));
            assert(constraint_entities(c).contains(line_b));
            assert(constraint_entities(c).contains(center));
            assert(constraint_entities(c).contains(radius_point));
            lemma_transfer_tangent::<R>(line_a, line_b, center, radius_point, resolved1, resolved2);
        }
        Constraint::CircleTangent { c1, rp1, c2, rp2 } => {
            assert(constraint_entities(c).contains(c1));
            assert(constraint_entities(c).contains(rp1));
            assert(constraint_entities(c).contains(c2));
            assert(constraint_entities(c).contains(rp2));
            lemma_transfer_circle_tangent::<R>(c1, rp1, c2, rp2, resolved1, resolved2);
        }
        Constraint::Angle { a1, a2, b1, b2, cos_sq } => {
            assert(constraint_entities(c).contains(a1));
            assert(constraint_entities(c).contains(a2));
            assert(constraint_entities(c).contains(b1));
            assert(constraint_entities(c).contains(b2));
            lemma_transfer_angle::<R>(a1, a2, b1, b2, cos_sq, resolved1, resolved2);
        }
        Constraint::NotCoincident { a, b } => {
            assert(constraint_entities(c).contains(a));
            assert(constraint_entities(c).contains(b));
            lemma_transfer_not_coincident::<R>(a, b, resolved1, resolved2);
        }
        Constraint::NormalToCircle { line_a, line_b, center, radius_point } => {
            assert(constraint_entities(c).contains(line_a));
            assert(constraint_entities(c).contains(line_b));
            assert(constraint_entities(c).contains(center));
            assert(constraint_entities(c).contains(radius_point));
            lemma_transfer_normal_to_circle::<R>(line_a, line_b, center, radius_point, resolved1, resolved2);
        }
        Constraint::PointOnEllipse { point, center, semi_a, semi_b } => {
            assert(constraint_entities(c).contains(point));
            assert(constraint_entities(c).contains(center));
            assert(constraint_entities(c).contains(semi_a));
            assert(constraint_entities(c).contains(semi_b));
            lemma_transfer_point_on_ellipse::<R>(point, center, semi_a, semi_b, resolved1, resolved2);
        }
        Constraint::PointOnArc { point, center, radius_point, arc_start, arc_end } => {
            assert(constraint_entities(c).contains(point));
            assert(constraint_entities(c).contains(center));
            assert(constraint_entities(c).contains(radius_point));
            assert(constraint_entities(c).contains(arc_start));
            assert(constraint_entities(c).contains(arc_end));
            lemma_transfer_point_on_arc::<R>(point, center, radius_point, arc_start, arc_end, resolved1, resolved2);
        }
        _ => {
            assert(!is_verification_constraint(c));
        }
    }
}

/// Try to verify a single plan variant. Returns Some(solution) if all checks pass.
fn verify_single_variant<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    variant: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    initial_points: &Vec<RuntimePoint2>,
    initial_flags: &Vec<bool>,
) -> (out: Option<VerifiedSolution<R>>)
    requires
        initial_points@.len() == initial_flags@.len(),
        all_points_wf(initial_points@),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], initial_points@.len() as nat),
        forall|i: int| 0 <= i < initial_flags@.len() ==>
            (#[trigger] initial_flags@[i]) ==
            partial_resolved_map(points_view(initial_points@), initial_flags@)
                .dom().contains(i as nat),
        forall|j: int| 0 <= j < variant@.len() ==>
            (#[trigger] variant@[j]).wf_spec(),
        forall|i: int, j: int|
            0 <= i < variant@.len() && 0 <= j < variant@.len() && i != j ==>
            step_target(#[trigger] variant@[i].spec_step()) !=
            step_target(#[trigger] variant@[j].spec_step()),
        forall|j: int| 0 <= j < variant@.len() ==>
            step_has_positive_discriminant((#[trigger] variant@[j]).spec_step()),
        forall|j: int| 0 <= j < variant@.len() ==>
            (step_target((#[trigger] variant@[j]).spec_step()) as int)
                < initial_points@.len(),
        forall|j: int| 0 <= j < variant@.len() ==>
            step_geometrically_valid((#[trigger] variant@[j]).spec_step()),
    ensures
        out.is_some() ==> {
            let sol = out.unwrap();
            &&& forall|i: int| 0 <= i < sol.ext_points@.len() ==>
                    (#[trigger] sol.ext_points@[i]).wf_spec()
            &&& forall|j: int| 0 <= j < sol.plan@.len() ==>
                    (#[trigger] sol.plan@[j]).wf_spec()
            &&& sol.ghost_constraints@ == constraints_to_spec(constraints@)
            &&& forall|ci: int| 0 <= ci < sol.ghost_constraints@.len() ==>
                    constraint_satisfied(
                        #[trigger] lift_constraints::<RationalModel, R>(sol.ghost_constraints@)[ci],
                        execute_plan_in_ext::<RationalModel, R>(sol.ghost_full_plan@))
            // The runtime ext_points agree with the spec-level deterministic execution.
            &&& forall|id: EntityId|
                    execute_plan_in_ext::<RationalModel, R>(sol.ghost_full_plan@).dom().contains(id) ==>
                    ext_vec_to_resolved_map::<R>(sol.ext_points@)[id]
                        == execute_plan_in_ext::<RationalModel, R>(sol.ghost_full_plan@)[id]
        },
{
    let n_points = initial_points.len();

    // Step 1: Runtime plan soundness check
    let sound = verify_plan_soundness_exec::<R, RR>(
        variant, constraints, n_points,
    );
    if !sound { return None; }

    // Step 1b: Check solver targets are unresolved
    let targets_unresolved = check_solver_targets_unresolved(variant, initial_flags);
    if !targets_unresolved { return None; }

    // Step 1c: Check entity coverage
    let coverage_ok = check_entity_coverage_exec(variant, constraints, initial_flags);
    if !coverage_ok { return None; }

    // Step 1d: Build full plan at runtime and check locus ordering
    let full_plan_runtime = build_full_plan_runtime(initial_points, initial_flags, variant);
    let locus_ordered = check_plan_locus_ordered_exec(
        &full_plan_runtime, constraints, n_points,
    );
    if !locus_ordered { return None; }

    // Step 1e: Check dynamic conjuncts 9-12 via full plan replay
    if n_points == 0 { return None; }

    // Establish preconditions for check_full_plan_dynamic_conjuncts_exec
    // by proving facts about full_plan_runtime via its spec correspondence
    let ghost plan_spec = plan_to_spec(variant@);
    let ghost cstr_spec = constraints_to_spec(constraints@);
    let ghost pts_spec = points_view(initial_points@);
    let ghost full_plan = build_full_plan(pts_spec, initial_flags@, plan_spec);
    let ghost init_steps = initial_point_steps(pts_spec, initial_flags@);
    let ghost init_len = init_steps.len() as int;

    proof {
        // full_plan_runtime spec correspondence
        assert(plan_to_spec(full_plan_runtime@) =~= full_plan);

        // Conjunct 1: distinct_targets for full_plan_runtime
        lemma_initial_steps_distinct_targets(pts_spec, initial_flags@);
        lemma_initial_steps_flags_true(pts_spec, initial_flags@);
        lemma_initial_steps_targets_bounded(pts_spec, initial_flags@);
        assert forall|i: int, j: int|
            0 <= i < full_plan_runtime@.len() && 0 <= j < full_plan_runtime@.len() && i != j
        implies step_target(full_plan_runtime@[i].spec_step())
            != step_target(full_plan_runtime@[j].spec_step())
        by {
            assert(full_plan_runtime@[i].spec_step() == full_plan[i]);
            assert(full_plan_runtime@[j].spec_step() == full_plan[j]);
            if i < init_len && j < init_len {
                assert(full_plan[i] == init_steps[i]);
                assert(full_plan[j] == init_steps[j]);
            } else if i >= init_len && j >= init_len {
                assert(full_plan[i] == plan_spec[i - init_len]);
                assert(full_plan[j] == plan_spec[j - init_len]);
                assert(plan_spec[i - init_len] == variant@[i - init_len].spec_step());
                assert(plan_spec[j - init_len] == variant@[j - init_len].spec_step());
            } else {
                let (init_idx, solver_idx) = if i < init_len {
                    (i, j - init_len)
                } else {
                    (j, i - init_len)
                };
                assert(full_plan[init_idx] == init_steps[init_idx]);
                let solver_step = plan_spec[solver_idx];
                assert(solver_step == variant@[solver_idx].spec_step());
            }
        }

        // Conjuncts 6, 7, 8: geometrically valid, positive discriminant, radicand matches
        lemma_initial_steps_trivial_properties::<R>(pts_spec, initial_flags@);
        assert forall|i: int| 0 <= i < full_plan_runtime@.len()
        implies step_geometrically_valid((#[trigger] full_plan_runtime@[i]).spec_step())
        by {
            assert(full_plan_runtime@[i].spec_step() == full_plan[i]);
            if i < init_len {
                assert(full_plan[i] == init_steps[i]);
            } else {
                assert(full_plan[i] == plan_spec[i - init_len]);
                assert(plan_spec[i - init_len] == variant@[i - init_len].spec_step());
            }
        }

        // Conjunct 5: is_fully_independent_plan for full_plan_runtime
        lemma_initial_steps_are_rational(pts_spec, initial_flags@);
        assert forall|j: int| 0 <= j < plan_spec.len()
        implies !(#[trigger] initial_flags@[step_target(plan_spec[j]) as int])
        by {
            assert(plan_spec[j] == variant@[j].spec_step());
        }
        lemma_full_plan_independent(pts_spec, initial_flags@, plan_spec, cstr_spec);
        // Transfer: plan_to_spec(full_plan_runtime@) =~= full_plan, so independence holds
        assert(is_fully_independent_plan(
            plan_to_spec(full_plan_runtime@), constraints_to_spec(constraints@)));
    }

    let dynamic_ok = check_full_plan_dynamic_conjuncts_exec(
        &full_plan_runtime, constraints, n_points);
    if !dynamic_ok { return None; }

    // Step 2: Execute the solver plan to get results
    let results = execute_plan_runtime::<R>(variant);

    // Step 3: Build extension-level resolved points and check verification constraints
    let ext_points = build_ext_resolved_vec::<R, RR>(
        &results, variant, initial_points,
    );
    let ext_ok = check_all_verification_constraints_ext::<R, RR>(
        constraints, &ext_points, n_points,
    );
    if !ext_ok { return None; }

    // Step 3b: Formal bridge — all constraints satisfied at extension level.
    proof {
        // Conjuncts 9-12: from check_full_plan_dynamic_conjuncts_exec ensures
        // plan_to_spec(full_plan_runtime@) =~= full_plan, so results transfer
        let fp_spec = plan_to_spec(full_plan_runtime@);
        let cs_spec = constraints_to_spec(constraints@);
        assert(fp_spec =~= full_plan);
        assert(cs_spec =~= cstr_spec);

        // Conjuncts 6, 7, 8 for spec full_plan (needed for plan_structurally_sound)
        lemma_initial_steps_trivial_properties::<R>(pts_spec, initial_flags@);
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
                assert(plan_spec[j - init_len] == variant@[j - init_len].spec_step());
            }
        }

        // Distinct targets for spec full_plan
        assert forall|i: int, j: int|
            0 <= i < full_plan.len() && 0 <= j < full_plan.len() && i != j
        implies step_target(full_plan[i]) != step_target(full_plan[j])
        by {
            assert(full_plan[i] == fp_spec[i]);
            assert(full_plan[j] == fp_spec[j]);
        }

        // Conjunct 5: independence for spec full_plan
        assert(is_fully_independent_plan(full_plan, cstr_spec));

        // === Prove conjunct 3: entity coverage ===
        assert forall|ci: int| 0 <= ci < cstr_spec.len()
        implies constraint_entities(#[trigger] cstr_spec[ci])
            .subset_of(execute_plan(full_plan).dom())
        by {
            assert forall|id: EntityId|
                constraint_entities(cstr_spec[ci]).contains(id)
            implies execute_plan(full_plan).dom().contains(id)
            by {
                assert(cstr_spec[ci] == runtime_constraint_model(constraints@[ci as int]));
                if initial_flags@[id as int] {
                    lemma_initial_steps_cover_flags(pts_spec, initial_flags@, id);
                    let i = choose|i: int| 0 <= i < init_steps.len()
                        && step_target(init_steps[i]) == id;
                    assert(full_plan[i] == init_steps[i]);
                    lemma_execute_plan_dom::<RationalModel>(full_plan, id);
                } else {
                    let j = choose|j: int| 0 <= j < variant@.len()
                        && step_target(variant@[j].spec_step()) == id;
                    assert(plan_spec[j] == variant@[j].spec_step());
                    assert(full_plan[init_len + j] == plan_spec[j]);
                    lemma_execute_plan_dom::<RationalModel>(full_plan, id);
                }
            }
        }

        // Conjunct 4: plan_locus_ordered (from runtime check on full_plan_runtime)
        assert(plan_locus_ordered(full_plan, cstr_spec));

        // Assert sub-predicates in stages to help Z3
        assert(plan_valid_structure(full_plan, cstr_spec));
        assert(plan_independence(full_plan, cstr_spec));
        assert(plan_geometric_validity::<R>(full_plan));
        assert(plan_dynamic_satisfaction(full_plan, cstr_spec));
        assert(plan_structurally_sound::<R>(full_plan, cstr_spec));

        // === Phase A: Prove verification constraint satisfaction ===
        lemma_initial_steps_execute_in_ext::<R>(pts_spec, initial_flags@);
        lemma_initial_steps_targets_bounded(pts_spec, initial_flags@);

        assert forall|k: int| 0 <= k < full_plan.len()
        implies
            ext_points@[step_target(#[trigger] full_plan[k]) as int]@
                == execute_step_in_ext::<RationalModel, R>(full_plan[k])
        by {
            if k < init_len {
                assert(full_plan[k] == init_steps[k]);
                let target = step_target(init_steps[k]);
                let target_int: int = target as int;
                assert forall|j: int| 0 <= j < results@.len()
                implies (#[trigger] results@[j]).entity_id() != target as nat
                by {
                    let si = init_len + j;
                    assert(full_plan[si] == plan_spec[j]);
                }
                assert(ext_points@[target_int]@
                    == lift_point2::<RationalModel, R>(initial_points@[target_int]@));
                assert(pts_spec[target_int] == initial_points@[target_int]@);
            } else {
                let j = k - init_len;
                assert(full_plan[k] == plan_spec[j]);
                assert(plan_spec[j] == variant@[j].spec_step());
                assert(results@[j].entity_id()
                    == step_target(variant@[j].spec_step()));
                assert(results@[j].entity_id() == step_target(plan_spec[j]));
                assert(results@[j].ext_point_value()
                    == execute_step_in_ext::<RationalModel, R>(plan_spec[j]));
                assert(ext_points@[results@[j].entity_id() as int]@
                    == results@[j].ext_point_value());
            }
        }

        assert forall|k: int| 0 <= k < full_plan.len()
        implies (step_target(#[trigger] full_plan[k]) as int) < ext_points@.len()
        by {
            if k < init_len {
                assert(full_plan[k] == init_steps[k]);
            } else {
                let j = k - init_len;
                assert(full_plan[k] == plan_spec[j]);
            }
        }

        lemma_ext_vec_agrees_with_plan::<R>(ext_points@, full_plan);
        lemma_execute_plan_in_ext_domain::<RationalModel, R>(full_plan);

        assert forall|ci: int| 0 <= ci < cstr_spec.len()
            && is_verification_constraint(#[trigger] cstr_spec[ci])
        implies constraint_satisfied(
            lift_constraint::<RationalModel, R>(cstr_spec[ci]),
            execute_plan_in_ext::<RationalModel, R>(full_plan))
        by {
            assert(cstr_spec[ci] == runtime_constraint_model(constraints@[ci]));
            lemma_verification_constraint_transfer::<R>(
                cstr_spec[ci],
                ext_vec_to_resolved_map::<R>(ext_points@),
                execute_plan_in_ext::<RationalModel, R>(full_plan),
            );
        }

        lemma_solver_to_soundness_det::<R>(full_plan, cstr_spec);
    }

    // Package into VerifiedSolution
    let ghost cstr_spec = constraints_to_spec(constraints@);
    let solution = VerifiedSolution {
        plan: copy_plan(variant),
        results,
        ext_points,
        ghost_constraints: Ghost(cstr_spec),
        ghost_full_plan: Ghost(full_plan),
    };
    Some(solution)
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
        forall|si: int| 0 <= si < out@.len() ==>
            (#[trigger] out@[si]).ghost_constraints@ == constraints_to_spec(constraints@),
        forall|si: int| 0 <= si < out@.len() ==>
            forall|ci: int| 0 <= ci < (#[trigger] out@[si]).ghost_constraints@.len() ==>
                constraint_satisfied(
                    #[trigger] lift_constraints::<RationalModel, R>(out@[si].ghost_constraints@)[ci],
                    execute_plan_in_ext::<RationalModel, R>(out@[si].ghost_full_plan@)),
        forall|si: int| 0 <= si < out@.len() ==>
            forall|id: EntityId|
                execute_plan_in_ext::<RationalModel, R>((#[trigger] out@[si]).ghost_full_plan@).dom().contains(id) ==>
                ext_vec_to_resolved_map::<R>(out@[si].ext_points@)[id]
                    == execute_plan_in_ext::<RationalModel, R>(out@[si].ghost_full_plan@)[id],
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
            // Ghost constraints match input
            forall|si: int| 0 <= si < solutions@.len() ==>
                (#[trigger] solutions@[si]).ghost_constraints@ == constraints_to_spec(constraints@),
            // All constraints satisfied at extension level
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|ci: int| 0 <= ci < (#[trigger] solutions@[si]).ghost_constraints@.len() ==>
                    constraint_satisfied(
                        #[trigger] lift_constraints::<RationalModel, R>(solutions@[si].ghost_constraints@)[ci],
                        execute_plan_in_ext::<RationalModel, R>(solutions@[si].ghost_full_plan@)),
            // Runtime ext_points agree with spec-level deterministic execution
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|id: EntityId|
                    execute_plan_in_ext::<RationalModel, R>((#[trigger] solutions@[si]).ghost_full_plan@).dom().contains(id) ==>
                    ext_vec_to_resolved_map::<R>(solutions@[si].ext_points@)[id]
                        == execute_plan_in_ext::<RationalModel, R>(solutions@[si].ghost_full_plan@)[id],
        decreases variants@.len() - vi,
    {
        let result = verify_single_variant::<R, RR>(
            &variants[vi], constraints, initial_points, initial_flags,
        );
        match result {
            Some(solution) => {
                solutions.push(solution);
            }
            None => {}
        }
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
    ensures
        // Every returned solution has all constraints satisfied at the extension level.
        forall|si: int| 0 <= si < out@.len() ==>
            (#[trigger] out@[si]).ghost_constraints@ == constraints_to_spec(constraints@),
        forall|si: int| 0 <= si < out@.len() ==>
            forall|ci: int| 0 <= ci < (#[trigger] out@[si]).ghost_constraints@.len() ==>
                constraint_satisfied(
                    #[trigger] lift_constraints::<RationalModel, R>(out@[si].ghost_constraints@)[ci],
                    execute_plan_in_ext::<RationalModel, R>(out@[si].ghost_full_plan@)),
        // The runtime ext_points agree with the spec-level deterministic execution.
        forall|si: int| 0 <= si < out@.len() ==>
            forall|id: EntityId|
                execute_plan_in_ext::<RationalModel, R>((#[trigger] out@[si]).ghost_full_plan@).dom().contains(id) ==>
                ext_vec_to_resolved_map::<R>(out@[si].ext_points@)[id]
                    == execute_plan_in_ext::<RationalModel, R>(out@[si].ghost_full_plan@)[id],
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

/// Helper: take(m).take(n) =~= take(n) for n <= m.
proof fn lemma_take_take<A>(s: Seq<A>, m: int, n: int)
    requires 0 <= n <= m <= s.len(),
    ensures s.take(m).take(n) =~= s.take(n),
{
    assert forall|k: int| 0 <= k < n implies
        s.take(m).take(n)[k] == s.take(n)[k]
    by {}
}

/// Helper: plan_to_spec distributes over concatenation.
proof fn lemma_plan_to_spec_concat(a: Seq<RuntimeStepData>, b: Seq<RuntimeStepData>)
    ensures plan_to_spec(a + b) =~= plan_to_spec(a) + plan_to_spec(b),
{
    let ab = a + b;
    let lhs = plan_to_spec(ab);
    let rhs = plan_to_spec(a) + plan_to_spec(b);
    assert forall|i: int| 0 <= i < lhs.len() implies lhs[i] == rhs[i]
    by {
        if i < a.len() as int {
            assert(ab[i] == a[i]);
            assert(lhs[i] == a[i].spec_step());
            assert(rhs[i] == plan_to_spec(a)[i]);
        } else {
            let j = i - a.len() as int;
            assert(ab[i] == b[j]);
            assert(lhs[i] == b[j].spec_step());
            assert(rhs[i] == plan_to_spec(b)[j]);
        }
    }
}

/// Build the full plan at runtime: init PointSteps for resolved entities,
/// followed by copies of the solver plan steps. Ensures spec correspondence
/// with build_full_plan.
fn build_full_plan_runtime(
    initial_points: &Vec<RuntimePoint2>,
    initial_flags: &Vec<bool>,
    solver_plan: &Vec<RuntimeStepData>,
) -> (out: Vec<RuntimeStepData>)
    requires
        initial_points@.len() == initial_flags@.len(),
        all_points_wf(initial_points@),
        forall|i: int| 0 <= i < solver_plan@.len() ==> (#[trigger] solver_plan@[i]).wf_spec(),
        forall|i: int| 0 <= i < solver_plan@.len() ==>
            (step_target((#[trigger] solver_plan@[i]).spec_step()) as int)
                < initial_points@.len(),
    ensures
        plan_to_spec(out@) =~= build_full_plan(
            points_view(initial_points@), initial_flags@,
            plan_to_spec(solver_plan@)),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==>
            (step_target((#[trigger] out@[i]).spec_step()) as int)
                < initial_points@.len(),
{
    let n = initial_points.len();
    let ghost pts_spec = points_view(initial_points@);

    // Phase 1: Build init steps for resolved entities
    let mut init_steps: Vec<RuntimeStepData> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == initial_points@.len(),
            n == initial_flags@.len(),
            pts_spec.len() == n as int,
            forall|k: int| 0 <= k < n as int ==>
                (#[trigger] pts_spec[k]) == initial_points@[k]@,
            all_points_wf(initial_points@),
            plan_to_spec(init_steps@) =~=
                initial_point_steps(pts_spec.take(i as int), initial_flags@.take(i as int)),
            forall|j: int| 0 <= j < init_steps@.len() ==>
                (#[trigger] init_steps@[j]).wf_spec(),
            forall|j: int| 0 <= j < init_steps@.len() ==>
                (step_target((#[trigger] init_steps@[j]).spec_step()) as int) < n,
        decreases n - i,
    {
        if initial_flags[i] {
            let x = copy_rational(&initial_points[i].x);
            let y = copy_rational(&initial_points[i].y);
            let step = RuntimeStepData::PointStep {
                target: i,
                x, y,
                model: Ghost(ConstructionStep::PointStep {
                    id: i as nat,
                    position: pts_spec[i as int],
                }),
            };
            proof {
                // wf_spec: x@/y@ match position via point wf + pts_spec[i] == initial_points@[i]@
                assert(initial_points@[i as int].wf_spec());
                assert(pts_spec[i as int] == initial_points@[i as int]@);
                assert(step.wf_spec());

                // Show plan_to_spec(init_steps@.push(step))
                //   == plan_to_spec(init_steps@).push(step.spec_step())
                let old_spec = plan_to_spec(init_steps@);
                let new_seq = init_steps@.push(step);
                assert forall|j: int| 0 <= j < plan_to_spec(new_seq).len()
                implies plan_to_spec(new_seq)[j] == (old_spec.push(step.spec_step()))[j]
                by {
                    if j < init_steps@.len() as int {
                        assert(new_seq[j] == init_steps@[j]);
                    }
                }
                assert(plan_to_spec(new_seq) =~= old_spec.push(step.spec_step()));

                // Help Z3 with take nesting: take(i+1).take(i) =~= take(i)
                lemma_take_take::<Point2<RationalModel>>(pts_spec, i as int + 1, i as int);
                lemma_take_take::<bool>(initial_flags@, i as int + 1, i as int);
            }
            init_steps.push(step);
        } else {
            proof {
                // flags[i] == false: initial_point_steps unchanged
                lemma_take_take::<Point2<RationalModel>>(pts_spec, i as int + 1, i as int);
                lemma_take_take::<bool>(initial_flags@, i as int + 1, i as int);
            }
        }
        i = i + 1;
    }

    proof {
        // At end of loop: i == n, so take(n) == full sequence
        assert(pts_spec.take(n as int) =~= pts_spec);
        assert(initial_flags@.take(n as int) =~= initial_flags@);
    }

    // Phase 2: Append solver plan copies
    let mut j: usize = 0;
    while j < solver_plan.len()
        invariant
            j <= solver_plan@.len(),
            n == initial_points@.len(),
            forall|k: int| 0 <= k < solver_plan@.len() ==>
                (#[trigger] solver_plan@[k]).wf_spec(),
            forall|k: int| 0 <= k < solver_plan@.len() ==>
                (step_target((#[trigger] solver_plan@[k]).spec_step()) as int) < n,
            // init_steps portion unchanged
            forall|k: int| 0 <= k < init_steps@.len() ==>
                (#[trigger] init_steps@[k]).wf_spec(),
            forall|k: int| 0 <= k < init_steps@.len() ==>
                (step_target((#[trigger] init_steps@[k]).spec_step()) as int) < n,
            plan_to_spec(init_steps@.take(
                (init_steps@.len() - j) as int)) =~=
                initial_point_steps(pts_spec, initial_flags@),
            // appended solver steps match
            init_steps@.len() >= j,
            forall|k: int|
                (init_steps@.len() - j) as int <= k < init_steps@.len() ==>
                (#[trigger] init_steps@[k]).spec_step()
                    == solver_plan@[k - (init_steps@.len() - j) as int].spec_step(),
        decreases solver_plan@.len() - j,
    {
        let step = copy_step(&solver_plan[j]);
        init_steps.push(step);
        j = j + 1;
    }

    proof {
        // Show plan_to_spec(init_steps@) =~= build_full_plan(...)
        let init_len = (init_steps@.len() - solver_plan@.len()) as int;
        let init_part = init_steps@.take(init_len);
        let solver_part = init_steps@.skip(init_len);

        // plan_to_spec distributes: plan_to_spec(init ++ solver) == plan_to_spec(init) ++ plan_to_spec(solver)
        assert(init_steps@ =~= init_part + solver_part);
        lemma_plan_to_spec_concat(init_part, solver_part);

        // plan_to_spec(init_part) =~= initial_point_steps(pts_spec, flags)
        // plan_to_spec(solver_part) =~= plan_to_spec(solver_plan@)
        assert forall|k: int| 0 <= k < solver_part.len()
        implies plan_to_spec(solver_part)[k] == plan_to_spec(solver_plan@)[k]
        by {
            assert(solver_part[k] == init_steps@[init_len + k]);
            assert(solver_part[k].spec_step() == solver_plan@[k].spec_step());
        }
        assert(plan_to_spec(solver_part) =~= plan_to_spec(solver_plan@));
    }

    init_steps
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
    let d6 = RuntimeRational::from_int(6);
    let d7 = RuntimeRational::from_int(7);
    let d10 = RuntimeRational::from_int(10);
    let d11 = RuntimeRational::from_int(11);
    let d13 = RuntimeRational::from_int(13);
    let mut found: u8 = 0; // 0 = none seen yet
    let mut i: usize = 0;

    while i < plan.len()
        invariant
            i <= plan@.len(),
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            d2.wf_spec(), d3.wf_spec(), d5.wf_spec(),
            d6.wf_spec(), d7.wf_spec(), d10.wf_spec(), d11.wf_spec(), d13.wf_spec(),
        decreases plan@.len() - i,
    {
        let disc_val: u8 = match &plan[i] {
            RuntimeStepData::CircleLine { circle, line, .. } => {
                let disc = cl_discriminant_exec(circle, line);
                if disc.eq(&d2) { 2u8 }
                else if disc.eq(&d3) { 3u8 }
                else if disc.eq(&d5) { 5u8 }
                else if disc.eq(&d6) { 6u8 }
                else if disc.eq(&d7) { 7u8 }
                else if disc.eq(&d10) { 10u8 }
                else if disc.eq(&d11) { 11u8 }
                else if disc.eq(&d13) { 13u8 }
                else { return 0; } // Unrecognized discriminant
            }
            RuntimeStepData::CircleCircle { c1, c2, .. } => {
                let disc = cc_discriminant_exec(c1, c2);
                if disc.eq(&d2) { 2u8 }
                else if disc.eq(&d3) { 3u8 }
                else if disc.eq(&d5) { 5u8 }
                else if disc.eq(&d6) { 6u8 }
                else if disc.eq(&d7) { 7u8 }
                else if disc.eq(&d10) { 10u8 }
                else if disc.eq(&d11) { 11u8 }
                else if disc.eq(&d13) { 13u8 }
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
    ensures
        out@.len() == solutions@.len(),
        forall|si: int| 0 <= si < out@.len() ==>
            (#[trigger] out@[si]).ghost_n_constraints_verified@
                == solutions@[si].ghost_constraints@.len(),
{
    let mut result: Vec<SolvedPoints> = Vec::new();
    let mut i: usize = 0;
    while i < solutions.len()
        invariant
            i <= solutions@.len(),
            result@.len() == i,
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|k: int| 0 <= k < (#[trigger] solutions@[si]).ext_points@.len() ==>
                    (#[trigger] solutions@[si].ext_points@[k]).wf_spec(),
            forall|si: int| 0 <= si < solutions@.len() ==>
                forall|j: int| 0 <= j < (#[trigger] solutions@[si]).plan@.len() ==>
                    (#[trigger] solutions@[si].plan@[j]).wf_spec(),
            forall|si: int| 0 <= si < result@.len() ==>
                (#[trigger] result@[si]).ghost_n_constraints_verified@
                    == solutions@[si].ghost_constraints@.len(),
        decreases solutions@.len() - i,
    {
        let sp = to_solved_points(&solutions[i]);
        result.push(sp);
        i = i + 1;
    }
    result
}

/// Top-level solve-and-verify with automatic radicand detection.
/// Detects whether all circle steps share a common square-free discriminant
/// (2, 3, 5, 6, 7, 10, 11, or 13), then dispatches to the appropriate
/// generic instantiation.
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
    ensures
        // Every returned solution verified all input constraints
        // at the extension level (radicand type-erased).
        forall|si: int| 0 <= si < out@.len() ==>
            (#[trigger] out@[si]).ghost_n_constraints_verified@
                == constraints_to_spec(constraints@).len(),
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
        6 => {
            let solutions = verify_variants::<Sqrt6, RuntimeSqrt6>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
        7 => {
            let solutions = verify_variants::<Sqrt7, RuntimeSqrt7>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
        10 => {
            let solutions = verify_variants::<Sqrt10, RuntimeSqrt10>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
        11 => {
            let solutions = verify_variants::<Sqrt11, RuntimeSqrt11>(
                &variants, constraints, &initial_points, &initial_flags,
            );
            collect_solved_points(&solutions)
        }
        13 => {
            let solutions = verify_variants::<Sqrt13, RuntimeSqrt13>(
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

// ===========================================================================
//  Lazy variant generation with early termination
// ===========================================================================

/// Detect discriminant from a single plan (not a vec of variants).
/// Used by lazy generation to detect before enumerating variants.
fn detect_discriminant_single(
    plan: &Vec<RuntimeStepData>,
) -> (out: u8)
    requires
        forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
{
    let d2 = RuntimeRational::from_int(2);
    let d3 = RuntimeRational::from_int(3);
    let d5 = RuntimeRational::from_int(5);
    let d6 = RuntimeRational::from_int(6);
    let d7 = RuntimeRational::from_int(7);
    let d10 = RuntimeRational::from_int(10);
    let d11 = RuntimeRational::from_int(11);
    let d13 = RuntimeRational::from_int(13);
    let mut found: u8 = 0;
    let mut i: usize = 0;

    while i < plan.len()
        invariant
            i <= plan@.len(),
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
            d2.wf_spec(), d3.wf_spec(), d5.wf_spec(),
            d6.wf_spec(), d7.wf_spec(), d10.wf_spec(), d11.wf_spec(), d13.wf_spec(),
        decreases plan@.len() - i,
    {
        let disc_val: u8 = match &plan[i] {
            RuntimeStepData::CircleLine { circle, line, .. } => {
                let disc = cl_discriminant_exec(circle, line);
                if disc.eq(&d2) { 2u8 }
                else if disc.eq(&d3) { 3u8 }
                else if disc.eq(&d5) { 5u8 }
                else if disc.eq(&d6) { 6u8 }
                else if disc.eq(&d7) { 7u8 }
                else if disc.eq(&d10) { 10u8 }
                else if disc.eq(&d11) { 11u8 }
                else if disc.eq(&d13) { 13u8 }
                else { return 0; }
            }
            RuntimeStepData::CircleCircle { c1, c2, .. } => {
                let disc = cc_discriminant_exec(c1, c2);
                if disc.eq(&d2) { 2u8 }
                else if disc.eq(&d3) { 3u8 }
                else if disc.eq(&d5) { 5u8 }
                else if disc.eq(&d6) { 6u8 }
                else if disc.eq(&d7) { 7u8 }
                else if disc.eq(&d10) { 10u8 }
                else if disc.eq(&d11) { 11u8 }
                else if disc.eq(&d13) { 13u8 }
                else { return 0; }
            }
            _ => { 0u8 }
        };

        if disc_val > 0 {
            if found == 0 {
                found = disc_val;
            } else if found != disc_val {
                return 0;
            }
        }
        i = i + 1;
    }

    found
}

/// Lazily generate variants and return the first verified solution.
/// Generates one variant at a time, avoiding upfront 2^k allocation.
fn lazy_verify_first<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    base_plan: &Vec<RuntimeStepData>,
    constraints: &Vec<RuntimeConstraint>,
    initial_points: &Vec<RuntimePoint2>,
    initial_flags: &Vec<bool>,
) -> (out: Option<SolvedPoints>)
    requires
        initial_points@.len() == initial_flags@.len(),
        all_points_wf(initial_points@),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], initial_points@.len() as nat),
        forall|i: int| 0 <= i < initial_flags@.len() ==>
            (#[trigger] initial_flags@[i]) ==
            partial_resolved_map(points_view(initial_points@), initial_flags@)
                .dom().contains(i as nat),
        forall|j: int| 0 <= j < base_plan@.len() ==> (#[trigger] base_plan@[j]).wf_spec(),
        forall|i: int, j: int|
            0 <= i < base_plan@.len() && 0 <= j < base_plan@.len() && i != j ==>
            step_target(#[trigger] base_plan@[i].spec_step()) !=
            step_target(#[trigger] base_plan@[j].spec_step()),
        forall|j: int| 0 <= j < base_plan@.len() ==>
            (step_target((#[trigger] base_plan@[j]).spec_step()) as int) < initial_points@.len(),
    ensures
        out.is_some() ==>
            out.unwrap().ghost_n_constraints_verified@
                == constraints_to_spec(constraints@).len(),
{
    // Check base plan feasibility once — discriminants don't change with sign flips
    if !check_variant_feasible(base_plan) {
        return None;
    }

    let k = count_circle_steps(base_plan);

    if k > 63 {
        // Too many circle steps to enumerate; try base plan only
        proof {
            assert forall|j: int| 0 <= j < base_plan@.len()
            implies step_geometrically_valid((#[trigger] base_plan@[j]).spec_step())
            by { assert(base_plan@[j].wf_spec()); }
        }
        let result = verify_single_variant::<R, RR>(
            base_plan, constraints, initial_points, initial_flags,
        );
        return match result {
            Some(sol) => Some(to_solved_points(&sol)),
            None => None,
        };
    }

    let n: u64 = 1u64 << (k as u64);
    let mut mask: u64 = 0;

    while mask < n
        invariant
            0 <= mask <= n,
            n == 1u64 << (k as u64),
            k <= 63,
            // Base plan properties
            forall|j: int| 0 <= j < base_plan@.len() ==> (#[trigger] base_plan@[j]).wf_spec(),
            forall|i: int, j: int|
                0 <= i < base_plan@.len() && 0 <= j < base_plan@.len() && i != j ==>
                step_target(#[trigger] base_plan@[i].spec_step()) !=
                step_target(#[trigger] base_plan@[j].spec_step()),
            forall|j: int| 0 <= j < base_plan@.len() ==>
                (step_target((#[trigger] base_plan@[j]).spec_step()) as int) < initial_points@.len(),
            forall|j: int| 0 <= j < base_plan@.len() ==>
                step_has_positive_discriminant((#[trigger] base_plan@[j]).spec_step()),
            // Initial state properties
            initial_points@.len() == initial_flags@.len(),
            all_points_wf(initial_points@),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], initial_points@.len() as nat),
            forall|i: int| 0 <= i < initial_flags@.len() ==>
                (#[trigger] initial_flags@[i]) ==
                partial_resolved_map(points_view(initial_points@), initial_flags@)
                    .dom().contains(i as nat),
        decreases n - mask,
    {
        let variant = make_sign_variant(base_plan, mask);
        proof {
            // Derive variant properties from base plan + make_sign_variant ensures
            assert forall|i: int, j: int|
                0 <= i < variant@.len() && 0 <= j < variant@.len() && i != j
            implies
                step_target(#[trigger] variant@[i].spec_step()) !=
                step_target(#[trigger] variant@[j].spec_step())
            by {
                assert(step_target(variant@[i].spec_step()) == step_target(base_plan@[i].spec_step()));
                assert(step_target(variant@[j].spec_step()) == step_target(base_plan@[j].spec_step()));
            }
            assert forall|j: int| 0 <= j < variant@.len()
            implies
                (step_target((#[trigger] variant@[j]).spec_step()) as int) < initial_points@.len()
            by {
                assert(step_target(variant@[j].spec_step()) == step_target(base_plan@[j].spec_step()));
            }
            assert forall|j: int| 0 <= j < variant@.len()
            implies
                step_has_positive_discriminant((#[trigger] variant@[j]).spec_step())
            by {
                assert(step_has_positive_discriminant(variant@[j].spec_step())
                    == step_has_positive_discriminant(base_plan@[j].spec_step()));
            }
            assert forall|j: int| 0 <= j < variant@.len()
            implies
                step_geometrically_valid((#[trigger] variant@[j]).spec_step())
            by {
                assert(variant@[j].wf_spec());
            }
        }
        let result = verify_single_variant::<R, RR>(
            &variant, constraints, initial_points, initial_flags,
        );
        match result {
            Some(sol) => {
                return Some(to_solved_points(&sol));
            }
            None => {}
        }
        mask = mask + 1;
    }

    None
}

/// Top-level solve-and-verify with early termination.
/// Returns the first valid solution found, or None.
/// Uses lazy variant generation: generates one variant at a time instead of
/// pre-computing all 2^k variants upfront.
pub fn solve_and_verify_first_auto(
    free_ids: &Vec<usize>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: Option<SolvedPoints>)
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
        out.is_some() ==>
            out.unwrap().ghost_n_constraints_verified@
                == constraints_to_spec(constraints@).len(),
{
    // Save initial state before greedy_solve_exec mutates
    let initial_points = copy_points_vec(points);
    let initial_flags = copy_flags_vec(resolved_flags);

    // Run greedy solver (mutates points/resolved_flags)
    let base_plan = greedy_solve_exec(free_ids, constraints, points, resolved_flags);

    // Detect discriminant from base plan
    let disc = detect_discriminant_single(&base_plan);

    // Dispatch to appropriate generic instantiation with lazy verification
    match disc {
        2 => lazy_verify_first::<Sqrt2, RuntimeSqrt2>(
            &base_plan, constraints, &initial_points, &initial_flags),
        3 => lazy_verify_first::<Sqrt3, RuntimeSqrt3>(
            &base_plan, constraints, &initial_points, &initial_flags),
        5 => lazy_verify_first::<Sqrt5, RuntimeSqrt5>(
            &base_plan, constraints, &initial_points, &initial_flags),
        6 => lazy_verify_first::<Sqrt6, RuntimeSqrt6>(
            &base_plan, constraints, &initial_points, &initial_flags),
        7 => lazy_verify_first::<Sqrt7, RuntimeSqrt7>(
            &base_plan, constraints, &initial_points, &initial_flags),
        10 => lazy_verify_first::<Sqrt10, RuntimeSqrt10>(
            &base_plan, constraints, &initial_points, &initial_flags),
        11 => lazy_verify_first::<Sqrt11, RuntimeSqrt11>(
            &base_plan, constraints, &initial_points, &initial_flags),
        13 => lazy_verify_first::<Sqrt13, RuntimeSqrt13>(
            &base_plan, constraints, &initial_points, &initial_flags),
        _ => lazy_verify_first::<Sqrt2, RuntimeSqrt2>(
            &base_plan, constraints, &initial_points, &initial_flags),
    }
}

// ===========================================================================
//  Arbitrary-depth solve-and-verify using dynamic field tower
// ===========================================================================

/// Solve constraints and verify using the arbitrary-depth dynamic field tower.
///
/// Unlike `solve_and_verify_auto` which dispatches to fixed radicand types (Sqrt2, Sqrt3, etc.)
/// and only handles depth-1 extensions, this function handles ANY depth by using DynFieldElem
/// to type-erase the tower level.
///
/// Flow:
/// 1. Greedy solver → construction plan
/// 2. Compute tower levels + constraint pairs
/// 3. Execute all levels: rational → Q(√d₁) → Q(√d₁)(√d₂) → ... (arbitrary depth)
/// 4. Runtime-check ALL constraints at the deepest level
/// 5. Extract rational approximations
///
/// **Spec guarantee:** When this function returns Some, all constraints are satisfied
/// at the DynTowerSpec level (`constraint_satisfied_dts`). This is a weaker guarantee
/// than `solve_and_verify<R>` (which ensures `constraint_satisfied` on
/// `execute_plan_in_ext`), but it is fully verified: each `check_*_dyn` function
/// has ensures connecting its runtime arithmetic to the `dts_*` spec operations.
/// The trust boundary is the `dyn_*` primitive methods on DynFieldElem.
pub fn solve_and_verify_chain(
    free_ids: &Vec<usize>,
    constraints: &Vec<RuntimeConstraint>,
    points: &mut Vec<RuntimePoint2>,
    resolved_flags: &mut Vec<bool>,
) -> (out: Option<Vec<RuntimePoint2>>)
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
        out.is_some() ==> ({
            let r = out.unwrap();
            &&& r@.len() == old(points)@.len()
            &&& all_points_wf(r@)
            // All constraints verified at the DynTowerSpec level:
            // there exist deep tower positions satisfying all constraints.
            &&& exists|deep: Seq<DynRtPoint2>|
                    #[trigger] all_dyn_points_wf(deep) && deep.len() > 0
                    && forall|ci: int| 0 <= ci < constraints@.len() ==>
                        constraint_satisfied_dts(#[trigger] constraints@[ci], deep)
        }),
{
    // Run greedy solver (mutates points/resolved_flags)
    let plan = greedy_solve_exec(free_ids, constraints, points, resolved_flags);

    if points.len() == 0 {
        return None;
    }

    // Extract abstract plan and compute tower levels
    let abstract_plan = extract_abstract_plan(&plan);
    let levels = compute_step_levels(&abstract_plan, constraints);
    let depth = crate::runtime::abstract_plan::max_depth(&levels);

    // If no circle steps, all positions are rational — return directly.
    // Wrap rational points as DynRtPoint2 and check constraints at DynTowerSpec level.
    if depth == 0 {
        let result = copy_points_vec(points);
        let dyn_pts = wrap_rationals_as_dyn(points);
        let dyn_ok = check_all_constraints_dyn(constraints, &dyn_pts);
        if !dyn_ok {
            return None;
        }
        proof {
            let deep = dyn_pts@;
            assert(all_dyn_points_wf(deep));
            assert(deep.len() > 0);
        }
        return Some(result);
    }

    // Extract constraint pairs for circle steps
    let pairs = match extract_constraint_pairs(&abstract_plan, constraints) {
        None => { return None; }
        Some(p) => p,
    };

    // Execute all tower levels using dyn_pipeline (no OrderedField, no assumes)
    let deep_positions = match execute_all_levels_dyn(
        &*points, &abstract_plan, constraints, &pairs, &levels, depth,
    ) {
        None => { return None; }
        Some(pos) => pos,
    };

    // Runtime-check ALL constraints at the deepest level (dyn-specific, no assumes)
    let all_ok = check_all_constraints_dyn(constraints, &deep_positions);

    if !all_ok {
        return None;
    }

    // Capture deep positions as ghost witness for the ensures
    let ghost deep_witness = deep_positions@;

    // Extract rational approximations (innermost re.re.re...)
    let rational_pts = extract_rational_points_dyn(&deep_positions);

    proof {
        // Provide the existential witness: deep_positions@ satisfies all constraints
        assert(all_dyn_points_wf(deep_witness));
        assert(deep_witness.len() > 0);
        assert(forall|ci: int| 0 <= ci < constraints@.len() ==>
            constraint_satisfied_dts(#[trigger] constraints@[ci], deep_witness));
    }

    Some(rational_pts)
}

} // verus!
