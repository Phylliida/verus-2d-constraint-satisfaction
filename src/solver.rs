use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use crate::entities::*;
use crate::constraints::*;
use crate::locus::*;
use crate::construction::*;

verus! {

// ===========================================================================
//  Greedy solver specification
// ===========================================================================

/// An entity is "ready" when all constraints referencing it have their
/// other entities already resolved, yielding at least two non-trivial loci.
pub open spec fn entity_ready<T: OrderedField>(
    id: EntityId,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
) -> bool {
    !resolved.dom().contains(id) && {
        let loci = collect_loci(constraints, resolved, id);
        // Count non-trivial (non-FullPlane) loci
        exists|i: int, j: int|
            0 <= i < loci.len() && 0 <= j < loci.len() && i != j
            && locus_is_nontrivial(loci[i])
            && locus_is_nontrivial(loci[j])
    }
}

/// Find the first two non-FullPlane loci for an entity.
pub open spec fn find_two_loci<T: OrderedField>(
    loci: Seq<Locus2d<T>>,
) -> Option<(Locus2d<T>, Locus2d<T>)>
    decreases loci.len(),
{
    if loci.len() == 0 {
        None
    } else {
        let rest_result = find_first_locus(loci.drop_last());
        let last = loci.last();
        if locus_is_nontrivial(last) {
            match rest_result {
                Some(first) => Some((first, last)),
                None => None,
            }
        } else {
            find_two_loci(loci.drop_last())
        }
    }
}

/// Find the first non-FullPlane locus.
pub open spec fn find_first_locus<T: OrderedField>(
    loci: Seq<Locus2d<T>>,
) -> Option<Locus2d<T>>
    decreases loci.len(),
{
    if loci.len() == 0 {
        None
    } else if !matches!(loci.last(), Locus2d::FullPlane) {
        Some(loci.last())
    } else {
        find_first_locus(loci.drop_last())
    }
}

// ===========================================================================
//  Greedy plan construction (spec-level)
// ===========================================================================

/// Try to build a step for entity `id` given current resolved state.
pub open spec fn try_build_step<T: OrderedField>(
    id: EntityId,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
) -> Option<ConstructionStep<T>> {
    let loci = collect_loci(constraints, resolved, id);
    match find_two_loci(loci) {
        Some((l1, l2)) => intersect_loci(id, l1, l2),
        None => None,
    }
}

/// Greedy solver: iteratively resolve entities that have enough constraints.
/// `free_ids` is the set of entity IDs that need to be resolved.
/// Returns the construction plan built so far.
pub open spec fn greedy_solve<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
    fuel: nat,
) -> ConstructionPlan<T>
    decreases fuel,
{
    if fuel == 0 || free_ids.len() == 0 {
        Seq::empty()
    } else {
        // Try each free entity; take the first one that works
        let step = find_next_step(free_ids, constraints, resolved, 0);
        match step {
            Some((idx, construction_step)) => {
                let new_id = step_target(construction_step);
                let new_resolved = resolved.insert(new_id, execute_step(construction_step));
                let remaining = remove_id(free_ids, idx);
                let rest = greedy_solve(remaining, constraints, new_resolved, (fuel - 1) as nat);
                Seq::empty().push(construction_step).add(rest)
            }
            None => Seq::empty(), // Stuck: no entity is ready
        }
    }
}

/// Scan free_ids from position `start` for the first entity that can be resolved.
pub open spec fn find_next_step<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
    start: int,
) -> Option<(int, ConstructionStep<T>)>
    decreases free_ids.len() - start,
{
    if start >= free_ids.len() {
        None
    } else {
        match try_build_step(free_ids[start], constraints, resolved) {
            Some(step) => Some((start, step)),
            None => find_next_step(free_ids, constraints, resolved, start + 1),
        }
    }
}

/// Remove element at index from a sequence.
pub open spec fn remove_id(ids: Seq<EntityId>, idx: int) -> Seq<EntityId> {
    ids.take(idx).add(ids.skip(idx + 1))
}

// ===========================================================================
//  Solver correctness helpers
// ===========================================================================

/// intersect_loci preserves the entity id: step_target of the result is id.
pub proof fn lemma_intersect_loci_target<T: OrderedField>(
    id: EntityId, l1: Locus2d<T>, l2: Locus2d<T>,
)
    ensures
        match intersect_loci(id, l1, l2) {
            Some(step) => step_target(step) == id,
            None => true,
        },
{
    // By case analysis on intersect_loci definition — every variant stores id.
}

/// find_next_step returns a step whose target is in free_ids.
proof fn lemma_find_next_step_target<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
    start: int,
)
    requires
        0 <= start,
    ensures
        match find_next_step(free_ids, constraints, resolved, start) {
            Some((idx, step)) => start <= idx < free_ids.len()
                && step_target(step) == free_ids[idx],
            None => true,
        },
    decreases free_ids.len() - start,
{
    if start >= free_ids.len() {
        // None
    } else {
        lemma_intersect_loci_target::<T>(
            free_ids[start],
            // We don't need to specify l1/l2 explicitly — just show the property holds
            // for whatever intersect_loci returns.
            // Actually we need the full try_build_step chain.
            // try_build_step calls intersect_loci(free_ids[start], l1, l2)
            // So step_target == free_ids[start].
            // But we need to thread through try_build_step.
            // Let's just check both branches.
            Locus2d::FullPlane, Locus2d::FullPlane, // placeholder — the actual proof is by unfolding
        );
        match try_build_step(free_ids[start], constraints, resolved) {
            Some(step) => {
                // try_build_step returns intersect_loci(free_ids[start], ...)
                // By lemma_intersect_loci_target, step_target == free_ids[start]
                // find_next_step returns (start, step)
                let loci = collect_loci(constraints, resolved, free_ids[start]);
                match find_two_loci(loci) {
                    Some((l1, l2)) => {
                        lemma_intersect_loci_target::<T>(free_ids[start], l1, l2);
                    }
                    None => {} // can't happen if try_build_step returned Some
                }
            }
            None => {
                lemma_find_next_step_target::<T>(free_ids, constraints, resolved, start + 1);
            }
        }
    }
}

/// Removing an element from a distinct sequence preserves distinctness.
proof fn lemma_remove_id_preserves_distinct(
    ids: Seq<EntityId>, idx: int,
)
    requires
        0 <= idx < ids.len(),
        forall|i: int, j: int|
            0 <= i < ids.len() && 0 <= j < ids.len() && i != j ==>
            ids[i] != ids[j],
    ensures ({
        let remaining = remove_id(ids, idx);
        &&& remaining.len() == ids.len() - 1
        &&& forall|i: int, j: int|
            0 <= i < remaining.len() && 0 <= j < remaining.len() && i != j ==>
            remaining[i] != remaining[j]
    }),
{
    let remaining = remove_id(ids, idx);
    // remaining = ids.take(idx) ++ ids.skip(idx + 1)
    // Length: idx + (ids.len() - idx - 1) = ids.len() - 1
    assert(remaining.len() == ids.len() - 1);

    // Distinctness: each element of remaining maps to a unique element of ids
    assert forall|i: int, j: int|
        0 <= i < remaining.len() && 0 <= j < remaining.len() && i != j
    implies remaining[i] != remaining[j]
    by {
        // Map remaining indices back to original indices
        let orig_i: int = if i < idx { i } else { i + 1 };
        let orig_j: int = if j < idx { j } else { j + 1 };
        assert(0 <= orig_i < ids.len());
        assert(0 <= orig_j < ids.len());
        assert(orig_i != orig_j);
        assert(ids[orig_i] != ids[orig_j]);
        // remaining[i] == ids[orig_i] and remaining[j] == ids[orig_j]
        if i < idx {
            assert(remaining[i] == ids.take(idx)[i]);
        } else {
            assert(remaining[i] == ids.skip(idx + 1)[i - idx]);
        }
        if j < idx {
            assert(remaining[j] == ids.take(idx)[j]);
        } else {
            assert(remaining[j] == ids.skip(idx + 1)[j - idx]);
        }
    };
}

/// Element at idx is not in remove_id(ids, idx) when ids has distinct elements.
proof fn lemma_removed_element_not_in_remaining(
    ids: Seq<EntityId>, idx: int,
)
    requires
        0 <= idx < ids.len(),
        forall|i: int, j: int|
            0 <= i < ids.len() && 0 <= j < ids.len() && i != j ==>
            ids[i] != ids[j],
    ensures ({
        let remaining = remove_id(ids, idx);
        forall|k: int| 0 <= k < remaining.len() ==> remaining[k] != ids[idx]
    }),
{
    let remaining = remove_id(ids, idx);
    assert forall|k: int| 0 <= k < remaining.len()
    implies remaining[k] != ids[idx]
    by {
        let orig_k: int = if k < idx { k } else { k + 1 };
        assert(0 <= orig_k < ids.len());
        assert(orig_k != idx);
        if k < idx {
            assert(remaining[k] == ids.take(idx)[k]);
        } else {
            assert(remaining[k] == ids.skip(idx + 1)[k - idx]);
        }
    };
}

/// Non-removed elements of ids appear in remove_id(ids, idx).
proof fn lemma_remove_id_contains_others(
    ids: Seq<EntityId>, idx: int, i: int,
)
    requires
        0 <= idx < ids.len(),
        0 <= i < ids.len(),
        i != idx,
    ensures ({
        let remaining = remove_id(ids, idx);
        let j: int = if i < idx { i } else { i - 1 };
        0 <= j < remaining.len() && remaining[j] == ids[i]
    }),
{
    let remaining = remove_id(ids, idx);
    let j: int = if i < idx { i } else { i - 1 };
    if i < idx {
        assert(remaining[j] == ids.take(idx)[i]);
    } else {
        assert(remaining[j] == ids.skip(idx + 1)[i - idx - 1]);
    }
}

// ===========================================================================
//  Solver correctness
// ===========================================================================

/// The greedy solver produces a plan with distinct targets, and every
/// target is one of the free_ids.
proof fn lemma_greedy_solver_sound_inner<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
    fuel: nat,
)
    requires
        forall|i: int, j: int|
            0 <= i < free_ids.len() && 0 <= j < free_ids.len() && i != j ==>
            free_ids[i] != free_ids[j],
    ensures ({
        let plan = greedy_solve(free_ids, constraints, resolved, fuel);
        // Distinct targets
        &&& forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j])
        // All targets are from free_ids
        &&& forall|k: int| #![trigger plan[k]]
            0 <= k < plan.len() ==>
            exists|fi: int| 0 <= fi < free_ids.len()
                && step_target(plan[k]) == free_ids[fi]
    }),
    decreases fuel,
{
    if fuel == 0 || free_ids.len() == 0 {
        // Empty plan — trivially true
    } else {
        let step_opt = find_next_step(free_ids, constraints, resolved, 0);
        lemma_find_next_step_target::<T>(free_ids, constraints, resolved, 0);
        match step_opt {
            Some((idx, construction_step)) => {
                let new_id = step_target(construction_step);
                let new_resolved = resolved.insert(
                    new_id, execute_step(construction_step),
                );
                let remaining = remove_id(free_ids, idx);

                lemma_remove_id_preserves_distinct(free_ids, idx);
                lemma_removed_element_not_in_remaining(free_ids, idx);

                // Recurse: rest plan has distinct targets, all from remaining
                lemma_greedy_solver_sound_inner::<T>(
                    remaining, constraints, new_resolved, (fuel - 1) as nat,
                );

                let rest = greedy_solve(
                    remaining, constraints, new_resolved, (fuel - 1) as nat,
                );
                let plan = Seq::empty().push(construction_step).add(rest);

                // Show all targets in rest are in remaining → in free_ids
                // And new_id == free_ids[idx] is not in remaining
                // So new_id ≠ any rest target
                assert forall|i: int, j: int|
                    0 <= i < plan.len() && 0 <= j < plan.len() && i != j
                implies step_target(plan[i]) != step_target(plan[j])
                by {
                    if i == 0 && j > 0 {
                        // plan[0] = construction_step, plan[j] = rest[j-1]
                        // step_target(plan[0]) = new_id = free_ids[idx]
                        // step_target(plan[j]) = step_target(rest[j-1]) ∈ remaining
                        // free_ids[idx] ∉ remaining
                        assert(plan[0] == construction_step);
                        assert(plan[j] == rest[j - 1]);
                    } else if j == 0 && i > 0 {
                        assert(plan[0] == construction_step);
                        assert(plan[i] == rest[i - 1]);
                    } else if i > 0 && j > 0 {
                        // Both in rest, which has distinct targets
                        assert(plan[i] == rest[i - 1]);
                        assert(plan[j] == rest[j - 1]);
                    }
                };

                // Show all targets are from free_ids
                assert forall|k: int| 0 <= k < plan.len()
                implies exists|fi: int| 0 <= fi < free_ids.len()
                    && step_target(#[trigger] plan[k]) == free_ids[fi]
                by {
                    if k == 0 {
                        assert(step_target(plan[0]) == free_ids[idx]);
                    } else {
                        assert(plan[k] == rest[k - 1]);
                        // rest[k-1] target is in remaining
                        // remaining elements are elements of free_ids
                        let fi_rem = choose|fi: int| 0 <= fi < remaining.len()
                            && step_target(rest[k - 1]) == remaining[fi];
                        let orig_fi: int = if fi_rem < idx { fi_rem } else { fi_rem + 1 };
                        assert(0 <= orig_fi < free_ids.len());
                        if fi_rem < idx {
                            assert(remaining[fi_rem] == free_ids.take(idx)[fi_rem]);
                        } else {
                            assert(remaining[fi_rem] == free_ids.skip(idx + 1)[fi_rem - idx]);
                        }
                    }
                };
            }
            None => {} // Empty plan
        }
    }
}

/// The greedy solver produces a valid plan (when it terminates).
pub proof fn lemma_greedy_solver_sound<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    initial_resolved: ResolvedPoints<T>,
    fuel: nat,
)
    requires
        // All free IDs are distinct
        forall|i: int, j: int|
            0 <= i < free_ids.len() && 0 <= j < free_ids.len() && i != j ==>
            free_ids[i] != free_ids[j],
        // Free IDs are not in the initial resolved set
        forall|i: int| 0 <= i < free_ids.len() ==>
            !initial_resolved.dom().contains(free_ids[i]),
    ensures ({
        let plan = greedy_solve(free_ids, constraints, initial_resolved, fuel);
        // Each step targets a distinct entity
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j])
    }),
{
    lemma_greedy_solver_sound_inner::<T>(
        free_ids, constraints, initial_resolved, fuel,
    );
}

// ===========================================================================
//  System well-constrained predicate
// ===========================================================================

/// A constraint system is well-constrained when the greedy solver with
/// sufficient fuel produces a plan covering ALL free entity IDs.
///
/// This is the spec-level characterization of solvability: every free entity
/// eventually becomes ready (has ≥ 2 non-trivial loci from resolved neighbors),
/// and the greedy algorithm terminates with all entities placed.
///
/// When this predicate is false, the system is either:
/// - Under-constrained: some entity has < 2 loci
/// - Cyclically constrained: entities depend on each other
/// - Degenerately constrained: locus intersections are invalid (parallel lines, etc.)
pub open spec fn system_is_well_constrained<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    initial_resolved: ResolvedPoints<T>,
) -> bool {
    greedy_solve(free_ids, constraints, initial_resolved, free_ids.len()).len()
        == free_ids.len()
}

/// The set of entity IDs that the greedy solver could not resolve.
/// Empty iff `system_is_well_constrained` holds.
pub open spec fn solver_stuck_entities<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    initial_resolved: ResolvedPoints<T>,
) -> Set<EntityId> {
    let plan = greedy_solve(free_ids, constraints, initial_resolved, free_ids.len());
    Set::new(|id: EntityId|
        exists|i: int| 0 <= i < free_ids.len() && free_ids[i] == id
        && forall|j: int| 0 <= j < plan.len() ==> step_target(plan[j]) != id
    )
}

// ===========================================================================
//  Completeness lemmas
// ===========================================================================

/// Greedy solver plan length is bounded by free_ids length.
/// The solver resolves at most one entity per fuel unit, and each entity
/// comes from free_ids (with removal), so the plan can't exceed free_ids.len().
pub proof fn lemma_greedy_solve_bounded<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
    fuel: nat,
)
    ensures greedy_solve(free_ids, constraints, resolved, fuel).len() <= free_ids.len(),
    decreases fuel,
{
    if fuel == 0 || free_ids.len() == 0 {
        // plan is empty
    } else {
        let step = find_next_step(free_ids, constraints, resolved, 0);
        match step {
            Some((idx, construction_step)) => {
                lemma_find_next_step_target::<T>(free_ids, constraints, resolved, 0);
                let remaining = remove_id(free_ids, idx);
                // remaining.len() == free_ids.len() - 1
                assert(0 <= idx < free_ids.len());
                assert(remaining == free_ids.take(idx).add(free_ids.skip(idx + 1)));
                assert(remaining.len() == free_ids.len() - 1) by {
                    assert(free_ids.take(idx).len() == idx);
                    assert(free_ids.skip(idx + 1).len() == free_ids.len() - idx - 1);
                };
                let new_resolved = resolved.insert(
                    step_target(construction_step), execute_step(construction_step));
                lemma_greedy_solve_bounded::<T>(
                    remaining, constraints, new_resolved, (fuel - 1) as nat);
                // rest.len() <= remaining.len() = free_ids.len() - 1
                // plan = [construction_step] ++ rest
                // plan.len() = 1 + rest.len() <= 1 + free_ids.len() - 1 = free_ids.len()
                let rest = greedy_solve(
                    remaining, constraints, new_resolved, (fuel - 1) as nat);
                let plan = Seq::empty().push(construction_step).add(rest);
                assert(plan.len() == 1 + rest.len());
            }
            None => {} // plan is empty
        }
    }
}

/// When the system is well-constrained and free_ids are distinct,
/// every free entity ID appears as a target in the greedy plan.
///
/// Proof: plan has free_ids.len() distinct targets, all drawn from free_ids.
/// By pigeonhole, every free_id must appear.
pub proof fn lemma_well_constrained_covers_all<T: OrderedField>(
    free_ids: Seq<EntityId>,
    constraints: Seq<Constraint<T>>,
    initial_resolved: ResolvedPoints<T>,
)
    requires
        system_is_well_constrained(free_ids, constraints, initial_resolved),
        forall|i: int, j: int|
            0 <= i < free_ids.len() && 0 <= j < free_ids.len() && i != j ==>
            free_ids[i] != free_ids[j],
        forall|i: int| 0 <= i < free_ids.len() ==>
            !initial_resolved.dom().contains(free_ids[i]),
    ensures ({
        let plan = greedy_solve(free_ids, constraints, initial_resolved, free_ids.len());
        forall|i: int| #![trigger free_ids[i]]
            0 <= i < free_ids.len() ==>
            exists|k: int| 0 <= k < plan.len()
                && step_target(#[trigger] plan[k]) == free_ids[i]
    }),
{
    let plan = greedy_solve(free_ids, constraints, initial_resolved, free_ids.len());
    let n = free_ids.len();

    // From system_is_well_constrained: plan.len() == n
    assert(plan.len() == n);

    // From lemma_greedy_solver_sound_inner: distinct targets, all from free_ids
    lemma_greedy_solver_sound_inner::<T>(
        free_ids, constraints, initial_resolved, free_ids.len());

    // Pigeonhole: n distinct values drawn from a set of size n covers everything.
    // We have an injection f: {0..n} → {0..n} where
    //   f(k) = the index fi such that step_target(plan[k]) == free_ids[fi]
    // Since plan targets are distinct and free_ids are distinct, f is injective.
    // An injection from {0..n} to {0..n} is a surjection.
    lemma_pigeonhole_covers::<T>(free_ids, plan);
}

/// Pigeonhole lemma: if plan has n distinct targets all drawn from n distinct
/// free_ids, then every free_id is covered.
proof fn lemma_pigeonhole_covers<T: OrderedField>(
    free_ids: Seq<EntityId>,
    plan: Seq<ConstructionStep<T>>,
)
    requires
        plan.len() == free_ids.len(),
        // Distinct targets
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        // All targets from free_ids
        forall|k: int| #![trigger plan[k]]
            0 <= k < plan.len() ==>
            exists|fi: int| 0 <= fi < free_ids.len()
                && step_target(plan[k]) == free_ids[fi],
        // Distinct free_ids
        forall|i: int, j: int|
            0 <= i < free_ids.len() && 0 <= j < free_ids.len() && i != j ==>
            free_ids[i] != free_ids[j],
    ensures
        forall|i: int| #![trigger free_ids[i]]
            0 <= i < free_ids.len() ==>
            exists|k: int| 0 <= k < plan.len()
                && step_target(#[trigger] plan[k]) == free_ids[i],
    decreases plan.len(),
{
    let n = plan.len();
    if n == 0 {
        // free_ids.len() == 0, so the ensures is vacuously true
    } else {
        // plan[n-1] maps to some free_ids[fi_last]
        let fi_last = choose|fi: int| 0 <= fi < free_ids.len()
            && step_target(plan[n as int - 1]) == free_ids[fi];

        // Remove plan[n-1] and free_ids[fi_last], apply induction
        let plan_prefix = plan.take(n as int - 1);
        let ids_reduced = remove_id(free_ids, fi_last);

        // plan_prefix has n-1 distinct targets
        assert forall|i: int, j: int|
            0 <= i < plan_prefix.len() && 0 <= j < plan_prefix.len() && i != j
        implies step_target(plan_prefix[i]) != step_target(plan_prefix[j])
        by {
            assert(plan_prefix[i] == plan[i]);
            assert(plan_prefix[j] == plan[j]);
        };

        // plan_prefix targets are all != free_ids[fi_last] (since plan targets are distinct)
        assert forall|k: int| 0 <= k < plan_prefix.len()
        implies step_target(plan_prefix[k]) != free_ids[fi_last]
        by {
            assert(plan_prefix[k] == plan[k]);
            // plan[k] != plan[n-1] since k != n-1
        };

        // ids_reduced has n-1 distinct elements
        lemma_remove_id_preserves_distinct(free_ids, fi_last);

        // All plan_prefix targets are in ids_reduced
        assert forall|k: int| #![trigger plan_prefix[k]]
            0 <= k < plan_prefix.len()
        implies exists|fi: int| 0 <= fi < ids_reduced.len()
            && step_target(plan_prefix[k]) == ids_reduced[fi]
        by {
            assert(plan_prefix[k] == plan[k]);
            // plan[k] target is in free_ids (from precondition)
            let fi_orig = choose|fi: int| 0 <= fi < free_ids.len()
                && step_target(plan[k]) == free_ids[fi];
            // fi_orig != fi_last: plan[k] target != plan[n-1] target (distinct)
            assert(step_target(plan[k]) != step_target(plan[n as int - 1]));
            assert(step_target(plan[k]) != free_ids[fi_last]);
            assert(free_ids[fi_orig] != free_ids[fi_last]);
            assert(fi_orig != fi_last);
            // Use helper: free_ids[fi_orig] appears in ids_reduced
            lemma_remove_id_contains_others(free_ids, fi_last, fi_orig);
        };

        // Verify recursive call preconditions explicitly
        assert(plan_prefix.len() == ids_reduced.len());

        // Apply induction
        lemma_pigeonhole_covers::<T>(ids_reduced, plan_prefix);

        // Now lift: every ids_reduced element is covered by plan_prefix
        // Every free_ids[i] with i != fi_last is in ids_reduced, so covered
        // And free_ids[fi_last] is covered by plan[n-1]
        assert forall|i: int| #![trigger free_ids[i]]
            0 <= i < free_ids.len()
        implies exists|k: int| 0 <= k < plan.len()
            && step_target(#[trigger] plan[k]) == free_ids[i]
        by {
            if i == fi_last {
                assert(step_target(plan[n as int - 1]) == free_ids[fi_last]);
            } else {
                // free_ids[i] is in ids_reduced (via helper)
                lemma_remove_id_contains_others(free_ids, fi_last, i);
                let i_red: int = if i < fi_last { i } else { i - 1 };
                // By induction, some plan_prefix[k] targets ids_reduced[i_red]
                let k_red = choose|k: int| 0 <= k < plan_prefix.len()
                    && step_target(plan_prefix[k]) == ids_reduced[i_red];
                assert(plan_prefix[k_red] == plan[k_red]);
            }
        };
    }
}

} // verus!
