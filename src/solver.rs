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

    // Build the explicit target→id map and target sequence as nat
    let targets = Seq::new(n, |k: int| -> nat { step_target(plan[k]) });
    let f = Seq::new(n, |k: int| -> int {
        choose|fi: int| 0 <= fi < n && step_target(plan[k]) == free_ids[fi]
    });

    // f maps correctly
    assert forall|k: int| #![trigger f[k]]
        0 <= k < f.len()
    implies 0 <= f[k] < free_ids.len() && targets[k] == free_ids[f[k]]
    by {
        let fi = choose|fi: int| 0 <= fi < n && step_target(plan[k]) == free_ids[fi];
        assert(targets[k] == step_target(plan[k]));
    };

    // f is injective (distinct targets + distinct free_ids)
    assert forall|i: int, j: int|
        0 <= i < f.len() && 0 <= j < f.len() && i != j
    implies f[i] != f[j]
    by {
        // step_target(plan[i]) != step_target(plan[j]) (distinct targets)
        // targets[i] == free_ids[f[i]] and targets[j] == free_ids[f[j]]
        // If f[i] == f[j], then free_ids[f[i]] == free_ids[f[j]],
        // so targets[i] == targets[j], so step_target(plan[i]) == step_target(plan[j]),
        // contradicting distinct targets
        if f[i] == f[j] {
            assert(targets[i] == free_ids[f[i]]);
            assert(targets[j] == free_ids[f[j]]);
            assert(targets[i] == targets[j]);
            assert(step_target(plan[i]) == step_target(plan[j]));
        }
    };

    // Apply pigeonhole
    lemma_pigeonhole_nat_seqs(free_ids, targets, f);

    // Transfer: targets[k] == free_ids[i] means step_target(plan[k]) == free_ids[i]
    assert forall|i: int| #![trigger free_ids[i]]
        0 <= i < free_ids.len()
    implies exists|k: int| 0 <= k < plan.len()
        && step_target(#[trigger] plan[k]) == free_ids[i]
    by {
        let k_found = choose|k: int| 0 <= k < targets.len() && targets[k] == free_ids[i];
        assert(targets[k_found] == step_target(plan[k_found]));
    };
}

/// Pigeonhole lemma: if plan has n distinct targets all drawn from n distinct
/// free_ids, then every free_id is covered.
/// Pigeonhole on nat sequences: if `targets` has n values all drawn from
/// `ids` (via explicit injection `f`), then every id is hit.
/// Using an explicit map Seq avoids quantifier/trigger issues.
proof fn lemma_pigeonhole_nat_seqs(
    ids: Seq<nat>,
    targets: Seq<nat>,
    f: Seq<int>,
)
    requires
        targets.len() == ids.len(),
        f.len() == targets.len(),
        forall|k: int| #![trigger f[k]]
            0 <= k < f.len() ==> 0 <= f[k] < ids.len(),
        forall|k: int| #![trigger f[k]]
            0 <= k < f.len() ==> targets[k] == ids[f[k]],
        forall|i: int, j: int|
            0 <= i < f.len() && 0 <= j < f.len() && i != j ==>
            f[i] != f[j],
    ensures
        forall|i: int| #![trigger ids[i]]
            0 <= i < ids.len() ==>
            exists|k: int| 0 <= k < targets.len() && targets[k] == ids[i],
    decreases targets.len(),
{
    let n = targets.len();
    if n == 0 {
    } else {
        let last_id_idx = f[n as int - 1];
        let targets_prefix = targets.take(n as int - 1);
        let ids_reduced = remove_id(ids, last_id_idx);

        // Build reduced map: shift f values past last_id_idx
        let f_reduced = Seq::new(
            (n - 1) as nat,
            |k: int| -> int { if f[k] < last_id_idx { f[k] } else { f[k] - 1 } },
        );

        // f_reduced maps correctly into ids_reduced
        assert forall|k: int| #![trigger f_reduced[k]]
            0 <= k < f_reduced.len()
        implies 0 <= f_reduced[k] < ids_reduced.len()
            && targets_prefix[k] == ids_reduced[f_reduced[k]]
        by {
            assert(targets_prefix[k] == targets[k]);
            assert(f[k] != last_id_idx) by {
                if f[k] == last_id_idx {
                    // f injective: k != n-1, so f[k] != f[n-1] = last_id_idx
                }
            };
            lemma_remove_id_contains_others(ids, last_id_idx, f[k]);
        };

        // f_reduced is injective
        assert forall|i: int, j: int|
            0 <= i < f_reduced.len() && 0 <= j < f_reduced.len() && i != j
        implies f_reduced[i] != f_reduced[j]
        by {
            assert(f[i] != f[j]);
        };

        // Induction
        lemma_pigeonhole_nat_seqs(ids_reduced, targets_prefix, f_reduced);

        // Lift back
        assert forall|i: int| #![trigger ids[i]]
            0 <= i < ids.len()
        implies exists|k: int| 0 <= k < targets.len() && targets[k] == ids[i]
        by {
            if i == last_id_idx {
                assert(targets[n as int - 1] == ids[f[n as int - 1]]);
            } else {
                lemma_remove_id_contains_others(ids, last_id_idx, i);
                let i_red: int = if i < last_id_idx { i } else { i - 1 };
                let k_red = choose|k: int| 0 <= k < targets_prefix.len()
                    && targets_prefix[k] == ids_reduced[i_red];
                assert(targets_prefix[k_red] == targets[k_red]);
            }
        };
    }
}

} // verus!
