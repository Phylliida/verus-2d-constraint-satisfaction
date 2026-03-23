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

verus! {

// ===========================================================================
//  Construction steps
// ===========================================================================

/// A single step in a geometric construction.
/// Each step places one entity by intersecting two loci.
pub enum ConstructionStep<T: OrderedField> {
    /// Entity is placed at a known position (fixed input or determined by a single AtPoint locus).
    PointStep { id: EntityId, position: Point2<T> },

    /// Entity is determined by the intersection of two lines.
    LineLine {
        id: EntityId,
        line1: Line2<T>,
        line2: Line2<T>,
    },

    /// Entity is determined by the intersection of a circle and a line.
    /// `plus` selects which of the (up to) two intersection points.
    CircleLine {
        id: EntityId,
        circle: Circle2<T>,
        line: Line2<T>,
        plus: bool,
    },

    /// Entity is determined by the intersection of two circles.
    /// `plus` selects which of the (up to) two intersection points.
    CircleCircle {
        id: EntityId,
        circle1: Circle2<T>,
        circle2: Circle2<T>,
        plus: bool,
    },
}

/// A construction plan: a sequence of steps that places all free entities.
pub type ConstructionPlan<T> = Seq<ConstructionStep<T>>;

// ===========================================================================
//  Step execution (spec level)
// ===========================================================================

/// The entity ID targeted by a construction step.
pub open spec fn step_target<T: OrderedField>(step: ConstructionStep<T>) -> EntityId {
    match step {
        ConstructionStep::PointStep { id, .. } => id,
        ConstructionStep::LineLine { id, .. } => id,
        ConstructionStep::CircleLine { id, .. } => id,
        ConstructionStep::CircleCircle { id, .. } => id,
    }
}

/// Execute a single construction step, returning the placed point.
///
/// **Non-deterministic for circle steps:** CircleLine and CircleCircle use `choose`
/// to select an arbitrary intersection point, ignoring the `plus` field. This is
/// because circle intersection formulas require square roots (√discriminant), which
/// do not exist in a generic `T: OrderedField`.
///
/// The canonical **deterministic** execution is `execute_step_in_ext`, which operates
/// in the extension field `SpecQuadExt<F, R>` where √ is available and uses the
/// `plus` flag to select a specific intersection. The soundness proof
/// (`lemma_solver_to_soundness_det`) goes through `execute_plan_in_ext`, not
/// `execute_plan`, so this non-determinism does not weaken any guarantees.
pub open spec fn execute_step<T: OrderedField>(step: ConstructionStep<T>) -> Point2<T> {
    match step {
        ConstructionStep::PointStep { position, .. } => position,

        ConstructionStep::LineLine { line1, line2, .. } => {
            line_line_intersection_2d(line1, line2)
        }

        ConstructionStep::CircleLine { circle, line, .. } => {
            choose|p: Point2<T>| point_on_circle2(circle, p) && point_on_line2(line, p)
        }

        ConstructionStep::CircleCircle { circle1, circle2, .. } => {
            choose|p: Point2<T>| point_on_circle2(circle1, p) && point_on_circle2(circle2, p)
        }
    }
}

/// Execute a full construction plan, accumulating resolved points.
pub open spec fn execute_plan<T: OrderedField>(
    plan: ConstructionPlan<T>,
) -> ResolvedPoints<T>
    decreases plan.len(),
{
    if plan.len() == 0 {
        Map::empty()
    } else {
        let prefix = plan.drop_last();
        let step = plan.last();
        let resolved = execute_plan(prefix);
        resolved.insert(step_target(step), execute_step(step))
    }
}

// ===========================================================================
//  Plan validity
// ===========================================================================

/// A step is well-formed: its loci are non-degenerate (lines not parallel, etc.)
pub open spec fn step_well_formed<T: OrderedField>(
    step: ConstructionStep<T>,
) -> bool {
    match step {
        ConstructionStep::PointStep { .. } => true,

        ConstructionStep::LineLine { id, line1, line2, .. } => {
            // Lines must not be parallel (det != 0)
            !line_det(line1, line2).eqv(T::zero())
        }

        ConstructionStep::CircleLine { circle, line, .. } => {
            // Line must be non-degenerate, and an intersection must exist in T.
            line2_nondegenerate(line) &&
            exists|p: Point2<T>| point_on_circle2(circle, p) && point_on_line2(line, p)
        }

        ConstructionStep::CircleCircle { circle1, circle2, .. } => {
            // Circles must have distinct centers, and an intersection must exist in T.
            !circle1.center.eqv(circle2.center) &&
            exists|p: Point2<T>| point_on_circle2(circle1, p) && point_on_circle2(circle2, p)
        }
    }
}

/// A construction step places the entity so it satisfies its locus.
pub open spec fn step_satisfies_locus<T: OrderedField>(
    step: ConstructionStep<T>,
    locus: Locus2d<T>,
) -> bool {
    point_satisfies_locus(locus, execute_step(step))
}

/// A construction step satisfies ALL constraint-derived loci for all constraints.
/// This is a per-step predicate that captures the N×M precondition
/// of the soundness theorem in a modular form.
pub open spec fn step_satisfies_all_constraint_loci<T: OrderedField>(
    step: ConstructionStep<T>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
) -> bool {
    let target = step_target(step);
    forall|ci: int| 0 <= ci < constraints.len() ==>
        point_satisfies_locus(
            constraint_to_locus(#[trigger] constraints[ci], resolved, target),
            execute_step(step),
        )
}

/// Check that a plan is valid:
/// - Each step targets a unique entity.
/// - Each step's loci come from constraints that reference only
///   previously-resolved entities.
/// - Each step is well-formed.
pub open spec fn plan_valid<T: OrderedField>(
    plan: ConstructionPlan<T>,
    constraints: Seq<Constraint<T>>,
) -> bool {
    // Each step targets an entity not yet placed
    &&& forall|i: int, j: int|
        0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
        step_target(plan[i]) != step_target(plan[j])

    // Each step is well-formed
    &&& forall|i: int| 0 <= i < plan.len() ==>
        step_well_formed(#[trigger] plan[i])
}

/// A plan is "locus-ordered" for a set of constraints:
/// for every constructive (non-verification) constraint, every non-locus entity step
/// has a later locus entity step for the same constraint.
/// This ensures the last entity placed for each constructive constraint is always
/// a locus entity, which guarantees the locus is non-trivial at the critical step.
/// Verification constraints (Tangent, CircleTangent, Angle) are excluded because
/// they have empty locus entities and are checked separately.
pub open spec fn plan_locus_ordered<T: OrderedField>(
    plan: ConstructionPlan<T>,
    constraints: Seq<Constraint<T>>,
) -> bool {
    forall|ci: int, si: int|
        #![trigger plan[si], constraints[ci]]
        0 <= ci < constraints.len() && 0 <= si < plan.len() &&
        constraint_entities(constraints[ci]).contains(step_target(plan[si])) &&
        !constraint_locus_entities(constraints[ci]).contains(step_target(plan[si]))
        ==> (
            is_verification_constraint(constraints[ci])
            || exists|si_loc: int|
                si < si_loc < plan.len() &&
                constraint_locus_entities(constraints[ci]).contains(step_target(plan[si_loc]))
        )
}

// ===========================================================================
//  Main soundness theorem
// ===========================================================================

// ===========================================================================
//  Helper lemmas for plan soundness
// ===========================================================================

/// The domain of execute_plan contains exactly the step targets.
pub proof fn lemma_execute_plan_dom<T: OrderedField>(
    plan: ConstructionPlan<T>,
    k: EntityId,
)
    ensures
        execute_plan(plan).dom().contains(k) <==>
        exists|i: int| 0 <= i < plan.len() && step_target(#[trigger] plan[i]) == k,
    decreases plan.len(),
{
    if plan.len() == 0 {
    } else {
        let prefix = plan.drop_last();
        let n = (plan.len() - 1) as int;
        lemma_execute_plan_dom::<T>(prefix, k);
        // IH: execute_plan(prefix).dom().contains(k) <==>
        //     exists|i| 0 <= i < n && step_target(prefix[i]) == k

        // Connect prefix[i] == plan[i]
        assert forall|i: int| 0 <= i < n implies prefix[i] == plan[i] by {
            assert(prefix =~= plan.take(n));
        };

        // execute_plan(plan).dom().contains(k) iff
        //   k == step_target(plan[n]) || execute_plan(prefix).dom().contains(k)
        let last_target = step_target(plan[n]);

        if execute_plan(plan).dom().contains(k) {
            // → direction: find the witness i
            if k == last_target {
                assert(step_target(plan[n]) == k);
            } else {
                // k in prefix dom → exists i < n with step_target(prefix[i]) == k
                // → step_target(plan[i]) == k
            }
        }
        // ← direction is automatic from Map::insert semantics
    }
}

/// With distinct targets, step_target(plan[n]) is NOT in execute_plan(plan.take(n)).dom().
pub proof fn lemma_step_target_not_in_prefix<T: OrderedField>(
    plan: ConstructionPlan<T>,
    n: int,
)
    requires
        0 <= n < plan.len(),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
    ensures
        !execute_plan(plan.take(n)).dom().contains(step_target(plan[n])),
{
    let target = step_target(plan[n]);
    let prefix = plan.take(n);
    lemma_execute_plan_dom::<T>(prefix, target);
    // If target were in prefix.dom(), there'd be some i < n with step_target(prefix[i]) == target
    // But prefix[i] == plan[i] and step_target(plan[i]) != step_target(plan[n]) since i != n.
    assert forall|i: int| 0 <= i < prefix.len()
    implies step_target(#[trigger] prefix[i]) != target
    by {
        assert(prefix[i] == plan[i]);
        assert(i != n);
    };
}

/// execute_plan(plan.take(n+1)) == execute_plan(plan.take(n)).insert(target, result).
pub proof fn lemma_execute_plan_take_step<T: OrderedField>(
    plan: ConstructionPlan<T>,
    n: int,
)
    requires
        0 <= n < plan.len(),
    ensures
        execute_plan(plan.take(n + 1)) ==
        execute_plan(plan.take(n)).insert(
            step_target(plan[n]), execute_step(plan[n]),
        ),
{
    let sub = plan.take(n + 1);
    // sub.len() == n + 1 > 0
    // sub.drop_last() == plan.take(n)
    // sub.last() == plan[n]
    assert(sub.drop_last() =~= plan.take(n));
    assert(sub.last() == plan[n]);
    // execute_plan(sub) = execute_plan(sub.drop_last()).insert(step_target(sub.last()), execute_step(sub.last()))
}

/// Iterated frame lemma: constraint satisfied at step n remains satisfied at step m > n.
proof fn lemma_constraint_frame_chain<T: OrderedField>(
    c: Constraint<T>,
    plan: ConstructionPlan<T>,
    from: int,
    to: int,
)
    requires
        0 <= from <= to <= plan.len(),
        constraint_satisfied(c, execute_plan(plan.take(from))),
        // None of the steps from `from` to `to-1` target entities in c
        forall|si: int| from <= si < to ==>
            !constraint_entities(c).contains(step_target(#[trigger] plan[si])),
    ensures
        constraint_satisfied(c, execute_plan(plan.take(to))),
    decreases to - from,
{
    if from == to {
        // Trivial
    } else {
        // First, chain from `from` to `to - 1`
        lemma_constraint_frame_chain::<T>(c, plan, from, to - 1);
        // Now go from to-1 to to using frame lemma
        lemma_execute_plan_take_step::<T>(plan, to - 1);
        // execute_plan(plan.take(to)) == execute_plan(plan.take(to-1)).insert(target, result)
        let target = step_target(plan[to - 1]);
        assert(!constraint_entities(c).contains(target));
        lemma_constraint_frame(
            c,
            execute_plan(plan.take(to - 1)),
            target,
            execute_step(plan[to - 1]),
        );
    }
}

// ===========================================================================
//  Main soundness theorem
// ===========================================================================

/// If a plan is valid and each step satisfies the constraint-derived loci,
/// then the final resolved map satisfies all constraints.
/// Verification constraints (Tangent, CircleTangent, Angle) are assumed to be
/// directly satisfied by the final positions.
pub proof fn lemma_valid_plan_satisfies_constraints<T: OrderedField>(
    plan: ConstructionPlan<T>,
    constraints: Seq<Constraint<T>>,
)
    requires
        plan_valid(plan, constraints),
        plan_locus_ordered(plan, constraints),
        // All constraints are well-formed (no degenerate entity overlaps)
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_well_formed(#[trigger] constraints[ci]),
        // Every constraint's entities appear in the plan
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_entities(constraints[ci]).subset_of(
                execute_plan(plan).dom()
            ),
        // Each step satisfies all constraint-derived loci
        forall|si: int| 0 <= si < plan.len() ==>
            step_satisfies_all_constraint_loci(
                #[trigger] plan[si],
                constraints,
                execute_plan(plan.take(si as int)),
            ),
        // Verification constraints are directly satisfied
        forall|ci: int| 0 <= ci < constraints.len()
            && is_verification_constraint(#[trigger] constraints[ci])
            ==> constraint_satisfied(constraints[ci], execute_plan(plan)),
    ensures
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_satisfied(constraints[ci], execute_plan(plan)),
{
    assert forall|ci: int| 0 <= ci < constraints.len()
    implies constraint_satisfied(#[trigger] constraints[ci], execute_plan(plan))
    by {
        if is_verification_constraint(constraints[ci]) {
            // Directly from the new precondition
        } else {
            lemma_constraint_satisfied_by_plan::<T>(plan, constraints, ci);
        }
    };
}

/// Helper: show a single constructive constraint is satisfied by the plan.
proof fn lemma_constraint_satisfied_by_plan<T: OrderedField>(
    plan: ConstructionPlan<T>,
    constraints: Seq<Constraint<T>>,
    ci: int,
)
    requires
        0 <= ci < constraints.len(),
        !is_verification_constraint(constraints[ci]),
        plan_valid(plan, constraints),
        plan_locus_ordered(plan, constraints),
        constraint_well_formed(constraints[ci]),
        constraint_entities(constraints[ci]).subset_of(execute_plan(plan).dom()),
        forall|si: int| 0 <= si < plan.len() ==>
            step_satisfies_all_constraint_loci(
                #[trigger] plan[si],
                constraints,
                execute_plan(plan.take(si as int)),
            ),
    ensures
        constraint_satisfied(constraints[ci], execute_plan(plan)),
{
    let c = constraints[ci];
    let entities = constraint_entities(c);

    // Find the last step placing an entity of c
    let si_last = lemma_find_last_entity_step::<T>(plan, c, constraints, ci);

    let target = step_target(plan[si_last]);
    let resolved = execute_plan(plan.take(si_last));

    // target is an entity of c
    // All other entities of c are in resolved.dom() (placed by earlier steps)

    // The locus at this step
    let locus = constraint_to_locus(c, resolved, target);

    // step satisfies the locus (from per-step predicate)
    assert(step_satisfies_all_constraint_loci(plan[si_last], constraints, resolved));
    assert(step_satisfies_locus(plan[si_last], locus));

    // The locus is non-trivial because:
    // - target ∈ entities
    // - entities.remove(target) ⊆ resolved.dom()
    // - constraint_to_locus returns a non-FullPlane locus when all other entities are resolved
    //   and the target is a proper entity of the constraint

    // target not in resolved.dom()
    lemma_step_target_not_in_prefix::<T>(plan, si_last);

    // The locus is non-trivial — need to show this.
    // constraint_to_locus(c, resolved, target) returns a non-FullPlane locus when:
    //   target is a proper entity of c AND all other entities are in resolved.dom()
    //   AND target is not in resolved.dom()
    // This is guaranteed by our find_last_entity_step construction.
    lemma_last_step_locus_nontrivial::<T>(plan, c, si_last);

    // Apply lemma_locus_sound
    let p = execute_step(plan[si_last]);
    assert(point_satisfies_locus(locus, p));
    lemma_locus_sound(c, resolved, target, p);
    // Now: constraint_satisfied(c, resolved.insert(target, p))

    // resolved.insert(target, p) == execute_plan(plan.take(si_last + 1))
    lemma_execute_plan_take_step::<T>(plan, si_last);

    // Frame: constraint_satisfied persists from step si_last+1 to plan.len()
    // Need: none of steps si_last+1 .. plan.len()-1 target entities of c
    // This is guaranteed because si_last was the LAST step placing an entity of c.
    lemma_constraint_frame_chain(
        c, plan, si_last + 1, plan.len() as int,
    );

    // execute_plan(plan.take(plan.len())) == execute_plan(plan)
    assert(plan.take(plan.len() as int) =~= plan);
}

/// Find the last step placing an entity of constraint c.
/// With `plan_locus_ordered`, this step always targets a locus entity.
/// Only valid for constructive (non-verification) constraints.
proof fn lemma_find_last_entity_step<T: OrderedField>(
    plan: ConstructionPlan<T>,
    c: Constraint<T>,
    constraints: Seq<Constraint<T>>,
    ci: int,
) -> (si_last: int)
    requires
        0 <= ci < constraints.len(),
        constraints[ci] == c,
        !is_verification_constraint(c),
        constraint_entities(c).subset_of(execute_plan(plan).dom()),
        constraint_well_formed(c),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
        plan_locus_ordered(plan, constraints),
    ensures
        0 <= si_last < plan.len(),
        constraint_entities(c).contains(step_target(plan[si_last])),
        constraint_locus_entities(c).contains(step_target(plan[si_last])),
        constraint_entities(c).remove(step_target(plan[si_last])).subset_of(
            execute_plan(plan.take(si_last)).dom()
        ),
        // No later step targets ANY entity of c
        forall|si: int| si_last < si < plan.len() ==>
            !constraint_entities(c).contains(step_target(#[trigger] plan[si])),
{
    let entities = constraint_entities(c);
    let locus_entities = constraint_locus_entities(c);

    // Find the last step placing ANY entity of c.
    let si_last = lemma_find_max_entity_step_idx::<T>(plan, c);

    let target = step_target(plan[si_last]);

    // Prove target is a locus entity by contradiction.
    // If target is a non-locus entity, plan_locus_ordered gives a later locus entity step.
    // But locus entities ⊆ entities, contradicting si_last being the last entity step.
    if !locus_entities.contains(target) {
        // plan_locus_ordered: since target ∈ entities but ∉ locus_entities,
        // we get: is_verification_constraint(c) || exists si_loc > si_last with locus entity.
        // Since !is_verification_constraint(c) (precondition), the existential must hold.
        assert(!is_verification_constraint(constraints[ci]));
        let si_loc = choose|si_loc: int|
            si_last < si_loc < plan.len() &&
            locus_entities.contains(step_target(plan[si_loc]));
        // locus entities ⊆ entities
        lemma_locus_entities_subset_entities(c);
        assert(entities.contains(step_target(plan[si_loc])));
        // But si_loc > si_last and no step after si_last has an entity of c
        assert(false); // contradiction
    }

    // si_last is the LAST step for ALL entities, so every other entity is in the prefix.
    assert forall|k: EntityId|
        entities.contains(k) && k != target
    implies execute_plan(plan.take(si_last)).dom().contains(k)
    by {
        lemma_execute_plan_dom::<T>(plan, k);
        let si_k = choose|si: int| 0 <= si < plan.len() && step_target(plan[si]) == k;
        assert(si_k != si_last);
        // si_k can't be > si_last (postcondition of find_max_entity_step_idx)
        assert(si_k < si_last);

        lemma_execute_plan_dom::<T>(plan.take(si_last), k);
        assert(plan.take(si_last)[si_k] == plan[si_k]);
    };

    si_last
}

/// Find the maximum step index that places an entity of c.
proof fn lemma_find_max_entity_step_idx<T: OrderedField>(
    plan: ConstructionPlan<T>,
    c: Constraint<T>,
) -> (max_idx: int)
    requires
        constraint_entities(c).subset_of(execute_plan(plan).dom()),
        forall|i: int, j: int|
            0 <= i < plan.len() && 0 <= j < plan.len() && i != j ==>
            step_target(plan[i]) != step_target(plan[j]),
    ensures
        0 <= max_idx < plan.len(),
        constraint_entities(c).contains(step_target(plan[max_idx])),
        forall|si: int| max_idx < si < plan.len() ==>
            !constraint_entities(c).contains(step_target(#[trigger] plan[si])),
    decreases plan.len(),
{
    let entities = constraint_entities(c);
    let n = plan.len();

    if n == 0 {
        // entities ⊆ Map::empty().dom() is impossible if entities is nonempty
        // But constraint_entities always returns a nonempty set
        // This case is unreachable
        assert(execute_plan(plan) == Map::<EntityId, Point2<T>>::empty());
        // entities.subset_of(empty.dom()) means entities is empty
        // But every constraint has at least one entity — contradiction
        // We need to show constraint_entities is nonempty for any constraint.
        lemma_constraint_entities_nonempty(c);
        // Now: entities has some element e, e ∈ empty.dom() — contradiction
        let e = entities.choose();
        assert(false); // unreachable
        0 // dummy
    } else {
        let last_target = step_target(plan[n - 1]);
        if entities.contains(last_target) {
            // Check if any entity of c is placed even later — no, this IS the last step
            // Is n-1 the max? Only if no later step places an entity of c.
            // But n-1 IS the last step, so trivially no later step exists.
            (n - 1) as int
        } else {
            // Last step doesn't place an entity of c
            // entities ⊆ execute_plan(plan).dom()
            // execute_plan(plan) = execute_plan(prefix).insert(last_target, ...)
            // Since last_target ∉ entities, entities ⊆ execute_plan(prefix).dom()
            let prefix = plan.drop_last();
            assert(prefix =~= plan.take((n - 1) as int));

            // Show entities ⊆ execute_plan(prefix).dom()
            assert forall|k: EntityId| entities.contains(k)
            implies execute_plan(prefix).dom().contains(k)
            by {
                assert(execute_plan(plan).dom().contains(k));
                // execute_plan(plan) = execute_plan(prefix).insert(last_target, ...)
                // k ∈ dom iff k == last_target or k ∈ execute_plan(prefix).dom()
                // k != last_target since k ∈ entities and last_target ∉ entities
                assert(k != last_target);
            };

            // Recurse on prefix
            let max_idx = lemma_find_max_entity_step_idx::<T>(prefix, c);
            // max_idx < prefix.len() = n - 1
            assert(prefix[max_idx] == plan[max_idx]);

            // No step from max_idx+1 to n-2 in prefix places an entity
            // Plus step n-1 doesn't place an entity (last_target ∉ entities)
            // So no step from max_idx+1 to n-1 places an entity
            assert forall|si: int| max_idx < si < plan.len()
            implies !entities.contains(step_target(#[trigger] plan[si]))
            by {
                if si < n - 1 {
                    assert(plan[si] == prefix[si]);
                }
                // si == n - 1: last_target ∉ entities
            };

            max_idx
        }
    }
}

/// Every constraint has at least one entity.
proof fn lemma_constraint_entities_nonempty<T: OrderedField>(c: Constraint<T>)
    ensures
        constraint_entities(c).len() > 0,
{
    match c {
        Constraint::Coincident { a, b } => {
            assert(constraint_entities(c).contains(a));
        }
        Constraint::DistanceSq { a, b, .. } => {
            assert(constraint_entities(c).contains(a));
        }
        Constraint::FixedX { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
        Constraint::FixedY { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
        Constraint::SameX { a, b } => {
            assert(constraint_entities(c).contains(a));
        }
        Constraint::SameY { a, b } => {
            assert(constraint_entities(c).contains(a));
        }
        Constraint::PointOnLine { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
        Constraint::EqualLengthSq { a1, .. } => {
            assert(constraint_entities(c).contains(a1));
        }
        Constraint::Midpoint { mid, .. } => {
            assert(constraint_entities(c).contains(mid));
        }
        Constraint::Perpendicular { a1, .. } => {
            assert(constraint_entities(c).contains(a1));
        }
        Constraint::Parallel { a1, .. } => {
            assert(constraint_entities(c).contains(a1));
        }
        Constraint::Collinear { a, .. } => {
            assert(constraint_entities(c).contains(a));
        }
        Constraint::PointOnCircle { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
        Constraint::Symmetric { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
        Constraint::FixedPoint { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
        Constraint::Ratio { a1, .. } => {
            assert(constraint_entities(c).contains(a1));
        }
        Constraint::Tangent { line_a, .. } => {
            assert(constraint_entities(c).contains(line_a));
        }
        Constraint::CircleTangent { c1, .. } => {
            assert(constraint_entities(c).contains(c1));
        }
        Constraint::Angle { a1, .. } => {
            assert(constraint_entities(c).contains(a1));
        }
        Constraint::NotCoincident { a, .. } => {
            assert(constraint_entities(c).contains(a));
        }
        Constraint::NormalToCircle { line_a, .. } => {
            assert(constraint_entities(c).contains(line_a));
        }
        Constraint::PointOnEllipse { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
        Constraint::PointOnArc { point, .. } => {
            assert(constraint_entities(c).contains(point));
        }
    }
}

/// constraint_locus_entities is a subset of constraint_entities.
proof fn lemma_locus_entities_subset_entities<T: OrderedField>(c: Constraint<T>)
    ensures
        constraint_locus_entities(c).subset_of(constraint_entities(c)),
{
    let le = constraint_locus_entities(c);
    let e = constraint_entities(c);
    assert forall|k: EntityId| le.contains(k) implies e.contains(k) by {
        match c {
            Constraint::PointOnLine { point, line_a, line_b } => {
                // le = set![point], e = set![point, line_a, line_b]
                assert(le.contains(k) ==> k == point);
            }
            Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
                // le = set![a1, a2], e = set![a1, a2, b1, b2]
                assert(le.contains(k) ==> k == a1 || k == a2);
            }
            Constraint::Perpendicular { a1, a2, b1, b2 } => {
                // le = set![a1, a2], e = set![a1, a2, b1, b2]
                assert(le.contains(k) ==> k == a1 || k == a2);
            }
            Constraint::Parallel { a1, a2, b1, b2 } => {
                // le = set![a1, a2], e = set![a1, a2, b1, b2]
                assert(le.contains(k) ==> k == a1 || k == a2);
            }
            Constraint::PointOnCircle { point, center, radius_point } => {
                // le = set![point], e = set![point, center, radius_point]
                assert(le.contains(k) ==> k == point);
            }
            Constraint::Symmetric { point, original, axis_a, axis_b } => {
                // le = set![point], e = set![point, original, axis_a, axis_b]
                assert(le.contains(k) ==> k == point);
            }
            _ => {} // le == e for all other constraints
        }
    };
}

/// The locus at the critical entity step is non-trivial.
proof fn lemma_last_step_locus_nontrivial<T: OrderedField>(
    plan: ConstructionPlan<T>,
    c: Constraint<T>,
    si_last: int,
)
    requires
        0 <= si_last < plan.len(),
        constraint_well_formed(c),
        constraint_entities(c).contains(step_target(plan[si_last])),
        constraint_locus_entities(c).contains(step_target(plan[si_last])),
        constraint_entities(c).remove(step_target(plan[si_last])).subset_of(
            execute_plan(plan.take(si_last)).dom()
        ),
        !execute_plan(plan.take(si_last)).dom().contains(step_target(plan[si_last])),
    ensures
        locus_is_nontrivial(
            constraint_to_locus(
                c,
                execute_plan(plan.take(si_last)),
                step_target(plan[si_last]),
            )
        ),
{
    let target = step_target(plan[si_last]);
    let resolved = execute_plan(plan.take(si_last));
    match c {
        Constraint::Coincident { a, b } => {
            if target == a {
                assert(resolved.dom().contains(b));
            } else {
                assert(resolved.dom().contains(a));
            }
        }
        Constraint::DistanceSq { a, b, .. } => {
            if target == a {
                assert(resolved.dom().contains(b));
            } else {
                assert(resolved.dom().contains(a));
            }
        }
        Constraint::FixedX { point, .. } => {
            assert(target == point);
        }
        Constraint::FixedY { point, .. } => {
            assert(target == point);
        }
        Constraint::SameX { a, b } => {
            if target == a {
                assert(resolved.dom().contains(b));
            } else {
                assert(resolved.dom().contains(a));
            }
        }
        Constraint::SameY { a, b } => {
            if target == a {
                assert(resolved.dom().contains(b));
            } else {
                assert(resolved.dom().contains(a));
            }
        }
        Constraint::PointOnLine { point, line_a, line_b } => {
            // locus_entities = set![point], so target must be point
            // (if target were line_a or line_b, the locus_entities precondition would fail)
            assert(target == point);
            assert(resolved.dom().contains(line_a));
            assert(resolved.dom().contains(line_b));
        }
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            // locus_entities = set![a1, a2], so target must be a1 or a2
            if target == a1 {
                assert(resolved.dom().contains(a2));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            } else {
                assert(target == a2);
                assert(resolved.dom().contains(a1));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            }
        }
        Constraint::Midpoint { mid, a, b } => {
            if target == mid {
                assert(resolved.dom().contains(a));
                assert(resolved.dom().contains(b));
            } else if target == a {
                assert(resolved.dom().contains(mid));
                assert(resolved.dom().contains(b));
            } else {
                assert(target == b);
                assert(resolved.dom().contains(mid));
                assert(resolved.dom().contains(a));
            }
        }
        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            // locus_entities = set![a1, a2], so target must be a1 or a2
            if target == a1 {
                assert(resolved.dom().contains(a2));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            } else {
                assert(target == a2);
                assert(resolved.dom().contains(a1));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            }
        }
        Constraint::Parallel { a1, a2, b1, b2 } => {
            if target == a1 {
                assert(resolved.dom().contains(a2));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            } else {
                assert(target == a2);
                assert(resolved.dom().contains(a1));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            }
        }
        Constraint::Collinear { a, b, c } => {
            // locus_entities = {a, b, c}, so target is one of them
            if target == a {
                assert(resolved.dom().contains(b));
                assert(resolved.dom().contains(c));
            } else if target == b {
                assert(resolved.dom().contains(a));
                assert(resolved.dom().contains(c));
            } else {
                assert(target == c);
                assert(resolved.dom().contains(a));
                assert(resolved.dom().contains(b));
            }
        }
        Constraint::PointOnCircle { point, center, radius_point } => {
            // locus_entities = {point}, so target must be point
            assert(target == point);
            assert(resolved.dom().contains(center));
            assert(resolved.dom().contains(radius_point));
        }
        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            // locus_entities = {point}, so target must be point
            assert(target == point);
            assert(resolved.dom().contains(original));
            assert(resolved.dom().contains(axis_a));
            assert(resolved.dom().contains(axis_b));
        }
        Constraint::FixedPoint { point, .. } => {
            // locus_entities = {point}, so target must be point
            assert(target == point);
        }
        Constraint::Ratio { a1, a2, b1, b2, .. } => {
            // locus_entities = {a1, a2}, so target is a1 or a2
            if target == a1 {
                assert(resolved.dom().contains(a2));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            } else {
                assert(target == a2);
                assert(resolved.dom().contains(a1));
                assert(resolved.dom().contains(b1));
                assert(resolved.dom().contains(b2));
            }
        }
        Constraint::Tangent { .. } => {
            // Verification constraint: locus_entities = empty set.
            // Precondition constraint_locus_entities(c).contains(target) is false.
            assert(false);
        }
        Constraint::CircleTangent { .. } => {
            // Verification constraint: locus_entities = empty set.
            assert(false);
        }
        Constraint::Angle { .. } => {
            // Verification constraint: locus_entities = empty set.
            assert(false);
        }
        Constraint::NotCoincident { .. } => { assert(false); }
        Constraint::NormalToCircle { .. } => { assert(false); }
        Constraint::PointOnEllipse { .. } => { assert(false); }
        Constraint::PointOnArc { .. } => { assert(false); }
    }
}

// ===========================================================================
//  Locus extraction helpers
// ===========================================================================

/// Given a target entity and a list of constraints, collect all loci
/// imposed on the target (given the current resolved state).
pub open spec fn collect_loci<T: OrderedField>(
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
    target: EntityId,
) -> Seq<Locus2d<T>>
    decreases constraints.len(),
{
    if constraints.len() == 0 {
        Seq::empty()
    } else {
        let rest = collect_loci(constraints.drop_last(), resolved, target);
        let locus = constraint_to_locus(constraints.last(), resolved, target);
        rest.push(locus)
    }
}

/// Intersect two loci to produce a construction step.
/// Returns None if the intersection is underdetermined or impossible.
pub open spec fn intersect_loci<T: OrderedField>(
    id: EntityId,
    l1: Locus2d<T>,
    l2: Locus2d<T>,
) -> Option<ConstructionStep<T>> {
    match (l1, l2) {
        // AtPoint overrides everything
        (Locus2d::AtPoint(p), _) => Some(ConstructionStep::PointStep { id, position: p }),
        (_, Locus2d::AtPoint(p)) => Some(ConstructionStep::PointStep { id, position: p }),

        // Line-line
        (Locus2d::OnLine(line1), Locus2d::OnLine(line2)) => {
            if !line_det(line1, line2).eqv(T::zero()) {
                Some(ConstructionStep::LineLine { id, line1, line2 })
            } else {
                None // Parallel or coincident lines
            }
        }

        // Circle-line (either order)
        (Locus2d::OnCircle(circle), Locus2d::OnLine(line)) => {
            Some(ConstructionStep::CircleLine { id, circle, line, plus: true })
        }
        (Locus2d::OnLine(line), Locus2d::OnCircle(circle)) => {
            Some(ConstructionStep::CircleLine { id, circle, line, plus: true })
        }

        // Circle-circle
        (Locus2d::OnCircle(c1), Locus2d::OnCircle(c2)) => {
            Some(ConstructionStep::CircleCircle { id, circle1: c1, circle2: c2, plus: true })
        }

        // FullPlane doesn't constrain
        (Locus2d::FullPlane, other) => None,
        (_, Locus2d::FullPlane) => None,
    }
}

// ===========================================================================
//  Locus satisfaction by intersect_loci steps
// ===========================================================================

/// When intersect_loci produces a step from two geometric loci
/// (OnLine or OnCircle, neither AtPoint nor FullPlane),
/// the step satisfies both loci (given step_well_formed).
pub proof fn lemma_intersect_loci_satisfies_both<T: OrderedField>(
    id: EntityId, l1: Locus2d<T>, l2: Locus2d<T>,
)
    requires
        matches!(intersect_loci(id, l1, l2), Some(..)),
        !matches!(l1, Locus2d::AtPoint(..)),
        !matches!(l1, Locus2d::FullPlane),
        !matches!(l2, Locus2d::AtPoint(..)),
        !matches!(l2, Locus2d::FullPlane),
        step_well_formed(
            intersect_loci(id, l1, l2).unwrap(),
        ),
    ensures ({
        let step = intersect_loci(id, l1, l2).unwrap();
        let p = execute_step(step);
        point_satisfies_locus(l1, p) && point_satisfies_locus(l2, p)
    }),
{
    let step = intersect_loci(id, l1, l2).unwrap();
    match (l1, l2) {
        (Locus2d::OnLine(line1), Locus2d::OnLine(line2)) => {
            // LineLine: line_line_intersection_2d satisfies both lines
            use verus_geometry::line_intersection::lemma_ll_intersection_on_l1;
            use verus_geometry::line_intersection::lemma_ll_intersection_on_l2;
            lemma_ll_intersection_on_l1(line1, line2);
            lemma_ll_intersection_on_l2(line1, line2);
        }
        (Locus2d::OnCircle(circle), Locus2d::OnLine(line)) => {
            // CircleLine: execute_step = choose|p| on_circle && on_line
            // step_well_formed guarantees exists|p| on_circle && on_line
            // So the choose is valid and satisfies both
        }
        (Locus2d::OnLine(line), Locus2d::OnCircle(circle)) => {
            // Same as above (CircleLine with swapped order)
        }
        (Locus2d::OnCircle(c1), Locus2d::OnCircle(c2)) => {
            // CircleCircle: execute_step = choose|p| on_circle1 && on_circle2
            // step_well_formed guarantees existence
        }
        _ => {
            // AtPoint/FullPlane excluded by preconditions
        }
    }
}

/// When intersect_loci produces a PointStep from an AtPoint locus,
/// the step satisfies that AtPoint locus (by eqv reflexivity).
pub proof fn lemma_intersect_loci_satisfies_atpoint<T: OrderedField>(
    id: EntityId, p: Point2<T>, other: Locus2d<T>,
)
    ensures
        point_satisfies_locus(
            Locus2d::AtPoint(p),
            execute_step(ConstructionStep::<T>::PointStep { id, position: p }),
        ),
{
    // Need p.eqv(p) — component-wise reflexivity
    T::axiom_eqv_reflexive(p.x);
    T::axiom_eqv_reflexive(p.y);
}

// ===========================================================================
//  Solver bridge lemma
// ===========================================================================

/// Bridge: if a step satisfies all nontrivial loci for its target,
/// it satisfies ALL loci (because FullPlane is trivially satisfied).
/// This allows the solver to only check nontrivial loci and conclude
/// step_satisfies_all_constraint_loci.
pub proof fn lemma_nontrivial_loci_imply_all_satisfied<T: OrderedField>(
    step: ConstructionStep<T>,
    constraints: Seq<Constraint<T>>,
    resolved: ResolvedPoints<T>,
)
    requires
        forall|ci: int| 0 <= ci < constraints.len()
            && locus_is_nontrivial(
                constraint_to_locus(#[trigger] constraints[ci], resolved, step_target(step)))
            ==> point_satisfies_locus(
                constraint_to_locus(constraints[ci], resolved, step_target(step)),
                execute_step(step)),
    ensures
        step_satisfies_all_constraint_loci(step, constraints, resolved),
{
    assert forall|ci: int| 0 <= ci < constraints.len()
    implies point_satisfies_locus(
        constraint_to_locus(#[trigger] constraints[ci], resolved, step_target(step)),
        execute_step(step))
    by {
        let locus = constraint_to_locus(constraints[ci], resolved, step_target(step));
        if locus_is_nontrivial(locus) {
            // Satisfied by precondition
        } else {
            // FullPlane: point_satisfies_locus(FullPlane, _) == true by definition
        }
    };
}

// ===========================================================================
//  End-to-end theorem
// ===========================================================================

/// Master end-to-end theorem:
/// If a valid, locus-ordered plan exists where each step satisfies its
/// constraint-derived loci, then executing the plan satisfies all constraints.
///
/// This is the main soundness guarantee. The greedy solver (in solver.rs)
/// produces plans with distinct targets; if additionally every step satisfies
/// its loci (which lemma_intersect_loci_satisfies_both guarantees for
/// geometric locus pairs), the resulting execution satisfies all constraints.
///
/// Verification constraints (Tangent, CircleTangent, Angle) must be checked
/// separately because they have no locus entities and cannot be constructively placed.
pub proof fn lemma_end_to_end<T: OrderedField>(
    plan: ConstructionPlan<T>,
    constraints: Seq<Constraint<T>>,
)
    requires
        // Plan validity
        plan_valid(plan, constraints),
        plan_locus_ordered(plan, constraints),
        // All constraints are well-formed
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_well_formed(#[trigger] constraints[ci]),
        // Every constraint's entities appear in the plan
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_entities(constraints[ci]).subset_of(
                execute_plan(plan).dom()
            ),
        // Each step satisfies all constraint-derived loci
        forall|si: int| 0 <= si < plan.len() ==>
            step_satisfies_all_constraint_loci(
                #[trigger] plan[si],
                constraints,
                execute_plan(plan.take(si as int)),
            ),
        // Verification constraints are directly satisfied
        forall|ci: int| 0 <= ci < constraints.len()
            && is_verification_constraint(#[trigger] constraints[ci])
            ==> constraint_satisfied(constraints[ci], execute_plan(plan)),
    ensures
        // All constraints are satisfied by the executed plan
        forall|ci: int| 0 <= ci < constraints.len() ==>
            constraint_satisfied(#[trigger] constraints[ci], execute_plan(plan)),
{
    lemma_valid_plan_satisfies_constraints(plan, constraints);
}

// ===========================================================================
//  Extension field step execution
// ===========================================================================

/// Lift a construction step from F to SpecQuadExt<F, R>.
pub open spec fn lift_construction_step<F: OrderedField, R: PositiveRadicand<F>>(
    step: ConstructionStep<F>,
) -> ConstructionStep<SpecQuadExt<F, R>> {
    match step {
        ConstructionStep::PointStep { id, position } =>
            ConstructionStep::PointStep { id, position: lift_point2(position) },
        ConstructionStep::LineLine { id, line1, line2 } =>
            ConstructionStep::LineLine { id, line1: lift_line2(line1), line2: lift_line2(line2) },
        ConstructionStep::CircleLine { id, circle, line, plus } =>
            ConstructionStep::CircleLine { id, circle: lift_circle2(circle), line: lift_line2(line), plus },
        ConstructionStep::CircleCircle { id, circle1, circle2, plus } =>
            ConstructionStep::CircleCircle { id, circle1: lift_circle2(circle1), circle2: lift_circle2(circle2), plus },
    }
}

/// **Canonical deterministic** execution of a construction step in Q(√R).
///
/// Unlike `execute_step` (which uses `choose` for circle steps), this function
/// is fully deterministic: circle intersections use `cl_intersection_point` /
/// `cc_intersection_point` with the `plus` flag to select a specific solution.
/// This works because `SpecQuadExt<F, R>` supports √R, enabling closed-form
/// intersection formulas.
///
/// The soundness theorem (`lemma_solver_to_soundness_det`) and the main ensures
/// on `solve_and_verify<R>` are stated in terms of `execute_plan_in_ext`, making
/// this the primary spec for constraint satisfaction guarantees.
pub open spec fn execute_step_in_ext<F: OrderedField, R: PositiveRadicand<F>>(
    step: ConstructionStep<F>,
) -> Point2<SpecQuadExt<F, R>> {
    match step {
        ConstructionStep::PointStep { position, .. } => lift_point2(position),
        ConstructionStep::LineLine { line1, line2, .. } =>
            lift_point2(line_line_intersection_2d(line1, line2)),
        ConstructionStep::CircleLine { circle, line, plus, .. } =>
            cl_intersection_point::<F, R>(circle, line, plus),
        ConstructionStep::CircleCircle { circle1, circle2, plus, .. } =>
            cc_intersection_point::<F, R>(circle1, circle2, plus),
    }
}

// ===========================================================================
//  Lifting lemmas
// ===========================================================================

/// Lifting preserves step_target.
pub proof fn lemma_lift_step_target<F: OrderedField, R: PositiveRadicand<F>>(
    step: ConstructionStep<F>,
)
    ensures
        step_target(lift_construction_step::<F, R>(step)) == step_target(step),
{
    // Each arm has the same `id` field — trivial by match.
}

/// THE KEY RESULT: lifting a step with positive discriminant and matching
/// radicand produces a well-formed step at the extension field level.
///
/// This closes the gap: the runtime proves geometric validity + positive
/// discriminant at T=Rational, and this lemma shows the existential in
/// step_well_formed is satisfiable at T=SpecQuadExt<Rational, R>.
pub proof fn lemma_lifted_step_well_formed<F: OrderedField, R: PositiveRadicand<F>>(
    step: ConstructionStep<F>,
)
    requires
        // Geometric preconditions (non-degenerate lines, distinct centers, non-parallel)
        match step {
            ConstructionStep::LineLine { line1, line2, .. } =>
                !line_det(line1, line2).eqv(F::zero()),
            ConstructionStep::CircleLine { line, .. } =>
                line2_nondegenerate(line),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                !circle1.center.eqv(circle2.center),
            _ => true,
        },
        // Positive discriminant for circle steps
        match step {
            ConstructionStep::CircleLine { circle, line, .. } =>
                F::zero().lt(cl_discriminant(circle, line)),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                F::zero().lt(cc_discriminant(circle1, circle2)),
            _ => true,
        },
        // Radicand matches discriminant for circle steps
        match step {
            ConstructionStep::CircleLine { circle, line, .. } =>
                R::value().eqv(cl_discriminant(circle, line)),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                R::value().eqv(cc_discriminant(circle1, circle2)),
            _ => true,
        },
    ensures
        step_well_formed(
            lift_construction_step::<F, R>(step),
        ),
{
    match step {
        ConstructionStep::PointStep { .. } => {
            // Trivially true
        }

        ConstructionStep::LineLine { id, line1, line2 } => {
            lemma_lifted_ll_well_formed::<F, R>(line1, line2);
        }

        ConstructionStep::CircleLine { id, circle, line, plus } => {
            lemma_lifted_cl_well_formed::<F, R>(circle, line, plus);
        }

        ConstructionStep::CircleCircle { id, circle1, circle2, plus } => {
            lemma_lifted_cc_well_formed::<F, R>(circle1, circle2, plus);
        }
    }
}

/// Helper: LineLine case of lemma_lifted_step_well_formed.
proof fn lemma_lifted_ll_well_formed<F: OrderedField, R: PositiveRadicand<F>>(
    line1: Line2<F>,
    line2: Line2<F>,
)
    requires
        !line_det(line1, line2).eqv(F::zero()),
    ensures
        !line_det(lift_line2::<F, R>(line1), lift_line2::<F, R>(line2)).eqv(
            SpecQuadExt::<F, R>::zero()
        ),
{
    // line_det(lift(l1), lift(l2)) ≡ qext_from_rational(line_det(l1, l2))
    lemma_lift_line_det::<F, R>(line1, line2);

    // Suppose for contradiction that line_det(lift(l1), lift(l2)).eqv(QE::zero())
    // QE::zero() = qext_from_rational(F::zero())
    // By transitivity + symmetry: qext_from_rational(line_det(l1,l2)).eqv(qext_from_rational(F::zero()))
    // By injectivity: line_det(l1,l2).eqv(F::zero()) — contradiction
    if line_det(lift_line2::<F, R>(line1), lift_line2::<F, R>(line2)).eqv(
        SpecQuadExt::<F, R>::zero()
    ) {
        // line_det(lift) ≡ qext_from_rational(line_det(l1,l2))
        // line_det(lift) ≡ QE::zero() = qext_from_rational(F::zero())
        // So qext_from_rational(line_det) ≡ qext_from_rational(F::zero())
        SpecQuadExt::<F, R>::axiom_eqv_symmetric(
            line_det(lift_line2::<F, R>(line1), lift_line2::<F, R>(line2)),
            qext_from_rational::<F, R>(line_det(line1, line2)),
        );
        F::axiom_eqv_reflexive(F::zero());
        SpecQuadExt::<F, R>::axiom_eqv_transitive(
            qext_from_rational::<F, R>(line_det(line1, line2)),
            line_det(lift_line2::<F, R>(line1), lift_line2::<F, R>(line2)),
            qext_from_rational::<F, R>(F::zero()),
        );
        lemma_qext_from_rational_injective::<F, R>(line_det(line1, line2), F::zero());
        // Now line_det(l1, l2).eqv(F::zero()) — contradicts requires
    }
}

/// Helper: CircleLine case of lemma_lifted_step_well_formed.
proof fn lemma_lifted_cl_well_formed<F: OrderedField, R: PositiveRadicand<F>>(
    circle: Circle2<F>,
    line: Line2<F>,
    plus: bool,
)
    requires
        line2_nondegenerate(line),
        F::zero().lt(cl_discriminant(circle, line)),
        R::value().eqv(cl_discriminant(circle, line)),
    ensures
        line2_nondegenerate(lift_line2::<F, R>(line)),
        exists|p: Point2<SpecQuadExt<F, R>>|
            point_on_circle2(lift_circle2::<F, R>(circle), p)
            && point_on_line2(lift_line2::<F, R>(line), p),
{
    // Nondegeneracy preserved
    lemma_lift_line2_nondegenerate::<F, R>(line);

    // Witness: p = cl_intersection_point(circle, line, plus)
    let p = cl_intersection_point::<F, R>(circle, line, plus);

    // On line
    lemma_cl_intersection_on_line::<F, R>(circle, line, plus);
    // ensures: point_on_line2(lift_line2(line), p)

    // On circle: lemma gives sq_dist(p, lift(center)).eqv(qext_from_rational(r²))
    lemma_cl_intersection_on_circle::<F, R>(circle, line, plus);
    // ensures: sq_dist_2d(p, lift_point2(center)).eqv(qext_from_rational(circle.radius_sq))
    // This is exactly point_on_circle2(lift_circle2(circle), p) since:
    //   lift_circle2(circle).center = lift_point2(circle.center)
    //   lift_circle2(circle).radius_sq = qext_from_rational(circle.radius_sq)
    //   point_on_circle2 = sq_dist_2d(p, center).eqv(radius_sq)
}

/// Helper: CircleCircle case of lemma_lifted_step_well_formed.
proof fn lemma_lifted_cc_well_formed<F: OrderedField, R: PositiveRadicand<F>>(
    circle1: Circle2<F>,
    circle2: Circle2<F>,
    plus: bool,
)
    requires
        !circle1.center.eqv(circle2.center),
        F::zero().lt(cc_discriminant(circle1, circle2)),
        R::value().eqv(cc_discriminant(circle1, circle2)),
    ensures
        !lift_point2::<F, R>(circle1.center).eqv(lift_point2::<F, R>(circle2.center)),
        exists|p: Point2<SpecQuadExt<F, R>>|
            point_on_circle2(lift_circle2::<F, R>(circle1), p)
            && point_on_circle2(lift_circle2::<F, R>(circle2), p),
{
    // Centers distinct when lifted
    lemma_lift_centers_distinct::<F, R>(circle1.center, circle2.center);

    // Witness: p = cc_intersection_point(circle1, circle2, plus)
    let p = cc_intersection_point::<F, R>(circle1, circle2, plus);

    // On c1: sq_dist(p, lift(c1.center)).eqv(qext_from_rational(c1.radius_sq))
    lemma_cc_intersection_on_c1::<F, R>(circle1, circle2, plus);
    // Help Z3 see lift_circle2 unfolds to match the lemma conclusion
    assert(lift_circle2::<F, R>(circle1).center == lift_point2::<F, R>(circle1.center));
    assert(lift_circle2::<F, R>(circle1).radius_sq == qext_from_rational::<F, R>(circle1.radius_sq));
    assert(point_on_circle2(lift_circle2::<F, R>(circle1), p));

    // On c2: sq_dist(p, lift(c2.center)).eqv(qext_from_rational(c2.radius_sq))
    lemma_cc_intersection_on_c2::<F, R>(circle1, circle2, plus);
    assert(lift_circle2::<F, R>(circle2).center == lift_point2::<F, R>(circle2.center));
    assert(lift_circle2::<F, R>(circle2).radius_sq == qext_from_rational::<F, R>(circle2.radius_sq));
    assert(point_on_circle2(lift_circle2::<F, R>(circle2), p));
}

/// Geometric correctness of execute_step_in_ext: the computed point
/// satisfies the relevant loci (on circle, on line).
pub proof fn lemma_execute_step_in_ext_satisfies_loci<F: OrderedField, R: PositiveRadicand<F>>(
    step: ConstructionStep<F>,
)
    requires
        // Geometric validity
        match step {
            ConstructionStep::LineLine { line1, line2, .. } =>
                !line_det(line1, line2).eqv(F::zero()),
            ConstructionStep::CircleLine { line, .. } =>
                line2_nondegenerate(line),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                !circle1.center.eqv(circle2.center),
            _ => true,
        },
        // Positive discriminant for circle steps
        match step {
            ConstructionStep::CircleLine { circle, line, .. } =>
                F::zero().lt(cl_discriminant(circle, line)),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                F::zero().lt(cc_discriminant(circle1, circle2)),
            _ => true,
        },
        // Radicand matches discriminant for circle steps
        match step {
            ConstructionStep::CircleLine { circle, line, .. } =>
                R::value().eqv(cl_discriminant(circle, line)),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                R::value().eqv(cc_discriminant(circle1, circle2)),
            _ => true,
        },
    ensures
        match step {
            ConstructionStep::CircleLine { circle, line, .. } =>
                point_on_circle2(lift_circle2::<F, R>(circle), execute_step_in_ext::<F, R>(step))
                && point_on_line2(lift_line2::<F, R>(line), execute_step_in_ext::<F, R>(step)),
            ConstructionStep::CircleCircle { circle1, circle2, .. } =>
                point_on_circle2(lift_circle2::<F, R>(circle1), execute_step_in_ext::<F, R>(step))
                && point_on_circle2(lift_circle2::<F, R>(circle2), execute_step_in_ext::<F, R>(step)),
            _ => true,
        },
{
    match step {
        ConstructionStep::CircleLine { id, circle, line, plus } => {
            // execute_step_in_ext = cl_intersection_point(circle, line, plus)
            lemma_cl_intersection_on_circle::<F, R>(circle, line, plus);
            lemma_cl_intersection_on_line::<F, R>(circle, line, plus);
        }
        ConstructionStep::CircleCircle { id, circle1, circle2, plus } => {
            // execute_step_in_ext = cc_intersection_point(c1, c2, plus)
            lemma_cc_intersection_on_c1::<F, R>(circle1, circle2, plus);
            lemma_cc_intersection_on_c2::<F, R>(circle1, circle2, plus);
        }
        _ => {}
    }
}

} // verus!
