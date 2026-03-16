/// Abstract plan and dependency analysis for circle chains.
///
/// An AbstractPlanStep records the solver's decisions without resolved geometry:
/// target entity, step kind, and plus flag. The dependency analysis assigns
/// each step a "level" indicating how deep in the extension tower its
/// coordinates live.
use vstd::prelude::*;
use crate::runtime::constraint::RuntimeConstraint;
use crate::runtime::construction::RuntimeStepData;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Abstract plan types
// ═══════════════════════════════════════════════════════════════════

/// The kind of a construction step (without geometry data).
pub enum AbstractStepKind {
    /// Known position (x, y) — level 0.
    Point,
    /// Line-line intersection — level 0 (rational).
    LineLine,
    /// Circle-line intersection — level ≥ 1.
    CircleLine,
    /// Circle-circle intersection — level ≥ 1.
    CircleCircle,
}

/// Abstract construction step: records target + kind + plus flag.
///
/// Created by `extract_abstract_plan` from a RuntimeStepData plan.
/// Used for dependency analysis and multi-level execution dispatch.
pub struct AbstractPlanStep {
    pub target: usize,
    pub kind: AbstractStepKind,
    pub plus: bool,
}

/// Extract an abstract plan from a RuntimeStepData plan.
///
/// This is a trivial O(n) extraction that records the target, kind, and plus
/// flag from each step without copying geometry.
pub fn extract_abstract_plan(plan: &Vec<RuntimeStepData>) -> (out: Vec<AbstractPlanStep>)
    requires
        forall|i: int| 0 <= i < plan@.len() ==> (#[trigger] plan@[i]).wf_spec(),
    ensures
        out@.len() == plan@.len(),
{
    let mut result: Vec<AbstractPlanStep> = Vec::new();
    let mut i: usize = 0;

    while i < plan.len()
        invariant
            0 <= i <= plan@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < plan@.len() ==> (#[trigger] plan@[j]).wf_spec(),
        decreases plan@.len() - i,
    {
        let step = match &plan[i] {
            RuntimeStepData::PointStep { target, .. } => {
                AbstractPlanStep { target: *target, kind: AbstractStepKind::Point, plus: false }
            }
            RuntimeStepData::LineLine { target, .. } => {
                AbstractPlanStep { target: *target, kind: AbstractStepKind::LineLine, plus: false }
            }
            RuntimeStepData::CircleLine { target, plus, .. } => {
                AbstractPlanStep { target: *target, kind: AbstractStepKind::CircleLine, plus: *plus }
            }
            RuntimeStepData::CircleCircle { target, plus, .. } => {
                AbstractPlanStep { target: *target, kind: AbstractStepKind::CircleCircle, plus: *plus }
            }
        };
        result.push(step);
        i = i + 1;
    }
    result
}

// ═══════════════════════════════════════════════════════════════════
//  Constraint entity extraction
// ═══════════════════════════════════════════════════════════════════

/// Check if a constraint references a given entity ID.
///
/// Returns true if entity_id appears among the constraint's entity references.
pub fn constraint_references_entity(rc: &RuntimeConstraint, entity_id: usize) -> (out: bool)
{
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } =>
            *a == entity_id || *b == entity_id,
        RuntimeConstraint::DistanceSq { a, b, .. } =>
            *a == entity_id || *b == entity_id,
        RuntimeConstraint::FixedX { point, .. } =>
            *point == entity_id,
        RuntimeConstraint::FixedY { point, .. } =>
            *point == entity_id,
        RuntimeConstraint::SameX { a, b, .. } =>
            *a == entity_id || *b == entity_id,
        RuntimeConstraint::SameY { a, b, .. } =>
            *a == entity_id || *b == entity_id,
        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } =>
            *point == entity_id || *line_a == entity_id || *line_b == entity_id,
        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } =>
            *a1 == entity_id || *a2 == entity_id || *b1 == entity_id || *b2 == entity_id,
        RuntimeConstraint::Midpoint { mid, a, b, .. } =>
            *mid == entity_id || *a == entity_id || *b == entity_id,
        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } =>
            *a1 == entity_id || *a2 == entity_id || *b1 == entity_id || *b2 == entity_id,
        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } =>
            *a1 == entity_id || *a2 == entity_id || *b1 == entity_id || *b2 == entity_id,
        RuntimeConstraint::Collinear { a, b, c, .. } =>
            *a == entity_id || *b == entity_id || *c == entity_id,
        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } =>
            *point == entity_id || *center == entity_id || *radius_point == entity_id,
        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } =>
            *point == entity_id || *original == entity_id || *axis_a == entity_id || *axis_b == entity_id,
        RuntimeConstraint::FixedPoint { point, .. } =>
            *point == entity_id,
        RuntimeConstraint::Ratio { a1, a2, b1, b2, .. } =>
            *a1 == entity_id || *a2 == entity_id || *b1 == entity_id || *b2 == entity_id,
        RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, .. } =>
            *line_a == entity_id || *line_b == entity_id || *center == entity_id || *radius_point == entity_id,
        RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, .. } =>
            *c1 == entity_id || *rp1 == entity_id || *c2 == entity_id || *rp2 == entity_id,
        RuntimeConstraint::Angle { a1, a2, b1, b2, .. } =>
            *a1 == entity_id || *a2 == entity_id || *b1 == entity_id || *b2 == entity_id,
    }
}

/// Check if a constraint references any entity in the given set of targets
/// (other than exclude_id).
///
/// Used for dependency analysis: given a constraint that references target T,
/// does it also reference any circle step target?
pub fn constraint_references_any_of(
    rc: &RuntimeConstraint,
    circle_targets: &Vec<usize>,
    exclude_id: usize,
) -> (out: bool)
{
    let mut j: usize = 0;
    while j < circle_targets.len()
        invariant 0 <= j <= circle_targets@.len()
        decreases circle_targets@.len() - j
    {
        let ct = circle_targets[j];
        if ct != exclude_id && constraint_references_entity(rc, ct) {
            return true;
        }
        j = j + 1;
    }
    false
}

// ═══════════════════════════════════════════════════════════════════
//  Dependency analysis: compute step levels
// ═══════════════════════════════════════════════════════════════════

/// Compute the extension tower level for each step.
///
/// Returns a Vec of levels where:
///   - Level 0: PointStep or LineLine (rational coordinates)
///   - Level 1: CircleLine/CircleCircle where all input entities are rational
///   - Level k: CircleLine/CircleCircle where at least one input entity
///              is a circle step target at level (k-1)
///
/// Uses conservative analysis: for each circle step at target T, checks
/// ALL constraints referencing T (not just the paired ones) for references
/// to other circle step targets.
pub fn compute_step_levels(
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
) -> (out: Vec<usize>)
    ensures out@.len() == abstract_plan@.len()
{
    let n = abstract_plan.len();

    // First pass: collect circle step targets
    let mut circle_targets: Vec<usize> = Vec::new();
    let mut ci: usize = 0;
    while ci < n
        invariant 0 <= ci <= n, n == abstract_plan@.len()
        decreases n - ci
    {
        match &abstract_plan[ci].kind {
            AbstractStepKind::CircleLine | AbstractStepKind::CircleCircle => {
                circle_targets.push(abstract_plan[ci].target);
            }
            _ => {}
        }
        ci = ci + 1;
    }

    // Second pass: compute levels iteratively
    // levels[i] = level of step i
    let mut levels: Vec<usize> = Vec::new();

    // Initialize all levels
    let mut init_i: usize = 0;
    while init_i < n
        invariant 0 <= init_i <= n, n == abstract_plan@.len(), levels@.len() == init_i
        decreases n - init_i
    {
        match &abstract_plan[init_i].kind {
            AbstractStepKind::Point | AbstractStepKind::LineLine => {
                levels.push(0);
            }
            _ => {
                levels.push(1); // Default: at least level 1 for circle steps
            }
        }
        init_i = init_i + 1;
    }

    // Build target_id → step_index map (linear scan for each lookup)
    // Iterate: for each circle step, check if any input entity is a circle
    // target at a higher level, and update accordingly.
    // Fixed-point iteration (converges in at most `n` passes).
    let mut changed = true;
    let mut pass: usize = 0;
    while changed && pass < n
        invariant
            0 <= pass <= n,
            n == abstract_plan@.len(),
            levels@.len() == n,
        decreases n - pass,
    {
        changed = false;
        let mut si: usize = 0;
        while si < n
            invariant
                0 <= si <= n,
                n == abstract_plan@.len(),
                levels@.len() == n,
            decreases n - si,
        {
            match &abstract_plan[si].kind {
                AbstractStepKind::CircleLine | AbstractStepKind::CircleCircle => {
                    let target = abstract_plan[si].target;
                    let mut max_dep_level: usize = 0;

                    // Check all constraints that reference this target
                    let mut cj: usize = 0;
                    while cj < constraints.len()
                        invariant
                            0 <= cj <= constraints@.len(),
                            n == abstract_plan@.len(),
                            levels@.len() == n,
                        decreases constraints@.len() - cj,
                    {
                        if constraint_references_entity(&constraints[cj], target) {
                            // Check all OTHER entities in this constraint
                            // Find the max level among circle targets referenced
                            let mut dk: usize = 0;
                            while dk < n
                                invariant
                                    0 <= dk <= n,
                                    n == abstract_plan@.len(),
                                    levels@.len() == n,
                                    (cj as int) < constraints@.len(),
                                decreases n - dk,
                            {
                                match &abstract_plan[dk].kind {
                                    AbstractStepKind::CircleLine | AbstractStepKind::CircleCircle => {
                                        let dep_target = abstract_plan[dk].target;
                                        if dep_target != target
                                            && constraint_references_entity(&constraints[cj], dep_target)
                                        {
                                            if levels[dk] > max_dep_level {
                                                max_dep_level = levels[dk];
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                                dk = dk + 1;
                            }
                        }
                        cj = cj + 1;
                    }

                    // Saturating add: cap at n (can't have more levels than steps)
                    let new_level = if max_dep_level > 0 && max_dep_level < n {
                        max_dep_level + 1
                    } else if max_dep_level >= n {
                        n
                    } else {
                        1usize
                    };
                    if new_level > levels[si] {
                        let mut old = new_level;
                        levels.set_and_swap(si, &mut old);
                        changed = true;
                    }
                }
                _ => {}
            }
            si = si + 1;
        }
        pass = pass + 1;
    }

    levels
}

/// Compute the maximum extension depth from step levels.
pub fn max_depth(levels: &Vec<usize>) -> (out: usize)
    ensures out == 0 ==> forall|i: int| 0 <= i < levels@.len() ==> levels@[i] == 0,
{
    let mut max_val: usize = 0;
    let mut i: usize = 0;
    while i < levels.len()
        invariant
            0 <= i <= levels@.len(),
            forall|j: int| 0 <= j < i ==> levels@[j] <= max_val,
            max_val == 0 ==> forall|j: int| 0 <= j < i ==> levels@[j] == 0,
        decreases levels@.len() - i,
    {
        if levels[i] > max_val {
            max_val = levels[i];
        }
        i = i + 1;
    }
    max_val
}

// ═══════════════════════════════════════════════════════════════════
//  Constraint pair extraction
// ═══════════════════════════════════════════════════════════════════

/// Find two constraint indices that reference a target entity.
///
/// Scans through constraints looking for two that reference target_id.
/// Returns (ci1, ci2) or None if fewer than two constraints reference it.
/// For non-circle steps, returns (0, 0) as a dummy.
fn find_two_constraints_for_target(
    constraints: &Vec<RuntimeConstraint>,
    target_id: usize,
) -> (out: Option<(usize, usize)>)
    ensures
        out.is_some() ==> ({
            let (a, b) = out.unwrap();
            a < constraints@.len() && b < constraints@.len() && a != b
        }),
{
    let mut first: usize = 0;
    let mut found_first = false;
    while first < constraints.len()
        invariant_except_break
            0 <= first <= constraints@.len(),
            !found_first,
        invariant
            0 <= first <= constraints@.len(),
        ensures
            found_first ==> (first as int) < constraints@.len(),
        decreases constraints@.len() - first,
    {
        if constraint_references_entity(&constraints[first], target_id) {
            found_first = true;
            break;
        }
        first = first + 1;
    }
    if !found_first {
        return None;
    }

    assert(first < constraints.len()); // from ensures above
    let mut second: usize = first + 1;
    let mut found_second = false;
    while second < constraints.len()
        invariant_except_break
            first < second && second <= constraints@.len(),
            !found_second,
        invariant
            (first as int) < constraints@.len(),
            first < second && second <= constraints@.len(),
        ensures
            found_second ==> (second as int) < constraints@.len(),
        decreases constraints@.len() - second,
    {
        if constraint_references_entity(&constraints[second], target_id) {
            found_second = true;
            break;
        }
        second = second + 1;
    }
    if !found_second {
        return None;
    }
    Some((first, second))
}

/// Extract constraint pairs for each step in the abstract plan.
///
/// For each circle step, finds two constraints that reference its target.
/// For non-circle steps (Point, LineLine), returns (0, 0) as a dummy.
/// Returns None if any circle step doesn't have two referencing constraints.
pub fn extract_constraint_pairs(
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
) -> (out: Option<Vec<(usize, usize)>>)
    ensures
        out.is_some() ==> out.unwrap()@.len() == abstract_plan@.len(),
{
    let mut pairs: Vec<(usize, usize)> = Vec::new();
    let mut i: usize = 0;
    while i < abstract_plan.len()
        invariant
            0 <= i <= abstract_plan@.len(),
            pairs@.len() == i,
        decreases abstract_plan@.len() - i,
    {
        match &abstract_plan[i].kind {
            AbstractStepKind::CircleLine | AbstractStepKind::CircleCircle => {
                let target = abstract_plan[i].target;
                match find_two_constraints_for_target(constraints, target) {
                    None => { return None; }
                    Some(pair) => { pairs.push(pair); }
                }
            }
            _ => {
                // Point/LineLine: dummy pair
                pairs.push((0usize, 0usize));
            }
        }
        i = i + 1;
    }
    Some(pairs)
}

} // verus!
