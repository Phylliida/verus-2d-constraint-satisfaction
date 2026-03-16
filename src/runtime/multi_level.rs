/// Multi-level executor for circle chain construction.
///
/// Executes construction steps level by level. At each level:
/// 1. Current positions are in field F_k
/// 2. For each circle step at this level, compute two constraint loci in F_k
/// 3. Intersect the loci → position in F_{k+1} = F_k(√d)
/// 4. Embed all positions to F_{k+1} and continue
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_geometry::runtime::point2::RuntimePoint2;
use verus_quadratic_extension::runtime_field::RuntimeFieldOps;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::runtime_qext::RuntimeQExt;
use verus_quadratic_extension::instances::*;
use verus_quadratic_extension::runtime_qext::{RuntimeDynL1, RuntimeDynL2, RuntimeDynL3};
use verus_quadratic_extension::dyn_tower::{DynTowerField, DynTowerRadicand};
use crate::runtime::constraint::*;
use crate::runtime::abstract_plan::*;
use crate::runtime::generic_point::*;
use crate::runtime::generic_locus::*;
use crate::runtime::generic_intersection::*;
use crate::runtime::dyn_field::{DynFieldElem, rational_to_dyn, collapse_to_dyn};

type RationalModel = verus_rational::rational::Rational;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Execute one level: loci in base field F, intersect → F(√d)
// ═══════════════════════════════════════════════════════════════════

/// Execute circle steps at a given level.
///
/// Computes loci in the base field F (where current positions live),
/// then intersects to produce points in F(√d). All positions are then
/// embedded from F to F(√d).
pub fn execute_circle_steps_at_level<
    FV: OrderedField,
    R: PositiveRadicand<FV>,
    F: RuntimeFieldOps<FV>,
>(
    positions: &Vec<GenericRtPoint2<FV, F>>,
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
    constraint_pairs: &Vec<(usize, usize)>,
    levels: &Vec<usize>,
    current_level: usize,
    radicand_rt: &F,
) -> (out: Option<Vec<GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>>>)
    requires
        radicand_rt.wf_spec(),
        radicand_rt.rf_view() == R::value(),
        abstract_plan@.len() == levels@.len(),
        abstract_plan@.len() == constraint_pairs@.len(),
        positions@.len() > 0,
        forall|i: int| 0 <= i < positions@.len() ==> (#[trigger] positions@[i]).wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], positions@.len() as nat),
    ensures
        out.is_some() ==> ({
            let r = out.unwrap();
            &&& r@.len() == positions@.len()
            &&& forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]).wf_spec()
        }),
{
    let n_entities = positions.len();

    // Build resolved flags: all true (all positions known at this level)
    let mut resolved_flags: Vec<bool> = Vec::new();
    let mut ri: usize = 0;
    while ri < n_entities
        invariant
            0 <= ri <= n_entities,
            resolved_flags@.len() == ri,
            n_entities == positions@.len(),
        decreases n_entities - ri,
    {
        resolved_flags.push(true);
        ri = ri + 1;
    }

    // Compute intersection points for circle steps at this level,
    // storing them as extension field points indexed by target entity.
    // We'll collect (target, point) pairs.
    let mut circle_results: Vec<(usize, GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>)> = Vec::new();

    let mut si: usize = 0;
    while si < abstract_plan.len()
        invariant
            0 <= si <= abstract_plan@.len(),
            n_entities == positions@.len(),
            resolved_flags@.len() == n_entities,
            abstract_plan@.len() == levels@.len(),
            abstract_plan@.len() == constraint_pairs@.len(),
            radicand_rt.wf_spec(),
            radicand_rt.rf_view() == R::value(),
            forall|i: int| 0 <= i < positions@.len() ==> (#[trigger] positions@[i]).wf_spec(),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], positions@.len() as nat),
            forall|j: int| 0 <= j < circle_results@.len() ==>
                (#[trigger] circle_results@[j]).1.wf_spec(),
        decreases abstract_plan@.len() - si,
    {
        if levels[si] == current_level {
            match &abstract_plan[si].kind {
                AbstractStepKind::CircleLine | AbstractStepKind::CircleCircle => {
                    let target = abstract_plan[si].target;
                    let plus = abstract_plan[si].plus;
                    let ci1 = constraint_pairs[si].0;
                    let ci2 = constraint_pairs[si].1;

                    if ci1 >= constraints.len() || ci2 >= constraints.len()
                        || target >= n_entities
                    {
                        return None;
                    }

                    // Need a template for rf_embed_rational
                    let template = positions[0].x.rf_copy();

                    // Compute loci in base field F
                    let locus1 = constraint_to_locus_generic::<FV, F>(
                        &constraints[ci1], positions, &resolved_flags, target, &template,
                    );
                    let locus2 = constraint_to_locus_generic::<FV, F>(
                        &constraints[ci2], positions, &resolved_flags, target, &template,
                    );

                    // Intersect: produces point in F(√d)
                    let intersection = intersect_loci::<FV, R, F>(
                        &locus1, &locus2, radicand_rt, plus,
                    );

                    match intersection {
                        None => { return None; }
                        Some(pt) => {
                            circle_results.push((target, pt));
                        }
                    }
                }
                _ => {} // Point/LineLine are level 0
            }
        }
        si = si + 1;
    }

    // Embed all positions from F to F(√d)
    let mut ext_positions = embed_points_to_ext::<FV, R, F>(positions, radicand_rt);

    // Overwrite circle step targets with computed intersection points
    let mut ci: usize = 0;
    while ci < circle_results.len()
        invariant
            0 <= ci <= circle_results@.len(),
            ext_positions@.len() == n_entities,
            n_entities == positions@.len(),
            forall|i: int| 0 <= i < ext_positions@.len() ==>
                (#[trigger] ext_positions@[i]).wf_spec(),
            forall|j: int| 0 <= j < circle_results@.len() ==>
                (#[trigger] circle_results@[j]).1.wf_spec(),
        decreases circle_results@.len() - ci,
    {
        let target = circle_results[ci].0;
        if target < n_entities {
            let pt = circle_results[ci].1.copy_point();
            let mut old = pt;
            ext_positions.set_and_swap(target, &mut old);
        }
        ci = ci + 1;
    }

    Some(ext_positions)
}

// ═══════════════════════════════════════════════════════════════════
//  Convert rational positions to GenericRtPoint2
// ═══════════════════════════════════════════════════════════════════

/// Convert RuntimePoint2 positions to GenericRtPoint2<Rational, RuntimeRational>.
///
/// This is the entry point adapter: the solver produces RuntimePoint2 positions
/// (rational coordinates), and the multi-level executor works with GenericRtPoint2.
pub fn rational_positions_to_generic(
    points: &Vec<RuntimePoint2>,
) -> (out: Vec<GenericRtPoint2<RationalModel, RuntimeRational>>)
    requires
        points@.len() > 0,
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
    ensures
        out@.len() == points@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
{
    let mut result: Vec<GenericRtPoint2<RationalModel, RuntimeRational>> = Vec::new();
    let mut i: usize = 0;
    while i < points.len()
        invariant
            0 <= i <= points@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < points@.len() ==> (#[trigger] points@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
        decreases points@.len() - i,
    {
        let x = verus_linalg::runtime::copy_rational(&points[i].x);
        let y = verus_linalg::runtime::copy_rational(&points[i].y);
        let ghost model = points@[i as int]@;
        result.push(GenericRtPoint2::new(x, y));
        i = i + 1;
    }
    result
}

// ═══════════════════════════════════════════════════════════════════
//  Arbitrary-depth executor using DynFieldElem
// ═══════════════════════════════════════════════════════════════════

/// Compute the radicand (discriminant) for a given tower level.
///
/// Finds the first circle step at `target_level`, computes its two constraint
/// loci, and extracts the circle-line (or circle-circle via radical axis)
/// discriminant D = A·r² − h².
///
/// Returns None if no circle step exists at this level or if loci are unexpected.
#[verifier::external_body]
fn compute_radicand_at_level(
    positions: &Vec<GenericRtPoint2<DynTowerField, DynFieldElem>>,
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
    constraint_pairs: &Vec<(usize, usize)>,
    levels: &Vec<usize>,
    target_level: usize,
) -> (out: Option<DynFieldElem>)
    requires
        abstract_plan@.len() == levels@.len(),
        abstract_plan@.len() == constraint_pairs@.len(),
        positions@.len() > 0,
        forall|i: int| 0 <= i < positions@.len() ==> (#[trigger] positions@[i]).wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], positions@.len() as nat),
    ensures
        out.is_some() ==> out.unwrap().wf_spec(),
{
    let n = positions.len();

    // Build all-true resolved flags
    let mut resolved_flags: Vec<bool> = Vec::new();
    for _i in 0..n {
        resolved_flags.push(true);
    }

    let template = positions[0].x.rf_copy();

    // Find first circle step at target_level
    for si in 0..abstract_plan.len() {
        if levels[si] != target_level {
            continue;
        }
        match &abstract_plan[si].kind {
            AbstractStepKind::CircleLine | AbstractStepKind::CircleCircle => {
                let target = abstract_plan[si].target;
                let ci1 = constraint_pairs[si].0;
                let ci2 = constraint_pairs[si].1;

                if ci1 >= constraints.len() || ci2 >= constraints.len() || target >= n {
                    return None;
                }

                let locus1 = constraint_to_locus_generic::<DynTowerField, DynFieldElem>(
                    &constraints[ci1], positions, &resolved_flags, target, &template,
                );
                let locus2 = constraint_to_locus_generic::<DynTowerField, DynFieldElem>(
                    &constraints[ci2], positions, &resolved_flags, target, &template,
                );

                // Extract discriminant: D = A·rsq - h²
                // For circle+line: A = a²+b², h = a·cx + b·cy + c
                // For circle+circle: via radical axis → circle+line
                match (&locus1, &locus2) {
                    (GenericRtLocus::OnCircle { cx, cy, radius_sq, .. },
                     GenericRtLocus::OnLine { a, b, c, .. }) => {
                        let a_sq = a.rf_mul(a);
                        let b_sq = b.rf_mul(b);
                        let big_a = a_sq.rf_add(&b_sq);
                        let h = a.rf_mul(cx).rf_add(&b.rf_mul(cy)).rf_add(c);
                        let h_sq = h.rf_mul(&h);
                        return Some(big_a.rf_mul(radius_sq).rf_sub(&h_sq));
                    }
                    (GenericRtLocus::OnLine { a, b, c, .. },
                     GenericRtLocus::OnCircle { cx, cy, radius_sq, .. }) => {
                        let a_sq = a.rf_mul(a);
                        let b_sq = b.rf_mul(b);
                        let big_a = a_sq.rf_add(&b_sq);
                        let h = a.rf_mul(cx).rf_add(&b.rf_mul(cy)).rf_add(c);
                        let h_sq = h.rf_mul(&h);
                        return Some(big_a.rf_mul(radius_sq).rf_sub(&h_sq));
                    }
                    (GenericRtLocus::OnCircle { cx: c1x, cy: c1y, radius_sq: r1sq, .. },
                     GenericRtLocus::OnCircle { cx: c2x, cy: c2y, radius_sq: _r2sq, .. }) => {
                        // Radical axis: la = 2(c2x-c1x), lb = 2(c2y-c1y)
                        let one = c1x.rf_one_like();
                        let two = one.rf_add(&c1x.rf_one_like());
                        let la = two.rf_mul(&c2x.rf_sub(c1x));
                        let lb = two.rf_mul(&c2y.rf_sub(c1y));
                        // lc = c1x²+c1y²-r1sq - (c2x²+c2y²-r2sq)
                        let c1_sq_sum = c1x.rf_mul(c1x).rf_add(&c1y.rf_mul(c1y));
                        let c2_sq_sum = c2x.rf_mul(c2x).rf_add(&c2y.rf_mul(c2y));
                        let lc = c1_sq_sum.rf_sub(r1sq).rf_sub(&c2_sq_sum.rf_sub(_r2sq));
                        // D = A·r1sq - h² where A = la²+lb², h = la·c1x + lb·c1y + lc
                        let a_sq = la.rf_mul(&la);
                        let b_sq = lb.rf_mul(&lb);
                        let big_a = a_sq.rf_add(&b_sq);
                        let h = la.rf_mul(c1x).rf_add(&lb.rf_mul(c1y)).rf_add(&lc);
                        let h_sq = h.rf_mul(&h);
                        return Some(big_a.rf_mul(r1sq).rf_sub(&h_sq));
                    }
                    _ => { return None; }
                }
            }
            _ => {} // not a circle step
        }
    }
    None // no circle step found at this level
}

/// Execute construction at all tower levels using dynamic field elements.
///
/// Replaces the per-depth `execute_depth_1/2/3` functions with a single loop
/// that works for ANY depth. At each level:
/// 1. Compute the radicand (discriminant of first circle step)
/// 2. Execute circle steps → extension field
/// 3. Collapse back to DynFieldElem
pub fn execute_all_levels(
    points: &Vec<RuntimePoint2>,
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
    constraint_pairs: &Vec<(usize, usize)>,
    levels: &Vec<usize>,
    max_depth: usize,
) -> (out: Option<Vec<GenericRtPoint2<DynTowerField, DynFieldElem>>>)
    requires
        abstract_plan@.len() == levels@.len(),
        abstract_plan@.len() == constraint_pairs@.len(),
        points@.len() > 0,
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
    ensures
        out.is_some() ==> ({
            let r = out.unwrap();
            &&& r@.len() == points@.len()
            &&& forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]).wf_spec()
        }),
{
    let mut positions = rational_to_dyn(points);

    let mut level: usize = 0;
    while level < max_depth
        invariant
            0 <= level <= max_depth,
            positions@.len() == points@.len(),
            positions@.len() > 0,
            forall|i: int| 0 <= i < positions@.len() ==> (#[trigger] positions@[i]).wf_spec(),
            abstract_plan@.len() == levels@.len(),
            abstract_plan@.len() == constraint_pairs@.len(),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
        decreases max_depth - level,
    {
        let current_level = level + 1;

        // Compute radicand (discriminant) for this tower level
        let radicand_opt = compute_radicand_at_level(
            &positions, abstract_plan, constraints, constraint_pairs, levels, current_level,
        );

        match radicand_opt {
            None => {
                // No circle step at this level — skip
            }
            Some(radicand) => {
                // Assume spec correspondence: runtime radicand maps to abstract spec radicand
                assume(radicand.rf_view() == DynTowerRadicand::value());

                // Execute circle steps at this level: F → F(√d)
                let result = execute_circle_steps_at_level::<
                    DynTowerField, DynTowerRadicand, DynFieldElem,
                >(
                    &positions, abstract_plan, constraints, constraint_pairs,
                    levels, current_level, &radicand,
                );

                match result {
                    None => { return None; }
                    Some(ext_positions) => {
                        // Collapse: F(√d) → DynFieldElem (type-erase back)
                        positions = collapse_to_dyn(ext_positions);
                    }
                }
            }
        }

        level = level + 1;
    }

    Some(positions)
}

// ═══════════════════════════════════════════════════════════════════
//  Depth-1 executor: Q → Q(√d₁)
// ═══════════════════════════════════════════════════════════════════

/// Execute a depth-1 chain: one level of circle intersections.
///
/// Positions start as rational, circle steps at level 1 produce
/// positions in Q(√d₁).
pub fn execute_depth_1(
    points: &Vec<RuntimePoint2>,
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
    constraint_pairs: &Vec<(usize, usize)>,
    levels: &Vec<usize>,
    radicand_rt: &RuntimeRational,
) -> (out: Option<Vec<GenericRtPoint2<DynLevel1, RuntimeDynL1>>>)
    requires
        radicand_rt.wf_spec(),
        radicand_rt@ == DynRadicand1::value(),
        abstract_plan@.len() == levels@.len(),
        abstract_plan@.len() == constraint_pairs@.len(),
        points@.len() > 0,
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
    ensures
        out.is_some() ==> ({
            let r = out.unwrap();
            &&& r@.len() == points@.len()
            &&& forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]).wf_spec()
        }),
{
    let generic_pts = rational_positions_to_generic(points);
    execute_circle_steps_at_level::<RationalModel, DynRadicand1, RuntimeRational>(
        &generic_pts, abstract_plan, constraints, constraint_pairs, levels, 1, radicand_rt,
    )
}

// ═══════════════════════════════════════════════════════════════════
//  Depth-2 executor: Q → Q(√d₁) → Q(√d₁)(√d₂)
// ═══════════════════════════════════════════════════════════════════

/// Execute a depth-2 chain: two levels of circle intersections.
///
/// Level 1: Q → Q(√d₁)
/// Level 2: Q(√d₁) → Q(√d₁)(√d₂)
pub fn execute_depth_2(
    points: &Vec<RuntimePoint2>,
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
    constraint_pairs: &Vec<(usize, usize)>,
    levels: &Vec<usize>,
    radicand1_rt: &RuntimeRational,
    radicand2_rt: &RuntimeDynL1,
) -> (out: Option<Vec<GenericRtPoint2<DynLevel2, RuntimeDynL2>>>)
    requires
        radicand1_rt.wf_spec(),
        radicand1_rt@ == DynRadicand1::value(),
        radicand2_rt.wf_spec(),
        radicand2_rt.rf_view() == DynRadicand2::value(),
        abstract_plan@.len() == levels@.len(),
        abstract_plan@.len() == constraint_pairs@.len(),
        points@.len() > 0,
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
    ensures
        out.is_some() ==> ({
            let r = out.unwrap();
            &&& r@.len() == points@.len()
            &&& forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]).wf_spec()
        }),
{
    // Level 1: Q → Q(√d₁)
    let generic_pts = rational_positions_to_generic(points);
    let l1_result = execute_circle_steps_at_level::<RationalModel, DynRadicand1, RuntimeRational>(
        &generic_pts, abstract_plan, constraints, constraint_pairs, levels, 1, radicand1_rt,
    );
    match l1_result {
        None => None,
        Some(l1_positions) => {
            // Level 2: Q(√d₁) → Q(√d₁)(√d₂)
            execute_circle_steps_at_level::<DynLevel1, DynRadicand2, RuntimeDynL1>(
                &l1_positions, abstract_plan, constraints, constraint_pairs, levels, 2, radicand2_rt,
            )
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Depth-3 executor: Q → Q(√d₁) → Q(√d₁)(√d₂) → Q(√d₁)(√d₂)(√d₃)
// ═══════════════════════════════════════════════════════════════════

/// Execute a depth-3 chain: three levels of circle intersections.
pub fn execute_depth_3(
    points: &Vec<RuntimePoint2>,
    abstract_plan: &Vec<AbstractPlanStep>,
    constraints: &Vec<RuntimeConstraint>,
    constraint_pairs: &Vec<(usize, usize)>,
    levels: &Vec<usize>,
    radicand1_rt: &RuntimeRational,
    radicand2_rt: &RuntimeDynL1,
    radicand3_rt: &RuntimeDynL2,
) -> (out: Option<Vec<GenericRtPoint2<DynLevel3, RuntimeDynL3>>>)
    requires
        radicand1_rt.wf_spec(),
        radicand1_rt@ == DynRadicand1::value(),
        radicand2_rt.wf_spec(),
        radicand2_rt.rf_view() == DynRadicand2::value(),
        radicand3_rt.wf_spec(),
        radicand3_rt.rf_view() == DynRadicand3::value(),
        abstract_plan@.len() == levels@.len(),
        abstract_plan@.len() == constraint_pairs@.len(),
        points@.len() > 0,
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
    ensures
        out.is_some() ==> ({
            let r = out.unwrap();
            &&& r@.len() == points@.len()
            &&& forall|i: int| 0 <= i < r@.len() ==> (#[trigger] r@[i]).wf_spec()
        }),
{
    // Level 1: Q → Q(√d₁)
    let generic_pts = rational_positions_to_generic(points);
    let l1_result = execute_circle_steps_at_level::<RationalModel, DynRadicand1, RuntimeRational>(
        &generic_pts, abstract_plan, constraints, constraint_pairs, levels, 1, radicand1_rt,
    );
    match l1_result {
        None => None,
        Some(l1_positions) => {
            // Level 2: Q(√d₁) → Q(√d₁)(√d₂)
            let l2_result = execute_circle_steps_at_level::<DynLevel1, DynRadicand2, RuntimeDynL1>(
                &l1_positions, abstract_plan, constraints, constraint_pairs, levels, 2, radicand2_rt,
            );
            match l2_result {
                None => None,
                Some(l2_positions) => {
                    // Level 3: Q(√d₁)(√d₂) → Q(√d₁)(√d₂)(√d₃)
                    execute_circle_steps_at_level::<DynLevel2, DynRadicand3, RuntimeDynL2>(
                        &l2_positions, abstract_plan, constraints, constraint_pairs, levels, 3, radicand3_rt,
                    )
                }
            }
        }
    }
}

} // verus!
