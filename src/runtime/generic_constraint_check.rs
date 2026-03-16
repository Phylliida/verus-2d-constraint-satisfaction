/// Generic constraint checking over any RuntimeFieldOps field.
///
/// Checks all 19 constraint types using generic field arithmetic (rf_* ops).
/// Used by the dynamic tower pipeline to verify constraints at arbitrary depth.
///
/// The ensures clause uses `assume` since DynTowerField's spec ops are abstract.
/// The runtime arithmetic is correct by construction (mirrors spec-level formulas).
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use verus_geometry::voronoi::sq_dist_2d;
use verus_quadratic_extension::runtime_field::RuntimeFieldOps;
use verus_rational::runtime_rational::RuntimeRational;
use crate::runtime::constraint::*;
use crate::runtime::generic_point::GenericRtPoint2;
use crate::runtime::generic_locus::all_generic_points_wf;

type RationalModel = verus_rational::rational::Rational;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Generic helpers
// ═══════════════════════════════════════════════════════════════════

/// Generic squared distance.
fn g_sq_dist<V: OrderedField, F: RuntimeFieldOps<V>>(
    p: &GenericRtPoint2<V, F>,
    q: &GenericRtPoint2<V, F>,
) -> (out: F)
    requires p.wf_spec(), q.wf_spec()
    ensures out.wf_spec()
{
    let dx = p.x.rf_sub(&q.x);
    let dy = p.y.rf_sub(&q.y);
    let dx2 = dx.rf_mul(&dx);
    let dy2 = dy.rf_mul(&dy);
    dx2.rf_add(&dy2)
}

/// Generic field element equivalence check.
fn g_eqv<V: OrderedField, F: RuntimeFieldOps<V>>(a: &F, b: &F) -> (out: bool)
    requires a.wf_spec(), b.wf_spec()
    ensures out == a.rf_view().eqv(b.rf_view())
{
    a.rf_eq(b)
}

/// Generic point equivalence check.
fn g_point_eqv<V: OrderedField, F: RuntimeFieldOps<V>>(
    a: &GenericRtPoint2<V, F>, b: &GenericRtPoint2<V, F>,
) -> (out: bool)
    requires a.wf_spec(), b.wf_spec()
    ensures out == (a.model@.x.eqv(b.model@.x) && a.model@.y.eqv(b.model@.y))
{
    a.x.rf_eq(&b.x) && a.y.rf_eq(&b.y)
}

/// Generic line eval: a*px + b*py + c
fn g_line_eval<V: OrderedField, F: RuntimeFieldOps<V>>(
    la: &F, lb: &F, lc: &F, px: &F, py: &F,
) -> (out: F)
    requires la.wf_spec(), lb.wf_spec(), lc.wf_spec(), px.wf_spec(), py.wf_spec()
    ensures out.wf_spec()
{
    la.rf_mul(px).rf_add(&lb.rf_mul(py)).rf_add(lc)
}

/// Generic line from two points: a = -(q.y - p.y), b = q.x - p.x, c = -(a*p.x + b*p.y)
fn g_line_from_points<V: OrderedField, F: RuntimeFieldOps<V>>(
    p: &GenericRtPoint2<V, F>, q: &GenericRtPoint2<V, F>,
) -> (out: (F, F, F))
    requires p.wf_spec(), q.wf_spec()
    ensures out.0.wf_spec(), out.1.wf_spec(), out.2.wf_spec()
{
    let dy = q.y.rf_sub(&p.y);
    let a = dy.rf_neg();
    let b = q.x.rf_sub(&p.x);
    let ap = a.rf_mul(&p.x);
    let bp = b.rf_mul(&p.y);
    let c = ap.rf_add(&bp).rf_neg();
    (a, b, c)
}

// ═══════════════════════════════════════════════════════════════════
//  Per-constraint checkers
// ═══════════════════════════════════════════════════════════════════

fn check_coincident_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => {
            g_point_eqv(&points[*a], &points[*b])
        }
        _ => false,
    }
}

fn check_distance_sq_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>, template: &F,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
{
    match rc {
        RuntimeConstraint::DistanceSq { a, b, dist_sq, .. } => {
            let d = g_sq_dist(&points[*a], &points[*b]);
            let target = template.rf_embed_rational(dist_sq);
            g_eqv(&d, &target)
        }
        _ => false,
    }
}

fn check_fixed_x_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>, template: &F,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
{
    match rc {
        RuntimeConstraint::FixedX { point, x, .. } => {
            let target = template.rf_embed_rational(x);
            g_eqv(&points[*point].x, &target)
        }
        _ => false,
    }
}

fn check_fixed_y_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>, template: &F,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
{
    match rc {
        RuntimeConstraint::FixedY { point, y, .. } => {
            let target = template.rf_embed_rational(y);
            g_eqv(&points[*point].y, &target)
        }
        _ => false,
    }
}

fn check_same_x_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::SameX { a, b, .. } => {
            g_eqv(&points[*a].x, &points[*b].x)
        }
        _ => false,
    }
}

fn check_same_y_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::SameY { a, b, .. } => {
            g_eqv(&points[*a].y, &points[*b].y)
        }
        _ => false,
    }
}

fn check_point_on_line_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } => {
            let (a, b, c) = g_line_from_points(&points[*line_a], &points[*line_b]);
            let eval = g_line_eval(&a, &b, &c, &points[*point].x, &points[*point].y);
            let zero = points[*point].x.rf_zero_like();
            g_eqv(&eval, &zero)
        }
        _ => false,
    }
}

fn check_equal_length_sq_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } => {
            let da = g_sq_dist(&points[*a1], &points[*a2]);
            let db = g_sq_dist(&points[*b1], &points[*b2]);
            g_eqv(&da, &db)
        }
        _ => false,
    }
}

fn check_midpoint_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::Midpoint { mid, a, b, .. } => {
            // Check 2*mid == a + b (avoids division)
            let one = points[*mid].x.rf_one_like();
            let two = one.rf_add(&points[*mid].x.rf_one_like());
            let mx2 = two.rf_mul(&points[*mid].x);
            let my2 = two.rf_mul(&points[*mid].y);
            let sx = points[*a].x.rf_add(&points[*b].x);
            let sy = points[*a].y.rf_add(&points[*b].y);
            g_eqv(&mx2, &sx) && g_eqv(&my2, &sy)
        }
        _ => false,
    }
}

fn check_perpendicular_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } => {
            // dot product of (a2-a1) . (b2-b1) == 0
            let d1x = points[*a2].x.rf_sub(&points[*a1].x);
            let d1y = points[*a2].y.rf_sub(&points[*a1].y);
            let d2x = points[*b2].x.rf_sub(&points[*b1].x);
            let d2y = points[*b2].y.rf_sub(&points[*b1].y);
            let dot = d1x.rf_mul(&d2x).rf_add(&d1y.rf_mul(&d2y));
            let zero = points[*a1].x.rf_zero_like();
            g_eqv(&dot, &zero)
        }
        _ => false,
    }
}

fn check_parallel_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } => {
            // cross product of (a2-a1) × (b2-b1) == 0
            let d1x = points[*a2].x.rf_sub(&points[*a1].x);
            let d1y = points[*a2].y.rf_sub(&points[*a1].y);
            let d2x = points[*b2].x.rf_sub(&points[*b1].x);
            let d2y = points[*b2].y.rf_sub(&points[*b1].y);
            let cross = d1x.rf_mul(&d2y).rf_sub(&d1y.rf_mul(&d2x));
            let zero = points[*a1].x.rf_zero_like();
            g_eqv(&cross, &zero)
        }
        _ => false,
    }
}

fn check_collinear_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::Collinear { a, b, c, .. } => {
            let (la, lb, lc) = g_line_from_points(&points[*a], &points[*b]);
            let eval = g_line_eval(&la, &lb, &lc, &points[*c].x, &points[*c].y);
            let zero = points[*a].x.rf_zero_like();
            g_eqv(&eval, &zero)
        }
        _ => false,
    }
}

fn check_point_on_circle_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } => {
            let d_pt = g_sq_dist(&points[*point], &points[*center]);
            let d_rad = g_sq_dist(&points[*radius_point], &points[*center]);
            g_eqv(&d_pt, &d_rad)
        }
        _ => false,
    }
}

fn check_symmetric_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
            // Reflection: point = 2*proj(original, line) - original
            // Check: point + original = 2*proj (i.e., midpoint on line, and perpendicular)
            // Simpler check: (point + original)/2 is on the axis line, and
            // (point - original) . (axis_b - axis_a) == 0
            let dx = points[*axis_b].x.rf_sub(&points[*axis_a].x);
            let dy = points[*axis_b].y.rf_sub(&points[*axis_a].y);

            // Check perpendicularity: (point - original) . (axis_b - axis_a) == 0
            let px = points[*point].x.rf_sub(&points[*original].x);
            let py = points[*point].y.rf_sub(&points[*original].y);
            let dot = px.rf_mul(&dx).rf_add(&py.rf_mul(&dy));
            let zero = points[*point].x.rf_zero_like();
            let perp = g_eqv(&dot, &zero);

            // Check midpoint on axis: line_eval(midpoint) == 0
            let one = points[*point].x.rf_one_like();
            let two = one.rf_add(&points[*point].x.rf_one_like());
            let mx2 = points[*point].x.rf_add(&points[*original].x);
            let my2 = points[*point].y.rf_add(&points[*original].y);

            let (la, lb, lc) = g_line_from_points(&points[*axis_a], &points[*axis_b]);
            // eval line at (mx2/2, my2/2) == 0, equiv to a*mx2 + b*my2 + 2c == 0
            let eval2 = la.rf_mul(&mx2).rf_add(&lb.rf_mul(&my2)).rf_add(&two.rf_mul(&lc));
            let zero2 = points[*point].x.rf_zero_like();
            let on_line = g_eqv(&eval2, &zero2);

            perp && on_line
        }
        _ => false,
    }
}

fn check_fixed_point_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>, template: &F,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
{
    match rc {
        RuntimeConstraint::FixedPoint { point, x, y, .. } => {
            let tx = template.rf_embed_rational(x);
            let ty = template.rf_embed_rational(y);
            g_eqv(&points[*point].x, &tx) && g_eqv(&points[*point].y, &ty)
        }
        _ => false,
    }
}

fn check_ratio_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>, template: &F,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
{
    match rc {
        RuntimeConstraint::Ratio { a1, a2, b1, b2, ratio_sq, .. } => {
            // |a1-a2|² == ratio_sq * |b1-b2|²
            let da = g_sq_dist(&points[*a1], &points[*a2]);
            let db = g_sq_dist(&points[*b1], &points[*b2]);
            let rsq = template.rf_embed_rational(ratio_sq);
            let rhs = rsq.rf_mul(&db);
            g_eqv(&da, &rhs)
        }
        _ => false,
    }
}

fn check_tangent_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, .. } => {
            // (a*cx + b*cy + c)² == (a²+b²) * r²
            let (a, b, c) = g_line_from_points(&points[*line_a], &points[*line_b]);
            let eval = g_line_eval(&a, &b, &c, &points[*center].x, &points[*center].y);
            let lhs = eval.rf_mul(&eval);
            let ab_sq = a.rf_mul(&a).rf_add(&b.rf_mul(&b));
            let r_sq = g_sq_dist(&points[*center], &points[*radius_point]);
            let rhs = ab_sq.rf_mul(&r_sq);
            g_eqv(&lhs, &rhs)
        }
        _ => false,
    }
}

fn check_circle_tangent_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
{
    match rc {
        RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, .. } => {
            // (d - r1 - r2)² == 4*r1*r2  where d = |c1-c2|², r1 = |c1-rp1|², r2 = |c2-rp2|²
            let d = g_sq_dist(&points[*c1], &points[*c2]);
            let r1 = g_sq_dist(&points[*c1], &points[*rp1]);
            let r2 = g_sq_dist(&points[*c2], &points[*rp2]);
            let one = points[*c1].x.rf_one_like();
            let two = one.rf_add(&points[*c1].x.rf_one_like());
            let four = two.rf_mul(&two);
            let diff = d.rf_sub(&r1).rf_sub(&r2);
            let lhs = diff.rf_mul(&diff);
            let rhs = four.rf_mul(&r1).rf_mul(&r2);
            g_eqv(&lhs, &rhs)
        }
        _ => false,
    }
}

fn check_angle_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint, points: &Vec<GenericRtPoint2<V, F>>, template: &F,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
{
    match rc {
        RuntimeConstraint::Angle { a1, a2, b1, b2, cos_sq, .. } => {
            // (d1 · d2)² == cos_sq * |d1|² * |d2|²
            let d1x = points[*a2].x.rf_sub(&points[*a1].x);
            let d1y = points[*a2].y.rf_sub(&points[*a1].y);
            let d2x = points[*b2].x.rf_sub(&points[*b1].x);
            let d2y = points[*b2].y.rf_sub(&points[*b1].y);
            let dp = d1x.rf_mul(&d2x).rf_add(&d1y.rf_mul(&d2y));
            let n1 = d1x.rf_mul(&d1x).rf_add(&d1y.rf_mul(&d1y));
            let n2 = d2x.rf_mul(&d2x).rf_add(&d2y.rf_mul(&d2y));
            let lhs = dp.rf_mul(&dp);
            let cs = template.rf_embed_rational(cos_sq);
            let rhs = cs.rf_mul(&n1).rf_mul(&n2);
            g_eqv(&lhs, &rhs)
        }
        _ => false,
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Main dispatcher + check_all loop
// ═══════════════════════════════════════════════════════════════════

/// Check if a single constraint is satisfied by generic field positions.
///
/// Dispatches to per-constraint helpers. Returns true if the constraint's
/// algebraic identity holds in the generic field.
pub fn check_constraint_satisfied_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint,
    points: &Vec<GenericRtPoint2<V, F>>,
    template: &F,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
{
    match rc {
        RuntimeConstraint::Coincident { .. } => check_coincident_generic(rc, points),
        RuntimeConstraint::DistanceSq { .. } => check_distance_sq_generic(rc, points, template),
        RuntimeConstraint::FixedX { .. } => check_fixed_x_generic(rc, points, template),
        RuntimeConstraint::FixedY { .. } => check_fixed_y_generic(rc, points, template),
        RuntimeConstraint::SameX { .. } => check_same_x_generic(rc, points),
        RuntimeConstraint::SameY { .. } => check_same_y_generic(rc, points),
        RuntimeConstraint::PointOnLine { .. } => check_point_on_line_generic(rc, points),
        RuntimeConstraint::EqualLengthSq { .. } => check_equal_length_sq_generic(rc, points),
        RuntimeConstraint::Midpoint { .. } => check_midpoint_generic(rc, points),
        RuntimeConstraint::Perpendicular { .. } => check_perpendicular_generic(rc, points),
        RuntimeConstraint::Parallel { .. } => check_parallel_generic(rc, points),
        RuntimeConstraint::Collinear { .. } => check_collinear_generic(rc, points),
        RuntimeConstraint::PointOnCircle { .. } => check_point_on_circle_generic(rc, points),
        RuntimeConstraint::Symmetric { .. } => check_symmetric_generic(rc, points),
        RuntimeConstraint::FixedPoint { .. } => check_fixed_point_generic(rc, points, template),
        RuntimeConstraint::Ratio { .. } => check_ratio_generic(rc, points, template),
        RuntimeConstraint::Tangent { .. } => check_tangent_generic(rc, points),
        RuntimeConstraint::CircleTangent { .. } => check_circle_tangent_generic(rc, points),
        RuntimeConstraint::Angle { .. } => check_angle_generic(rc, points, template),
    }
}

/// Check if ALL constraints are satisfied by generic field positions.
///
/// Returns true only if every constraint passes.
pub fn check_all_constraints_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    constraints: &Vec<RuntimeConstraint>,
    points: &Vec<GenericRtPoint2<V, F>>,
    template: &F,
) -> (out: bool)
    requires
        all_generic_points_wf::<V, F>(points@),
        template.wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
{
    let mut i: usize = 0;
    while i < constraints.len()
        invariant
            0 <= i <= constraints@.len(),
            all_generic_points_wf::<V, F>(points@),
            template.wf_spec(),
            forall|j: int| 0 <= j < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[j], points@.len() as nat),
        decreases constraints@.len() - i,
    {
        let ok = check_constraint_satisfied_generic(
            &constraints[i], points, template,
        );
        if !ok {
            return false;
        }
        i = i + 1;
    }
    true
}

} // verus!
