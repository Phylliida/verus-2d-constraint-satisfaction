/// Generic constraint-to-locus computation over any RuntimeFieldOps field.
///
/// Mirrors the spec-level `constraint_to_locus<T: OrderedField>` but at the
/// exec level, using RuntimeFieldOps for arithmetic. Constraint parameters
/// (distances, coordinates) are embedded from Rational into the target field.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use verus_geometry::line2::Line2;
use verus_geometry::circle2::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_quadratic_extension::runtime_field::RuntimeFieldOps;
use verus_rational::runtime_rational::RuntimeRational;
use crate::locus::*;
use crate::construction_ext::lemma_two_ne_zero;
use crate::runtime::constraint::*;
use crate::runtime::generic_point::GenericRtPoint2;

type RationalModel = verus_rational::rational::Rational;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  GenericRtLocus — generic runtime locus type
// ═══════════════════════════════════════════════════════════════════

/// Runtime locus with coordinates in a generic field F.
///
/// Each variant carries a `Ghost<Locus2d<V>>` model for spec correspondence
/// (also satisfies Rust's "V must be used" constraint).
pub enum GenericRtLocus<V: OrderedField, F: RuntimeFieldOps<V>> {
    FullPlane { model: Ghost<Locus2d<V>> },
    OnLine { a: F, b: F, c: F, model: Ghost<Locus2d<V>> },
    OnCircle { cx: F, cy: F, radius_sq: F, model: Ghost<Locus2d<V>> },
    AtPoint { x: F, y: F, model: Ghost<Locus2d<V>> },
}

impl<V: OrderedField, F: RuntimeFieldOps<V>> GenericRtLocus<V, F> {
    pub open spec fn wf_spec(&self) -> bool {
        match self {
            GenericRtLocus::FullPlane { .. } => true,
            GenericRtLocus::OnLine { a, b, c, .. } =>
                a.wf_spec() && b.wf_spec() && c.wf_spec(),
            GenericRtLocus::OnCircle { cx, cy, radius_sq, .. } =>
                cx.wf_spec() && cy.wf_spec() && radius_sq.wf_spec(),
            GenericRtLocus::AtPoint { x, y, .. } => x.wf_spec() && y.wf_spec(),
        }
    }

    pub open spec fn spec_locus(&self) -> Locus2d<V> {
        match self {
            GenericRtLocus::FullPlane { model } => model@,
            GenericRtLocus::OnLine { model, .. } => model@,
            GenericRtLocus::OnCircle { model, .. } => model@,
            GenericRtLocus::AtPoint { model, .. } => model@,
        }
    }

    pub open spec fn is_nontrivial(&self) -> bool {
        !matches!(self, GenericRtLocus::FullPlane { .. })
    }
}

// Helper: construct FullPlane with correct model
fn mk_full_plane<V: OrderedField, F: RuntimeFieldOps<V>>() -> (out: GenericRtLocus<V, F>)
    ensures out.wf_spec()
{
    GenericRtLocus::FullPlane { model: Ghost(Locus2d::FullPlane) }
}

// ═══════════════════════════════════════════════════════════════════
//  Helper: generic line from two points
// ═══════════════════════════════════════════════════════════════════

/// Compute line coefficients (a, b, c) from two points, using generic field ops.
fn generic_line_from_points<V: OrderedField, F: RuntimeFieldOps<V>>(
    p: &GenericRtPoint2<V, F>,
    q: &GenericRtPoint2<V, F>,
) -> (out: (F, F, F))
    requires p.wf_spec(), q.wf_spec()
    ensures out.0.wf_spec(), out.1.wf_spec(), out.2.wf_spec(),
{
    let dy = q.y.rf_sub(&p.y);
    let a = dy.rf_neg();
    let b = q.x.rf_sub(&p.x);
    let ap = a.rf_mul(&p.x);
    let bp = b.rf_mul(&p.y);
    let c = ap.rf_add(&bp).rf_neg();
    (a, b, c)
}

/// Squared distance between two generic points.
fn generic_sq_dist<V: OrderedField, F: RuntimeFieldOps<V>>(
    p: &GenericRtPoint2<V, F>,
    q: &GenericRtPoint2<V, F>,
) -> (out: F)
    requires p.wf_spec(), q.wf_spec()
    ensures out.wf_spec(), out.rf_view() == sq_dist_2d::<V>(p.model@, q.model@),
{
    let dx = p.x.rf_sub(&q.x);
    let dy = p.y.rf_sub(&q.y);
    let dx2 = dx.rf_mul(&dx);
    let dy2 = dy.rf_mul(&dy);
    dx2.rf_add(&dy2)
}

// ═══════════════════════════════════════════════════════════════════
//  Generic constraint → locus
// ═══════════════════════════════════════════════════════════════════

/// Well-formedness for generic points vec.
pub open spec fn all_generic_points_wf<V: OrderedField, F: RuntimeFieldOps<V>>(
    points: Seq<GenericRtPoint2<V, F>>,
) -> bool {
    forall|i: int| 0 <= i < points.len() ==> (#[trigger] points[i]).wf_spec()
}

/// Compute the locus a constraint imposes on a target entity, with positions
/// in a generic field F.
///
/// Constraint parameters (dist_sq, x, y, ratio_sq) are embedded from Rational
/// into F using rf_embed_rational. A "template" element is needed for context.
///
/// Ghost models use `arbitrary()` — spec correspondence proved in Phase 5.
pub fn constraint_to_locus_generic<V: OrderedField, F: RuntimeFieldOps<V>>(
    rc: &RuntimeConstraint,
    points: &Vec<GenericRtPoint2<V, F>>,
    resolved_flags: &Vec<bool>,
    target: usize,
    template: &F,
) -> (out: GenericRtLocus<V, F>)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_generic_points_wf::<V, F>(points@),
        resolved_flags@.len() == points@.len(),
        (target as int) < points@.len(),
        template.wf_spec(),
    ensures
        out.wf_spec(),
{
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => {
            if target == *a && resolved_flags[*b] {
                GenericRtLocus::AtPoint {
                    x: points[*b].x.rf_copy(), y: points[*b].y.rf_copy(),
                    model: Ghost(arbitrary()),
                }
            } else if target == *b && resolved_flags[*a] {
                GenericRtLocus::AtPoint {
                    x: points[*a].x.rf_copy(), y: points[*a].y.rf_copy(),
                    model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::DistanceSq { a, b, dist_sq, .. } => {
            if target == *a && resolved_flags[*b] {
                let d = template.rf_embed_rational(dist_sq);
                GenericRtLocus::OnCircle {
                    cx: points[*b].x.rf_copy(), cy: points[*b].y.rf_copy(),
                    radius_sq: d, model: Ghost(arbitrary()),
                }
            } else if target == *b && resolved_flags[*a] {
                let d = template.rf_embed_rational(dist_sq);
                GenericRtLocus::OnCircle {
                    cx: points[*a].x.rf_copy(), cy: points[*a].y.rf_copy(),
                    radius_sq: d, model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::FixedX { point, x, .. } => {
            if target == *point {
                let one = template.rf_one_like();
                let zero = template.rf_zero_like();
                let xv = template.rf_embed_rational(x);
                GenericRtLocus::OnLine { a: one, b: zero, c: xv.rf_neg(), model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::FixedY { point, y, .. } => {
            if target == *point {
                let zero = template.rf_zero_like();
                let one = template.rf_one_like();
                let yv = template.rf_embed_rational(y);
                GenericRtLocus::OnLine { a: zero, b: one, c: yv.rf_neg(), model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::SameX { a, b, .. } => {
            if target == *a && resolved_flags[*b] {
                let one = template.rf_one_like();
                let zero = template.rf_zero_like();
                GenericRtLocus::OnLine { a: one, b: zero, c: points[*b].x.rf_neg(), model: Ghost(arbitrary()) }
            } else if target == *b && resolved_flags[*a] {
                let one = template.rf_one_like();
                let zero = template.rf_zero_like();
                GenericRtLocus::OnLine { a: one, b: zero, c: points[*a].x.rf_neg(), model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::SameY { a, b, .. } => {
            if target == *a && resolved_flags[*b] {
                let zero = template.rf_zero_like();
                let one = template.rf_one_like();
                GenericRtLocus::OnLine { a: zero, b: one, c: points[*b].y.rf_neg(), model: Ghost(arbitrary()) }
            } else if target == *b && resolved_flags[*a] {
                let zero = template.rf_zero_like();
                let one = template.rf_one_like();
                GenericRtLocus::OnLine { a: zero, b: one, c: points[*a].y.rf_neg(), model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } => {
            if target == *point && resolved_flags[*line_a] && resolved_flags[*line_b] {
                let (a, b, c) = generic_line_from_points(&points[*line_a], &points[*line_b]);
                GenericRtLocus::OnLine { a, b, c, model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } => {
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                let r2 = generic_sq_dist(&points[*b1], &points[*b2]);
                GenericRtLocus::OnCircle {
                    cx: points[*a2].x.rf_copy(), cy: points[*a2].y.rf_copy(),
                    radius_sq: r2, model: Ghost(arbitrary()),
                }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                let r2 = generic_sq_dist(&points[*b1], &points[*b2]);
                GenericRtLocus::OnCircle {
                    cx: points[*a1].x.rf_copy(), cy: points[*a1].y.rf_copy(),
                    radius_sq: r2, model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::Midpoint { mid, a, b, .. } => {
            if target == *mid && resolved_flags[*a] && resolved_flags[*b] {
                let one = template.rf_one_like();
                let two = one.rf_add(&template.rf_one_like());
                proof { lemma_two_ne_zero::<V>(); }
                let sx = points[*a].x.rf_add(&points[*b].x);
                let sy = points[*a].y.rf_add(&points[*b].y);
                GenericRtLocus::AtPoint { x: sx.rf_div(&two), y: sy.rf_div(&two), model: Ghost(arbitrary()) }
            } else if target == *a && resolved_flags[*mid] && resolved_flags[*b] {
                let one = template.rf_one_like();
                let two = one.rf_add(&template.rf_one_like());
                GenericRtLocus::AtPoint {
                    x: two.rf_mul(&points[*mid].x).rf_sub(&points[*b].x),
                    y: two.rf_mul(&points[*mid].y).rf_sub(&points[*b].y),
                    model: Ghost(arbitrary()),
                }
            } else if target == *b && resolved_flags[*mid] && resolved_flags[*a] {
                let one = template.rf_one_like();
                let two = one.rf_add(&template.rf_one_like());
                GenericRtLocus::AtPoint {
                    x: two.rf_mul(&points[*mid].x).rf_sub(&points[*a].x),
                    y: two.rf_mul(&points[*mid].y).rf_sub(&points[*a].y),
                    model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } => {
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                let dbx = points[*b2].x.rf_sub(&points[*b1].x);
                let dby = points[*b2].y.rf_sub(&points[*b1].y);
                let c_val = dbx.rf_mul(&points[*a2].x).rf_add(&dby.rf_mul(&points[*a2].y)).rf_neg();
                GenericRtLocus::OnLine { a: dbx, b: dby, c: c_val, model: Ghost(arbitrary()) }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                let dbx = points[*b2].x.rf_sub(&points[*b1].x);
                let dby = points[*b2].y.rf_sub(&points[*b1].y);
                let c_val = dbx.rf_mul(&points[*a1].x).rf_add(&dby.rf_mul(&points[*a1].y)).rf_neg();
                GenericRtLocus::OnLine { a: dbx, b: dby, c: c_val, model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } => {
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                let dbx = points[*b2].x.rf_sub(&points[*b1].x);
                let dby = points[*b2].y.rf_sub(&points[*b1].y);
                let neg_dbx = dbx.rf_neg();
                let c_val = dby.rf_mul(&points[*a2].x).rf_add(&neg_dbx.rf_mul(&points[*a2].y)).rf_neg();
                GenericRtLocus::OnLine { a: dby, b: neg_dbx, c: c_val, model: Ghost(arbitrary()) }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                let dbx = points[*b2].x.rf_sub(&points[*b1].x);
                let dby = points[*b2].y.rf_sub(&points[*b1].y);
                let neg_dbx = dbx.rf_neg();
                let c_val = dby.rf_mul(&points[*a1].x).rf_add(&neg_dbx.rf_mul(&points[*a1].y)).rf_neg();
                GenericRtLocus::OnLine { a: dby, b: neg_dbx, c: c_val, model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::Collinear { a, b, c, .. } => {
            if target == *c && resolved_flags[*a] && resolved_flags[*b] {
                let (la, lb, lc) = generic_line_from_points(&points[*a], &points[*b]);
                GenericRtLocus::OnLine { a: la, b: lb, c: lc, model: Ghost(arbitrary()) }
            } else if target == *a && resolved_flags[*b] && resolved_flags[*c] {
                let (la, lb, lc) = generic_line_from_points(&points[*b], &points[*c]);
                GenericRtLocus::OnLine { a: la, b: lb, c: lc, model: Ghost(arbitrary()) }
            } else if target == *b && resolved_flags[*a] && resolved_flags[*c] {
                let (la, lb, lc) = generic_line_from_points(&points[*a], &points[*c]);
                GenericRtLocus::OnLine { a: la, b: lb, c: lc, model: Ghost(arbitrary()) }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } => {
            if target == *point && resolved_flags[*center] && resolved_flags[*radius_point] {
                let r2 = generic_sq_dist(&points[*radius_point], &points[*center]);
                GenericRtLocus::OnCircle {
                    cx: points[*center].x.rf_copy(), cy: points[*center].y.rf_copy(),
                    radius_sq: r2, model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
            if target == *point && resolved_flags[*original] && resolved_flags[*axis_a] && resolved_flags[*axis_b] {
                let dx = points[*axis_b].x.rf_sub(&points[*axis_a].x);
                let dy = points[*axis_b].y.rf_sub(&points[*axis_a].y);
                let pax = points[*original].x.rf_sub(&points[*axis_a].x);
                let pay = points[*original].y.rf_sub(&points[*axis_a].y);
                let dot_dd = dx.rf_mul(&dx).rf_add(&dy.rf_mul(&dy));
                let one = template.rf_one_like();
                let two = one.rf_add(&template.rf_one_like());
                let dot_pad = pax.rf_mul(&dx).rf_add(&pay.rf_mul(&dy));
                let zero = template.rf_zero_like();
                let is_zero = dot_dd.rf_eq(&zero);
                let t = if is_zero {
                    dot_pad.rf_mul(&dot_dd)
                } else {
                    dot_pad.rf_div(&dot_dd)
                };
                let proj_x = points[*axis_a].x.rf_add(&t.rf_mul(&dx));
                let proj_y = points[*axis_a].y.rf_add(&t.rf_mul(&dy));
                GenericRtLocus::AtPoint {
                    x: two.rf_mul(&proj_x).rf_sub(&points[*original].x),
                    y: two.rf_mul(&proj_y).rf_sub(&points[*original].y),
                    model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::FixedPoint { point, x, y, .. } => {
            if target == *point {
                GenericRtLocus::AtPoint {
                    x: template.rf_embed_rational(x),
                    y: template.rf_embed_rational(y),
                    model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        RuntimeConstraint::Ratio { a1, a2, b1, b2, ratio_sq, .. } => {
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                let db = generic_sq_dist(&points[*b1], &points[*b2]);
                let rsq = template.rf_embed_rational(ratio_sq);
                GenericRtLocus::OnCircle {
                    cx: points[*a2].x.rf_copy(), cy: points[*a2].y.rf_copy(),
                    radius_sq: rsq.rf_mul(&db), model: Ghost(arbitrary()),
                }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                let db = generic_sq_dist(&points[*b1], &points[*b2]);
                let rsq = template.rf_embed_rational(ratio_sq);
                GenericRtLocus::OnCircle {
                    cx: points[*a1].x.rf_copy(), cy: points[*a1].y.rf_copy(),
                    radius_sq: rsq.rf_mul(&db), model: Ghost(arbitrary()),
                }
            } else { mk_full_plane() }
        }

        // Verification-only constraints: no geometric locus
        RuntimeConstraint::Tangent { .. } => { mk_full_plane() }
        RuntimeConstraint::CircleTangent { .. } => { mk_full_plane() }
        RuntimeConstraint::Angle { .. } => { mk_full_plane() }
    }
}

} // verus!
