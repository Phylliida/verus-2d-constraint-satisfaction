/// Generic circle-line and circle-circle intersection using RuntimeFieldOps.
///
/// Computes intersection points in the extension field F(√d), producing
/// RuntimeQExt<FV, R, F> coordinates. All arithmetic uses rf_* methods.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use verus_geometry::line2::Line2;
use verus_geometry::circle2::*;
use verus_geometry::circle_line::*;
use verus_geometry::circle_circle::*;
use verus_quadratic_extension::runtime_field::RuntimeFieldOps;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::runtime_qext::RuntimeQExt;
use crate::runtime::generic_point::GenericRtPoint2;
use crate::runtime::generic_locus::GenericRtLocus;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  Generic circle-line intersection
// ═══════════════════════════════════════════════════════════════════

/// Compute circle-line intersection in generic field, producing point
/// in extension F(√d).
///
/// The circle is (center, radius_sq) and the line is (a, b, c).
/// Returns a GenericRtPoint2 in the extension field.
///
/// Mirrors spec: cl_intersection_point.
/// Formula:
///   A = a² + b²
///   h = a*cx + b*cy + c
///   x = cx - a*h/A ∓ b*√D/A  →  re = cx - a*h/A, im_x = ∓b/A
///   y = cy - b*h/A ± a*√D/A  →  re = cy - b*h/A, im_y = ±a/A
pub fn generic_cl_intersection<
    FV: OrderedField,
    R: PositiveRadicand<FV>,
    F: RuntimeFieldOps<FV>,
>(
    // Circle: center (cx, cy) and radius_sq
    cx: &F, cy: &F, radius_sq: &F,
    // Line: coefficients a, b, c
    la: &F, lb: &F, lc: &F,
    // Radicand runtime value for the extension
    radicand_rt: &F,
    plus: bool,
) -> (out: GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>)
    requires
        cx.wf_spec(), cy.wf_spec(), radius_sq.wf_spec(),
        la.wf_spec(), lb.wf_spec(), lc.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt.rf_view() == R::value(),
        // A = a² + b² ≠ 0 (line is non-degenerate)
        !la.rf_view().mul(la.rf_view()).add(lb.rf_view().mul(lb.rf_view())).eqv(FV::zero()),
    ensures
        out.wf_spec(),
{
    // A = a² + b²
    let a_sq = la.rf_mul(la);
    let b_sq = lb.rf_mul(lb);
    let big_a = a_sq.rf_add(&b_sq);

    // h = a*cx + b*cy + c
    let h = la.rf_mul(cx).rf_add(&lb.rf_mul(cy)).rf_add(lc);

    // re_x = cx - a*h/A
    let re_x = cx.rf_sub(&la.rf_mul(&h).rf_div(&big_a));

    // im_x = ∓b/A  (minus for plus=true, plus for plus=false)
    let im_x = if plus {
        lb.rf_neg().rf_div(&big_a)
    } else {
        lb.rf_copy().rf_div(&big_a)
    };

    // re_y = cy - b*h/A
    let re_y = cy.rf_sub(&lb.rf_mul(&h).rf_div(&big_a));

    // im_y = ±a/A
    let im_y = if plus {
        la.rf_copy().rf_div(&big_a)
    } else {
        la.rf_neg().rf_div(&big_a)
    };

    // Build extension coordinates
    let x_ext = RuntimeQExt::<FV, R, F>::new(re_x, im_x, radicand_rt.rf_copy());
    let y_ext = RuntimeQExt::<FV, R, F>::new(re_y, im_y, radicand_rt.rf_copy());

    GenericRtPoint2::new(x_ext, y_ext)
}

// ═══════════════════════════════════════════════════════════════════
//  Generic circle-circle intersection (via radical axis)
// ═══════════════════════════════════════════════════════════════════

/// Compute circle-circle intersection in generic field.
///
/// First computes the radical axis (a line), then delegates to
/// circle-line intersection.
///
/// Mirrors spec: cc_intersection_point = cl_intersection_point(c1, radical_axis(c1, c2), plus).
pub fn generic_cc_intersection<
    FV: OrderedField,
    R: PositiveRadicand<FV>,
    F: RuntimeFieldOps<FV>,
>(
    // Circle 1: center (c1x, c1y), radius_sq1
    c1x: &F, c1y: &F, r1sq: &F,
    // Circle 2: center (c2x, c2y), radius_sq2
    c2x: &F, c2y: &F, r2sq: &F,
    // Radicand runtime value
    radicand_rt: &F,
    plus: bool,
) -> (out: GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>)
    requires
        c1x.wf_spec(), c1y.wf_spec(), r1sq.wf_spec(),
        c2x.wf_spec(), c2y.wf_spec(), r2sq.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt.rf_view() == R::value(),
        // Radical axis must be non-degenerate (centers not coincident in both coords)
        ({
            let two = FV::one().add(FV::one());
            let ra = two.mul(c2x.rf_view().sub(c1x.rf_view()));
            let rb = two.mul(c2y.rf_view().sub(c1y.rf_view()));
            !ra.mul(ra).add(rb.mul(rb)).eqv(FV::zero())
        }),
    ensures
        out.wf_spec(),
{
    // Compute radical axis: Line2 { a: 2(c2x-c1x), b: 2(c2y-c1y), c: ... }
    let one = c1x.rf_one_like();
    let two = one.rf_add(&c1x.rf_one_like());

    let la = two.rf_mul(&c2x.rf_sub(c1x));
    let lb = two.rf_mul(&c2y.rf_sub(c1y));

    // c = c1x² + c1y² - r1sq - (c2x² + c2y² - r2sq)
    let c1_sq = c1x.rf_mul(c1x).rf_add(&c1y.rf_mul(c1y));
    let c2_sq = c2x.rf_mul(c2x).rf_add(&c2y.rf_mul(c2y));
    let lc = c1_sq.rf_sub(r1sq).rf_sub(&c2_sq.rf_sub(r2sq));

    // Delegate to circle-line intersection (circle 1 with the radical axis)
    generic_cl_intersection::<FV, R, F>(
        c1x, c1y, r1sq,
        &la, &lb, &lc,
        radicand_rt,
        plus,
    )
}

// ═══════════════════════════════════════════════════════════════════
//  Locus intersection helper: intersect two GenericRtLocus values
// ═══════════════════════════════════════════════════════════════════

/// Intersect two loci (circle+line or circle+circle) to produce an
/// intersection point in the extension field.
///
/// Returns None if the loci combination is not a valid intersection
/// (e.g., two lines, point loci, or full planes).
pub fn intersect_loci<
    FV: OrderedField,
    R: PositiveRadicand<FV>,
    F: RuntimeFieldOps<FV>,
>(
    locus1: &GenericRtLocus<FV, F>,
    locus2: &GenericRtLocus<FV, F>,
    radicand_rt: &F,
    plus: bool,
) -> (out: Option<GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>>)
    requires
        locus1.wf_spec(),
        locus2.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt.rf_view() == R::value(),
    ensures
        out.is_some() ==> out.unwrap().wf_spec(),
{
    match (locus1, locus2) {
        // Circle + Line
        (GenericRtLocus::OnCircle { cx, cy, radius_sq, .. },
         GenericRtLocus::OnLine { a, b, c, .. }) => {
            let a_sq = a.rf_mul(a);
            let b_sq = b.rf_mul(b);
            let big_a = a_sq.rf_add(&b_sq);
            let zero = cx.rf_zero_like();
            if big_a.rf_eq(&zero) {
                return None;  // degenerate line
            }
            Some(generic_cl_intersection::<FV, R, F>(
                cx, cy, radius_sq, a, b, c, radicand_rt, plus,
            ))
        }

        // Line + Circle (swap)
        (GenericRtLocus::OnLine { a, b, c, .. },
         GenericRtLocus::OnCircle { cx, cy, radius_sq, .. }) => {
            let a_sq = a.rf_mul(a);
            let b_sq = b.rf_mul(b);
            let big_a = a_sq.rf_add(&b_sq);
            let zero = cx.rf_zero_like();
            if big_a.rf_eq(&zero) {
                return None;
            }
            Some(generic_cl_intersection::<FV, R, F>(
                cx, cy, radius_sq, a, b, c, radicand_rt, plus,
            ))
        }

        // Circle + Circle
        (GenericRtLocus::OnCircle { cx: c1x, cy: c1y, radius_sq: r1sq, .. },
         GenericRtLocus::OnCircle { cx: c2x, cy: c2y, radius_sq: r2sq, .. }) => {
            // Check radical axis non-degeneracy
            let one = c1x.rf_one_like();
            let two = one.rf_add(&c1x.rf_one_like());
            let ra = two.rf_mul(&c2x.rf_sub(c1x));
            let rb = two.rf_mul(&c2y.rf_sub(c1y));
            let ra_sq = ra.rf_mul(&ra);
            let rb_sq = rb.rf_mul(&rb);
            let norm = ra_sq.rf_add(&rb_sq);
            let zero = c1x.rf_zero_like();
            if norm.rf_eq(&zero) {
                return None;  // concentric circles
            }
            Some(generic_cc_intersection::<FV, R, F>(
                c1x, c1y, r1sq, c2x, c2y, r2sq, radicand_rt, plus,
            ))
        }

        // All other combinations: not a valid intersection for circle steps
        _ => None,
    }
}

} // verus!
