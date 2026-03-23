use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::orient2d::orient2d;
use verus_geometry::constructed_scalar::{qext_from_rational, lift_point2};
use verus_geometry::runtime::point2::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::ordered::{qe_nonneg, qe_le};
use verus_quadratic_extension::runtime::{RuntimeQExtRat, RuntimeRadicand};
use crate::entities::*;
use crate::constraints::*;
use crate::construction::step_target;
use crate::construction_ext::{lift_constraint, is_rational_step};
use crate::runtime::constraint::*;
use crate::runtime::construction::*;

type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Helper: qe_nonneg(x) ==> zero().le(x)
// ===========================================================================

/// Bridge from qe_nonneg to the PartialOrder::le formulation.
/// zero().le(x) == qe_nonneg(qe_sub(x, zero())) == qe_nonneg(qext(x.re - 0, x.im - 0)).
/// Since a - 0 ≡ a for ordered fields, nonneg_congruence gives the result.
proof fn lemma_nonneg_implies_zero_le<F: OrderedField, R: PositiveRadicand<F>>(
    x: SpecQuadExt<F, R>,
)
    requires qe_nonneg::<F, R>(x),
    ensures SpecQuadExt::<F, R>::zero().le(x),
{
    // zero().le(x) = qe_nonneg(qe_sub(x, zero()))
    // qe_sub(x, zero()) = qext(x.re.sub(F::zero()), x.im.sub(F::zero()))
    // Since a.sub(zero) = a.add(zero.neg()) ≡ a.add(zero) ≡ a,
    // we use nonneg_congruence to transfer from x to qe_sub(x, zero()).
    use verus_algebra::lemmas::additive_group_lemmas::{lemma_neg_zero, lemma_add_congruence_right};

    // Show x.re.sub(zero) ≡ x.re
    // Step 1: sub(a, b) ≡ add(a, neg(b))
    F::axiom_sub_is_add_neg(x.re, F::zero());
    // Step 2: add(x.re, neg(zero)) ≡ add(x.re, zero)  [since neg(zero) ≡ zero]
    lemma_neg_zero::<F>();
    lemma_add_congruence_right::<F>(x.re, F::zero().neg(), F::zero());
    // Step 3: add(x.re, zero) ≡ x.re
    F::axiom_add_zero_right(x.re);
    // Chain: sub ≡ add(neg) ≡ add(zero) ≡ x.re
    F::axiom_eqv_transitive(x.re.sub(F::zero()), x.re.add(F::zero().neg()), x.re.add(F::zero()));
    F::axiom_eqv_transitive(x.re.sub(F::zero()), x.re.add(F::zero()), x.re);

    // Show x.im.sub(zero) ≡ x.im (same chain)
    F::axiom_sub_is_add_neg(x.im, F::zero());
    lemma_add_congruence_right::<F>(x.im, F::zero().neg(), F::zero());
    F::axiom_add_zero_right(x.im);
    F::axiom_eqv_transitive(x.im.sub(F::zero()), x.im.add(F::zero().neg()), x.im.add(F::zero()));
    F::axiom_eqv_transitive(x.im.sub(F::zero()), x.im.add(F::zero()), x.im);

    // Symmetric: x.re ≡ x.re.sub(zero) (nonneg_congruence needs this direction)
    F::axiom_eqv_symmetric(x.re.sub(F::zero()), x.re);
    F::axiom_eqv_symmetric(x.im.sub(F::zero()), x.im);

    // nonneg_congruence: qe_nonneg(x) && x.re ≡ sub.re && x.im ≡ sub.im ==> qe_nonneg(sub)
    verus_quadratic_extension::ordered::lemma_nonneg_congruence::<F, R>(x,
        qe_sub::<F, R>(x, qe_zero::<F, R>()));
}

// ===========================================================================
//  2a: QExt embedding helpers
// ===========================================================================

/// Embed a rational value into Q(√d): v ↦ v + 0·√d
fn embed_rational<R: Radicand<RationalModel>>(
    v: &RuntimeRational,
) -> (out: RuntimeQExtRat<R>)
    requires v.wf_spec(),
    ensures out.wf_spec(), out@ == qext_from_rational::<RationalModel, R>(v@),
{
    let re = copy_rational(v);
    let im = RuntimeRational::from_int(0);
    RuntimeQExtRat::<R>::new(re, im)
}

/// Embed a rational point into Q(√d): (x, y) ↦ (x + 0·√d, y + 0·√d)
fn embed_rational_point<R: Radicand<RationalModel>>(
    p: &RuntimePoint2,
) -> (out: RuntimeQExtPoint2<R>)
    requires p.wf_spec(),
    ensures out.wf_spec(), out@ == lift_point2::<RationalModel, R>(p@),
{
    let x = embed_rational::<R>(&p.x);
    let y = embed_rational::<R>(&p.y);
    RuntimeQExtPoint2 { x, y, model: Ghost(lift_point2::<RationalModel, R>(p@)) }
}

// ===========================================================================
//  2b: QExt arithmetic helpers
// ===========================================================================

/// QExt squared distance: ||a - b||²
fn qext_sq_dist_2d<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    a: &RuntimeQExtPoint2<R>,
    b: &RuntimeQExtPoint2<R>,
) -> (out: RuntimeQExtRat<R>)
    requires a.wf_spec(), b.wf_spec(),
    ensures out.wf_spec(), out@ == sq_dist_2d::<SpecQuadExt<RationalModel, R>>(a@, b@),
{
    let dx = a.x.sub_exec(&b.x);
    let dy = a.y.sub_exec(&b.y);
    let dx2 = dx.mul_exec::<RR>(&dx);
    let dy2 = dy.mul_exec::<RR>(&dy);
    dx2.add_exec(&dy2)
}

/// QExt line2_from_points: line through two points, returns (a, b, c) coefficients.
/// Mirrors spec: a = -(q.y - p.y), b = q.x - p.x, c = -(a*p.x + b*p.y)
fn qext_line2_from_points<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    p: &RuntimeQExtPoint2<R>,
    q: &RuntimeQExtPoint2<R>,
) -> (out: (RuntimeQExtRat<R>, RuntimeQExtRat<R>, RuntimeQExtRat<R>))
    requires p.wf_spec(), q.wf_spec(),
    ensures
        out.0.wf_spec(), out.1.wf_spec(), out.2.wf_spec(),
        ({
            let line = line2_from_points::<SpecQuadExt<RationalModel, R>>(p@, q@);
            out.0@ == line.a && out.1@ == line.b && out.2@ == line.c
        }),
{
    // spec: a = q.y.sub(p.y).neg(), b = q.x.sub(p.x), c = a.mul(p.x).add(b.mul(p.y)).neg()
    // a = (q.y - p.y).neg() = p.y - q.y
    let a = q.y.sub_exec(&p.y).neg_exec();
    let b = q.x.sub_exec(&p.x);
    // c = -(a * p.x + b * p.y)
    let ax = a.mul_exec::<RR>(&p.x);
    let by = b.mul_exec::<RR>(&p.y);
    let sum = ax.add_exec(&by);
    let c = sum.neg_exec();
    (a, b, c)
}

/// QExt line2_eval: a*p.x + b*p.y + c
fn qext_line2_eval<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    la: &RuntimeQExtRat<R>,
    lb: &RuntimeQExtRat<R>,
    lc: &RuntimeQExtRat<R>,
    p: &RuntimeQExtPoint2<R>,
) -> (out: RuntimeQExtRat<R>)
    requires la.wf_spec(), lb.wf_spec(), lc.wf_spec(), p.wf_spec(),
    ensures
        out.wf_spec(),
        out@ == line2_eval::<SpecQuadExt<RationalModel, R>>(
            Line2 { a: la@, b: lb@, c: lc@ }, p@),
{
    let ax = la.mul_exec::<RR>(&p.x);
    let by = lb.mul_exec::<RR>(&p.y);
    let sum = ax.add_exec(&by);
    sum.add_exec(lc)
}

// ===========================================================================
//  2c: Build extension resolved vec
// ===========================================================================

/// Spec helper: view an ext points vec as a resolved map.
pub open spec fn ext_vec_to_resolved_map<R: Radicand<RationalModel>>(
    ext_points: Seq<RuntimeQExtPoint2<R>>,
) -> ResolvedPoints<SpecQuadExt<RationalModel, R>> {
    Map::new(
        |id: nat| (id as int) < ext_points.len(),
        |id: nat| ext_points[id as int]@,
    )
}

/// Build a Vec of QExt points from execution results + plan steps + initial (rational) points.
/// Initial points are embedded; execution results are either embedded (rational)
/// or copied (QExt). The output vec has the same length as initial_points.
/// The plan steps provide exec-level target IDs for indexing.
pub fn build_ext_resolved_vec<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    results: &Vec<RuntimeConstructionResult<R>>,
    steps: &Vec<RuntimeStepData>,
    initial_points: &Vec<RuntimePoint2>,
) -> (out: Vec<RuntimeQExtPoint2<R>>)
    requires
        all_points_wf(initial_points@),
        results@.len() == steps@.len(),
        forall|i: int| 0 <= i < results@.len() ==> (#[trigger] results@[i]).wf_spec(),
        forall|i: int| 0 <= i < steps@.len() ==> (#[trigger] steps@[i]).wf_spec(),
        forall|i: int| 0 <= i < results@.len() ==>
            (#[trigger] results@[i]).entity_id() == step_target(steps@[i].spec_step()),
        forall|i: int| 0 <= i < steps@.len() ==>
            (step_target(#[trigger] steps@[i].spec_step()) as int) < initial_points@.len(),
        // Distinct entity IDs across results
        forall|i: int, j: int| 0 <= i < results@.len() && 0 <= j < results@.len() && i != j
            ==> (#[trigger] results@[i]).entity_id() != (#[trigger] results@[j]).entity_id(),
    ensures
        out@.len() == initial_points@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        // Overwritten entries: result ext_point_value
        forall|k: int| 0 <= k < results@.len()
            ==> out@[results@[k].entity_id() as int]@ == (#[trigger] results@[k]).ext_point_value(),
        // Non-overwritten entries: lifted initial points
        forall|j: int| 0 <= j < out@.len()
            && (forall|k: int| 0 <= k < results@.len()
                ==> (#[trigger] results@[k]).entity_id() != j as nat)
            ==> out@[j]@ == lift_point2::<RationalModel, R>(initial_points@[j]@),
{
    let n = initial_points.len();

    // Start by embedding all initial points
    let mut ext_points: Vec<RuntimeQExtPoint2<R>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == initial_points@.len(),
            ext_points@.len() == i as int,
            all_points_wf(initial_points@),
            forall|j: int| 0 <= j < ext_points@.len() ==> (#[trigger] ext_points@[j]).wf_spec(),
            forall|j: int| 0 <= j < ext_points@.len() ==>
                ext_points@[j]@ == lift_point2::<RationalModel, R>(initial_points@[j]@),
        decreases n - i,
    {
        let pt = embed_rational_point::<R>(&initial_points[i]);
        ext_points.push(pt);
        i = i + 1;
    }

    // Overwrite with execution results using plan step targets for indexing
    let mut ri: usize = 0;
    while ri < results.len()
        invariant
            ri <= results@.len(),
            ext_points@.len() == n as int,
            n == initial_points@.len(),
            results@.len() == steps@.len(),
            forall|i: int| 0 <= i < results@.len() ==> (#[trigger] results@[i]).wf_spec(),
            forall|i: int| 0 <= i < steps@.len() ==> (#[trigger] steps@[i]).wf_spec(),
            forall|i: int| 0 <= i < results@.len() ==>
                (#[trigger] results@[i]).entity_id() == step_target(steps@[i].spec_step()),
            forall|i: int| 0 <= i < steps@.len() ==>
                (step_target(#[trigger] steps@[i].spec_step()) as int) < n,
            forall|i: int, j: int| 0 <= i < results@.len() && 0 <= j < results@.len() && i != j
                ==> (#[trigger] results@[i]).entity_id() != (#[trigger] results@[j]).entity_id(),
            forall|j: int| 0 <= j < ext_points@.len() ==> (#[trigger] ext_points@[j]).wf_spec(),
            // Overwritten entries: result ext_point_value for k < ri
            forall|k: int| 0 <= k < ri ==>
                ext_points@[results@[k].entity_id() as int]@
                    == (#[trigger] results@[k]).ext_point_value(),
            // Non-overwritten entries: still initial
            forall|j: int| 0 <= j < n
                && (forall|k: int| 0 <= k < ri
                    ==> (#[trigger] results@[k]).entity_id() as int != j)
                ==> ext_points@[j]@ == lift_point2::<RationalModel, R>(initial_points@[j]@),
        decreases results@.len() - ri,
    {
        let idx = steps[ri].target_id();
        match &results[ri] {
            RuntimeConstructionResult::RationalPoint { point, entity_id } => {
                let embedded = embed_rational_point::<R>(point);
                let mut swap = embedded;
                ext_points.set_and_swap(idx, &mut swap);
            }
            RuntimeConstructionResult::QExtPoint { point, entity_id } => {
                let copied = RuntimeQExtPoint2 {
                    x: point.x.copy_exec(),
                    y: point.y.copy_exec(),
                    model: Ghost(point@),
                };
                let mut swap = copied;
                ext_points.set_and_swap(idx, &mut swap);
            }
        }
        ri = ri + 1;
    }
    ext_points
}

// ===========================================================================
//  2d: Verification constraint checkers at QExt level
// ===========================================================================

/// Check Tangent constraint at QExt level:
/// eval² ≡ norm_sq · r_sq
/// where eval = line2_eval(line_from_points(la, lb), center),
///       norm_sq = a² + b²,
///       r_sq = sq_dist_2d(center, radius_point).
fn check_tangent_ext<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    line_a_pt: &RuntimeQExtPoint2<R>,
    line_b_pt: &RuntimeQExtPoint2<R>,
    center: &RuntimeQExtPoint2<R>,
    radius_point: &RuntimeQExtPoint2<R>,
) -> (out: bool)
    requires
        line_a_pt.wf_spec(), line_b_pt.wf_spec(),
        center.wf_spec(), radius_point.wf_spec(),
    ensures
        out ==> {
            let line = line2_from_points::<SpecQuadExt<RationalModel, R>>(line_a_pt@, line_b_pt@);
            let eval = line2_eval(line, center@);
            let norm_sq = line.a.mul(line.a).add(line.b.mul(line.b));
            let r_sq = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(center@, radius_point@);
            eval.mul(eval).eqv(norm_sq.mul(r_sq))
        },
{
    let (la, lb, lc) = qext_line2_from_points::<R, RR>(line_a_pt, line_b_pt);
    let eval = qext_line2_eval::<R, RR>(&la, &lb, &lc, center);
    let eval_sq = eval.mul_exec::<RR>(&eval);
    let a_sq = la.mul_exec::<RR>(&la);
    let b_sq = lb.mul_exec::<RR>(&lb);
    let norm_sq = a_sq.add_exec(&b_sq);
    let r_sq = qext_sq_dist_2d::<R, RR>(center, radius_point);
    let lhs = eval_sq;
    let rhs = norm_sq.mul_exec::<RR>(&r_sq);
    lhs.eq_exec(&rhs)
}

/// Check CircleTangent constraint at QExt level:
/// (d - r1 - r2)² ≡ 4 · r1 · r2
/// where d = sq_dist_2d(c1, c2), r1 = sq_dist_2d(c1, rp1), r2 = sq_dist_2d(c2, rp2).
fn check_circle_tangent_ext<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    c1: &RuntimeQExtPoint2<R>,
    rp1: &RuntimeQExtPoint2<R>,
    c2: &RuntimeQExtPoint2<R>,
    rp2: &RuntimeQExtPoint2<R>,
) -> (out: bool)
    requires c1.wf_spec(), rp1.wf_spec(), c2.wf_spec(), rp2.wf_spec(),
    ensures
        out ==> {
            let d = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(c1@, c2@);
            let r1 = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(c1@, rp1@);
            let r2 = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(c2@, rp2@);
            let t_one = SpecQuadExt::<RationalModel, R>::one();
            let four = t_one.add(t_one).mul(t_one.add(t_one));
            let diff = d.sub(r1).sub(r2);
            diff.mul(diff).eqv(four.mul(r1).mul(r2))
        },
{
    let d = qext_sq_dist_2d::<R, RR>(c1, c2);
    let r1 = qext_sq_dist_2d::<R, RR>(c1, rp1);
    let r2 = qext_sq_dist_2d::<R, RR>(c2, rp2);
    // four = 1+1+1+1 = (1+1)*(1+1)
    let one = RuntimeQExtRat::<R>::one_exec();
    let two = one.add_exec(&one);
    let four = two.mul_exec::<RR>(&two);
    // diff = d - r1 - r2
    let diff = d.sub_exec(&r1).sub_exec(&r2);
    let lhs = diff.mul_exec::<RR>(&diff);
    let rhs = four.mul_exec::<RR>(&r1).mul_exec::<RR>(&r2);
    lhs.eq_exec(&rhs)
}

/// Check Angle constraint at QExt level:
/// dp² ≡ cos_sq · n1 · n2
/// where dp = dot(d1, d2), n1 = |d1|², n2 = |d2|²,
///       d1 = a2 - a1, d2 = b2 - b1.
fn check_angle_ext<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    a1: &RuntimeQExtPoint2<R>,
    a2: &RuntimeQExtPoint2<R>,
    b1: &RuntimeQExtPoint2<R>,
    b2: &RuntimeQExtPoint2<R>,
    cos_sq: &RuntimeRational,
) -> (out: bool)
    requires
        a1.wf_spec(), a2.wf_spec(), b1.wf_spec(), b2.wf_spec(),
        cos_sq.wf_spec(),
    ensures
        out ==> {
            let d1 = sub2::<SpecQuadExt<RationalModel, R>>(a2@, a1@);
            let d2 = sub2::<SpecQuadExt<RationalModel, R>>(b2@, b1@);
            let dp = d1.x.mul(d2.x).add(d1.y.mul(d2.y));
            let n1 = d1.x.mul(d1.x).add(d1.y.mul(d1.y));
            let n2 = d2.x.mul(d2.x).add(d2.y.mul(d2.y));
            let cos_sq_ext = qext_from_rational::<RationalModel, R>(cos_sq@);
            dp.mul(dp).eqv(cos_sq_ext.mul(n1).mul(n2))
        },
{
    // d1 = a2 - a1
    let dx1 = a2.x.sub_exec(&a1.x);
    let dy1 = a2.y.sub_exec(&a1.y);
    // d2 = b2 - b1
    let dx2 = b2.x.sub_exec(&b1.x);
    let dy2 = b2.y.sub_exec(&b1.y);
    // dp = d1.x * d2.x + d1.y * d2.y
    let dp = dx1.mul_exec::<RR>(&dx2).add_exec(&dy1.mul_exec::<RR>(&dy2));
    // n1 = d1.x² + d1.y²
    let n1 = dx1.mul_exec::<RR>(&dx1).add_exec(&dy1.mul_exec::<RR>(&dy1));
    // n2 = d2.x² + d2.y²
    let n2 = dx2.mul_exec::<RR>(&dx2).add_exec(&dy2.mul_exec::<RR>(&dy2));
    // cos_sq embedded into QExt
    let cos_sq_ext = embed_rational::<R>(cos_sq);
    let lhs = dp.mul_exec::<RR>(&dp);
    let rhs = cos_sq_ext.mul_exec::<RR>(&n1).mul_exec::<RR>(&n2);
    lhs.eq_exec(&rhs)
}

/// QExt orient2d: (b.x-a.x)*(c.y-a.y) - (b.y-a.y)*(c.x-a.x)
fn qext_orient2d<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    a: &RuntimeQExtPoint2<R>,
    b: &RuntimeQExtPoint2<R>,
    c: &RuntimeQExtPoint2<R>,
) -> (out: RuntimeQExtRat<R>)
    requires a.wf_spec(), b.wf_spec(), c.wf_spec(),
    ensures out.wf_spec(),
        out@ == verus_geometry::orient2d::orient2d::<SpecQuadExt<RationalModel, R>>(a@, b@, c@),
{
    let bx_ax = b.x.sub_exec(&a.x);
    let by_ay = b.y.sub_exec(&a.y);
    let cx_ax = c.x.sub_exec(&a.x);
    let cy_ay = c.y.sub_exec(&a.y);
    bx_ax.mul_exec::<RR>(&cy_ay).sub_exec(&by_ay.mul_exec::<RR>(&cx_ax))
}

/// Check NotCoincident at QExt level: !(a.x ≡ b.x && a.y ≡ b.y)
fn check_not_coincident_ext<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    a: &RuntimeQExtPoint2<R>,
    b: &RuntimeQExtPoint2<R>,
) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(),
    ensures out ==> !a@.eqv(b@),
{
    !(a.x.eq_exec(&b.x) && a.y.eq_exec(&b.y))
}

/// Check NormalToCircle at QExt level: on_circle(line_a, center, radius_point) && collinear(line_a, line_b, center)
fn check_normal_to_circle_ext<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    line_a: &RuntimeQExtPoint2<R>,
    line_b: &RuntimeQExtPoint2<R>,
    center: &RuntimeQExtPoint2<R>,
    radius_point: &RuntimeQExtPoint2<R>,
) -> (out: bool)
    requires line_a.wf_spec(), line_b.wf_spec(), center.wf_spec(), radius_point.wf_spec(),
    ensures out ==> {
        // on_circle: sq_dist(line_a, center) ≡ sq_dist(radius_point, center)
        let on_circle = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(line_a@, center@).eqv(
            sq_dist_2d::<SpecQuadExt<RationalModel, R>>(radius_point@, center@));
        // collinear: point_on_line2(line_from_points(line_a, line_b), center)
        let collinear = point_on_line2(
            line2_from_points::<SpecQuadExt<RationalModel, R>>(line_a@, line_b@),
            center@);
        on_circle && collinear
    },
{
    // Check on_circle
    let d_la = qext_sq_dist_2d::<R, RR>(line_a, center);
    let d_rp = qext_sq_dist_2d::<R, RR>(radius_point, center);
    let on_circle = d_la.eq_exec(&d_rp);
    if !on_circle { return false; }
    // Check collinear
    let (la, lb, lc) = qext_line2_from_points::<R, RR>(line_a, line_b);
    let eval = qext_line2_eval::<R, RR>(&la, &lb, &lc, center);
    let zero = RuntimeQExtRat::<R>::zero_exec();
    eval.eq_exec(&zero) && on_circle
}

/// Check PointOnEllipse at QExt level:
/// proj_u² * b_sq + proj_v² * a_sq ≡ a_sq * b_sq
fn check_point_on_ellipse_ext<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    point: &RuntimeQExtPoint2<R>,
    center: &RuntimeQExtPoint2<R>,
    semi_a: &RuntimeQExtPoint2<R>,
    semi_b: &RuntimeQExtPoint2<R>,
) -> (out: bool)
    requires point.wf_spec(), center.wf_spec(), semi_a.wf_spec(), semi_b.wf_spec(),
    ensures out ==> {
        let d = sub2::<SpecQuadExt<RationalModel, R>>(point@, center@);
        let u = sub2::<SpecQuadExt<RationalModel, R>>(semi_a@, center@);
        let vv = sub2::<SpecQuadExt<RationalModel, R>>(semi_b@, center@);
        let a_sq = u.x.mul(u.x).add(u.y.mul(u.y));
        let b_sq = vv.x.mul(vv.x).add(vv.y.mul(vv.y));
        let proj_u = d.x.mul(u.x).add(d.y.mul(u.y));
        let proj_v = d.x.mul(vv.x).add(d.y.mul(vv.y));
        proj_u.mul(proj_u).mul(b_sq).add(proj_v.mul(proj_v).mul(a_sq))
            .eqv(a_sq.mul(b_sq))
    },
{
    // d = point - center
    let dx = point.x.sub_exec(&center.x);
    let dy = point.y.sub_exec(&center.y);
    // u = semi_a - center
    let ux = semi_a.x.sub_exec(&center.x);
    let uy = semi_a.y.sub_exec(&center.y);
    // v = semi_b - center
    let vx = semi_b.x.sub_exec(&center.x);
    let vy = semi_b.y.sub_exec(&center.y);
    // a_sq = |u|²
    let a_sq = ux.mul_exec::<RR>(&ux).add_exec(&uy.mul_exec::<RR>(&uy));
    // b_sq = |v|²
    let b_sq = vx.mul_exec::<RR>(&vx).add_exec(&vy.mul_exec::<RR>(&vy));
    // proj_u = dot(d, u)
    let proj_u = dx.mul_exec::<RR>(&ux).add_exec(&dy.mul_exec::<RR>(&uy));
    // proj_v = dot(d, v)
    let proj_v = dx.mul_exec::<RR>(&vx).add_exec(&dy.mul_exec::<RR>(&vy));
    // Check: proj_u² * b_sq + proj_v² * a_sq ≡ a_sq * b_sq
    let lhs = proj_u.mul_exec::<RR>(&proj_u).mul_exec::<RR>(&b_sq)
        .add_exec(&proj_v.mul_exec::<RR>(&proj_v).mul_exec::<RR>(&a_sq));
    let rhs = a_sq.mul_exec::<RR>(&b_sq);
    lhs.eq_exec(&rhs)
}

/// Check PointOnArc at QExt level:
/// on_circle AND angular check via orient2d sign consistency.
fn check_point_on_arc_ext<R: PositiveRadicand<RationalModel>, RR: RuntimeRadicand<R>>(
    point: &RuntimeQExtPoint2<R>,
    center: &RuntimeQExtPoint2<R>,
    radius_point: &RuntimeQExtPoint2<R>,
    arc_start: &RuntimeQExtPoint2<R>,
    arc_end: &RuntimeQExtPoint2<R>,
) -> (out: bool)
    requires point.wf_spec(), center.wf_spec(), radius_point.wf_spec(),
             arc_start.wf_spec(), arc_end.wf_spec(),
    ensures out ==> {
        let on_circle = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(point@, center@).eqv(
            sq_dist_2d::<SpecQuadExt<RationalModel, R>>(radius_point@, center@));
        let o_se = orient2d::<SpecQuadExt<RationalModel, R>>(center@, arc_start@, arc_end@);
        let o_sp = orient2d::<SpecQuadExt<RationalModel, R>>(center@, arc_start@, point@);
        let o_pe = orient2d::<SpecQuadExt<RationalModel, R>>(center@, point@, arc_end@);
        on_circle &&
        SpecQuadExt::<RationalModel, R>::zero().le(o_sp.mul(o_se)) &&
        SpecQuadExt::<RationalModel, R>::zero().le(o_pe.mul(o_se))
    },
{
    // Check on_circle
    let d_pt = qext_sq_dist_2d::<R, RR>(point, center);
    let d_rp = qext_sq_dist_2d::<R, RR>(radius_point, center);
    if !d_pt.eq_exec(&d_rp) { return false; }

    // Angular check: compute orient2d values and check sign consistency
    // orient2d(c, s, e), orient2d(c, s, p), orient2d(c, p, e)
    // Check: 0 <= o_sp * o_se && 0 <= o_pe * o_se
    // Using nonneg check via qext ordering
    let o_se = qext_orient2d::<R, RR>(center, arc_start, arc_end);
    let o_sp = qext_orient2d::<R, RR>(center, arc_start, point);
    let o_pe = qext_orient2d::<R, RR>(center, point, arc_end);
    let prod1 = o_sp.mul_exec::<RR>(&o_se);
    let prod2 = o_pe.mul_exec::<RR>(&o_se);
    let nn1 = prod1.nonneg_exec::<RR>();
    let nn2 = prod2.nonneg_exec::<RR>();
    proof {
        if nn1 {
            lemma_nonneg_implies_zero_le::<RationalModel, R>(prod1@);
        }
        if nn2 {
            lemma_nonneg_implies_zero_le::<RationalModel, R>(prod2@);
        }
    }
    nn1 && nn2
}

// ===========================================================================
//  2e: Lightweight predicate for verification check results
// ===========================================================================

/// Lightweight predicate: the algebraic identity for verification constraints
/// holds on the ext_points. Only matches the 3 verification types (Tangent,
/// CircleTangent, Angle), returns true for all others.
/// This avoids unfolding constraint_satisfied (19 arms) in tight loops.
pub open spec fn ext_verification_identity<R: PositiveRadicand<RationalModel>>(
    rc: RuntimeConstraint,
    ext_points: Seq<RuntimeQExtPoint2<R>>,
) -> bool {
    match rc {
        RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, .. } => {
            let line = line2_from_points::<SpecQuadExt<RationalModel, R>>(
                ext_points[line_a as int]@, ext_points[line_b as int]@);
            let eval = line2_eval(line, ext_points[center as int]@);
            let norm_sq = line.a.mul(line.a).add(line.b.mul(line.b));
            let r_sq = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[center as int]@, ext_points[radius_point as int]@);
            eval.mul(eval).eqv(norm_sq.mul(r_sq))
        }
        RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, .. } => {
            let d = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[c1 as int]@, ext_points[c2 as int]@);
            let r1 = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[c1 as int]@, ext_points[rp1 as int]@);
            let r2 = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[c2 as int]@, ext_points[rp2 as int]@);
            let t_one = SpecQuadExt::<RationalModel, R>::one();
            let four = t_one.add(t_one).mul(t_one.add(t_one));
            let diff = d.sub(r1).sub(r2);
            diff.mul(diff).eqv(four.mul(r1).mul(r2))
        }
        RuntimeConstraint::Angle { a1, a2, b1, b2, cos_sq, .. } => {
            let d1 = sub2::<SpecQuadExt<RationalModel, R>>(
                ext_points[a2 as int]@, ext_points[a1 as int]@);
            let d2 = sub2::<SpecQuadExt<RationalModel, R>>(
                ext_points[b2 as int]@, ext_points[b1 as int]@);
            let dp = d1.x.mul(d2.x).add(d1.y.mul(d2.y));
            let n1 = d1.x.mul(d1.x).add(d1.y.mul(d1.y));
            let n2 = d2.x.mul(d2.x).add(d2.y.mul(d2.y));
            let cos_sq_ext = qext_from_rational::<RationalModel, R>(cos_sq@);
            dp.mul(dp).eqv(cos_sq_ext.mul(n1).mul(n2))
        }
        RuntimeConstraint::NotCoincident { a, b, .. } => {
            !ext_points[a as int]@.eqv(ext_points[b as int]@)
        }
        RuntimeConstraint::NormalToCircle { line_a, line_b, center, radius_point, .. } => {
            sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[line_a as int]@, ext_points[center as int]@).eqv(
                sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                    ext_points[radius_point as int]@, ext_points[center as int]@))
            && point_on_line2(
                line2_from_points::<SpecQuadExt<RationalModel, R>>(
                    ext_points[line_a as int]@, ext_points[line_b as int]@),
                ext_points[center as int]@)
        }
        RuntimeConstraint::PointOnEllipse { point, center, semi_a, semi_b, .. } => {
            let d = sub2::<SpecQuadExt<RationalModel, R>>(ext_points[point as int]@, ext_points[center as int]@);
            let u = sub2::<SpecQuadExt<RationalModel, R>>(ext_points[semi_a as int]@, ext_points[center as int]@);
            let vv = sub2::<SpecQuadExt<RationalModel, R>>(ext_points[semi_b as int]@, ext_points[center as int]@);
            let a_sq = u.x.mul(u.x).add(u.y.mul(u.y));
            let b_sq = vv.x.mul(vv.x).add(vv.y.mul(vv.y));
            let proj_u = d.x.mul(u.x).add(d.y.mul(u.y));
            let proj_v = d.x.mul(vv.x).add(d.y.mul(vv.y));
            proj_u.mul(proj_u).mul(b_sq).add(proj_v.mul(proj_v).mul(a_sq))
                .eqv(a_sq.mul(b_sq))
        }
        RuntimeConstraint::PointOnArc { point, center, radius_point, arc_start, arc_end, .. } => {
            let on_circle = sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[point as int]@, ext_points[center as int]@).eqv(
                sq_dist_2d::<SpecQuadExt<RationalModel, R>>(
                    ext_points[radius_point as int]@, ext_points[center as int]@));
            let o_se = orient2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[center as int]@, ext_points[arc_start as int]@, ext_points[arc_end as int]@);
            let o_sp = orient2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[center as int]@, ext_points[arc_start as int]@, ext_points[point as int]@);
            let o_pe = orient2d::<SpecQuadExt<RationalModel, R>>(
                ext_points[center as int]@, ext_points[point as int]@, ext_points[arc_end as int]@);
            on_circle &&
            SpecQuadExt::<RationalModel, R>::zero().le(o_sp.mul(o_se)) &&
            SpecQuadExt::<RationalModel, R>::zero().le(o_pe.mul(o_se))
        }
        _ => true,
    }
}

/// Bridge: ext_verification_identity → constraint_satisfied.
/// Only needs to run once per constraint (not in a tight loop).
proof fn lemma_ext_identity_to_constraint_satisfied<R: PositiveRadicand<RationalModel>>(
    rc: RuntimeConstraint,
    ext_points: Seq<RuntimeQExtPoint2<R>>,
    n_points: nat,
)
    requires
        runtime_constraint_wf(rc, n_points),
        n_points == ext_points.len(),
        forall|i: int| 0 <= i < ext_points.len() ==> (#[trigger] ext_points[i]).wf_spec(),
        is_verification_constraint(runtime_constraint_model(rc)),
        ext_verification_identity::<R>(rc, ext_points),
    ensures
        constraint_satisfied(
            lift_constraint::<RationalModel, R>(runtime_constraint_model(rc)),
            ext_vec_to_resolved_map::<R>(ext_points)),
{
    let ext_map = ext_vec_to_resolved_map::<R>(ext_points);
    match rc {
        RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, model } => {
            assert(ext_map.dom().contains(line_a as nat));
            assert(ext_map.dom().contains(line_b as nat));
            assert(ext_map.dom().contains(center as nat));
            assert(ext_map.dom().contains(radius_point as nat));
            assert(ext_map[line_a as nat] == ext_points[line_a as int]@);
            assert(ext_map[line_b as nat] == ext_points[line_b as int]@);
            assert(ext_map[center as nat] == ext_points[center as int]@);
            assert(ext_map[radius_point as nat] == ext_points[radius_point as int]@);
        }
        RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, model } => {
            assert(ext_map.dom().contains(c1 as nat));
            assert(ext_map.dom().contains(rp1 as nat));
            assert(ext_map.dom().contains(c2 as nat));
            assert(ext_map.dom().contains(rp2 as nat));
            assert(ext_map[c1 as nat] == ext_points[c1 as int]@);
            assert(ext_map[rp1 as nat] == ext_points[rp1 as int]@);
            assert(ext_map[c2 as nat] == ext_points[c2 as int]@);
            assert(ext_map[rp2 as nat] == ext_points[rp2 as int]@);
        }
        RuntimeConstraint::Angle { a1, a2, b1, b2, cos_sq, model } => {
            assert(ext_map.dom().contains(a1 as nat));
            assert(ext_map.dom().contains(a2 as nat));
            assert(ext_map.dom().contains(b1 as nat));
            assert(ext_map.dom().contains(b2 as nat));
            assert(ext_map[a1 as nat] == ext_points[a1 as int]@);
            assert(ext_map[a2 as nat] == ext_points[a2 as int]@);
            assert(ext_map[b1 as nat] == ext_points[b1 as int]@);
            assert(ext_map[b2 as nat] == ext_points[b2 as int]@);
        }
        // New verification constraints: ext_verification_identity returns true unconditionally,
        // and constraint_satisfied for these holds trivially from the ext_points equality.
        RuntimeConstraint::NotCoincident { a, b, .. } => {
            assert(ext_map.dom().contains(a as nat));
            assert(ext_map.dom().contains(b as nat));
        }
        RuntimeConstraint::NormalToCircle { line_a, line_b, center, radius_point, .. } => {
            assert(ext_map.dom().contains(line_a as nat));
            assert(ext_map.dom().contains(line_b as nat));
            assert(ext_map.dom().contains(center as nat));
            assert(ext_map.dom().contains(radius_point as nat));
        }
        RuntimeConstraint::PointOnEllipse { point, center, semi_a, semi_b, .. } => {
            assert(ext_map.dom().contains(point as nat));
            assert(ext_map.dom().contains(center as nat));
            assert(ext_map.dom().contains(semi_a as nat));
            assert(ext_map.dom().contains(semi_b as nat));
        }
        RuntimeConstraint::PointOnArc { point, center, radius_point, arc_start, arc_end, .. } => {
            assert(ext_map.dom().contains(point as nat));
            assert(ext_map.dom().contains(center as nat));
            assert(ext_map.dom().contains(radius_point as nat));
            assert(ext_map.dom().contains(arc_start as nat));
            assert(ext_map.dom().contains(arc_end as nat));
        }
        _ => {} // impossible by is_verification_constraint
    }
}

// ===========================================================================
//  2f: Check all verification constraints at QExt level
// ===========================================================================

/// Check a single constraint at the ext level and establish ext_verification_identity.
/// Extracted from the loop body to reduce Z3 proof context.
fn check_single_verification_constraint_ext<
    R: PositiveRadicand<RationalModel>,
    RR: RuntimeRadicand<R>,
>(
    rc: &RuntimeConstraint,
    ext_points: &Vec<RuntimeQExtPoint2<R>>,
    n_points: usize,
) -> (out: bool)
    requires
        n_points == ext_points@.len(),
        forall|i: int| 0 <= i < ext_points@.len() ==> (#[trigger] ext_points@[i]).wf_spec(),
        runtime_constraint_wf(*rc, n_points as nat),
    ensures
        out && is_verification_constraint(runtime_constraint_model(*rc))
            ==> ext_verification_identity::<R>(*rc, ext_points@),
{
    match rc {
        RuntimeConstraint::Tangent { line_a, line_b, center, radius_point, .. } => {
            check_tangent_ext::<R, RR>(
                &ext_points[*line_a], &ext_points[*line_b],
                &ext_points[*center], &ext_points[*radius_point],
            )
        }
        RuntimeConstraint::CircleTangent { c1, rp1, c2, rp2, .. } => {
            check_circle_tangent_ext::<R, RR>(
                &ext_points[*c1], &ext_points[*rp1],
                &ext_points[*c2], &ext_points[*rp2],
            )
        }
        RuntimeConstraint::Angle { a1, a2, b1, b2, cos_sq, .. } => {
            check_angle_ext::<R, RR>(
                &ext_points[*a1], &ext_points[*a2],
                &ext_points[*b1], &ext_points[*b2],
                cos_sq,
            )
        }
        RuntimeConstraint::NotCoincident { a, b, .. } => {
            check_not_coincident_ext::<R, RR>(&ext_points[*a], &ext_points[*b])
        }
        RuntimeConstraint::NormalToCircle { line_a, line_b, center, radius_point, .. } => {
            check_normal_to_circle_ext::<R, RR>(
                &ext_points[*line_a], &ext_points[*line_b],
                &ext_points[*center], &ext_points[*radius_point])
        }
        RuntimeConstraint::PointOnEllipse { point, center, semi_a, semi_b, .. } => {
            check_point_on_ellipse_ext::<R, RR>(
                &ext_points[*point], &ext_points[*center],
                &ext_points[*semi_a], &ext_points[*semi_b])
        }
        RuntimeConstraint::PointOnArc { point, center, radius_point, arc_start, arc_end, .. } => {
            check_point_on_arc_ext::<R, RR>(
                &ext_points[*point], &ext_points[*center],
                &ext_points[*radius_point], &ext_points[*arc_start], &ext_points[*arc_end])
        }
        _ => true, // Non-verification constraints: skip
    }
}

/// Check all verification constraints are satisfied by the ext-level resolved points.
pub fn check_all_verification_constraints_ext<
    R: PositiveRadicand<RationalModel>,
    RR: RuntimeRadicand<R>,
>(
    constraints: &Vec<RuntimeConstraint>,
    ext_points: &Vec<RuntimeQExtPoint2<R>>,
    n_points: usize,
) -> (out: bool)
    requires
        n_points == ext_points@.len(),
        forall|i: int| 0 <= i < ext_points@.len() ==> (#[trigger] ext_points@[i]).wf_spec(),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
    ensures
        out ==> forall|ci: int| 0 <= ci < constraints@.len()
            && is_verification_constraint(runtime_constraint_model(#[trigger] constraints@[ci]))
            ==> constraint_satisfied(
                lift_constraint::<RationalModel, R>(runtime_constraint_model(constraints@[ci])),
                ext_vec_to_resolved_map::<R>(ext_points@)),
{
    // Phase 1: Loop accumulates the lightweight ext_verification_identity predicate.
    let mut ci: usize = 0;
    while ci < constraints.len()
        invariant
            ci <= constraints@.len(),
            n_points == ext_points@.len(),
            forall|i: int| 0 <= i < ext_points@.len() ==> (#[trigger] ext_points@[i]).wf_spec(),
            forall|i: int| 0 <= i < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[i], n_points as nat),
            forall|j: int| 0 <= j < ci
                && is_verification_constraint(runtime_constraint_model(#[trigger] constraints@[j]))
                ==> ext_verification_identity::<R>(constraints@[j], ext_points@),
        decreases constraints@.len() - ci,
    {
        let ok = check_single_verification_constraint_ext::<R, RR>(
            &constraints[ci], ext_points, n_points,
        );
        if !ok {
            return false;
        }
        ci = ci + 1;
    }

    // Phase 2: Bridge from lightweight identity to constraint_satisfied.
    proof {
        assert forall|ci: int| 0 <= ci < constraints@.len()
            && is_verification_constraint(runtime_constraint_model(#[trigger] constraints@[ci]))
        implies constraint_satisfied(
            lift_constraint::<RationalModel, R>(runtime_constraint_model(constraints@[ci])),
            ext_vec_to_resolved_map::<R>(ext_points@))
        by {
            lemma_ext_identity_to_constraint_satisfied::<R>(
                constraints@[ci], ext_points@, n_points as nat);
        }
    }
    true
}

} // verus!
