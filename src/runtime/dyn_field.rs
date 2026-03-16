/// Dynamic field element for arbitrary-depth quadratic extension towers.
///
/// `DynFieldElem` type-erases the tower level, allowing a single loop
/// to iterate `execute_circle_steps_at_level` for any depth. After each
/// level, `collapse_to_dyn` converts the `RuntimeQExt<DynTowerField, ...>`
/// output back to `DynFieldElem`, maintaining the same Rust type.
///
/// All arithmetic operations are `external_body` — their runtime behavior
/// is standard extension field arithmetic (correct by construction), and the
/// spec-level correspondence goes through the abstract DynTowerField type
/// whose axioms are all assumed.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_rational::rational::Rational;
use verus_geometry::point2::Point2;
use verus_geometry::runtime::point2::RuntimePoint2;
use verus_quadratic_extension::runtime_field::RuntimeFieldOps;
use verus_quadratic_extension::dyn_tower::*;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::runtime_qext::RuntimeQExt;
use crate::runtime::generic_point::GenericRtPoint2;

type RationalModel = Rational;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  DynFieldElem — recursive field element at any tower depth
// ═══════════════════════════════════════════════════════════════════

/// Runtime field element at any depth of the quadratic extension tower.
///
/// - `Rational(r)`: base-level element in Q
/// - `Extension { re, im, radicand }`: element `re + im·√radicand` where
///   re, im, radicand are themselves DynFieldElem at one level lower.
pub enum DynFieldElem {
    Rational(RuntimeRational),
    Extension {
        re: Box<DynFieldElem>,
        im: Box<DynFieldElem>,
        radicand: Box<DynFieldElem>,
    },
}

// ═══════════════════════════════════════════════════════════════════
//  Inherent methods (external_body — runtime arithmetic by construction)
// ═══════════════════════════════════════════════════════════════════

impl DynFieldElem {
    pub open spec fn dyn_wf(&self) -> bool
        decreases self,
    {
        match self {
            DynFieldElem::Rational(r) => r.wf_spec(),
            DynFieldElem::Extension { re, im, radicand } =>
                re.dyn_wf() && im.dyn_wf() && radicand.dyn_wf(),
        }
    }

    #[verifier::external_body]
    pub fn dyn_add(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out.dyn_wf()
    {
        match (self, rhs) {
            (DynFieldElem::Rational(a), DynFieldElem::Rational(b)) =>
                DynFieldElem::Rational(a.add(b)),
            (DynFieldElem::Extension { re: re1, im: im1, radicand: d1 },
             DynFieldElem::Extension { re: re2, im: im2, .. }) =>
                DynFieldElem::Extension {
                    re: Box::new(re1.dyn_add(re2)),
                    im: Box::new(im1.dyn_add(im2)),
                    radicand: Box::new(d1.dyn_copy()),
                },
            _ => panic!("mismatched DynFieldElem depths in add"),
        }
    }

    #[verifier::external_body]
    pub fn dyn_sub(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out.dyn_wf()
    {
        match (self, rhs) {
            (DynFieldElem::Rational(a), DynFieldElem::Rational(b)) =>
                DynFieldElem::Rational(a.sub(b)),
            (DynFieldElem::Extension { re: re1, im: im1, radicand: d1 },
             DynFieldElem::Extension { re: re2, im: im2, .. }) =>
                DynFieldElem::Extension {
                    re: Box::new(re1.dyn_sub(re2)),
                    im: Box::new(im1.dyn_sub(im2)),
                    radicand: Box::new(d1.dyn_copy()),
                },
            _ => panic!("mismatched DynFieldElem depths in sub"),
        }
    }

    #[verifier::external_body]
    pub fn dyn_neg(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf()
    {
        match self {
            DynFieldElem::Rational(a) => DynFieldElem::Rational(a.neg()),
            DynFieldElem::Extension { re, im, radicand } =>
                DynFieldElem::Extension {
                    re: Box::new(re.dyn_neg()),
                    im: Box::new(im.dyn_neg()),
                    radicand: Box::new(radicand.dyn_copy()),
                },
        }
    }

    #[verifier::external_body]
    pub fn dyn_mul(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out.dyn_wf()
    {
        match (self, rhs) {
            (DynFieldElem::Rational(a), DynFieldElem::Rational(b)) =>
                DynFieldElem::Rational(a.mul(b)),
            (DynFieldElem::Extension { re: a, im: b, radicand: d },
             DynFieldElem::Extension { re: c, im: e, .. }) => {
                let ac = a.dyn_mul(c);
                let be = b.dyn_mul(e);
                let bed = be.dyn_mul(d);
                let re_out = ac.dyn_add(&bed);
                let ae = a.dyn_mul(e);
                let bc = b.dyn_mul(c);
                let im_out = ae.dyn_add(&bc);
                DynFieldElem::Extension {
                    re: Box::new(re_out),
                    im: Box::new(im_out),
                    radicand: Box::new(d.dyn_copy()),
                }
            }
            _ => panic!("mismatched DynFieldElem depths in mul"),
        }
    }

    #[verifier::external_body]
    pub fn dyn_eq(&self, rhs: &Self) -> (out: bool)
        requires self.dyn_wf(), rhs.dyn_wf()
    {
        match (self, rhs) {
            (DynFieldElem::Rational(a), DynFieldElem::Rational(b)) => a.eq(b),
            (DynFieldElem::Extension { re: re1, im: im1, .. },
             DynFieldElem::Extension { re: re2, im: im2, .. }) =>
                re1.dyn_eq(re2) && im1.dyn_eq(im2),
            _ => false,
        }
    }

    #[verifier::external_body]
    pub fn dyn_nonneg(&self) -> (out: bool)
        requires self.dyn_wf()
    {
        match self {
            DynFieldElem::Rational(r) => {
                let zero = RuntimeRational::from_int(0);
                zero.le(r)
            }
            DynFieldElem::Extension { re: a, im: b, radicand: d } => {
                let zero = a.dyn_zero_like();
                let a_nonneg = zero.dyn_le(a);
                let zero2 = a.dyn_zero_like();
                let b_nonneg = zero2.dyn_le(b);

                if a_nonneg && b_nonneg { return true; }

                let a_sq = a.dyn_mul(a);
                let b_sq = b.dyn_mul(b);
                let b2d = b_sq.dyn_mul(d);

                let zero3 = a.dyn_zero_like();
                let b_neg = b.dyn_lt(&zero3);
                let zero4 = a.dyn_zero_like();
                let a_neg = a.dyn_lt(&zero4);
                let zero5 = a.dyn_zero_like();
                let b_pos = zero5.dyn_lt(b);

                if a_nonneg && b_neg && b2d.dyn_le(&a_sq) { return true; }
                if a_neg && b_pos && a_sq.dyn_le(&b2d) { return true; }
                false
            }
        }
    }

    #[verifier::external_body]
    pub fn dyn_le(&self, rhs: &Self) -> (out: bool)
        requires self.dyn_wf(), rhs.dyn_wf()
    {
        rhs.dyn_sub(self).dyn_nonneg()
    }

    #[verifier::external_body]
    pub fn dyn_lt(&self, rhs: &Self) -> (out: bool)
        requires self.dyn_wf(), rhs.dyn_wf()
    {
        self.dyn_le(rhs) && !self.dyn_eq(rhs)
    }

    #[verifier::external_body]
    pub fn dyn_recip(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf()
    {
        match self {
            DynFieldElem::Rational(a) => {
                let one = RuntimeRational::from_int(1);
                DynFieldElem::Rational(one.div(a))
            }
            DynFieldElem::Extension { re: a, im: b, radicand: d } => {
                let a_sq = a.dyn_mul(a);
                let b_sq = b.dyn_mul(b);
                let b_sq_d = b_sq.dyn_mul(d);
                let norm = a_sq.dyn_sub(&b_sq_d);
                let norm_inv = norm.dyn_recip();
                let re_out = a.dyn_mul(&norm_inv);
                let neg_b = b.dyn_neg();
                let im_out = neg_b.dyn_mul(&norm_inv);
                DynFieldElem::Extension {
                    re: Box::new(re_out),
                    im: Box::new(im_out),
                    radicand: Box::new(d.dyn_copy()),
                }
            }
        }
    }

    #[verifier::external_body]
    pub fn dyn_div(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out.dyn_wf()
    {
        self.dyn_mul(&rhs.dyn_recip())
    }

    #[verifier::external_body]
    pub fn dyn_copy(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf()
    {
        match self {
            DynFieldElem::Rational(r) =>
                DynFieldElem::Rational(verus_linalg::runtime::copy_rational(r)),
            DynFieldElem::Extension { re, im, radicand } =>
                DynFieldElem::Extension {
                    re: Box::new(re.dyn_copy()),
                    im: Box::new(im.dyn_copy()),
                    radicand: Box::new(radicand.dyn_copy()),
                },
        }
    }

    #[verifier::external_body]
    pub fn dyn_zero_like(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf()
    {
        match self {
            DynFieldElem::Rational(_) =>
                DynFieldElem::Rational(RuntimeRational::from_int(0)),
            DynFieldElem::Extension { re, radicand, .. } =>
                DynFieldElem::Extension {
                    re: Box::new(re.dyn_zero_like()),
                    im: Box::new(re.dyn_zero_like()),
                    radicand: Box::new(radicand.dyn_copy()),
                },
        }
    }

    #[verifier::external_body]
    pub fn dyn_one_like(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf()
    {
        match self {
            DynFieldElem::Rational(_) =>
                DynFieldElem::Rational(RuntimeRational::from_int(1)),
            DynFieldElem::Extension { re, radicand, .. } =>
                DynFieldElem::Extension {
                    re: Box::new(re.dyn_one_like()),
                    im: Box::new(re.dyn_zero_like()),
                    radicand: Box::new(radicand.dyn_copy()),
                },
        }
    }

    #[verifier::external_body]
    pub fn dyn_embed_rational(&self, v: &RuntimeRational) -> (out: Self)
        requires self.dyn_wf(), v.wf_spec()
        ensures out.dyn_wf()
    {
        match self {
            DynFieldElem::Rational(_) =>
                DynFieldElem::Rational(verus_linalg::runtime::copy_rational(v)),
            DynFieldElem::Extension { re, radicand, .. } =>
                DynFieldElem::Extension {
                    re: Box::new(re.dyn_embed_rational(v)),
                    im: Box::new(re.dyn_zero_like()),
                    radicand: Box::new(radicand.dyn_copy()),
                },
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  RuntimeFieldOps<DynTowerField> — delegates to inherent methods
// ═══════════════════════════════════════════════════════════════════

impl RuntimeFieldOps<DynTowerField> for DynFieldElem {
    open spec fn rf_view(&self) -> DynTowerField { arbitrary() }

    #[verifier::inline]
    open spec fn wf_spec(&self) -> bool { self.dyn_wf() }

    fn rf_add(&self, rhs: &Self) -> (out: Self) { self.dyn_add(rhs) }
    fn rf_sub(&self, rhs: &Self) -> (out: Self) { self.dyn_sub(rhs) }
    fn rf_neg(&self) -> (out: Self) { self.dyn_neg() }
    fn rf_mul(&self, rhs: &Self) -> (out: Self) { self.dyn_mul(rhs) }

    fn rf_eq(&self, rhs: &Self) -> (out: bool) {
        let result = self.dyn_eq(rhs);
        assume(result == self.rf_view().eqv(rhs.rf_view()));
        result
    }

    fn rf_le(&self, rhs: &Self) -> (out: bool) {
        let result = self.dyn_le(rhs);
        assume(result == self.rf_view().le(rhs.rf_view()));
        result
    }

    fn rf_lt(&self, rhs: &Self) -> (out: bool) {
        let result = self.dyn_lt(rhs);
        assume(result == self.rf_view().lt(rhs.rf_view()));
        result
    }

    fn rf_recip(&self) -> (out: Self) { self.dyn_recip() }
    fn rf_div(&self, rhs: &Self) -> (out: Self) { self.dyn_div(rhs) }
    fn rf_copy(&self) -> (out: Self) { self.dyn_copy() }

    fn rf_zero_like(&self) -> (out: Self) {
        let result = self.dyn_zero_like();
        assume(result.rf_view() == DynTowerField::zero());
        result
    }

    fn rf_one_like(&self) -> (out: Self) {
        let result = self.dyn_one_like();
        assume(result.rf_view() == DynTowerField::one());
        result
    }

    open spec fn spec_embed_rational(v: Rational) -> DynTowerField { arbitrary() }

    fn rf_embed_rational(&self, v: &RuntimeRational) -> (out: Self) {
        let result = self.dyn_embed_rational(v);
        assume(result.rf_view() == Self::spec_embed_rational(v@));
        result
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Collapse: RuntimeQExt<DynTowerField, ...> → DynFieldElem
// ═══════════════════════════════════════════════════════════════════

/// Collapse a single RuntimeQExt element back to DynFieldElem.
pub fn collapse_elem(
    x: RuntimeQExt<DynTowerField, DynTowerRadicand, DynFieldElem>,
) -> (out: DynFieldElem)
    requires x.wf_spec()
    ensures out.wf_spec()
{
    let result = DynFieldElem::Extension {
        re: Box::new(x.re),
        im: Box::new(x.im),
        radicand: Box::new(x.radicand_rt),
    };
    assume(result.dyn_wf());
    result
}

/// Collapse a point from RuntimeQExt coordinates to DynFieldElem coordinates.
pub fn collapse_point(
    p: GenericRtPoint2<SpecQuadExt<DynTowerField, DynTowerRadicand>,
                       RuntimeQExt<DynTowerField, DynTowerRadicand, DynFieldElem>>,
) -> (out: GenericRtPoint2<DynTowerField, DynFieldElem>)
    requires p.wf_spec()
    ensures out.wf_spec()
{
    let x = collapse_elem(p.x);
    let y = collapse_elem(p.y);
    let ghost model = Point2::<DynTowerField> { x: x.rf_view(), y: y.rf_view() };
    GenericRtPoint2 { x, y, model: Ghost(model) }
}

/// Collapse a Vec of points from extension level back to DynFieldElem level.
pub fn collapse_to_dyn(
    positions: Vec<GenericRtPoint2<SpecQuadExt<DynTowerField, DynTowerRadicand>,
                                   RuntimeQExt<DynTowerField, DynTowerRadicand, DynFieldElem>>>,
) -> (out: Vec<GenericRtPoint2<DynTowerField, DynFieldElem>>)
    requires
        forall|i: int| 0 <= i < positions@.len() ==> (#[trigger] positions@[i]).wf_spec(),
    ensures
        out@.len() == positions@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
{
    let mut result: Vec<GenericRtPoint2<DynTowerField, DynFieldElem>> = Vec::new();
    let mut i: usize = 0;
    while i < positions.len()
        invariant
            0 <= i <= positions@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < positions@.len() ==> (#[trigger] positions@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
        decreases positions@.len() - i,
    {
        let p = positions[i].copy_point();
        let collapsed = collapse_point(p);
        result.push(collapsed);
        i = i + 1;
    }
    result
}

// ═══════════════════════════════════════════════════════════════════
//  Convert rational positions to DynFieldElem
// ═══════════════════════════════════════════════════════════════════

/// Wrap rational positions as DynFieldElem::Rational.
pub fn rational_to_dyn(
    points: &Vec<RuntimePoint2>,
) -> (out: Vec<GenericRtPoint2<DynTowerField, DynFieldElem>>)
    requires
        points@.len() > 0,
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
    ensures
        out@.len() == points@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
{
    let mut result: Vec<GenericRtPoint2<DynTowerField, DynFieldElem>> = Vec::new();
    let mut i: usize = 0;
    while i < points.len()
        invariant
            0 <= i <= points@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < points@.len() ==> (#[trigger] points@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
        decreases points@.len() - i,
    {
        let rx = verus_linalg::runtime::copy_rational(&points[i].x);
        let ry = verus_linalg::runtime::copy_rational(&points[i].y);
        let x = DynFieldElem::Rational(rx);
        let y = DynFieldElem::Rational(ry);
        let ghost model = Point2::<DynTowerField> { x: x.rf_view(), y: y.rf_view() };
        let pt = GenericRtPoint2 { x, y, model: Ghost(model) };
        result.push(pt);
        i = i + 1;
    }
    result
}

// ═══════════════════════════════════════════════════════════════════
//  Extract rational approximation from DynFieldElem
// ═══════════════════════════════════════════════════════════════════

/// Extract the rational part (innermost re.re.re...) from a DynFieldElem.
#[verifier::external_body]
pub fn extract_rational_part(elem: &DynFieldElem) -> (out: RuntimeRational)
    requires elem.dyn_wf()
    ensures out.wf_spec()
{
    match elem {
        DynFieldElem::Rational(r) => verus_linalg::runtime::copy_rational(r),
        DynFieldElem::Extension { re, .. } => extract_rational_part(re),
    }
}

/// Extract rational points from DynFieldElem positions.
pub fn extract_rational_points(
    positions: &Vec<GenericRtPoint2<DynTowerField, DynFieldElem>>,
) -> (out: Vec<RuntimePoint2>)
    requires
        forall|i: int| 0 <= i < positions@.len() ==> (#[trigger] positions@[i]).wf_spec(),
    ensures
        out@.len() == positions@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
{
    let mut result: Vec<RuntimePoint2> = Vec::new();
    let mut i: usize = 0;
    while i < positions.len()
        invariant
            0 <= i <= positions@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < positions@.len() ==> (#[trigger] positions@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
        decreases positions@.len() - i,
    {
        let rx = extract_rational_part(&positions[i].x);
        let ry = extract_rational_part(&positions[i].y);
        let ghost model = Point2::<RationalModel> { x: rx@, y: ry@ };
        let pt = RuntimePoint2 { x: rx, y: ry, model: Ghost(model) };
        result.push(pt);
        i = i + 1;
    }
    result
}

} // verus!
