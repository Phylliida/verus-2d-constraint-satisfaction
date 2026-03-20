/// Dynamic field element for arbitrary-depth quadratic extension towers.
///
/// `DynFieldElem` type-erases the tower level, allowing arbitrary-depth
/// quadratic extension arithmetic via recursive `dyn_*` methods.
///
/// Ghost tracking via `dts_model` maps each `DynFieldElem` to a concrete
/// `DynTowerSpec`, enabling spec-level reasoning about operations.
///
/// Most methods are fully verified (no external_body). The remaining
/// external_body methods (add, sub, mul, recip, div, nonneg, le, lt)
/// need depth-matching preconditions to remove.
use vstd::prelude::*;
use verus_rational::runtime_rational::RuntimeRational;
use verus_quadratic_extension::dyn_tower::*;

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
//  Ghost model: DynFieldElem → DynTowerSpec
// ═══════════════════════════════════════════════════════════════════

/// Structural mapping from runtime DynFieldElem to spec DynTowerSpec.
/// Each RuntimeRational maps to Rat(r@), each Extension maps to Ext.
pub open spec fn dts_model(x: DynFieldElem) -> DynTowerSpec
    decreases x,
{
    match x {
        DynFieldElem::Rational(r) => DynTowerSpec::Rat(r@),
        DynFieldElem::Extension { re, im, radicand } => DynTowerSpec::Ext(
            Box::new(dts_model(*re)),
            Box::new(dts_model(*im)),
            Box::new(dts_model(*radicand)),
        ),
    }
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

    pub fn dyn_add(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out.dyn_wf(), dts_model(out) == dts_add(dts_model(*self), dts_model(*rhs))
        decreases *self, *rhs,
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
            (DynFieldElem::Rational(_), DynFieldElem::Extension { re, im, radicand }) =>
                DynFieldElem::Extension {
                    re: Box::new(self.dyn_add(re)),
                    im: Box::new(im.dyn_copy()),
                    radicand: Box::new(radicand.dyn_copy()),
                },
            (DynFieldElem::Extension { re, im, radicand }, DynFieldElem::Rational(_)) =>
                DynFieldElem::Extension {
                    re: Box::new(re.dyn_add(rhs)),
                    im: Box::new(im.dyn_copy()),
                    radicand: Box::new(radicand.dyn_copy()),
                },
        }
    }

    pub fn dyn_sub(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out.dyn_wf(), dts_model(out) == dts_sub(dts_model(*self), dts_model(*rhs))
    {
        let neg_rhs = rhs.dyn_neg();
        self.dyn_add(&neg_rhs)
    }

    pub fn dyn_neg(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf(), dts_model(out) == dts_neg(dts_model(*self))
        decreases *self,
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

    pub fn dyn_mul(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out.dyn_wf(), dts_model(out) == dts_mul(dts_model(*self), dts_model(*rhs))
        decreases *self, *rhs,
    {
        match (self, rhs) {
            (DynFieldElem::Rational(a), DynFieldElem::Rational(b)) =>
                DynFieldElem::Rational(a.mul(b)),
            (DynFieldElem::Extension { re: a, im: b, radicand: d },
             DynFieldElem::Extension { re: c, im: e, .. }) => {
                // (a + b√d)(c + e√d) = (ac + d·be) + (ae + bc)√d
                let ac = a.dyn_mul(c);
                let be = b.dyn_mul(e);
                // d.dyn_mul(&be) matches spec's dts_mul(*d, im1_im2) for termination
                let d_be = d.dyn_mul(&be);
                let re_out = ac.dyn_add(&d_be);
                let ae = a.dyn_mul(e);
                let bc = b.dyn_mul(c);
                let im_out = ae.dyn_add(&bc);
                DynFieldElem::Extension {
                    re: Box::new(re_out),
                    im: Box::new(im_out),
                    radicand: Box::new(d.dyn_copy()),
                }
            }
            (DynFieldElem::Rational(_), DynFieldElem::Extension { re, im, radicand }) =>
                DynFieldElem::Extension {
                    re: Box::new(self.dyn_mul(re)),
                    im: Box::new(self.dyn_mul(im)),
                    radicand: Box::new(radicand.dyn_copy()),
                },
            (DynFieldElem::Extension { re, im, radicand }, DynFieldElem::Rational(_)) =>
                DynFieldElem::Extension {
                    re: Box::new(re.dyn_mul(rhs)),
                    im: Box::new(im.dyn_mul(rhs)),
                    radicand: Box::new(radicand.dyn_copy()),
                },
        }
    }

    /// Check if this element is zero (im and re are recursively zero).
    pub fn dyn_is_zero(&self) -> (out: bool)
        requires self.dyn_wf()
        ensures out == dts_is_zero(dts_model(*self))
        decreases *self,
    {
        match self {
            DynFieldElem::Rational(r) => {
                let zero = RuntimeRational::from_int(0);
                r.eq(&zero)
            }
            DynFieldElem::Extension { re, im, .. } =>
                re.dyn_is_zero() && im.dyn_is_zero(),
        }
    }

    /// Check if this element is equivalent to a rational value.
    /// Terminates by structural descent on self.
    pub fn dyn_eq_rational(&self, r: &RuntimeRational) -> (out: bool)
        requires self.dyn_wf(), r.wf_spec()
        ensures out == dts_eqv(dts_model(*self), DynTowerSpec::Rat(r@))
        decreases *self,
    {
        match self {
            DynFieldElem::Rational(a) => a.eq(r),
            DynFieldElem::Extension { re, im, .. } =>
                re.dyn_eq_rational(r) && im.dyn_is_zero(),
        }
    }

    pub fn dyn_eq(&self, rhs: &Self) -> (out: bool)
        requires self.dyn_wf(), rhs.dyn_wf()
        ensures out == dts_eqv(dts_model(*self), dts_model(*rhs))
        decreases *self, *rhs,
    {
        match (self, rhs) {
            (DynFieldElem::Rational(a), DynFieldElem::Rational(b)) => a.eq(b),
            (DynFieldElem::Extension { re: re1, im: im1, .. },
             DynFieldElem::Extension { re: re2, im: im2, .. }) =>
                re1.dyn_eq(re2) && im1.dyn_eq(im2),
            (DynFieldElem::Rational(r), DynFieldElem::Extension { re, im, .. }) => {
                let out = re.dyn_eq_rational(r) && im.dyn_is_zero();
                proof {
                    // dyn_eq_rational gives dts_eqv(model(*re), Rat(r@))
                    // but spec needs dts_eqv(Rat(r@), model(*re))
                    verus_quadratic_extension::dyn_tower_lemmas::lemma_dts_eqv_symmetric(
                        dts_model(**re), DynTowerSpec::Rat(r@));
                }
                out
            }
            (DynFieldElem::Extension { re, im, .. }, DynFieldElem::Rational(r)) =>
                re.dyn_eq_rational(r) && im.dyn_is_zero(),
        }
    }


    /// Reciprocal with explicit fuel for termination.
    /// For nonzero inputs: dts_model(out) == dts_recip_fuel(dts_model(*self), fuel).
    /// For zero inputs: only wf is guaranteed (reciprocal of zero is undefined).
    fn dyn_recip_fuel(&self, fuel: u64) -> (out: Self)
        requires self.dyn_wf()
        ensures
            out.dyn_wf(),
            !dts_is_zero(dts_model(*self)) ==>
                dts_model(out) == dts_recip_fuel(dts_model(*self), fuel as nat),
        decreases fuel,
    {
        match self {
            DynFieldElem::Rational(a) => {
                match a.recip() {
                    Some(r) => DynFieldElem::Rational(r),
                    None => {
                        // a ≡ 0: reciprocal undefined, return wf garbage
                        DynFieldElem::Rational(RuntimeRational::from_int(0))
                    }
                }
            }
            DynFieldElem::Extension { re: a, im: b, radicand: d } => {
                if fuel == 0 {
                    return self.dyn_copy();
                }
                // norm = a² - d·b²
                let a_sq = a.dyn_mul(a);
                let b_sq = b.dyn_mul(b);
                let d_b_sq = d.dyn_mul(&b_sq);
                let norm = a_sq.dyn_sub(&d_b_sq);
                let norm_inv = norm.dyn_recip_fuel(fuel - 1);
                // re_out = a · norm_inv
                let re_out = a.dyn_mul(&norm_inv);
                // im_out = -(b · norm_inv)  (matches spec's dts_neg(dts_mul(*im, norm_inv)))
                let b_norm_inv = b.dyn_mul(&norm_inv);
                let im_out = b_norm_inv.dyn_neg();
                DynFieldElem::Extension {
                    re: Box::new(re_out),
                    im: Box::new(im_out),
                    radicand: Box::new(d.dyn_copy()),
                }
            }
        }
    }

    /// Compute tower depth as u64 for fuel computation.
    fn dyn_depth_exec(&self) -> (out: u64)
        requires self.dyn_wf(), dts_depth(dts_model(*self)) <= u64::MAX as nat
        ensures out as nat == dts_depth(dts_model(*self))
        decreases *self,
    {
        match self {
            DynFieldElem::Rational(_) => 0,
            DynFieldElem::Extension { re, im, radicand } => {
                let dr = re.dyn_depth_exec();
                let di = im.dyn_depth_exec();
                let dd = radicand.dyn_depth_exec();
                let m = if dr >= di { if dr >= dd { dr } else { dd } }
                        else { if di >= dd { di } else { dd } };
                1 + m
            }
        }
    }

    pub fn dyn_recip(&self) -> (out: Self)
        requires self.dyn_wf(), dts_depth(dts_model(*self)) < u64::MAX as nat
        ensures
            out.dyn_wf(),
            !dts_is_zero(dts_model(*self)) ==>
                dts_model(out) == dts_recip(dts_model(*self)),
    {
        let depth = self.dyn_depth_exec();
        self.dyn_recip_fuel(depth + 1)
    }

    pub fn dyn_div(&self, rhs: &Self) -> (out: Self)
        requires self.dyn_wf(), rhs.dyn_wf(),
            dts_depth(dts_model(*rhs)) < u64::MAX as nat
        ensures
            out.dyn_wf(),
            !dts_is_zero(dts_model(*rhs)) ==>
                dts_model(out) == dts_div(dts_model(*self), dts_model(*rhs)),
    {
        self.dyn_mul(&rhs.dyn_recip())
    }

    pub fn dyn_copy(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf(), dts_model(out) == dts_model(*self)
        decreases *self,
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

    pub fn dyn_zero_like(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf(), dts_eqv(dts_model(out), dts_zero())
        decreases *self,
    {
        match self {
            DynFieldElem::Rational(_) =>
                DynFieldElem::Rational(RuntimeRational::from_int(0)),
            DynFieldElem::Extension { re, radicand, .. } => {
                let re_out = re.dyn_zero_like();
                let im_out = re.dyn_zero_like();
                let d_out = radicand.dyn_copy();
                proof {
                    // Recursive ensures: dts_eqv(dts_model(re_out), dts_zero())
                    //                    dts_eqv(dts_model(im_out), dts_zero())
                    // Need: dts_is_zero(dts_model(im_out)) for the cross-variant unfolding
                    verus_quadratic_extension::dyn_tower_lemmas::lemma_dts_eqv_zero_implies_is_zero(
                        dts_model(im_out));
                }
                DynFieldElem::Extension {
                    re: Box::new(re_out),
                    im: Box::new(im_out),
                    radicand: Box::new(d_out),
                }
            }
        }
    }

    pub fn dyn_one_like(&self) -> (out: Self)
        requires self.dyn_wf()
        ensures out.dyn_wf(), dts_eqv(dts_model(out), dts_one())
        decreases *self,
    {
        match self {
            DynFieldElem::Rational(_) =>
                DynFieldElem::Rational(RuntimeRational::from_int(1)),
            DynFieldElem::Extension { re, radicand, .. } => {
                let re_out = re.dyn_one_like();
                let im_out = re.dyn_zero_like();
                let d_out = radicand.dyn_copy();
                proof {
                    verus_quadratic_extension::dyn_tower_lemmas::lemma_dts_eqv_zero_implies_is_zero(
                        dts_model(im_out));
                }
                DynFieldElem::Extension {
                    re: Box::new(re_out),
                    im: Box::new(im_out),
                    radicand: Box::new(d_out),
                }
            }
        }
    }

    pub fn dyn_embed_rational(&self, v: &RuntimeRational) -> (out: Self)
        requires self.dyn_wf(), v.wf_spec()
        ensures out.dyn_wf(), dts_eqv(dts_model(out), DynTowerSpec::Rat(v@))
        decreases *self,
    {
        match self {
            DynFieldElem::Rational(_) =>
                DynFieldElem::Rational(verus_linalg::runtime::copy_rational(v)),
            DynFieldElem::Extension { re, radicand, .. } => {
                let re_out = re.dyn_embed_rational(v);
                let im_out = re.dyn_zero_like();
                let d_out = radicand.dyn_copy();
                proof {
                    verus_quadratic_extension::dyn_tower_lemmas::lemma_dts_eqv_zero_implies_is_zero(
                        dts_model(im_out));
                }
                DynFieldElem::Extension {
                    re: Box::new(re_out),
                    im: Box::new(im_out),
                    radicand: Box::new(d_out),
                }
            }
        }
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Extract rational approximation from DynFieldElem
// ═══════════════════════════════════════════════════════════════════

/// Extract the rational part (innermost re.re.re...) from a DynFieldElem.
pub fn extract_rational_part(elem: &DynFieldElem) -> (out: RuntimeRational)
    requires elem.dyn_wf()
    ensures out.wf_spec()
    decreases *elem,
{
    match elem {
        DynFieldElem::Rational(r) => verus_linalg::runtime::copy_rational(r),
        DynFieldElem::Extension { re, .. } => extract_rational_part(re),
    }
}

} // verus!
