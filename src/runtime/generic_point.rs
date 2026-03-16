/// Generic runtime 2D point over any RuntimeFieldOps base field.
///
/// GenericRtPoint2<V, F> generalizes RuntimePoint2 (rational) and
/// RuntimeQExtPoint2<R> (single-level extension) to arbitrary fields.
/// Used by the multi-level executor for positions at any tower depth.
use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::constructed_scalar::qext_from_rational;
use verus_quadratic_extension::runtime_field::RuntimeFieldOps;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::runtime_qext::RuntimeQExt;

verus! {

// ═══════════════════════════════════════════════════════════════════
//  GenericRtPoint2 — generic runtime 2D point
// ═══════════════════════════════════════════════════════════════════

/// Runtime 2D point with coordinates in a generic field F.
///
/// The spec-level model is Point2<V> where V is the OrderedField
/// that F implements RuntimeFieldOps for.
pub struct GenericRtPoint2<V: OrderedField, F: RuntimeFieldOps<V>> {
    pub x: F,
    pub y: F,
    pub model: Ghost<Point2<V>>,
}

impl<V: OrderedField, F: RuntimeFieldOps<V>> GenericRtPoint2<V, F> {
    /// Well-formedness: runtime coords match the ghost model.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x.rf_view() == self.model@.x
        &&& self.y.rf_view() == self.model@.y
    }

    /// Construct from components.
    pub fn new(x: F, y: F) -> (out: Self)
        requires x.wf_spec(), y.wf_spec()
        ensures
            out.wf_spec(),
            out.model@.x == x.rf_view(),
            out.model@.y == y.rf_view(),
    {
        let ghost model = Point2 { x: x.rf_view(), y: y.rf_view() };
        GenericRtPoint2 { x, y, model: Ghost(model) }
    }

    /// Copy point by copying each coordinate.
    pub fn copy_point(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.model@ == self.model@
    {
        let x = self.x.rf_copy();
        let y = self.y.rf_copy();
        GenericRtPoint2 { x, y, model: Ghost(self.model@) }
    }

    /// Squared distance to another point: ||self - other||².
    pub fn sq_dist(&self, other: &Self) -> (out: F)
        requires self.wf_spec(), other.wf_spec()
        ensures
            out.wf_spec(),
            out.rf_view() == sq_dist_2d::<V>(self.model@, other.model@),
    {
        let dx = self.x.rf_sub(&other.x);
        let dy = self.y.rf_sub(&other.y);
        let dx2 = dx.rf_mul(&dx);
        let dy2 = dy.rf_mul(&dy);
        dx2.rf_add(&dy2)
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Embedding: lift GenericRtPoint2<V, F> to GenericRtPoint2<QExt, QExtRt>
// ═══════════════════════════════════════════════════════════════════

/// Embed a point from base field F into extension field F(√d).
///
/// Each coordinate v is mapped to v + 0·√d.
/// Requires a radicand runtime value to construct the extension elements.
pub fn embed_point_to_ext<
    FV: OrderedField,
    R: PositiveRadicand<FV>,
    F: RuntimeFieldOps<FV>,
>(
    p: &GenericRtPoint2<FV, F>,
    radicand_rt: &F,
) -> (out: GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>)
    requires
        p.wf_spec(),
        radicand_rt.wf_spec(),
        radicand_rt.rf_view() == R::value(),
    ensures
        out.wf_spec(),
        out.model@.x == qext_from_rational::<FV, R>(p.model@.x),
        out.model@.y == qext_from_rational::<FV, R>(p.model@.y),
{
    let x_ext = RuntimeQExt::<FV, R, F>::embed_base(
        p.x.rf_copy(),
        radicand_rt.rf_copy(),
    );
    let y_ext = RuntimeQExt::<FV, R, F>::embed_base(
        p.y.rf_copy(),
        radicand_rt.rf_copy(),
    );
    let ghost ext_model = Point2 {
        x: qext_from_rational::<FV, R>(p.model@.x),
        y: qext_from_rational::<FV, R>(p.model@.y),
    };
    GenericRtPoint2 { x: x_ext, y: y_ext, model: Ghost(ext_model) }
}

/// Embed a Vec of points from base field to extension field.
pub fn embed_points_to_ext<
    FV: OrderedField,
    R: PositiveRadicand<FV>,
    F: RuntimeFieldOps<FV>,
>(
    points: &Vec<GenericRtPoint2<FV, F>>,
    radicand_rt: &F,
) -> (out: Vec<GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>>)
    requires
        radicand_rt.wf_spec(),
        radicand_rt.rf_view() == R::value(),
        forall|i: int| 0 <= i < points@.len() ==> (#[trigger] points@[i]).wf_spec(),
    ensures
        out@.len() == points@.len(),
        forall|i: int| 0 <= i < out@.len() ==> (#[trigger] out@[i]).wf_spec(),
        forall|i: int| 0 <= i < out@.len() ==> {
            &&& (#[trigger] out@[i]).model@.x == qext_from_rational::<FV, R>(points@[i].model@.x)
            &&& out@[i].model@.y == qext_from_rational::<FV, R>(points@[i].model@.y)
        },
{
    let mut result: Vec<GenericRtPoint2<SpecQuadExt<FV, R>, RuntimeQExt<FV, R, F>>> = Vec::new();
    let mut i: usize = 0;
    while i < points.len()
        invariant
            0 <= i <= points@.len(),
            result@.len() == i,
            radicand_rt.wf_spec(),
            radicand_rt.rf_view() == R::value(),
            forall|j: int| 0 <= j < points@.len() ==> (#[trigger] points@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> (#[trigger] result@[j]).wf_spec(),
            forall|j: int| 0 <= j < result@.len() ==> {
                &&& (#[trigger] result@[j]).model@.x == qext_from_rational::<FV, R>(points@[j].model@.x)
                &&& result@[j].model@.y == qext_from_rational::<FV, R>(points@[j].model@.y)
            },
        decreases points@.len() - i,
    {
        let embedded = embed_point_to_ext::<FV, R, F>(&points[i], radicand_rt);
        result.push(embedded);
        i = i + 1;
    }
    result
}

} // verus!
