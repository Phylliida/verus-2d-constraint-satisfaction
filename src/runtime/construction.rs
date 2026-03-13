use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::line_intersection::*;
use verus_geometry::circle_line::*;
use verus_geometry::circle_circle::*;
use verus_geometry::runtime::point2::*;
use verus_geometry::runtime::line2::*;
use verus_geometry::runtime::circle2::*;
use verus_geometry::runtime::line_intersection::*;
use verus_geometry::runtime::circle_line::*;
use verus_geometry::runtime::circle_circle::*;
use verus_quadratic_extension::radicand::*;
use verus_quadratic_extension::spec::*;
use verus_quadratic_extension::runtime::RuntimeQExtRat;
use crate::construction::*;

use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Runtime construction step execution
// ===========================================================================

/// Execute a Fixed step: just wrap the given position.
pub fn execute_fixed_step(
    x: &RuntimeRational,
    y: &RuntimeRational,
) -> (out: RuntimePoint2)
    requires
        x.wf_spec(),
        y.wf_spec(),
    ensures
        out.wf_spec(),
        out@.x == x@,
        out@.y == y@,
{
    RuntimePoint2 {
        x: copy_rational(x),
        y: copy_rational(y),
        model: Ghost(Point2 { x: x@, y: y@ }),
    }
}

/// Execute a LineLine step.
pub fn execute_line_line_step(
    l1: &RuntimeLine2,
    l2: &RuntimeLine2,
) -> (out: RuntimePoint2)
    requires
        l1.wf_spec(),
        l2.wf_spec(),
        !line_det::<RationalModel>(l1@, l2@).eqv(RationalModel::from_int_spec(0)),
    ensures
        out.wf_spec(),
        out@ == line_line_intersection_2d::<RationalModel>(l1@, l2@),
{
    line_line_intersection_2d_exec(l1, l2)
}

// ===========================================================================
//  Circle intersection step execution (quadratic extension coordinates)
// ===========================================================================

/// Runtime point in a quadratic extension field Q(sqrt(d)).
/// Stores (x, y) coordinates as RuntimeQExtRat<R>.
pub struct RuntimeQExtPoint2<R: Radicand<RationalModel>> {
    pub x: RuntimeQExtRat<R>,
    pub y: RuntimeQExtRat<R>,
    pub model: Ghost<Point2<SpecQuadExt<RationalModel, R>>>,
}

impl<R: Radicand<RationalModel>> View for RuntimeQExtPoint2<R> {
    type V = Point2<SpecQuadExt<RationalModel, R>>;

    open spec fn view(&self) -> Point2<SpecQuadExt<RationalModel, R>> {
        self.model@
    }
}

impl<R: Radicand<RationalModel>> RuntimeQExtPoint2<R> {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.x.wf_spec()
        &&& self.y.wf_spec()
        &&& self.x@ == self@.x
        &&& self.y@ == self@.y
    }
}

/// Execute a CircleLine step: intersect a circle with a line.
/// Returns a point with coordinates in Q(sqrt(discriminant)).
/// R must encode the discriminant of the circle-line intersection.
pub fn execute_circle_line_step<R: PositiveRadicand<RationalModel>>(
    circle: &RuntimeCircle2,
    line: &RuntimeLine2,
    plus: bool,
) -> (out: RuntimeQExtPoint2<R>)
    where R: verus_quadratic_extension::runtime::RuntimeRadicand<R>
    requires
        circle.wf_spec(),
        line.wf_spec(),
        line2_nondegenerate(line@),
    ensures
        out.wf_spec(),
        out@ == cl_intersection_point::<RationalModel, R>(circle@, line@, plus),
{
    proof {
        lemma_cl_quad_a_positive::<RationalModel>(line@);
        RationalModel::axiom_lt_iff_le_and_not_eqv(
            RationalModel::from_int_spec(0),
            cl_quad_a::<RationalModel>(line@),
        );
        RationalModel::axiom_eqv_symmetric(
            RationalModel::from_int_spec(0),
            cl_quad_a::<RationalModel>(line@),
        );
    }
    let x = cl_intersection_x_exec::<R>(circle, line, plus);
    let y = cl_intersection_y_exec::<R>(circle, line, plus);
    let ghost model = cl_intersection_point::<RationalModel, R>(circle@, line@, plus);
    RuntimeQExtPoint2 { x, y, model: Ghost(model) }
}

/// Execute a CircleCircle step: intersect two circles.
/// Computes the radical axis and delegates to circle-line intersection.
pub fn execute_circle_circle_step<R: PositiveRadicand<RationalModel>>(
    c1: &RuntimeCircle2,
    c2: &RuntimeCircle2,
    plus: bool,
) -> (out: RuntimeQExtPoint2<R>)
    where R: verus_quadratic_extension::runtime::RuntimeRadicand<R>
    requires
        c1.wf_spec(),
        c2.wf_spec(),
        !c1@.center.eqv(c2@.center),
    ensures
        out.wf_spec(),
        out@ == cc_intersection_point::<RationalModel, R>(c1@, c2@, plus),
{
    let x = cc_intersection_x_exec::<R>(c1, c2, plus);
    let y = cc_intersection_y_exec::<R>(c1, c2, plus);
    let ghost model = cc_intersection_point::<RationalModel, R>(c1@, c2@, plus);
    RuntimeQExtPoint2 { x, y, model: Ghost(model) }
}

} // verus!
