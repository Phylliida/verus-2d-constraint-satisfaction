use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::line_intersection::*;
use verus_geometry::runtime::point2::*;
use verus_geometry::runtime::line2::*;
use verus_geometry::runtime::circle2::*;
use verus_geometry::runtime::line_intersection::*;
use crate::construction::*;

use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Runtime construction step execution
// ===========================================================================

/// Runtime representation of a line-line construction step result.
/// For now, we only support Fixed and LineLine steps at runtime
/// (CircleLine and CircleCircle require quadratic extension runtime,
///  which can be added as needed).
pub enum RuntimeConstructionResult {
    /// A rational point (from Fixed, LineLine, or Determined steps).
    RationalPoint(RuntimePoint2),
}

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

} // verus!
