use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::runtime::point2::*;
use verus_geometry::runtime::line2::*;
use verus_geometry::runtime::voronoi::sq_dist_2d_exec;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use crate::entities::*;
use crate::constraints::*;

type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Resolved points bridge
// ===========================================================================

/// Convert a Vec of runtime points (viewed as spec) into a ResolvedPoints map.
/// Entity i maps to points[i] for 0 <= i < points.len().
pub open spec fn vec_to_resolved_map(
    points: Seq<Point2<RationalModel>>,
) -> ResolvedPoints<RationalModel> {
    Map::new(
        |id: nat| (id as int) < points.len(),
        |id: nat| points[id as int],
    )
}

/// Partial resolved map: only entities with flags[i] == true are in the domain.
/// Used by the greedy solver where not all entities are resolved yet.
pub open spec fn partial_resolved_map(
    points: Seq<Point2<RationalModel>>,
    flags: Seq<bool>,
) -> ResolvedPoints<RationalModel> {
    Map::new(
        |id: nat| (id as int) < points.len() && (id as int) < flags.len() && flags[id as int],
        |id: nat| points[id as int],
    )
}

/// Helper: check that all points in the Vec satisfy wf_spec.
pub open spec fn all_points_wf(points: Seq<RuntimePoint2>) -> bool {
    forall|i: int| 0 <= i < points.len() ==> (#[trigger] points[i]).wf_spec()
}

/// Lift the views of all RuntimePoint2 in a Vec to a spec-level Seq of Point2.
pub open spec fn points_view(points: Seq<RuntimePoint2>) -> Seq<Point2<RationalModel>> {
    Seq::new(points.len(), |i: int| points[i]@)
}

// ===========================================================================
//  Runtime constraint enum
// ===========================================================================

/// Runtime constraint: mirrors spec-level Constraint<RationalModel> with
/// entity IDs as usize indices into a resolved-points Vec.
pub enum RuntimeConstraint {
    Coincident { a: usize, b: usize, model: Ghost<Constraint<RationalModel>> },
    DistanceSq { a: usize, b: usize, dist_sq: RuntimeRational, model: Ghost<Constraint<RationalModel>> },
    FixedX { point: usize, x: RuntimeRational, model: Ghost<Constraint<RationalModel>> },
    FixedY { point: usize, y: RuntimeRational, model: Ghost<Constraint<RationalModel>> },
    SameX { a: usize, b: usize, model: Ghost<Constraint<RationalModel>> },
    SameY { a: usize, b: usize, model: Ghost<Constraint<RationalModel>> },
    PointOnLine { point: usize, line_a: usize, line_b: usize, model: Ghost<Constraint<RationalModel>> },
    EqualLengthSq { a1: usize, a2: usize, b1: usize, b2: usize, model: Ghost<Constraint<RationalModel>> },
    Midpoint { mid: usize, a: usize, b: usize, model: Ghost<Constraint<RationalModel>> },
    Perpendicular { a1: usize, a2: usize, b1: usize, b2: usize, model: Ghost<Constraint<RationalModel>> },
    Parallel { a1: usize, a2: usize, b1: usize, b2: usize, model: Ghost<Constraint<RationalModel>> },
    Collinear { a: usize, b: usize, c: usize, model: Ghost<Constraint<RationalModel>> },
    PointOnCircle { point: usize, center: usize, radius_point: usize, model: Ghost<Constraint<RationalModel>> },
    Symmetric { point: usize, original: usize, axis_a: usize, axis_b: usize, model: Ghost<Constraint<RationalModel>> },
}

/// Well-formedness: the runtime constraint matches its ghost model and
/// all entity IDs are valid nats matching the spec EntityId.
pub open spec fn runtime_constraint_wf(
    rc: RuntimeConstraint, n_points: nat,
) -> bool {
    match rc {
        RuntimeConstraint::Coincident { a, b, model } =>
            model@ == Constraint::<RationalModel>::Coincident { a: a as nat, b: b as nat }
            && (a as int) < n_points && (b as int) < n_points,
        RuntimeConstraint::DistanceSq { a, b, dist_sq, model } =>
            dist_sq.wf_spec()
            && model@ == Constraint::<RationalModel>::DistanceSq { a: a as nat, b: b as nat, dist_sq: dist_sq@ }
            && (a as int) < n_points && (b as int) < n_points,
        RuntimeConstraint::FixedX { point, x, model } =>
            x.wf_spec()
            && model@ == Constraint::<RationalModel>::FixedX { point: point as nat, x: x@ }
            && (point as int) < n_points,
        RuntimeConstraint::FixedY { point, y, model } =>
            y.wf_spec()
            && model@ == Constraint::<RationalModel>::FixedY { point: point as nat, y: y@ }
            && (point as int) < n_points,
        RuntimeConstraint::SameX { a, b, model } =>
            model@ == Constraint::<RationalModel>::SameX { a: a as nat, b: b as nat }
            && (a as int) < n_points && (b as int) < n_points,
        RuntimeConstraint::SameY { a, b, model } =>
            model@ == Constraint::<RationalModel>::SameY { a: a as nat, b: b as nat }
            && (a as int) < n_points && (b as int) < n_points,
        RuntimeConstraint::PointOnLine { point, line_a, line_b, model } =>
            model@ == Constraint::<RationalModel>::PointOnLine { point: point as nat, line_a: line_a as nat, line_b: line_b as nat }
            && (point as int) < n_points && (line_a as int) < n_points && (line_b as int) < n_points,
        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, model } =>
            model@ == Constraint::<RationalModel>::EqualLengthSq { a1: a1 as nat, a2: a2 as nat, b1: b1 as nat, b2: b2 as nat }
            && (a1 as int) < n_points && (a2 as int) < n_points
            && (b1 as int) < n_points && (b2 as int) < n_points,
        RuntimeConstraint::Midpoint { mid, a, b, model } =>
            model@ == Constraint::<RationalModel>::Midpoint { mid: mid as nat, a: a as nat, b: b as nat }
            && (mid as int) < n_points && (a as int) < n_points && (b as int) < n_points,
        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, model } =>
            model@ == Constraint::<RationalModel>::Perpendicular { a1: a1 as nat, a2: a2 as nat, b1: b1 as nat, b2: b2 as nat }
            && (a1 as int) < n_points && (a2 as int) < n_points
            && (b1 as int) < n_points && (b2 as int) < n_points,
        RuntimeConstraint::Parallel { a1, a2, b1, b2, model } =>
            model@ == Constraint::<RationalModel>::Parallel { a1: a1 as nat, a2: a2 as nat, b1: b1 as nat, b2: b2 as nat }
            && (a1 as int) < n_points && (a2 as int) < n_points
            && (b1 as int) < n_points && (b2 as int) < n_points,
        RuntimeConstraint::Collinear { a, b, c, model } =>
            model@ == Constraint::<RationalModel>::Collinear { a: a as nat, b: b as nat, c: c as nat }
            && (a as int) < n_points && (b as int) < n_points && (c as int) < n_points,
        RuntimeConstraint::PointOnCircle { point, center, radius_point, model } =>
            model@ == Constraint::<RationalModel>::PointOnCircle { point: point as nat, center: center as nat, radius_point: radius_point as nat }
            && (point as int) < n_points && (center as int) < n_points && (radius_point as int) < n_points,
        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, model } =>
            model@ == Constraint::<RationalModel>::Symmetric { point: point as nat, original: original as nat, axis_a: axis_a as nat, axis_b: axis_b as nat }
            && (point as int) < n_points && (original as int) < n_points
            && (axis_a as int) < n_points && (axis_b as int) < n_points,
    }
}

/// Extract the ghost model from a RuntimeConstraint.
pub open spec fn runtime_constraint_model(rc: RuntimeConstraint) -> Constraint<RationalModel> {
    match rc {
        RuntimeConstraint::Coincident { model, .. } => model@,
        RuntimeConstraint::DistanceSq { model, .. } => model@,
        RuntimeConstraint::FixedX { model, .. } => model@,
        RuntimeConstraint::FixedY { model, .. } => model@,
        RuntimeConstraint::SameX { model, .. } => model@,
        RuntimeConstraint::SameY { model, .. } => model@,
        RuntimeConstraint::PointOnLine { model, .. } => model@,
        RuntimeConstraint::EqualLengthSq { model, .. } => model@,
        RuntimeConstraint::Midpoint { model, .. } => model@,
        RuntimeConstraint::Perpendicular { model, .. } => model@,
        RuntimeConstraint::Parallel { model, .. } => model@,
        RuntimeConstraint::Collinear { model, .. } => model@,
        RuntimeConstraint::PointOnCircle { model, .. } => model@,
        RuntimeConstraint::Symmetric { model, .. } => model@,
    }
}

// ===========================================================================
//  Constraint checker helpers
// ===========================================================================

/// Check rational equality: a@ ≡ b@ (using le both ways).
fn rational_eqv(a: &RuntimeRational, b: &RuntimeRational) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(),
    ensures out == a@.eqv(b@),
{
    a.le(b) && b.le(a)
}

/// Check Point2 equivalence: both coordinates match.
fn point2_eqv(a: &RuntimePoint2, b: &RuntimePoint2) -> (out: bool)
    requires a.wf_spec(), b.wf_spec(),
    ensures out == a@.eqv(b@),
{
    rational_eqv(&a.x, &b.x) && rational_eqv(&a.y, &b.y)
}

// ===========================================================================
//  Main checker
// ===========================================================================

/// Check if a single runtime constraint is satisfied by the resolved points.
pub fn check_constraint_satisfied_exec(
    rc: &RuntimeConstraint,
    points: &Vec<RuntimePoint2>,
) -> (out: bool)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_points_wf(points@),
    ensures
        out ==> constraint_satisfied(
            runtime_constraint_model(*rc),
            vec_to_resolved_map(points_view(points@)),
        ),
{
    let ghost resolved = vec_to_resolved_map(points_view(points@));
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => {
            // constraint_satisfied: resolved[a].eqv(resolved[b])
            // dom checks are automatic since all indices < points.len()
            proof {
                assert(resolved.dom().contains(*a as nat));
                assert(resolved.dom().contains(*b as nat));
                assert(resolved[*a as nat] == points@[*a as int]@);
                assert(resolved[*b as nat] == points@[*b as int]@);
            }
            point2_eqv(&points[*a], &points[*b])
        }

        RuntimeConstraint::DistanceSq { a, b, dist_sq, .. } => {
            proof {
                assert(resolved.dom().contains(*a as nat));
                assert(resolved.dom().contains(*b as nat));
                assert(resolved[*a as nat] == points@[*a as int]@);
                assert(resolved[*b as nat] == points@[*b as int]@);
            }
            let d = sq_dist_2d_exec(&points[*a], &points[*b]);
            rational_eqv(&d, dist_sq)
        }

        RuntimeConstraint::FixedX { point, x, .. } => {
            proof {
                assert(resolved.dom().contains(*point as nat));
                assert(resolved[*point as nat] == points@[*point as int]@);
            }
            rational_eqv(&points[*point].x, x)
        }

        RuntimeConstraint::FixedY { point, y, .. } => {
            proof {
                assert(resolved.dom().contains(*point as nat));
                assert(resolved[*point as nat] == points@[*point as int]@);
            }
            rational_eqv(&points[*point].y, y)
        }

        RuntimeConstraint::SameX { a, b, .. } => {
            proof {
                assert(resolved.dom().contains(*a as nat));
                assert(resolved.dom().contains(*b as nat));
                assert(resolved[*a as nat] == points@[*a as int]@);
                assert(resolved[*b as nat] == points@[*b as int]@);
            }
            rational_eqv(&points[*a].x, &points[*b].x)
        }

        RuntimeConstraint::SameY { a, b, .. } => {
            proof {
                assert(resolved.dom().contains(*a as nat));
                assert(resolved.dom().contains(*b as nat));
                assert(resolved[*a as nat] == points@[*a as int]@);
                assert(resolved[*b as nat] == points@[*b as int]@);
            }
            rational_eqv(&points[*a].y, &points[*b].y)
        }

        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } => {
            proof {
                assert(resolved.dom().contains(*point as nat));
                assert(resolved.dom().contains(*line_a as nat));
                assert(resolved.dom().contains(*line_b as nat));
                assert(resolved[*point as nat] == points@[*point as int]@);
                assert(resolved[*line_a as nat] == points@[*line_a as int]@);
                assert(resolved[*line_b as nat] == points@[*line_b as int]@);
            }
            let line = line2_from_points_exec(&points[*line_a], &points[*line_b]);
            let eval = line2_eval_exec(&line, &points[*point]);
            eval.is_zero()
        }

        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } => {
            proof {
                assert(resolved.dom().contains(*a1 as nat));
                assert(resolved.dom().contains(*a2 as nat));
                assert(resolved.dom().contains(*b1 as nat));
                assert(resolved.dom().contains(*b2 as nat));
                assert(resolved[*a1 as nat] == points@[*a1 as int]@);
                assert(resolved[*a2 as nat] == points@[*a2 as int]@);
                assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                assert(resolved[*b2 as nat] == points@[*b2 as int]@);
            }
            let da = sq_dist_2d_exec(&points[*a1], &points[*a2]);
            let db = sq_dist_2d_exec(&points[*b1], &points[*b2]);
            rational_eqv(&da, &db)
        }

        RuntimeConstraint::Midpoint { mid, a, b, .. } => {
            proof {
                assert(resolved.dom().contains(*mid as nat));
                assert(resolved.dom().contains(*a as nat));
                assert(resolved.dom().contains(*b as nat));
                assert(resolved[*mid as nat] == points@[*mid as int]@);
                assert(resolved[*a as nat] == points@[*a as int]@);
                assert(resolved[*b as nat] == points@[*b as int]@);
            }
            // mid.x * 2 ≡ a.x + b.x && mid.y * 2 ≡ a.y + b.y
            let one = RuntimeRational::from_int(1);
            let two = one.add(&one);
            let mx2 = points[*mid].x.mul(&two);
            let my2 = points[*mid].y.mul(&two);
            let sx = points[*a].x.add(&points[*b].x);
            let sy = points[*a].y.add(&points[*b].y);
            rational_eqv(&mx2, &sx) && rational_eqv(&my2, &sy)
        }

        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } => {
            proof {
                assert(resolved.dom().contains(*a1 as nat));
                assert(resolved.dom().contains(*a2 as nat));
                assert(resolved.dom().contains(*b1 as nat));
                assert(resolved.dom().contains(*b2 as nat));
                assert(resolved[*a1 as nat] == points@[*a1 as int]@);
                assert(resolved[*a2 as nat] == points@[*a2 as int]@);
                assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                assert(resolved[*b2 as nat] == points@[*b2 as int]@);
            }
            // point_on_line2(Line2{db.x, db.y, -(db.x*a1.x + db.y*a1.y)}, a2)
            let dbx = points[*b2].x.sub(&points[*b1].x);
            let dby = points[*b2].y.sub(&points[*b1].y);
            let c_val = dbx.mul(&points[*a1].x).add(&dby.mul(&points[*a1].y)).neg();
            let line = RuntimeLine2::new(dbx, dby, c_val);
            let eval = line2_eval_exec(&line, &points[*a2]);
            eval.is_zero()
        }

        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } => {
            proof {
                assert(resolved.dom().contains(*a1 as nat));
                assert(resolved.dom().contains(*a2 as nat));
                assert(resolved.dom().contains(*b1 as nat));
                assert(resolved.dom().contains(*b2 as nat));
                assert(resolved[*a1 as nat] == points@[*a1 as int]@);
                assert(resolved[*a2 as nat] == points@[*a2 as int]@);
                assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                assert(resolved[*b2 as nat] == points@[*b2 as int]@);
            }
            // point_on_line2(Line2{db.y, -db.x, -(db.y*a1.x + (-db.x)*a1.y)}, a2)
            let dbx = points[*b2].x.sub(&points[*b1].x);
            let dby = points[*b2].y.sub(&points[*b1].y);
            let neg_dbx = dbx.neg();
            let c_val = dby.mul(&points[*a1].x).add(&neg_dbx.mul(&points[*a1].y)).neg();
            let line = RuntimeLine2::new(dby, neg_dbx, c_val);
            let eval = line2_eval_exec(&line, &points[*a2]);
            eval.is_zero()
        }

        RuntimeConstraint::Collinear { a, b, c, .. } => {
            proof {
                assert(resolved.dom().contains(*a as nat));
                assert(resolved.dom().contains(*b as nat));
                assert(resolved.dom().contains(*c as nat));
                assert(resolved[*a as nat] == points@[*a as int]@);
                assert(resolved[*b as nat] == points@[*b as int]@);
                assert(resolved[*c as nat] == points@[*c as int]@);
            }
            let line = line2_from_points_exec(&points[*a], &points[*b]);
            let eval = line2_eval_exec(&line, &points[*c]);
            eval.is_zero()
        }

        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } => {
            proof {
                assert(resolved.dom().contains(*point as nat));
                assert(resolved.dom().contains(*center as nat));
                assert(resolved.dom().contains(*radius_point as nat));
                assert(resolved[*point as nat] == points@[*point as int]@);
                assert(resolved[*center as nat] == points@[*center as int]@);
                assert(resolved[*radius_point as nat] == points@[*radius_point as int]@);
            }
            let d_point = sq_dist_2d_exec(&points[*point], &points[*center]);
            let d_radius = sq_dist_2d_exec(&points[*radius_point], &points[*center]);
            rational_eqv(&d_point, &d_radius)
        }

        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
            proof {
                assert(resolved.dom().contains(*point as nat));
                assert(resolved.dom().contains(*original as nat));
                assert(resolved.dom().contains(*axis_a as nat));
                assert(resolved.dom().contains(*axis_b as nat));
                assert(resolved[*point as nat] == points@[*point as int]@);
                assert(resolved[*original as nat] == points@[*original as int]@);
                assert(resolved[*axis_a as nat] == points@[*axis_a as int]@);
                assert(resolved[*axis_b as nat] == points@[*axis_b as int]@);
            }
            // Compute reflect(original, axis_a, axis_b) and compare with point
            // d = axis_b - axis_a
            let dx = points[*axis_b].x.sub(&points[*axis_a].x);
            let dy = points[*axis_b].y.sub(&points[*axis_a].y);
            // pa = original - axis_a
            let pax = points[*original].x.sub(&points[*axis_a].x);
            let pay = points[*original].y.sub(&points[*axis_a].y);
            // dot_dd = dx*dx + dy*dy
            let dot_dd = dx.mul(&dx).add(&dy.mul(&dy));
            // If axis is degenerate (both axis points coincide), return false
            if dot_dd.is_zero() {
                return false;
            }
            // dot_pad = pax*dx + pay*dy
            let dot_pad = pax.mul(&dx).add(&pay.mul(&dy));
            // t = dot_pad / dot_dd
            let t = dot_pad.div(&dot_dd);
            // proj = axis_a + t * d
            let proj_x = points[*axis_a].x.add(&t.mul(&dx));
            let proj_y = points[*axis_a].y.add(&t.mul(&dy));
            // reflected = 2 * proj - original
            let one = RuntimeRational::from_int(1);
            let two = one.add(&one);
            let ref_x = two.mul(&proj_x).sub(&points[*original].x);
            let ref_y = two.mul(&proj_y).sub(&points[*original].y);
            // Compare point with reflected
            rational_eqv(&points[*point].x, &ref_x)
                && rational_eqv(&points[*point].y, &ref_y)
        }
    }
}

/// Check if all constraints in a Vec are satisfied.
pub fn check_all_constraints_exec(
    constraints: &Vec<RuntimeConstraint>,
    points: &Vec<RuntimePoint2>,
) -> (out: bool)
    requires
        all_points_wf(points@),
        forall|i: int| 0 <= i < constraints@.len() ==>
            runtime_constraint_wf(#[trigger] constraints@[i], points@.len() as nat),
    ensures
        out ==> forall|i: int| 0 <= i < constraints@.len() ==>
            constraint_satisfied(
                runtime_constraint_model(#[trigger] constraints@[i]),
                vec_to_resolved_map(points_view(points@)),
            ),
{
    let mut i: usize = 0;
    while i < constraints.len()
        invariant
            0 <= i <= constraints.len(),
            all_points_wf(points@),
            forall|k: int| 0 <= k < constraints@.len() ==>
                runtime_constraint_wf(#[trigger] constraints@[k], points@.len() as nat),
            forall|j: int| 0 <= j < i as int ==>
                constraint_satisfied(
                    runtime_constraint_model(#[trigger] constraints@[j]),
                    vec_to_resolved_map(points_view(points@)),
                ),
        decreases constraints.len() - i,
    {
        assert(runtime_constraint_wf(constraints@[i as int], points@.len() as nat));
        if !check_constraint_satisfied_exec(&constraints[i], points) {
            return false;
        }
        i = i + 1;
    }
    true
}

} // verus!
