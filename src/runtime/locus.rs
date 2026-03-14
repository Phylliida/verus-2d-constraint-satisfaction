use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::runtime::point2::*;
use verus_geometry::runtime::line2::*;
use verus_geometry::runtime::circle2::*;
use verus_geometry::runtime::voronoi::sq_dist_2d_exec;
use verus_rational::runtime_rational::RuntimeRational;
use verus_linalg::runtime::copy_rational;
use crate::entities::*;
use crate::constraints::*;
use crate::locus::*;
use crate::runtime::constraint::*;

type RationalModel = verus_rational::rational::Rational;

verus! {

// ===========================================================================
//  Runtime locus type
// ===========================================================================

/// Runtime representation of a geometric locus.
pub enum RuntimeLocus {
    FullPlane,
    OnLine { line: RuntimeLine2 },
    OnCircle { circle: RuntimeCircle2 },
    AtPoint { point: RuntimePoint2 },
}

impl RuntimeLocus {
    pub open spec fn wf_spec(&self) -> bool {
        match self {
            RuntimeLocus::FullPlane => true,
            RuntimeLocus::OnLine { line } => line.wf_spec(),
            RuntimeLocus::OnCircle { circle } => circle.wf_spec(),
            RuntimeLocus::AtPoint { point } => point.wf_spec(),
        }
    }

    pub open spec fn spec_locus(&self) -> Locus2d<RationalModel> {
        match self {
            RuntimeLocus::FullPlane => Locus2d::FullPlane,
            RuntimeLocus::OnLine { line } => Locus2d::OnLine(line@),
            RuntimeLocus::OnCircle { circle } => Locus2d::OnCircle(circle@),
            RuntimeLocus::AtPoint { point } => Locus2d::AtPoint(point@),
        }
    }

    pub open spec fn is_nontrivial(&self) -> bool {
        !matches!(self, RuntimeLocus::FullPlane)
    }
}

// ===========================================================================
//  Constraint → Locus at runtime
// ===========================================================================

/// Compute the locus a constraint imposes on target, given resolved points.
/// `resolved_flags[i]` indicates whether entity i is resolved.
/// Mirrors spec-level `constraint_to_locus`.
pub fn constraint_to_locus_exec(
    rc: &RuntimeConstraint,
    points: &Vec<RuntimePoint2>,
    resolved_flags: &Vec<bool>,
    target: usize,
) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat),
        all_points_wf(points@),
        resolved_flags@.len() == points@.len(),
        (target as int) < points@.len(),
        // resolved_flags[i] == true iff entity i is in the partial resolved map
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) ==
            partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
    ensures
        out.wf_spec(),
        out.spec_locus() == constraint_to_locus(
            runtime_constraint_model(*rc),
            partial_resolved_map(points_view(points@), resolved_flags@),
            target as nat,
        ),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);

    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::Coincident { a: *a as nat, b: *b as nat });
            }
            if target == *a && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let point = RuntimePoint2::new(
                    copy_rational(&points[*b].x),
                    copy_rational(&points[*b].y),
                );
                RuntimeLocus::AtPoint { point }
            } else if target == *b && resolved_flags[*a] {
                proof {
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@);
                }
                let point = RuntimePoint2::new(
                    copy_rational(&points[*a].x),
                    copy_rational(&points[*a].y),
                );
                RuntimeLocus::AtPoint { point }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::DistanceSq { a, b, dist_sq, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::DistanceSq {
                    a: *a as nat, b: *b as nat, dist_sq: dist_sq@,
                });
            }
            if target == *a && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let center = RuntimePoint2::new(
                    copy_rational(&points[*b].x),
                    copy_rational(&points[*b].y),
                );
                let r_sq = copy_rational(dist_sq);
                let circle = RuntimeCircle2::from_center_radius_sq(center, r_sq);
                RuntimeLocus::OnCircle { circle }
            } else if target == *b && resolved_flags[*a] {
                proof {
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@);
                }
                let center = RuntimePoint2::new(
                    copy_rational(&points[*a].x),
                    copy_rational(&points[*a].y),
                );
                let r_sq = copy_rational(dist_sq);
                let circle = RuntimeCircle2::from_center_radius_sq(center, r_sq);
                RuntimeLocus::OnCircle { circle }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::FixedX { point, x, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::FixedX { point: *point as nat, x: x@ });
            }
            if target == *point {
                let one = RuntimeRational::from_int(1);
                let zero = RuntimeRational::from_int(0);
                let neg_x = x.neg();
                let line = RuntimeLine2::new(one, zero, neg_x);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::FixedY { point, y, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::FixedY { point: *point as nat, y: y@ });
            }
            if target == *point {
                let zero = RuntimeRational::from_int(0);
                let one = RuntimeRational::from_int(1);
                let neg_y = y.neg();
                let line = RuntimeLine2::new(zero, one, neg_y);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::SameX { a, b, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::SameX { a: *a as nat, b: *b as nat });
            }
            if target == *a && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let one = RuntimeRational::from_int(1);
                let zero = RuntimeRational::from_int(0);
                let neg_bx = points[*b].x.neg();
                let line = RuntimeLine2::new(one, zero, neg_bx);
                RuntimeLocus::OnLine { line }
            } else if target == *b && resolved_flags[*a] {
                proof {
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@);
                }
                let one = RuntimeRational::from_int(1);
                let zero = RuntimeRational::from_int(0);
                let neg_ax = points[*a].x.neg();
                let line = RuntimeLine2::new(one, zero, neg_ax);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::SameY { a, b, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::SameY { a: *a as nat, b: *b as nat });
            }
            if target == *a && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let zero = RuntimeRational::from_int(0);
                let one = RuntimeRational::from_int(1);
                let neg_by = points[*b].y.neg();
                let line = RuntimeLine2::new(zero, one, neg_by);
                RuntimeLocus::OnLine { line }
            } else if target == *b && resolved_flags[*a] {
                proof {
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@);
                }
                let zero = RuntimeRational::from_int(0);
                let one = RuntimeRational::from_int(1);
                let neg_ay = points[*a].y.neg();
                let line = RuntimeLine2::new(zero, one, neg_ay);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::PointOnLine {
                    point: *point as nat, line_a: *line_a as nat, line_b: *line_b as nat,
                });
            }
            if target == *point && resolved_flags[*line_a] && resolved_flags[*line_b] {
                proof {
                    assert(resolved.dom().contains(*line_a as nat));
                    assert(resolved.dom().contains(*line_b as nat));
                    assert(resolved[*line_a as nat] == points@[*line_a as int]@);
                    assert(resolved[*line_b as nat] == points@[*line_b as int]@);
                }
                let line = line2_from_points_exec(&points[*line_a], &points[*line_b]);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::EqualLengthSq {
                    a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat,
                });
            }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let r2 = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let center = RuntimePoint2::new(
                    copy_rational(&points[*a2].x),
                    copy_rational(&points[*a2].y),
                );
                let circle = RuntimeCircle2::from_center_radius_sq(center, r2);
                RuntimeLocus::OnCircle { circle }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let r2 = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let center = RuntimePoint2::new(
                    copy_rational(&points[*a1].x),
                    copy_rational(&points[*a1].y),
                );
                let circle = RuntimeCircle2::from_center_radius_sq(center, r2);
                RuntimeLocus::OnCircle { circle }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::Midpoint { mid, a, b, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::Midpoint {
                    mid: *mid as nat, a: *a as nat, b: *b as nat,
                });
            }
            if target == *mid && resolved_flags[*a] && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@);
                    assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let one = RuntimeRational::from_int(1);
                let two = one.add(&one);
                let sx = points[*a].x.add(&points[*b].x);
                let sy = points[*a].y.add(&points[*b].y);
                let mx = sx.div(&two);
                let my = sy.div(&two);
                let point = RuntimePoint2::new(mx, my);
                RuntimeLocus::AtPoint { point }
            } else if target == *a && resolved_flags[*mid] && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*mid as nat));
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*mid as nat] == points@[*mid as int]@);
                    assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let one = RuntimeRational::from_int(1);
                let two = one.add(&one);
                let ax = two.mul(&points[*mid].x).sub(&points[*b].x);
                let ay = two.mul(&points[*mid].y).sub(&points[*b].y);
                let point = RuntimePoint2::new(ax, ay);
                RuntimeLocus::AtPoint { point }
            } else if target == *b && resolved_flags[*mid] && resolved_flags[*a] {
                proof {
                    assert(resolved.dom().contains(*mid as nat));
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved[*mid as nat] == points@[*mid as int]@);
                    assert(resolved[*a as nat] == points@[*a as int]@);
                }
                let one = RuntimeRational::from_int(1);
                let two = one.add(&one);
                let bx = two.mul(&points[*mid].x).sub(&points[*a].x);
                let by = two.mul(&points[*mid].y).sub(&points[*a].y);
                let point = RuntimePoint2::new(bx, by);
                RuntimeLocus::AtPoint { point }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::Perpendicular {
                    a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat,
                });
            }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x);
                let dby = points[*b2].y.sub(&points[*b1].y);
                let c_val = dbx.mul(&points[*a2].x).add(&dby.mul(&points[*a2].y)).neg();
                let line = RuntimeLine2::new(dbx, dby, c_val);
                RuntimeLocus::OnLine { line }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x);
                let dby = points[*b2].y.sub(&points[*b1].y);
                let c_val = dbx.mul(&points[*a1].x).add(&dby.mul(&points[*a1].y)).neg();
                let line = RuntimeLine2::new(dbx, dby, c_val);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::Parallel {
                    a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat,
                });
            }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x);
                let dby = points[*b2].y.sub(&points[*b1].y);
                let neg_dbx = dbx.neg();
                let c_val = dby.mul(&points[*a2].x).add(&neg_dbx.mul(&points[*a2].y)).neg();
                let line = RuntimeLine2::new(dby, neg_dbx, c_val);
                RuntimeLocus::OnLine { line }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x);
                let dby = points[*b2].y.sub(&points[*b1].y);
                let neg_dbx = dbx.neg();
                let c_val = dby.mul(&points[*a1].x).add(&neg_dbx.mul(&points[*a1].y)).neg();
                let line = RuntimeLine2::new(dby, neg_dbx, c_val);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::Collinear { a, b, c, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::Collinear {
                    a: *a as nat, b: *b as nat, c: *c as nat,
                });
            }
            if target == *c && resolved_flags[*a] && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@);
                    assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let line = line2_from_points_exec(&points[*a], &points[*b]);
                RuntimeLocus::OnLine { line }
            } else if target == *a && resolved_flags[*b] && resolved_flags[*c] {
                proof {
                    assert(resolved.dom().contains(*b as nat));
                    assert(resolved.dom().contains(*c as nat));
                    assert(resolved[*b as nat] == points@[*b as int]@);
                    assert(resolved[*c as nat] == points@[*c as int]@);
                }
                let line = line2_from_points_exec(&points[*b], &points[*c]);
                RuntimeLocus::OnLine { line }
            } else if target == *b && resolved_flags[*a] && resolved_flags[*c] {
                proof {
                    assert(resolved.dom().contains(*a as nat));
                    assert(resolved.dom().contains(*c as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@);
                    assert(resolved[*c as nat] == points@[*c as int]@);
                }
                let line = line2_from_points_exec(&points[*a], &points[*c]);
                RuntimeLocus::OnLine { line }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::PointOnCircle {
                    point: *point as nat, center: *center as nat, radius_point: *radius_point as nat,
                });
            }
            if target == *point && resolved_flags[*center] && resolved_flags[*radius_point] {
                proof {
                    assert(resolved.dom().contains(*center as nat));
                    assert(resolved.dom().contains(*radius_point as nat));
                    assert(resolved[*center as nat] == points@[*center as int]@);
                    assert(resolved[*radius_point as nat] == points@[*radius_point as int]@);
                }
                let r2 = sq_dist_2d_exec(&points[*radius_point], &points[*center]);
                let ctr = RuntimePoint2::new(
                    copy_rational(&points[*center].x),
                    copy_rational(&points[*center].y),
                );
                let circle = RuntimeCircle2::from_center_radius_sq(ctr, r2);
                RuntimeLocus::OnCircle { circle }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::Symmetric {
                    point: *point as nat, original: *original as nat,
                    axis_a: *axis_a as nat, axis_b: *axis_b as nat,
                });
            }
            if target == *point && resolved_flags[*original] && resolved_flags[*axis_a] && resolved_flags[*axis_b] {
                proof {
                    assert(resolved.dom().contains(*original as nat));
                    assert(resolved.dom().contains(*axis_a as nat));
                    assert(resolved.dom().contains(*axis_b as nat));
                    assert(resolved[*original as nat] == points@[*original as int]@);
                    assert(resolved[*axis_a as nat] == points@[*axis_a as int]@);
                    assert(resolved[*axis_b as nat] == points@[*axis_b as int]@);
                }
                // Compute reflect(original, axis_a, axis_b)
                // d = axis_b - axis_a
                let dx = points[*axis_b].x.sub(&points[*axis_a].x);
                let dy = points[*axis_b].y.sub(&points[*axis_a].y);
                // pa = original - axis_a
                let pax = points[*original].x.sub(&points[*axis_a].x);
                let pay = points[*original].y.sub(&points[*axis_a].y);
                // dot_dd = dx*dx + dy*dy
                let dot_dd = dx.mul(&dx).add(&dy.mul(&dy));
                let one = RuntimeRational::from_int(1);
                let two = one.add(&one);
                // dot_pad = pax*dx + pay*dy
                let dot_pad = pax.mul(&dx).add(&pay.mul(&dy));
                // t = dot_pad / dot_dd (or dot_pad * dot_dd when degenerate)
                // For Rational: div(a,b) = a * reciprocal(b).
                // When b.num == 0, reciprocal(b) == b structurally,
                // so div(a,b) == a * b. We exploit this to avoid the
                // RuntimeRational::div non-zero precondition.
                let t = if dot_dd.is_zero() {
                    proof {
                        // dot_dd.is_zero() → dot_dd@.eqv_spec(0) ↔ dot_dd@.num == 0
                        RationalModel::lemma_eqv_zero_iff_num_zero(dot_dd@);
                        // Now Z3 knows dot_dd@.num == 0
                        // reciprocal_spec with num==0 returns self
                        assert(dot_dd@.reciprocal_spec() == dot_dd@);
                        // div_spec = mul_spec(self, rhs.reciprocal_spec()) = mul_spec(self, rhs)
                        assert(dot_pad@.div_spec(dot_dd@) == dot_pad@.mul_spec(dot_dd@));
                    }
                    dot_pad.mul(&dot_dd)
                } else {
                    dot_pad.div(&dot_dd)
                };
                // proj = axis_a + t * d
                let proj_x = points[*axis_a].x.add(&t.mul(&dx));
                let proj_y = points[*axis_a].y.add(&t.mul(&dy));
                // reflected = 2 * proj - original
                let ref_x = two.mul(&proj_x).sub(&points[*original].x);
                let ref_y = two.mul(&proj_y).sub(&points[*original].y);
                let point = RuntimePoint2::new(ref_x, ref_y);
                RuntimeLocus::AtPoint { point }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::FixedPoint { point, x, y, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::FixedPoint {
                    point: *point as nat, x: x@, y: y@,
                });
            }
            if target == *point {
                let px = copy_rational(x);
                let py = copy_rational(y);
                let pt = RuntimePoint2::new(px, py);
                RuntimeLocus::AtPoint { point: pt }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::Ratio { a1, a2, b1, b2, ratio_sq, .. } => {
            proof {
                assert(model == Constraint::<RationalModel>::Ratio {
                    a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat, ratio_sq: ratio_sq@,
                });
            }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let db = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let r2 = ratio_sq.mul(&db);
                let center = RuntimePoint2::new(
                    copy_rational(&points[*a2].x),
                    copy_rational(&points[*a2].y),
                );
                let circle = RuntimeCircle2::from_center_radius_sq(center, r2);
                RuntimeLocus::OnCircle { circle }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat));
                    assert(resolved.dom().contains(*b1 as nat));
                    assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@);
                    assert(resolved[*b1 as nat] == points@[*b1 as int]@);
                    assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let db = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let r2 = ratio_sq.mul(&db);
                let center = RuntimePoint2::new(
                    copy_rational(&points[*a1].x),
                    copy_rational(&points[*a1].y),
                );
                let circle = RuntimeCircle2::from_center_radius_sq(center, r2);
                RuntimeLocus::OnCircle { circle }
            } else {
                RuntimeLocus::FullPlane
            }
        }

        RuntimeConstraint::Tangent { .. } => {
            RuntimeLocus::FullPlane
        }

        RuntimeConstraint::CircleTangent { .. } => {
            RuntimeLocus::FullPlane
        }

        RuntimeConstraint::Angle { .. } => {
            RuntimeLocus::FullPlane
        }
    }
}

} // verus!
