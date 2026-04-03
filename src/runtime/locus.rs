use vstd::prelude::*;
use super::{RuntimePoint2, RuntimeLine2, RuntimeCircle2};
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
use verus_rational::runtime_rational::copy_rational;
use crate::entities::*;
use crate::constraints::*;
use crate::locus::*;
use crate::runtime::constraint::*;

type RationalModel = verus_rational::rational::Rational;

verus! {

//  ===========================================================================
//   Runtime locus type
//  ===========================================================================

///  Runtime representation of a geometric locus.
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

//  ===========================================================================
//   Line construction helpers (runtime)
//  ===========================================================================

///  Runtime vertical line at x-coordinate: mirrors spec-level vertical_line.
fn vertical_line_exec(x: &RuntimeRational) -> (out: RuntimeLine2)
    requires x.wf_spec(),
    ensures out.wf_spec(), out@ == vertical_line::<RationalModel>(x@),
{
    let one = RuntimeRational::from_int(1);
    let zero = RuntimeRational::from_int(0);
    let neg_x = x.neg();
    RuntimeLine2::new(one, zero, neg_x)
}

///  Runtime horizontal line at y-coordinate: mirrors spec-level horizontal_line.
fn horizontal_line_exec(y: &RuntimeRational) -> (out: RuntimeLine2)
    requires y.wf_spec(),
    ensures out.wf_spec(), out@ == horizontal_line::<RationalModel>(y@),
{
    let zero = RuntimeRational::from_int(0);
    let one = RuntimeRational::from_int(1);
    let neg_y = y.neg();
    RuntimeLine2::new(zero, one, neg_y)
}

//  ===========================================================================
//   Per-constraint locus helpers
//  ===========================================================================

//  Shared requires/ensures for all locus helpers (same as constraint_to_locus_exec).
//  Each helper handles one constraint variant, returning FullPlane for non-matching variants.

fn locus_coincident_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Coincident{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::Coincident { a, b, .. } => {
            proof { assert(model == Constraint::<RationalModel>::Coincident { a: *a as nat, b: *b as nat }); }
            if target == *a && resolved_flags[*b] {
                proof { assert(resolved.dom().contains(*b as nat)); assert(resolved[*b as nat] == points@[*b as int]@); }
                RuntimeLocus::AtPoint { point: RuntimePoint2::new(copy_rational(&points[*b].x), copy_rational(&points[*b].y)) }
            } else if target == *b && resolved_flags[*a] {
                proof { assert(resolved.dom().contains(*a as nat)); assert(resolved[*a as nat] == points@[*a as int]@); }
                RuntimeLocus::AtPoint { point: RuntimePoint2::new(copy_rational(&points[*a].x), copy_rational(&points[*a].y)) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_distance_sq_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::DistanceSq{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::DistanceSq { a, b, dist_sq, .. } => {
            proof { assert(model == Constraint::<RationalModel>::DistanceSq { a: *a as nat, b: *b as nat, dist_sq: dist_sq@ }); }
            if target == *a && resolved_flags[*b] {
                proof { assert(resolved.dom().contains(*b as nat)); assert(resolved[*b as nat] == points@[*b as int]@); }
                let center = RuntimePoint2::new(copy_rational(&points[*b].x), copy_rational(&points[*b].y));
                RuntimeLocus::OnCircle { circle: RuntimeCircle2::from_center_radius_sq(center, copy_rational(dist_sq)) }
            } else if target == *b && resolved_flags[*a] {
                proof { assert(resolved.dom().contains(*a as nat)); assert(resolved[*a as nat] == points@[*a as int]@); }
                let center = RuntimePoint2::new(copy_rational(&points[*a].x), copy_rational(&points[*a].y));
                RuntimeLocus::OnCircle { circle: RuntimeCircle2::from_center_radius_sq(center, copy_rational(dist_sq)) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_fixed_x_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::FixedX{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::FixedX { point, x, .. } => {
            proof { assert(model == Constraint::<RationalModel>::FixedX { point: *point as nat, x: x@ }); }
            if target == *point { RuntimeLocus::OnLine { line: vertical_line_exec(x) } }
            else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_fixed_y_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::FixedY{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::FixedY { point, y, .. } => {
            proof { assert(model == Constraint::<RationalModel>::FixedY { point: *point as nat, y: y@ }); }
            if target == *point { RuntimeLocus::OnLine { line: horizontal_line_exec(y) } }
            else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_same_x_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::SameX{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::SameX { a, b, .. } => {
            proof { assert(model == Constraint::<RationalModel>::SameX { a: *a as nat, b: *b as nat }); }
            if target == *a && resolved_flags[*b] {
                proof { assert(resolved.dom().contains(*b as nat)); assert(resolved[*b as nat] == points@[*b as int]@); }
                RuntimeLocus::OnLine { line: vertical_line_exec(&points[*b].x) }
            } else if target == *b && resolved_flags[*a] {
                proof { assert(resolved.dom().contains(*a as nat)); assert(resolved[*a as nat] == points@[*a as int]@); }
                RuntimeLocus::OnLine { line: vertical_line_exec(&points[*a].x) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_same_y_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::SameY{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::SameY { a, b, .. } => {
            proof { assert(model == Constraint::<RationalModel>::SameY { a: *a as nat, b: *b as nat }); }
            if target == *a && resolved_flags[*b] {
                proof { assert(resolved.dom().contains(*b as nat)); assert(resolved[*b as nat] == points@[*b as int]@); }
                RuntimeLocus::OnLine { line: horizontal_line_exec(&points[*b].y) }
            } else if target == *b && resolved_flags[*a] {
                proof { assert(resolved.dom().contains(*a as nat)); assert(resolved[*a as nat] == points@[*a as int]@); }
                RuntimeLocus::OnLine { line: horizontal_line_exec(&points[*a].y) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_point_on_line_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::PointOnLine{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::PointOnLine { point, line_a, line_b, .. } => {
            proof { assert(model == Constraint::<RationalModel>::PointOnLine { point: *point as nat, line_a: *line_a as nat, line_b: *line_b as nat }); }
            if target == *point && resolved_flags[*line_a] && resolved_flags[*line_b] {
                proof {
                    assert(resolved.dom().contains(*line_a as nat)); assert(resolved.dom().contains(*line_b as nat));
                    assert(resolved[*line_a as nat] == points@[*line_a as int]@); assert(resolved[*line_b as nat] == points@[*line_b as int]@);
                }
                RuntimeLocus::OnLine { line: line2_from_points_exec(&points[*line_a], &points[*line_b]) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_equal_length_sq_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::EqualLengthSq{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::EqualLengthSq { a1, a2, b1, b2, .. } => {
            proof { assert(model == Constraint::<RationalModel>::EqualLengthSq { a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat }); }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let r2 = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let center = RuntimePoint2::new(copy_rational(&points[*a2].x), copy_rational(&points[*a2].y));
                RuntimeLocus::OnCircle { circle: RuntimeCircle2::from_center_radius_sq(center, r2) }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let r2 = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let center = RuntimePoint2::new(copy_rational(&points[*a1].x), copy_rational(&points[*a1].y));
                RuntimeLocus::OnCircle { circle: RuntimeCircle2::from_center_radius_sq(center, r2) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_midpoint_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Midpoint{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::Midpoint { mid, a, b, .. } => {
            proof { assert(model == Constraint::<RationalModel>::Midpoint { mid: *mid as nat, a: *a as nat, b: *b as nat }); }
            if target == *mid && resolved_flags[*a] && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*a as nat)); assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*a as nat] == points@[*a as int]@); assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let one = RuntimeRational::from_int(1); let two = one.add(&one);
                proof {
                    RationalModel::lemma_eqv_zero_iff_num_zero(two@);
                }
                let sx = points[*a].x.add(&points[*b].x);
                let sy = points[*a].y.add(&points[*b].y);
                let mx = sx.div(&two);
                let my = sy.div(&two);
                RuntimeLocus::AtPoint { point: RuntimePoint2::new(mx, my) }
            } else if target == *a && resolved_flags[*mid] && resolved_flags[*b] {
                proof {
                    assert(resolved.dom().contains(*mid as nat)); assert(resolved.dom().contains(*b as nat));
                    assert(resolved[*mid as nat] == points@[*mid as int]@); assert(resolved[*b as nat] == points@[*b as int]@);
                }
                let one = RuntimeRational::from_int(1); let two = one.add(&one);
                let ax = two.mul(&points[*mid].x).sub(&points[*b].x);
                let ay = two.mul(&points[*mid].y).sub(&points[*b].y);
                RuntimeLocus::AtPoint { point: RuntimePoint2::new(ax, ay) }
            } else if target == *b && resolved_flags[*mid] && resolved_flags[*a] {
                proof {
                    assert(resolved.dom().contains(*mid as nat)); assert(resolved.dom().contains(*a as nat));
                    assert(resolved[*mid as nat] == points@[*mid as int]@); assert(resolved[*a as nat] == points@[*a as int]@);
                }
                let one = RuntimeRational::from_int(1); let two = one.add(&one);
                let bx = two.mul(&points[*mid].x).sub(&points[*a].x);
                let by = two.mul(&points[*mid].y).sub(&points[*a].y);
                RuntimeLocus::AtPoint { point: RuntimePoint2::new(bx, by) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_perpendicular_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Perpendicular{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::Perpendicular { a1, a2, b1, b2, .. } => {
            proof { assert(model == Constraint::<RationalModel>::Perpendicular { a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat }); }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x); let dby = points[*b2].y.sub(&points[*b1].y);
                let c_val = dbx.mul(&points[*a2].x).add(&dby.mul(&points[*a2].y)).neg();
                RuntimeLocus::OnLine { line: RuntimeLine2::new(dbx, dby, c_val) }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x); let dby = points[*b2].y.sub(&points[*b1].y);
                let c_val = dbx.mul(&points[*a1].x).add(&dby.mul(&points[*a1].y)).neg();
                RuntimeLocus::OnLine { line: RuntimeLine2::new(dbx, dby, c_val) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_parallel_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Parallel{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::Parallel { a1, a2, b1, b2, .. } => {
            proof { assert(model == Constraint::<RationalModel>::Parallel { a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat }); }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x); let dby = points[*b2].y.sub(&points[*b1].y); let neg_dbx = dbx.neg();
                let c_val = dby.mul(&points[*a2].x).add(&neg_dbx.mul(&points[*a2].y)).neg();
                RuntimeLocus::OnLine { line: RuntimeLine2::new(dby, neg_dbx, c_val) }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let dbx = points[*b2].x.sub(&points[*b1].x); let dby = points[*b2].y.sub(&points[*b1].y); let neg_dbx = dbx.neg();
                let c_val = dby.mul(&points[*a1].x).add(&neg_dbx.mul(&points[*a1].y)).neg();
                RuntimeLocus::OnLine { line: RuntimeLine2::new(dby, neg_dbx, c_val) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_collinear_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Collinear{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::Collinear { a, b, c, .. } => {
            proof { assert(model == Constraint::<RationalModel>::Collinear { a: *a as nat, b: *b as nat, c: *c as nat }); }
            if target == *c && resolved_flags[*a] && resolved_flags[*b] {
                proof { assert(resolved.dom().contains(*a as nat)); assert(resolved.dom().contains(*b as nat)); assert(resolved[*a as nat] == points@[*a as int]@); assert(resolved[*b as nat] == points@[*b as int]@); }
                RuntimeLocus::OnLine { line: line2_from_points_exec(&points[*a], &points[*b]) }
            } else if target == *a && resolved_flags[*b] && resolved_flags[*c] {
                proof { assert(resolved.dom().contains(*b as nat)); assert(resolved.dom().contains(*c as nat)); assert(resolved[*b as nat] == points@[*b as int]@); assert(resolved[*c as nat] == points@[*c as int]@); }
                RuntimeLocus::OnLine { line: line2_from_points_exec(&points[*b], &points[*c]) }
            } else if target == *b && resolved_flags[*a] && resolved_flags[*c] {
                proof { assert(resolved.dom().contains(*a as nat)); assert(resolved.dom().contains(*c as nat)); assert(resolved[*a as nat] == points@[*a as int]@); assert(resolved[*c as nat] == points@[*c as int]@); }
                RuntimeLocus::OnLine { line: line2_from_points_exec(&points[*a], &points[*c]) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_point_on_circle_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::PointOnCircle{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::PointOnCircle { point, center, radius_point, .. } => {
            proof { assert(model == Constraint::<RationalModel>::PointOnCircle { point: *point as nat, center: *center as nat, radius_point: *radius_point as nat }); }
            if target == *point && resolved_flags[*center] && resolved_flags[*radius_point] {
                proof {
                    assert(resolved.dom().contains(*center as nat)); assert(resolved.dom().contains(*radius_point as nat));
                    assert(resolved[*center as nat] == points@[*center as int]@); assert(resolved[*radius_point as nat] == points@[*radius_point as int]@);
                }
                let r2 = sq_dist_2d_exec(&points[*radius_point], &points[*center]);
                let ctr = RuntimePoint2::new(copy_rational(&points[*center].x), copy_rational(&points[*center].y));
                RuntimeLocus::OnCircle { circle: RuntimeCircle2::from_center_radius_sq(ctr, r2) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_symmetric_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Symmetric{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::Symmetric { point, original, axis_a, axis_b, .. } => {
            proof { assert(model == Constraint::<RationalModel>::Symmetric { point: *point as nat, original: *original as nat, axis_a: *axis_a as nat, axis_b: *axis_b as nat }); }
            if target == *point && resolved_flags[*original] && resolved_flags[*axis_a] && resolved_flags[*axis_b] {
                proof {
                    assert(resolved.dom().contains(*original as nat)); assert(resolved.dom().contains(*axis_a as nat)); assert(resolved.dom().contains(*axis_b as nat));
                    assert(resolved[*original as nat] == points@[*original as int]@); assert(resolved[*axis_a as nat] == points@[*axis_a as int]@); assert(resolved[*axis_b as nat] == points@[*axis_b as int]@);
                }
                let dx = points[*axis_b].x.sub(&points[*axis_a].x);
                let dy = points[*axis_b].y.sub(&points[*axis_a].y);
                let pax = points[*original].x.sub(&points[*axis_a].x);
                let pay = points[*original].y.sub(&points[*axis_a].y);
                let dot_dd = dx.mul(&dx).add(&dy.mul(&dy));
                let one = RuntimeRational::from_int(1); let two = one.add(&one);
                let dot_pad = pax.mul(&dx).add(&pay.mul(&dy));
                let t = if dot_dd.is_zero() {
                    proof {
                        RationalModel::lemma_eqv_zero_iff_num_zero(dot_dd@);
                        assert(dot_dd@.reciprocal_spec() == dot_dd@);
                        assert(dot_pad@.div_spec(dot_dd@) == dot_pad@.mul_spec(dot_dd@));
                    }
                    dot_pad.mul(&dot_dd)
                } else {
                    dot_pad.div(&dot_dd)
                };
                let proj_x = points[*axis_a].x.add(&t.mul(&dx));
                let proj_y = points[*axis_a].y.add(&t.mul(&dy));
                let ref_x = two.mul(&proj_x).sub(&points[*original].x);
                let ref_y = two.mul(&proj_y).sub(&points[*original].y);
                RuntimeLocus::AtPoint { point: RuntimePoint2::new(ref_x, ref_y) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_fixed_point_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::FixedPoint{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::FixedPoint { point, x, y, .. } => {
            proof { assert(model == Constraint::<RationalModel>::FixedPoint { point: *point as nat, x: x@, y: y@ }); }
            if target == *point {
                RuntimeLocus::AtPoint { point: RuntimePoint2::new(copy_rational(x), copy_rational(y)) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

fn locus_ratio_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Ratio{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    let ghost resolved = partial_resolved_map(points_view(points@), resolved_flags@);
    let ghost model = runtime_constraint_model(*rc);
    match rc {
        RuntimeConstraint::Ratio { a1, a2, b1, b2, ratio_sq, .. } => {
            proof { assert(model == Constraint::<RationalModel>::Ratio { a1: *a1 as nat, a2: *a2 as nat, b1: *b1 as nat, b2: *b2 as nat, ratio_sq: ratio_sq@ }); }
            if target == *a1 && resolved_flags[*a2] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a2 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a2 as nat] == points@[*a2 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let db = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let r2 = ratio_sq.mul(&db);
                let center = RuntimePoint2::new(copy_rational(&points[*a2].x), copy_rational(&points[*a2].y));
                RuntimeLocus::OnCircle { circle: RuntimeCircle2::from_center_radius_sq(center, r2) }
            } else if target == *a2 && resolved_flags[*a1] && resolved_flags[*b1] && resolved_flags[*b2] {
                proof {
                    assert(resolved.dom().contains(*a1 as nat)); assert(resolved.dom().contains(*b1 as nat)); assert(resolved.dom().contains(*b2 as nat));
                    assert(resolved[*a1 as nat] == points@[*a1 as int]@); assert(resolved[*b1 as nat] == points@[*b1 as int]@); assert(resolved[*b2 as nat] == points@[*b2 as int]@);
                }
                let db = sq_dist_2d_exec(&points[*b1], &points[*b2]);
                let r2 = ratio_sq.mul(&db);
                let center = RuntimePoint2::new(copy_rational(&points[*a1].x), copy_rational(&points[*a1].y));
                RuntimeLocus::OnCircle { circle: RuntimeCircle2::from_center_radius_sq(center, r2) }
            } else { RuntimeLocus::FullPlane }
        }
        _ => { RuntimeLocus::FullPlane }
    }
}

///  Tangent, CircleTangent, and Angle constraints don't impose geometric loci
///  (they are verification-only constraints). Returns FullPlane for matching
///  variants, FullPlane for non-matching.
fn locus_verification_only_exec(rc: &RuntimeConstraint, points: &Vec<RuntimePoint2>, resolved_flags: &Vec<bool>, target: usize) -> (out: RuntimeLocus)
    requires
        runtime_constraint_wf(*rc, points@.len() as nat), all_points_wf(points@),
        resolved_flags@.len() == points@.len(), (target as int) < points@.len(),
        forall|i: int| 0 <= i < resolved_flags@.len() ==>
            (#[trigger] resolved_flags@[i]) == partial_resolved_map(points_view(points@), resolved_flags@).dom().contains(i as nat),
        match runtime_constraint_model(*rc) { Constraint::Tangent{..} | Constraint::CircleTangent{..} | Constraint::Angle{..} | Constraint::NotCoincident{..} | Constraint::NormalToCircle{..} | Constraint::PointOnEllipse{..} | Constraint::PointOnArc{..} => true, _ => false },
    ensures out.wf_spec(), out.spec_locus() == constraint_to_locus(runtime_constraint_model(*rc), partial_resolved_map(points_view(points@), resolved_flags@), target as nat),
{
    RuntimeLocus::FullPlane
}

//  ===========================================================================
//   Constraint → Locus at runtime (dispatcher)
//  ===========================================================================

///  Compute the locus a constraint imposes on target, given resolved points.
///  `resolved_flags[i]` indicates whether entity i is resolved.
///  Mirrors spec-level `constraint_to_locus`.
///  Dispatches to per-constraint helpers for efficient verification.
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
        //  resolved_flags[i] == true iff entity i is in the partial resolved map
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
    match rc {
        RuntimeConstraint::Coincident { .. } => locus_coincident_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::DistanceSq { .. } => locus_distance_sq_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::FixedX { .. } => locus_fixed_x_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::FixedY { .. } => locus_fixed_y_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::SameX { .. } => locus_same_x_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::SameY { .. } => locus_same_y_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::PointOnLine { .. } => locus_point_on_line_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::EqualLengthSq { .. } => locus_equal_length_sq_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Midpoint { .. } => locus_midpoint_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Perpendicular { .. } => locus_perpendicular_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Parallel { .. } => locus_parallel_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Collinear { .. } => locus_collinear_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::PointOnCircle { .. } => locus_point_on_circle_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Symmetric { .. } => locus_symmetric_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::FixedPoint { .. } => locus_fixed_point_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Ratio { .. } => locus_ratio_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Tangent { .. } => locus_verification_only_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::CircleTangent { .. } => locus_verification_only_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::Angle { .. } => locus_verification_only_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::NotCoincident { .. } => locus_verification_only_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::NormalToCircle { .. } => locus_verification_only_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::PointOnEllipse { .. } => locus_verification_only_exec(rc, points, resolved_flags, target),
        RuntimeConstraint::PointOnArc { .. } => locus_verification_only_exec(rc, points, resolved_flags, target),
    }
}

} //  verus!
