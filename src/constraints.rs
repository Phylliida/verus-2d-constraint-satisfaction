use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::line2::*;
use verus_geometry::orient2d::orient2d;
use crate::entities::*;

verus! {

// ===========================================================================
//  Constraint types
// ===========================================================================

/// A 2D geometric constraint between entities.
pub enum Constraint<T: OrderedField> {
    /// Two points coincide.
    Coincident { a: EntityId, b: EntityId },

    /// Squared distance between two points equals a value.
    DistanceSq { a: EntityId, b: EntityId, dist_sq: T },

    /// Fix the x-coordinate of a point.
    FixedX { point: EntityId, x: T },

    /// Fix the y-coordinate of a point.
    FixedY { point: EntityId, y: T },

    /// Two points share the same x-coordinate.
    SameX { a: EntityId, b: EntityId },

    /// Two points share the same y-coordinate.
    SameY { a: EntityId, b: EntityId },

    /// A point lies on the line through two other points.
    PointOnLine { point: EntityId, line_a: EntityId, line_b: EntityId },

    /// Two segments have equal squared length.
    EqualLengthSq { a1: EntityId, a2: EntityId, b1: EntityId, b2: EntityId },

    /// A point is the midpoint of two other points.
    Midpoint { mid: EntityId, a: EntityId, b: EntityId },

    /// Two segments are perpendicular: dot product of direction vectors = 0.
    Perpendicular { a1: EntityId, a2: EntityId, b1: EntityId, b2: EntityId },

    /// Two segments are parallel: cross product of direction vectors = 0.
    Parallel { a1: EntityId, a2: EntityId, b1: EntityId, b2: EntityId },

    /// Three points are collinear (lie on a common line).
    Collinear { a: EntityId, b: EntityId, c: EntityId },

    /// Point lies on the circle defined by center and a radius-defining point.
    /// sq_dist(point, center) ≡ sq_dist(radius_point, center)
    PointOnCircle { point: EntityId, center: EntityId, radius_point: EntityId },

    /// Point is the reflection of `original` across the line through `axis_a` and `axis_b`.
    Symmetric { point: EntityId, original: EntityId, axis_a: EntityId, axis_b: EntityId },

    /// Fix a point to exact coordinates.
    FixedPoint { point: EntityId, x: T, y: T },

    /// Ratio of squared distances: |a1-a2|² ≡ ratio_sq * |b1-b2|²
    Ratio { a1: EntityId, a2: EntityId, b1: EntityId, b2: EntityId, ratio_sq: T },

    /// Line-circle tangency: the squared distance from center to the line through
    /// (line_a, line_b) equals the squared radius (defined by center→radius_point).
    /// eval² ≡ norm_sq * r_sq where line = line2_from_points(line_a, line_b).
    Tangent { line_a: EntityId, line_b: EntityId, center: EntityId, radius_point: EntityId },

    /// Circle-circle tangency (external): (D - R1 - R2)² ≡ 4·R1·R2
    /// where D = sq_dist(c1,c2), Ri = sq_dist(ci, rpi).
    CircleTangent { c1: EntityId, rp1: EntityId, c2: EntityId, rp2: EntityId },

    /// Angle between two segments via squared cosine:
    /// dot(d1,d2)² ≡ cos_sq · norm_sq(d1) · norm_sq(d2)
    /// where d1 = sub2(a2,a1), d2 = sub2(b2,b1).
    Angle { a1: EntityId, a2: EntityId, b1: EntityId, b2: EntityId, cos_sq: T },

    /// Non-degeneracy: two points must NOT coincide.
    /// Verification-only (no constructive locus).
    NotCoincident { a: EntityId, b: EntityId },

    /// Normal to circle: a line segment (line_a, line_b) passes through the center
    /// of a circle, and line_a lies on the circle.
    /// Equivalent to: Collinear(line_a, line_b, center) AND PointOnCircle(line_a, center, radius_point).
    /// Constructive for line_a (locus = circle intersected with line through line_b and center).
    NormalToCircle { line_a: EntityId, line_b: EntityId, center: EntityId, radius_point: EntityId },

    /// Point lies on an ellipse defined by center, semi-major axis endpoint, and semi-minor axis endpoint.
    /// The ellipse passes through semi_a and semi_b with axes along (semi_a - center) and (semi_b - center).
    /// Check: ((dx·ux + dy·uy)²/a² + (dx·vx + dy·vy)²/b²) ≡ 1
    /// where d = point - center, u = semi_a - center (unit direction), v = semi_b - center,
    /// a = |semi_a - center|, b = |semi_b - center|.
    /// Verification-only (quartic locus, not line/circle).
    PointOnEllipse { point: EntityId, center: EntityId, semi_a: EntityId, semi_b: EntityId },

    /// Point lies on a circular arc. The arc is defined by center, radius_point (defines radius),
    /// and two boundary points arc_start and arc_end on the circle.
    /// Check: point is on the circle AND the signed angle from arc_start to point (around center)
    /// is between 0 and the signed angle from arc_start to arc_end.
    /// Uses ordering (not just eqv), so the satisfaction check uses `le` comparisons.
    /// Verification-only.
    PointOnArc { point: EntityId, center: EntityId, radius_point: EntityId,
                 arc_start: EntityId, arc_end: EntityId },
}

// ===========================================================================
//  Constraint satisfaction predicate
// ===========================================================================

/// Check if a constraint is satisfied by the resolved point positions.
pub open spec fn constraint_satisfied<T: OrderedField>(
    c: Constraint<T>, resolved: ResolvedPoints<T>,
) -> bool {
    match c {
        Constraint::Coincident { a, b } => {
            resolved.dom().contains(a) && resolved.dom().contains(b) &&
            resolved[a].eqv(resolved[b])
        }

        Constraint::DistanceSq { a, b, dist_sq } => {
            resolved.dom().contains(a) && resolved.dom().contains(b) &&
            sq_dist_2d(resolved[a], resolved[b]).eqv(dist_sq)
        }

        Constraint::FixedX { point, x } => {
            resolved.dom().contains(point) &&
            resolved[point].x.eqv(x)
        }

        Constraint::FixedY { point, y } => {
            resolved.dom().contains(point) &&
            resolved[point].y.eqv(y)
        }

        Constraint::SameX { a, b } => {
            resolved.dom().contains(a) && resolved.dom().contains(b) &&
            resolved[a].x.eqv(resolved[b].x)
        }

        Constraint::SameY { a, b } => {
            resolved.dom().contains(a) && resolved.dom().contains(b) &&
            resolved[a].y.eqv(resolved[b].y)
        }

        Constraint::PointOnLine { point, line_a, line_b } => {
            resolved.dom().contains(point) &&
            resolved.dom().contains(line_a) &&
            resolved.dom().contains(line_b) &&
            point_on_line2(
                line2_from_points(resolved[line_a], resolved[line_b]),
                resolved[point],
            )
        }

        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            resolved.dom().contains(a1) && resolved.dom().contains(a2) &&
            resolved.dom().contains(b1) && resolved.dom().contains(b2) &&
            sq_dist_2d(resolved[a1], resolved[a2]).eqv(
                sq_dist_2d(resolved[b1], resolved[b2])
            )
        }

        Constraint::Midpoint { mid, a, b } => {
            resolved.dom().contains(mid) &&
            resolved.dom().contains(a) &&
            resolved.dom().contains(b) && {
                let two = T::one().add(T::one());
                // mid.x * 2 ≡ a.x + b.x
                resolved[mid].x.mul(two).eqv(resolved[a].x.add(resolved[b].x)) &&
                resolved[mid].y.mul(two).eqv(resolved[a].y.add(resolved[b].y))
            }
        }

        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            resolved.dom().contains(a1) && resolved.dom().contains(a2) &&
            resolved.dom().contains(b1) && resolved.dom().contains(b2) && {
                // dot(sub2(a2, a1), sub2(b2, b1)) ≡ 0, expressed as point_on_line2
                // to match the locus form and simplify soundness proofs.
                let db = sub2(resolved[b2], resolved[b1]);
                let c = db.x.mul(resolved[a1].x).add(db.y.mul(resolved[a1].y)).neg();
                point_on_line2(Line2 { a: db.x, b: db.y, c }, resolved[a2])
            }
        }

        Constraint::Parallel { a1, a2, b1, b2 } => {
            resolved.dom().contains(a1) && resolved.dom().contains(a2) &&
            resolved.dom().contains(b1) && resolved.dom().contains(b2) && {
                // det2d(sub2(a2, a1), sub2(b2, b1)) ≡ 0, expressed as point_on_line2
                let db = sub2(resolved[b2], resolved[b1]);
                let c = db.y.mul(resolved[a1].x).add(db.x.neg().mul(resolved[a1].y)).neg();
                point_on_line2(Line2 { a: db.y, b: db.x.neg(), c }, resolved[a2])
            }
        }

        Constraint::Collinear { a, b, c } => {
            resolved.dom().contains(a) && resolved.dom().contains(b) &&
            resolved.dom().contains(c) &&
            point_on_line2(
                line2_from_points(resolved[a], resolved[b]),
                resolved[c],
            )
        }

        Constraint::PointOnCircle { point, center, radius_point } => {
            resolved.dom().contains(point) &&
            resolved.dom().contains(center) &&
            resolved.dom().contains(radius_point) &&
            sq_dist_2d(resolved[point], resolved[center]).eqv(
                sq_dist_2d(resolved[radius_point], resolved[center])
            )
        }

        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            resolved.dom().contains(point) &&
            resolved.dom().contains(original) &&
            resolved.dom().contains(axis_a) &&
            resolved.dom().contains(axis_b) &&
            resolved[point].eqv(reflect_point_across_line(
                resolved[original], resolved[axis_a], resolved[axis_b],
            ))
        }

        Constraint::FixedPoint { point, x, y } => {
            resolved.dom().contains(point) &&
            resolved[point].x.eqv(x) && resolved[point].y.eqv(y)
        }

        Constraint::Ratio { a1, a2, b1, b2, ratio_sq } => {
            resolved.dom().contains(a1) && resolved.dom().contains(a2) &&
            resolved.dom().contains(b1) && resolved.dom().contains(b2) &&
            sq_dist_2d(resolved[a1], resolved[a2]).eqv(
                ratio_sq.mul(sq_dist_2d(resolved[b1], resolved[b2]))
            )
        }

        Constraint::Tangent { line_a, line_b, center, radius_point } => {
            resolved.dom().contains(line_a) && resolved.dom().contains(line_b) &&
            resolved.dom().contains(center) && resolved.dom().contains(radius_point) && {
                let line = line2_from_points(resolved[line_a], resolved[line_b]);
                let eval = line2_eval(line, resolved[center]);
                let norm_sq = line.a.mul(line.a).add(line.b.mul(line.b));
                let r_sq = sq_dist_2d(resolved[center], resolved[radius_point]);
                eval.mul(eval).eqv(norm_sq.mul(r_sq))
            }
        }

        Constraint::CircleTangent { c1, rp1, c2, rp2 } => {
            resolved.dom().contains(c1) && resolved.dom().contains(rp1) &&
            resolved.dom().contains(c2) && resolved.dom().contains(rp2) && {
                let d = sq_dist_2d(resolved[c1], resolved[c2]);
                let r1 = sq_dist_2d(resolved[c1], resolved[rp1]);
                let r2 = sq_dist_2d(resolved[c2], resolved[rp2]);
                let four = T::one().add(T::one()).mul(T::one().add(T::one()));
                let diff = d.sub(r1).sub(r2);
                diff.mul(diff).eqv(four.mul(r1).mul(r2))
            }
        }

        Constraint::Angle { a1, a2, b1, b2, cos_sq } => {
            resolved.dom().contains(a1) && resolved.dom().contains(a2) &&
            resolved.dom().contains(b1) && resolved.dom().contains(b2) && {
                let d1 = sub2(resolved[a2], resolved[a1]);
                let d2 = sub2(resolved[b2], resolved[b1]);
                let dp = d1.x.mul(d2.x).add(d1.y.mul(d2.y));
                let n1 = d1.x.mul(d1.x).add(d1.y.mul(d1.y));
                let n2 = d2.x.mul(d2.x).add(d2.y.mul(d2.y));
                dp.mul(dp).eqv(cos_sq.mul(n1).mul(n2))
            }
        }

        Constraint::NotCoincident { a, b } => {
            resolved.dom().contains(a) && resolved.dom().contains(b) &&
            !resolved[a].eqv(resolved[b])
        }

        Constraint::NormalToCircle { line_a, line_b, center, radius_point } => {
            resolved.dom().contains(line_a) && resolved.dom().contains(line_b) &&
            resolved.dom().contains(center) && resolved.dom().contains(radius_point) &&
            // line_a on circle
            sq_dist_2d(resolved[line_a], resolved[center]).eqv(
                sq_dist_2d(resolved[radius_point], resolved[center])) &&
            // line_a, line_b, center collinear
            point_on_line2(
                line2_from_points(resolved[line_a], resolved[line_b]),
                resolved[center])
        }

        Constraint::PointOnEllipse { point, center, semi_a, semi_b } => {
            resolved.dom().contains(point) && resolved.dom().contains(center) &&
            resolved.dom().contains(semi_a) && resolved.dom().contains(semi_b) && {
                // d = point - center
                let d = sub2(resolved[point], resolved[center]);
                // u = semi_a - center (semi-major axis vector)
                let u = sub2(resolved[semi_a], resolved[center]);
                // v = semi_b - center (semi-minor axis vector)
                let vv = sub2(resolved[semi_b], resolved[center]);
                // a_sq = |u|², b_sq = |v|²
                let a_sq = u.x.mul(u.x).add(u.y.mul(u.y));
                let b_sq = vv.x.mul(vv.x).add(vv.y.mul(vv.y));
                // proj_u = dot(d, u), proj_v = dot(d, v)
                let proj_u = d.x.mul(u.x).add(d.y.mul(u.y));
                let proj_v = d.x.mul(vv.x).add(d.y.mul(vv.y));
                // Ellipse equation (multiplied through to avoid division):
                // proj_u² * b_sq + proj_v² * a_sq ≡ a_sq * b_sq
                proj_u.mul(proj_u).mul(b_sq).add(proj_v.mul(proj_v).mul(a_sq))
                    .eqv(a_sq.mul(b_sq))
            }
        }

        Constraint::PointOnArc { point, center, radius_point, arc_start, arc_end } => {
            resolved.dom().contains(point) && resolved.dom().contains(center) &&
            resolved.dom().contains(radius_point) && resolved.dom().contains(arc_start) &&
            resolved.dom().contains(arc_end) && {
                // Point must be on the circle
                let on_circle = sq_dist_2d(resolved[point], resolved[center]).eqv(
                    sq_dist_2d(resolved[radius_point], resolved[center]));
                // Angular check using cross products (signed area test).
                // Point is on the arc from arc_start to arc_end (counterclockwise)
                // iff orient2d(center, arc_start, point) >= 0
                // and orient2d(center, point, arc_end) >= 0
                // and (if the arc is > 180°, handle the reflex case).
                //
                // For simplicity, use the "short arc" convention:
                // orient2d(center, arc_start, point) and orient2d(center, point, arc_end)
                // must have the same sign as orient2d(center, arc_start, arc_end).
                let o_se = orient2d(resolved[center], resolved[arc_start], resolved[arc_end]);
                let o_sp = orient2d(resolved[center], resolved[arc_start], resolved[point]);
                let o_pe = orient2d(resolved[center], resolved[point], resolved[arc_end]);
                // All three orient2d values have consistent sign (all >= 0 or all <= 0):
                // For CCW arc: o_sp >= 0 && o_pe >= 0
                // We use: o_sp * o_se >= 0 && o_pe * o_se >= 0 (same sign as the arc direction)
                on_circle &&
                T::zero().le(o_sp.mul(o_se)) &&
                T::zero().le(o_pe.mul(o_se))
            }
        }
    }
}

/// All entities referenced by a constraint.
pub open spec fn constraint_entities<T: OrderedField>(c: Constraint<T>) -> Set<EntityId> {
    match c {
        Constraint::Coincident { a, b } => set![a, b],
        Constraint::DistanceSq { a, b, .. } => set![a, b],
        Constraint::FixedX { point, .. } => set![point],
        Constraint::FixedY { point, .. } => set![point],
        Constraint::SameX { a, b } => set![a, b],
        Constraint::SameY { a, b } => set![a, b],
        Constraint::PointOnLine { point, line_a, line_b } => set![point, line_a, line_b],
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => set![a1, a2, b1, b2],
        Constraint::Midpoint { mid, a, b } => set![mid, a, b],
        Constraint::Perpendicular { a1, a2, b1, b2 } => set![a1, a2, b1, b2],
        Constraint::Parallel { a1, a2, b1, b2 } => set![a1, a2, b1, b2],
        Constraint::Collinear { a, b, c } => set![a, b, c],
        Constraint::PointOnCircle { point, center, radius_point } => set![point, center, radius_point],
        Constraint::Symmetric { point, original, axis_a, axis_b } => set![point, original, axis_a, axis_b],
        Constraint::FixedPoint { point, .. } => set![point],
        Constraint::Ratio { a1, a2, b1, b2, .. } => set![a1, a2, b1, b2],
        Constraint::Tangent { line_a, line_b, center, radius_point } => set![line_a, line_b, center, radius_point],
        Constraint::CircleTangent { c1, rp1, c2, rp2 } => set![c1, rp1, c2, rp2],
        Constraint::Angle { a1, a2, b1, b2, .. } => set![a1, a2, b1, b2],
        Constraint::NotCoincident { a, b } => set![a, b],
        Constraint::NormalToCircle { line_a, line_b, center, radius_point } =>
            set![line_a, line_b, center, radius_point],
        Constraint::PointOnEllipse { point, center, semi_a, semi_b } =>
            set![point, center, semi_a, semi_b],
        Constraint::PointOnArc { point, center, radius_point, arc_start, arc_end } =>
            set![point, center, radius_point, arc_start, arc_end],
    }
}

/// A constraint is well-formed: entity IDs are distinct where required
/// so that the constraint imposes a non-trivial geometric condition.
pub open spec fn constraint_well_formed<T: OrderedField>(c: Constraint<T>) -> bool {
    match c {
        Constraint::Coincident { a, b } => a != b,
        Constraint::DistanceSq { a, b, .. } => a != b,
        Constraint::FixedX { .. } => true,
        Constraint::FixedY { .. } => true,
        Constraint::SameX { a, b } => a != b,
        Constraint::SameY { a, b } => a != b,
        Constraint::PointOnLine { point, line_a, line_b } =>
            point != line_a && point != line_b && line_a != line_b,
        Constraint::EqualLengthSq { a1, a2, b1, b2 } =>
            a1 != a2 && a1 != b1 && a1 != b2 && a2 != b1 && a2 != b2,
        Constraint::Midpoint { mid, a, b } =>
            mid != a && mid != b && a != b,
        Constraint::Perpendicular { a1, a2, b1, b2 } =>
            a1 != a2 && b1 != b2 && a1 != b1 && a1 != b2 && a2 != b1 && a2 != b2,
        Constraint::Parallel { a1, a2, b1, b2 } =>
            a1 != a2 && b1 != b2 && a1 != b1 && a1 != b2 && a2 != b1 && a2 != b2,
        Constraint::Collinear { a, b, c } =>
            a != b && a != c && b != c,
        Constraint::PointOnCircle { point, center, radius_point } =>
            point != center && point != radius_point && center != radius_point,
        Constraint::Symmetric { point, original, axis_a, axis_b } =>
            point != original && point != axis_a && point != axis_b
            && original != axis_a && original != axis_b && axis_a != axis_b,
        Constraint::FixedPoint { .. } => true,
        Constraint::Ratio { a1, a2, b1, b2, .. } =>
            a1 != a2 && a1 != b1 && a1 != b2 && a2 != b1 && a2 != b2,
        Constraint::Tangent { line_a, line_b, center, radius_point } =>
            line_a != line_b && line_a != center && line_a != radius_point
            && line_b != center && line_b != radius_point && center != radius_point,
        Constraint::CircleTangent { c1, rp1, c2, rp2 } =>
            c1 != rp1 && c2 != rp2 && c1 != c2,
        Constraint::Angle { a1, a2, b1, b2, .. } =>
            a1 != a2 && b1 != b2 && a1 != b1 && a1 != b2 && a2 != b1 && a2 != b2,
        Constraint::NotCoincident { a, b } => a != b,
        Constraint::NormalToCircle { line_a, line_b, center, radius_point } =>
            line_a != line_b && line_a != center && line_a != radius_point
            && line_b != center && line_b != radius_point && center != radius_point,
        Constraint::PointOnEllipse { point, center, semi_a, semi_b } =>
            point != center && point != semi_a && point != semi_b
            && center != semi_a && center != semi_b && semi_a != semi_b,
        Constraint::PointOnArc { point, center, radius_point, arc_start, arc_end } =>
            point != center && center != radius_point
            && arc_start != arc_end && arc_start != center && arc_end != center,
    }
}

/// Whether a constraint is a "verification-only" constraint.
/// These constraints have no locus entities (constraint_locus_entities returns empty set),
/// meaning the solver cannot constructively place points to satisfy them.
/// Instead, they are checked after the plan is fully executed.
pub open spec fn is_verification_constraint<T: OrderedField>(c: Constraint<T>) -> bool {
    match c {
        Constraint::Tangent { .. } => true,
        Constraint::CircleTangent { .. } => true,
        Constraint::Angle { .. } => true,
        Constraint::NotCoincident { .. } => true,
        Constraint::PointOnEllipse { .. } => true,
        Constraint::PointOnArc { .. } => true,
        _ => false,
    }
}

/// Verification constraints have empty locus entities.
pub proof fn lemma_verification_constraint_iff_empty_locus<T: OrderedField>(c: Constraint<T>)
    ensures
        is_verification_constraint(c) <==> constraint_locus_entities(c) =~= Set::empty(),
{
    match c {
        Constraint::Coincident { a, .. } => {
            assert(constraint_locus_entities(c).contains(a));
        }
        Constraint::DistanceSq { a, .. } => {
            assert(constraint_locus_entities(c).contains(a));
        }
        Constraint::FixedX { point, .. } => {
            assert(constraint_locus_entities(c).contains(point));
        }
        Constraint::FixedY { point, .. } => {
            assert(constraint_locus_entities(c).contains(point));
        }
        Constraint::SameX { a, .. } => {
            assert(constraint_locus_entities(c).contains(a));
        }
        Constraint::SameY { a, .. } => {
            assert(constraint_locus_entities(c).contains(a));
        }
        Constraint::PointOnLine { point, .. } => {
            assert(constraint_locus_entities(c).contains(point));
        }
        Constraint::EqualLengthSq { a1, .. } => {
            assert(constraint_locus_entities(c).contains(a1));
        }
        Constraint::Midpoint { mid, .. } => {
            assert(constraint_locus_entities(c).contains(mid));
        }
        Constraint::Perpendicular { a1, .. } => {
            assert(constraint_locus_entities(c).contains(a1));
        }
        Constraint::Parallel { a1, .. } => {
            assert(constraint_locus_entities(c).contains(a1));
        }
        Constraint::Collinear { a, .. } => {
            assert(constraint_locus_entities(c).contains(a));
        }
        Constraint::PointOnCircle { point, .. } => {
            assert(constraint_locus_entities(c).contains(point));
        }
        Constraint::Symmetric { point, .. } => {
            assert(constraint_locus_entities(c).contains(point));
        }
        Constraint::FixedPoint { point, .. } => {
            assert(constraint_locus_entities(c).contains(point));
        }
        Constraint::Ratio { a1, .. } => {
            assert(constraint_locus_entities(c).contains(a1));
        }
        Constraint::Tangent { .. } => {}
        Constraint::CircleTangent { .. } => {}
        Constraint::Angle { .. } => {}
        Constraint::NotCoincident { .. } => {}
        Constraint::NormalToCircle { line_a, .. } => {
            assert(constraint_locus_entities(c).contains(line_a));
        }
        Constraint::PointOnEllipse { .. } => {}
        Constraint::PointOnArc { .. } => {}
    }
}

/// The entities for which constraint_to_locus can return a non-trivial locus.
/// For most constraints, this is all entities. For PointOnLine, only `point`.
/// For EqualLengthSq, only a1 and a2.
pub open spec fn constraint_locus_entities<T: OrderedField>(c: Constraint<T>) -> Set<EntityId> {
    match c {
        Constraint::Coincident { a, b } => set![a, b],
        Constraint::DistanceSq { a, b, .. } => set![a, b],
        Constraint::FixedX { point, .. } => set![point],
        Constraint::FixedY { point, .. } => set![point],
        Constraint::SameX { a, b } => set![a, b],
        Constraint::SameY { a, b } => set![a, b],
        Constraint::PointOnLine { point, .. } => set![point],
        Constraint::EqualLengthSq { a1, a2, .. } => set![a1, a2],
        Constraint::Midpoint { mid, a, b } => set![mid, a, b],
        Constraint::Perpendicular { a1, a2, .. } => set![a1, a2],
        Constraint::Parallel { a1, a2, .. } => set![a1, a2],
        Constraint::Collinear { a, b, c } => set![a, b, c],
        Constraint::PointOnCircle { point, .. } => set![point],
        Constraint::Symmetric { point, .. } => set![point],
        Constraint::FixedPoint { point, .. } => set![point],
        Constraint::Ratio { a1, a2, .. } => set![a1, a2],
        Constraint::Tangent { .. } => set![],
        Constraint::CircleTangent { .. } => set![],
        Constraint::Angle { .. } => set![],
        Constraint::NotCoincident { .. } => set![],
        Constraint::NormalToCircle { line_a, .. } => set![line_a],
        Constraint::PointOnEllipse { .. } => set![],
        Constraint::PointOnArc { .. } => set![],
    }
}

} // verus!
