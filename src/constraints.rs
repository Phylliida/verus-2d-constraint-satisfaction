use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::line2::*;
use verus_geometry::orient2d::det2d;
use verus_linalg::vec2::ops::dot;
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
                let da = sub2(resolved[a2], resolved[a1]);
                let db = sub2(resolved[b2], resolved[b1]);
                dot(da, db).eqv(T::zero())
            }
        }

        Constraint::Parallel { a1, a2, b1, b2 } => {
            resolved.dom().contains(a1) && resolved.dom().contains(a2) &&
            resolved.dom().contains(b1) && resolved.dom().contains(b2) && {
                let da = sub2(resolved[a2], resolved[a1]);
                let db = sub2(resolved[b2], resolved[b1]);
                det2d(da, db).eqv(T::zero())
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
            a1 != a2 && b1 != b2,
        Constraint::Parallel { a1, a2, b1, b2 } =>
            a1 != a2 && b1 != b2,
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
    }
}

} // verus!
