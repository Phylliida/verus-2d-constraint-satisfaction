use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_geometry::point2::Point2;

verus! {

///  Unique identifier for geometric entities.
pub type EntityId = nat;

///  A free point that the solver needs to determine.
pub struct FreePoint {
    pub id: EntityId,
}

///  A fixed point with known coordinates.
pub struct FixedPoint<T: Ring> {
    pub id: EntityId,
    pub position: Point2<T>,
}

///  Resolved coordinates for a point.
pub type ResolvedPoints<T> = Map<EntityId, Point2<T>>;

///  Check if an entity is resolved.
pub open spec fn is_resolved<T: Ring>(
    resolved: ResolvedPoints<T>, id: EntityId,
) -> bool {
    resolved.dom().contains(id)
}

///  Get the resolved position of an entity.
pub open spec fn get_position<T: Ring>(
    resolved: ResolvedPoints<T>, id: EntityId,
) -> Point2<T> {
    resolved[id]
}

} //  verus!
