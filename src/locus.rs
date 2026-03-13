use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_algebra::lemmas::field_lemmas::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::voronoi::sq_dist_2d;
use verus_geometry::orient2d::{orient2d, lemma_orient2d_cyclic, lemma_orient2d_swap_bc};
use crate::entities::*;
use crate::constraints::*;

verus! {

// ===========================================================================
//  Geometric loci
// ===========================================================================

/// A geometric locus in 2D: the set of points satisfying a single constraint
/// when all other referenced entities are already resolved.
pub enum Locus2d<T: OrderedField> {
    /// No constraint on the point (e.g., unconstrained entity).
    FullPlane,

    /// Point must lie on a line.
    OnLine(Line2<T>),

    /// Point must lie on a circle.
    OnCircle(Circle2<T>),

    /// Point is fully determined.
    AtPoint(Point2<T>),
}

/// A point satisfies a locus.
pub open spec fn point_satisfies_locus<T: OrderedField>(
    locus: Locus2d<T>, p: Point2<T>,
) -> bool {
    match locus {
        Locus2d::FullPlane => true,
        Locus2d::OnLine(line) => point_on_line2(line, p),
        Locus2d::OnCircle(circle) => point_on_circle2(circle, p),
        Locus2d::AtPoint(q) => p.eqv(q),
    }
}

/// Whether a locus actually constrains the point (i.e., is not FullPlane).
pub open spec fn locus_is_nontrivial<T: OrderedField>(locus: Locus2d<T>) -> bool {
    !matches!(locus, Locus2d::FullPlane)
}

// ===========================================================================
//  Constraint → Locus mapping
// ===========================================================================

/// Convert a constraint into the locus it imposes on a target entity,
/// given already-resolved positions for all other referenced entities.
pub open spec fn constraint_to_locus<T: OrderedField>(
    c: Constraint<T>,
    resolved: ResolvedPoints<T>,
    target: EntityId,
) -> Locus2d<T> {
    match c {
        Constraint::Coincident { a, b } => {
            if target == a && resolved.dom().contains(b) {
                Locus2d::AtPoint(resolved[b])
            } else if target == b && resolved.dom().contains(a) {
                Locus2d::AtPoint(resolved[a])
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::DistanceSq { a, b, dist_sq } => {
            if target == a && resolved.dom().contains(b) {
                Locus2d::OnCircle(circle2_from_center_radius_sq(resolved[b], dist_sq))
            } else if target == b && resolved.dom().contains(a) {
                Locus2d::OnCircle(circle2_from_center_radius_sq(resolved[a], dist_sq))
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::FixedX { point, x } => {
            if target == point {
                // x = constant → vertical line: 1*x + 0*y + (-x_val) = 0
                Locus2d::OnLine(Line2 { a: T::one(), b: T::zero(), c: x.neg() })
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::FixedY { point, y } => {
            if target == point {
                // y = constant → horizontal line: 0*x + 1*y + (-y_val) = 0
                Locus2d::OnLine(Line2 { a: T::zero(), b: T::one(), c: y.neg() })
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::SameX { a, b } => {
            if target == a && resolved.dom().contains(b) {
                // x = b.x → vertical line through b.x
                Locus2d::OnLine(Line2 { a: T::one(), b: T::zero(), c: resolved[b].x.neg() })
            } else if target == b && resolved.dom().contains(a) {
                Locus2d::OnLine(Line2 { a: T::one(), b: T::zero(), c: resolved[a].x.neg() })
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::SameY { a, b } => {
            if target == a && resolved.dom().contains(b) {
                Locus2d::OnLine(Line2 { a: T::zero(), b: T::one(), c: resolved[b].y.neg() })
            } else if target == b && resolved.dom().contains(a) {
                Locus2d::OnLine(Line2 { a: T::zero(), b: T::one(), c: resolved[a].y.neg() })
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::PointOnLine { point, line_a, line_b } => {
            if target == point && resolved.dom().contains(line_a) && resolved.dom().contains(line_b) {
                Locus2d::OnLine(line2_from_points(resolved[line_a], resolved[line_b]))
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            // |target - other|² = |b1 - b2|² when target is a1 or a2 and others resolved
            if target == a1 && resolved.dom().contains(a2) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                let r2 = sq_dist_2d(resolved[b1], resolved[b2]);
                Locus2d::OnCircle(circle2_from_center_radius_sq(resolved[a2], r2))
            } else if target == a2 && resolved.dom().contains(a1) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                let r2 = sq_dist_2d(resolved[b1], resolved[b2]);
                Locus2d::OnCircle(circle2_from_center_radius_sq(resolved[a1], r2))
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::Midpoint { mid, a, b } => {
            if target == mid && resolved.dom().contains(a) && resolved.dom().contains(b) {
                // midpoint is fully determined
                let two = T::one().add(T::one());
                let mx = resolved[a].x.add(resolved[b].x).div(two);
                let my = resolved[a].y.add(resolved[b].y).div(two);
                Locus2d::AtPoint(Point2 { x: mx, y: my })
            } else if target == a && resolved.dom().contains(mid) && resolved.dom().contains(b) {
                // a = 2*mid - b
                let two = T::one().add(T::one());
                let ax = two.mul(resolved[mid].x).sub(resolved[b].x);
                let ay = two.mul(resolved[mid].y).sub(resolved[b].y);
                Locus2d::AtPoint(Point2 { x: ax, y: ay })
            } else if target == b && resolved.dom().contains(mid) && resolved.dom().contains(a) {
                let two = T::one().add(T::one());
                let bx = two.mul(resolved[mid].x).sub(resolved[a].x);
                let by = two.mul(resolved[mid].y).sub(resolved[a].y);
                Locus2d::AtPoint(Point2 { x: bx, y: by })
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            // Perpendicular: line through other with normal = db = sub2(b2, b1).
            // Uses db.x * other.x + db.y * other.y order to match constraint_satisfied.
            if target == a1 && resolved.dom().contains(a2) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                let db = sub2(resolved[b2], resolved[b1]);
                let c = db.x.mul(resolved[a2].x).add(db.y.mul(resolved[a2].y)).neg();
                Locus2d::OnLine(Line2 { a: db.x, b: db.y, c })
            } else if target == a2 && resolved.dom().contains(a1) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                let db = sub2(resolved[b2], resolved[b1]);
                let c = db.x.mul(resolved[a1].x).add(db.y.mul(resolved[a1].y)).neg();
                Locus2d::OnLine(Line2 { a: db.x, b: db.y, c })
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::Parallel { a1, a2, b1, b2 } => {
            // Parallel: line through other with direction = db = sub2(b2, b1).
            // Normal = (db.y, -db.x). Uses db.y * other.x + (-db.x) * other.y order.
            if target == a1 && resolved.dom().contains(a2) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                let db = sub2(resolved[b2], resolved[b1]);
                let c = db.y.mul(resolved[a2].x).add(db.x.neg().mul(resolved[a2].y)).neg();
                Locus2d::OnLine(Line2 { a: db.y, b: db.x.neg(), c })
            } else if target == a2 && resolved.dom().contains(a1) && resolved.dom().contains(b1) && resolved.dom().contains(b2) {
                let db = sub2(resolved[b2], resolved[b1]);
                let c = db.y.mul(resolved[a1].x).add(db.x.neg().mul(resolved[a1].y)).neg();
                Locus2d::OnLine(Line2 { a: db.y, b: db.x.neg(), c })
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::Collinear { a, b, c } => {
            // Any of the three can be the target; the other two define the line.
            if target == c && resolved.dom().contains(a) && resolved.dom().contains(b) {
                Locus2d::OnLine(line2_from_points(resolved[a], resolved[b]))
            } else if target == a && resolved.dom().contains(b) && resolved.dom().contains(c) {
                Locus2d::OnLine(line2_from_points(resolved[b], resolved[c]))
            } else if target == b && resolved.dom().contains(a) && resolved.dom().contains(c) {
                Locus2d::OnLine(line2_from_points(resolved[a], resolved[c]))
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::PointOnCircle { point, center, radius_point } => {
            if target == point && resolved.dom().contains(center) && resolved.dom().contains(radius_point) {
                let r2 = sq_dist_2d(resolved[radius_point], resolved[center]);
                Locus2d::OnCircle(circle2_from_center_radius_sq(resolved[center], r2))
            } else {
                Locus2d::FullPlane
            }
        }

        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            if target == point && resolved.dom().contains(original) && resolved.dom().contains(axis_a) && resolved.dom().contains(axis_b) {
                Locus2d::AtPoint(reflect_point_across_line(
                    resolved[original], resolved[axis_a], resolved[axis_b],
                ))
            } else {
                Locus2d::FullPlane
            }
        }
    }
}

// ===========================================================================
//  Helper lemmas for locus soundness
// ===========================================================================

/// point_on_line2(Line2{1, 0, -x_val}, p) implies p.x ≡ x_val.
proof fn lemma_vertical_line_extract_x<T: OrderedField>(p: Point2<T>, x_val: T)
    requires
        point_on_line2(Line2 { a: T::one(), b: T::zero(), c: x_val.neg() }, p),
    ensures
        p.x.eqv(x_val),
{
    // Expands to: 1*p.x + 0*p.y + (-x_val) ≡ 0
    let line = Line2 { a: T::one(), b: T::zero(), c: x_val.neg() };
    // 1*p.x ≡ p.x
    lemma_mul_one_left::<T>(p.x);
    // 0*p.y ≡ 0
    lemma_mul_zero_left::<T>(p.y);
    // So: p.x + 0 + (-x_val) ≡ 0
    // By congruence: 1*p.x + 0*p.y ≡ p.x + 0
    lemma_add_congruence::<T>(
        T::one().mul(p.x), p.x,
        T::zero().mul(p.y), T::zero(),
    );
    // p.x + 0 ≡ p.x  (add zero right = comm + add zero left)
    T::axiom_add_commutative(p.x, T::zero());
    lemma_add_zero_left::<T>(p.x);
    T::axiom_eqv_transitive(p.x.add(T::zero()), T::zero().add(p.x), p.x);
    // Chain: 1*p.x + 0*p.y ≡ p.x + 0 ≡ p.x
    T::axiom_eqv_transitive(T::one().mul(p.x).add(T::zero().mul(p.y)), p.x.add(T::zero()), p.x);
    // So: (1*p.x + 0*p.y) + (-x_val) ≡ p.x + (-x_val)
    T::axiom_eqv_reflexive(x_val.neg());
    lemma_add_congruence::<T>(
        T::one().mul(p.x).add(T::zero().mul(p.y)), p.x,
        line.c, x_val.neg(),
    );
    // point_on_line2 gives: line.a*px + line.b*py + line.c ≡ 0
    // congruence above gives: line.a*px + line.b*py + line.c ≡ px + (-xval)
    // (since line.a=1, line.b=0, line.c=-xval are structurally equal)
    // Reverse direction: px + (-xval) ≡ LHS
    T::axiom_eqv_symmetric(
        T::one().mul(p.x).add(T::zero().mul(p.y)).add(line.c),
        p.x.add(x_val.neg()),
    );
    // Chain: px + (-xval) ≡ LHS ≡ 0
    T::axiom_eqv_transitive(p.x.add(x_val.neg()), T::one().mul(p.x).add(T::zero().mul(p.y)).add(line.c), T::zero());
    // p.x + (-x_val) ≡ 0 → x_val ≡ -(p.x)... no, use neg_unique:
    // p.x + (-x_val) ≡ 0 → (-x_val) ≡ -(p.x)
    lemma_neg_unique::<T>(p.x, x_val.neg());
    // x_val.neg() ≡ p.x.neg()
    // So x_val ≡ p.x by double negation:
    // -(-(p.x)) ≡ p.x
    lemma_neg_involution::<T>(p.x);
    // -(-(x_val)) ≡ x_val
    lemma_neg_involution::<T>(x_val);
    // x_val.neg() ≡ p.x.neg() → x_val.neg().neg() ≡ p.x.neg().neg() (congruence)
    T::axiom_neg_congruence(x_val.neg(), p.x.neg());
    // x_val.neg().neg() ≡ x_val  AND  p.x.neg().neg() ≡ p.x
    // Chain: x_val ≡ x_val.neg().neg() ≡ p.x.neg().neg() ≡ p.x
    T::axiom_eqv_symmetric(x_val.neg().neg(), x_val);
    T::axiom_eqv_transitive(x_val, x_val.neg().neg(), p.x.neg().neg());
    T::axiom_eqv_transitive(x_val, p.x.neg().neg(), p.x);
    T::axiom_eqv_symmetric(x_val, p.x);
    // p.x ≡ x_val ✓
}

/// point_on_line2(Line2{0, 1, -y_val}, p) implies p.y ≡ y_val.
proof fn lemma_horizontal_line_extract_y<T: OrderedField>(p: Point2<T>, y_val: T)
    requires
        point_on_line2(Line2 { a: T::zero(), b: T::one(), c: y_val.neg() }, p),
    ensures
        p.y.eqv(y_val),
{
    let line = Line2 { a: T::zero(), b: T::one(), c: y_val.neg() };
    // 0*p.x ≡ 0
    lemma_mul_zero_left::<T>(p.x);
    // 1*p.y ≡ p.y
    lemma_mul_one_left::<T>(p.y);
    // 0*p.x + 1*p.y ≡ 0 + p.y ≡ p.y
    lemma_add_congruence::<T>(
        T::zero().mul(p.x), T::zero(),
        T::one().mul(p.y), p.y,
    );
    lemma_add_zero_left::<T>(p.y);
    T::axiom_eqv_transitive(T::zero().mul(p.x).add(T::one().mul(p.y)), T::zero().add(p.y), p.y);
    // (0*p.x + 1*p.y) + (-y_val) ≡ p.y + (-y_val)
    T::axiom_eqv_reflexive(y_val.neg());
    lemma_add_congruence::<T>(
        T::zero().mul(p.x).add(T::one().mul(p.y)), p.y,
        line.c, y_val.neg(),
    );
    // LHS ≡ 0 (from point_on_line2), and LHS ≡ p.y + (-y_val)
    T::axiom_eqv_symmetric(
        line.a.mul(p.x).add(line.b.mul(p.y)).add(line.c),
        p.y.add(y_val.neg()),
    );
    T::axiom_eqv_transitive(p.y.add(y_val.neg()), line.a.mul(p.x).add(line.b.mul(p.y)).add(line.c), T::zero());
    // p.y + (-y_val) ≡ 0 → p.y ≡ y_val
    lemma_neg_unique::<T>(p.y, y_val.neg());
    lemma_neg_involution::<T>(p.y);
    lemma_neg_involution::<T>(y_val);
    T::axiom_neg_congruence(y_val.neg(), p.y.neg());
    T::axiom_eqv_symmetric(y_val.neg().neg(), y_val);
    T::axiom_eqv_transitive(y_val, y_val.neg().neg(), p.y.neg().neg());
    T::axiom_eqv_transitive(y_val, p.y.neg().neg(), p.y);
    T::axiom_eqv_symmetric(y_val, p.y);
}

/// Midpoint: if p ≡ Point2{(ax+bx)/2, (ay+by)/2}, then p.x*2 ≡ ax+bx and p.y*2 ≡ ay+by.
proof fn lemma_midpoint_div_satisfies<T: OrderedField>(
    ax: T, bx: T, ay: T, by_: T, p: Point2<T>,
)
    requires ({
        let two = T::one().add(T::one());
        let mx = ax.add(bx).div(two);
        let my = ay.add(by_).div(two);
        p.eqv(Point2 { x: mx, y: my })
    }),
    ensures ({
        let two = T::one().add(T::one());
        p.x.mul(two).eqv(ax.add(bx)) && p.y.mul(two).eqv(ay.add(by_))
    }),
{
    let two = T::one().add(T::one());
    let mx = ax.add(bx).div(two);
    let my = ay.add(by_).div(two);

    // p.eqv(Point2{mx, my}) means p.x.eqv(mx) && p.y.eqv(my)
    // p.x ≡ mx = (ax+bx)/two
    // Need: p.x * two ≡ ax+bx

    // two ≢ 0 (needed for div_mul_cancel)
    verus_algebra::convex::lemma_two_nonzero::<T>();

    // By congruence: p.x * two ≡ mx * two = ((ax+bx)/two) * two
    T::axiom_mul_congruence_left(p.x, mx, two);
    // mx * two = ((ax+bx)/two) * two ≡ ax+bx by div_mul_cancel
    lemma_div_mul_cancel::<T>(ax.add(bx), two);
    // Chain
    T::axiom_eqv_transitive(p.x.mul(two), mx.mul(two), ax.add(bx));

    // Same for y
    T::axiom_mul_congruence_left(p.y, my, two);
    lemma_div_mul_cancel::<T>(ay.add(by_), two);
    T::axiom_eqv_transitive(p.y.mul(two), my.mul(two), ay.add(by_));
}

/// Midpoint target=a: if p ≡ Point2{2*mid.x - b.x, 2*mid.y - b.y},
/// then mid.x*2 ≡ p.x + b.x and mid.y*2 ≡ p.y + b.y.
proof fn lemma_midpoint_a_satisfies<T: OrderedField>(
    mid_x: T, mid_y: T, bx: T, by_: T, p: Point2<T>,
)
    requires ({
        let two = T::one().add(T::one());
        let ax = two.mul(mid_x).sub(bx);
        let ay = two.mul(mid_y).sub(by_);
        p.eqv(Point2 { x: ax, y: ay })
    }),
    ensures ({
        let two = T::one().add(T::one());
        // mid*2 ≡ p + b → equivalent to the constraint check
        mid_x.mul(two).eqv(p.x.add(bx)) && mid_y.mul(two).eqv(p.y.add(by_))
    }),
{
    let two = T::one().add(T::one());
    let ax = two.mul(mid_x).sub(bx);
    let ay = two.mul(mid_y).sub(by_);

    // p.x ≡ ax = 2*mid_x - bx
    // p.x + bx ≡ (2*mid_x - bx) + bx ≡ 2*mid_x
    // (2*mid_x - bx) + bx ≡ 2*mid_x by sub + add cancel
    T::axiom_sub_is_add_neg(two.mul(mid_x), bx);
    // ax ≡ 2*mid_x + (-bx)
    T::axiom_add_associative(two.mul(mid_x), bx.neg(), bx);
    T::axiom_eqv_symmetric(
        two.mul(mid_x).add(bx.neg()).add(bx),
        two.mul(mid_x).add(bx.neg().add(bx)),
    );
    lemma_add_inverse_left::<T>(bx);
    lemma_add_congruence_right::<T>(two.mul(mid_x), bx.neg().add(bx), T::zero());
    T::axiom_add_commutative(two.mul(mid_x), T::zero());
    lemma_add_zero_left::<T>(two.mul(mid_x));
    T::axiom_eqv_transitive(two.mul(mid_x).add(T::zero()), T::zero().add(two.mul(mid_x)), two.mul(mid_x));
    T::axiom_eqv_transitive(two.mul(mid_x).add(bx.neg().add(bx)), two.mul(mid_x).add(T::zero()), two.mul(mid_x));
    T::axiom_eqv_transitive(two.mul(mid_x).add(bx.neg()).add(bx), two.mul(mid_x).add(bx.neg().add(bx)), two.mul(mid_x));
    // ax + bx ≡ (2*mid_x + (-bx)) + bx ≡ 2*mid_x
    T::axiom_eqv_reflexive(bx);
    lemma_add_congruence::<T>(ax, two.mul(mid_x).add(bx.neg()), bx, bx);
    T::axiom_eqv_transitive(ax.add(bx), two.mul(mid_x).add(bx.neg()).add(bx), two.mul(mid_x));

    // p.x + bx ≡ ax + bx  (from p.x ≡ ax)
    T::axiom_add_congruence_left(p.x, ax, bx);
    T::axiom_eqv_transitive(p.x.add(bx), ax.add(bx), two.mul(mid_x));
    // mid_x * two ≡ two * mid_x (comm)
    T::axiom_mul_commutative(mid_x, two);
    T::axiom_eqv_symmetric(p.x.add(bx), two.mul(mid_x));
    T::axiom_eqv_transitive(mid_x.mul(two), two.mul(mid_x), p.x.add(bx));

    // Same for y
    T::axiom_sub_is_add_neg(two.mul(mid_y), by_);
    T::axiom_add_associative(two.mul(mid_y), by_.neg(), by_);
    T::axiom_eqv_symmetric(
        two.mul(mid_y).add(by_.neg()).add(by_),
        two.mul(mid_y).add(by_.neg().add(by_)),
    );
    lemma_add_inverse_left::<T>(by_);
    lemma_add_congruence_right::<T>(two.mul(mid_y), by_.neg().add(by_), T::zero());
    T::axiom_add_commutative(two.mul(mid_y), T::zero());
    lemma_add_zero_left::<T>(two.mul(mid_y));
    T::axiom_eqv_transitive(two.mul(mid_y).add(T::zero()), T::zero().add(two.mul(mid_y)), two.mul(mid_y));
    T::axiom_eqv_transitive(two.mul(mid_y).add(by_.neg().add(by_)), two.mul(mid_y).add(T::zero()), two.mul(mid_y));
    T::axiom_eqv_transitive(two.mul(mid_y).add(by_.neg()).add(by_), two.mul(mid_y).add(by_.neg().add(by_)), two.mul(mid_y));
    T::axiom_eqv_reflexive(by_);
    lemma_add_congruence::<T>(ay, two.mul(mid_y).add(by_.neg()), by_, by_);
    T::axiom_eqv_transitive(ay.add(by_), two.mul(mid_y).add(by_.neg()).add(by_), two.mul(mid_y));
    T::axiom_add_congruence_left(p.y, ay, by_);
    T::axiom_eqv_transitive(p.y.add(by_), ay.add(by_), two.mul(mid_y));
    T::axiom_mul_commutative(mid_y, two);
    T::axiom_eqv_symmetric(p.y.add(by_), two.mul(mid_y));
    T::axiom_eqv_transitive(mid_y.mul(two), two.mul(mid_y), p.y.add(by_));
}

// ===========================================================================
//  Collinear locus soundness helpers
// ===========================================================================

/// If x.neg() ≡ 0, then x ≡ 0.
proof fn lemma_neg_eqv_zero_implies_zero<T: Ring>(x: T)
    requires x.neg().eqv(T::zero()),
    ensures x.eqv(T::zero()),
{
    T::axiom_neg_congruence(x.neg(), T::zero());
    // x.neg().neg() ≡ T::zero().neg()
    verus_algebra::quadratic::lemma_neg_zero::<T>();
    // T::zero().neg() ≡ T::zero()
    lemma_neg_involution::<T>(x);
    // x.neg().neg() ≡ x
    T::axiom_eqv_symmetric(x.neg().neg(), x);
    // x ≡ x.neg().neg()
    T::axiom_eqv_transitive(x, x.neg().neg(), T::zero().neg());
    T::axiom_eqv_transitive(x, T::zero().neg(), T::zero());
}

/// Collinear soundness for target=a: point_on_line2(line_from_points(b,c), p) implies
/// point_on_line2(line_from_points(p, b), c).
/// Uses orient2d cyclic permutation.
proof fn lemma_collinear_cyclic<T: OrderedField>(
    p: Point2<T>, b: Point2<T>, c: Point2<T>,
)
    requires
        point_on_line2(line2_from_points(b, c), p),
    ensures
        point_on_line2(line2_from_points(p, b), c),
{
    // From locus: line2_eval(line_from_points(b,c), p) ≡ 0
    // By orient2d equivalence: orient2d(b,c,p) ≡ line2_eval(line_from_points(b,c), p)
    lemma_line2_orient2d_equivalence(b, c, p);
    // orient2d(b,c,p) ≡ 0
    T::axiom_eqv_symmetric(line2_eval(line2_from_points(b, c), p), orient2d(b, c, p));
    T::axiom_eqv_transitive(orient2d(b, c, p), line2_eval(line2_from_points(b, c), p), T::zero());

    // By cyclic: orient2d(p,b,c) ≡ orient2d(b,c,p)
    lemma_orient2d_cyclic(p, b, c);
    // orient2d(p,b,c) ≡ orient2d(b,c,p) ≡ 0
    T::axiom_eqv_transitive(orient2d(p, b, c), orient2d(b, c, p), T::zero());

    // By orient2d equivalence (reverse): line2_eval(line_from_points(p,b), c) ≡ orient2d(p,b,c)
    lemma_line2_orient2d_equivalence(p, b, c);
    // line2_eval ≡ orient2d(p,b,c) ≡ 0
    T::axiom_eqv_transitive(
        line2_eval(line2_from_points(p, b), c),
        orient2d(p, b, c),
        T::zero(),
    );
}

/// Collinear soundness for target=b: point_on_line2(line_from_points(a,c), p) implies
/// point_on_line2(line_from_points(a, p), c).
/// Uses orient2d swap_bc.
proof fn lemma_collinear_swap<T: OrderedField>(
    a: Point2<T>, p: Point2<T>, c: Point2<T>,
)
    requires
        point_on_line2(line2_from_points(a, c), p),
    ensures
        point_on_line2(line2_from_points(a, p), c),
{
    // From locus: line2_eval(line_from_points(a,c), p) ≡ 0
    lemma_line2_orient2d_equivalence(a, c, p);
    T::axiom_eqv_symmetric(line2_eval(line2_from_points(a, c), p), orient2d(a, c, p));
    T::axiom_eqv_transitive(orient2d(a, c, p), line2_eval(line2_from_points(a, c), p), T::zero());
    // orient2d(a,c,p) ≡ 0

    // By swap_bc: orient2d(a,c,p) ≡ orient2d(a,p,c).neg()
    lemma_orient2d_swap_bc(a, p, c);
    T::axiom_eqv_symmetric(orient2d(a, c, p), orient2d(a, p, c).neg());
    T::axiom_eqv_transitive(orient2d(a, p, c).neg(), orient2d(a, c, p), T::zero());
    // orient2d(a,p,c).neg() ≡ 0

    // By helper: orient2d(a,p,c) ≡ 0
    lemma_neg_eqv_zero_implies_zero(orient2d(a, p, c));

    // Orient2d equivalence for the target line
    lemma_line2_orient2d_equivalence(a, p, c);
    T::axiom_eqv_transitive(
        line2_eval(line2_from_points(a, p), c),
        orient2d(a, p, c),
        T::zero(),
    );
}

// ===========================================================================
//  Perpendicular/Parallel locus soundness helpers
// ===========================================================================

/// Swap lemma for point_on_line2 with computed c:
/// if a*px + b*py + (-(a*qx + b*qy)) ≡ 0, then a*qx + b*qy + (-(a*px + b*py)) ≡ 0.
/// This handles the "reversed target" case for Perpendicular/Parallel constraints.
proof fn lemma_point_on_line2_swap<T: OrderedField>(
    a: T, b: T, px: T, py: T, qx: T, qy: T,
)
    requires
        point_on_line2(
            Line2 { a, b, c: a.mul(qx).add(b.mul(qy)).neg() },
            Point2 { x: px, y: py },
        ),
    ensures
        point_on_line2(
            Line2 { a, b, c: a.mul(px).add(b.mul(py)).neg() },
            Point2 { x: qx, y: qy },
        ),
{
    // Let S1 = a*px + b*py, S2 = a*qx + b*qy
    // Given: S1 + (-S2) ≡ 0
    // Need:  S2 + (-S1) ≡ 0
    let s1 = a.mul(px).add(b.mul(py));
    let s2 = a.mul(qx).add(b.mul(qy));

    // Step 1: neg both sides: -(S1 + (-S2)) ≡ -0 ≡ 0
    T::axiom_neg_congruence(s1.add(s2.neg()), T::zero());
    lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(s1.add(s2.neg()).neg(), T::zero().neg(), T::zero());

    // Step 2: -(S1 + (-S2)) ≡ (-S1) + S2  [by neg_add + neg_involution]
    lemma_neg_add::<T>(s1, s2.neg());
    lemma_neg_involution::<T>(s2);
    lemma_add_congruence_right::<T>(s1.neg(), s2.neg().neg(), s2);
    T::axiom_eqv_transitive(
        s1.add(s2.neg()).neg(),
        s1.neg().add(s2.neg().neg()),
        s1.neg().add(s2),
    );

    // Step 3: (-S1) + S2 ≡ 0  (transitive from steps 1 + 2)
    T::axiom_eqv_symmetric(s1.add(s2.neg()).neg(), s1.neg().add(s2));
    T::axiom_eqv_transitive(s1.neg().add(s2), s1.add(s2.neg()).neg(), T::zero());

    // Step 4: S2 + (-S1) ≡ (-S1) + S2 ≡ 0  [by commutativity]
    T::axiom_add_commutative(s2, s1.neg());
    T::axiom_eqv_transitive(s2.add(s1.neg()), s1.neg().add(s2), T::zero());
}

// ===========================================================================
//  Soundness lemmas
// ===========================================================================

/// Frame lemma: inserting an entity not referenced by the constraint
/// preserves constraint satisfaction.
pub proof fn lemma_constraint_frame<T: OrderedField>(
    c: Constraint<T>,
    resolved: ResolvedPoints<T>,
    key: EntityId,
    p: Point2<T>,
)
    requires
        !constraint_entities(c).contains(key),
        constraint_satisfied(c, resolved),
    ensures
        constraint_satisfied(c, resolved.insert(key, p)),
{
    // For every entity e in constraint_entities(c), key != e,
    // so resolved.insert(key, p)[e] == resolved[e].
    // All dom checks pass since resolved.dom() ⊆ resolved.insert(key,p).dom().
    // The predicate evaluates identically.
    match c {
        Constraint::Coincident { a, b } => {
            assert(key != a && key != b);
            assert(resolved.insert(key, p)[a] == resolved[a]);
            assert(resolved.insert(key, p)[b] == resolved[b]);
        }
        Constraint::DistanceSq { a, b, .. } => {
            assert(key != a && key != b);
            assert(resolved.insert(key, p)[a] == resolved[a]);
            assert(resolved.insert(key, p)[b] == resolved[b]);
        }
        Constraint::FixedX { point, .. } => {
            assert(key != point);
            assert(resolved.insert(key, p)[point] == resolved[point]);
        }
        Constraint::FixedY { point, .. } => {
            assert(key != point);
            assert(resolved.insert(key, p)[point] == resolved[point]);
        }
        Constraint::SameX { a, b } => {
            assert(key != a && key != b);
            assert(resolved.insert(key, p)[a] == resolved[a]);
            assert(resolved.insert(key, p)[b] == resolved[b]);
        }
        Constraint::SameY { a, b } => {
            assert(key != a && key != b);
            assert(resolved.insert(key, p)[a] == resolved[a]);
            assert(resolved.insert(key, p)[b] == resolved[b]);
        }
        Constraint::PointOnLine { point, line_a, line_b } => {
            assert(key != point && key != line_a && key != line_b);
            assert(resolved.insert(key, p)[point] == resolved[point]);
            assert(resolved.insert(key, p)[line_a] == resolved[line_a]);
            assert(resolved.insert(key, p)[line_b] == resolved[line_b]);
        }
        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            assert(key != a1 && key != a2 && key != b1 && key != b2);
            assert(resolved.insert(key, p)[a1] == resolved[a1]);
            assert(resolved.insert(key, p)[a2] == resolved[a2]);
            assert(resolved.insert(key, p)[b1] == resolved[b1]);
            assert(resolved.insert(key, p)[b2] == resolved[b2]);
        }
        Constraint::Midpoint { mid, a, b } => {
            assert(key != mid && key != a && key != b);
            assert(resolved.insert(key, p)[mid] == resolved[mid]);
            assert(resolved.insert(key, p)[a] == resolved[a]);
            assert(resolved.insert(key, p)[b] == resolved[b]);
        }
        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            assert(key != a1 && key != a2 && key != b1 && key != b2);
            assert(resolved.insert(key, p)[a1] == resolved[a1]);
            assert(resolved.insert(key, p)[a2] == resolved[a2]);
            assert(resolved.insert(key, p)[b1] == resolved[b1]);
            assert(resolved.insert(key, p)[b2] == resolved[b2]);
        }
        Constraint::Parallel { a1, a2, b1, b2 } => {
            assert(key != a1 && key != a2 && key != b1 && key != b2);
            assert(resolved.insert(key, p)[a1] == resolved[a1]);
            assert(resolved.insert(key, p)[a2] == resolved[a2]);
            assert(resolved.insert(key, p)[b1] == resolved[b1]);
            assert(resolved.insert(key, p)[b2] == resolved[b2]);
        }
        Constraint::Collinear { a, b, c } => {
            assert(key != a && key != b && key != c);
            assert(resolved.insert(key, p)[a] == resolved[a]);
            assert(resolved.insert(key, p)[b] == resolved[b]);
            assert(resolved.insert(key, p)[c] == resolved[c]);
        }
        Constraint::PointOnCircle { point, center, radius_point } => {
            assert(key != point && key != center && key != radius_point);
            assert(resolved.insert(key, p)[point] == resolved[point]);
            assert(resolved.insert(key, p)[center] == resolved[center]);
            assert(resolved.insert(key, p)[radius_point] == resolved[radius_point]);
        }
        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            assert(key != point && key != original && key != axis_a && key != axis_b);
            assert(resolved.insert(key, p)[point] == resolved[point]);
            assert(resolved.insert(key, p)[original] == resolved[original]);
            assert(resolved.insert(key, p)[axis_a] == resolved[axis_a]);
            assert(resolved.insert(key, p)[axis_b] == resolved[axis_b]);
        }
    }
}

/// Soundness: if a non-trivial locus is satisfied, the original constraint is satisfied.
/// When the locus is FullPlane (trivial), this lemma provides no guarantee —
/// the constraint must be verified by other means.
pub proof fn lemma_locus_sound<T: OrderedField>(
    c: Constraint<T>,
    resolved: ResolvedPoints<T>,
    target: EntityId,
    p: Point2<T>,
)
    requires
        point_satisfies_locus(constraint_to_locus(c, resolved, target), p),
        constraint_entities(c).contains(target),
        constraint_entities(c).remove(target).subset_of(resolved.dom()),
        !resolved.dom().contains(target),
        locus_is_nontrivial(constraint_to_locus(c, resolved, target)),
    ensures
        constraint_satisfied(c, resolved.insert(target, p)),
{
    let r = resolved.insert(target, p);

    match c {
        Constraint::Coincident { a, b } => {
            // target is a or b
            if target == a {
                // dom checks
                assert(r.dom().contains(a));
                if a == b {
                    // r[a] == r[b] == p, need p.eqv(p)
                    Point2::axiom_eqv_reflexive(p);
                } else {
                    // resolved.dom().contains(b) from subset precondition
                    assert(r.dom().contains(b));
                    assert(r[a] == p);
                    assert(r[b] == resolved[b]);
                    // locus: p.eqv(resolved[b]) → r[a].eqv(r[b])
                }
            } else {
                // target == b
                assert(r.dom().contains(b));
                if a == b {
                    Point2::axiom_eqv_reflexive(p);
                } else {
                    assert(r.dom().contains(a));
                    assert(r[a] == resolved[a]);
                    assert(r[b] == p);
                    // locus: p.eqv(resolved[a]) → need r[a].eqv(r[b]) = resolved[a].eqv(p)
                    Point2::axiom_eqv_symmetric(p, resolved[a]);
                }
            }
        }

        Constraint::DistanceSq { a, b, dist_sq } => {
            if target == a {
                assert(r.dom().contains(a) && r.dom().contains(b));
                if a == b {
                    // Locus is FullPlane (b==target, not in resolved.dom())
                    // Unreachable: locus_is_nontrivial precondition
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                } else {
                    assert(r[a] == p);
                    assert(r[b] == resolved[b]);
                    // Locus: OnCircle(center=resolved[b], radius_sq=dist_sq)
                    // point_on_circle2: sq_dist(p, resolved[b]) ≡ dist_sq
                    // constraint: sq_dist(r[a], r[b]) ≡ dist_sq = sq_dist(p, resolved[b]) ≡ dist_sq ✓
                }
            } else {
                assert(target == b);
                assert(r.dom().contains(a) && r.dom().contains(b));
                if a == b {
                    // Unreachable: locus is FullPlane
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                } else {
                    assert(r[a] == resolved[a]);
                    assert(r[b] == p);
                    // Locus: OnCircle(center=resolved[a], radius_sq=dist_sq)
                    // sq_dist(p, resolved[a]) ≡ dist_sq (from locus)
                    // constraint: sq_dist(r[a], r[b]) = sq_dist(resolved[a], p) ≡ dist_sq
                    // Bridge: sq_dist(resolved[a], p) ≡ sq_dist(p, resolved[a])
                    lemma_sq_dist_symmetric::<T>(resolved[a], p);
                    T::axiom_eqv_transitive(
                        sq_dist_2d(resolved[a], p),
                        sq_dist_2d(p, resolved[a]),
                        dist_sq,
                    );
                }
            }
        }

        Constraint::FixedX { point, x } => {
            assert(target == point);
            assert(r.dom().contains(point));
            assert(r[point] == p);
            // Locus: OnLine(Line2{1, 0, -x})
            // point_on_line2 → p.x ≡ x (by helper)
            lemma_vertical_line_extract_x(p, x);
        }

        Constraint::FixedY { point, y } => {
            assert(target == point);
            assert(r.dom().contains(point));
            assert(r[point] == p);
            lemma_horizontal_line_extract_y(p, y);
        }

        Constraint::SameX { a, b } => {
            if target == a {
                assert(r.dom().contains(a) && r.dom().contains(b));
                if a == b {
                    Point2::axiom_eqv_reflexive(p);
                    T::axiom_eqv_reflexive(p.x);
                } else {
                    assert(r[a] == p && r[b] == resolved[b]);
                    // Locus: OnLine(Line2{1, 0, -resolved[b].x})
                    lemma_vertical_line_extract_x(p, resolved[b].x);
                    // p.x ≡ resolved[b].x = r[b].x
                }
            } else {
                assert(target == b);
                assert(r.dom().contains(a) && r.dom().contains(b));
                if a == b {
                    T::axiom_eqv_reflexive(p.x);
                } else {
                    assert(r[a] == resolved[a] && r[b] == p);
                    lemma_vertical_line_extract_x(p, resolved[a].x);
                    // p.x ≡ resolved[a].x → r[a].x ≡ r[b].x
                    T::axiom_eqv_symmetric(p.x, resolved[a].x);
                }
            }
        }

        Constraint::SameY { a, b } => {
            if target == a {
                assert(r.dom().contains(a) && r.dom().contains(b));
                if a == b {
                    T::axiom_eqv_reflexive(p.y);
                } else {
                    assert(r[a] == p && r[b] == resolved[b]);
                    lemma_horizontal_line_extract_y(p, resolved[b].y);
                }
            } else {
                assert(target == b);
                assert(r.dom().contains(a) && r.dom().contains(b));
                if a == b {
                    T::axiom_eqv_reflexive(p.y);
                } else {
                    assert(r[a] == resolved[a] && r[b] == p);
                    lemma_horizontal_line_extract_y(p, resolved[a].y);
                    T::axiom_eqv_symmetric(p.y, resolved[a].y);
                }
            }
        }

        Constraint::PointOnLine { point, line_a, line_b } => {
            // target must be point (we only generate loci for point, not line_a/line_b)
            if target == point {
                assert(r.dom().contains(point));
                assert(r.dom().contains(line_a));
                assert(r.dom().contains(line_b));
                assert(r[point] == p);
                // If target != line_a and target != line_b:
                // r[line_a] == resolved[line_a], r[line_b] == resolved[line_b]
                // Locus: OnLine(line2_from_points(resolved[line_a], resolved[line_b]))
                // point_on_line2(line2_from_points(resolved[line_a], resolved[line_b]), p)
                // constraint_satisfied checks:
                //   point_on_line2(line2_from_points(r[line_a], r[line_b]), r[point])
                // If line_a and line_b are different from target, r[line_a]==resolved[line_a] etc.
                // So the predicate is the same.
                if target != line_a && target != line_b {
                    assert(r[line_a] == resolved[line_a]);
                    assert(r[line_b] == resolved[line_b]);
                } else {
                    // Degenerate: point coincides with a line endpoint → FullPlane
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                // target is line_a or line_b → locus is FullPlane
                assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
            }
        }

        Constraint::EqualLengthSq { a1, a2, b1, b2 } => {
            if target == a1 {
                assert(r.dom().contains(a1) && r.dom().contains(a2));
                assert(r.dom().contains(b1) && r.dom().contains(b2));
                if a1 != a2 && a1 != b1 && a1 != b2 {
                    assert(r[a1] == p);
                    assert(r[a2] == resolved[a2]);
                    assert(r[b1] == resolved[b1]);
                    assert(r[b2] == resolved[b2]);
                    // Locus: OnCircle(center=resolved[a2], radius_sq=sq_dist(resolved[b1], resolved[b2]))
                    // point_on_circle2: sq_dist(p, resolved[a2]) ≡ sq_dist(resolved[b1], resolved[b2])
                    // constraint: sq_dist(r[a1], r[a2]) ≡ sq_dist(r[b1], r[b2])
                    //           = sq_dist(p, resolved[a2]) ≡ sq_dist(resolved[b1], resolved[b2]) ✓
                } else {
                    // Entity overlap: a1 == some other entity == target
                    // Since !resolved.dom().contains(target), constraint_to_locus
                    // can't find the overlapping entity in resolved → FullPlane
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else if target == a2 {
                if a2 != a1 && a2 != b1 && a2 != b2 {
                    assert(r[a1] == resolved[a1]);
                    assert(r[a2] == p);
                    assert(r[b1] == resolved[b1]);
                    assert(r[b2] == resolved[b2]);
                    // Locus: OnCircle(center=resolved[a1], radius_sq=sq_dist(b1,b2))
                    // sq_dist(p, resolved[a1]) ≡ sq_dist(resolved[b1], resolved[b2])
                    // constraint: sq_dist(resolved[a1], p) ≡ sq_dist(resolved[b1], resolved[b2])
                    lemma_sq_dist_symmetric::<T>(resolved[a1], p);
                    T::axiom_eqv_transitive(
                        sq_dist_2d(resolved[a1], p),
                        sq_dist_2d(p, resolved[a1]),
                        sq_dist_2d(resolved[b1], resolved[b2]),
                    );
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                // target is b1 or b2 — locus is FullPlane
                assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
            }
        }

        Constraint::Perpendicular { a1, a2, b1, b2 } => {
            if target == a1 {
                if a1 != a2 && a1 != b1 && a1 != b2 {
                    assert(r.dom().contains(a1) && r.dom().contains(a2));
                    assert(r.dom().contains(b1) && r.dom().contains(b2));
                    assert(r[a1] == p);
                    assert(r[a2] == resolved[a2]);
                    assert(r[b1] == resolved[b1]);
                    assert(r[b2] == resolved[b2]);
                    // Locus line: Line2{db.x, db.y, -(db.x*a2.x + db.y*a2.y)}
                    // Locus gives: db.x*p.x + db.y*p.y + (-(db.x*a2.x + db.y*a2.y)) ≡ 0
                    // Constraint needs: db.x*a2.x + db.y*a2.y + (-(db.x*p.x + db.y*p.y)) ≡ 0
                    // This is the swap: S1 + (-S2) ≡ 0 → S2 + (-S1) ≡ 0
                    let db = sub2(resolved[b2], resolved[b1]);
                    lemma_point_on_line2_swap::<T>(
                        db.x, db.y, p.x, p.y, resolved[a2].x, resolved[a2].y,
                    );
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else if target == a2 {
                if a2 != a1 && a2 != b1 && a2 != b2 {
                    assert(r.dom().contains(a1) && r.dom().contains(a2));
                    assert(r.dom().contains(b1) && r.dom().contains(b2));
                    assert(r[a2] == p);
                    assert(r[a1] == resolved[a1]);
                    assert(r[b1] == resolved[b1]);
                    assert(r[b2] == resolved[b2]);
                    // Locus line and constraint line are structurally identical
                    // (both use resolved[a1] as the "other" point).
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
            }
        }

        Constraint::Parallel { a1, a2, b1, b2 } => {
            if target == a1 {
                if a1 != a2 && a1 != b1 && a1 != b2 {
                    assert(r.dom().contains(a1) && r.dom().contains(a2));
                    assert(r.dom().contains(b1) && r.dom().contains(b2));
                    assert(r[a1] == p);
                    assert(r[a2] == resolved[a2]);
                    assert(r[b1] == resolved[b1]);
                    assert(r[b2] == resolved[b2]);
                    // Same swap pattern with coefficients db.y and db.x.neg()
                    let db = sub2(resolved[b2], resolved[b1]);
                    lemma_point_on_line2_swap::<T>(
                        db.y, db.x.neg(), p.x, p.y, resolved[a2].x, resolved[a2].y,
                    );
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else if target == a2 {
                if a2 != a1 && a2 != b1 && a2 != b2 {
                    assert(r.dom().contains(a1) && r.dom().contains(a2));
                    assert(r.dom().contains(b1) && r.dom().contains(b2));
                    assert(r[a2] == p);
                    assert(r[a1] == resolved[a1]);
                    assert(r[b1] == resolved[b1]);
                    assert(r[b2] == resolved[b2]);
                    // Structurally identical — locus and constraint use same line.
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
            }
        }

        Constraint::Midpoint { mid, a, b } => {
            if target == mid {
                assert(r.dom().contains(mid) && r.dom().contains(a) && r.dom().contains(b));
                if mid != a && mid != b {
                    assert(r[mid] == p);
                    assert(r[a] == resolved[a]);
                    assert(r[b] == resolved[b]);
                    lemma_midpoint_div_satisfies(
                        resolved[a].x, resolved[b].x,
                        resolved[a].y, resolved[b].y,
                        p,
                    );
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else if target == a {
                assert(r.dom().contains(mid) && r.dom().contains(a) && r.dom().contains(b));
                if a != mid && a != b {
                    assert(r[a] == p);
                    assert(r[mid] == resolved[mid]);
                    assert(r[b] == resolved[b]);
                    lemma_midpoint_a_satisfies(
                        resolved[mid].x, resolved[mid].y,
                        resolved[b].x, resolved[b].y,
                        p,
                    );
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                assert(target == b);
                assert(r.dom().contains(mid) && r.dom().contains(a) && r.dom().contains(b));
                if b != mid && b != a {
                    assert(r[b] == p);
                    assert(r[mid] == resolved[mid]);
                    assert(r[a] == resolved[a]);
                    lemma_midpoint_a_satisfies(
                        resolved[mid].x, resolved[mid].y,
                        resolved[a].x, resolved[a].y,
                        p,
                    );
                    let two = T::one().add(T::one());
                    T::axiom_add_commutative(p.x, resolved[a].x);
                    T::axiom_eqv_transitive(
                        resolved[mid].x.mul(two),
                        p.x.add(resolved[a].x),
                        resolved[a].x.add(p.x),
                    );
                    T::axiom_add_commutative(p.y, resolved[a].y);
                    T::axiom_eqv_transitive(
                        resolved[mid].y.mul(two),
                        p.y.add(resolved[a].y),
                        resolved[a].y.add(p.y),
                    );
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            }
        }

        Constraint::Collinear { a, b, c: c_id } => {
            // constraint_satisfied: point_on_line2(line2_from_points(r[a], r[b]), r[c_id])
            if target == c_id {
                // target = c_id: locus is OnLine(line2_from_points(resolved[a], resolved[b]))
                // point_on_line2(line2_from_points(a', b'), p) — directly matches constraint
                if c_id != a && c_id != b {
                    assert(r.dom().contains(a) && r.dom().contains(b) && r.dom().contains(c_id));
                    assert(r[c_id] == p);
                    assert(r[a] == resolved[a]);
                    assert(r[b] == resolved[b]);
                    // Locus and constraint use identical line and point — direct match
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else if target == a {
                // target = a: locus is OnLine(line2_from_points(resolved[b], resolved[c_id]))
                // Need: point_on_line2(line2_from_points(p, resolved[b]), resolved[c_id])
                if a != b && a != c_id {
                    assert(r.dom().contains(a) && r.dom().contains(b) && r.dom().contains(c_id));
                    assert(r[a] == p);
                    assert(r[b] == resolved[b]);
                    assert(r[c_id] == resolved[c_id]);
                    // From locus: point_on_line2(line2_from_points(b', c'), p)
                    // Need: point_on_line2(line2_from_points(p, b'), c')
                    lemma_collinear_cyclic(p, resolved[b], resolved[c_id]);
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                assert(target == b);
                // target = b: locus is OnLine(line2_from_points(resolved[a], resolved[c_id]))
                // Need: point_on_line2(line2_from_points(resolved[a], p), resolved[c_id])
                if b != a && b != c_id {
                    assert(r.dom().contains(a) && r.dom().contains(b) && r.dom().contains(c_id));
                    assert(r[b] == p);
                    assert(r[a] == resolved[a]);
                    assert(r[c_id] == resolved[c_id]);
                    // From locus: point_on_line2(line2_from_points(a', c'), p)
                    // Need: point_on_line2(line2_from_points(a', p), c')
                    lemma_collinear_swap(resolved[a], p, resolved[c_id]);
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            }
        }

        Constraint::PointOnCircle { point, center, radius_point } => {
            // constraint_satisfied: sq_dist(r[point], r[center]) ≡ sq_dist(r[radius_point], r[center])
            // target must be point (only locus entity)
            if target == point {
                if point != center && point != radius_point {
                    assert(r.dom().contains(point) && r.dom().contains(center) && r.dom().contains(radius_point));
                    assert(r[point] == p);
                    assert(r[center] == resolved[center]);
                    assert(r[radius_point] == resolved[radius_point]);
                    // Locus: OnCircle(center=resolved[center], radius_sq=sq_dist(radius_point', center'))
                    // point_on_circle2: sq_dist(p, center') ≡ sq_dist(radius_point', center')
                    // constraint: sq_dist(r[point], r[center]) ≡ sq_dist(r[radius_point], r[center])
                    //           = sq_dist(p, center') ≡ sq_dist(radius_point', center') ✓
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                // target is center or radius_point — not in locus_entities → FullPlane
                assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
            }
        }

        Constraint::Symmetric { point, original, axis_a, axis_b } => {
            // constraint_satisfied: r[point].eqv(reflect(...r[original], r[axis_a], r[axis_b]...))
            // target must be point (only locus entity)
            if target == point {
                if point != original && point != axis_a && point != axis_b {
                    assert(r.dom().contains(point) && r.dom().contains(original));
                    assert(r.dom().contains(axis_a) && r.dom().contains(axis_b));
                    assert(r[point] == p);
                    assert(r[original] == resolved[original]);
                    assert(r[axis_a] == resolved[axis_a]);
                    assert(r[axis_b] == resolved[axis_b]);
                    // Locus: AtPoint(reflect_point_across_line(original', axis_a', axis_b'))
                    // point_satisfies_locus: p.eqv(reflect(original', axis_a', axis_b'))
                    // constraint: r[point].eqv(reflect(r[original], r[axis_a], r[axis_b]))
                    //           = p.eqv(reflect(original', axis_a', axis_b')) ✓ direct match
                } else {
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else {
                assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
            }
        }
    }
}

} // verus!
