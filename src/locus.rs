use vstd::prelude::*;
use verus_algebra::traits::*;
use verus_algebra::lemmas::additive_group_lemmas::*;
use verus_algebra::lemmas::ring_lemmas::*;
use verus_algebra::lemmas::field_lemmas::*;
use verus_geometry::point2::*;
use verus_geometry::line2::*;
use verus_geometry::circle2::*;
use verus_geometry::voronoi::sq_dist_2d;
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

        Constraint::Midpoint { mid, a, b } => {
            if target == mid {
                assert(r.dom().contains(mid) && r.dom().contains(a) && r.dom().contains(b));
                if mid != a && mid != b {
                    assert(r[mid] == p);
                    assert(r[a] == resolved[a]);
                    assert(r[b] == resolved[b]);
                    // Locus: AtPoint with midpoint coordinates
                    // p ≡ Point2{(a.x+b.x)/2, (a.y+b.y)/2}
                    // Need: p.x*2 ≡ a.x + b.x and p.y*2 ≡ a.y + b.y
                    lemma_midpoint_div_satisfies(
                        resolved[a].x, resolved[b].x,
                        resolved[a].y, resolved[b].y,
                        p,
                    );
                } else {
                    // Entity overlap: mid == a or mid == b, target not in resolved → FullPlane
                    assert(!locus_is_nontrivial(constraint_to_locus(c, resolved, target)));
                }
            } else if target == a {
                assert(r.dom().contains(mid) && r.dom().contains(a) && r.dom().contains(b));
                if a != mid && a != b {
                    assert(r[a] == p);
                    assert(r[mid] == resolved[mid]);
                    assert(r[b] == resolved[b]);
                    // Locus: AtPoint(2*mid - b)
                    // p ≡ Point2{2*mid.x - b.x, 2*mid.y - b.y}
                    // Need: mid.x*2 ≡ p.x + b.x
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
                    // Symmetric to target==a case
                    lemma_midpoint_a_satisfies(
                        resolved[mid].x, resolved[mid].y,
                        resolved[a].x, resolved[a].y,
                        p,
                    );
                    // constraint: r[mid].x.mul(two).eqv(r[a].x.add(r[b].x))
                    // Helper gives mid.x*2 ≡ p.x + a.x
                    // But constraint needs mid.x*2 ≡ a.x + p.x
                    // By add commutativity:
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
    }
}

} // verus!
