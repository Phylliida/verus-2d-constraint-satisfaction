# verus-2d-constraint-satisfaction

Formally verified 2D geometric constraint solver in Rust + [Verus](https://github.com/verus-lang/verus).

**398 verified functions, 0 errors, 0 `assume(false)`.**

## What it does

Given a set of 2D geometric constraints (distances, angles, collinearity, tangency, etc.) and some fixed points, this crate finds positions for all free points that satisfy every constraint. The solver is formally verified: when it returns a solution, a machine-checked proof guarantees that all constraints are satisfied.

## Architecture

The crate has three layers:

### Spec layer (pure mathematical definitions)
- **`constraints.rs`** -- 19 constraint types (`Coincident`, `DistanceSq`, `FixedX`, `PointOnLine`, `Perpendicular`, `Parallel`, `Symmetric`, `Tangent`, etc.) and the `constraint_satisfied` predicate
- **`locus.rs`** -- Each constraint induces a geometric locus (line, circle, or point) on its target entity. `constraint_to_locus` maps constraints to loci, with a full soundness proof (`lemma_locus_sound`)
- **`construction.rs`** -- Construction plans: sequences of steps that place entities by intersecting pairs of loci. Includes the main soundness theorem `lemma_valid_plan_satisfies_constraints`
- **`solver.rs`** -- Greedy solver spec: iteratively resolves entities that have >= 2 non-trivial loci. Includes `system_is_well_constrained` predicate for diagnosing unsolvable systems

### Construction extension layer
- **`construction_ext.rs`** -- Lifts construction plans from base field F to the quadratic extension field Q(sqrt(R)), enabling exact circle intersection via closed-form formulas. Proves `lemma_solver_to_soundness_det`: the deterministic execution in the extension field satisfies all constraints

### Runtime layer (executable code with verified ensures)
- **`runtime/solver.rs`** -- Greedy solver implementation. Enumerates sign variants (which intersection point to use for each circle step). Includes `check_well_constrained` diagnostic
- **`runtime/pipeline.rs`** -- End-to-end pipeline with three entry points:
  - `solve_and_verify<R>` -- Full spec guarantee: ensures `constraint_satisfied` at the extension field level for every returned solution
  - `solve_and_verify_auto` -- Automatic radicand detection (sqrt(2), sqrt(3), ..., sqrt(13)). Type-erased but tracks verification count
  - `solve_and_verify_chain` -- Arbitrary-depth quadratic tower via `DynFieldElem`. Ensures `constraint_satisfied_dts` (spec-level constraint satisfaction on dynamic tower values)
- **`runtime/dyn_pipeline.rs`** -- Dynamic field tower constraint checking. All 19 constraint checkers have verified ensures connecting to `constraint_satisfied_dts`
- **`runtime/construction.rs`** -- Runtime plan execution with extension field arithmetic
- **`runtime/ext_constraint.rs`** -- Extension-level verification constraint checking (for Tangent, CircleTangent, Angle)

## Constraint types

| Constraint | Description | Constructive? |
|---|---|---|
| `Coincident` | Two points at same position | Yes |
| `DistanceSq` | Squared distance between two points equals a value | Yes |
| `FixedX` / `FixedY` | Fix one coordinate | Yes |
| `SameX` / `SameY` | Two points share a coordinate | Yes |
| `PointOnLine` | Point lies on line through two other points | Yes |
| `EqualLengthSq` | Two segments have equal squared length | Yes |
| `Midpoint` | Point is midpoint of two others | Yes |
| `Perpendicular` | Two segments are perpendicular | Yes |
| `Parallel` | Two segments are parallel | Yes |
| `Collinear` | Three points are collinear | Yes |
| `PointOnCircle` | Point on circle defined by center + radius point | Yes |
| `Symmetric` | Point is reflection of another across a line | Yes |
| `FixedPoint` | Fix both coordinates | Yes |
| `Ratio` | Ratio of squared distances | Yes |
| `Tangent` | Line-circle tangency | Verification-only |
| `CircleTangent` | Circle-circle tangency | Verification-only |
| `Angle` | Angle between segments via squared cosine | Verification-only |

"Constructive" constraints contribute loci that the solver uses to place points. "Verification-only" constraints are checked after the plan executes but cannot constructively place points (they involve quartic conditions that don't reduce to line/circle loci).

## Verification guarantees

### Generic path (`solve_and_verify<R>`)

The strongest guarantee. For each returned solution:

```
forall|ci| constraint_satisfied(
    lift_constraints::<RationalModel, R>(constraints)[ci],
    execute_plan_in_ext::<RationalModel, R>(full_plan))
```

This says: every constraint, lifted to the quadratic extension field Q(sqrt(R)), is satisfied by the deterministic plan execution. The proof chain:

1. Runtime checks plan validity (distinct targets, well-formed steps, locus ordering, independence, geometric validity)
2. Executes the plan in Q(sqrt(R)) using exact circle intersection formulas
3. Checks verification constraints at the extension level
4. Invokes `lemma_solver_to_soundness_det` which proves constraint satisfaction from the checked properties

Additionally, the runtime `ext_points` are proven to agree with the spec-level execution:
```
ext_vec_to_resolved_map(sol.ext_points)[id] == execute_plan_in_ext(full_plan)[id]
```

### Dynamic tower path (`solve_and_verify_chain`)

For arbitrary-depth problems (nested square roots), uses `DynFieldElem` with type-erased tower arithmetic:

```
exists|deep: Seq<DynRtPoint2>|
    all_dyn_points_wf(deep) &&
    forall|ci| constraint_satisfied_dts(constraints[ci], deep)
```

The `constraint_satisfied_dts` predicate mirrors `constraint_satisfied` using `DynTowerSpec` operations. Each of the 19 runtime checkers (`check_*_dyn`) has a verified ensures connecting to this predicate. The trust boundary is the `dyn_*` primitive methods on `DynFieldElem`.

## How the solver works

1. **Greedy resolution**: Scan free entities, find one with >= 2 non-trivial loci from resolved neighbors, intersect the loci to place it
2. **Locus intersection**: Line-line (deterministic), circle-line or circle-circle (two solutions, selected by `plus` flag)
3. **Sign variants**: Enumerate all 2^k combinations of plus/minus for k circle steps
4. **Verification**: For each variant, check plan soundness + constraint satisfaction
5. **Extension field**: Circle intersections use exact formulas in Q(sqrt(discriminant)), avoiding floating-point

## Key design decisions

### `execute_step` vs `execute_step_in_ext`

`execute_step` uses `choose` (non-deterministic) for circle intersections because the formulas require square roots unavailable in a generic `T: OrderedField`. The canonical deterministic execution is `execute_step_in_ext` which works in `SpecQuadExt<F, R>` where sqrt(R) exists. The soundness theorem goes through `execute_plan_in_ext`.

### `constraint_satisfied_dts` existential witnesses

For constraints involving embedded scalars (Midpoint, Ratio, CircleTangent, Angle), `constraint_satisfied_dts` uses existential witnesses: `exists|two: DynTowerSpec| dts_eqv(two, 1+1) && ...`. This avoids needing multiplication congruence across tower depths (the `dts_eqv` predicate ignores radicands, so values at different depths can be eqv but not interchangeable in multiplication). The witnesses are provided by the runtime `dts_model` of computed values.

### Symmetric decomposition

The `Symmetric` constraint checks perpendicularity + midpoint-on-axis (algebraic conditions) rather than directly computing `reflect_point_across_line` (which involves division). The equivalence is fully proved in `verus-geometry/src/reflection.rs`:

```
lemma_symmetric_decomposition_backward:
    perp(q-p, d) && midpoint_on_axis(p, q, a, b) && dot(d,d) != 0
    ==> q == reflect_point_across_line(p, a, b)
```

## Dependencies

- `verus-algebra` -- Algebraic trait hierarchy (Ring, Field, OrderedField) and lemma libraries
- `verus-geometry` -- Point2, Line2, Circle2, intersection formulas, reflection proofs
- `verus-rational` -- Exact rational arithmetic (numerator/denominator representation)
- `verus-quadratic-extension` -- Q(sqrt(R)) extension fields, DynTowerSpec dynamic tower
- `verus-linalg` -- Vec2 operations, runtime rational helpers
- `verus-bigint` -- Arbitrary-precision integers (used by rational arithmetic)

## Verification stats

```
verus-2d-constraint-satisfaction: 398 verified, 0 errors, 0 assume(false)
verus-quadratic-extension:       231 verified, 0 errors, 0 assume(false)
verus-geometry:                  580 verified, 0 errors, 0 assume(false)
```
