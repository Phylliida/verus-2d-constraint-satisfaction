# Displacement Optimality Proof — Status and Lessons

## Goal

Prove formally that `compute_greedy_mask` selects the sign combination that minimizes displacement. Specifically:

```
cl_displacement_sign(circle, line, target) > 0
⟹ sq_dist(P_plus, Q) > sq_dist(P_minus, Q)   [in QExt ordering]
```

This is `lemma_cl_displacement_sign_determines_order` in `verus-geometry/src/circle_line.rs`.

## What's Proved (all verified, 0 errors)

### Building blocks (all in circle_line.rs unless noted)

| Lemma | What it proves | Status |
|-------|---------------|--------|
| `lemma_qe_nonneg_pure_im` (ordered.rs) | `qe_nonneg(qext(0, im)) == zero.le(im)` | **Verified** |
| `lemma_qe_sq_re_conjugate` | `(a+b√d)².re ≡ (a-b√d)².re` | **Verified** |
| `lemma_qe_sq_im_conjugate` | `(a-b√d)².im ≡ neg((a+b√d)².im)` | **Verified** |
| `lemma_qe_sq_re_im_congruence` | If `a ≡ b` then `sq(qext(r,a)).re ≡ sq(qext(r,b)).re` | **Verified** |
| `lemma_qe_sq_im_im_congruence` | If `a ≡ b` then `sq(qext(r,a)).im ≡ sq(qext(r,b)).im` | **Verified** |
| `lemma_sub_zero` | `a - 0 ≡ a` | **Verified** |
| `lemma_cl_intersection_conjugate` | P_plus and P_minus have same re parts | **Verified** |
| `lemma_cl_sq_dist_re_equal` | `sq_dist(P_plus, Q).re ≡ sq_dist(P_minus, Q).re` | **Verified** |
| `lemma_cl_sq_dist_sign_from_im` | `diff.re ≡ 0 ∧ diff.im > 0 ⟹ zero.lt(diff)` | **Verified** |
| `lemma_cl_displacement_cancellation` | Cross-term cancellation identity | **Verified** |
| `lemma_scaled_step_a/b/c` | Chain `v*(a/A) - u*(b/A) ≡ numer/A` | **Verified** |
| `lemma_scaled_disp_eqv` | Full eqv chain combining steps A/B/C | **Verified** |
| `lemma_scaled_disp_positive` | `v*(a/A) - u*(b/A) > 0` when `neg(b)*u + a*v > 0` | **Verified** |
| `lemma_neg_plus_minus_double` | `neg(X)+Y-(X+neg(Y)) ≡ (Y-X)+(Y-X)` | **Verified** |
| `lemma_double_sub_double` | `(t+t)-(s+s) ≡ (t-s)+(t-s)` | **Verified** |
| `lemma_cl_sq_dist_im_eqv_scaled` | `diff.im ≡ 4*scaled` (full im expansion) | **Verified** |
| `lemma_cl_displacement_sign_determines_order` | Main theorem: sign > 0 ⟹ P_plus farther | **Verified** |

### Theorem chain

1. `diff.re ≡ 0` — **PROVED** (lemma_cl_sq_dist_re_equal)
2. `diff.re ≡ 0 ∧ diff.im > 0 ⟹ zero.lt(diff)` — **PROVED** (lemma_cl_sq_dist_sign_from_im)
3. `diff.im ≡ 4*scaled` — **PROVED** (lemma_cl_sq_dist_im_eqv_scaled)
4. `scaled > 0 when cl_displacement_sign > 0` — **PROVED** (lemma_scaled_disp_positive + cancellation)
5. `cl_displacement_sign > 0 ⟹ zero.lt(diff)` — **PROVED** (lemma_cl_displacement_sign_determines_order)

## Completion

**All proof obligations are fully verified. 604 verified, 0 errors in verus-geometry. 470 verified, 0 errors in verus-2d-constraint-satisfaction.**

**Estimated remaining: ~30-50 lines of ring axiom plumbing.**

## Key Lessons Learned

### 1. Z3 can't handle large proof functions
**SMT solver response time is superlinear in proof size.** Functions with >50 assertions consistently fail even with high rlimit. The solution: split into focused helpers of ≤30 lines each.

Example: `lemma_scaled_disp_eqv` was 100+ lines and failed. Split into `lemma_scaled_step_a`, `step_b`, `step_c` (each ~10 lines) — all verified instantly.

### 2. The `assert(F) by { ... }` pattern is critical
Facts introduced inside `by { ... }` are scoped. This prevents context pollution. Use it whenever a lemma's ensures introduces terms that aren't needed by later steps.

### 3. Structural term matching is the biggest obstacle
Verus spec terms are structural — `a.sub(F::zero())` is NOT structurally `a` even though they're `eqv`. Every time the QExt `sub`, `mul`, `add` trait methods produce terms that differ structurally from what the proof needs, you need explicit `eqv` bridges.

The `sub(im, zero)` bridge was needed for EVERY coordinate of EVERY intersection point — 8 bridge calls per proof.

### 4. `neg(b)/A ≠ neg(b/A)` structurally
`cl_intersection_x` with `plus=true` gives `im = neg(b).div(A)`. But `neg(b/A) = b.div(A).neg()`. These are different terms connected by `lemma_div_neg_numerator`. This structural mismatch requires explicit bridging in every proof that works with both signs.

### 5. Proof-by-contradiction in `assert by` blocks doesn't work directly
`assert(!P) by { if P { ..contradiction.. } }` doesn't close automatically in Verus. Instead, use the `if P { ... establish 0.eqv(numer) ... }` pattern OUTSIDE `assert by`, letting Z3 see the contradiction in the main context.

### 6. The algebraic identity (hard part) was proved first
`lemma_cl_displacement_cancellation` (the cross-term cancellation `a*b*h/A - a*b*h/A = 0`) was the mathematically interesting part and was proved cleanly in ~100 lines. The QExt unfolding plumbing (connecting through `sq_dist_2d` → `sub2` → `norm_sq` → `qe_mul` trait methods) is the tedious part.

### 7. The recursive spec fn pattern (from memory) solved the dedup proof
`forall...exists` postconditions on Vec operations hit a Z3 limitation. The solution: replace with a recursive spec predicate (`seq_contains_all`) that avoids existential quantifiers entirely. This pattern from `feedback_verus_specfn_triggers.md` turned an impossible proof into a clean 15-line one.

## File Map

| File | Key additions |
|------|--------------|
| `verus-quadratic-extension/src/ordered.rs` | `lemma_qe_nonneg_pure_im` |
| `verus-geometry/src/circle_line.rs` | All circle-line displacement lemmas (~25 functions) |
| `verus-2d-constraint-satisfaction/src/runtime/solver.rs` | `compute_greedy_mask`, union-find, component decomposition, diagnostics |
| `verus-2d-constraint-satisfaction/src/runtime/pipeline.rs` | `solve_min_displacement_auto`, `dedup_masks` with `seq_contains_all` |
| `verus-2d-constraint-satisfaction/src/runtime/ext_constraint.rs` | `compute_total_displacement` with non-negativity proof |
| `verus-2d-constraint-satisfaction/src/construction_ext.rs` | `lemma_step_result_independent`, `lemma_displacement_separable` |
