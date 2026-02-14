# PLAN_EMDASH_STRICT_ACCUMULATION_ORDINARY.md

Date: 2026-02-09

## 1. Title

Strict Accumulation Rewrites for Ordinary `tapp1_fapp0` (Category-Theoretic Stress-Test)

## 2. Summary

Implement a focused category-theoretic milestone by adding stable-head strict accumulation rewrites
for ordinary off-diagonal transfor components (`tapp1_fapp0`) using the existing internal
composition order (`g ∘ f` as `compose_morph g f` / `comp_fapp0 g f`).

This milestone is ordinary-first (not displayed-first), then mirrored to displayed
(`tdapp1_fapp0`) in the next step after ordinary rules are validated.

## 3. Scope

In scope:

1. Canonicalization + strict accumulation rules on ordinary stable heads (`tapp1_fapp0`).
2. Regression and stress tests proving reduction behavior.
3. No parser changes.

Out of scope:

1. Displayed accumulation rules (`tdapp1_fapp0` / `fdapp1_fapp0`).
2. Adjunction triangle rules.
3. Broad lax/strict syntax distinction.

## 4. Public Interface / Kernel-Facing Additions

1. `emdash1/src/stdlib.ts`
- Add stable-head-oriented rewrite rules for ordinary accumulation:
  - postcomposition-style accumulation:
    `compose_morph (FMap1Term G g) (tapp1_fapp0 eps f)  ↪  tapp1_fapp0 eps (comp_fapp0 g f)`
  - precomposition-style accumulation:
    `compose_morph (tapp1_fapp0 eps f) (FMap1Term F g)  ↪  tapp1_fapp0 eps (comp_fapp0 f g)`
- Keep orientation consistent with existing internal order.

2. `emdash1/src/types.ts`
- No new AST constructors required for this slice.
- Reuse `TApp1FApp0Term`, `FMap1Term`, and existing composition heads.

## 5. Implementation Details

1. Build rules against existing primitives only:
- `compose_morph`
- `FMap1Term`
- `TApp1FApp0Term`
- `compose_morph` for base-arrow composition.

2. Keep rewrite set terminating:
- one-way accumulation orientation only,
- avoid adding symmetric inverse rules.

3. Validate no overlap loops with existing functoriality rule
`F(a) ∘ F(a') ↪ F(a∘a')`.

## 6. Test Plan

Target file: `emdash1/tests/emdash2_functor_transfor_tests.ts`.

Add positive tests:

1. postcomposition accumulation:
- construct `G(g) ∘ ϵ_(f)` and verify normalization to `ϵ_(g∘f)`.

2. precomposition accumulation:
- construct `ϵ_(f) ∘ F(g)` and verify normalization to `ϵ_(f∘g)`.

3. strict functoriality composition sanity:
- construct `F(f) ∘ F(g)` and verify normalization to `F(f∘g)`.

Add negative/guard tests:

1. rule does not produce ill-typed results in mismatched categories (typing layer prevents this);
2. no rewrite-loop regression under normal test run.

## 7. Validation Commands

1. `npm test --prefix emdash1`
2. `EMDASH_TYPECHECK_TIMEOUT=60s make check`

Both must pass.

## 8. Assumptions / Defaults

1. Strictness is assumed for this milestone.
2. Internal composition order stays current (`compose_morph g f` means `g ∘ f`).
3. Stable-head rewrites are preferred over unification-only encoding.
4. Ordinary-first rollout before displayed accumulation.
