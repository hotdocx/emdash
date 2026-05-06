# emdash3 Homd Rework Without Opaque Target Wrappers

## Summary

Rework `homd_int` so its type directly exposes the iterated `Functor_catd`/`Pi_cat` structure:

`b0 : Z^op, e0 : E[b0]^op ⊢ Π b1:Z. E[b1] → Hom_Z(b0,b1)^op → Cat`

Do not introduce a `Homd_target_catd` whose meaning is only a `Fibre_cat` rule. Instead, build the target as a direct expression from general reusable combinators: `Edge_catd_fam`, `Functor_catd` internalization, and `Pi_func`.

## Key Changes

- Add reusable internal combinators:
  - `Pi_func Z : Functor (Catd_cat Z) Cat_cat`, with `fapp0 (Pi_func Z) D ↪ Pi_cat D`.
  - `Functor_catd_fapp0_func E : Functor (Catd_cat Z) (Catd_cat Z)`, with `D ↦ Functor_catd E D`.
  - `Functor_catd_fixR_func D : Functor (Op_cat (Catd_cat Z)) (Catd_cat Z)`, with `K ↦ Functor_catd K D`.
- Replace object-only `Edge_catd` usage with an internal edge family:
  - `Edge_catd_fam Z : Functor (Op_cat Z) (Op_cat (Catd_cat Z))`.
  - `Edge_catd x` remains a projection/view of `Edge_catd_fam x`.
  - Fibre sanity: `Fibre_cat (Edge_catd x) y ↪ Op_cat (Hom_cat Z x y)`.
- Define the homd base target as a direct δ-expression, not an opaque target category:
  - `homd_base_func E : Functor (Op_cat Z) Cat_cat`
  - object shape:
    `homd_base_func(E)(b0) ↪ Pi_cat (Functor_catd E (Functor_catd (Edge_catd b0) (CatCat_catd Z)))`
- Redefine:
  - `homd_int E : Functord (Op_catd E) (Fibration_cov_catd (homd_base_func E))`
  - `homd_section E b0 e0` as the projection of `fdapp0 (homd_int E) b0 e0`.
  - `homd_eval_func E b0 e0 b1 e1` as evaluation of that section at `b1` and `e1`.
- Keep endpoint computation:
  - For `E = Fibration_cov_catd M`, `fapp0 (homd_eval_func E b0 e0 b1 e1) f ↪ Hom_cat (M[b1]) (f_! e0) e1`.

## Implementation Notes

- Keep `CatCat_catd Z = Const_catd Z Cat_cat`; do not replace it with `Fib_func` in this layer. `Fib_func` classifies Cat-valued functors/fibrations, while the inner target here is literally `Cat`.
- Do not add a generic `Functor_catd'` yet. The current homd shape is expressible with ordinary `Functor_catd` over `Z` plus `Pi_func`; a deeper relative `Functor_catd` can be introduced later if a codomain depends on an already-bound fibre variable in a way this does not cover.
- Update reports to mark the previous `homd_curry_base_fam`/`homd_int` target as superseded by the direct iterated-`Functor_catd` expression.

## Test Plan

- Run `lambdapi check -w emdash3.lp` after each patch.
- Add assertions for:
  - `fapp0 (Pi_func Z) D ≡ Pi_cat D`.
  - `fapp0 (Functor_catd_fapp0_func E) D ≡ Functor_catd E D`.
  - `fapp0 (Functor_catd_fixR_func D) K ≡ Functor_catd K D`.
  - `Fibre_cat (Edge_catd b0) b1 ≡ Op_cat (Hom_cat Z b0 b1)`.
  - `fapp0 (homd_base_func E) b0 ≡ Pi_cat (Functor_catd E (Functor_catd (Edge_catd b0) (CatCat_catd Z)))`.
  - `fdapp0 (homd_int E) b0 e0 ≡ homd_section E b0 e0`.
  - evaluating `homd_section` at `b1,e1` folds to `homd_eval_func E b0 e0 b1 e1`.
  - Groth endpoint computation and `Sigma_cat` hom computation still pass.
- Also run `EMDASH_TYPECHECK_TIMEOUT=60s make check` for the repository SOP check.

## Assumptions

- The chosen internal order is `Π b1. E[b1] → Hom_Z(b0,b1)^op → Cat`, matching the user’s latest sketch.
- `homd_eval_func` and `Homd_func` remain projection/debugging heads only; `homd_int` is the primary iteratable construction.

## Superseded Note

This plan is preserved for context, but the next review identified a likely flaw: the terminal target should not be modeled as a constant `CatCat_catd` surrogate if the intended layer is better expressed by applying `Fib_func` to the bound hom category/functor. The corrected direction should connect `E^op`, `E`, and the base hom directly, preferably using `hom_`/`hom2_int` rather than an `Edge_catd` intermediary.
