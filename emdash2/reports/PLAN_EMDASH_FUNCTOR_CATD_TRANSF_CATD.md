# PLAN_EMDASH_FUNCTOR_CATD_TRANSF_CATD.md

Date: 2026-02-09

## 1. Title

Implement `Functor_catd` and `Transf_catd` in TS elaboration/runtime, aligned with `emdash2.lp`

## 2. Summary

Add first-class support for the two missing fibrewise displayed constructors:

- `Functor_catd : [Z:Cat] -> Catd Z -> Catd Z -> Catd Z`
- `Transf_catd : [Z:Cat] [E D:Catd Z] -> Functord E D -> Functord E D -> Catd Z`

and their key fibre computation behavior in TS:

- `Fibre (Functor_catd E D) z` computes to `Functor_cat (Fibre E z) (Fibre D z)`.
- `Fibre (Transf_catd FF GG) z` computes to `Transf_cat (Fibre_func FF z) (Fibre_func GG z)`.

## 3. Scope

In scope:

1. New term constructors/tags in TS for `Functor_catd` and `Transf_catd`.
2. Elaboration typing rules:
   - both constructors elaborate to `Catd Z`.
3. Runtime reduction support for the two fibre computation laws above.
4. Stdlib globals:
   - `Functor_catd`, `Transf_catd`, and supporting `Fibre_func` (for typed target of `Transf_catd` fibre rule).
5. Test coverage for positive and negative scenarios.

Out of scope:

1. Full transport/cleavage semantics over base arrows.
2. New parser surface syntax.
3. Extra coherence rules not directly required by these fibre computations.

## 4. Interfaces / TS changes

1. `emdash1/src/types.ts`
   - Add:
     - `FunctorCatdTerm(baseCat, displayedDom, displayedCod)`
     - `TransfCatdTerm(baseCat, displayedDom, displayedCod, displayedFunctorFF, displayedFunctorGG)`
2. Exhaustive integration in:
   - `state.ts`, `elaboration.ts`, `reduction.ts`, `equality.ts`, `structural.ts`, `pattern.ts`, `unification.ts`, `proof.ts`.
3. `emdash1/src/stdlib.ts`
   - Define global `Functor_catd` with value to canonical term constructor.
   - Define global `Transf_catd` with value to canonical term constructor.
   - Define global `Fibre_func` interface (typed symbol used by `Transf_catd` fibre computation).

## 5. Reduction behavior to implement

In WHNF for `Fibre Z E z` shape:

1. If `E` WHNF is `FunctorCatdTerm(Z,E0,D0)`:
   - reduce to `FunctorCategoryTerm(Fibre Z E0 z, Fibre Z D0 z)`.
2. If `E` WHNF is `TransfCatdTerm(Z,E0,D0,FF,GG)`:
   - reduce to `TransfCategoryTerm(Fibre Z E0 z, Fibre Z D0 z, Fibre_func FF z, Fibre_func GG z)`.

## 6. Tests / validation suite

Add or extend tests to include:

1. `Obj(Fibre Z (Functor_catd Z E D) z)` elaborates to `Obj(Functor_cat (Fibre Z E z) (Fibre Z D z))`.
2. `Obj(Fibre Z (Transf_catd Z E D FF GG) z)` elaborates to `Obj(Transf_cat (Fibre_func FF z) (Fibre_func GG z))`.
3. Context-level internalized usage remains valid:
   - `FF : Obj(Functord_cat Z E D)`, `GG : Obj(Functord_cat Z E D)`.
4. Negative checks:
   - mismatched base category in `Functor_catd`/`Transf_catd`,
   - wrong `FF/GG` classifier for `Transf_catd`.

Validation commands:

1. `npm test --prefix emdash1`
2. `EMDASH_TYPECHECK_TIMEOUT=60s make check`

## 7. Assumptions

1. This slice follows the current pointwise/fibrewise design only.
2. `Fibre_func` is added as a typed interface symbol (no extra computation rules yet).
3. Existing strict ordinary/displayed accumulation tests must continue to pass unchanged.
