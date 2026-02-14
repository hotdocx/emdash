# PLAN_EMDASH_TYPESCRIPT_ELABORATION_MODED_HOMD_CURRY.md

Date: 2026-02-09

## 1. Title

Mode-Enforced Eta-Copy of `homd_curry` with Category-Theoretic Stress Tests

## 2. Summary

Implement strict binder-mode enforcement in elaboration so a fake eta-expanded copy of `homd_curry` can be declared and defined with explicit modes:

- `b0, b1` functorial (`:^f`)
- `e0, f, e1` natural (`:^n`)

and validated through real category-theoretic typing (`Catd`/`Fibre`/`Hom`) rather than metadata-only checks.

## 3. Public Interface Changes

1. Add mode metadata to binder terms:
- `Lam` gains optional `mode`, `controllerCat`
- `Pi` gains optional `mode`, `controllerCat`

2. Add helper constructors:
- `LamMode(...)`
- `PiMode(...)`

3. Add stdlib defined symbol:
- `homd_curry_eta_copy`
- type equal to `homd_curry`
- value is eta-expanded lambdas ending with `homd_curry` reapplication

## 4. Elaboration Rules

1. Lambda-vs-Pi checking resolves binder metadata from lambda/expected type and rejects conflicts.
2. Context extension propagates mode/controller metadata.
3. Hom-binder discipline:
- `:^o` binders cannot bind hom arrows
- Hom endpoints must be functorial in arrow-indexed contexts
- controller category must match hom base category when provided

## 5. Test Scenarios

1. `homd_curry_eta_copy` exists and has type equal to `homd_curry`.
2. `homd_curry_eta_copy Z E b0 e0 b1 f e1` has expected codomain type and is convertible with `homd_curry ...`.
3. Mode mismatch failure:
- `b0` as object-only where expected functorial fails.
4. Mode mismatch failure:
- `e0` as functorial where expected natural fails.
5. Hom discipline failure:
- object-only endpoints used in `f : Hom(Z,b0,b1)` fail.
6. Existing mismatch test for wrong base-arrow category remains failing as expected.

## 6. Assumptions / Defaults

1. This slice enforces exact modes for the eta-copy binder chain via expected `Pi` metadata.
2. Parser/surface string syntax remains out of scope.
3. `CatConst_catd` remains a temporary hardcoded weakening surrogate for `Cat[b]`.
4. Computational rules for `homd_curry` are still deferred; this slice targets elaboration correctness.
