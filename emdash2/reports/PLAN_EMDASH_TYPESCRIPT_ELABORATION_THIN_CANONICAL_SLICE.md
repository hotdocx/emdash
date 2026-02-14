# PLAN_EMDASH_TYPESCRIPT_ELABORATION_THIN_CANONICAL_SLICE.md

Date: 2026-02-09

## 1. Title

Category-Theoretic Elaboration Slice for Lax Displayed Arrow-Action

## 2. Summary

Implement a thin canonical category-theoretic slice (not parser work) that extends current
mode-discipline elaboration to typed, first-class off-diagonal displayed action terms:

- displayed functor arrow-action: `FF₁(σ)`
- displayed transfor off-diagonal component: `ϵ_(σ)`

The milestone target is to type-check and elaborate eta/skeleton terms that mirror `EMAIL.md`
judgments, while keeping computational normalization laws (exchange/accumulation rewrites)
out of this slice.

## 3. Scope and Non-Scope

In scope:

- TS core term/type constructors and elaboration checks for displayed off-diagonal action.
- Fibred `Cat_cat` weakening surrogate consistency via `CatConst_catd` path.
- Stress-test declarations/definitions equivalent in shape to `homd_curry`-style eta expansion and off-diagonal usage.

Out of scope:

- Parser/string grammar (`emdash1/src/parser.ts` remains ignored).
- New Lambdapi rewrite rules for exchange/triangle normalization in this milestone.

## 4. Public Interface / Type Changes

1. `emdash1/src/types.ts`
- Add explicit displayed off-diagonal constructors (canonical AST nodes), with stable-head intent:
  - `FDApp1Term`: models `FF₁(σ)`.
  - `TDApp1Term`: models `ϵ_(σ)` in displayed setting.
- Keep existing `LamMode`/`PiMode` metadata and ensure these constructors include enough fields to recover:
  - base category `Z`,
  - displayed families `E`, `D`,
  - relevant indices (`z`, `z'`, `f`, `e`, `e'`, `σ`),
  - source functor/transfor term (`FF` or `ϵ`).

2. `emdash1/src/stdlib.ts`
- Declare corresponding stable-head globals with explicit dependent types:
  - displayed functor off-diagonal eliminator head (`fdapp1_*` family naming consistent with current stdlib style),
  - displayed transfor off-diagonal eliminator head (`tdapp1_*` family naming consistent with current stdlib style).
- Ensure codomain expresses dependent hom over base arrow (`→_f`) through existing `Hom`/`Fibre` encodings.
- Keep `CatConst_catd` as the hardcoded fibred `Cat_cat` weakening surrogate for this phase.

3. `emdash1/src/elaboration.ts`
- Add bidirectional typing/elaboration rules for new AST constructors to canonical stable-head apps.
- Enforce mode/controller discipline for the EMAIL-style context:
  - base objects `z,z'` must be `:^f`,
  - base arrow `f` is natural/arrow-indexed,
  - fibre objects `e,e'` natural in arrow-indexed context,
  - displayed arrow witness `σ` functorial over the base arrow.
- Add controller consistency checks:
  - if a term claims to live over base `Z`, endpoints and base arrow must align with `Z`;
  - reject accidental use of `Catd_cat` semantics where `CatConst_catd` is required.
- Keep existing hom-endpoint object-only rejection behavior.

4. `emdash1/src/state.ts`, `emdash1/src/reduction.ts`, `emdash1/src/pattern.ts`
- Ensure mode/controller metadata propagation remains lossless for any new binder forms/constructor normalization paths.
- Preserve constructor fields under substitution and normalization.

## 5. Implementation Steps

1. Introduce new term constructors and pretty-print support.
2. Add stdlib declarations for displayed off-diagonal eliminator heads with precise Pi chains.
3. Implement elaboration inference/checking for those constructors:
- infer required implicit parameters from terms when possible,
- otherwise generate constraints and fail with explicit mode/controller diagnostics.
4. Wire conversion to canonical kernel-headed applications only (no macro expansion to non-canonical forms).
5. Add targeted negative checks for controller/category mismatches and binder-mode misuse.
6. Run full regression (`npm test --prefix emdash1`, `EMDASH_TYPECHECK_TIMEOUT=60s make check`).

## 6. Test Plan

1. Extend `emdash1/tests/emdash2_functor_transfor_tests.ts` with positive cases:
- type `FF₁(σ)` in context shape:
  `z:^f Z, e:^n E[z], z':^f Z, f:^n z→z', e':^n E[z'], σ:^f e→_f e'`
  and verify codomain:
  `FF[e] →_f FF[e']`.
- type `ϵ_(σ)` with:
  `ϵ : Transfd FF GG`
  and verify codomain:
  `FF[e] →_f GG[e']`.

2. Add equivalence/canonicalization checks:
- explicit constructor elaborates to same canonical stable head app as manual `App(...)` construction.

3. Add negative tests:
- wrong base category for `f`,
- wrong fibre family for `e/e'`,
- object-only binder at arrow-indexed endpoint rejected,
- controller mismatch (`Z` vs `Z_bad`) rejected.

4. Keep and re-run existing `homd_curry` alias/eta-copy tests unchanged as regression anchors.

5. Optional stress-test:
- define a fake eta-expanded alias that starts with mode-annotated lambdas and ends by reapplying the canonical head for off-diagonal action.

## 7. Acceptance Criteria

1. All existing tests pass unchanged.
2. New off-diagonal displayed functor/transfor tests pass (positive + negative).
3. `make check` still passes for `emdash2.lp`.
4. No parser changes are required to use/test this milestone.
5. Errors for invalid contexts mention mode/controller mismatch clearly (contain `Mode error` or category/controller mismatch text).

## 8. Assumptions and Defaults

1. Chosen scope is the thin canonical slice.
2. `CatConst_catd` remains the endorsed fibred weakening surrogate for `Cat_cat` in TS elaboration for now.
3. `:^o` remains exceptional; arrow-indexed dependent contexts default to `:^f`/`:^n` discipline.
4. Computational normalization laws (strict naturality accumulation/exchange, adjunction triangles) are deferred to the next milestone, after constructor/elaboration stability is validated.
