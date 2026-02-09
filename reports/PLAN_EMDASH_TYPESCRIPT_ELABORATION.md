# PLAN_EMDASH_TYPESCRIPT_ELABORATION.md

Date: 2026-02-09

## 1. Goal

Integrate emdash2-aligned functor/transformation elaboration in `emdash1/` with a test-first loop (`LLM <-> tests/type-checker`), and land a concrete stress-test milestone around `homd_curry` typing.

Parser work (`src/parser.ts`) remains out of scope.

## 2. Current Milestone (M1): `alias_homd_` Declaration Stress-Test

Main target:

- declare a new constant `alias_homd_` whose type is intentionally the same as `homd_curry` in the current TypeScript kernel layer,
- validate that the full binder chain needed for a potential definition skeleton is expressible:
  - `b0`, `e0`, `b1`, `f`, `e1`.

Scope of M1:

- type/declaration only,
- no computational rewrite behavior for `homd_*`,
- no parser syntax work.

## 3. Locked Design Decisions

1. Binder discipline for this milestone:
- in arrow-indexed dependent contexts we treat base binders as functorial (`:^f` intent).
- `:^o` remains available but is not the default for this stress-test path.

2. `Cat[b]` encoding in `emdash1`:
- do **not** overload `Catd_cat` name (reserved for emdash2 meaning),
- introduce a dedicated hardcoded displayed family symbol:
  - `CatConst_catd : Π Z:Cat, Catd Z`,
  - intended fibre behavior: `Fibre(Z, CatConst_catd Z, b)` is the local category-of-categories at `b`.

3. Weakening/pullback:
- general weakening/pullback infrastructure is needed long-term,
- M1 uses the hardcoded `CatConst_catd` bridge only.

## 4. Implementation Plan

## 4.1 `emdash1/src/stdlib.ts`

Add typed interface symbols:

1. `CatConst_catd`
- `CatConst_catd : Π Z:Cat, Catd Z`.

2. `homd_curry` (type-only declaration)
- `homd_curry : Π Z:Cat, Π E:Catd Z,
    Π b0:Obj Z, Obj(Fibre Z E b0) ->
    Π b1:Obj Z, Hom Z b0 b1 ->
    Obj(Fibre Z E b1) ->
    Obj(Fibre Z (CatConst_catd Z) b1)`.

3. `alias_homd_` with exactly the same type as `homd_curry`.

Notes:

- opposite variance markers from Lambdapi (`E[b0]^op`, `Hom(b0,b1)^op`) are intentionally not reified in this slice,
- this is a typing/declaration checkpoint, not computational normalization.

## 4.2 Tests (`emdash1/tests/emdash2_homd_curry_alias_tests.ts`)

Add dedicated tests:

1. Symbol declaration sanity:
- `homd_curry` and `alias_homd_` exist and their declared types are definitionally equal.

2. End-to-end application typing:
- `alias_homd_ Z E b0 e0 b1 f e1` elaborates to
  `Obj(Fibre Z (CatConst_catd Z) b1)`.
- same check for `homd_curry`.

3. Lambda skeleton expressibility:
- check a term shaped like
  `λ b0, λ e0, λ b1, λ f, λ e1, ?`
  against the expected `alias_homd_ Z E` function type.

4. Negative check:
- reject application when `f` is a hom in the wrong base category.

## 4.3 Test Runner Wiring

- include `./emdash2_homd_curry_alias_tests` in `emdash1/tests/main_tests.ts`.

## 4.4 Docs Alignment

Update docs to reflect latest binder insight:

- in arrow-indexed dependent contexts we default to functorial binder intent (`:^f`),
- `:^o` is explicit/specialized, not the default for this milestone path.

## 5. Acceptance Criteria

M1 is complete when:

1. `CatConst_catd`, `homd_curry`, `alias_homd_` are declared in stdlib with the intended types.
2. The new alias test suite is green.
3. Existing `emdash1` tests remain green.
4. `make check` on the Lambdapi side remains green.

## 6. Deferred (Next Milestones)

- computational rules/bridges for `homd_curry` / `homd_int`,
- explicit weakening/pullback elaboration insertion policy,
- displayed off-diagonal higher heads (`fdapp1_*`, `tdapp1_*`) computational bridges,
- parser-level surface syntax.
