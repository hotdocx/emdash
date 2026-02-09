# PLAN_EMDASH_TYPESCRIPT_ELABORATION.md

Date: 2026-02-09

## 1. Goal

Integrate emdash2-oriented functor/transformation elaboration into `emdash1/` with a testing-first workflow for iterative AI-agent loops (`LLM <-> tests/type-checker`), while ignoring parser work (`src/parser.ts` out of scope).

## 2. Scope for This Iteration

Hard in-place reset of **category-theory direction**:

- stop relying on legacy `phase1_tests` / old functorial test architecture as the canonical path,
- establish emdash2-aligned term/elaboration primitives in the core,
- build a new focused validation suite for ordinary + minimal displayed layers.

This iteration delivers:

1. Binder-mode context infrastructure (`:^f`, `:^n`, `:^o` semantics),
2. Ordinary off-diagonal transfor stable head typing (`tapp1_fapp0` equivalent),
3. Minimal displayed shell (typed globals for `Catd`, `Fibre`, `Functord`, `fdapp0`, `Transfd`, `tdapp0_fapp0`),
4. New emdash2-focused tests and validation entry in `tests/main_tests.ts`.

## 3. Design Decisions (Locked)

- Binder policy: **hybrid**
  - use functorial base binders where arrow-indexed/off-diagonal action is involved,
  - keep object-only mode available for strictly object-level contexts.
- Ordinary + displayed are implemented together (displayed shell is unavoidable for realistic context discipline).
- Parser changes are excluded.
- Strong tests are mandatory and treated as primary acceptance criteria.

## 4. Implementation Plan

## 4.1 Core Type/Context Layer (`src/types.ts`, `src/state.ts`)

- Add binder mode enum:
  - `Functorial`,
  - `Natural`,
  - `ObjectOnly`.
- Extend `Binding` with:
  - `mode?: BinderMode`,
  - `controllerCat?: Term`.
- Extend context extension helper (`extendCtx`) to carry mode/controller.
- Keep defaults backward compatible (`Functorial` when unspecified).

## 4.2 Ordinary Stable Head (off-diagonal)

- Add kernel term constructor/tag for ordinary off-diagonal transformation component:
  - `TApp1FApp0Term`.
- Typing rule target:
  - input: `eps : Transf(A,B,F,G)`, `f : Hom(A,x,y)`,
  - output type: `Hom(B, F[x], G[y])`.
- Support implicit argument insertion for this head in kernel-implicit metadata.

## 4.3 Minimal Displayed Shell (typed, non-parser)

Define globals in stdlib (typed interface layer, minimal computation assumptions):

- `Catd : Π Z:Cat, Type`
- `Fibre : Π Z:Cat, Catd Z -> Obj Z -> Cat`
- `Functord : Π Z:Cat, Catd Z -> Catd Z -> Type`
- `fdapp0 : ... -> Obj(Fibre ... E z) -> Obj(Fibre ... D z)`
- `Transfd : ... -> Type`
- `tdapp0_fapp0 : ... -> Hom(Fibre ... D z, fdapp0 FF z e, fdapp0 GG z e)`

This provides a valid displayed typing shell for elaboration tests without requiring full displayed rewrite semantics yet.

## 4.4 Engine Coverage Updates

For the new off-diagonal ordinary term:

- elaboration: infer/check typing support,
- reduction: preserve/normalize recursively,
- equality + structural equality: constructor-aware comparison,
- unification + pattern machinery: decomposition/substitution/matching support,
- printing/proof traversal: readable and exhaustive handling.

## 4.5 Tests and Validation (Primary)

Add new test suite:

- `tests/emdash2_functor_transfor_tests.ts`

Planned tests:

1. Binder mode metadata is preserved in contexts.
2. `tapp1_fapp0` term elaborates with expected type `Hom(B, F[x], G[y])`.
3. Displayed shell:
   - `fdapp0` application is typable in a fibre,
   - `tdapp0_fapp0` component is typable as a hom in displayed codomain fibre.
4. Negative test:
   - reject mismatched morphism domain/codomain in `tapp1_fapp0`.

Test runner update:

- Include new suite in `tests/main_tests.ts`.
- Remove legacy category-theory suites from the default loop:
  - `functorial_elaboration`,
  - `phase1_tests`.

Validation commands:

- `npm test --prefix emdash1`
- `EMDASH_TYPECHECK_TIMEOUT=60s make check`

## 5. Acceptance Criteria

Implementation is accepted for this iteration when:

1. New plan-driven test suite is green and included in default test loop.
2. Off-diagonal ordinary component has typed elaboration support.
3. Displayed shell globals allow end-to-end typing tests for `fdapp0` and `tdapp0_fapp0`.
4. Repository checks remain green.

## 6. Deferred to Next Iteration

- Full `tdapp1_*` / `fdapp1_*` displayed off-diagonal computational bridges,
- `homd_int` computational behavior in TS kernel,
- parser-level syntax layer,
- feature flags for draft computational regions.

