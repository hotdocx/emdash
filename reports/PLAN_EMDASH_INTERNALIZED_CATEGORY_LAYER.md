# PLAN_EMDASH_INTERNALIZED_CATEGORY_LAYER.md

Date: 2026-02-09

## 1. Title

Internalized Category Layer for TS Elaboration (`Cat_cat`, `Catd_cat`, `Functor_cat`, `Functord_cat`, `Transf_cat`, `Transfd_cat`)

## 2. Summary

Re-architect the TypeScript kernel/elaboration layer so internalized category objects from `emdash2.lp`
are first-class in TS (dedicated terms), instead of relying on weaker surrogate typing.

Primary objective:

- support contexts corresponding to
  `A : Cat_cat, B : Cat_cat, F : Functor_cat A B, ...`
  (with `:^f` / `:^n` annotations where intended by the corresponding Lambdapi symbols).

Secondary objective:

- keep strict typing behavior first (no extra lax/coherence rewrites in this slice).

## 3. Required Clarification Captured

As requested, this slice records the binder nuance from `EMAIL.md`:

- some context arguments (e.g. `F_BA : Functor B A` in `hom_int`-style typing) should remain plain/object-level
  binders (`:` / effectively `:^o`) and **must not** be treated as functorial/natural varying binders.
- mode usage is symbol-dependent and should follow the corresponding `emdash2.lp` declaration intent.

## 4. Scope

In scope:

1. Add internalized category terms for:
   - `Cat_cat`
   - `Catd_cat`
   - `Functor_cat` (cleanup to new architecture)
   - `Functord_cat`
   - `Transf_cat`
   - `Transfd_cat`
2. Integrate them across elaboration/equality/reduction/unification/pattern/proof traversal.
3. Add tests proving these can appear in contexts as true category objects.
4. Add at least one report/docs note capturing binder-mode exceptions like `F_BA`.

Out of scope:

1. New parser syntax.
2. New lax coherence rewrites beyond existing strict test slice.
3. Backward compatibility with old/outdated pre-emdash2 TS architecture.

## 5. Core Design

Use dedicated term tags (no purely symbolic `App(Var(...),...)` only approach) for stronger kernel invariants:

- `CatCategoryTerm`               // `Cat_cat`
- `CatdCategoryTerm(base)`        // `Catd_cat base`
- `FunctorCategoryTerm(A,B)`      // `Functor_cat A B` (existing, kept as canonical)
- `FunctordCategoryTerm(Z,E,D)`   // `Functord_cat Z E D`
- `TransfCategoryTerm(A,B,F,G)`   // `Transf_cat A B F G`
- `TransfdCategoryTerm(Z,E,D,FF,GG)` // `Transfd_cat Z E D FF GG`

`Transf` / `Transfd` object-level classifiers remain available and are aligned so their values are objects in
`Transf_cat` / `Transfd_cat` respectively.

## 6. Implementation Steps

1. `types.ts`
   - add new term tags + constructors.
2. `stdlib.ts`
   - define globals for `Cat_cat`, `Catd_cat`, `Functord_cat`, `Transf_cat`, `Transfd_cat`.
   - cleanly align `Functor_cat`.
3. `elaboration.ts`
   - infer/check rules for new terms (`: Cat` outputs).
   - enforce expected argument formation (`E,D : Catd Z`, `FF,GG : Functord ...`, etc.).
4. Exhaustiveness updates:
   - `state.ts`, `reduction.ts`, `pattern.ts`, `equality.ts`, `structural.ts`, `unification.ts`, `proof.ts`.
5. Tests:
   - new context-level tests demonstrating:
     - `A : Obj(Cat_cat)`, `B : Obj(Cat_cat)`,
     - `F : Obj(Functor_cat A B)`,
     - `FF : Obj(Functord_cat Z E D)`,
     - `ϵ : Obj(Transfd_cat Z E D FF GG)`.
   - negative tests for malformed parameters.
6. Update documentation/report note with binder exception (`F_BA` plain/object-level).

## 7. Validation

1. `npm test --prefix emdash1`
2. `EMDASH_TYPECHECK_TIMEOUT=60s make check`

Both must pass.

## 8. Assumptions

1. Removing outdated legacy `Functor_cat` TS behavior is allowed.
2. This slice is strict typing/elaboration only.
3. Existing tests that were semantically weak may be tightened.
