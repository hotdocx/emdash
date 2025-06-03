## Task: Refactor Functor Specification

**Objective:** Split the Functor concept into `Functor A B` (the type of functors) and `Functor_cat A B` (the category of functors).

### Implemented Changes:

1.  **`src/core_types.ts`**:
    *   Introduced `FunctorTypeTerm { domainCat: Term, codomainCat: Term }` to represent `Functor A B` (a TYPE).
    *   The existing `FunctorCategoryTerm { domainCat: Term, codomainCat: Term }` now unambiguously represents `Functor_cat A B` (a Cat).
    *   Updated comments in `FMap0Term`, `FMap1Term`, `NatTransTypeTerm` to reflect that their `functor` (or `functorF`/`functorG`) arguments are terms of type `FunctorTypeTerm`.

2.  **`src/core_state.ts`**:
    *   Added `FunctorTypeTerm` to imports.
    *   Updated `printTerm` to correctly display `FunctorTypeTerm` as `(FunctorType ...)`.
    *   Included `FunctorTypeTerm` in `EMDASH_UNIFICATION_INJECTIVE_TAGS`.
    *   Included `FunctorTypeTerm` in `isKernelConstantSymbolStructurally` switch case, treating it as a structural constant.

3.  **`src/core_logic.ts`**:
    *   Added `FunctorTypeTerm` to imports.
    *   Added handling for `FunctorTypeTerm` in:
        *   `areStructurallyEqualNoWhnf`
        *   `whnf` (for reducing sub-terms)
        *   `normalize`
        *   `areEqual`
        *   `termContainsHole`
        *   `collectPatternVars`
    *   In `unify`:
        *   Added `FunctorTypeTerm` to the main switch for unifying two `FunctorTypeTerm`s.
        *   Implemented the kernel unification rule: `Obj Z === FunctorTypeTerm A B` (and its symmetric version) now adds a constraint `Z === FunctorCategoryTerm A B`.
    *   The existing `whnf` rule for `HomTerm` (where `HomTerm(FunctorCategoryTerm A B, F, G)` becomes `NatTransTypeTerm(A, B, F, G)`) correctly implements `rule @Hom (Functor_cat _ _) $F $G ↪ Transf $F $G`.

4.  **`src/core_elaboration.ts`**:
    *   Added `FunctorTypeTerm` to imports and created `FunctorTypeTermType` alias.
    *   `infer`:
        *   Added a case to infer the type of a `FunctorTypeTerm` as `Type()`.
        *   Modified `FMap0Term`, `FMap1Term`, `NatTransTypeTerm` inference: the `expectedFunctorType` for functor arguments (`F`, `G`) is now `FunctorTypeTerm` (previously was `ObjTerm(FunctorCategoryTerm(...))`).
        *   Modified `HomCovFunctorIdentity` inference: its inferred type is now `FunctorTypeTerm domainCat SetTerm()` (previously `ObjTerm(FunctorCategoryTerm(...))`).
    *   Added `FunctorTypeTerm` handling to `matchPattern` and `applySubst`.
    *   Fixed a minor linter error related to variable scoping in an error message.

5.  **`src/core_context_globals.ts`**:
    *   Added `FunctorTypeTerm` to imports.
    *   Modified `defineGlobal("Functor", ...)`:
        *   Its type is now `Π(A : Cat), Π(B : Cat), Type()`.
        *   Its value constructs a `FunctorTypeTerm(A, B)`.
    *   Added `defineGlobal("Functor_cat", ...)`:
        *   Its type is `Π(A : Cat), Π(B : Cat), CatTerm()`.
        *   Its value constructs a `FunctorCategoryTerm(A, B)`.
    *   Modified `defineGlobal("Transf", ...)`:
        *   The `F` and `G` parameters are now expected to be of type `FunctorTypeTerm`.
    *   Modified `defineGlobal("hom_cov", ...)`:
        *   Its resulting type is now `FunctorTypeTerm(A_cat_val, SetTerm())`.

### Remaining Work / Next Steps:

*   Thorough testing of these changes is required, especially focusing on type inference, unification, and rewrite rules involving functors and natural transformations.
*   Review other parts of the `emdash_specification_lambdapi.lp` to see if any other rules or definitions are impacted by this change or need to be implemented/adjusted in light of this refactoring.
*   The specification also mentions `Functor_Type` (e.g., `constant symbol Functor_Type : Π(A : Cat), Π(B : Cat), Type; rule τ (@Functor_Type $A $B) ↪ @Functor $A $B;`). This was not explicitly implemented as a separate global constant since `Functor` itself is now defined to return `Type()` and its value is `FunctorTypeTerm`. This seems to align with the principle of not needing `_Type` versions in TypeScript if the main symbol already serves this role. This decision can be revisited if necessary.

We are ready to archive this Task file and move on to the next main Task if the user confirms these changes are satisfactory after review and testing. 