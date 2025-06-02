## Task: Refactor Category Theory Primitives (mkCat_, identity_morph, compose_morph)

**Phase 1: Removal from Kernel and Core File Updates**

*   **`src/core_types.ts`**:
    *   Removed `MkCat_`, `IdentityMorph`, `ComposeMorph` from `BaseTerm` union.
    *   Removed factory functions: `MkCat_()`, `IdentityMorph()`, `ComposeMorph()`.
*   **`src/core_logic.ts`**:
    *   Removed cases for `MkCat_`, `IdentityMorph`, `ComposeMorph` from:
        *   `areStructurallyEqualNoWhnf`
        *   `whnf` (including specific reductions involving these terms like `ObjTerm` reducing via `MkCat_`, and `HomTerm` via `MkCat_`, and the `ComposeMorph` case).
        *   `normalize`
        *   `areEqual`
        *   `termContainsHole`
        *   `unify` (structural unification and main switch cases)
        *   `collectPatternVars`
    *   Removed the `isActuallyInjectiveHead` helper function as its primary use was for `ComposeMorph`.
*   **`src/core_elaboration.ts`**:
    *   Removed `IdentityMorphType` and `ComposeMorphType` (extracted type aliases).
    *   Removed cases for `MkCat_`, `IdentityMorph`, `ComposeMorph` from:
        *   `infer`
        *   `matchPattern`
        *   `applySubst`
        *   `printTerm`
    *   Ensured `ensureKernelImplicitsPresent` no longer references these terms (they had no implicit fields defined in `KERNEL_IMPLICIT_SPECS` anyway).
*   **`src/core_kernel_metadata.ts`**:
    *   Removed `IdentityMorphTypeExt` and `ComposeMorphTypeExt`.
    *   Removed specifications for `IdentityMorph` and `ComposeMorph` from `KERNEL_IMPLICIT_SPECS` array.
*   **`src/core_context_globals.ts`**:
    *   Removed `MkCat_`, `IdentityMorph`, `ComposeMorph` from imports from `../core_types`.
    *   Removed these tags from `EMDASH_CONSTANT_SYMBOLS_TAGS` and `EMDASH_UNIFICATION_INJECTIVE_TAGS` sets.

**Phase 2: Redefinition as Global Symbols and Rules in `src/core_context_globals.ts` (within `setupPhase1GlobalsAndRules`)**

*   **Global Symbol Definitions**:
    *   `mkCat_`: Defined as a global constant symbol (`isConstantSymbol: true`, `isInjective: true`).
        *   Type: `Π (Obj_repr : Type) (Hom_repr : Π (X: Obj_repr) (Y: Obj_repr), Type) (compose_impl : Π [X_obj: Obj_repr], Π [Y_obj: Obj_repr], Π [Z_obj: Obj_repr], Π (g_morph: Hom_repr Y_obj Z_obj), Π (f_morph: Hom_repr X_obj Y_obj), Hom_repr X_obj Z_obj), Cat`
    *   `identity_morph`: Defined as a global injective symbol (`isConstantSymbol: false`, `isInjective: true`).
        *   Type: `Π[A : Cat], Π(X: Obj A), Hom X X`
    *   `compose_morph`: Defined as a global symbol (`isConstantSymbol: false`, `isInjective: false`).
        *   Type: `Π [A : Cat], Π [X: Obj A], Π [Y: Obj A], Π [Z: Obj A], Π (g: Hom Y Z), Π (f: Hom X Y), Hom X Z`
*   **Rewrite Rules Added/Updated**:
    *   `Obj_mkCat_eval`: `@Obj (mkCat_ $O $H $C) ↪ $O`
    *   `Hom_mkCat_eval`: `@Hom (mkCat_ $O $H $C) $X $Y ↪ ($H $X $Y)`
    *   `compose_mkCat_eval`: `@compose_morph (mkCat_ $O $H $C) ↪ $C`
    *   `comp_f_idX_fwd` (replaces old kernel behavior): `compose_morph $f (identity_morph $X) @ A ↪ $f`
    *   `comp_idY_f_fwd_new` (replaces old kernel behavior): `compose_morph (identity_morph $Y) $f @ A ↪ $f`
*   **Unification Rule Added**:
    *   `unif_hom_cov_fapp1_compose`: `(fapp1 (hom_cov $W) $a) $f ≡ compose_morph $a $f ↪ [ tt ≡ tt ]`
        *   Pattern Vars: `["$A_cat", "$W_obj", "$X_obj", "$Y_obj", "$Z_obj", "$a_morph", "$f_morph"]`
        *   LHS1: `App(FMap1Term(App(App(Var("hom_cov"), Var("$A_cat"), Icit.Impl), Var("$W_obj"), Icit.Expl), Var("$a_morph"), Var("$A_cat"), SetTerm(), Var("$Y_obj"), Var("$Z_obj")), Var("$f_morph"))`
        *   LHS2: `App(App(App(App(App(App(Var("compose_morph"), Var("$A_cat"), Icit.Impl), Var("$X_obj"), Icit.Impl), Var("$Y_obj"), Icit.Impl), Var("$Z_obj"), Icit.Impl), Var("$a_morph"), Icit.Expl), Var("$f_morph"), Icit.Expl)`
        *   RHS Constraints: `[{ t1: Type(), t2: Type() }]`

**Status**:

*   Implemented: All listed changes have been applied to the codebase.
*   Remaining: Thorough testing is required to ensure the refactoring didn't introduce regressions and that the new rules and definitions behave as expected. Potential linter errors in other unedited files might arise if they were using the removed kernel terms directly.
*   Next: Proceed with testing. If successful, this task can be considered complete. 