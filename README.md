## Instructions for Recreating MyLambdaPi/Emdash Project (Phase 1 Complete)

**Project Goal:** To implement "Emdash," a dependent type system specialized for computational synthetic category theory, by extending a foundational dependent type system ("MyLambdaPi"). This document outlines the current state after completing "Phase 1: Core Categories."

**Your Task:** Based on the information below, your primary goal is to reconstruct the TypeScript source code for the `MyLambdaPi/Emdash` system that successfully passes all Phase 1 tests as described. You will then be asked to continue its development.

### I. Summary of Current Specification (MyLambdaPi Core + Emdash Phase 1)

The system is a dependent type theory with a single sort `Type` (where `Type : Type`). It includes standard Π-types, λ-abstractions, application, global definitions, and hole-filling via first-order unification. Emdash Phase 1 adds core categorical constructs as primitive.

**A. MyLambdaPi Core Primitives:**

*   **Terms:**
    *   `Type`: The sort of types.
    *   `Var(name: string)`: Variables.
    *   `Lam(paramName: string, paramType?: Term, body: (v: Term) => Term)`: Lambda abstraction. `paramType` can be omitted for inference.
    *   `App(func: Term, arg: Term)`: Application.
    *   `Pi(paramName: string, paramType: Term, bodyType: (v: Term) => Term)`: Dependent function type.
    *   `Hole(id?: string)`: Metavariables for unification. Store `ref` (solution) and `elaboratedType`.
*   **Key Operations:** Bidirectional type checking (`infer`/`check`), definitional equality (`areEqual` via `whnf`), normalization (`normalize`, `whnf`), first-order unification (`unify`), constraint solving (`solveConstraints`), global definitions (`defineGlobal`), user-defined computation rewrite rules (`addRewriteRule`), and user-defined unification rules (`addUnificationRule`).

**B. Emdash Phase 1: Core Categorical Constructs:**

These are added as new primitive term constructors and types.

1.  **Sorts/Base Types for Category Theory:**
    *   `CatTerm()`
        *   **Type Theory Rule (Formation):** `Γ ⊢ CatTerm : Type`
        *   Represents the type "Cat", the type of all categories.
        *   Behaves as a "constant symbol": its tag `CatTerm` is unification-injective and cannot be the head of a user rewrite rule. `whnf(CatTerm())` is `CatTerm()`.

2.  **Object Type Constructor:**
    *   `ObjTerm(cat: Term)`
        *   **Type Theory Rule (Formation):** `Γ ⊢ C : CatTerm ⇒ Γ ⊢ ObjTerm C : Type`
        *   Represents the type `Obj C`, the type of objects in category `C`.
        *   `cat` argument must be a term of type `CatTerm`.
        *   Behaves as a "injective symbol".

3.  **Morphism (Hom-Set) Type Constructor:**
    *   `HomTerm(cat: Term, dom: Term, cod: Term)`
        *   **Type Theory Rule (Formation):**
            `Γ ⊢ C : CatTerm`
            `Γ ⊢ X : ObjTerm C`
            `Γ ⊢ Y : ObjTerm C`
            `------------------------------------ ⇒ Γ ⊢ HomTerm C X Y : Type`
        *   Represents the type `Hom C X Y`, the type of morphisms from object `X` to object `Y` in category `C`.
        *   Behaves as a "injective symbol".

4.  **Category Constructor (`MkCat_`):**
    *   `MkCat_(objRepresentation: Term, homRepresentation: Term, composeImplementation: Term)`
        *   **Type Theory Rule (Introduction):**
            `Γ ⊢ O_repr : Type`
            `Γ ⊢ H_repr : (Π X:O_repr . Π Y:O_repr . Type)`
            `Γ ⊢ C_impl : (Π X:O_repr . Π Y:O_repr . Π Z:O_repr . Π g:(H_repr Y Z) . Π f:(H_repr X Y) . (H_repr X Z))`
            `--------------------------------------------------------------------------------------------------- ⇒ Γ ⊢ MkCat_(O_repr, H_repr, C_impl) : CatTerm`
            *(Note: `(H_repr Y Z)` is shorthand for `App(App(H_repr,Y),Z)`)*
        *   Constructs a category from an object representation type, a Hom-set forming function, and a composition implementation.
        *   Behaves as a "constant symbol".
        *   **Definitional/Computational Rules (Emdash Unfolding):**
            *   `whnf(ObjTerm(MkCat_(O, H, C))) ↪ O`
            *   `whnf(HomTerm(MkCat_(O, H, C), X, Y)) ↪ App(App(H, X), Y)`
            *   `whnf(ComposeMorph(g, f, cat = MkCat_(O,H,C_impl), objX, objY, objZ)) ↪ App(App(App(App(App(C_impl, objX), objY), objZ), g), f)`
                *(This rule applies if `ComposeMorph`'s category argument reduces to an `MkCat_` term. The implicit object arguments `objX, objY, objZ` for `ComposeMorph` are used to saturate `C_impl`)*

5.  **Identity Morphism:**
    *   `IdentityMorph(obj: Term, cat_IMPLICIT?: Term)`
        *   **Type Theory Rule (Introduction):** `Γ ⊢ X : ObjTerm C ⇒ Γ ⊢ IdentityMorph(X, cat_IMPLICIT=C) : HomTerm C X X`
        *   `cat_IMPLICIT` is inferred if not provided. Elaboration fills this with a `Hole` which is then solved.
        *   The `IdentityMorph` tag is unification-injective (its arguments `obj` and `cat_IMPLICIT` are unified directly if two `IdentityMorph` terms are unified).

6.  **Morphism Composition:**
    *   `ComposeMorph(g: Term, f: Term, cat_IMPLICIT?: Term, objX_IMPLICIT?: Term, objY_IMPLICIT?: Term, objZ_IMPLICIT?: Term)`
        *   **Type Theory Rule (Introduction):**
            `Γ ⊢ f : HomTerm C X Y`
            `Γ ⊢ g : HomTerm C Y Z`
            `------------------------------------------------------------------------------------------ ⇒ Γ ⊢ ComposeMorph(g,f, cat_IMPLICIT=C, objX_IMPLICIT=X, objY_IMPLICIT=Y, objZ_IMPLICIT=Z) : HomTerm C X Z`
        *   Implicits `cat_IMPLICIT`, `objX_IMPLICIT` (domain of `f`), `objY_IMPLICIT` (codomain of `f` / domain of `g`), and `objZ_IMPLICIT` (codomain of `g`) are inferred/filled with `Hole`s during elaboration.
        *   `ComposeMorph` itself is **not** unification-injective for its `g` and `f` arguments. Equality relies on reduction.
        *   **Definitional/Computational Rules (User Rewrite Rules for Identity Laws):**
            *   `ComposeMorph(g, IdentityMorph(X, C), C, Z, X, X) ↪ g`  (where `g : Hom C Z X`)
            *   `ComposeMorph(IdentityMorph(Y, C), f, C, Y, Y, X) ↪ f`  (where `f : Hom C X Y`)
            *(These user rewrite rules are given higher priority in `whnf` than the Emdash unfolding rule for `ComposeMorph` with `MkCat_`)*

**C. Implicit Arguments and Hole Elaboration:**
*   For Emdash constructors like `IdentityMorph` and `ComposeMorph`, arguments suffixed with `_IMPLICIT` in their TypeScript definition are conceptually implicit.
*   When a term is constructed without these (e.g., `IdentityMorph(myObj)`), the `ensureImplicitsAsHoles` helper (called at the start of `infer` and `check`) mutates the term to fill these undefined slots with freshly generated `Hole` terms.
*   The `infer` or `check` logic for these constructors then adds constraints to the system. For example, for `IdentityMorph(obj, cat_hole)`, a constraint `infer(obj) === ObjTerm(cat_hole)` is generated.
*   The main `solveConstraints` function then attempts to unify these holes.

**D. "Constant Symbol" and "Injective Symbol" Implementation:**
*   **Constant Symbol (Tags):** Tags like `CatTerm`,  `MkCat_` are "constant symbols." This means:
    1.  They are unification-injective: `MkCat_(...) === MkCat_(...)` unifies arguments.
    2.  `whnf` does not attempt to find user rewrite rules where these tags are at the head of the LHS.

*   **Constant Symbol (Globals):** `defineGlobal(name, type, undefined, true)` creates an opaque global constant. It has no definition to unfold via delta reduction and cannot be the head of a user rewrite rule.
*   **Unification-Injective Symbol (Tags):** Tags like `IdentityMorph`, `ObjTerm`, `HomTerm`, (and all constant symbol tags) are unification-injective. `unify` will directly compare their arguments. `ComposeMorph` is *not* unification-injective on `f` and `g`.

## Other

The specification of the MyLambdaPi/Emdash written in Lamdapi is in the file `emdash_specification_lambdapi.lp`

Other example project of type system implementation with type inference/checking, elaboration, holes, unification are in the file `example_unification.hs`

