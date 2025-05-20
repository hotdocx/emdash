# Emdash: A Dependently Typed System for Computational Synthetic Category Theory

## Abstract

Emdash is a prototype dependent type system implemented in TypeScript, designed to support computational synthetic category theory. It extends a foundational dependent type system (MyLambdaPi) with primitive constructs for categories, objects, morphisms, and their operations. The system features bidirectional type checking, hole-filling via unification with metavariables, user-defined rewrite rules, and support for higher-order abstract syntax (HOAS). This document details the architecture, implementation, analysis, and future development roadmap of Emdash, focusing on its current Phase 1 completion (core categorical constructs) and the plan towards implementing Phase 2 (functors and natural transformations) as specified in its accompanying Lambdapi formalization.

## 1. Introduction

### 1.1 Project Goal

The primary goal of the Emdash project is to develop a practical and expressive dependent type system tailored for computational synthetic category theory. This involves:

1.  **Building upon a minimal dependent type theory core:** Leveraging established principles of systems like Martin-Löf Type Theory (MLTT) or the Calculus of Constructions (CoC), simplified for prototyping (e.g., `Type : Type`).
2.  **Introducing native categorical constructs:** Instead of encoding categories from set-theoretic or type-theoretic first principles (which can be verbose and computationally expensive), Emdash defines core categorical notions like `Cat` (the type of categories), `Obj C` (the type of objects in a category `C`), and `Hom C X Y` (the type of morphisms between objects `X`, `Y` in `C`) as primitive types and term formers.
3.  **Supporting computational aspects:** The system is designed not just for formalization but also for computation within the type theory. This includes definitional equality based on reduction (including unfolding of category constructors and rewrite rules for categorical laws) and type inference/checking mechanisms that actively participate in constructing and verifying categorical structures.
4.  **Facilitating synthetic reasoning:** By providing high-level categorical primitives, Emdash aims to allow users to reason about and construct categorical arguments in a style closer to common mathematical practice, abstracting away lower-level encodings.
5.  **Extensibility:** The system is designed to be extensible with further categorical constructs (functors, natural transformations, adjunctions, etc.) and potentially user-defined theories.

The current implementation, `emdash_v2.ts`, represents the completion of "Phase 1," which focuses on these foundational core categorical structures.

### 1.2 Motivation

Category theory provides a powerful and abstract language for structuring mathematics and computer science. "Synthetic" approaches to category theory aim to internalize categorical reasoning within a formal system, treating categorical objects as primitive data rather than constructed sets or types. A *computational* synthetic approach further emphasizes the ability to execute and verify these constructions.

Traditional proof assistants, while capable of formalizing category theory, often require significant encoding effort. Emdash is motivated by the desire for a system where:

*   **Categorical concepts are first-class citizens:** Reducing the boilerplate and indirection often associated with deep encodings.
*   **Type checking performs categorical coherence checking:** For instance, ensuring that objects belong to the correct category or that morphisms compose correctly is part of the type system's built-in logic.
*   **Computation and formalization are intertwined:** Definitional equality can reflect categorical laws, and rewrite rules can implement categorical computations.
*   **Prototyping and experimentation are facilitated:** A more lightweight, scriptable environment (like TypeScript) can be advantageous for exploring new ideas in computational category theory before committing to larger, more established proof assistants.

Emdash draws inspiration from systems like Lambdapi, which also emphasizes a close relationship between syntax and semantics for computational proof, and aims to provide a similar "direct" feel for categorical constructions. The project explores how far a relatively simple dependent type core, augmented with specialized features, can go in supporting this vision.

## 2. System Architecture (`emdash_v2.ts`)

The Emdash system, implemented in `emdash_v2.ts`, is structured around a core set of data types representing terms and their operational semantics.

### 2.1 Core Data Structures

*   **`Term`:** The fundamental data type for all expressions in the system. It's a discriminated union (`BaseTerm`) encompassing:
    *   **Standard TT constructs:** `Type`, `Var`, `Lam` (lambda abstraction), `App` (application), `Pi` (dependent function type).
    *   **Metavariables:** `Hole` (representing unsolved parts of terms, with `id`, optional `ref` to its solution, and `elaboratedType`).
    *   **Emdash Phase 1 Categorical Constructs:**
        *   `CatTerm`: The type of categories.
        *   `ObjTerm(cat: Term)`: The type of objects in a category `cat`.
        *   `HomTerm(cat: Term, dom: Term, cod: Term)`: The type of morphisms.
        *   `MkCat_(objRepresentation: Term, homRepresentation: Term, composeImplementation: Term)`: Constructor for concrete categories.
        *   `IdentityMorph(obj: Term, cat_IMPLICIT?: Term)`: Identity morphism.
        *   `ComposeMorph(g: Term, f: Term, cat_IMPLICIT?: Term, objX_IMPLICIT?: Term, objY_IMPLICIT?: Term, objZ_IMPLICIT?: Term)`: Composition of morphisms.
    ```typescript
    type BaseTerm =
        | { tag: 'Type' }
        | { tag: 'Var', name: string }
        // ... other core terms
        | { tag: 'CatTerm' }
        | { tag: 'ObjTerm', cat: Term }
        // ... other Emdash terms
    type Term = BaseTerm;
    ```

*   **`Context` (`Ctx`)**: A list of `Binding`s (`{ name: string, type: Term }`), representing the typing context. It's extended using `extendCtx` and queried with `lookupCtx`. This is a standard representation for contexts in type theory.

*   **`GlobalDef` and `globalDefs`**: A `Map` storing global definitions (`name`, `type`, optional `value`, and `isConstantSymbol` flag). `defineGlobal` adds to this map. This allows for defining constants and terms that can be unfolded (delta-reduction).

*   **`Constraint`**: Represents a unification constraint ` { t1: Term, t2: Term, origin?: string } `. These are collected during type checking and solved by the unifier.

*   **`RewriteRule` and `userRewriteRules`**: Stores user-defined computation rules (`{ name: string; patternVars: PatternVarDecl[]; lhs: Term; rhs: Term; }`). These are applied during `whnf`.

*   **`UnificationRule` and `userUnificationRules`**: Stores user-defined unification rules (`{ name: string; patternVars: PatternVarDecl[]; lhsPattern1: Term; lhsPattern2: Term; rhsNewConstraints: Array<{ t1: Term, t2: Term }>; }`). These are used by `unify` to break down complex unification problems or guide the unification process.

### 2.2 Key Algorithms

#### 2.2.1 Normalization and Definitional Equality

*   **`whnf(term: Term, ctx: Context)` (Weak Head Normal Form):**
    *   Reduces a term to its weak head normal form. This is the core computational engine.
    *   Order of operations:
        1.  **Hole Resolution:** Dereferences solved holes (`getTermRef`).
        2.  **User-Defined Rewrite Rules:** Attempts to apply rules from `userRewriteRules` if the term is not a "kernel constant symbol". `matchPattern` is used here. If a rule applies and changes the term structurally (checked by `areStructurallyEqualNoWhnf`), `whnf` restarts.
        3.  **Head-Specific Reductions:**
            *   **Beta Reduction:** `(λx. body) arg` ↪ `body[arg/x]`.
            *   **Categorical Beta Reductions (Emdash Unfolding):**
                *   `ObjTerm(MkCat_(O, H, C))` ↪ `O`
                *   `HomTerm(MkCat_(O, H, C), X, Y)` ↪ `App(App(H, X), Y)`
                *   `ComposeMorph(g, f, cat=MkCat_(...), ...)` ↪ `App(App(...C_impl...), g), f)` (if implicits are filled and `cat` reduces to `MkCat_`).
            *   **Delta Reduction:** Unfolds global definitions (`Var`s that have a `value` and are not `isConstantSymbol`).
    *   The `whnf` function iterates these steps until no more reductions can be applied to the head of the term or `MAX_WHNF_ITERATIONS` is reached.
    *   A new function `areStructurallyEqualNoWhnf` was introduced to check if a rewrite rule application resulted in a structural change without further reduction, preventing non-productive rewrite loops.

*   **`normalize(term: Term, ctx: Context)`:**
    *   Reduces a term to its normal form by recursively calling `whnf` on the head and then `normalize` on the subterms.
    *   For `Lam` and `Pi` terms, it normalizes types and bodies under extended contexts.

*   **`areEqual(t1: Term, t2: Term, ctx: Context)`:**
    *   Determines definitional equality by reducing both terms to `whnf` and then comparing their structure. For `Lam` and `Pi` types, it uses fresh variables to compare bodies/body types under extended contexts. It handles solved holes via `getTermRef`.

#### 2.2.2 Type Inference and Checking (Bidirectional Typing)

*   **`elaborate(term: Term, expectedType?: Term, initialCtx?: Context)`:**
    *   The main entry point for type checking.
    *   Resets global `constraints`, `nextHoleId`, and `nextVarId`.
    *   Calls `check` if `expectedType` is provided, otherwise calls `infer`.
    *   Calls `solveConstraints` to attempt to unify all generated constraints.
    *   If successful, returns the normalized elaborated term and its normalized type.
    *   Handles errors by throwing exceptions.

*   **`infer(ctx: Context, term: Term)`:**
    *   Infers the type of a given `term`.
    *   **Implicit Handling:** Calls `ensureImplicitsAsHoles` to fill undefined `_IMPLICIT` arguments in `IdentityMorph` and `ComposeMorph` with fresh holes.
    *   Rules implemented:
        *   `Var`: Looks up type in `ctx` or `globalDefs`.
        *   `Type`: `Type : Type`.
        *   `Hole`: If `elaboratedType` exists, returns it. Otherwise, creates a new hole `?h_type` for its type, sets `hole.elaboratedType = ?h_type`, and returns `?h_type`.
        *   `App(func, arg)`: Infers type of `func`. Expects it to be a `Pi` type `(Π P : A. B)` (or a hole constrained to be one). Checks `arg` against `A`. Returns `B[arg/P]`.
        *   `Lam(param, body)`:
            *   If annotated (`paramType` exists): Checks `paramType : Type`. Infers type of `body` under `ctx` extended with `param : paramType`. Returns `(Π param : paramType. typeof(body))`.
            *   If unannotated: Creates a fresh hole `?paramType` for the parameter type. Annotates the lambda term itself with this hole. Infers type of `body` under `ctx` extended with `param : ?paramType`. Returns `(Π param : ?paramType. typeof(body))`. This self-annotation is crucial for solving the parameter type.
        *   `Pi(param, paramType, bodyType)`: Checks `paramType : Type`. Checks `bodyType` (instantiated) against `Type` under `ctx` extended with `param : paramType`. Returns `Type`.
        *   **Emdash Categorical Constructs:** Implements formation rules by checking subterms and returning the appropriate type (e.g., `CatTerm() : Type`, `ObjTerm(C) : Type` if `C : CatTerm`). For `IdentityMorph` and `ComposeMorph`, it adds constraints to relate their implicit arguments (now holes) with the types of their explicit arguments. For example, for `IdentityMorph(obj, cat_hole)`, a constraint `infer(obj) === ObjTerm(cat_hole)` is generated.

*   **`check(ctx: Context, term: Term, expectedType: Term)`:**
    *   Checks if `term` has `expectedType`.
    *   **Implicit Handling:** Calls `ensureImplicitsAsHoles`.
    *   `whnf`s `expectedType`.
    *   **Special Lambda Rule:** If `term` is an unannotated `Lam` and `expectedType` is `Pi A B`, it annotates the `Lam` with `A` and recursively checks the `Lam` body against `B` (deep elaboration).
    *   **Hole Rule:** If `term` is a `Hole`, its `elaboratedType` (if not present, it's set to `expectedType`) is inferred and constrained to be equal to `expectedType`. Also checks `expectedType : Type`.
    *   **Special Emdash Rules:** For `IdentityMorph` and `ComposeMorph` being checked against an `HomTerm`, it directly generates constraints between the implicits of the constructor and the components of the expected `HomTerm`. This is a more direct way to guide unification.
    *   **Default Rule:** Infers the type of `term` (`inferredType`) and adds a constraint `inferredType === expectedType`.

*   **`ensureImplicitsAsHoles(term: Term)`:**
    *   Mutates `IdentityMorph` and `ComposeMorph` terms to replace `undefined` implicit arguments with new `Hole`s. This is done at the beginning of `infer` and `check`.

#### 2.2.3 Unification and Constraint Solving

*   **`unify(t1: Term, t2: Term, ctx: Context)`:**
    *   Attempts to unify `t1` and `t2`. Returns `UnifyResult` (`Solved`, `Failed`, `RewrittenByRule`, `Progress`).
    *   **Hole Cases:** If `t1` (or `t2`) is a `Hole ?h`, it attempts `unifyHole(?h, whnf(t2))`.
        *   `unifyHole(?h, term)`: Solves `?h := term` if `term` is not `?h` and `term` does not contain `?h` (occurs check via `termContainsHole`). If `term` is also a hole `?h'`, it orders them by ID to avoid cycles.
    *   **Injective Structural Unification (Pre-WHNF):** If `t1` and `t2` have the same tag and the tag is in `EMDASH_UNIFICATION_INJECTIVE_TAGS` (e.g., `CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`, `IdentityMorph`), it recursively calls `unifyArgs` on their arguments. If this fails, it falls through to WHNF.
    *   **General Case (Post-WHNF):**
        *   Reduces `t1` and `t2` to `whnf` (`rt1_whnf`, `rt2_whnf`).
        *   Re-checks equality and hole cases.
        *   If tags differ and neither is a hole, tries `tryUnificationRules`.
        *   If tags are the same:
            *   For injective symbols (if pre-WHNF failed or was skipped): Retries `unifyArgs` with arguments from `rt1_whnf`, `rt2_whnf`.
            *   For non-injective symbols (e.g., `App`, `Lam`, `Pi`, `ComposeMorph`): Recursively unifies components. For `Lam`/`Pi`, this involves unifying under extended contexts with fresh variables.
            *   If structural unification fails, calls `tryUnificationRules`.
    *   `EMDASH_CONSTANT_SYMBOLS_TAGS`: `CatTerm`, `MkCat_`. Used to block rewrite rules.
    *   `EMDASH_UNIFICATION_INJECTIVE_TAGS`: `IdentityMorph`, `CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`.

*   **`tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number)`:**
    *   Iterates through `userUnificationRules`.
    *   For each rule, attempts to match `(rule.lhsPattern1, rule.lhsPattern2)` against `(t1, t2)` and `(t2, t1)` using `matchPattern`.
    *   If a match is found, `applyAndAddRuleConstraints` is called to instantiate the RHS constraints with the substitution and add them to the global `constraints` list. Returns `UnifyResult.RewrittenByRule`.
    *   If no rule applies, returns `UnifyResult.Failed`.

*   **`solveConstraints(ctx: Context)`:**
    *   Iteratively processes the global `constraints` list.
    *   For each constraint `{t1, t2}`:
        *   If `areEqual(getTermRef(t1), getTermRef(t2))`, removes the constraint.
        *   Otherwise, calls `unify(getTermRef(t1), getTermRef(t2))`.
            *   If `Solved` or `Progress`: Continues.
            *   If `RewrittenByRule`: The original constraint is removed (new ones are added by the rule).
            *   If `Failed`: Reports an error and returns `false`.
    *   The loop continues as long as changes are made (`changedInOuterLoop`) or max iterations are not reached.
    *   Returns `true` if all constraints are eventually removed/solved, `false` otherwise.

#### 2.2.4 Pattern Matching and Rewriting

*   **`matchPattern(pattern: Term, termToMatch: Term, ctx: Context, patternVarDecls: PatternVarDecl[], currentSubst?: Substitution)`:**
    *   Matches a `pattern` term (which may contain pattern variables) against `termToMatch`.
    *   Pattern variables are identified by `isPatternVarName`.
    *   If `pattern` is a pattern variable `pvar`:
        *   If `pvar` is `_` (wildcard), succeeds.
        *   If `pvar` is already in `subst`, checks if `termToMatch` is structurally equal (via `areStructurallyEqualNoWhnf`) to the existing binding.
        *   Otherwise, adds `pvar := termToMatch` to `subst`.
    *   Otherwise, compares tags. If different, fails.
    *   Recursively matches subterms. For HOAS terms (`Lam`, `Pi`), bodies are compared using `areEqual` under fresh variables, as direct structural matching of functions is not feasible.
    *   Returns the `Substitution` map or `null` on failure.

*   **`applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[])`:**
    *   Applies a `Substitution` to a `term` (typically the RHS of a rewrite rule).
    *   If `term` is a pattern variable, replaces it with its binding in `subst`.
    *   Otherwise, recursively applies substitution to subterms. For HOAS, the substitution is applied inside the new HOAS function body.

*   **Rewrite Rule Application (in `whnf`):**
    *   Iterates `userRewriteRules`.
    *   For each rule, calls `matchPattern(rule.lhs, currentTerm, ...)`.
    *   If successful, calls `applySubst(rule.rhs, subst, ...)` to get the new term.
    *   Checks if `areStructurallyEqualNoWhnf(rhsApplied, termBeforeThisRuleAttempt)` to ensure actual progress.
    *   If progress is made, `currentTerm` is updated, and `whnf` restarts.

#### 2.2.5 Higher-Order Abstract Syntax (HOAS)

*   `Lam` and `Pi` terms use JavaScript functions to represent their bodies:
    *   `Lam(paramName, paramType?, body: (v: Term) => Term)`
    *   `Pi(paramName, paramType, bodyType: (v: Term) => Term)`
*   **Instantiation:** When operating on the body (e.g., in `infer`, `check`, `areEqual`, `normalize`, `matchPattern`, `applySubst`), the body function is called with a fresh `Var` (e.g., `lam.body(Var(paramName))`).
*   **Equality (`areEqual`):** Compares HOAS bodies by instantiating them with the same fresh variable and recursively calling `areEqual` on the results.
*   **Matching (`matchPattern` for `Lam`/`Pi`):** Parameter types are matched structurally. Bodies are compared using `areEqual` after instantiation with a fresh variable. This means patterns cannot directly bind variables *within* a HOAS body; the body is treated more opaquely for matching its internal structure unless it's a concrete function.
*   **Substitution (`applySubst`):** For `Lam`/`Pi`, returns a new `Lam`/`Pi` whose JavaScript body function, when called, applies the substitution to the result of the original body function. This effectively pushes the substitution inside the HOAS scope.

#### 2.2.6 Implicit Argument Mechanism

*   Term constructors `IdentityMorph` and `ComposeMorph` have fields like `cat_IMPLICIT`, `objX_IMPLICIT`, etc.
*   **`ensureImplicitsAsHoles(term: Term)`:** Called at the start of `infer` and `check`. If these `_IMPLICIT` fields are `undefined` in a term being processed, this function mutates the term to fill these slots with freshly generated `Hole`s. Hole names are generated with hints (e.g., `_cat_of_objName`).
*   **Constraint Generation:**
    *   **`infer` for `IdentityMorph(obj, cat_hole)`:** Generates `infer(obj) === ObjTerm(cat_hole)`.
    *   **`infer` for `ComposeMorph(g, f, cat_h, X_h, Y_h, Z_h)`:** Generates `check(f, Hom(cat_h, X_h, Y_h))` and `check(g, Hom(cat_h, Y_h, Z_h))`.
    *   **`check` for `IdentityMorph(obj, cat_h)` against `HomTerm(C, D, E)`:** Generates `cat_h === C`, `obj === D`, `obj === E`.
    *   **`check` for `ComposeMorph(g, f, cat_h, X_h, Y_h, Z_h)` against `HomTerm(C, D, E)`:** Generates `cat_h === C`, `X_h === D`, `Z_h === E`, and then checks `f` against `Hom(cat_h, X_h, Y_h)` and `g` against `Hom(cat_h, Y_h, Z_h)`.
*   **Solving:** The `solveConstraints` function attempts to unify these holes along with other constraints. The filled-in values for these implicits become part of the elaborated term.

This architecture provides a foundation for dependent type checking with integrated support for categorical reasoning through specialized term constructors and tailored inference/checking logic.

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

