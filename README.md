Okay, I will generate an updated `README.md` file that incorporates the new design, architecture, and implementation details, especially focusing on the features around implicit arguments, pattern elaboration, kernel constructor implicits, and unification with injective symbols.

This new `README.md` will synthesize information from the previous version and the details outlined in `TASK_SCRATCHPAD_002_Implicit_Arguments_Pattern_Elaboration_Injectivity.md`.

```markdown
# Emdash: A Dependently Typed System for Computational Synthetic Category Theory

## Abstract

Emdash is a prototype dependent type system implemented in TypeScript, designed to support computational synthetic category theory. It extends a foundational dependent type system with primitive constructs for categories, objects, morphisms, and their operations. The system features bidirectional type checking, hole-filling via unification with metavariables, user-defined rewrite rules, and support for higher-order abstract syntax (HOAS). A key recent enhancement includes a robust and systematic approach to implicit arguments for core term constructors (`Lam`, `App`, `Pi`) and kernel-defined categorical primitives, alongside an improved pattern elaboration mechanism for rewrite rules and injectivity controls for unification. This document details the architecture, implementation, analysis, and future development roadmap of Emdash.

## 1. Introduction

### 1.1 Project Goal

The primary goal of the Emdash project is to develop a practical and expressive dependent type system tailored for computational synthetic category theory. This involves:

1.  **Building upon a minimal dependent type theory core:** Leveraging established principles of systems like Martin-Löf Type Theory (MLTT) or the Calculus of Constructions (CoC), simplified for prototyping (e.g., `Type : Type`).
2.  **Introducing native categorical constructs:** Instead of encoding categories from set-theoretic or type-theoretic first principles, Emdash defines core categorical notions like `Cat` (the type of categories), `Obj C` (the type of objects in a category `C`), and `Hom C X Y` (the type of morphisms between objects `X`, `Y` in `C`) as primitive types and term formers.
3.  **Supporting computational aspects:** The system is designed not just for formalization but also for computation within the type theory. This includes definitional equality based on reduction (including unfolding of category constructors and rewrite rules for categorical laws) and type inference/checking mechanisms that actively participate in constructing and verifying categorical structures.
4.  **Facilitating synthetic reasoning:** By providing high-level categorical primitives, Emdash aims to allow users to reason about and construct categorical arguments in a style closer to common mathematical practice.
5.  **Extensibility and Robustness:** The system is designed to be extensible with further categorical constructs and incorporates advanced features like comprehensive implicit argument handling and sophisticated pattern matching for rewrite rules to enhance expressiveness and correctness.

### 1.2 Motivation

Category theory provides a powerful and abstract language for structuring mathematics and computer science. "Synthetic" approaches to category theory aim to internalize categorical reasoning within a formal system. A *computational* synthetic approach further emphasizes the ability to execute and verify these constructions. Emdash is motivated by the desire for a system where:

*   **Categorical concepts are first-class citizens.**
*   **Type checking performs categorical coherence checking.**
*   **Computation and formalization are intertwined.**
*   **Implicit arguments are handled systematically**, reducing verbosity and aligning with common mathematical notation.
*   **Rewrite rules are powerful and well-behaved**, thanks to robust pattern elaboration.
*   **Prototyping and experimentation are facilitated** in a TypeScript environment.

Emdash draws inspiration from systems like Lambdapi and aims to provide a similar "direct" feel for categorical constructions, now enhanced with more mature handling of implicits and patterns.

## 2. System Architecture

The Emdash system is structured around a core set of data types representing terms and their operational semantics, now significantly enhanced to support generalized implicit arguments and related features.

### 2.1 Core Data Structures

*   **`Icit` Enum**:
    ```typescript
    export enum Icit {
        Expl = 'Expl', // Explicit
        Impl = 'Impl', // Implicit
    }
    ```
    This enumeration is used to mark the implicitness of arguments in applications and binders in lambdas and Pi-types.

*   **`Term`**: The fundamental data type for all expressions. It's a discriminated union (`BaseTerm`) encompassing:
    *   **Standard TT constructs (with `Icit` integration):**
        *   `Type`: The sort of types.
        *   `Var(name: string)`: Variables.
        *   `Lam(name: string, icit: Icit, body: (v: Term) => Term, paramType?: Term, _isAnnotated?: boolean)`: Lambda abstraction, where `icit` marks the binder's implicitness.
        *   `App(func: Term, arg: Term, icit: Icit)`: Application, where `icit` marks the argument's implicitness (e.g., `f {implicit_arg}` vs. `f explicit_arg`).
        *   `Pi(name: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term)`: Dependent function type, where `icit` marks the binder's implicitness.
    *   **Metavariables:** `Hole(id, ref?, elaboratedType?)`.
    *   **Emdash Categorical Constructs (with enhanced implicit handling):**
        *   `CatTerm`: The type of categories.
        *   `ObjTerm(cat: Term)`: The type of objects in a category `cat`.
        *   `HomTerm(cat: Term, dom: Term, cod: Term)`: The type of morphisms.
        *   `MkCat_(objRepresentation, homRepresentation, composeImplementation)`: Constructor for concrete categories.
        *   `IdentityMorph(obj: Term, implicitArgs?: Term[])`: Identity morphism. Now stores its implicit arguments (e.g., the category) in `implicitArgs`.
        *   `ComposeMorph(g: Term, f: Term, implicitArgs?: Term[])`: Composition of morphisms. Similarly stores its implicit arguments (category, intermediate objects) in `implicitArgs`.

*   **`Context` (`Ctx`)**: A list of `Binding`s (`{ name: string, type: Term }`).

*   **`GlobalDef` and `globalDefs`**: A `Map` storing global definitions. The `GlobalDef` interface is now:
    ```typescript
    export interface GlobalDef {
        name: string;
        type: Term;
        value?: Term;
        isConstantSymbol: boolean;
        isInjective?: boolean; // If true, App(Global, L) = App(Global, R) can reduce to L = R in unification.
        kernelImplicitSpec?: KernelImplicitSpec; // Describes structure of kernel implicits.
    }
    ```

*   **`KernelImplicitSpec` and `KERNEL_IMPLICITS_METADATA`**:
    ```typescript
    export interface KernelImplicitParam { name: string; }
    export interface KernelImplicitSpec {
        implicitArity: number;
        paramNames: string[];
    }
    export const KERNEL_IMPLICITS_METADATA: Record<string, KernelImplicitSpec> = {
        IdentityMorph: { implicitArity: 1, paramNames: ["cat_IMPLICIT"] },
        ComposeMorph:  { implicitArity: 4, paramNames: ["cat_IMPLICIT", "objX_IMPLICIT", "objY_IMPLICIT", "objZ_IMPLICIT"] },
        // Other kernel constructors can be added here.
    };
    ```
    This provides a uniform way to declare and manage implicit arguments for kernel-defined terms. The term constructors like `IdentityMorph` now carry an `implicitArgs: Term[]` field.

*   **`Constraint`**: Represents a unification constraint `{ t1: Term, t2: Term, origin?: string }`.

*   **`RewriteRule` and `userRewriteRules`**: Stores user-defined computation rules. The `lhs` pattern is now elaborated before matching.

*   **`UnificationRule` and `userUnificationRules`**: Stores user-defined unification rules. Patterns here are also elaborated.

### 2.2 Key Algorithms

#### 2.2.1 Normalization and Definitional Equality (`whnf`, `normalize`, `areEqual`)

*   These functions remain central, but now operate on terms that include `Icit` tags and systematically handled implicit arguments.
*   `whnf` still performs β-reduction, δ-reduction (unfolding global definitions), user rewrite rule application, and Emdash-specific unfoldings (e.g., for `MkCat_`).
*   The logic for handling rewrite rule loops (`areStructurallyEqualNoWhnf`) remains crucial.

#### 2.2.2 Type Inference and Checking (Bidirectional Typing: `infer`, `check`)

This is significantly enhanced to support the new implicit argument system.

*   **`elaborate(term: Term, expectedType?: Term, initialCtx?: Context, normalizeResult: boolean = true)`**:
    *   The main entry point. Now includes a `normalizeResult` flag. When `false` (used for pattern elaboration), the term is returned after type checking and hole filling but before full normalization.
*   **Handling `Icit` in `App`, `Lam`, `Pi`:**
    *   **`App`:**
        *   When inferring/checking `App(f, arg, icit)`, the type of `f` is expected to be a `Pi` with a matching `icit` for its binder.
        *   **Implicit Argument Insertion:** If `infer` encounters `App(f, arg, Icit.Expl)` but `type(f)` (after `whnf`) is `Pi(x, Icit.Impl, paramType, bodyType)`, a fresh hole `?h_impl` is created for the implicit argument. The application is conceptually transformed: `f {?h_impl} arg`. `?h_impl` is checked against `paramType`, and the process continues with the (now partially applied) function `f {?h_impl}`. This is applied iteratively.
    *   **`Lam`:**
        *   Checking `Lam(x, icit, body, typeAnn?)` against `Pi(y, pi_icit, A, B)` requires `icit === pi_icit`.
        *   **Implicit Lambda Insertion (Eta-expansion for Implicits):** When checking a `term` against an expected `Pi(x, Icit.Impl, A, B)`, if `term` itself is not an implicit lambda, the system attempts to insert one. For instance, `term` might be transformed into `λ{x':A}. (term {x'})` (if `term` is a function that now expects explicit args due to implicit lambda) or `λ{x':A}. term`. This new implicit lambda is then checked.
*   **Uniform Kernel Implicit Handling (`ensureKernelImplicitsPresent`):**
    *   Called at the start of `infer`/`check` for terms like `IdentityMorph`, `ComposeMorph`.
    *   Uses `KERNEL_IMPLICITS_METADATA` to inspect the term's `implicitArgs` array.
    *   If the array is missing, has incorrect length, or contains `undefined` elements, it's initialized or filled with fresh `Hole`s.
    *   Subsequent constraint generation in `infer`/`check` (e.g., `type(obj) === ObjTerm(?cat_hole)` for `IdentityMorph(obj, [?cat_hole])`) proceeds as before but with these systematically managed holes.

#### 2.2.3 Unification and Constraint Solving (`unify`, `solveConstraints`)

*   **`unify(t1: Term, t2: Term, ctx: Context)`:**
    *   **Injectivity for Globals:** When unifying `App(f1, arg1, icit1)` and `App(f2, arg2, icit2)`:
        1.  `whnf(f1)` to `rf1`, `whnf(f2)` to `rf2`.
        2.  If `rf1` is `Var(name1)`, `rf2` is `Var(name2)`, and `name1 === name2`:
            *   Retrieve `globalDef` for `name1`.
            *   If `globalDef.isInjective === true`: Recursively unify `arg1` with `arg2` (and `f1` with `f2`, `icit1` with `icit2`).
            *   Else (not injective, or heads are not identical injective vars): The terms `App(...)` do not decompose automatically. Unification relies on `areEqual` or user unification rules.
    *   Hole unification (`unifyHole`) and structural unification for other terms (including `Icit` comparison for `Lam`, `App`, `Pi`) proceed with refinements.
*   **`solveConstraints`:** Iteratively processes constraints, using `unify`.

#### 2.2.4 Pattern Matching and Rewriting (`elaboratePattern`, `matchPattern`, `applySubst`)

This area has been significantly redesigned for robustness with implicit arguments.

*   **`elaboratePattern(patternInput: Term, ctx: Context, patternVarDecls: PatternVarDecl[], expectedType?: Term)`:**
    *   **Reuses Term Elaboration:** Instead of a bespoke algorithm, `elaboratePattern` now leverages the main `elaborate` function.
    *   A `patternInfCtx` is created by adding `patternVarDecls` (e.g., `$x: typeOfX`) to the input `ctx`.
    *   `elaborate(patternInput, expectedType, patternInfCtx, normalizeResult = false)` is called. The `normalizeResult = false` flag is crucial, ensuring the pattern's structure is preserved after type checking and implicit insertion, rather than being normalized away.
    *   The returned `result.term` is the elaborated pattern, now potentially including implicit `App`s (with holes or inferred terms) and implicit `Lam`s, consistent with how a regular term would be elaborated.
*   **`matchPattern(elaboratedPattern: Term, termToMatch: Term, ctx: Context, patternVarDecls: PatternVarDecl[], currentSubst?: Substitution)`:**
    *   Always receives an *elaborated* LHS pattern.
    *   When matching constructs like `App`, `Lam`, `Pi`, it now also compares their `icit` tags. If `pattern.icit !== term.icit`, the match fails.
    *   Holes within the elaborated pattern (e.g., `eq {?h_T} $a $b` where `?h_T` was a hole filled by `elaboratePattern`) are matched against the corresponding parts of `termToMatch`. These pattern-internal holes behave like wildcards for matching purposes but typically don't bind into the substitution for the RHS (unless specifically designed to do so, which is not the current primary approach). The main pattern variables (`$a`, `$b`) are bound as usual.
*   **`applySubst`:** Applies the substitution (from a successful `matchPattern`) to the (potentially also elaborated) RHS of a rule.

#### 2.2.5 Higher-Order Abstract Syntax (HOAS)

*   `Lam` and `Pi` terms continue to use JavaScript functions for their bodies.
*   Instantiation, equality comparison, matching, and substitution for HOAS terms are adapted to correctly handle the `icit` tags and the elaborated nature of terms.

## 3. Detailed Code Review and Analysis

The introduction of systematic implicit argument handling and pattern elaboration addresses many previous complexities and enhances the system's robustness.

### 3.1 Overall Code Structure and Quality

*   The use of `Icit` and explicit `icit` fields in terms improves clarity regarding argument handling.
*   `KERNEL_IMPLICITS_METADATA` centralizes the definition of implicit arguments for kernel terms, promoting uniformity.
*   The strategy of reusing `elaborate` (with `normalizeResult=false`) for `elaboratePattern` is a significant simplification and promotes consistency between term and pattern processing.

### 3.2 Key Improvements and Considerations

1.  **Robust Implicit Handling:** The system now has a more predictable and comprehensive way to manage implicits, both for user-defined functions/types and for built-in categorical constructors. This is crucial for writing intuitive and less verbose Emdash code.
2.  **Pattern Elaboration Correctness:** By elaborating patterns using the same logic as terms, rewrite rules are more likely to match as intended, especially when implicits are involved. For example, a pattern `eq $a $b` (where `eq` expects an implicit type argument) will be elaborated to `eq {?T} $a $b`, correctly aligning its structure with an elaborated term like `eq {Nat} (Num 1) (Num 2)`.
3.  **Injectivity Control in Unification:** The `isInjective` flag on global definitions provides finer control over how unification decomposes application terms, preventing unsound decompositions for non-injective functions.
4.  **Uniformity of Kernel Implicits:** The `ensureKernelImplicitsPresent` function, driven by `KERNEL_IMPLICITS_METADATA`, standardizes how constructors like `IdentityMorph` and `ComposeMorph` manage their implicit arguments, replacing previous ad-hoc mechanisms.
5.  **Complexity Management:** While these features add power, they also increase the complexity of the elaboration and unification logic. Careful testing is essential. The interaction between implicit insertion, hole solving, and pattern variable instantiation needs to be robust.
6.  **Non-Normalizing Elaboration:** The introduction of a non-normalizing mode for `elaborate` is a key technical detail that makes reusing it for patterns feasible. It ensures that user-intended pattern structures are not computed away.
7.  **HOAS and Elaborated Patterns:** When an elaborated pattern contains a `Lam` or `Pi` with a HOAS body, the matching logic (`matchPattern`) must correctly handle the comparison of these HOAS bodies, considering that the pattern's body itself is now the result of an elaboration process.

### 3.3 Strengths of the New Design

*   **Expressiveness:** Users can define functions and types with implicit arguments in a standard way. Rewrite rules can be written more naturally.
*   **Consistency:** Term elaboration and pattern elaboration follow similar principles. Kernel implicits are handled uniformly.
*   **Reduced Verbosity:** Implicit arguments significantly cut down on the boilerplate in writing terms.
*   **Soundness:** Injectivity controls and more careful pattern matching contribute to a more sound unification and rewriting process.

## 4. Emdash Type Theory Specification (with Implicits)

This section details the type theory implemented in Emdash, now incorporating explicit and implicit arguments.

### 4.1 Core Type System: MyLambdaPi Base with Implicits

*   **Sorts:**
    *   A single sort `Type`. Axiom: `Type : Type`.
*   **Terms:**
    1.  **`Type`**: The sort of all types.
    2.  **`Var(name: string)`**: Variables.
    3.  **`Lam(paramName: string, icit: Icit, body: (v: Term) => Term, paramType?: Term)`**: Lambda abstraction.
        *   Introduction (Explicit Binder): `Γ, x:A ⊢ t : B(x)  =>  Γ ⊢ (λ(x:A). t) : (Π(x:A). B(x))`
        *   Introduction (Implicit Binder): `Γ, x:A ⊢ t : B(x)  =>  Γ ⊢ (λ{x:A}. t) : (Π{x:A}. B(x))`
            (Type annotation `A` can be a hole `?A` during inference).
    4.  **`App(func: Term, arg: Term, icit: Icit)`**: Application.
        *   Elimination (Explicit Argument): `Γ ⊢ f : (Π(x:A). B(x)), Γ ⊢ a : A  =>  Γ ⊢ f(a) : B(a)`
        *   Elimination (Implicit Argument): `Γ ⊢ f : (Π{x:A}. B(x)), Γ ⊢ a : A  =>  Γ ⊢ f{a} : B(a)`
    5.  **`Pi(paramName: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term)`**: Dependent function type.
        *   Formation (Explicit Binder): `Γ ⊢ A : Type, Γ, x:A ⊢ B(x) : Type  =>  Γ ⊢ (Π(x:A). B(x)) : Type`
        *   Formation (Implicit Binder): `Γ ⊢ A : Type, Γ, x:A ⊢ B(x) : Type  =>  Γ ⊢ (Π{x:A}. B(x)) : Type`
    6.  **`Hole(id?: string)`**: Metavariables.

### 4.2 Emdash Phase 1: Core Categorical Constructs with Uniform Implicits

Primitive term constructors like `IdentityMorph` and `ComposeMorph` now have their implicit arguments (e.g., category, objects) managed via an `implicitArgs: Term[]` field. These are initialized with holes by `ensureKernelImplicitsPresent` based on `KERNEL_IMPLICITS_METADATA` and then solved during elaboration.

*   **`IdentityMorph(obj: Term, implicitArgs?: Term[])`**
    *   `implicitArgs` (typically `[cat_hole]`)
    *   Type Rule: `Γ ⊢ X : ObjTerm(C) => Γ ⊢ IdentityMorph(X, [C]) : HomTerm(C, X, X)`
*   **`ComposeMorph(g: Term, f: Term, implicitArgs?: Term[])`**
    *   `implicitArgs` (typically `[cat_hole, objX_hole, objY_hole, objZ_hole]`)
    *   Type Rule: `Γ ⊢ f:Hom(C,X,Y), g:Hom(C,Y,Z) => Γ ⊢ ComposeMorph(g,f, [C,X,Y,Z]) : HomTerm(C,X,Z)`

Other constructs (`CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`) remain largely the same in their typing rules but interact with a system that is now fully aware of implicits.

### 4.2.1 Emdash Phase 2: Functors and Natural Transformations (Kernel Implementation)

Building upon the core, Phase 2 introduces kernel-level terms for functors and natural transformations:

*   **`FunctorCategoryTerm(domainCat: Term, codomainCat: Term)`**: Represents the category `Functor A B` (or `B^A`).
    *   Type Rule: `Γ ⊢ A:Cat, B:Cat => Γ ⊢ FunctorCategoryTerm(A,B) : Cat`
*   **`FMap0Term(functor: Term, objectX: Term, catA_IMPLICIT?: Term, catB_IMPLICIT?: Term)`**: Represents the object mapping `F(X)` of a functor `F`. (`fapp0 F X` in LP spec).
    *   `functor` has type `ObjTerm(FunctorCategoryTerm(catA, catB))`, `objectX` has type `ObjTerm(catA)`.
    *   Type Rule: `Γ ⊢ F:Obj(Functor(A,B)), X:Obj(A) => Γ ⊢ FMap0Term(F,X,[A],[B]) : ObjTerm(B)`
*   **`FMap1Term(functor: Term, morphism_a: Term, catA_IMPLICIT?: Term, catB_IMPLICIT?: Term, objX_A_IMPLICIT?: Term, objY_A_IMPLICIT?: Term)`**: Represents the morphism mapping `F(a)` of a functor `F`. (`fapp1 F a` in LP spec).
    *   `functor` has type `ObjTerm(FunctorCategoryTerm(catA, catB))`, `morphism_a` has type `HomTerm(catA, objX_A, objY_A)`.
    *   Type Rule: `Γ ⊢ F:Obj(Functor(A,B)), a:Hom(A,X,Y) => Γ ⊢ FMap1Term(F,a,[A],[B],[X],[Y]) : HomTerm(B, FMap0Term(F,X), FMap0Term(F,Y))`
*   **`NatTransTypeTerm(catA: Term, catB: Term, functorF: Term, functorG: Term)`**: Represents the type of natural transformations `Transf A B F G`.
    *   `functorF` and `functorG` have type `ObjTerm(FunctorCategoryTerm(catA, catB))`.
    *   Type Rule: `Γ ⊢ A:Cat, B:Cat, F:Obj(Functor(A,B)), G:Obj(Functor(A,B)) => Γ ⊢ NatTransTypeTerm(A,B,F,G) : Type`
*   **`NatTransComponentTerm(transformation: Term, objectX: Term, catA_IMPLICIT?: Term, catB_IMPLICIT?: Term, functorF_IMPLICIT?: Term, functorG_IMPLICIT?: Term)`**: Represents the component `ε_X` of a natural transformation `ε`. (`tapp eps X` in LP spec).
    *   `transformation` has type `NatTransTypeTerm(catA, catB, functorF, functorG)`, `objectX` has type `ObjTerm(catA)`.
    *   Type Rule: `Γ ⊢ ε:NatTrans(A,B,F,G), X:Obj(A) => Γ ⊢ NatTransComponentTerm(ε,X,[A],[B],[F],[G]) : HomTerm(B, FMap0Term(F,X), FMap0Term(G,X))`

*   **Kernel Reduction Rule:** The LP rule `@Hom (Functor _ _) $F $G ↪ Transf $F $G` is implemented directly in the `whnf` reduction logic:
    *   `HomTerm(cat = FunctorCategoryTerm(A,B), dom = F, cod = G)` reduces to `NatTransTypeTerm(A,B,F,G)`. 

These terms also have their relevant implicit arguments (e.g., `catA_IMPLICIT`) managed via `ensureKernelImplicitsPresent` and `KERNEL_IMPLICITS_METADATA`.

### 4.3 Elaboration Strategy for Implicits

*   **Implicit Application Insertion:** If `f` has type `Π{A}.B` and an explicit application `f t` is encountered, a hole `?h_impl:A` is inserted: `f {?h_impl} t`.
*   **Implicit Lambda Insertion:** If checking `t` against `Π{A}.B` and `t` is not an implicit lambda, `t` is eta-expanded into `λ{x:A}. t'`, which is then checked.
*   **Kernel Implicits:** Handled by `ensureKernelImplicitsPresent` creating holes, which are then solved by standard constraint generation and unification.

## 5. Development Journey (Highlighting Implicits and Patterns)

The development of Emdash's robust implicit argument system and pattern elaboration was a significant step.

1.  **Initial State:** Implicit arguments were handled ad-hoc, primarily for kernel constructors like `IdentityMorph` via `_IMPLICIT` suffixed fields. Pattern matching was purely structural on the raw pattern.
2.  **Recognizing the Need:** As the system grew, the limitations became apparent:
    *   Lack of general implicit arguments made terms verbose.
    *   Rewrite rules often failed to match correctly when terms involved any form of implicit arguments not mirrored exactly in the pattern.
3.  **Design Phase for Implicits:**
    *   Introduced the `Icit` enum and integrated it into `Lam`, `App`, `Pi`.
    *   Designed the `infer`/`check` logic for inserting implicit applications and lambdas.
    *   Conceptualized uniform handling for kernel constructor implicits using `KERNEL_IMPLICITS_METADATA` and an `implicitArgs` array on terms.
4.  **Redesigning Pattern Handling (`elaboratePattern`):**
    *   **Initial thoughts:** Considered a complex, separate recursive algorithm to "elaborate" patterns by trying to infer where implicits should go.
    *   **Key Insight:** Realized that the existing term elaboration logic (`infer`/`check`) already does exactly this type-directed insertion of implicits.
    *   **Solution:** Modify `elaborate` to have a non-normalizing mode (`normalizeResult = false`). Then, `elaboratePattern` could simply call `elaborate` on the pattern term within a context enriched with pattern variable declarations. This ensures patterns undergo the same implicit argument insertion process as terms.
5.  **Refining Unification and Matching:**
    *   Added the `isInjective` flag for globals to control application decomposition in `unify`.
    *   Updated `matchPattern` to compare `icit` tags and to expect already elaborated patterns.
6.  **Implementation and Testing:** This involved substantial changes across `core_types.ts`, `core_elaboration.ts`, and `core_logic.ts`, followed by extensive testing to ensure correctness and handle edge cases. The main challenge was ensuring the interactions between HOAS, implicit insertion, pattern variable scope, and the non-normalizing elaboration mode were all correct.

This iterative process of design, insight, and refinement led to the current, more robust system.

## 6. Future Work and Improvements

With a solid foundation for implicit arguments and pattern matching, future work can build upon this.

### 6.1 Immediate Next Steps: Phase 2 (Functors and Natural Transformations)

The enhanced implicit handling and pattern elaboration will be invaluable for Phase 2.
*   Functor and natural transformation definitions often involve implicit arguments (e.g., source/target categories), which are now handled systematically by the kernel term design and `ensureKernelImplicitsPresent`.
*   Rewrite rules for functoriality and naturality laws will benefit from the robust pattern matching on these new kernel terms.
*   The core kernel implementation of Functors and Natural Transformations ( `FunctorCategoryTerm`, `FMap0Term`, `FMap1Term`, `NatTransTypeTerm`, `NatTransComponentTerm`), their typing rules, and the key reduction for `HomTerm(FunctorCategoryTerm(...))` are now in place.

Further work in Phase 2 will involve:
*   Defining user-facing constructor functions (like `mkFunctor_`, `mkNatTrans_` from the LP spec, if desired) that build these kernel terms.
*   Adding user-level rewrite rules for functoriality (e.g., `F(id) = id`, `F(g ∘ f) = F(g) ∘ F(f)`) and naturality squares.
*   Defining `Set` category and the Yoneda embedding, which will utilize these functorial constructs.
*   Extensive testing of these higher-level definitions and rules.

The new implicit argument handling and pattern elaboration significantly de-risk Phase 2 by providing a more powerful and predictable foundation for defining these higher-level categorical structures and their laws.

### 6.2 Potential New Features and Enhancements (Revisited)

*   **Named Implicits:** Extend the `Icit` system or `App` term to support named implicit arguments (e.g., `f {argName = val}`). This would require parser changes and modifications to the application handling in `infer`/`check`.
*   **More Sophisticated Pattern Language:**
    *   Allowing pattern variables to bind implicit arguments explicitly if desired.
    *   Type-annotated pattern variables directly in the pattern syntax.
*   **Error Reporting for Implicits:** Improve error messages when implicit resolution fails or leads to ambiguity.

Other future work (universe polymorphism, propositional equality, inductive types, tactics, performance, UI) remains relevant and will benefit from the more expressive core system.

## 7. Test Cases (Focus on New Features)

New tests were crucial for validating the implicit argument and pattern elaboration features:
*   **`Icit` Tagging:** Ensuring `infer`/`check` correctly assign and use `Icit.Expl` vs. `Icit.Impl`.
*   **Implicit Application Insertion:**
    *   `f x` where `f: Π{A}.Π(B).C` correctly becomes `f {?h1} x`.
    *   Multiple implicit arguments.
*   **Implicit Lambda Insertion:**
    *   Checking `t` against `Π{A}.B` correctly wraps `t` in an implicit lambda.
*   **`elaboratePattern`:**
    *   `eq $a $b` (for `eq : Π{T}.T→T→Type`) elaborates to `eq {?h_T} $a $b`.
    *   Patterns involving nested structures with implicits.
*   **`matchPattern` with Elaborated Patterns:**
    *   Ensuring `eq {?h_T} $a $b` matches `eq {Nat} (plus 1 2) 3`.
    *   Matching failure if `icit` tags differ between pattern and term.
*   **Unification with `isInjective`:**
    *   `App(inj_f, X) = App(inj_f, Y)` leads to `X=Y`.
    *   `App(noninj_f, X) = App(noninj_f, Y)` does not automatically lead to `X=Y`.
*   **Uniform Kernel Implicits:**
    *   `IdentityMorph(obj)` correctly infers the category.
    *   `ComposeMorph(g, f)` correctly infers category and intermediate objects.
    *   Cases where user provides some, but not all, kernel implicits explicitly.

## 8. Plan Forward and Conclusion

### 8.1 Plan for Phase 2: Functors and Natural Transformations (Leveraging New Implicit System)

The strategy for Phase 2 has commenced with the kernel implementation:
1.  **Extending `Term` type:** `FunctorCategoryTerm`, `FMap0Term`, `FMap1Term`, `NatTransTypeTerm`, `NatTransComponentTerm` have been added. These benefit from the `KERNEL_IMPLICITS_METADATA` mechanism for their implicit arguments.
2.  **Updating `infer`/`check`:** Type rules for these new terms are implemented, using the existing `Icit` system and implicit argument handling for their components and parameters.
3.  **Implementing `whnf` reductions:** The key reduction `HomTerm(FunctorCategoryTerm(A,B), F, G) ==> NatTransTypeTerm(A,B,F,G)` is implemented.

Next steps within Phase 2 involve:
4.  **User-level constructors and Rewrite rules:** Defining functions like `mkFunctor` (which would construct an `ObjTerm(FunctorCategoryTerm(...))` along with its map actions potentially as `FMap0Term`/`FMap1Term` or lambda abstractions returning these) and `mkTransf`. Adding rewrite rules for functoriality and naturality. The improved `elaboratePattern` will make these rules more robust.
5.  **Defining `Set` and Yoneda:** Implementing the `Set` category and the Yoneda embedding using the new functorial machinery.
6.  **Testing:** Thoroughly testing all new definitions, rules, and their interactions.

The new implicit argument handling and pattern elaboration significantly de-risk Phase 2 by providing a more powerful and predictable foundation for defining these higher-level categorical structures and their laws.

### 8.2. Conclusion

Emdash has undergone a significant enhancement with the introduction of a comprehensive system for implicit arguments, robust pattern elaboration, uniform kernel implicit handling, and controlled injectivity in unification. These features address key areas of expressiveness, correctness, and user convenience, moving Emdash closer to its goal of being a practical tool for computational synthetic category theory.

The design choices, particularly reusing term elaboration logic for patterns and standardizing kernel implicits, aim for consistency and maintainability. While adding complexity, these features are foundational for tackling more advanced categorical constructs in Phase 2 and beyond. The development journey underscores the iterative nature of type system design, where addressing core logical requirements (like proper implicit handling) unlocks further potential. Emdash is now better equipped to support the concise and powerful expression of categorical ideas.
```
