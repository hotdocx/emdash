# Emdash: A Dependently Typed System for Computational Synthetic Category Theory

## Abstract

Emdash is a prototype dependent type system implemented in TypeScript, designed to support computational synthetic category theory. It extends a foundational dependent type system (MyLambdaPi) with primitive constructs for categories, objects, morphisms, and their operations. The system features bidirectional type checking, hole-filling via unification with metavariables, user-defined rewrite rules with elaborated patterns, generalized implicit argument handling, and support for higher-order abstract syntax (HOAS). This document details the architecture, implementation, analysis, and future development roadmap of Emdash, focusing on its current Phase 1 completion (core categorical constructs with enhanced implicit argument handling) and the plan towards implementing Phase 2 (functors and natural transformations).

## 1. Introduction

### 1.1 Project Goal

The primary goal of the Emdash project is to develop a practical and expressive dependent type system tailored for computational synthetic category theory. This involves:

1.  **Building upon a minimal dependent type theory core:** Leveraging established principles of systems like Martin-Löf Type Theory (MLTT) or the Calculus of Constructions (CoC), simplified for prototyping (e.g., `Type : Type`).
2.  **Introducing native categorical constructs:** Instead of encoding categories from set-theoretic or type-theoretic first principles, Emdash defines core categorical notions like `Cat` (the type of categories), `Obj C` (the type of objects in a category `C`), and `Hom C X Y` (the type of morphisms between objects `X`, `Y` in `C`) as primitive types and term formers.
3.  **Supporting computational aspects:** The system is designed for computation within the type theory. This includes definitional equality based on reduction (including unfolding of category constructors and rewrite rules for categorical laws) and type inference/checking mechanisms that actively participate in constructing and verifying categorical structures, now with robust handling of implicit arguments.
4.  **Facilitating synthetic reasoning:** By providing high-level categorical primitives and sophisticated implicit argument inference, Emdash aims to allow users to reason about and construct categorical arguments in a style closer to common mathematical practice.
5.  **Extensibility:** The system is designed to be extensible with further categorical constructs and user-defined theories.

The current implementation, `emdash_v2.ts` (and associated core modules), represents the completion of "Phase 1," which focuses on foundational core categorical structures and a robust infrastructure for implicit arguments and pattern-based rewriting.

### 1.2 Motivation

Category theory provides a powerful and abstract language. "Synthetic" approaches internalize categorical reasoning within a formal system. A *computational* synthetic approach emphasizes executing and verifying these constructions.

Emdash is motivated by the desire for a system where:
*   **Categorical concepts are first-class citizens.**
*   **Type checking performs categorical coherence checking and infers implicit information.**
*   **Computation and formalization are intertwined.**
*   **Prototyping and experimentation are facilitated.**

Emdash draws inspiration from systems like Lambdapi and aims to provide a similar "direct" feel for categorical constructions, enhanced by powerful implicit argument handling.

## 2. System Architecture

The Emdash system is structured around core data types and algorithms.

### 2.1 Core Data Structures

*   **`Icit` Enum**: `enum Icit { Expl, Impl }` specifies whether an argument or binder is explicit or implicit.

*   **`Term`**: The fundamental data type for all expressions. A discriminated union (`BaseTerm`) encompassing:
    *   **Standard TT constructs:** `Type`, `Var`.
    *   **Terms with Implicitness:**
        *   `Lam(name, icit: Icit, body, paramType?)`: Lambda abstraction.
        *   `App(func, arg, icit: Icit)`: Application.
        *   `Pi(name, icit: Icit, paramType, bodyType)`: Dependent function type.
    *   **Metavariables:** `Hole(id?, ref?, elaboratedType?)`.
    *   **Emdash Phase 1 Categorical Constructs:**
        *   `CatTerm`: The type of categories.
        *   `ObjTerm(cat: Term)`: The type of objects in a category `cat`.
        *   `HomTerm(cat: Term, dom: Term, cod: Term)`: The type of morphisms.
        *   `MkCat_(objRepresentation, homRepresentation, composeImplementation)`: Constructor for concrete categories.
        *   `IdentityMorph(obj: Term, implicitArgs: Term[])`: Identity morphism. Implicit args (e.g., category) stored in array.
        *   `ComposeMorph(g: Term, f: Term, implicitArgs: Term[])`: Composition of morphisms. Implicit args stored in array.
    ```typescript
    // Simplified representation
    type BaseTerm =
        | { tag: 'Type' }
        | { tag: 'Var', name: string }
        | { tag: 'Lam', name: string, icit: Icit, body: (v: Term) => Term, paramType?: Term }
        | { tag: 'App', func: Term, arg: Term, icit: Icit }
        // ... other core terms
        | { tag: 'CatTerm' }
        | { tag: 'ObjTerm', cat: Term }
        | { tag: 'IdentityMorph', obj: Term, implicitArgs: Term[] }
        // ... other Emdash terms
    type Term = BaseTerm;
    ```

*   **`Context` (`Ctx`)**: A list of `Binding`s (`{ name: string, type: Term }`).

*   **`GlobalDef` and `globalDefs`**: A `Map` storing global definitions.
    ```typescript
    interface GlobalDef {
        name: string;
        type: Term;
        value?: Term;
        isConstantSymbol: boolean;
        isInjective?: boolean; // If true, App(Global, L) = App(Global, R) can reduce to L = R
        kernelImplicitSpec?: KernelImplicitSpec; // Metadata for kernel constructor implicits
    }
    ```
*   **`KernelImplicitSpec` and `KERNEL_IMPLICITS_METADATA`**: Defines the number and names of implicit arguments for kernel term constructors (like `IdentityMorph`), used for uniform initialization with holes.

*   **`Constraint`**: Represents a unification constraint ` { t1: Term, t2: Term, origin?: string } `. These are collected during type checking and solved by the unifier.

*   **`RewriteRule` and `userRewriteRules`**: Stores user-defined computation rules (`{ name: string; patternVars: PatternVarDecl[]; rawLhs: Term; rawRhs: Term; elaboratedLhs?: Term; }`). The `rawLhs` is elaborated before matching.

*   **`UnificationRule` and `userUnificationRules`**: Stores user-defined unification rules. LHS patterns are also elaborated.

### 2.2 Key Algorithms

#### 2.2.1 Normalization and Definitional Equality

*   **`whnf(term: Term, ctx: Context)` (Weak Head Normal Form):**
    *   Reduces a term to its weak head normal form.
    *   Order of operations:
        1.  Hole Resolution (`getTermRef`).
        2.  User-Defined Rewrite Rules: Attempts to apply rules from `userRewriteRules` (matching against the *elaborated* LHS of the rule).
        3.  Head-Specific Reductions (Beta, Categorical Unfolding, Delta).
    *   Operates on terms that now include `Icit` tags.

*   **`normalize(term: Term, ctx: Context)`:** Reduces a term to normal form.
*   **`areEqual(t1: Term, t2: Term, ctx: Context)`:** Determines definitional equality.

#### 2.2.2 Type Inference and Checking (Bidirectional Typing)

*   **`elaborate(term: Term, expectedType?: Term, initialCtx?: Context, normalizeResult: boolean = true)`:**
    *   Main entry point. Resets globals. Calls `check` or `infer`. Solves constraints.
    *   The `normalizeResult` flag (defaults to `true`) controls whether the final term and type are normalized. Set to `false` when elaborating patterns.

*   **`infer(ctx: Context, term: Term)` and `check(ctx: Context, term: Term, expectedType: Term)`:**
    *   These algorithms now fully handle the `Icit` property of `Lam`, `App`, and `Pi` terms.
    *   **Implicit Application Insertion:** When `infer`ing or `check`ing an explicit application `App(f, arg, Icit.Expl)`, if the type of `f` (after `whnf`) is an implicit Pi-type `Π{x:A}.B`, the system automatically inserts a fresh hole for `x` (e.g., `f {?h_impl}`) and continues type checking. This process is iterative.
    *   **Implicit Lambda Insertion:** When `check`ing a term `t` against an expected implicit Pi-type `Π{x:A}.B`, if `t` is not already an implicit lambda, the system may eta-expand `t` into `λ{x':A}. (t x')` (if `t` is a function) or `λ{x':A}. t` and check this new lambda.
    *   **Kernel Implicits:** For kernel constructors like `IdentityMorph`, `ComposeMorph`, the `ensureKernelImplicitsPresent` function is called. It uses `KERNEL_IMPLICITS_METADATA` to ensure the `implicitArgs` array is populated with the correct number of holes before specific type checking rules generate constraints for them. This replaces the older `ensureImplicitsAsHoles` mechanism.

#### 2.2.3 Unification and Constraint Solving

*   **`unify(t1: Term, t2: Term, ctx: Context)`:**
    *   Attempts to unify `t1` and `t2`.
    *   **Hole Cases:** `unifyHole(?h, term)` solves `?h := term` (with occurs check).
    *   **Injectivity for Variables:** When unifying `App(f1, arg1, _)` and `App(f2, arg2, _)`, if `f1` and `f2` reduce to the same `Var(globalName)` and this `globalName` is marked `isInjective` in `globalDefs`, then `unify` will attempt to decompose the problem by unifying `arg1` with `arg2` (and `f1` with `f2`, and `icit`s).
    *   If the head is not an injective variable, or heads differ, the application terms are not automatically decomposed by this rule; equality relies on full reduction or user unification rules.
    *   **User Unification Rules:** `tryUnificationRules` can be used to guide unification, now operating on elaborated patterns for its LHS.

*   **`solveConstraints(ctx: Context)`:** Iteratively processes and solves constraints.

#### 2.2.4 Pattern Matching and Rewriting

*   **`elaboratePattern(patternInput: Term, ctx: Context, patternVarDecls: PatternVarDecl[], expectedType?: Term)`:**
    *   This function is called to prepare a raw pattern term (e.g., LHS of a rewrite rule) before matching.
    *   It leverages the main `elaborate` function (with `normalizeResult = false`).
    *   It extends the `ctx` with declarations for pattern variables (`$x`, `$y`, etc.).
    *   The `elaborate` call infers types, inserts implicit arguments (as holes or resolved terms if possible from context), and fills kernel implicits within the pattern structure, but does *not* normalize it.
    *   The result is an "elaborated pattern" that has a structure comparable to fully elaborated terms.

*   **`matchPattern(elaboratedPattern: Term, termToMatch: Term, ctx: Context, patternVarDecls: PatternVarDecl[], currentSubst?: Substitution)`:**
    *   Matches an *elaborated* `pattern` against `termToMatch` (which is typically already elaborated or will be reduced by `areEqual` during matching).
    *   Pattern variables (`$x`) are bound in the substitution.
    *   `Icit` tags on `App`, `Lam`, `Pi` in the `elaboratedPattern` and `termToMatch` must correspond for a successful match.
    *   Holes that remain in the `elaboratedPattern` (e.g., `eq {?T} $a $b`) must unify with the corresponding parts of `termToMatch`.

*   **`applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[])`:** Applies substitution to RHS of rules.

*   **Rewrite Rule Application (in `whnf`):**
    *   When a `RewriteRule` is considered:
        1.  Its `rawLhs` is first processed by `elaboratePattern` (if not already cached).
        2.  `matchPattern` is then called with this `elaboratedLhs`.
    *   This ensures that rewrite rules are sensitive to and can correctly match against terms with implicit arguments.

#### 2.2.5 Higher-Order Abstract Syntax (HOAS)

*   `Lam` and `Pi` terms use JavaScript functions for bodies.
*   Manipulation (equality, matching, substitution, inference) involves instantiating these functions with fresh variables.

#### 2.2.6 Implicit Argument Mechanism (Revised)

*   **General Implicits:** `Lam`, `App`, `Pi` terms now carry an `Icit` tag.
    *   Type inference (`infer`/`check`) is responsible for inserting implicit applications (filling in `{_}` style arguments) and implicit lambdas (eta-expanding for leading implicit binders).
*   **Kernel Constructor Implicits:**
    *   Constructors like `IdentityMorph`, `ComposeMorph` store their implicit arguments in an `implicitArgs: Term[]` array.
    *   `KERNEL_IMPLICITS_METADATA` provides specifications (arity, names) for these.
    *   `ensureKernelImplicitsPresent` function (called during `infer`/`check`) uses this metadata to populate `implicitArgs` with fresh holes if they are not provided or incomplete.
    *   Subsequent type checking generates constraints for these holes.
*   This provides a unified and more powerful system for handling various forms of implicitness.

## 3. Detailed Code Review and Analysis (`emdash_v2.ts` and core modules)

This section requires updates to reflect the new design.

### 3.1 Overall Code Structure and Quality

*   Remains generally well-structured. The introduction of `Icit` and refined implicit handling adds complexity but aims for uniformity.

### 3.2 Identified Bugs, Inconsistencies, and Areas for Concern (Previously)

*   Many concerns about ad-hoc implicit handling (`_IMPLICIT` fields, `ensureImplicitsAsHoles`) are addressed by the new `Icit` tags and `KERNEL_IMPLICITS_METADATA` system.
*   Concerns about pattern matching with implicits are addressed by `elaboratePattern`.

### New Considerations:

*   **Complexity of `infer`/`check`:** The logic for inserting implicit applications and lambdas adds significant complexity to these core algorithms. Thorough testing is paramount.
*   **Interaction of `elaboratePattern` with `infer`/`check`:** Relies on `elaborate` (with `normalizeResult=false`) behaving correctly for pattern structures.
*   **Performance of Elaboration:** Increased elaborations (for terms and patterns) might have performance implications.

### 3.3 Logical Flaws and Algorithmic Coherence

*   The revised system aims for greater coherence in implicit handling and pattern matching.
*   The injectivity check in `unify` provides more mathematically sound decomposition of applications.

### 3.4 Divergences from Standard Implementations or Expectations

*   The explicitness of `Icit` tags is a design choice. Some systems infer implicitness entirely from types.
*   Elaborating patterns via the main type checker is a powerful approach.

### 3.5 Strengths and Novel Aspects

*   **Unified Implicit Argument Handling:** `Icit` tags and systematic insertion rules provide a more robust approach.
*   **Elaborated Patterns:** Enables rewrite rules to work correctly and predictably in the presence of implicit arguments.
*   **Principled Injectivity:** Improves the behavior of unification for function applications.
*   **Uniform Kernel Implicits:** `KERNEL_IMPLICITS_METADATA` centralizes and standardizes how built-in constructors manage their implicit parameters.

## 4. Comparative Analysis

(This section would benefit from re-evaluation based on how the new implicit argument system compares to those in `example_implicits.hs` and Lambdapi, particularly regarding explicitness of `Icit` vs. type-directed inference of implicitness.)

## 5. Emdash Type Theory Specification (Phase 1 - Revised)

This section needs updates to reflect `Icit` in `Lam`, `App`, `Pi`, and the rules for implicit insertion.

### 5.1 Core Type System: MyLambdaPi Base

*   **Terms:**
    1.  **`Type`**
    2.  **`Var(name: string)`**
    3.  **`Lam(paramName: string, icit: Icit, body: (v: Term) => Term, paramType?: Term)`**:
        *   Typing rules depend on `icit`.
    4.  **`App(func: Term, arg: Term, icit: Icit)`**:
        *   Typing rules handle insertion of implicit applications if `func`'s type expects further implicit arguments before an explicit one.
    5.  **`Pi(paramName: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term)`**:
        *   Formation rules standard, `icit` included.
    6.  **`Hole(id?: string)`**

### 5.2 Emdash Phase 1: Core Categorical Constructs

*   Constructors like `IdentityMorph` and `ComposeMorph` now use `implicitArgs: Term[]` populated via `ensureKernelImplicitsPresent` and `KERNEL_IMPLICITS_METADATA`.

### 5.3 Implicit Arguments and Elaboration Strategy (Revised)

*   Elaboration (`infer`/`check`) actively inserts implicit `App`lications based on Pi-types encountered.
*   It inserts implicit `Lam`bdas when checking against implicit Pi-types.
*   Kernel implicits are uniformly initialized as holes.
*   `elaboratePattern` uses this same machinery for patterns.

### 5.4 "Constant Symbol" and "Injective Symbol" Semantics

*   `GlobalDef.isInjective` flag now controls unification decomposition for `Var` heads in applications.

## 6. Development Journey

### New Subsection: Implementing General Implicits, Pattern Elaboration, and Injectivity

The development of these features involved several key design decisions and iterations:

1.  **Need for General Implicits:** The initial ad-hoc handling of `_IMPLICIT` fields for kernel constructors was insufficient for user-defined functions or for patterns. A general mechanism was needed.
2.  **`Icit` Tagging:** Introducing `Icit.Expl` and `Icit.Impl` on `App`, `Lam`, and `Pi` terms was chosen to make implicitness explicit in the term structure.
3.  **Pattern Elaboration Strategy:**
    *   **Initial ideas:** Considered "peeling off" implicit arguments from terms during matching or having a complex, separate `elaboratePattern` function.
    *   **Chosen Solution:** Leverage the main `infer`/`check` (via `elaborate(..., normalizeResult=false)`) to elaborate patterns. This reuses existing type-driven implicit insertion logic, ensuring consistency between how terms and patterns are understood. Pattern variables are added to the context for this elaboration.
4.  **Uniform Kernel Implicits:** The `KERNEL_IMPLICITS_METADATA` and `implicitArgs: Term[]` field provide a standardized way to declare and manage implicits for built-in term formers, replacing `ensureImplicitsAsHoles`.
5.  **Injectivity in Unification:** The `isInjective` flag on `GlobalDef` allows fine-grained control over when `App(F,X) = App(F,Y)` can be simplified to `X=Y`, crucial for soundness when `F` is not injective.
6.  **Refinement of `infer`/`check`:** These algorithms were significantly extended to:
    *   Iteratively insert implicit applications when a function's type indicates pending implicit arguments.
    *   Insert implicit lambdas when checking a term against an implicit Pi-type.
7.  **Iterative Design:** The interaction between pattern elaboration, implicit argument insertion, and unification required careful thought and iterative refinement to ensure the components work together correctly. The goal was to follow principles from systems like Agda/Idris while adapting to Emdash's HOAS and TypeScript implementation.

This refactoring makes the system more principled and powerful for handling realistic scenarios involving implicit arguments in definitions and rewrite rules.

(Previous subsections of Development Journey remain relevant for prior history).

## 7. Future Work and Improvements

*   **Named Implicit Arguments:** Allow users to provide implicit arguments by name (e.g., `list_map {A=Nat} {B=Bool} f nat_list`). This would require parsing support and extending elaboration to match names against Pi-binder names.
*   (Other existing future work points remain relevant).

## 8. Plan Forward and Conclusion

(The existing plan for Phase 2 remains largely the same, but it will benefit from the more robust core system for implicits.)

### 8.1 Plan for Phase 2: Functors and Natural Transformations
(Content as before)

#### 8.1.1. Handling Laws (Functoriality and Naturality)
(Content as before)

### 8.2. Test Cases for Phase 2
(Content as before)

### 8.3. Conclusion

Emdash, with its significantly enhanced Phase 1 features including generalized implicit arguments, robust pattern elaboration, and principled injectivity, provides a stronger foundation for a dependently typed system tailored for synthetic category theory. The TypeScript implementation has successfully incorporated these advanced features, making the system more expressive and reliable.

The journey has highlighted the complexities of integrating sophisticated type system features like pervasive implicits with HOAS and rewrite systems. The solutions adopted, particularly leveraging the core type checker for pattern elaboration, aim for consistency and power.

Moving to Phase 2 (Functors and Natural Transformations) will build upon this more mature core. The ultimate aim remains to create a practical tool for computational mathematics. Emdash is on a clear path to becoming a valuable environment for exploring and formalizing categorical concepts, with a type system that now more closely mirrors the conveniences found in established proof assistants.
```
