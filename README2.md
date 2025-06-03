# Emdash - A Functorial Programming System

Emdash is an experimental dependent type system with a focus on category theory concepts, designed to explore functorial programming paradigms. This document outlines the structure and key components of its TypeScript implementation.

## Core Architecture

The system is built around several key modules:

1.  **`types.ts`**:
    *   Defines all fundamental data structures: `Term` (representing expressions, types, etc.), `Context`, `Binding`, `GlobalDef`, `RewriteRule`, `UnificationRule`, `Constraint`, and various enums like `Icit` (implicitness).
    *   Includes constructor functions for all `Term` variants (e.g., `Var()`, `Lam()`, `App()`, `Pi()`, `CatTerm()`, `FMap0Term()`).

2.  **`state.ts`**:
    *   Manages all global mutable state:
        *   `globalDefs`: A map storing defined global symbols, their types, and optional values.
        *   `userRewriteRules`: An array of elaborated rewrite rules.
        *   `userUnificationRules`: An array of unification rules.
        *   `constraints`: An array of pending equality constraints to be solved.
    *   Handles generation of fresh names for variables (`freshVarName`) and holes (`freshHoleName`).
    *   Provides utilities for context manipulation (`emptyCtx`, `extendCtx`, `lookupCtx`).
    *   Includes `getTermRef` for dereferencing holes and `cloneTerm` (currently a no-op, for potential future use with mutable terms).
    *   Manages debug flags and control structures (e.g., `solveConstraintsControl`).
    *   Defines constants and predicates related to kernel symbol properties (e.g., `isKernelConstantSymbolStructurally`, `EMDASH_UNIFICATION_INJECTIVE_TAGS`).

3.  **`utils.ts`**:
    *   Contains general utility functions.
    *   `printTerm`: Pretty-prints terms for display, handling bound variables and recursion depth.
    *   `consoleLog`: A wrapper for `console.log` that respects a global verbosity flag.

4.  **`kernel_metadata.ts`**:
    *   Defines metadata for "kernel terms" – terms that have a fixed structure with implicit arguments (e.g., `FMap0Term`, `FMap1Term`).
    *   `KERNEL_IMPLICIT_SPECS`: An array specifying which fields of these kernel terms are implicit. This is used by the elaboration process.

5.  **`logic.ts`**:
    *   Implements the core logical machinery of the type system:
        *   `whnf(term, context)`: Reduces a term to its Weak Head Normal Form. This involves beta-reduction, applying rewrite rules, and unfolding global definitions.
        *   `normalize(term, context)`: Reduces a term to its full normal form by recursively calling `whnf` on subterms.
        *   `areEqual(term1, term2, context)`: Checks if two terms are definitionally equal (convertible) by reducing both to WHNF and comparing structurally (alpha-equivalence for binders).
        *   `unify(term1, term2, context)`: Attempts to make two terms equal, typically by solving holes or decomposing problems.
        *   `solveConstraints(context)`: Iteratively processes and attempts to solve all pending equality constraints using `unify`.
        *   `termContainsHole(term, holeId)`: Performs an occurs check.
        *   `areStructurallyEqualNoWhnf`: A syntactic equality check without reduction.

6.  **`elaboration.ts`**:
    *   Handles the process of taking user-input terms and producing fully typed, well-formed internal terms.
        *   `infer(term, context)`: Infers the type of a term.
        *   `check(term, expectedType, context)`: Checks if a term has an expected type.
        *   `elaborate(term, expectedType?, context?)`: Top-level elaboration function that orchestrates `infer` or `check` and constraint solving.
        *   `ensureKernelImplicitsPresent(term)`: Fills in missing implicit arguments for kernel terms using metadata from `kernel_metadata.ts`.
        *   `insertImplicitApps(term, type, context)`: Automatically inserts applications of implicit arguments based on a term's Pi type.
        *   `matchPattern(pattern, term, ...)`: Matches a pattern term (potentially with pattern variables) against a concrete term, producing a substitution.
        *   `applySubst(term, substitution, ...)`: Applies a substitution to a term.

7.  **`runtime.ts`**:
    *   Provides the primary API for users to define new symbols and rules:
        *   `defineGlobal(name, type, value?, ...)`: Defines a new global symbol.
        *   `addRewriteRule(name, patternVars, lhs, rhs, context)`: Adds a new rewrite rule.
        *   `addUnificationRule(rule)`: Adds a new unification rule.
        *   `resetMyLambdaPi()`: Resets the system state.

8.  **`prelude.ts`**:
    *   Sets up the initial environment by defining foundational types, category theory primitives, and their associated rules.
    *   `setupPhase1GlobalsAndRules()`: Defines core types like `Cat`, `Obj`, `Hom`, `Functor`, `Transf`, and rules for category construction (e.g., `mkCat_` evaluation).
    *   `setupCatTheoryPrimitives(context)`: Defines specific categories like `Set`, the `hom_cov` functor, and naturality rewrite rules.
    *   `resetMyLambdaPi_Emdash()`: A convenience function to reset the system and load the entire prelude.

## Workflow

1.  **Initialization**: Typically, `resetMyLambdaPi_Emdash()` from `prelude.ts` is called to set up the base system.
2.  **Definitions**: Users employ `defineGlobal` from `runtime.ts` to introduce new constants, functions, and types.
3.  **Rules**: `addRewriteRule` and `addUnificationRule` from `runtime.ts` are used to extend the system's definitional equality and unification behavior.
4.  **Elaboration**: When a term needs to be type-checked or its type inferred (e.g., in `defineGlobal` or during testing), the `elaborate` function from `elaboration.ts` is used.
    *   This involves `infer` and `check`, which may generate equality `constraints`.
    *   `ensureKernelImplicitsPresent` and `insertImplicitApps` help manage implicit arguments.
5.  **Logic**:
    *   During elaboration and other operations, `whnf`, `normalize`, and `areEqual` from `logic.ts` are used for reduction and equality judgments.
    *   `solveConstraints` is called to process constraints generated during elaboration, using `unify`.
    *   `unify` itself may use `whnf`, structural decomposition, and `tryUnificationRules`.
    *   Rewrite rules (from `state.ts`) are applied during `whnf` using `matchPattern` and `applySubst` (from `elaboration.ts`).

## Key Concepts

*   **Dependent Types**: The system supports Pi-types (dependent function types) and a universe `Type`.
*   **Category Theory**: First-class support for categories (`Cat`), objects (`Obj`), morphisms (`Hom`), functors (`Functor`, `FMap0Term`, `FMap1Term`), and natural transformations (`Transf`, `NatTransComponentTerm`).
*   **Kernel Terms vs. Globals**: Some category theory constructs are "kernel terms" (e.g., `CatTerm`, `ObjTerm(c)`) with specific constructors. Others are defined as global symbols with associated types and optional values (e.g., `identity_morph`, `compose_morph`).
*   **Elaboration**: A crucial phase that resolves ambiguities, infers types, fills in implicit information, and ensures terms are well-typed.
*   **Rewrite Rules**: User-defined rules that extend definitional equality (e.g., `(f ∘ id) = f`).
*   **Unification Rules**: User-defined rules that guide the unification algorithm for specific patterns (e.g., equating two different representations of composition).
*   **Constraint Solving**: Equality constraints generated during type checking are solved to ensure type consistency and infer hole values.

This refactored structure aims for better modularity and clarity, separating concerns while managing the inherent interdependencies in a type system implementation.