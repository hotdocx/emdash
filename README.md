# emdash - A Dependently Typed Language Core with a Categorical Focus

## Overview

`emdash` is a TypeScript project implementing the core of a dependently typed language. It is designed with a strong emphasis on integrating concepts from category theory as first-class citizens. The system provides a robust type theory kernel featuring:

*   **Dependent Types:** Full support for Pi-types (dependent functions), Lambda abstractions, and a `Type` universe.
*   **Elaboration Engine:** A sophisticated bidirectional type checking and inference system (`check` and `infer`) that drives the entire process. It handles:
    *   Creation and solving of unification constraints.
    *   Automatic insertion of implicit arguments.
    *   Specialized handling for "kernel-defined" implicit arguments for category theory constructors.
*   **Unification:** A constraint-based unification algorithm capable of solving higher-order problems (via Miller's pattern unification) and using meta-variables (holes).
*   **Reduction and Equality:**
    *   Term evaluation to Weak Head Normal Form (WHNF) and full normalization.
    *   Term convertibility (equality) checking, supporting α, β, and η-equivalence.
*   **Extensibility:**
    *   A global context for defining constants and functions.
    *   User-defined rewrite rules for equational reasoning.
    *   User-defined unification rules to provide hints to the solver.
*   **First-Class Category Theory:**
    *   Core notions: `Cat` (the type of categories), `Obj C`, `Hom C X Y`.
    *   Functors and Functor Categories: `Functor C D`, `Functor_cat C D`.
    *   Natural Transformations: `Transf F G`, `tapp α X`.
    *   Built-in `Set` category and the covariant Hom-functor.

The design is heavily inspired by systems like Agda and Lambdapi, aiming to provide a powerful and flexible foundation for computational type theory and functorial programming.

## Core Concepts and Workflow

The system revolves around a central elaboration process that validates and transforms raw terms into fully typed and consistent expressions.

1.  **Terms and Types (`types.ts`)**: The foundation is the `Term` data type, representing every expression, including types. The system is built on a "types-are-terms" principle.

2.  **Global State (`state.ts`)**: All global state, including definitions (`globalDefs`), rules, and constraints, is managed centrally. This module also provides utilities for context manipulation, fresh name generation, and term printing.

3.  **Elaboration (`elaboration.ts`)**: This is the system's entry point. When a term is processed by `elaborate()`:
    *   It is passed to `check()` (if an expected type is given) or `infer()` (to deduce the type).
    *   During this traversal, the system generates **unification constraints** (e.g., `?h1 === NatType`) whenever two terms must be equal.
    *   **Implicit arguments** are automatically inserted where needed based on Pi-types. For example, if `f` has type `Π {A:Type}. A -> A`, then checking `f 42` against `Nat` will transform the term to `f {Nat} 42`.
    *   **Kernel Implicits (`constants.ts`)**: Special category theory terms (like `FMap0Term` for functor application) have certain arguments declared as "kernel implicits" (e.g., the source and target categories). `ensureKernelImplicitsPresent` fills these with fresh holes if they are not provided, allowing for less verbose term construction.

4.  **Unification (`unification.ts`)**: After the initial traversal, `solveConstraints()` is called.
    *   It iteratively tries to solve pending constraints using the `unify()` function.
    *   `unify()` is a powerful algorithm that can decompose problems on injective constructors (e.g., `(F X) === (F Y)` becomes `X === Y`), solve for meta-variables (holes), and perform occurs-checks.
    *   For flex-rigid problems (e.g., `?M x y === f x`), it uses **higher-order pattern unification** (`solveHoFlexRigid`) to find a lambda abstraction that solves the hole (e.g., `?M = λa b. f a`).
    *   The process can be guided by user-defined unification rules.

5.  **Reduction (`reduction.ts`)**: The `whnf()` function is used pervasively to reduce terms to their head normal form. This involves:
    *   β-reduction: `(λx. e) a  ~>  e[a/x]`.
    *   Unfolding global definitions (unless they are marked as opaque constants).
    *   Applying user-defined **rewrite rules**.
    *   η-contraction (if enabled): `λx. F x  ~>  F`.
    *   `normalize()` recursively calls `whnf()` for full normalization.

6.  **Equality (`equality.ts`)**: The `areEqual()` function determines if two terms are convertible by reducing both to WHNF and then comparing their structure, respecting α-equivalence for binders.

7.  **Pattern Matching (`pattern.ts`)**: The `matchPattern()` function is the engine for rewrite rules. It supports **higher-order patterns**, where pattern variables can stand for functions. It also respects scope annotations on pattern variables (e.g., `$F.[x]` means `$F` can contain the binder `x`), which is crucial for correct matching under binders.

## File Structure

The `src/` directory is organized into the following key modules:

*   `types.ts`: Defines all core data structures, including `Term`, `Context`, `Icit`, and the various term constructors.
*   `state.ts`: Manages all global state: definitions, rules, constraints, flags, and utilities for context manipulation and term printing.
*   `constants.ts`: Defines metadata for kernel-level implicit arguments, used by the elaborator.
*   `elaboration.ts`: The heart of the system. Implements `elaborate`, `check`, `infer`, and handles implicit argument insertion.
*   `unification.ts`: Implements the unification algorithm, constraint solver, and higher-order unification logic.
*   `reduction.ts`: Implements term reduction (`whnf`, `normalize`) and the application of rewrite rules.
*   `equality.ts`: Implements the term convertibility checking algorithm (`areEqual`).
*   `pattern.ts`: Implements higher-order pattern matching (`matchPattern`) used by rewrite rules.
*   `globals.ts`: Provides the user-facing API (`defineGlobal`, `addRewriteRule`) for extending the system.
*   `stdlib.ts`: Defines the standard library, setting up primitives for category theory.
*   `structural.ts`: Provides functions for checking raw structural equality without reduction.

## Testing Strategy

The project is accompanied by a growing suite of unit tests in the `tests/` directory to ensure the correctness and stability of the core logic. The tests are written using Node.js's native test runner.

Key test suites include:
*   `equality_tests.ts`: Verifies α, β, and η equivalence.
*   `dependent_types_tests.ts`: Tests dependent type checking using length-indexed vectors (`Vec`).
*   `error_reporting_tests.ts`: Ensures sensible errors are thrown for common mistakes like unbound variables and type mismatches.
*   `higher_order_unification_tests.ts`: Contains specific tests for the higher-order unification solver.
*   `higher_order_pattern_matching_tests.ts`: Tests the higher-order pattern matcher with various scope restrictions.
*   `kernel_implicits_tests.ts`: Validates the automatic insertion and checking of implicit arguments for category theory constructors.
*   `rewrite_rules_tests.ts`: Checks the elaboration and application of user-defined rewrite rules.