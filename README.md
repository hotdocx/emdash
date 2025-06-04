# emdash - A Functorial Programming Language Core

## Overview

`emdash` is a TypeScript project implementing the core of a dependently typed language with a focus on category theory concepts. It provides a foundational type theory kernel, including:

*   **Dependent Types:** Pi types (dependent functions) and Lambda abstractions.
*   **Universes:** A simple `Type` universe.
*   **Core Logic:**
    *   Weak Head Normal Form (WHNF) reduction.
    *   Normalization.
    *   Term equality (convertibility) checking.
    *   Unification with support for meta-variables (holes).
*   **Elaboration:**
    *   Type inference and checking.
    *   Implicit argument insertion.
    *   Resolution of kernel-defined implicit arguments for specific term constructors.
*   **Extensibility:**
    *   Global definitions for constants and functions.
    *   User-defined rewrite rules for equational reasoning.
    *   User-defined unification rules to guide the unification algorithm.
*   **Category Theory Primitives:**
    *   Basic notions: `Cat` (type of categories), `Obj C` (objects of `C`), `Hom C X Y` (morphisms in `C` from `X` to `Y`).
    *   Functors: `Functor C D` (type of functors from `C` to `D`), `fmap0 F X` (action on objects), `fmap1 F f` (action on morphisms).
    *   Natural Transformations: `Transf F G` (type of natural transformations between `F` and `G`), `tapp α X` (component at `X`).
    *   Functor Categories: `Functor_cat C D` (the category `[C, D]`).
    *   The `Set` category and covariant Hom-functors `Hom_A(W, -)`.

The design is inspired by systems like Lambdapi, Agda, and Coq, with a particular emphasis on making category-theoretic constructions first-class.

## File Structure

The `src/` directory contains the core implementation, partitioned into logical modules:

*   **`types.ts`**: Defines all fundamental data structures for terms (`Term`, `Var`, `App`, `Lam`, `Pi`, `Hole`, and various category theory term constructors like `CatTerm`, `ObjTerm`, `FMap0Term`, etc.), contexts (`Context`), implicit/explicit markers (`Icit`), and interfaces for global definitions, rewrite rules, and unification rules.
*   **`constants.ts`**: Specifies metadata for built-in ("kernel") term constructors that have implicit arguments (e.g., `FMap0Term` has implicit category arguments). This metadata is used by the elaborator to ensure these implicits are correctly handled.
*   **`state.ts`**: Manages all global state, including:
    *   `globalDefs`: A map storing global symbol definitions.
    *   `userRewriteRules`, `userUnificationRules`: Arrays for user-defined rules.
    *   `constraints`: The list of pending unification constraints.
    *   Context manipulation utilities (`extendCtx`, `lookupCtx`).
    *   Fresh name/hole ID generation.
    *   Term dereferencing (`getTermRef`) to resolve hole assignments.
    *   Debugging flags and a `consoleLog` utility.
    *   The `printTerm` function for pretty-printing terms.
*   **`logic.ts`**: Contains the core computational logic of the type theory:
    *   `whnf`: Reduces terms to Weak Head Normal Form.
    *   `normalize`: Fully normalizes terms.
    *   `areEqual`: Checks for term convertibility (equality modulo reduction).
    *   `areStructurallyEqualNoWhnf`: Checks for raw structural equality.
    *   `unify`: The unification algorithm for solving constraints `t1 === t2`.
    *   `solveConstraints`: The main constraint solver loop.
    *   `matchPattern`: Matches a pattern term against a subject term, producing a substitution (used by rewrite and unification rules).
    *   `applySubst`: Applies a substitution to a term.
    *   `isPatternVarName`, `collectPatternVars`, `applyAndAddRuleConstraints`, `tryUnificationRules`: Helper functions for pattern matching and rule application.
*   **`elaboration.ts`**: Implements the type checking and inference layer:
    *   `infer`: Infers the type of a given term.
    *   `check`: Checks if a term has a given expected type.
    *   `elaborate`: The main entry point for type checking/inference, which drives `infer` or `check` and then `solveConstraints`.
    *   Handles insertion of implicit arguments based on Pi-types.
    *   Uses `ensureKernelImplicitsPresent` (which uses `kernel_metadata.ts`) to fill in missing implicit arguments for specific kernel terms.
*   **`globals.ts`**: Provides an API for defining global symbols and adding rules:
    *   `defineGlobal`: Adds a new global symbol with its type and optional value.
    *   `addRewriteRule`: Adds a user-defined rewrite rule (LHS and RHS are elaborated).
    *   `addUnificationRule`: Adds a user-defined unification rule.
*   **`stdlib.ts`**: Defines a basic standard library of primitive types, constants, and rules necessary for the system and for category theory.
    *   `setupPhase1GlobalsAndRules`: Defines `Cat`, `Obj`, `Hom`, `Functor`, `Transf`, `mkCat_`, `identity_morph`, `compose_morph`, and associated evaluation rules for `mkCat_`.
    *   `setupCatTheoryPrimitives`: Defines `Set`, `hom_cov` (covariant Hom functor), and a naturality rewrite rule.
    *   `resetMyLambdaPi`, `resetMyLambdaPi_Emdash`: Functions to reset the system state and reinitialize the standard library.

## Core Concepts and Workflow

1.  **Terms and Types**: The system is built around the `Term` data type, which represents all expressions in the language. Types are also terms (e.g., `Pi` types, `Type`, `Cat`).
2.  **Context**: A `Context` is a list of bindings, mapping names to their types and optional definitions (for local `let`s).
3.  **Elaboration**: When a term is processed:
    *   It's passed to `elaborate()`, optionally with an expected type.
    *   `elaborate()` calls `check()` or `infer()`.
    *   `infer()` tries to deduce the type of the term.
    *   `check()` verifies that the term has the expected type.
    *   During this process, implicit arguments are inserted, holes (`?hN`) might be created for unknown parts, and unification constraints are generated (e.g., `?h1 === NatType`).
    *   Kernel implicit arguments (like the source/target categories for `FMap0Term`) are ensured to be present, often by inserting fresh holes if they are missing during initial term construction.
4.  **Reduction (WHNF/Normalize)**:
    *   `whnf()` is used extensively to reduce terms to their head normal form. This involves β-reduction, unfolding definitions (unless marked `isTypeNameLike` or `isConstantSymbol`), and applying user rewrite rules.
    *   `normalize()` recursively calls `whnf()` on subterms to get a full normal form.
5.  **Equality**: `areEqual()` determines if two terms are convertible by reducing both to WHNF and then comparing their structure.
6.  **Unification and Constraint Solving**:
    *   When `check()` or `infer()` encounter a situation where two terms must be equal (e.g., an inferred type vs. an expected type, or a hole's type vs. an expected type), a `Constraint` is added.
    *   `solveConstraints()` iteratively processes these constraints using `unify()`.
    *   `unify()` tries to make two terms equal. If one is a hole, it attempts to assign the other term to the hole (after an occurs check). If both are structured terms, it decomposes the problem (e.g., for `App(f,a) === App(g,b)`, it tries to unify `f===g` and `a===b`, especially if `App`'s head is injective).
    *   User-defined unification rules can provide custom logic for specific unification problems.
7.  **Global Definitions and Rules**:
    *   `defineGlobal()` allows declaring constants and defining functions/values globally. These are stored in `globalDefs`.
    *   `addRewriteRule()` allows users to add equational rules (`lhs === rhs`). The `lhs` and `rhs` are elaborated to ensure type correctness. These rules are used by `whnf()`.
    *   `addUnificationRule()` allows adding rules of the form `P1 === P2  ==>  C1, C2, ...`, which can transform one unification problem into a set of new ones.

## Example of Category Theory Setup

The `stdlib.ts` file demonstrates how category theory primitives are set up:

*   `Cat` is defined as a `Type`.
*   `Obj A` (where `A : Cat`) is defined as a `Type`.
*   `Hom A X Y` (where `X, Y : Obj A`) is defined as a `Type`.
*   Functors like `hom_cov A W : Functor A Set` are defined, where `Set` is a predefined category.
*   Rewrite rules are added, for example, for naturality conditions:
    `(tapp eps X) _∘> (G a)  ↪  (F a) _∘> (tapp eps X')`
    This is expressed using `FMap1Term` (for functorial action on morphisms) and `NatTransComponentTerm` (for `tapp`).

This setup allows the system to reason about and compute with these categorical structures.