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
    *   **Hole Rule:** If `term` is a `Hole`, its `elaboratedType` (if not present, it\'s set to `expectedType`) is inferred and constrained to be equal to `expectedType`. Also checks `expectedType : Type`.
    *   **Special Emdash Rules:** For `IdentityMorph` and `ComposeMorph` being checked against an `HomTerm`, it directly generates constraints between the implicits of the constructor and the components of the expected `HomTerm`. This is a more direct way to guide unification.
    *   **Default Rule:** Infers the type of `term` (`inferredType`) and adds a constraint `inferredType === expectedType`.

*   **`ensureImplicitsAsHoles(term: Term)`:**
    *   Mutates `IdentityMorph` and `ComposeMorph` terms to replace `undefined` implicit arguments with new `Hole`s. This is done at the beginning of `infer` and `check`.

#### 2.2.3 Unification and Constraint Solving

*   **`unify(t1: Term, t2: Term, ctx: Context)`:**
    *   Attempts to unify `t1` and `t2`. Returns `UnifyResult` (`Solved`, `Failed`, `RewrittenByRule`, `Progress`).
    *   **Hole Cases:** If `t1` (or `t2`) is a `Hole ?h`, it attempts `unifyHole(?h, whnf(t2))`.\
        *   `unifyHole(?h, term)`: Solves `?h := term` if `term` is not `?h` and `term` does not contain `?h` (occurs check via `termContainsHole`). If `term` is also a hole `?h\'`, it orders them by ID to avoid cycles.
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
        *   Otherwise, calls `unify(getTermRef(t1), getTermRef(t2))`.\
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
    *   For each rule, calls `matchPattern(rule.lhs, currentTerm, ...)`.\
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

## 3. Detailed Code Review and Analysis (`emdash_v2.ts`)

This section provides a critical review of the `emdash_v2.ts` implementation, highlighting its strengths, weaknesses, and areas for attention.

### 3.1 Overall Code Structure and Quality

*   **Readability:** The code is generally well-structured and readable, with descriptive function and variable names. The use of TypeScript enhances type safety and understanding.
*   **Organization:** Functions are grouped logically (e.g., term constructors, context operations, normalization, unification, type checking, pattern matching). Global state variables (`constraints`, `globalDefs`, ID counters) are defined at the top.
*   **TypeScript Usage:** Effective use of discriminated unions for `Term` is a core strength. Type annotations are consistent. However, some `any` types or type assertions might be present implicitly if not all paths are strictly covered by TypeScript's inference, which is common in complex recursive functions found in type systems.
*   **Modularity:** While functions are grouped, the system relies on several global mutable states (`constraints`, `nextVarId`, `nextHoleId`, `userRewriteRules`, `userUnificationRules`, `globalDefs`). This simplifies passing these around but reduces modularity and makes concurrent execution or independent instantiations of the type checker problematic (though not a goal for this prototype).
*   **Debugging Traces:** The `DEBUG_VERBOSE` flag and `consoleLog` calls are helpful for development and understanding the system's behavior but should be managed or stripped for any performance-sensitive or "production" use.

### 3.2 Identified Bugs, Inconsistencies, and Areas for Concern

1.  **`whnf` Loop and `areStructurallyEqualNoWhnf`:**
    *   **Issue:** A significant historical issue was non-terminating loops in `whnf` when a rewrite rule produced a term that, while definitionally equal to the LHS, was not structurally identical before further `whnf`-ing. This could cause `whnf` to re-apply the same rule indefinitely if the rule's RHS wasn't immediately in WHNF itself but reduced back to a form matching the LHS.
    *   **Solution:** The introduction of `areStructurallyEqualNoWhnf` addresses this. After a rewrite rule application `LHS -> RHS_applied`, `whnf` now checks if `RHS_applied` is *structurally* different from the `LHS` instance *before* attempting further reduction of `RHS_applied`. If they are structurally identical *without further reduction*, that specific rule application is considered non-progressive, and `whnf` continues to try other rules or reduction steps. If `RHS_applied` is structurally different, `whnf` restarts its main loop with `RHS_applied`.
    *   **Concern:** This relies heavily on the correctness and precision of `areStructurallyEqualNoWhnf`. Any subtle differences in how terms are constructed versus how they are compared structurally (especially around HOAS or hole states) could lead to issues. The current `areStructurallyEqualNoWhnf` seems to be a direct copy of `areEqual` but without the initial `whnf` calls, which is the correct approach for this specific check.

2.  **Stack Depth and Iteration Limits (`MAX_WHNF_ITERATIONS`, `MAX_STACK_DEPTH`):**
    *   **Issue:** The system uses hardcoded limits for recursion depth in `whnf`, `normalize`, `areEqual`, `unify`, `infer`, `check`, `matchPattern`, and `termContainsHole`. Similarly, `solveConstraints` and `whnf` have iteration limits.
    *   **Concern:** These are pragmatic safeguards against non-termination or stack overflows but can lead to legitimate computations being cut off prematurely if they are complex but terminating. The current values (e.g., `MAX_STACK_DEPTH = 200`) might be too low for deeply nested terms or complex inference chains. Non-termination in type theory is a complex issue, and these limits are a blunt instrument.

3.  **Mutation and State Management:**
    *   **`ensureImplicitsAsHoles`:** This function directly mutates the input `term` by filling `undefined` implicit arguments with `Hole`s. While efficient, mutation can make reasoning about term states harder if references are shared unexpectedly.
    *   **`infer` for unannotated `Lam`:** Mutates the `Lam` term to fill `paramType` with a hole and sets `_isAnnotated = true`. This is crucial for the bidirectional algorithm but again relies on controlled mutation.
    *   **`Hole.ref` and `Hole.elaboratedType`:** These are mutable fields updated during unification and inference/checking. This is standard for unification-based systems but requires careful management.
    *   **Global State Reset in `elaborate`:** `constraints`, `nextHoleId`, `nextVarId` are reset globally. This makes each call to `elaborate` independent from the previous one in terms of fresh names and pending constraints, which is good for testing individual elaborations. However, it means the system, as a whole, doesn't accumulate constraints or maintain a persistent hole-naming context across multiple top-level `elaborate` calls if that were ever desired.

4.  **`getTermRef(term: Term)` Usage:**
    *   **Necessity:** This function is vital for working with terms that might be solved holes. It recursively follows the `ref` field of `Hole` terms until a non-hole or an unsolved hole is found.
    *   **Concern:** It's crucial that `getTermRef` is called *before* inspecting the tag or structure of any term that could potentially be a solved hole. Forgetting this could lead to operating on an outdated view of a term. The codebase appears to use this correctly in most critical places (e.g., at the start of `infer`, `check`, `unify`, `areEqual`, `matchPattern`).

5.  **`matchPattern` for HOAS (`Lam`, `Pi`):**
    *   **Limitation:** When matching a pattern `Lam P_param. P_body` against a term `Lam T_param. T_body`, the parameter types are matched recursively, but the bodies `P_body` and `T_body` (after instantiation with a fresh variable) are compared using `areEqual`. This means `matchPattern` cannot bind pattern variables *inside* the HOAS body function. The HOAS body in a pattern is effectively a template whose *resulting term structure* after instantiation is compared for equality, rather than being deconstructed for further pattern variable binding. This is a common simplification for HOAS pattern matching unless more sophisticated techniques (like higher-order pattern unification for the bodies themselves) are employed.

6.  **Error Reporting:**
    *   Error messages are generally informative (e.g., `Type error: Could not solve constraints. Approx failing: ...`, `Unbound variable: ...`).
    *   The `origin` field in `Constraint` helps trace back unification failures. However, diagnosing deeply nested unification failures or non-termination can still be challenging with the current tracing.

7.  **`applySubst` and Unbound Pattern Variables:**
    *   `applySubst` includes a `console.warn` if it encounters a pattern variable in the RHS of a rule that isn't bound in the substitution. This indicates a potential issue in rule definition (e.g., a variable used in RHS but not LHS) or in how fresh variables are handled in unification rules that introduce new constraints with unbound pattern variables. The current approach in `applyAndAddRuleConstraints` attempts to mitigate this for unification rules by instantiating such RHS-only unbound variables as fresh holes.

8.  **Consistency of `cat_IMPLICIT` handling in `IdentityMorph` `ComposeMorph`:**
    *   The `printTerm` function for `IdentityMorph` and `ComposeMorph` only prints the `cat_IMPLICIT` if it's *not* a hole (`getTermRef(current.cat_IMPLICIT).tag !== \'Hole\'`). This is a cosmetic choice but means that if a category is inferred (and remains a hole temporarily during some phase of printing/debugging), it might not be shown.
    *   In contrast, `areEqual` and `matchPattern` (via `matchOptImplicitArgPattern`) for these terms treat `undefined` implicits differently from implicits that are explicitly `Hole`s in some contexts, requiring careful handling (e.g. `matchOptImplicitArgPattern` logic).

### 3.3 Logical Flaws and Algorithmic Coherence

*   **Termination of `whnf` and `solveConstraints`:** While limits are in place, formal arguments for termination (especially in the presence of arbitrary user rewrite rules and unification rules) are complex. The current strategy relies on:
    *   `whnf` restarting on structurally different terms from rewrite rules.
    *   `solveConstraints` processing a worklist, with unification either solving, failing, or adding new (hopefully simpler or solvable) constraints.
    *   The interplay between `whnf` called inside `unify`/`areEqual` (which are called by `solveConstraints`) and `whnf`\'s own rewrite rule application loop is intricate. The current system seems to work for the Phase 1 tests, but more complex rule sets could expose edge cases.
*   **Pre-WHNF vs. Post-WHNF Unification for Injective Symbols:**
    *   `unify` attempts to unify arguments of injective constructors *before* `whnf`-ing the parent terms (Step 2). If this fails, it proceeds to `whnf` the parents and then may retry unifying arguments of injective constructors if the tags still match (Step 3, within the `isEmdashUnificationInjectiveStructurally` block).
    *   This two-pronged approach is a heuristic. The pre-WHNF check is an optimization for cases where arguments can be unified without needing to compute the parent. The post-WHNF check handles cases where reduction of the parent is necessary to expose the true structure of the arguments. This seems coherent, ensuring that reduction doesn't prevent unification of already-matching structures and that reduction can enable unification.
*   **Pattern Variable Typing in `PatternVarDecl`:**
    *   `PatternVarDecl` includes a `type` for pattern variables, but this type information is not currently used by `matchPattern` or `applySubst`. Matching is purely structural. This is a simplification; a more advanced system might use these types to constrain matches or ensure type preservation during rewriting/unification rule application.

### 3.4 Divergences from Standard Implementations or Expectations

*   **`Type : Type`:** This makes the base type theory predicative (like in CoC before universes) but inconsistent if not managed carefully (e.g. Girard's Paradox). For a prototype focused on categorical structures, this is often a pragmatic simplification to avoid the complexity of a full universe hierarchy, but it's a known deviation from systems like Agda or Lean that enforce universe levels for consistency.
*   **HOAS Implementation:** Using JavaScript functions for `Lam`/`Pi` bodies is a direct and common way to implement HOAS, leveraging the host language's binding. However:
    *   **Inspection/Serialization:** It makes it difficult to deeply inspect or serialize the structure of the function body as a `Term` without applying it.
    *   **Equality/Matching:** Equality and matching are based on applying the function to fresh variables and comparing the results, which is extensional-like for the body but doesn't allow structural matching *within* the body for pattern variables.
    *   Alternative: Explicitly represent lambda bodies as terms with De Bruijn indices/levels, which requires managing binders explicitly but allows full structural manipulation.
*   **Global Mutable State:** As mentioned, the reliance on global mutable state for constraints, fresh name generation, and rule sets is common in simpler interpreters or prototypes but differs from more robust implementations that would typically thread such state through monads or pass it explicitly.
*   **First-Order Unification with Ad-hoc Unification Rules:** The core unification is largely first-order (holes don't abstract over other holes or have complex dependent types themselves directly, though their solutions can be complex terms). User-defined unification rules (`addUnificationRule`) allow extending the unifier's capabilities in a somewhat ad-hoc way, which is flexible but lacks the systematic guarantees of, say, fully higher-order unification algorithms (which are undecidable in general) or more restricted but complete algorithms like Miller Patterms.

### 3.5 Strengths and Novel Aspects

*   **Direct Embedding of Categorical Primitives:** The most significant strength is the first-class representation of `CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`, `IdentityMorph`, and `ComposeMorph`. This allows for a more natural expression of categorical ideas compared to deep encodings.
*   **Targeted Bidirectional Typing:** The `infer` and `check` rules are specifically tailored for these categorical constructors, including the implicit argument handling and constraint generation, making type inference quite powerful for these structures.
*   **Integrated Computation:** The `whnf` rules for `MkCat_` (unfolding `ObjTerm`, `HomTerm`, `ComposeMorph` when the category is concrete) directly implement the computational semantics of these constructors.
*   **User-Defined Rules for Categorical Laws:** The ability to add rewrite rules (e.g., for identity laws of composition) and unification rules allows the system to be customized with domain-specific knowledge, moving beyond purely syntactic equality.
*   **`ensureImplicitsAsHoles` Mechanism:** This is a practical and effective solution for handling implicit arguments in a way that integrates smoothly with the unification-based elaboration process.
*   **`areStructurallyEqualNoWhnf` for Rewrite Control:** This function is a nuanced addition to control the application of rewrite rules, preventing some classes of non-productive loops by requiring immediate structural change.
*   **TypeScript for Prototyping:** Using TypeScript provides a good balance of type safety and rapid development flexibility, suitable for exploring type system designs.

This detailed review reveals a sophisticated and largely coherent system for its stage, with pragmatic solutions to common challenges in type system implementation like HOAS, implicits, and rewrite loops. The identified areas of concern are typical for prototypes and highlight avenues for future refinement and robustness improvements.

## 4. Comparative Analysis

This section compares Emdash's design and implementation choices with the provided Haskell example (`example_unification.hs`) and the Lambdapi specification (`emdash_specification_lambdapi.lp` and related documentation).

### 4.1 Comparison with `example_unification.hs` (Bidirectional Elaboration with Untyped Pattern Unification)

The `example_unification.hs` file provides a Haskell implementation of a bidirectional type checker with hole-filling via untyped pattern unification. It serves as a useful reference for certain algorithmic patterns.

#### Similarities:

*   **Bidirectional Type Checking:** Both systems employ a bidirectional approach (`infer`/`check` in Emdash, similar concepts in the Haskell example) which is standard for type systems with significant inference capabilities.
*   **Hole-Filling with Metavariables:** Both use metavariables (Emdash `Hole`, Haskell `MetaVar`) to represent unknown terms that are to be solved by unification.
*   **Untyped Pattern Unification Concept:** The Haskell example is explicitly about "untyped pattern unification." While Emdash's `unify` is primarily first-order structural, the *goal* of solving holes to satisfy type constraints is shared. Emdash's `userUnificationRules` could be seen as a way to implement specific pattern-like unification behaviors.
*   **Metas Abstracting Over Scope:** `example_unification.hs` details how metavariable solutions (`?α := λ spine. rhs`) become functions abstracting over variables in the spine (local scope). Emdash's HOAS for `Lam`/`Pi` and its use of `Hole`s that can be solved to such terms implicitly achieves a similar effect; a hole's solution can indeed be a lambda abstraction that effectively captures variables from its surrounding scope upon instantiation. The `InsertedMeta` in Haskell, applied to bound variables, is conceptually similar to how Emdash might use a hole whose inferred type forces it to be a function.
*   **Forcing Values:** The Haskell example mentions the need to `force` values to update them with respect to solved metas before pattern matching on them. Emdash achieves this implicitly by consistent use of `getTermRef` before inspecting any term that could be a (solved) hole.

#### Differences:

*   **Language and Implementation Paradigm:**
    *   **Emdash:** TypeScript, using mutable global state for constraints, IDs, and rules. HOAS is via JavaScript functions.
    *   **`example_unification.hs`:** Haskell, using `IORef`s for mutable state (metacontext, nextMeta ID) to manage side effects in a pure functional language. HOAS is via Haskell closures.
*   **Pattern Unification Implementation:**
    *   **Emdash:** The `matchPattern` function is primarily used for user-defined *rewrite rules*. Unification of holes (`unifyHole`) is first-order: `?h := term`. Higher-order aspects come from `term` itself being a `Lam` or `Pi`. There isn't a direct "pattern unification solver" for metas in the sense of `?α spine =? rhs` from the Haskell example's description. Instead, structural unification and constraint solving drive the instantiation of holes.
    *   **`example_unification.hs`:** Describes a specific algorithm for higher-order pattern unification (`solve` using `invert` and `rename`) where metas are solved to `λ spine. rhs`. This is a more specialized algorithm focused on a decidable fragment of higher-order unification.
*   **Scope and Nature of Metavariables:**
    *   **Emdash:** `Hole` terms are placeholders within the term structure. Their `ref` points to a solution, and `elaboratedType` tracks their inferred type.
    *   **`example_unification.hs`:** `MetaVar` solutions are explicitly constructed as lambda abstractions over the variables in their spine. The Haskell example also uses `InsertedMeta MetaVar [BD]` to track which local bound variables a fresh meta should be applied to, which Emdash handles by the context in which a `Hole`'s type is inferred and constrained.
*   **Focus and Features:**
    *   **Emdash:** A larger system with built-in categorical types, definitional computation rules for them, and user-defined rewrite/unification rules.
    *   **`example_unification.hs`:** A minimal, focused demonstration of the pattern unification algorithm itself within a simple type theory.
*   **Extensibility of Unification:**
    *   **Emdash:** Features `userUnificationRules`, allowing ad-hoc extensions to how unification problems are decomposed or solved.
    *   **`example_unification.hs`:** The core pattern unification is algorithmic; extensions would likely modify this core algorithm.

In essence, Emdash uses a more general-purpose first-order unifier for its holes, where the "higher-order" nature of solutions arises from the structure of terms (like `Lam`) that fill these holes. The Haskell example details a specific higher-order *pattern* unification algorithm.

### 4.2 Comparison with Lambdapi (`emdash_specification_lambdapi.lp` and Documentation)

Lambdapi is a dependently typed proof assistant based on the λΠ-calculus modulo theory. The `emdash_specification_lambdapi.lp` file provides a formal specification for Emdash's intended categorical constructs within a Lambdapi-like framework.

#### 4.2.1 Core Dependent Type Theory

*   **Similarities:**
    *   Both are dependently typed systems.
    *   Fundamental constructs like Π-types (`Pi`), λ-abstractions (`Lam`), application (`App`), and global definitions (`defineGlobal` / `constant symbol`) are present in both.
    *   Emdash's `Type : Type` is a common simplification, and Lambdapi allows defining `Type` as a `CONSTANT SYMBOL` which can then be used in signatures.
*   **Differences:**
    *   **Syntax and Implementation:** Emdash uses TypeScript syntax and is an interpreter. Lambdapi has its own S-expression like syntax and is typically a compiled kernel (often OCaml).
    *   **Eta-Equality:** Lambdapi explicitly has a flag for `eta_equality`. Emdash's `areEqual` for `Lam` performs beta-reduction and compares instantiated bodies, which is more aligned with beta-equality. Full eta-equality (`λx. f x === f` if `x` is not free in `f`) is not explicitly implemented or tested as a conversion rule in Emdash `whnf` or `areEqual`.
    *   **Proof System vs. Type Checker:** Lambdapi is a full proof assistant, implying features like tactic-based proof, explicit proof terms, etc. Emdash is currently focused on type checking, elaboration, and computation based on its defined rules.
    *   **Universes/Sorts:** Lambdapi's use of `TYPE` (e.g., `constant symbol Type : TYPE;`) suggests a more structured universe system, while Emdash uses a single sort `Type` where `Type: Type`, which is known to be inconsistent without careful management (like Girard's Paradox) but is a common simplification for prototypes. The `τ` symbol in Lambdapi (e.g., `injective symbol τ : Type → TYPE;`, `rule τ (Obj_Type $A) ↪ Obj $A;`) seems related to this, possibly as a coercion or sort annotation, which Emdash doesn't have due to its simpler type hierarchy.
    *   **Builtins:** Lambdapi uses `builtin` declarations (e.g., for `eq`, `refl`). Emdash primitives are hardcoded into the `Term` type and associated functions.

#### 4.2.2 Categorical Constructs (Comparing `emdash_v2.ts` to `emdash_specification_lambdapi.lp`)

Emdash aims to implement the categorical structures defined in `emdash_specification_lambdapi.lp`.

*   **`Cat` (Type of Categories):**
    *   LP: `constant symbol Cat : TYPE;`
    *   TS: `CatTerm()` which has type `Type`. This aligns.
*   **`Obj` (Type of Objects in a Category):**
    *   LP: `injective symbol Obj : Cat → TYPE;` (also `Obj_Type` with `τ (Obj_Type $A) ↪ Obj $A;`)
    *   TS: `ObjTerm(cat: Term)` which has type `Type`. The `cat` argument must be of type `CatTerm`. `ObjTerm` is unification-injective. This aligns with `Obj` being injective.
*   **`Hom` (Type of Morphisms):**
    *   LP: `injective symbol Hom : Π [A : Cat] (X: Obj A) (Y: Obj A), TYPE;` (also `Hom_Type`)
    *   TS: `HomTerm(cat: Term, dom: Term, cod: Term)` which has type `Type`. Arguments must be well-typed. `HomTerm` is unification-injective. This aligns.
*   **`identity_morph` (Identity Morphism):**
    *   LP: `injective symbol identity_morph : Π[A : Cat], Π(X: Obj A), Hom X X;`
    *   TS: `IdentityMorph(obj: Term, cat_IMPLICIT?: Term)`. Infers type `HomTerm C X X` where `obj: ObjTerm C` and `X` is `obj`. `cat_IMPLICIT` is inferred. `IdentityMorph` is unification-injective. This aligns.
*   **`compose_morph` (Morphism Composition):**
    *   LP: `symbol compose_morph : Π [A : Cat], Π [X: Obj A], Π [Y: Obj A], Π [Z: Obj A], Π (g: Hom Y Z), Π (f: Hom X Y), Hom X Z;` (Note: LP uses `compose_morph g f` for `f ; g` or `g after f`).
    *   TS: `ComposeMorph(g: Term, f: Term, cat_IMPLICIT?, objX_IMPLICIT?, objY_IMPLICIT?, objZ_IMPLICIT?)`. The order `(g, f)` implies `f` then `g`. Infers type `HomTerm C X Z`. Implicits are inferred. `ComposeMorph` is *not* unification-injective on `g` and `f`. This also aligns with LP's `compose_morph` being a plain `symbol`.
*   **Identity Laws for Composition (Rewrite Rules):**
    *   LP: `rule compose_morph $f (identity_morph _) ↪ $f;` and `rule compose_morph (identity_morph _) $f ↪ $f;`
    *   TS: Implemented as user rewrite rules (`comp_g_idX_fwd`, `comp_idY_f_fwd`) in `setupPhase1GlobalsAndRules`. These rules match specific `ComposeMorph` structures involving `IdentityMorph`. The LP rules use pattern variables (`$f`) making them more general. Emdash's current rules are concrete instantiations.
        *   `comp_g_idX_fwd`: `ComposeMorph(g, id_X, C, X, X, Y) -> g` (corresponds to `g <∘ id` in LP if `g` is `$f`, or `g ∘ id` in standard math).
        *   `comp_idY_f_fwd`: `ComposeMorph(id_Y, f, C, X, Y, Y) -> f` (corresponds to `id <∘ f` in LP if `f` is `$f`, or `id ∘ f` in standard math).
*   **`mkCat_` (Category Constructor):**
    *   LP: `constant symbol mkCat_ : Π (Obj : Type) (Hom : Π (X:τ Obj) (Y: τ Obj), Type) (compose_morph : ...), Cat;`
    *   TS: `MkCat_(objRepresentation: Term, homRepresentation: Term, composeImplementation: Term)`. The argument types align with the LP specification (a type for objects, a type-former for Homs, and a term for composition). `MkCat_` is a "constant symbol" in TS.
*   **`mkCat_` Unfolding Rules (Computational Rules):**
    *   LP:
        *   `rule @Obj (mkCat_ $O $H $C) ↪ τ $O;`
        *   `rule @Hom (mkCat_ $O $H $C) $X $Y ↪ τ ($H $X $Y);`
        *   `rule @compose_morph (mkCat_ $O $H $C) ↪ $C;` (This implies that `compose_morph (mkCat_ O H Cimpl) X Y Z g f` would reduce using `Cimpl`).
    *   TS: These are implemented as head-specific reductions in `whnf`:
        *   `whnf(ObjTerm(MkCat_(O, H, C)))` ↪ `O`
        *   `whnf(HomTerm(MkCat_(O, H, C), X, Y))` ↪ `App(App(H, X), Y)`
        *   `whnf(ComposeMorph(g, f, cat = MkCat_(O,H,Cimpl), objX, objY, objZ))` ↪ `App(App(App(App(App(Cimpl, objX), objY), objZ), g), f)`
    *   This is a direct and faithful implementation of the computational behavior specified in LP.
*   **"Constant Symbol" vs. "Injective Symbol" Semantics:**
    *   LP: Uses these explicit keywords. `constant symbol`s are opaque and cannot be LHS of user rules. `injective symbol`s allow unification to proceed on arguments.
    *   TS:
        *   `EMDASH_CONSTANT_SYMBOLS_TAGS` (`CatTerm`, `MkCat_`): These are unification-injective and also block user rewrite rules where they are the head of the LHS.
        *   `EMDASH_UNIFICATION_INJECTIVE_TAGS` (`IdentityMorph`, `CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`): These are unification-injective.
        *   This mapping is largely consistent. For example, `mkCat_` is `constant` in LP and TS. `Obj`, `Hom`, `identity_morph` are `injective` in LP and TS (for the latter, via its tag being in `EMDASH_UNIFICATION_INJECTIVE_TAGS`). `compose_morph` is a plain `symbol` in LP, and its Emdash counterpart `ComposeMorph` is not unification-injective on its function arguments `f` and `g`.
*   **User-Defined Unification Rules:**
    *   LP: Has `unif_rule ... ↪ ... ;`. For example, `unif_rule Obj $A ≡ Type ↪ [ $A ≡ Set ];` from the "Yoneda" section.
    *   TS: Has `addUnificationRule({ name, patternVars, lhsPattern1, lhsPattern2, rhsNewConstraints })`. This provides a similar mechanism for users to guide or extend the unification behavior.

#### 4.2.3 Summary of Emdash's Approach in Relation to Comparisons

*   **Elaboration Strategy:** Emdash uses bidirectional typing with constraint generation and solving, similar in spirit to how many modern type systems (including those in proof assistants like Coq/Lean, which Lambdapi shares heritage with) operate. The explicit `elaborate` function orchestrates this.
*   **Type Inference for Implicits:** The `ensureImplicitsAsHoles` coupled with constraint generation in `infer`/`check` is a practical way to handle implicit arguments, a common feature in systems like Agda or Idris, and emulated here.
*   **Hole Solving:** First-order unification is the primary mechanism. The system doesn't implement a full higher-order unification algorithm like that sometimes found in Isabelle/HOL or experimental systems, but relies on the structure of solutions (e.g., a hole being solved to a `Lam` term).
*   **Definitional Equality and Computation:**
    *   `whnf` with beta, delta, and Emdash-specific unfolding rules (for `MkCat_`) forms the core of definitional equality.
    *   User-defined rewrite rules (`addRewriteRule`) allow extending this computation, akin to how rewrite rules work in Lambdapi or other systems supporting computation modulo theory. The priority given to user rules over some built-in reductions (like `MkCat_` unfolding for `ComposeMorph` if specific identity rewrite rules are present) is a design choice.
*   **Consistency with Lambdapi Specification:** For Phase 1, Emdash's TypeScript implementation of core categorical constructs (`CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`, `IdentityMorph`, `ComposeMorph`) and their basic computational rules (unfolding `MkCat_`, identity laws via rewrite rules) is largely faithful to the `emdash_specification_lambdapi.lp`. The main deviations are:
    *   Syntactic differences (TS vs. LP).
    *   Emdash's explicit implicit argument handling mechanism (`_IMPLICIT` fields, `ensureImplicitsAsHoles`). Lambdapi often handles implicits through its own more general mechanisms.
    *   The simpler `Type : Type` system in Emdash.
    *   The interactive proof aspects of Lambdapi are not yet present in Emdash.

Emdash effectively uses standard type theory implementation techniques (bidirectional checking, unification-based elaboration, HOAS via host language) to realize a system with first-class categorical primitives as outlined in its Lambdapi specification. The design choices favor direct implementation of categorical operations and inference for a more "synthetic" feel.

## 5. Emdash Type Theory Specification (Phase 1)

This section details the type theory implemented in Emdash `emdash_v2.ts`, focusing on the core system and the Phase 1 categorical extensions.

### 5.1 Core Type System: MyLambdaPi Base

Emdash is built upon a simplified dependent type system, referred to as "MyLambdaPi."

*   **Sorts:**
    *   A single sort `Type`.
    *   Axiom: `Type : Type`. This is a common simplification for prototypes, but it makes the system predicative and potentially inconsistent (Girard's Paradox) if not carefully managed with additional mechanisms like explicit universe levels, which are not currently implemented.

*   **Terms:**
    1.  **`Type`**: The sort of all types.
        *   Formation: `Γ ⊢ Type : Type`
    2.  **`Var(name: string)`**: Variables.
        *   Lookup: If `(x : A) ∈ Γ`, then `Γ ⊢ x : A`.
    3.  **`Lam(paramName: string, paramType?: Term, body: (v: Term) => Term)`**: Lambda abstraction.
        *   Introduction (Annotated):
            \[ \frac{\Gamma \vdash A : \text{Type} \quad \Gamma, x:A \vdash t : B(x)}{\Gamma \vdash (\lambda x:A. t) : (\Pi x:A. B(x))} \]
        *   Introduction (Unannotated - for inference):
            \[ \frac{\Gamma, x:\text{?A} \vdash t : \text{?B}(x)}{\Gamma \vdash (\lambda x. t) : (\Pi x:\text{?A}. \text{?B}(x))} \]
            (where `?A` is a fresh hole for the parameter type, inferred during elaboration).
    4.  **`App(func: Term, arg: Term)`**: Application.
        *   Elimination:
            \[ \frac{\Gamma \vdash f : (\Pi x:A. B(x)) \quad \Gamma \vdash a : A}{\Gamma \vdash f(a) : B(a)} \]
    5.  **`Pi(paramName: string, paramType: Term, bodyType: (v: Term) => Term)`**: Dependent function type (Π-type).
        *   Formation:
            \[ \frac{\Gamma \vdash A : \text{Type} \quad \Gamma, x:A \vdash B(x) : \text{Type}}{\Gamma \vdash (\Pi x:A. B(x)) : \text{Type}} \]
    6.  **`Hole(id?: string)`**: Metavariables or placeholders.
        *   During elaboration, a hole `?h` is assigned an `elaboratedType` (often another hole, e.g., `?t_h`). Constraints are generated based on its usage, and `solveConstraints` attempts to find a term `s` such that `?h := s` and `?t_h` is solved to its actual type.

*   **Key Operations:**
    *   **Context (`Γ`)**: A list of variable bindings `x : A`.
    *   **Bidirectional Type Checking**: `infer(Γ, t) 返す A` and `check(Γ, t, A)`.
    *   **Definitional Equality (`===`)**: Based on `whnf` and structural comparison. Includes β-reduction and δ-reduction (unfolding of global definitions that are not `isConstantSymbol`).
    *   **Global Definitions**: `defineGlobal(name, type, value?, isConstantSymbol?)`.
    *   **User Rewrite Rules**: `addRewriteRule(rule)` allows adding equational rules applied during `whnf`.
    *   **User Unification Rules**: `addUnificationRule(rule)` allows adding rules to guide the `unify` process.

### 5.2 Emdash Phase 1: Core Categorical Constructs

These are new primitive term constructors and types extending the MyLambdaPi base.

1.  **`CatTerm()` (The Type of Categories)**
    *   **Term Constructor:** `CatTerm`
    *   **Type Formation Rule:**
        \[ \frac{}{\Gamma \vdash \text{CatTerm} : \text{Type}} \]
    *   **Semantics:** Represents the type "Cat", the collection of all categories.
    *   **Properties:**
        *   "Constant Symbol": `whnf(CatTerm())` is `CatTerm()`. Its tag `CatTerm` is unification-injective. It cannot be the head of a user rewrite rule.

2.  **`ObjTerm(cat: Term)` (The Type of Objects in a Category)**
    *   **Term Constructor:** `ObjTerm`
    *   **Argument:** `cat : CatTerm`
    *   **Type Formation Rule:**
        \[ \frac{\Gamma \vdash C : \text{CatTerm}}{\Gamma \vdash \text{ObjTerm}(C) : \text{Type}} \]
    *   **Semantics:** Represents `Obj C`, the type of objects in a category `C`.
    *   **Properties:**
        *   "Unification-Injective Symbol": If `ObjTerm(C1) === ObjTerm(C2)`, then `C1 === C2` is added as a constraint.

3.  **`HomTerm(cat: Term, dom: Term, cod: Term)` (The Type of Morphisms)**
    *   **Term Constructor:** `HomTerm`
    *   **Arguments:**
        *   `cat : CatTerm`
        *   `dom : ObjTerm(cat)`
        *   `cod : ObjTerm(cat)`
    *   **Type Formation Rule:**
        \[ \frac{\Gamma \vdash C : \text{CatTerm} \quad \Gamma \vdash X : \text{ObjTerm}(C) \quad \Gamma \vdash Y : \text{ObjTerm}(C)}{\Gamma \vdash \text{HomTerm}(C, X, Y) : \text{Type}} \]
    *   **Semantics:** Represents `Hom C X Y`, the type of morphisms from object `X` to object `Y` in category `C`.
    *   **Properties:**
        *   "Unification-Injective Symbol": If `HomTerm(C1,D1,E1) === HomTerm(C2,D2,E2)`, then constraints `C1===C2`, `D1===D2`, `E1===E2` are added.

4.  **`MkCat_(objRepresentation: Term, homRepresentation: Term, composeImplementation: Term)` (Category Constructor)**
    *   **Term Constructor:** `MkCat_`
    *   **Arguments:**
        *   `objRepresentation : Type` (Type of the objects' underlying representation)
        *   `homRepresentation : Π X:objRepresentation. Π Y:objRepresentation. Type` (Function forming Hom-set types from object representations)
        *   `composeImplementation : Π X:objRepresentation. Π Y:objRepresentation. Π Z:objRepresentation. Π g:(homRepresentation Y Z). Π f:(homRepresentation X Y). (homRepresentation X Z)` (The composition operation)
    *   **Type Rule (Introduction):**
        \[ \frac{\Gamma \vdash O_{rep} : \text{Type} \quad \Gamma \vdash H_{rep} : (\Pi X:O_{rep}. \Pi Y:O_{rep}. \text{Type}) \quad \Gamma \vdash C_{impl} : (\Pi X:O_{rep} \dots \Pi f:(H_{rep} X Y). (H_{rep} X Z))}{\Gamma \vdash \text{MkCat_}(O_{rep}, H_{rep}, C_{impl}) : \text{CatTerm}} \]
    *   **Semantics:** Constructs a concrete category.
    *   **Properties:**
        *   "Constant Symbol": Its tag `MkCat_` is unification-injective and blocks user rewrite rules.
    *   **Computational Rules (Emdash Unfolding in `whnf`):**
        *   `ObjTerm(MkCat_(O, H, Cimpl))` ↪ `O`
        *   `HomTerm(MkCat_(O, H, Cimpl), X, Y)` ↪ `App(App(H, X), Y)`
        *   `ComposeMorph(g, f, cat=MkCat_(O,H,Cimpl), X, Y, Z)` ↪ `App(App(App(App(App(Cimpl,X),Y),Z),g),f)`
            *(Requires `cat` to reduce to `MkCat_` and implicits `X,Y,Z` to be present/inferred for `ComposeMorph`)*

5.  **`IdentityMorph(obj: Term, cat_IMPLICIT?: Term)` (Identity Morphism)**
    *   **Term Constructor:** `IdentityMorph`
    *   **Arguments:**
        *   `obj : ObjTerm(C)` (for some category `C`)
        *   `cat_IMPLICIT : CatTerm` (Inferred to be `C` if not provided)
    *   **Type Rule (Introduction):**
        \[ \frac{\Gamma \vdash C : \text{CatTerm} \quad \Gamma \vdash X : \text{ObjTerm}(C)}{\Gamma \vdash \text{IdentityMorph}(X, \text{cat_IMPLICIT}=C) : \text{HomTerm}(C, X, X)} \]
        (Elaboration fills `cat_IMPLICIT` with a hole `?cat` and adds constraint `type(X) === ObjTerm(?cat)`).
    *   **Properties:**
        *   "Unification-Injective Symbol": If `IdentityMorph(o1, c1) === IdentityMorph(o2, c2)`, then `o1===o2` and `c1===c2` are added as constraints.

6.  **`ComposeMorph(g: Term, f: Term, cat_IMPLICIT?: Term, objX_IMPLICIT?: Term, objY_IMPLICIT?: Term, objZ_IMPLICIT?: Term)` (Morphism Composition)**
    *   **Term Constructor:** `ComposeMorph` (represents `g ∘ f`, meaning `f` then `g`)
    *   **Arguments:**
        *   `f : HomTerm(C, X, Y)`
        *   `g : HomTerm(C, Y, Z)`
        *   Implicits: `cat_IMPLICIT` (C), `objX_IMPLICIT` (X), `objY_IMPLICIT` (Y), `objZ_IMPLICIT` (Z). These are inferred.
    *   **Type Rule (Introduction):**
        \[ \frac{\Gamma \vdash C:\text{CatTerm} \quad \Gamma \vdash X:\text{ObjTerm}(C) \quad \Gamma \vdash Y:\text{ObjTerm}(C) \quad \Gamma \vdash Z:\text{ObjTerm}(C) \quad \Gamma \vdash f : \text{HomTerm}(C,X,Y) \quad \Gamma \vdash g : \text{HomTerm}(C,Y,Z)}{\Gamma \vdash \text{ComposeMorph}(g,f, \text{impls...}) : \text{HomTerm}(C,X,Z)} \]
        (Elaboration fills implicits with holes and generates constraints like `type(f) === HomTerm(?cat, ?X, ?Y)`, `type(g) === HomTerm(?cat, ?Y, ?Z)`).
    *   **Properties:**
        *   **Not** unification-injective on `f` and `g`. Equality relies on reduction.
    *   **Computational Rules:**
        *   **Emdash Unfolding (from `MkCat_`):** See above.
        *   **User Rewrite Rules for Identity Laws (higher priority than `MkCat_` unfolding for `ComposeMorph`):**
            *   `ComposeMorph(g, IdentityMorph(X, C), C, Z, X, X) ↪ g` (where `g : Hom C Z X`)
            *   `ComposeMorph(IdentityMorph(Y, C), f, C, Y, Y, X) ↪ f` (where `f : Hom C X Y`)
            *(Note: The actual TypeScript implementation uses specific variable names and implicit argument order in the rewrite rule LHS.)*

### 5.3 Implicit Arguments and Elaboration Strategy

*   Constructors `IdentityMorph` and `ComposeMorph` have optional `_IMPLICIT` arguments.
*   The `ensureImplicitsAsHoles` function, called by `infer`/`check`, mutates terms to fill these with fresh `Hole`s if undefined.
*   Type checking rules for these constructors then generate equality constraints involving these holes and the types of explicit arguments.
*   `solveConstraints` attempts to unify these holes. The results of unification directly modify the `ref` of these `Hole`s, effectively filling in the implicit arguments.
*   The final elaborated term, after normalization, will contain these inferred arguments (or the holes if they couldn't be fully resolved).

### 5.4 "Constant Symbol" and "Injective Symbol" Semantics

*   **Constant Symbol (Tags):** (`CatTerm`, `MkCat_`)
    1.  Unification-injective: `MkCat_(...) === MkCat_(...)` unifies respective arguments.
    2.  Blocked for rewrite rule LHS: `whnf` does not attempt user rewrite rules if the term's head tag is a constant symbol tag.
*   **Constant Symbol (Globals):** `defineGlobal(name, type, undefined, isConstantSymbol=true)` creates an opaque global that cannot be unfolded by delta-reduction and cannot be the head of a user rewrite rule.
*   **Unification-Injective Symbol (Tags):** (`IdentityMorph`, `ObjTerm`, `HomTerm`, plus all constant symbol tags). `unify` will directly compare their arguments if tags match.
*   **`ComposeMorph` is notably *not* unification-injective for its main `f` and `g` arguments.** Its equality is determined by reduction or specific unification rules.

### 5.5 Current Limitations

*   **`Type : Type`:** Potential for inconsistency (Girard's Paradox). No universe hierarchy.
*   **No explicit η-equality for functions:** Definitional equality is primarily βδ-equality.
*   **Limited Higher-Order Unification:** Hole solving is first-order. While solutions can be higher-order terms, the unification process itself doesn't employ general higher-order algorithms.
*   **Termination:** Relies on iteration/recursion depth limits rather than formal termination proofs for all configurations of rules.
*   **Pattern Matching for HOAS:** Limited capabilities for matching *inside* HOAS bodies.
*   **Error Reporting:** While functional, deep diagnostic capabilities for complex unification failures or non-termination could be improved.
*   **Proof Terms/Tactics:** Not a proof assistant; no explicit proof terms or tactic system.
*   **Modularity of State:** Global mutable state for constraints, IDs, and rules.

## 6. Development Journey

The development of Emdash (Phase 1) involved tackling several common and some specific challenges related to implementing a dependently typed system with categorical features.

### 6.1 Initial Challenges and Solutions

1.  **Representing Higher-Order Abstract Syntax (HOAS):**
    *   **Problem:** How to represent terms like `Lam(param, body)` and `Pi(param, paramType, bodyType)` where the `body`/`bodyType` depends on the `param`.
    *   **Solution:** Adopted the standard HOAS approach using JavaScript functions: `body: (v: Term) => Term`. This leverages JavaScript's lexical scoping for binders.
        *   *Manipulation:* Operations like `infer`, `check`, `normalize`, `areEqual`, `matchPattern`, and `applySubst` instantiate these functions with fresh variables when they need to operate on the body's structure.
    *   **Trade-offs:** Simplifies binder management but makes direct structural inspection/matching of the raw function body difficult.

2.  **Implementing Definitional Equality (`areEqual`):**
    *   **Problem:** Defining when two terms are considered the same.
    *   **Solution:** Based on reducing both terms to Weak Head Normal Form (`whnf`) and then performing a structural comparison.
        *   For HOAS terms (`Lam`, `Pi`), this involves instantiating bodies with a fresh, common variable and recursively comparing the results.
    *   **Challenge:** Ensuring `whnf` is correct and handles all necessary reductions (β, δ, and new Emdash-specific unfoldings).

3.  **Bidirectional Type Checking (`infer`/`check`):**
    *   **Problem:** Efficiently determining if a term is well-typed and inferring its type when possible.
    *   **Solution:** Implemented a standard bidirectional system.
        *   `infer(Γ, term)` attempts to synthesize a type for `term`.
        *   `check(Γ, term, expectedType)` verifies `term` against `expectedType`.
    *   **Key Interactions:**
        *   Checking an application `App(f, a)` against type `B_expected`: Infer type of `f` to be `Π x:A. B_actual`, check `a:A`, then unify `B_actual[a/x]` with `B_expected`.
        *   Inferring an unannotated `Lam x.t`: Create a hole `?A` for `x`'s type, infer `t : ?B` in context `x : ?A`, result type is `Π x:?A. ?B`.
        *   Checking `Lam x.t` against `Π x:A. B`: Annotate `x` with `A`, then check `t:B` in context `x:A` (deep elaboration of lambda body).

4.  **Hole Filling and Unification:**
    *   **Problem:** Allowing underscores (`_`) or missing terms (like implicit arguments) to be automatically determined.
    *   **Solution:**
        1.  Represent underscores/implicits as `Hole` terms.
        2.  `infer`/`check` generate `Constraint`s (equality claims like `type_of_hole === expected_type_for_hole`).
        3.  `solveConstraints` iterates through constraints, calling `unify(t1, t2)`.
        4.  `unifyHole(?h, term)` attempts to solve `?h := term` after an occurs check (`termContainsHole`).
    *   **Initial Simplification:** Started with basic first-order unification.

5.  **Implicit Arguments for Categorical Constructors:**
    *   **Problem:** Constructors like `IdentityMorph(obj)` and `ComposeMorph(g, f)` have implicit category and object arguments (e.g., `C`, `X`, `Y`, `Z`). These need to be inferred.
    *   **Solution (`ensureImplicitsAsHoles` and Constraint Generation):**
        1.  `IdentityMorph` and `ComposeMorph` TypeScript types have optional `_IMPLICIT` fields.
        2.  `ensureImplicitsAsHoles` (called by `infer`/`check`) mutates these terms to fill `undefined` implicits with fresh `Hole`s.
        3.  `infer` rules for these constructors add constraints:
            *   `IdentityMorph(obj, ?cat)`: `infer(obj) === ObjTerm(?cat)`.
            *   `ComposeMorph(g, f, ?cat, ?X, ?Y, ?Z)`: `check(f, Hom(?cat,?X,?Y))`, `check(g, Hom(?cat,?Y,?Z))`.
        4.  `check` rules provide more direct constraints if an expected `HomTerm` is given. For example, `check(IdentityMorph(obj, ?cat_id), HomTerm(C_exp, D_exp, E_exp))` generates `?cat_id === C_exp`, `obj === D_exp`, `obj === E_exp`.
    *   This mechanism proved effective for inferring these critical but often unstated arguments.

### 6.2 Evolving `whnf` and Rewrite Rule Application

1.  **Initial `whnf`:** Focused on β-reduction, δ-reduction (global defs), and the new Emdash unfolding rules for `MkCat_`.
2.  **Introducing User Rewrite Rules:**
    *   **Problem:** Needed a way to implement categorical laws like identity laws for composition, which are not β-reductions.
    *   **Solution:** Added `userRewriteRules` and logic in `whnf` to try `matchPattern(rule.lhs, term)` and then `applySubst(rule.rhs, ...)` if a match occurs.
3.  **Non-Terminating `whnf` Loop with Rewrite Rules:**
    *   **Problem:** A major hurdle was that a rewrite rule `LHS -> RHS` might apply, and `RHS` (after some computation) could reduce back to a form identical or definitionally equal to `LHS`, causing `whnf` to loop indefinitely by reapplying the same rule. This happened even if the rule was "correct" (e.g., `A -> A`). The issue was that `whnf` would restart if *any* change occurred, and the "change" might be undone by subsequent reductions within the same `whnf` call before the rule was considered again.
    *   **Initial Attempt (Flawed):** Trying to compare `whnf(RHS)` with `whnf(LHS)` was too complex and could lead to its own loops or incorrect assessments of progress.
    *   **Refined Solution (`areStructurallyEqualNoWhnf`):**
        *   When a rewrite rule `rule.lhs` matches a `termToMatch` (which is `current` in `whnf`) resulting in `rhsApplied`, `whnf` now explicitly checks if `rhsApplied` is *structurally identical* to `termToMatch` *without further reduction*.
        *   `areStructurallyEqualNoWhnf` was created for this, essentially being `areEqual` but without the initial `whnf` calls on its arguments.
        *   If `areStructurallyEqualNoWhnf(rhsApplied, termToMatch)` is true, that specific rule application is deemed non-progressive for this iteration, and `whnf` continues to other reduction steps or rules.
        *   If `rhsApplied` is structurally different, `whnf` considers this progress, updates `current = rhsApplied`, and restarts its main reduction loop (to ensure hole dereferencing or other prior steps get a chance on the new term).
    *   This provided a more stable way to ensure rewrite rules make concrete structural progress before `whnf` commits to restarting.

4.  **Order of Reductions in `whnf`:**
    *   The current order is: 1. Hole dereferencing, 2. User Rewrite Rules, 3. Head-specific (β, categorical, δ).
    *   This order prioritizes user rules over built-in unfoldings for terms that aren't kernel constants, allowing, for example, identity laws for `ComposeMorph` to apply before `ComposeMorph` unfolds due to a `MkCat_`.

### 6.3 Unification Logic Refinements

1.  **Basic Unification and Occurs Check:**
    *   Implemented `unifyHole` with `termContainsHole` for the occurs check.
2.  **Injective Symbols:**
    *   Identified certain term tags (`ObjTerm`, `HomTerm`, `IdentityMorph`, `MkCat_`, `CatTerm`) as "unification-injective."
    *   `unify` was augmented to, if tags match and are injective, recursively unify arguments.
3.  **Pre-WHNF vs. Post-WHNF Unification for Injectives:**
    *   **Problem:** Should arguments of injective constructors be unified before or after `whnf`-ing the constructors themselves? Doing it only after `whnf` might miss cases where arguments are already unifiable. Doing it only before might fail if arguments need reduction.
    *   **Solution:** `unify` now tries to unify arguments of injective constructors *before* `whnf`-ing the parent terms (Step 2). If that fails, it proceeds to `whnf` the parents (Step 3) and then, if the tags are still matching and injective, retries unifying the (now potentially reduced) arguments.
4.  **User-Defined Unification Rules:**
    *   **Motivation:** Some unification problems are not straightforward structural decomposition (e.g., `?X === Type` might imply `?X` should be unified with `Type`, but this could also be a custom rule like `Obj ?C === Type` implies `?C === Set` from the LP spec).
    *   **Solution:** Added `userUnificationRules` which allow specifying `lhsPattern1 === lhsPattern2` should lead to `rhsNewConstraints`. `tryUnificationRules` is called by `unify` when structural unification fails or is not applicable.

### 6.4 Stack Depth and Iteration Limits

*   **Problem:** Recursive functions (`whnf`, `normalize`, `areEqual`, `unify`, `infer`, `check`, `matchPattern`, `termContainsHole`) and loops (`solveConstraints`, `whnf`) can lead to stack overflows or non-termination for complex inputs or ill-defined rules.
*   **Solution:** Introduced `MAX_STACK_DEPTH` and `MAX_WHNF_ITERATIONS` / `solveConstraints` iteration limits.
*   **Ongoing Concern:** These are pragmatic but not a complete solution for guaranteeing termination or handling extremely deep computations. They are a common practical measure in interpreters.

### 6.5 Anticipating Future Problems

*   **Scalability of Constraint Solving:** As more complex features (like functors, natural transformations with their laws) are added, the number and complexity of constraints could grow, potentially slowing down `solveConstraints`. Optimization strategies or more incremental solving might be needed.
*   **Termination with More Expressive Rules:** Adding more powerful rewrite or unification rules (especially higher-order ones) will increase the risk of non-termination if not carefully designed (e.g., ensuring confluence and strong normalization for rewrite systems).
*   **Universe Management:** If the system moves beyond `Type:Type`, implementing a consistent universe hierarchy is a significant undertaking.
*   **Proof Irrelevance (if proofs were added):** Managing proof terms and ensuring proof irrelevance (if desired) adds complexity.
*   **Interaction between Features:** Ensuring that new features (e.g., functoriality rules) interact correctly with existing ones (e.g., `MkCat_` unfolding) will require careful testing and design. For example, how should `fapp1 F (identity_morph X)` (which should reduce to `identity_morph (fapp0 F X)`) interact if `F` itself is a `mkFunctor_` that unfolds? The order of rewrite rule application versus `MkCat_`/`mkFunctor_` unfolding needs to be well-defined.

The development journey has been iterative, with solutions to problems like rewrite looping and implicit argument handling being key refinements. The current system provides a solid base for Phase 1, but future phases will require continued attention to these foundational aspects.

### 6.6 Refactoring `check(Lam, Pi)` for Deep Elaboration

A key part of bidirectional type checking is the rule for checking an unannotated lambda abstraction `λx. body` against an expected Pi-type `Πx:A. Bx`. This rule typically involves:
1.  Using the type `A` from the Pi-type to annotate the lambda's parameter `x`.
2.  Then, checking that the lambda's `body` (with `x` now considered to have type `A`) conforms to the expected body type `Bx`. This is often referred to as "deep elaboration" of the lambda body.

**Previous Implementation (HOAS Body Replacement):**

The initial implementation of this rule in `check(ctx, term, expectedType)` for the case `term = Lam(...)` and `expectedType = Pi(...)` (after normalization) involved the following steps:
1.  Identify the lambda term to be annotated (`lamToAnnotate`).
2.  Mutate `lamToAnnotate` by setting its `paramType` to `expectedPi.paramType` and `_isAnnotated = true`.
3.  **Crucially, the `body` field of `lamToAnnotate` (which is a HOAS JavaScript function) was replaced with a *new* JavaScript function.** This new function, when invoked with an argument `v_arg` (representing the lambda parameter):
    a.  Called the *original* body function: `freshInnerRawTerm = originalBodyFn(v_arg)`.
    b.  Constructed an appropriate context `ctxForInnerBody` by extending the outer `check`'s context with `v_arg` and its (now annotated) type.
    c.  Determined the `expectedTypeForInnerBody` by evaluating `expectedPi.bodyType(v_arg)`.
    d.  Performed a recursive call: `check(ctxForInnerBody, freshInnerRawTerm, expectedTypeForInnerBody)`.
    e.  Returned `freshInnerRawTerm`.
4.  After this HOAS body replacement, the `check` function would then immediately make a call like `check(extendedCtx, lamToAnnotate.body(Var(paramName)), expectedPi.bodyType(Var(paramName)))` to trigger the newly installed checking logic within the modified body.

This approach, while functional, was somewhat indirect. The modification of the HOAS function itself made the flow of control for the deep elaboration less immediately obvious from the main `check` function's structure.

**Refactored Implementation (Direct Body Check):**

The `check(Lam, Pi)` rule was refactored for clarity and more direct logic:
1.  When `check` is called with an unannotated `Lam` and an expected `Pi` type:
2.  Identify the lambda term instance that needs its annotation updated for the scope of the current elaboration (e.g., `lamToUpdateAnnotation`). If found, its `paramType` is set from `expectedPi.paramType` and `_isAnnotated` is set to `true`.
3.  The core logic then proceeds directly:
    a.  The parameter name (`paramName`) and type (`paramType`) are taken from the lambda and the expected Pi-type.
    b.  An `extendedCtx` is created: `extendCtx(ctx, paramName, paramType)`.
    c.  The lambda's original HOAS body function is invoked with a variable representing its parameter: `actualBodyTerm = lamTerm.body(Var(paramName))`.
    d.  The Pi-type's body type function is also invoked with the same variable: `expectedBodyPiType = expectedPi.bodyType(Var(paramName))`.
    e.  A direct recursive call is made: `check(extendedCtx, actualBodyTerm, expectedBodyPiType)`.

**Motivation and Outcome:**

This refactoring achieves the same "deep elaboration" goal but in a more straightforward manner. It avoids modifying the lambda's HOAS `body` function with another layer of HOAS function. Instead, it directly instantiates the original body and the expected body type and performs the check. This makes the logic more localized and easier to follow within the `check` function.

This change was made after resolving several issues related to context handling in `areEqual` for `Lam` and `Pi` types, particularly when `infer(Lam)` constructs `Pi` types whose bodies involve further `infer` calls. After this refactoring (and the related `areEqual` fixes), all existing tests, including new Test B11 specifically designed for `check(Lam, Pi)`, continued to pass, suggesting the change is robust for the current test suite. Documenting this allows for easier review or reversion if future, more complex scenarios reveal issues.

## 7. Future Work and Improvements

With Phase 1 (Core Categories) complete, Emdash has a foundational layer. Future work can expand its capabilities in several directions, from implementing more categorical structures to refining the core type system.

### 7.1 Immediate Next Steps: Phase 2 (Functors and Natural Transformations)

This is the highest priority and will be detailed further in the "Roadmap for Phase 2" section. It involves:

*   Defining `FunctorTerm(srcCat, tgtCat)` type.
*   Defining `MkFunctor_` term constructor with object mapping (`fapp0`) and morphism mapping (`fapp1`).
*   Implementing computational rules for `fapp0(MkFunctor_(...))` and `fapp1(MkFunctor_(...))`.
*   Adding rewrite rules for functor laws:
    *   `fapp1 F (identity_morph X) ↪ identity_morph (fapp0 F X)`
    *   `fapp1 F (compose_morph g f) ↪ compose_morph (fapp1 F g) (fapp1 F f)`
*   Defining `NatTransTerm(F, G)` type (Natural Transformations).
*   Defining `MkNatTrans_` term constructor with components (`tapp`).
*   Implementing computational rule for `tapp(MkNatTrans_(...))`.
*   Adding rewrite rules or type-checking conditions for the naturality condition.

### 7.2 Potential New Features and Enhancements

*   **Universe Polymorphism and Hierarchy:**
    *   Move beyond `Type : Type` to a system with `Type_i : Type_{i+1}` to ensure logical consistency and allow for constructions like the category of all small categories (`Cat_cat` from `emdash_specification_lambdapi.lp`). This is a major undertaking.
*   **Extensionality:**
    *   **Function Extensionality:** Consider adding rules or axioms for `(λx. f x) === f`.
    *   **Propositional Equality (`=`):** Introduce a primitive type for propositional equality `Eq {A} (a:A) (b:A)` with `refl` and potentially `J` (or `eqind` as in `example_unification.hs` and `emdash_specification_lambdapi.lp`). This is crucial for stating and proving properties *within* the type theory.
    *   **Hom-set Extensionality for `Set`:** As seen in `emdash_specification_lambdapi.lp`, if a category `Set` (of types/sets) is introduced where `HomSet X Y` is `X -> Y`, then extensionality rules for this specific Hom-set (e.g., two functions are equal if they are pointwise equal) would be needed.
*   **Quotient Types / Setoids:** For dealing with equality more abstractly, especially when defining categories where objects or morphisms are subject to equivalences.
*   **Inductive Types:** General support for user-defined inductive types (like natural numbers, lists, etc.) with constructors and eliminators. This would make the base type theory more expressive.
*   **More Sophisticated Unification:**
    *   **Higher-Order Pattern Unification:** Implement a more complete Miller-style pattern unification algorithm for metavariables, as discussed in `example_unification.hs`. This could make hole inference more powerful.
    *   **Typed Unification:** Incorporate type information into the unification process for metavariables, which can prune search space and improve inference.
*   **Tactic System:** For more complex constructions or proofs (if equality proofs are added), a simple tactic language could be beneficial.
*   **Improved Error Reporting:**
    *   More precise source location tracking for errors originating from sub-terms or generated constraints.
    *   Suggestions for fixes ("did you mean...?").
    *   Better visualization of unification failures or non-terminating rewrite loops.
*   **Performance Optimizations:**
    *   **Term Representation:** Explore more compact or efficient term representations (e.g., using integers for global definition IDs instead of strings in `Var`s).
    *   **Context Lookup:** Optimize context lookups if they become a bottleneck.
    *   **Caching for `whnf`/`normalize`:** For pure terms, results of normalization could be cached.
    *   **More Efficient HOAS:** While JavaScript functions are convenient, direct De Bruijn index manipulation can sometimes be more performant for core operations if JIT optimizations are not sufficient.
*   **User Interface / Interactivity:**
    *   A simple REPL or a more integrated development environment (e.g., web-based using Monaco editor) could greatly improve usability.
*   **Formalization of Category Theory Concepts from `emdash_specification_lambdapi.lp`:**
    *   `Set` category.
    *   Yoneda Lemma and embedding (`hom_cov`).
    *   Category of Functors (`Functor A B` as a category itself).
    *   Adjunctions, Limits, Colimits.

### 7.3 Suggestions for New Test Cases

As new features are added, comprehensive test cases are crucial.

*   **Functors:**
    *   Identity functor.
    *   Constant functor.
    *   Composition of functors: `H ∘ (G ∘ F) === (H ∘ G) ∘ F`.
    *   Functor laws applied to `MkFunctor_` instances.
    *   Type checking of terms involving `fapp0` and `fapp1` where arguments are holes.
*   **Natural Transformations:**
    *   Identity natural transformation.
    *   Vertical composition of natural transformations.
    *   Horizontal composition of natural transformations (Whiskering).
    *   Naturality condition checks for various `MkNatTrans_` instances.
    *   Godement product (interchange law for vertical and horizontal composition).
*   **Interactions:**
    *   Test interaction of functor laws with `MkCat_` unfolding rules.
    *   Test composition of `IdentityMorph` with `fapp1` of a functor.
*   **Error Cases:**
    *   Terms that should fail type checking due to incorrect functor/natural transformation definitions.
    *   Cases that test the occurs check and other unification failure conditions in more complex settings.
*   **More Complex `MkCat_` Examples:**
    *   The discrete category on a type.
    *   The category with one object and a monoid of morphisms.
    *   Product category.
*   **User-Defined Rewrite/Unification Rules:**
    *   More complex rewrite rules involving new categorical constructs.
    *   Unification rules that might be needed for specific categorical arguments (e.g., related to universal properties).

### 7.4 Code Refinements

*   **Reduce Global State:** Explore ways to make the core machinery (fresh name generation, constraint collection, rule storage) more encapsulated, perhaps by passing a "system environment" object or using a Reader/State monad pattern if a more functional style is desired (though this is a larger refactor for TypeScript).
*   **Immutable Data Structures:** While `Term` is defined immutably, operations like `ensureImplicitsAsHoles` and updates to `Hole.ref` involve mutation. Consider strategies for more pervasive immutability if performance allows and reasoning benefits are significant (e.g., using lenses or functional update patterns).
*   **Strict Type Guards and Exhaustiveness Checks:** Ensure all discriminated unions are handled exhaustively in `switch` statements (e.g., using a `default` case that throws an error or a helper function for exhaustiveness).
*   **Configuration for Limits:** Make `MAX_STACK_DEPTH` and iteration limits configurable rather than hardcoded constants.

By systematically addressing these areas, Emdash can evolve into a more robust, expressive, and user-friendly system for computational synthetic category theory.


Okay, we're nearing the end of the report. Here is **Section 8: Plan Forward and Conclusion**. Please append this to your `README.md` file.

```markdown
## 8. Plan Forward and Conclusion

### 8.1 Plan for Phase 2: Functors and Natural Transformations

With the core categorical constructs of Phase 1 implemented and analyzed, the project is ready to move towards Phase 2: implementing Functors and Natural Transformations. This phase will be guided by the `emdash_specification_lambdapi.lp` file.

The general strategy will involve:
1.  **Extending the `Term` type:** Introduce new constructors for `FunctorCatTerm`, `MkFunctor_`, `FMap0` (object mapping), `FMap1` (morphism mapping), `NatTransTerm`, and `MkNatTrans_`.
2.  **Updating `infer` and `check`:** Implement the typing rules for these new constructors. This will involve:
    *   `FunctorCatTerm A B : Type` (where `A, B : Cat`).
    *   `MkFunctor_ f0 f1 : FunctorCatTerm A B` requires checking `f0 : Obj A -> Obj B` and `f1 : (X:Obj A) -> (Y:Obj A) -> Hom A X Y -> Hom B (f0 X) (f0 Y)`, plus functoriality laws (see 8.1.1).
    *   `FMap0 F X : Obj B` (where `F : FunctorCatTerm A B`, `X : Obj A`).
    *   `FMap1 F f : Hom B (FMap0 F (dom f)) (FMap0 F (cod f))` (where `f : Hom A X Y`).
    *   `NatTransTerm F G : Type` (where `F, G : FunctorCatTerm A B`).
    *   `MkNatTrans_ eta : NatTransTerm F G` requires checking `eta : (X:Obj A) -> Hom B (FMap0 F X) (FMap0 G X)`, plus naturality conditions (see 8.1.1).
3.  **Implementing `whnf` reductions:**
    *   `FMap0 (MkFunctor_ f0 f1) X` reduces to `f0 X`.
    *   `FMap1 (MkFunctor_ f0 f1) f` reduces to `f1 f` (appropriately applied).
    *   (Potentially) `TApp (MkNatTrans_ eta) X` reduces to `eta X`.
4.  **Adding rewrite rules:** Implement the specified rewrite rules for functoriality (`F(id) = id`, `F(g ∘ f) = F(g) ∘ F(f)`) and naturality. These might be initially implemented as system rewrite rules if user-defined rule matching becomes too complex. The Lambdapi spec uses `rule` for these, suggesting they are computational.
    *   `fapp1 F (identity_morph X) ↪ identity_morph (fapp0 F X)`
    *   `compose_morph (fapp1 F a) (fapp1 F a') ↪ fapp1 F (compose_morph a a')`
    *   Naturality square: `compose_morph (fapp1 G f) (tapp ϵ X) ↪ compose_morph (tapp ϵ Y) (fapp1 F f)` (adjusting for our `compose_morph` argument order and `tapp` definition).
5.  **Defining `Set` and Yoneda:**
    *   Introduce `Set` as a primitive category. Its objects are `Type`s, and `Hom Set X Y` is `X -> Y`.
    *   Implement `hom_cov : (A:Cat) -> (W:Obj A) -> FunctorCatTerm A Set`.
        *   `fapp0 (hom_cov W) Y` should be `Hom_Type W Y` (which is `Hom W Y` after τ-reduction in LP).
        *   `fapp1 (hom_cov W) a f` (where `a: Hom X Y`, `f: Hom W X`) should be `compose_morph a f`. This is the "kernel/value yoneda action".
6.  **Testing:** Develop comprehensive tests for functor and natural transformation definitions, applications, and laws.

#### 8.1.1. Handling Laws (Functoriality and Naturality)

The functoriality and naturality laws are crucial.
*   **Functoriality:**
    1.  `F(id_X) = id_{F(X)}`
    2.  `F(g ∘ f) = F(g) ∘ F(f)`
*   **Naturality:** For a natural transformation `η : F ⇒ G`, and a morphism `f : X → Y` in C, the following diagram must commute:
    ```mermaid
    graph TD
        FX[F(X)] ---| η_X |--- GX[G(X)]
        FX ---| F(f) |--- FY[F(Y)]
        GX ---| G(f) |--- GY[G(Y)]
        FY ---| η_Y |--- GY
    ```
    This translates to `η_Y ∘ F(f) = G(f) ∘ η_X`.

These laws can be enforced in several ways:
*   **As part of `MkFunctor_` / `MkNatTrans_` type checking:** The checking rule for these constructors could require proofs of these laws as additional arguments. This is the most type-safe approach but adds significant user overhead. The Lambdapi spec (`functoriality_TYPE`, `naturality_TYPE`) suggests this approach by defining types for these proofs.
*   **As system-level rewrite rules:** Assume the constructors are "correct" and enforce laws via directed rewrites during `whnf`/`normalize`. This is simpler for the user but relies on the confluency and termination of these rules. The `rule` declarations in Lambdapi for functoriality suggest this.
*   **Via unification rules:** If laws are expressed as equalities, unification rules could attempt to solve them.

Given the `rule` directives in the Lambdapi specification for functoriality (`fapp1 F id = id`, `fapp1 F (g . f) = fapp1 F g . fapp1 F f`), it's likely that these are intended as computational (rewrite) rules. Naturality is also expressed via a `rule` (though commented with `/\\*!\\*/`, perhaps indicating complexity or choice).

**Initial Plan:**
1.  Implement the core term constructors and their `infer`/`check` logic without proof arguments for laws.
2.  Implement the functoriality laws as system rewrite rules applied during `whnf`.
3.  For naturality, `mkTransf_` will take the components `tapp: (X: Obj A) -> Hom (fapp0 F X) (fapp0 G X)`. The naturality condition `(tapp Y) ∘ (fapp1 F f) = (fapp1 G f) ∘ (tapp X)` will initially be enforced by a rewrite rule during `whnf`.
    *   The Lambdapi rule `compose_morph (fapp1 G a) (tapp ϵ X) ↪ fapp1 (hom_cov _) (tapp ϵ X') (fapp1 F a)` (adjusting for `_∘>` which is `fapp1 (hom_cov _)` application) looks like it tries to achieve one direction of this. The `hom_cov _` seems to be a placeholder for the codomain category `B` of the functor.

This phased approach allows for incremental development and testing.

### 8.2. Test Cases for Phase 2

*   Define a simple category (e.g., a discrete category from `NatType`).
*   Define an endofunctor on this category (e.g., `F(X) = X`, `F(f) = f`).
*   Verify `MkFunctor_` type checking and law enforcement (if done via rewrites).
*   Define the identity natural transformation `id_F : F ⇒ F`.
*   Define another functor `G` and a natural transformation `η : F ⇒ G`.
*   Test `tapp`, composition of natural transformations.
*   Test Yoneda embedding: `hom_cov W` for some object `W`.
    *   Verify `fapp0 (hom_cov W) Y` gives `Hom W Y`.
    *   Verify `fapp1 (hom_cov W) a f` correctly composes `a ∘ f`.
*   Example from `super_yoneda_functor_1` and `_2` in the Lambdapi spec: composing functors and creating natural transformations between them.

### 8.3. Conclusion

Emdash, even in its current Phase 1 state, demonstrates a robust foundation for a dependently typed system tailored for synthetic category theory. The TypeScript implementation, while challenging due to the language's type system limitations for such advanced concepts, has successfully incorporated core features like bidirectional type checking, hole-based inference, unification, and user-defined rewrite rules. The detailed analysis revealed a sophisticated design with pragmatic solutions for common issues in type theory implementation.

The journey has highlighted the complexities of HOAS, implicit argument handling, and ensuring the confluence and termination of rewrite rules. The solutions adopted, such as deep elaboration for lambdas and careful management of hole resolution and unification, provide a solid base.

Moving to Phase 2, the focus will be on extending the system with functors and natural transformations, drawing heavily from the Lambdapi specification. This will further test the system's capacity for abstraction and computation in a categorical setting. The ultimate aim remains to create a practical tool for computational mathematics, and the progress so far is promising. The identified areas for improvement, such as performance optimization, enhanced error reporting, and a more formal treatment of confluence, will be ongoing concerns as the system evolves. Emdash is on a clear path to becoming a valuable environment for exploring and formalizing categorical concepts.
```
