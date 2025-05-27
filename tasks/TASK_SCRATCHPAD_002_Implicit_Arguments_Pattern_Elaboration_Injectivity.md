# Task Scratchpad: Implicit Arguments, Pattern Elaboration, Kernel Implicits & Injectivity

**Date:** 2024-07-27
**Version:** 1.0
**Status:** Design Finalized, Implementation Detailed

## 1. Introduction

This document outlines the design, architecture, and implementation details for a major enhancement to the Emdash type system. The primary goals addressed are:

1.  **General Implicit Arguments:** Introduce a systematic way to handle implicit arguments for `Lam`, `App`, and `Pi` terms, moving beyond ad-hoc mechanisms.
2.  **Elaboration of Patterns:** Define a robust strategy for elaborating patterns used in rewrite rules, ensuring they correctly interact with terms that have implicit arguments.
3.  **Uniform Kernel Constructor Implicits:** Standardize the handling of implicit arguments for built-in kernel term constructors (like `IdentityMorph`, `ComposeMorph`).
4.  **Injectivity in Unification:** Refine the unification logic to respect an `isInjective` property for global symbols when decomposing applications.

These features are crucial for increasing the expressiveness and correctness of the Emdash system, particularly for defining and using rewrite rules in a setting with rich implicit argument behavior.

## 2. Core Type System Changes (`src/core_types.ts`)

### 2.1. `Icit` Enum (Implicitness Tag)

An enumeration `Icit` is introduced to mark arguments/binders as explicit or implicit:

```typescript
export enum Icit {
    Expl = 'Expl', // Explicit
    Impl = 'Impl', // Implicit
}
```

### 2.2. Updates to Core Term Structures

The `Lam`, `App`, and `Pi` term structures are augmented with an `icit` field:

*   **`LamTerm`**: `Lam(name: string, icit: Icit, body: (v: Term) => Term, paramType?: Term, _isAnnotated?: boolean)`
    *   `icit`: Specifies if the lambda abstraction itself is implicit (e.g., `λ{x:A}.t`).
    *   `paramType`: Remains optional for type inference.
*   **`AppTerm`**: `App(func: Term, arg: Term, icit: Icit)`
    *   `icit`: Specifies if this application is implicit (e.g., `f {arg}`) or explicit (e.g., `f arg`).
*   **`PiTerm`**: `Pi(name: string, icit: Icit, paramType: Term, bodyType: (v: Term) => Term)`
    *   `icit`: Specifies if the binder is implicit (e.g., `Π{x:A}.B`) or explicit (e.g., `Π(x:A).B`).

### 2.3. `GlobalDef` Enhancements

The `GlobalDef` structure is updated:

```typescript
export interface GlobalDef {
    name: string;
    type: Term;
    value?: Term;
    isConstantSymbol: boolean;
    isInjective?: boolean; // New: For unification behavior
    kernelImplicitSpec?: KernelImplicitSpec; // New: For kernel constructor implicits
}
```
*   `isInjective`: If `true`, and the global is a function-like symbol, `unify` may decompose `App(GlobalSym, argL) = App(GlobalSym, argR)` into `argL = argR`.
*   `kernelImplicitSpec`: Describes the number and initial state (e.g., hole) of implicit arguments for kernel constructors.

### 2.4. Uniform Kernel Constructor Implicits

To handle implicits for kernel constructors (e.g., `IdentityMorph`, `ComposeMorph`) uniformly:

```typescript
export interface KernelImplicitParam {
    name: string; // For debugging/printing
    // We don't pre-assign types here; they are inferred.
}

export interface KernelImplicitSpec {
    implicitArity: number;
    paramNames: string[]; // Names for these implicit params, e.g., ["cat", "objX", "objY", "objZ"]
}

export const KERNEL_IMPLICITS_METADATA: Record<string, KernelImplicitSpec> = {
    IdentityMorph: { implicitArity: 1, paramNames: ["cat_IMPLICIT"] },
    ComposeMorph:  { implicitArity: 4, paramNames: ["cat_IMPLICIT", "objX_IMPLICIT", "objY_IMPLICIT", "objZ_IMPLICIT"] },
    // Add other kernel constructors here
};
```

Term constructors like `IdentityMorph` and `ComposeMorph` will store their implicit arguments in a dedicated array field, e.g., `implicitArgs: Term[]`. The `ensureKernelImplicitsPresent` function will use `KERNEL_IMPLICITS_METADATA` to initialize these arrays with holes if they are not fully provided.

## 3. Context and Globals (`src/core_context_globals.ts`)

### 3.1. `defineGlobal`

The `defineGlobal` function is updated to accept and store the `isInjective` flag and the `kernelImplicitSpec`.

```typescript
export function defineGlobal(
    name: string,
    type: Term,
    value?: Term,
    isConstantSymbol: boolean = false,
    isInjective: boolean = false, // New
    kernelImplicitSpec?: KernelImplicitSpec // New
): void {
    // ... existing logic ...
    globalDefs.set(name, { name, type, value, isConstantSymbol, isInjective, kernelImplicitSpec });
}
```

## 4. Elaboration (`src/core_elaboration.ts`)

The bidirectional type checking algorithms (`infer`/`check`) are central to handling implicit arguments. Normalization (`whnf`, `normalize`) will operate on these elaborated terms.

### 4.1. `infer` and `check` Modifications

*   **Handling `App` (Application):**
    *   **Inference (`infer(App(f, arg, Icit.Expl))`):**
        1.  Infer type of `f` to be `Π(x:A).B` (or `Π{x:A}.B` which is an error here if not all implicits filled).
        2.  Check `arg` against `A`.
        3.  Return `B[arg/x]`.
    *   **Inference (`infer(App(f, arg, Icit.Impl))`):** Similar, but expects `Π{x:A}.B`.
    *   **Checking (`check(App(f, arg, Icit.Expl), expectedType)`):**
        1.  Infer type of `f` to `Π(x:A).B`.
        2.  Check `arg` against `A`.
        3.  Constrain `B[arg/x]` with `expectedType`.
    *   **Implicit Argument Insertion (during `infer`/`check` of an application `f arg1 ... argN`):**
        When `infer` encounters `App(f, arg, Icit.Expl)`, and `type(f)` (after `whnf`) is `Pi(x, Icit.Impl, paramType, bodyType)`:
        1.  A fresh hole `?h_impl` is created for the implicit argument.
        2.  The application is conceptually transformed: `f {?h_impl} arg`.
        3.  `?h_impl` is checked against `paramType`.
        4.  The process continues with the new function `f {?h_impl}` and remaining arguments.
        This is iteratively applied until an explicit `Pi` is found or no `Pi` is left.

*   **Handling `Lam` (Lambda Abstraction):**
    *   **Checking (`check(Lam(x, Icit.Expl, body, typeAnn?), Pi(y, Icit.Expl, A, B))`):**
        Standard rule: check `body` (with `x:A`) against `B[x/y]`.
    *   **Checking (`check(Lam(x, Icit.Impl, body, typeAnn?), Pi(y, Icit.Impl, A, B))`):** Similar for implicit lambdas.
    *   **Implicit Lambda Insertion (Eta-expansion for Implicits):**
        When `check(term, Pi(x, Icit.Impl, A, B))` and `term` is not an implicit lambda:
        1.  Conceptually transform `term` into `λ{x':A}. (term {x'})` if `term` is a function expecting explicit args, or `λ{x':A}. term` if `term` is not a function.
        2.  This new implicit lambda is then checked against `Pi(x, Icit.Impl, A, B)`.
        3.  The inner `term {x'}` or `term` is then checked against `B[x'/x]`.
        (This is inspired by how Agda/Idris insert implicit lambdas).

*   **Handling `Pi` (Dependent Function Type):**
    *   Formation rules remain standard, but `icit` is now part of the structure:
        `check(Pi(x, icit, A, B), Type)` requires `check(A, Type)` and `check(B[fresh/x], Type)`.

### 4.2. Uniform Kernel Implicit Handling

*   A new function `ensureKernelImplicitsPresent(term: TermWithImplicits)` will be called at the start of `infer`/`check` for terms that might have kernel implicits (e.g. `IdentityMorph`, `ComposeMorph`).
*   This function uses `KERNEL_IMPLICITS_METADATA` for the term's tag.
*   It checks if `term.implicitArgs` array exists and has the correct `implicitArity`.
*   If not, or if elements are `undefined`, it fills/replaces them with fresh `Hole`s.
*   The existing `infer`/`check` logic for `IdentityMorph` and `ComposeMorph` will then generate constraints for these holes as before.

### 4.3. Elaboration of Patterns (`elaboratePattern`)

The strategy for elaborating patterns is to **reuse the existing `infer` (or `check`) mechanism**.

```typescript
export function elaboratePattern(
    patternInput: Term,
    ctx: Context,
    patternVarDecls: PatternVarDecl[], // Declares types for $x, $y, etc.
    expectedType?: Term // Optional: if the context of the rule implies an expected type for LHS
): Term {
    const patternInfCtx = patternVarDecls.reduce(
        (accCtx, decl) => extendCtx(accCtx, decl.name, decl.type), // Add $x: typeOfX to context
        ctx
    );

    // We need a way to tell `infer` (or `elaborate`) not to normalize the result term,
    // as patterns should remain structural.
    // `elaborate` will be modified to take a `normalizeResult: boolean` flag.
    const result = elaborate(patternInput, expectedType, patternInfCtx, /* normalizeResult = */ false);
    return result.term; // Return the (structurally) elaborated pattern
}
```

*   **No Separate `elaboratePattern` Algorithm:** We avoid a complex, bespoke recursive algorithm for patterns.
*   **Context for Pattern Variables:** Pattern variables (`$x`, `$y`) are declared with their types and added to the context used for `infer`/`check`.
*   **Hole for `expectedType`:** If the LHS pattern's type isn't known/enforced, `expectedType` can be a fresh hole or `undefined` (triggering `infer`).
*   **Non-Normalizing Elaboration:** `elaborate` will gain a flag to return the term after type checking and hole filling but *before* normalization. This is crucial because patterns must retain their specific structure (e.g., `add $x 0` should not become `$x`).
*   **Pattern Variables (`Var('$x')`):** During `infer`/`check` of the pattern, these are treated like regular variables whose types are looked up in `patternInfCtx`. They are not holes to be solved by this elaboration step.
*   **Implicit Insertion:** `infer`/`check` will automatically insert implicit `App`s and `Lam`s into the pattern structure as needed, based on the types of symbols and pattern variables encountered. For example, if `eq` has type `Π{T:Type}. T -> T -> Bool`, a pattern `eq $a $b` will be elaborated by `infer` into `eq {?h_T} $a $b`. `?h_T` will be a hole within the elaborated pattern.

### 4.4. `printTerm`

`printTerm` will be updated to reflect the `icit` status of `App`, `Lam`, and `Pi` terms, e.g., printing `{arg}` for implicit applications or `λ{x:A}.t` for implicit lambdas.

## 5. Logic (`src/core_logic.ts`)

### 5.1. `unify` Modifications

The primary change is how `unify` handles applications, respecting the `isInjective` flag.

*   **`App` vs. `App` Case:**
    When unifying `t1 = App(f1, arg1, icit1)` and `t2 = App(f2, arg2, icit2)`:
    1.  Reduce `f1` and `f2` to `whnf`. Let them be `rf1` and `rf2`.
    2.  If `rf1` is `Var(name1)` and `rf2` is `Var(name2)` and `name1 === name2`:
        *   Look up `GlobalDef` for `name1`.
        *   If `globalDef.isInjective` is `true`:
            *   Recursively unify `f1` with `f2` (covers cases where they might be syntactically different but reduce to the same injective var).
            *   Recursively unify `arg1` with `arg2`.
            *   Unify `icit1` with `icit2` (they must match).
            *   If all succeed, `Progress`.
        *   Else (not injective): The terms `t1` and `t2` are only equal if they are fully structurally equal after reduction or if a unification rule applies. Do not decompose.
    3.  Else (heads are different, or not both Vars, or Vars but not injective):
        *   Proceed with existing logic: if `areEqual(t1, t2, ctx)` then `Solved`.
        *   Else, try unification rules or fail. The equation `App(...) = App(...)` does not automatically decompose if the common head is not an injective variable. For example, if `f1` and `f2` reduce to the same `Lam` expression, `unify` will try to compare them structurally.

### 5.2. `matchPattern`

*   **Operates on Elaborated Patterns:** `matchPattern` will receive an *already elaborated* LHS pattern (from `elaboratePattern`).
*   **`Icit` Matching:**
    *   When matching `App(pat_f, pat_arg, pat_icit)` against `App(term_f, term_arg, term_icit)`, it will require `pat_icit === term_icit`.
    *   Similarly for `Lam` and `Pi` icit tags.
*   **Holes in Elaborated Patterns:** An elaborated pattern like `eq {?h_T} $a $b` will match `eq {Nat} t1 t2` if `$a` matches `t1`, `$b` matches `t2`, and `?h_T` (a pattern hole) matches `Nat`. These pattern holes are distinct from pattern variables like `$a`. Pattern holes behave like wildcards that must match the corresponding part of the term but don't bind to the substitution for the RHS. (Alternatively, and perhaps more simply, if pattern holes are filled by `infer` with concrete types from the pattern context, then they just become part of the structure to match). The primary pattern variables are `$a`, `$b`.

## 6. Soundness and Design Considerations

*   **Elaborating Patterns is Key:** This approach ensures that the structure of patterns (including their implicit arguments) aligns with the structure of elaborated terms they are matched against. This avoids mismatches due to implicit arguments being present in terms but not patterns (or vice-versa).
*   **Reusing `infer`/`check` for Patterns:** This is a significant simplification and promotes consistency. The core typing logic is trusted to correctly insert implicits based on type information.
*   **Pattern Variables vs. Holes in Patterns:**
    *   Pattern variables (`$x`) are declared and their types are known to `infer`/`check`.
    *   Holes (`?h`) *within* a pattern can arise if, for example, an implicit argument in the pattern cannot be determined from the pattern's structure alone (e.g., `eq $_ $x $y` elaborates to `eq {?T} $x $y` where `?T` is a hole in the pattern). During matching, this `?T` would need to unify with the corresponding part of the term being matched.
*   **Inspiration from `example_implicits.hs`:** The general strategy of using type inference to drive implicit argument insertion is adapted. Our HOAS with names and mutable term references presents different implementation details compared to the Haskell example's pure, de Bruijn approach.
*   **Non-Normalizing Elaboration for Patterns:** Essential to preserve the syntactic structure intended by the user for matching.

## 7. Implementation Status & Next Steps

*   **Design:** The design detailed above is considered final for this phase.
*   **Implementation:** 
    *   The core type system changes (`Icit` enum, `Lam`, `App`, `Pi` updates, `GlobalDef` enhancements for `isInjective`) have been implemented.
    *   The context and globals (`defineGlobal`) have been updated.
    *   Elaboration logic (`infer`, `check`) has been significantly updated to handle implicit argument insertion for `App` and `Lam`, and `icit` matching.
    *   Kernel implicit handling for `IdentityMorph` and `ComposeMorph` (via `ensureImplicitsAsHoles`) has been integrated into `infer`/`check`.
    *   The `unify` logic in `core_logic.ts` has been updated to handle injective symbols (`isInjective` flag on global definitions) for `App` vs `App` cases.
    *   `printTerm` has been updated for `Icit`.
    *   Elaboration of patterns via reusing `infer`/`check` (with a non-normalizing option in `elaborate`) is implemented. `matchPattern` now expects elaborated patterns and matches `icit` tags.
*   **Testing:** 
    *   Basic tests for `Icit` tagging, implicit application/lambda insertion exist in `runImplicitArgumentTests`.
    *   **A new suite `runMoreImplicitArgumentTests` has been added to `emdash_v2_tests.ts` to translate and test more examples from `example_implicits.hs`, covering `id`, `const`, `the`, explicit implicit application, and implicit lambda insertion rules (`insert`, `noinsert`, `insert2`).**
    *   Further testing is needed for: 
        *   More complex pattern elaboration scenarios.
        *   `matchPattern` behavior with more diverse elaborated patterns and terms.
        *   More intricate unification cases involving `isInjective` symbols.
        *   Thorough tests for uniform kernel implicits, especially for `ComposeMorph` with many implicits.
*   **Next Steps:**
    1.  Continue adding targeted tests for the areas mentioned above.
    2.  Address any bugs or refinements identified during testing.
    3.  Once testing is satisfactory, consider this task complete for the core functionality.
*   **Archival:** This task is approaching completion for the core logic. Further refinement will likely occur as more complex user-level features are built upon this foundation.

This concludes the plan for the scratchpad. 