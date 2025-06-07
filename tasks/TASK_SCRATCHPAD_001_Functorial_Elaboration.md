# Functorial Elaboration (`MkFunctorTerm`) - Progress Report

This document tracks the implementation of the "Functorial Elaboration" feature, focusing on the `MkFunctorTerm` kernel primitive.

## Task Summary

The goal was to enhance the emdash kernel to support "functorial elaboration". This means creating a primitive term constructor for functors, `MkFunctorTerm`, which, during type checking (elaboration), would computationally verify that the provided object and arrow maps satisfy the functoriality law (i.e., that the arrow map preserves composition).

This verification is performed by constructing the two sides of the functoriality equation (`F(g ∘ f)` and `F(g) ∘ F(f)`) with abstract inputs and checking if they are definitionally equal via normalization, leveraging the existing `areEqual` function.

## Implementation Details

### Phase 1: Core Data Structures & Utilities

-   **`src/types.ts`**:
    -   A new term variant `MkFunctorTerm` was added to the `BaseTerm` union type. It stores the domain category, codomain category, object map (`fmap0`), and arrow map (`fmap1`).
    -   A corresponding factory function `MkFunctorTerm(...)` was created.

-   **`src/equality.ts`**:
    -   The `areEqual` function was updated to handle `MkFunctorTerm`. It performs a structural comparison, checking if the respective fields of two `MkFunctorTerm`s are equal.

-   **`src/pattern.ts`**:
    -   All relevant pattern-matching and term-manipulation utilities (`matchPattern`, `applySubst`, `collectPatternVars`, `replaceFreeVar`, `getFreeVariables`) were updated to correctly traverse and handle the new `MkFunctorTerm`.

### Phase 2: Elaboration Logic

-   **`src/elaboration.ts`**:
    -   This was the core of the implementation.
    -   A new `CoherenceError` class was introduced to provide detailed error messages when a law (like functoriality) fails to hold. It reports the LHS, RHS, and their normal forms.
    -   A new case was added to the main `infer` function's switch statement for `MkFunctorTerm`.
    -   This case delegates to a new helper function, `infer_mkFunctor`.
    -   **`infer_mkFunctor` Logic**:
        1.  It first elaborates the domain and codomain categories to ensure they are valid `CatTerm`s.
        2.  It then elaborates `fmap0` and `fmap1` against their expected types (e.g., `fmap0` must have type `Obj A -> Obj B`).
        3.  It programmatically constructs the functoriality law to be checked:
            `compose_B (fmap1 g) (fmap1 f) =?= fmap1 (compose_A g f)`
            This is done in a fresh local context with abstract variables for the objects (`X`, `Y`, `Z`) and morphisms (`f`, `g`). The user-facing `compose_morph` global is used for composition.
        4.  It normalizes both the left-hand side (LHS) and right-hand side (RHS) of the equation.
        5.  It uses `areEqual` to check if the normalized terms are convertible.
        6.  If they are not equal, it throws the `CoherenceError`.
        7.  If they are equal, it returns the fully elaborated `MkFunctorTerm` and its inferred type, which is `FunctorTypeTerm A B`.

### Phase 3: Standard Library and Testing

-   **`src/stdlib.ts`**:
    -   After some trouble with the file being corrupted by previous edits, the file was restored to a clean state.
    -   A new user-facing global constant, `mkFunctor_`, was defined.
    -   `mkFunctor_` is a curried function that takes the object and arrow maps and wraps them in the kernel `MkFunctorTerm`. Its type uses implicit Pi binders (`{A:Cat} {B:Cat}`), so the domain and codomain categories can be inferred by the elaborator from the types of the maps. This provides a convenient, high-level way for users to create functors while benefiting from the underlying kernel verification.

-   **`tests/dependent_types_tests.ts`**:
    -   A new test suite, "Functorial Elaboration", was added to verify the feature.
    -   **Success Case**: A test was created that defines a valid (constant) functor from a discrete category to `Set`. It asserts that calling `elaborate` on `mkFunctor_` with the correct maps succeeds and produces a term of the expected `Functor` type.
    -   **Failure Case**: A second test was added to ensure the coherence check works correctly. It defines a category `C3` with a composition law and an "arrow map" that provably violates this law (by always returning the successor function `s`, for which `s ∘ s ≠ s`). It asserts that `elaborate` correctly throws a `CoherenceError` when given this invalid functor definition.

## Remaining Tasks & Next Steps

The core implementation for `MkFunctorTerm` is complete and tested. The same pattern can now be applied to the other categorical constructors.

-   **Implement `MkCatTerm`**:
    -   This would involve adding a `MkCatTerm` to `types.ts` and updating all the necessary functions (`areEqual`, `pattern.ts` utilities).
    -   The elaboration logic in `infer_mkCat` would computationally verify the category laws (identity and associativity for `compose_morph`). This will be very similar to the `infer_mkFunctor` implementation.

-   **Implement `MkTransfTerm`**:
    -   Similarly, this would add a `MkTransfTerm` and update all related functions.
    -   The elaboration logic `infer_mkTransf` would verify the naturality condition for the transformation.

Once these are complete, the core "computational category theory" features of the kernel will be fully realized. We are ready to archive this task file and move on to the next main task, which would be implementing `MkCatTerm`.

**Suggestion for next prompt:** "Now, let's implement `MkCatTerm` following the same design pattern we used for `MkFunctorTerm`. This will involve adding the term to the kernel and implementing the elaboration logic to verify the category laws (identity and associativity) by computation." 