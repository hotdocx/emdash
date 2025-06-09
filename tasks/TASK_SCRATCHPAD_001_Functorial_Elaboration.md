# Functorial Elaboration (`MkFunctorTerm`) - Progress Report

This document tracks the implementation of the "Functorial Elaboration" feature, focusing on the `MkFunctorTerm` kernel primitive.

## Task Summary

The goal was to enhance the emdash kernel to support "functorial elaboration". This means creating a primitive term constructor for functors, `MkFunctorTerm`, which, during type checking (elaboration), would computationally verify that the provided object and arrow maps satisfy the functoriality law (i.e., that the arrow map preserves composition).

This verification is performed by constructing the two sides of the functoriality equation (`F(g ∘ f)` and `F(g) ∘ F(f)`) with abstract inputs and checking if they are definitionally equal via normalization, leveraging the existing `areEqual` function.

## Task: Explicit Functoriality Proofs

The `MkFunctorTerm` feature has been enhanced to allow users to provide an explicit proof of the functoriality law, rather than relying solely on the kernel's computational verification.

### What has already been implemented (and where, and how):

-   **`src/types.ts`**:
    -   The `MkFunctorTerm` type was modified to include a new optional field: `proof?: Term`.
    -   The corresponding factory function `MkFunctorTerm(...)` was updated to accept this optional proof.

-   **`src/equality.ts` & `src/pattern.ts`**:
    -   The `areEqual` function in `src/equality.ts` was updated to correctly compare `MkFunctorTerm` instances by also checking their `proof` fields.
    -   All relevant pattern-matching and term-manipulation utilities (`matchPattern`, `applySubst`, `collectPatternVars`, `replaceFreeVar`, `getFreeVariables`) in `src/pattern.ts` were updated to correctly traverse and handle the new `proof` field.

-   **`src/stdlib.ts`**:
    -   The indexed inductive type family for propositional equality (`Eq`), its constructor (`refl`), and its eliminator (`Eq_elim` with its rewrite rule `Eq_elim_refl`), were moved from a test file into the main standard library file. This makes them globally available for constructing and using proofs.
    -   The user-facing `mkFunctor_` global was redefined. Its new signature now requires an additional `functoriality` proof argument. The type of this argument is a proposition using the `Eq` type, asserting that the functor laws hold.

-   **`src/elaboration.ts`**:
    -   The `infer_mkFunctor` function was significantly refactored to handle the new `proof` field.
    -   **If a proof is provided**: The function now type-checks the provided proof term. The expected type for the proof is constructed programmatically as a dependent proposition asserting the functoriality law: `∀(X,Y,Z,a,a'), Eq (Hom_B (F X) (F Z)) (compose_B (fmap1 a) (fmap1 a')) (fmap1 (compose_A a a'))`. If the proof is valid, the computational check is skipped.
    -   **If no proof is provided**: The function falls back to the original behavior of computationally verifying the law by normalizing the two sides of the equation and checking for definitional equality.
    -   The final elaborated `MkFunctorTerm` now includes the elaborated proof if one was provided.

### What remains to be implemented to finish the current main Task:

- **Testing**: We need to create a new test file or update an existing one to verify the new explicit proof functionality. This should include:
    1.  A test case where a valid functor is created with a correct, explicit proof (`refl` of a computationally valid law).
    2.  A test case that asserts elaboration fails if an *incorrect* proof is provided for a valid functor.
    3.  A test case that asserts elaboration fails if a correct proof is provided for an *invalid* functor definition (where the law doesn't actually hold).

### Next user prompt suggestion:

"The implementation of the explicit functoriality proof mechanism looks complete. Now, let's create a new test file `tests/functor_proofs.ts` to thoroughly test this new functionality."

## Remaining Tasks & Next Steps

The core implementation for `MkFunctorTerm` is complete and tested. The same pattern can now be applied to the other categorical constructors.

-   **Implement `MkCatTerm`**:
    -   This would involve adding a `MkCatTerm` to `types.ts` and updating all the necessary functions (`areEqual`, `pattern.ts` utilities).
    -   The elaboration logic in `infer_mkCat` would computationally verify the category laws (identity and associativity for `compose_morph`). This will be very similar to the `infer_mkFunctor` implementation.

-   **Implement `MkTransfTerm`**:
    -   Similarly, this would add a `MkTransfTerm` and update all related functions.
    -   The elaboration logic `infer_mkTransf` would verify the naturality condition for the transformation.

Once these are complete, the core "computational category theory" features of the kernel will be fully realized. We are ready to archive this task file and move on to the next main Task, which would be implementing `MkCatTerm`.

**Suggestion for next prompt:** "Now, let's implement `MkCatTerm` following the same design pattern we used for `MkFunctorTerm`. This will involve adding the term to the kernel and implementing the elaboration logic to verify the category laws (identity and associativity) by computation." 