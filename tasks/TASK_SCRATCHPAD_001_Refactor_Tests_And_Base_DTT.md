## Task: Refactor Tests and Add Base DTT Tests

**Date:** 2024-07-26 (Updated 2024-07-27)

### Subtasks Completed:

1.  **Moved Existing Tests:**
    *   The original `runPhase1Tests` function and its helper assertion functions (`assertEqual`, `assertLogs`) were moved from `emdash_v2.ts` to a new file `emdash_v2_tests.ts`.
    *   Necessary imports from `emdash_v2.ts` were added to `emdash_v2_tests.ts`.

2.  **Modified `emdash_v2.ts`:**
    *   Removed `runPhase1Tests` and its helper functions.
    *   Added `export` keywords to all necessary functions, type definitions, and constants required by `emdash_v2_tests.ts`.

3.  **Generated New Base DTT Tests:**
    *   A new test suite function `runBaseDTTTests` was created in `emdash_v2_tests.ts`.
    *   This suite includes tests for: `Type : Type`, variable lookup, basic `Pi`/`Lam`/`App` constructs, beta reduction, unbound variable errors, basic hole inference, definitional equality (alpha-equivalence for `Lam`/`Pi`), normalization, and type mismatch errors.

4.  **Corrected HOAS Usage & Linter Errors:**
    *   All `Lam` and `Pi` constructor calls in `runBaseDTTTests` were updated to use proper Higher-Order Abstract Syntax (HOAS) for their function bodies/body types. This involved changing direct term embeddings (like `Var("A")` or `Type()`) into functions (e.g., `(A_var: Term) => A_var`).
    *   Explicit type annotations (`: Term`) were added to these HOAS functions for clarity and to satisfy the TypeScript compiler.
    *   The `runPhase1Tests` function in `emdash_v2_tests.ts` was replaced with a new version provided by the user.
    *   Linter errors related to template literals and variable access in the updated `emdash_v2_tests.ts` were resolved.

### Implemented (and Where/How):

*   **`emdash_v2_tests.ts`**: This file now contains all tests.
    *   `runPhase1Tests()`: Contains the user-provided verbatim test suite focusing on Emdash categorical constructs (`CatTerm`, `ObjTerm`, `HomTerm`, `MkCat_`, `IdentityMorph`, `ComposeMorph`), including their formation, inference with implicits, `MkCat_` unfolding, and basic rewrite rule application for identity laws.
    *   `runBaseDTTTests()`: Contains tests for the foundational dependent type theory (MyLambdaPi), ensuring core term constructors, type checking, inference, and reduction mechanisms work as expected. HOAS usage for `Lam` and `Pi` is now correct.
    *   Helper functions `assertEqual`, `assertLogs`, and `elabType` are present.
    *   Imports from `emdash_v2.ts` are correctly configured.
*   **`emdash_v2.ts`**: Exports necessary components and no longer contains test code.
*   **`tasks/TASK_SCRATCHPAD_001_Refactor_Tests_And_Base_DTT.md`**: This file is updated to reflect the current progress.

### Remaining to be Implemented (for this task):

*   None. All requested changes for moving tests, adding base DTT tests, and resolving linter errors related to HOAS have been addressed.

### Next Steps & Task Archival:

*   The system now has a separate test file with expanded test coverage.
*   The critical HOAS issues in the tests have been resolved.
*   This task can be considered complete and this scratchpad file can be archived.
*   **Suggested next user prompt:** "The tests seem to be in good order now. Let's proceed by appending the content from Section 8 of the `README.md` (Plan Forward and Conclusion) to the main `README.md` file." 