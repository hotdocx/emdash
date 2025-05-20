# Task Scratchpad: Review Base DTT Tests (emdash_v2_tests.ts)

## Date: 2024-07-15

## Implemented So Far:

1.  **Initial Review:**
    *   Analyzed the provided test results for `runBaseDTTTests` in `emdash_v2_tests.ts`.
    *   Focused on user-identified problematic tests: B2.3 and B7.1.

2.  **Test B2.3 (`(id Type Type)` evaluation):**
    *   **Validity:** Confirmed that Test B2.3 is a standard, valid test for higher-order polymorphic function application.
        *   `GlobalId = (λ A:Type. λ x:A. x)`
        *   `App(App(Var("GlobalId"), Type()), Type())` should correctly evaluate to the term `Type` with type `Type`.
    *   **Current Status:** The test is currently failing with the error: `Type error: Could not solve constraints. Approx failing: Type vs A (orig: Check general: Type vs A for term Type)`.
    *   **Conclusion:** This failure indicates a bug in the `emdash_v2.ts` type system implementation. No source code changes were made yet as per user instruction.

3.  **Test B7.1 (Normalization of complex beta-reduction):**
    *   **Validity of Original:** Confirmed user's finding that the original test was unsound. The term `App(App(Lam("F", (Π A:Type.A), F_var => F_var), Lam("G", Type(), G_var => G_var)), Type())` was ill-typed because `(Π G:Type. Type)` (type of `Lam("G",...)`) is not unifiable with `(Π A:Type. A)` (expected parameter type for `Lam("F",...)`). The system correctly reported this as a type error.
    *   **Correction:** The test was modified to use a well-typed complex beta-reduction:
        *   New term: `App( (λ F:(Π Z:Type.Z). (F Type)) , (λ Y:Type.Y) )`
        *   This term correctly beta-reduces to `Type`, and its type is `Type`.
        *   The `emdash_v2_tests.ts` file was updated with this corrected test logic.
    *   **Current Status:** The corrected test B7.1 has been applied to `emdash_v2_tests.ts`.

## What Remains to be Implemented (Current Task):

1.  **Verify B7.1 Correction:** Run the tests to confirm that the corrected B7.1 now passes as expected.
2.  **Address B2.3 Failure:**
    *   Investigate the root cause of the failure in Test B2.3 within `emdash_v2.ts`.
    *   Propose and implement a fix in `emdash_v2.ts` for the identified bug.
3.  **Review Other Tests (If Necessary):** Briefly review other tests in `runBaseDTTTests` if the B2.3 fix reveals related issues or if further instabilities are observed.

## Next User Prompt Suggestion:

"Let's run the tests again to see the results after the B7.1 correction. Then, we can focus on debugging the failure in Test B2.3 and fixing the `emdash_v2.ts` code."

## Archival Readiness:

This task file (`TASK_SCRATCHPAD_001_Review_BaseDTT_Tests.md`) is **not yet ready to be archived**. The primary goal of ensuring the base DTT tests are sound and passing (which involves fixing B2.3) is still pending. 