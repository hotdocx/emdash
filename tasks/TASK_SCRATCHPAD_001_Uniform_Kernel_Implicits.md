# Task: Uniform Kernel Implicit Handling

## Date: 2024-07-26

## 1. Summary of Implementation

The goal was to create a more uniform and extensible way to handle implicit arguments for kernel-defined term constructors (like `IdentityMorph`, `ComposeMorph`), moving away from manual case-by-case implicit hole creation.

**Key changes:**

*   **`src/core_kernel_metadata.ts`:**
    *   Introduced `KERNEL_IMPLICIT_SPECS`, an arrayraped metadata structure. Each entry defines a kernel term's `tag` (e.g., 'IdentityMorph') and an array of `fields` that represent its implicit arguments (e.g., `['cat_IMPLICIT']`).
    *   Used TypeScript's `Extract<BaseTerm, { tag: '...' }>` utility type to correctly and robustly refer to the specific discriminated union member types (e.g., `IdentityMorphType = Extract<BaseTerm, { tag: 'IdentityMorph' }>`) when defining the `KernelImplicitSpec` generic type. This resolved persistent linter issues related to type/value name clashes.

*   **`src/core_elaboration.ts`:**
    *   **`ensureKernelImplicitsPresent(term: Term): Term` function:**
        *   This new function replaces the old `ensureImplicitsAsHoles`.
        *   It iterates over `KERNEL_IMPLICIT_SPECS`. If `term.tag` matches a spec's tag, it checks each specified implicit field on the term.
        *   If an implicit field is `undefined`, a fresh `Hole` is created and assigned to that field. Hole names are generated with hints from the term tag, field name, and potentially parts of the term itself (e.g., an object name for `IdentityMorph`).
    *   **`infer(ctx, term, ...)` function:**
        *   Now calls `ensureKernelImplicitsPresent(originalTerm)` at the very beginning on the `originalTerm` *before* `getTermRef`.
        *   The specific case handlers for `IdentityMorph` and `ComposeMorph` were updated:
            *   Removed manual `Hole` creation for their implicits (this is now done by `ensureKernelImplicitsPresent`).
            *   They now directly `check` the (guaranteed to exist) implicit argument fields (e.g., `idTerm.cat_IMPLICIT!`).
            *   Ensured that the *elaborated* versions of these implicit arguments (after `check`) are used when constructing the final `IdentityMorph` or `ComposeMorph` terms using their respective constructors (e.g., `IdentityMorph(elaboratedObj, getTermRef(elaboratedCatImplicit))`).
            *   Type casts like `current as Term & IdentityMorph` were updated to use the `Extract`ed types (e.g., `current as Term & IdentityMorphType`) to satisfy the linter and ensure type safety.
    *   **`check(ctx, term, ...)` function:**
        *   Now also calls `ensureKernelImplicitsPresent(originalTerm)` at its beginning, similar to `infer`.
    *   Removed the old `ensureImplicitsAsHoles` function.

## 2. Files Modified/Created

*   **Created:** `src/core_kernel_metadata.ts`
*   **Modified:** `src/core_elaboration.ts`
*   **Modified:** `tasks/TASK_SCRATCHPAD_001_Uniform_Kernel_Implicits.md` (this file)

## 3. What remains to be implemented?

*   **Testing:** Thoroughly test the new uniform implicit handling with existing and new test cases, especially focusing on:
    *   `IdentityMorph` and `ComposeMorph` with some or all implicits provided by the user.
    *   `IdentityMorph` and `ComposeMorph` with no implicits provided (should be filled by holes and resolved).
    *   Cases where inference of these implicits should succeed or fail gracefully.
*   **New Kernel Terms:** As new kernel term constructors with implicit arguments are added to `core_types.ts` (e.g., for indexed categories, fibrations, etc.), their metadata should be added to `KERNEL_IMPLICIT_SPECS` in `src/core_kernel_metadata.ts`. The `ensureKernelImplicitsPresent` function should then handle them automatically without further changes to `infer` or `check` logic for this specific aspect.
*   **Refinement of Hole Naming (Optional):** The hole naming in `ensureKernelImplicitsPresent` provides some hints. This could be further refined if more detailed debug information in hole names is desired for more complex kernel terms.
*   **Review `cloneTerm`:** The user has `cloneTerm` commented out in `core_context_globals.ts`. It was used in `addRewriteRule` and `defineGlobal`. If deep cloning is necessary there for correctness (to avoid unintended mutations of terms passed into these setup functions), it should be reviewed and potentially re-enabled or a more robust cloning solution implemented. For the current task of implicit handling, this was not directly involved, but it's an observation from reviewing the codebase.

## 4. Next Steps

*   Proceed with thorough testing of the changes.
*   If tests pass, this task can be considered complete and archived. The system is now better prepared for adding more complex kernel terms with implicit arguments.

Suggest next user prompt:
"Let's create some test cases in `emdash_v2_tests.ts` to specifically verify the new uniform kernel implicit handling for `IdentityMorph` and `ComposeMorph`. We should cover scenarios where implicits are fully provided, partially provided (if that's a state we want to support, though typically they'd become holes), and not provided at all." 