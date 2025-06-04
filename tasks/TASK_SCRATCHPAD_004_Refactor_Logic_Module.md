# Task Scratchpad: Refactor Logic Module

**Date:** 2024-07-28
**Version:** 1.0
**Status:** In Progress

## 1. Introduction

This document tracks the progress of refactoring the `src/logic.ts` file into multiple smaller, more focused modules within a new `src/logic/` directory. This aims to improve code organization, maintainability, and readability.

## 2. Proposed File Structure

The `src/logic.ts` module is being split as follows:

-   `src/logic/structural.ts`: Contains `areStructurallyEqualNoWhnf`.
-   `src/logic/equality.ts`: Contains `areEqual` and `areAllArgsEqual` (renamed to `areAllArgsConvertible`).
-   `src/logic/reduction.ts`: Contains `MAX_WHNF_ITERATIONS`, `whnf`, and `normalize`.
-   `src/logic/pattern.ts`: Contains `isPatternVarName`, `matchPattern`, `applySubst`, and `collectPatternVars`.
-   `src/logic/unification.ts`: Contains the remaining functions from `logic.ts` related to unification, constraint solving, `termContainsHole`, `tryUnificationRules`, `applyAndAddRuleConstraints`, `solveConstraints`, etc.
-   `src/logic/constants.ts`: Created to hold shared constants like `MAX_STACK_DEPTH` to avoid circular dependencies.

## 3. Implementation Status

### 3.1. Completed Steps:

1.  **Created `src/logic/structural.ts`**:
    *   Moved `areStructurallyEqualNoWhnf` into this file.
    *   Corrected import paths from `../../types` and `../../state` to `../types` and `../state`.
    *   Moved `MAX_STACK_DEPTH` to `src/logic/constants.ts` and updated import.
2.  **Created `src/logic/equality.ts`**:
    *   Moved `areEqual` and `areAllArgsEqual` (renamed to `areAllArgsConvertible`) into this file.
    *   Updated imports, including a forward reference to `./reduction` for `whnf`.
3.  **Created `src/logic/reduction.ts`**:
    *   Moved `MAX_WHNF_ITERATIONS`, `whnf`, and `normalize` into this file.
    *   Updated imports, including forward references to `./pattern` and `./structural`.
4.  **Created `src/logic/pattern.ts`**:
    *   Moved `isPatternVarName`, `matchPattern`, `applySubst`, and `collectPatternVars` into this file.
    *   Corrected `MAX_STACK_DEPTH` import to point to `./constants`.
5.  **Created `src/logic/unification.ts`**:
    *   Moved the remaining unification and constraint solving functions (`termContainsHole`, `unifyHole`, `unifyArgs`, `unify`, `applyAndAddRuleConstraints`, `tryUnificationRules`, `solveConstraints`) into this file.
    *   Updated internal imports.
6.  **Created `src/logic/constants.ts`**:
    *   Moved `MAX_STACK_DEPTH` into this file.
7.  **Updated Import Paths in Dependent Files**:
    *   `src/elaboration.ts`: Imports from `logic.ts` were updated to point to the new files in `src/logic/`.
        -   `whnf`, `normalize` from `./logic/reduction`
        -   `areEqual` from `./logic/equality`
        -   `solveConstraints` from `./logic/unification`
        -   `MAX_STACK_DEPTH` from `./logic/constants`
        -   `matchPattern`, `applySubst`, `isPatternVarName` from `./logic/pattern`
    *   `src/globals.ts`: Imports from `logic.ts` were updated.
        -   `whnf` from `./logic/reduction`
        -   `solveConstraints` from `./logic/unification`
        -   `areEqual` from `./logic/equality`
    *   `src/state.ts`: No imports from `logic.ts`, so no changes were needed.
    *   `src/stdlib.ts`: No imports from `logic.ts`, so no changes were needed.
8.  **Deleted Original `src/logic.ts`**: The original file was removed as its contents are now in the `src/logic/` subdirectory.

### 3.2. Remaining Steps:

*   All planned file movements and import path corrections have been completed.
*   The next step is to ensure the project builds and all tests pass after these significant refactoring changes.

## 4. Next Steps & Conclusion

The refactoring of the `logic.ts` module into the `src/logic/` directory is structurally complete.

**Next User Prompt Suggestion:** "Please run the build process and execute the test suite to ensure the refactoring was successful and didn't introduce any regressions."

We are ready to archive this task file if the build and tests pass. 