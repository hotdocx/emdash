# Task Scratchpad: Refactor Core Logic

## Goal
Refactor the existing `emdash_v2.ts` and `emdash_v2_tests.ts` files into smaller, more manageable modules within a `src/` directory at the project root.

## Plan

1.  **Verify `src/` directory exists at the project root.** (Completed)
2.  **Define the new file structure within `src/`.**
    *   `src/types.ts`: Core type definitions.
    *   `src/term_constructors.ts`: Term constructor functions.
    *   `src/globals_and_rules.ts`: Global variables, constants, and rule management functions.
    *   `src/reduction.ts`: `whnf` and `normalize` functions.
    *   `src/equality.ts`: `areEqual` and `areStructurallyEqualNoWhnf` functions.
    *   `src/unification.ts`: Unification logic.
    *   `src/type_checking.ts`: Type inference (`infer`) and checking (`check`).
    *   `src/elaboration.ts`: The main `elaborate` function.
    *   `src/pattern_matching.ts`: Pattern matching logic for rewrite rules.
    *   `src/pretty_print.ts`: The `printTerm` function.
    *   `src/utils.ts`: Utility functions like `consoleLog`, `resetMyLambdaPi`, context helpers.
    *   `src/index.ts`: Main entry pointbarrel file re-exporting necessary components.
3.  **Move code from `emdash_v2.ts` into the new files, managing exports and imports.**
4.  **Move `emdash_v2_tests.ts` to `src/tests.ts` and update its imports.**
5.  **Delete original `emdash_v2.ts` and `emdash_v2_tests.ts` from the project root.**

## Progress

### Phase 1: Create `src/types.ts`
- **Implemented:**
    - Created `src/types.ts`.
    - Moved `BaseTerm`, `Term`, `PatternVarDecl`, `Binding`, `Context`, `GlobalDef`, `RewriteRule`, `UnificationRule`, `Substitution`, `Constraint`, `UnifyResult`, `ElaborationResult` to `src/types.ts`.
    - Added exports for all types.
- **Remaining:**
    - Update other files to import these types from `src/types.ts`.

## Next Steps
Proceed with creating `src/term_constructors.ts` and moving relevant code. 