## TASK: Add tests for inductive types

### Implemented

- A new test file was created at `tests/inductive_types.ts` to house tests for user-defined inductive types.
- **Natural Numbers (`Nat`):**
    - Defined `Nat` as a type with constructors `z` (zero) and `s` (successor).
    - Implemented the induction principle for `Nat` (`Nat_elim`) as a global constant.
    - Added the necessary rewrite rules to give `Nat_elim` its computational behavior:
        - `Nat_elim P pz ps z` reduces to `pz`.
        - `Nat_elim P pz ps (s n)` reduces to `ps n (Nat_elim P pz ps n)`.
    - Showcased two methods for defining functions:
        1.  **Via Eliminator:** The `add_elim` function was defined formally using `Nat_elim`.
        2.  **Via Rewrite Rules:** The `add_rw` function was defined using simple pattern matching rules on `z` and `s n`.
    - Added tests to verify that both `add` implementations compute correctly (e.g., `1 + 2 = 3`).
- **Booleans (`Bool`):**
    - Defined `Bool` as a type with constructors `true` and `false`.
    - Implemented the elimination principle for `Bool` (`Bool_elim`) and its corresponding rewrite rules.
    - Defined a `not` function using both the eliminator and direct rewrite rules, with tests to verify its correctness.

This demonstrates that the current system is expressive enough to handle the definition and use of common inductive types through global definitions and rewrite rules.

### What remains to be implemented

- The current test setup is sufficient for this task.
- For future work, we could add tests for more complex inductive types like `List` or trees.
- The core logic for `Vec` (length-indexed vectors) already exists in `dependent_types_tests.ts`, which is a more advanced form of inductive type (an inductive family).
- A major enhancement would be to implement a more user-friendly mechanism for declaring inductive types (e.g., an `Inductive` command) that automatically generates the type, constructors, and eliminator principle, rather than requiring manual definition for each.

### Next Prompt Suggestion

We are now ready to move on. A good next step would be to leverage the infrastructure in `src/proof.ts` to build an interactive proof assistant.

**Suggested prompt:** "Using the `findHoles`, `getHoleGoal`, `refine`, and `intro` functions from `src/proof.ts`, let's build a simple read-eval-print loop (REPL) that allows a user to interactively construct a proof for a term that contains holes. The REPL should support commands like `goal` (to show the current goal), `intro` (to introduce a variable), and `exact <term>` (to fill a hole with a term)." 