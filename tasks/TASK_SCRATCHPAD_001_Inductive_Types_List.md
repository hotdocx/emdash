# TASK_SCRATCHPAD_001_Inductive_Types_List.md

## Task: Add tests for polymorphic List inductive type

### Implemented

-   **Location**: `tests/inductive_types.ts`
-   **Details**:
    1.  Added a new `describe` block for `"Polymorphic Lists (List A)"`.
    2.  **Declarations**:
        -   `List: Type -> Type`
        -   `nil: Π {A:Type}. List A`
        -   `cons: Π {A:Type}. A -> List A -> List A`
    3.  **Induction via Eliminator**:
        -   Defined `List_elim` and its associated rewrite rules for `nil` and `cons` cases.
        -   Implemented a `map` function over `List A` using the `List_elim` primitive.
        -   Added a test case to verify that `map s [1, 2]` correctly computes to `[2, 3]`, where `s` is the successor function for `Nat`.
    4.  **Induction via Rewrite Rules**:
        -   Defined an `append_rw` function for concatenating two lists.
        -   Added rewrite rules for the `nil` and `cons` cases of the first list argument.
        -   Added a test case to verify that `append [1] [2, 3]` correctly computes to `[1, 2, 3]`.
-   **Helper definitions**: Created several sample lists of `Nat` (`list12_nat`, `list23_nat`, `list123_nat`) to be used in the tests.

### What remains to be implemented for this Task

-   The current task is complete. The new tests cover the declaration of a polymorphic inductive type and functions defined over it using both eliminators and direct rewrite rules.

### Next Steps

The new tests are ready. You can now run the test suite to ensure everything is working as expected.

**Next suggested prompt:**
`Let's run the tests and see if there are any issues.` 