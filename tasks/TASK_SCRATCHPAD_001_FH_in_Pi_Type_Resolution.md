## Task: Test FH() in Pi Type Resolution

**Goal:** Ensure that a fresh hole `FH()` nested within a Pi type's parameter type declaration is correctly inferred and resolved during elaboration.

**Test Expression:** `Π A_type : Type. Π A_val : A_type. Π P : (Π ignored_P_arg : FH(). Type). P A_val`

**Expected Outcome:** 
- The `FH()` instance should resolve to `A_type` (which is `Var(A_type_param_name)` in the context of the `P` binder).
- The overall type of the expression should be `Type`.

### Implementation Steps:

1.  **Define the test term in `emdash_v2_tests.ts` within `runChurchEncodingTests`:**
    *   Use unique parameter names (e.g., `A_type_fh_test20`, `A_val_fh_test20`, `P_fh_test20`, `ignored_P_arg_fh_test20`).
    *   Create a specific instance of `FH()`: `const fh_hole_instance = FH();`.
    *   Construct the Pi type for `P`'s parameter: `const P_param_type_decl_fh = Pi(ignored_P_arg_name_fh, Icit.Expl, fh_hole_instance, _ => Type());`
    *   Construct the full test term using nested `Pi` and `App` constructors.

2.  **Elaborate the term:**
    *   `elabRes = elaborate(term_FH_test, undefined, baseCtx);`

3.  **Assertions:**
    *   Assert that `elabRes.type` is equal to `Type()`.
        ```typescript
        assert(areEqual(elabRes.type, Type(), baseCtx), "Church Test 20.1: Overall expression type is Type");
        ```
    *   Traverse the structure of `elabRes.term` to access the part corresponding to where `fh_hole_instance` was.
        *   `const elaborated_term_FH = getTermRef(elabRes.term);`
        *   Assert it's a Pi (for `A_type`).
        *   Access its body type, get the next Pi (for `A_val`).
        *   Assert `A_val`'s param type is `Var(A_type_param_name_fh)`.
        *   Access `A_val`'s body type, get the next Pi (for `P`).
        *   Access `P`'s param type (which is `P_param_type_decl_fh` elaborated).
        *   Assert this is a Pi (for `ignored_P_arg`).
        *   Access `ignored_P_arg`'s param type. This is where `fh_hole_instance` was.
        *   Assert this resolved type is equal to `Var(A_type_param_name_fh)`.
            ```typescript
            // ... traversal logic ...
            const Pi_ignored_elab = P_param_type_elab as Term & { tag: 'Pi' };
            const ignored_param_type_elab = getTermRef(Pi_ignored_elab.paramType);
            const expected_resolution = Var(Pi_Atype_elab.paramName); // Var(A_type_param_name_fh)
            assert(areEqual(ignored_param_type_elab, expected_resolution, baseCtx), "Church Test 20.X: fh_hole resolved correctly");
            ```
    *   Directly check the `ref` of the original `fh_hole_instance` object.
        ```typescript
        const resolved_fh_direct = getTermRef(fh_hole_instance);
        assert(areEqual(resolved_fh_direct, expected_resolution, baseCtx), "Church Test 20.Y: Direct check of fh_hole_instance.ref resolved correctly");
        ```
    *   Verify the structure of `P`'s body (the application `P A_val`).

### Analysis of Elaboration Logic:

The key interaction happens during the `check` of the application `P A_val`:

-   `infer(ctx, P)` yields type `Π ignored : fh_hole_instance. Type`.
-   `check(ctx, A_val, fh_hole_instance)` is called.
    -   Inside this `check`, `infer(ctx, A_val)` yields type `A_type` (i.e., `Var(A_type_param_name)`).
    -   A constraint `Var(A_type_param_name) === fh_hole_instance` is added.
-   The `solveConstraints` function processes this constraint, calling `unify(Var(A_type_param_name), fh_hole_instance)`.
-   `unifyHole(fh_hole_instance, Var(A_type_param_name))` then sets `fh_hole_instance.ref = Var(A_type_param_name)`.

This mechanism seems correct and should lead to the desired resolution of the hole.

### Status:

-   [x] Test case added to `emdash_v2_tests.ts`.
-   [x] Analysis of relevant elaboration logic performed.

**Next Steps:**
- Run the tests to confirm the new test case (Church Test 20) passes.
- If it passes, this task can be considered complete and archived.
- If it fails, debugging will be required based on the failure message and further analysis of the trace. Assuming it passes given the analysis.

**Conclusion (Anticipated):** The test should pass, confirming the robust handling of holes within nested Pi type parameter declarations. We are ready to archive this task file and move on to the next main Task.

## Update & Analysis (Post Test 21 Manual Fix & Test 18.1 Debug)

**User manually fixed Test 21.6 assertion:** The original assertion `areEqual(Q_body_elab21, Type(), ...)` was indeed unsound. The body `App(Q_term, five_val_global_ref)` should have type `Type`, but the term itself is an application, not `Type`. The corrected assertion likely checks `areEqual(elabRes21.type, Type(), baseCtx)` for the overall expression, and specific structural checks for the body, which now pass.

**Test 18.1 (`eqTest_val`) Failure Analysis:**

*   **Observation:** Test 18.1 still fails. The `gdef.value` for `eqTest_val` showed `((refl_func ?h13(:Type)) ?h14(:?h13(:Type)))`. This indicates that the holes `?h13` and `?h14` (from `FH()` in the *value* part of `eqTest_val`) are correctly having their `elaboratedType` properties set during inference.
*   **Issue in `defineGlobal`:** A crucial bug was identified: `elaboratedValue = getTermRef(valueToCheck)` should be `elaboratedValue = getTermRef(checkedValueResult)`. The `check` function returns the elaborated term, which might be structurally different (e.g., due to implicit lambda insertion) from the input `valueToCheck`. This has been corrected.
*   **Root Cause of 18.1 Failure (Hypothesis):** The core problem for Test 18.1 seems to be that the `type` stored in `globalDefs` for `eqTest_val` (which is `elabRes.type` in the test, derived from `elaboratedType` in `defineGlobal`) is being corrupted. Specifically, a subterm `Var("Nat_type")` within this stored type definition appears to be replaced by or aliased with `?h13` (a hole originating from the *value's* elaboration).
    *   The original type `Eq_type Nat_type hundred_val hundred_val` has no holes.
    *   The `elaboratedType` in `defineGlobal` is a clone of this original type and should remain pristine.
    *   However, the failure log `whnf(elabRes.type): (Π (P_Eq_param : (Π (ignored_P_arg : ?h13(:Type)). Type))` indicates that `elabRes.type` effectively became `Eq_type ?h13 hundred_val hundred_val`.
    *   This points to an unintended mutation of the `elaboratedType` (the `expectedType` argument to `check`) during the elaboration/checking of the *value* part of the global definition.

**Current State of `isTypeNameLike` fix:**
*   The `isTypeNameLike` flag was added to `GlobalDef` and `defineGlobal`.
*   `whnf` was updated to respect `isTypeNameLike` for `Var`s, preventing unfolding of these globals.
*   Definitions for `Nat_type`, `Bool_type`, `List_type`, `Eq_type` in tests were updated with `isTypeNameLike: true`.
*   This successfully fixed Test 21.4 and 21.5 where `fh_hole_instance_21` now correctly resolves to `Var("Nat_type")` instead of its unfolded definition.

**Next Steps:**
1.  Re-run all tests to see if the `checkedValueResult` fix in `defineGlobal` has fixed Test 18.1. It's possible that storing an incompletely elaborated value led to subsequent errors during `areEqual` that manifested as the type mismatch.
2.  If Test 18.1 still fails, a deep dive into how `expectedType` (which is `elaboratedType` in `defineGlobal`) could be mutated by `check(..., valueToCheck, elaboratedType, ...)` or its sub-calls (`addConstraint`, `solveConstraints`, `unify`) is required. This might involve careful logging or step-through debugging, looking for any aliasing or direct modification of non-hole terms within `elaboratedType`.

We are ready to archive this task file if re-running tests after the `checkedValueResult` fix shows that Test 18.1 passes. If not, further investigation is needed for Test 18.1.

**Conclusion (Anticipated):** The test should pass, confirming the robust handling of holes within nested Pi type parameter declarations. We are ready to archive this task file and move on to the next main Task.

## Progress Log

### Implemented (Fixes and Refinements)

1.  **`defineGlobal` uses `checkedValueResult`**: Modified `src/core_context_globals.ts` so that `elaboratedValue` in `defineGlobal` is now correctly assigned from `getTermRef(checkedValueResult)`. This ensures that the term stored for a global definition is the one that has been fully type-checked and potentially transformed by the `check` function (e.g., with inserted implicit lambdas).
2.  **Corrected Lam-Pi Rule in `check`**: Updated the `check` function in `src/core_elaboration.ts` (around lines 341-357) for the case where a `Lam` term is checked against a `Pi` type. The body of the returned `Lam` term is now a function that, when invoked with an argument `v_arg`, correctly sets up a new context where the lambda's parameter is bound to `v_arg`. It then re-checks the original lambda's body structure against the Pi's body type (instantiated with `v_arg`) within this new context. This ensures that the elaborated lambda body is correctly dependent on its argument.
3.  **Corrected Implicit Lambda Insertion in `check`**: Updated the `check` function in `src/core_elaboration.ts` (around lines 310-328) for the implicit lambda insertion case. Similar to the explicit `Lam`-`Pi` rule, the body of the newly inserted implicit `Lam` is now a function. This function, when invoked with an argument `v_actual_arg`, sets up a context where the lambda's parameter is bound to `v_actual_arg`. It then re-checks the original `currentTerm` (the term being wrapped by the implicit lambda) against the expected body type (derived from the `Pi` type and instantiated with `v_actual_arg`) within this new context. This ensures that the implicit lambda correctly processes its argument during evaluation.

### Remaining for Task Completion

1.  **Run all tests**: After these significant changes to `check` and `defineGlobal`, all tests (especially "Church Test 18.1" and the "Implicit Argument Tests" like IA1.1) need to be re-run to confirm that: 
    *   The original issues are resolved.
    *   No new regressions have been introduced.
2.  **Analyze `normalize` for `Var` case**: Investigate the `normalize` function in `src/core_logic.ts`, specifically the `'Var'` case, to ensure it correctly handles global definitions, potentially looking them up and unfolding them if appropriate (respecting flags like `isTypeNameLike`).
3.  **Final Review**: Conduct a final review of the changes and their impact on the overall type checking and elaboration logic.

### Next Steps

*   The user should run the full test suite.
*   Based on the test results, if Test 18.1 or other tests still fail, the next prompt should focus on debugging those specific failures, potentially starting with the `normalize` function or further refining the context handling in `check` and `infer` if the issue seems related to how terms are processed under binders or during substitution.

We are not ready to archive this task file. The core issue of Test 18.1 and related elaboration subtleties are still under investigation, although significant progress has been made in the `check` function. 