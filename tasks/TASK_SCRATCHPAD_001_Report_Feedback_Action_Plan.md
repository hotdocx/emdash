## Task Scratchpad: Action Plan for LLM Report Feedback (Emdash v2)

**Date:** 2023-10-27 (Placeholder)
**Associated User Query:** Review of `report_from_other_llm.md` and related comments.
**Goal:** Draft a detailed plan of action for each piece of feedback, without immediate implementation.

---

### 1. Uniform Implicit Argument Handling

*   **Summary:** Current implicit handling for `IdentityMorph` and `ComposeMorph` in `check` is ad-hoc. Aim for a uniform mechanism.
*   **Action Plan:**
    1.  **Declarative Implicits:** Define a way to mark arguments in `Term` constructors (or associated metadata) as implicit (e.g., `IdentityMorph`, `ComposeMorph`, future `FMap0`/`FMap1`).
    2.  **Generic Hole Insertion:** Refactor/replace `ensureImplicitsAsHoles`. New generic mechanism to iterate term arguments, check "implicitness" metadata, and insert fresh holes if an implicit argument is not user-provided.
    3.  **Uniform Constraint Generation:** Remove special `case`s in `infer`/`check` for specific constructors' implicits. Standard type inference/checking, guided by the constructor's full Pi-type signature (including implicits), should generate constraints that solve these holes.
    4.  **Review Signatures:** Ensure Pi-types for constructors with implicits are well-defined to guide this.
*   **Expected Outcome:** Cleaner `infer`/`check` functions, more extensible implicit handling.

---

### 2. Pattern Variable Hygiene

*   **Summary:** Pattern variables in rewrite rules (e.g., `X_obj_pv`) could clash with global names.
*   **Action Plan:**
    1.  **Short-Term (Convention):** Adopt and document a strict naming convention for pattern variables (e.g., `$` prefix like `$X_obj`, or suffix `_pv`). Apply immediately to all existing rules.
    2.  **Medium-Term (Enforcement/Improved Logic):**
        *   **Option A (Prefix Enforcement):** Modify `isPatternVarName` to only recognize names with the chosen convention (e.g., starting with `$`). Update rule definitions.
        *   **Option B (Disjointness Check):** Enhance `matchPattern` to ensure a pattern variable name is not also a global definition name (check against `globalDefs`).
*   **Expected Outcome:** Increased robustness of the rewrite rule matching system.

---

### 3. More Declarative Implicit Handling (Reiteration)

*   **Summary:** Reinforces point 1.
*   **Action Plan:** Covered by the plan in point 1.

---

### 4. `MkFunctor_` (and `MkCat_`) as Kernel Term vs. Library Definition

*   **Summary:** Discuss whether `MkFunctor_` (and `MkCat_`) should be primitive kernel terms or library definitions (global `Var`s).
*   **Action Plan (Recommendation: Kernel Terms):**
    *   **Maintain Kernel Status:** For foundational constructors like `MkCat_` and upcoming `MkFunctor_`, whose unfolding is critical and has a fixed structure, keeping them as kernel terms is preferable for Emdash.
    *   **Pros:** Performance (direct `whnf` rules), ease of giving special semantic status (constant symbol, injectivity), clarity of primitives, tailored type-checking.
    *   **Rationale:** Aligns with direct computational support for categorical constructs and is consistent with how `MkCat_` is handled. The LP spec defines `mkCat_` as a `constant symbol`.
*   **Expected Outcome:** Continued direct and efficient computational semantics for these core constructors.

---

### 5. Functor Law Implementation (Kernel Reduction vs. Rewrite Rules)

*   **Summary:** How to implement functor laws (`F(id)`, `F(g . f)`).
*   **Action Plan (Recommendation: Rewrite Rules):**
    1.  **Unfolding in `whnf`:** `whnf` logic for `FMap0`/`FMap1` should focus on their definitional unfolding when applied to a `MkFunctor_` instance (e.g., `FMap0(MkFunctor_ f0 f1, X) -> f0 X`).
    2.  **Laws as Rewrite Rules:** Implement functoriality laws as system-defined rewrite rules.
    *   **Pros:** Declarative, explicit, uses existing rewrite mechanism, consistent with Phase 1 identity laws and Lambdapi `rule` declarations for functoriality.
*   **Expected Outcome:** Clear separation of definitional unfolding and equational laws, consistency in how laws are handled.

---

### 6. Error Reporting and Debugging (Source Positions)

*   **Summary:** Need richer error messages, verbose tracing, and linking errors to original term locations.
*   **Action Plan:**
    1.  **Source Position Propagation:**
        *   Ensure parser output (raw syntax tree) includes source positions.
        *   Ensure `Cxt.pos` is correctly updated as the elaborator processes subterms.
        *   Capture `Cxt.pos` when errors are created.
        *   Use `SourcePos` in error display functions (file, line, column).
    2.  **Richer Error Messages & Tracing:**
        *   Utilize/enhance `Constraint.origin` for better context in unification failures.
        *   Improve clarity of "cannot unify" messages.
        *   Develop more structured logging/tracing beyond `DEBUG_VERBOSE` (e.g., different flags for different trace types).
        *   Consider optionally returning the final substitution map (solved holes) from `elaborate` for debugging.
*   **Expected Outcome:** Improved developer experience and easier debugging.

---

### 7. Elaboration and Normalization

*   **Summary:** Discussion on whether `elaborate` should normalize the term or just the type.
*   **Action Plan (Recommendation: No Immediate Change):**
    *   **Current Behavior:** Emdash's `elaborate` returns a fully normalized term and type. This is acceptable.
    *   **Rationale:** Normalizing the type is essential. Normalizing the term provides a canonical output.
    *   **Future Consideration:** If performance becomes an issue or unnormalized-but-elaborated terms are needed, consider adding an option to `elaborate` or a separate function. For now, the current behavior is clear and consistent.
*   **Expected Outcome:** Maintain current behavior unless a strong need for change arises.

---
**Next Steps:**
*   Review this action plan.
*   Prioritize items for implementation, likely starting with those impacting Phase 2 development (e.g., implicit handling if it simplifies functor/NT implementation).
*   Begin implementation of Phase 2 features, incorporating relevant planned refinements as feasible. 