# Review Report: `emdash2` Research Paper (`print/public/index.md`)

**Date:** January 23, 2026
**Reviewer:** Gemini CLI Agent
**Subject:** Coherence and Consistency Review of `print/public/index.md` against the `emdash2` codebase.

## 1. Executive Summary

The draft paper `print/public/index.md` is **highly coherent, consistent, and technically accurate** with respect to the provided source files, particularly the primary kernel specification `emdash2.lp`.

The paper successfully navigates the distinction between the project's phases:
1.  **v1 (TypeScript Kernel):** Documented in `emdash_cpp2026.md`, referenced as proof of feasibility for the elaboration pipeline.
2.  **Warm-ups (Lambdapi):** `cartierSolution*.lp` files, correctly cited as methodological precursors for large-scale interfaces (schemes, arithmetic).
3.  **v2 (Current Lambdapi Kernel):** `emdash2.lp`, the main subject of the paper.

The paper faithfully describes the specific design patterns of `emdash2.lp`—such as "stable rewrite heads," "off-diagonal components" (`tapp1_fapp0`), and the "simplicial" dependent-hom approach (`homd_cov`)—without overstating the completeness of the current implementation.

## 2. Detailed Alignment Check

### 2.1. Kernel Primitives and Symbols
The paper's "Appendix A" and technical sections cite specific kernel symbols. All checked symbols are present in `emdash2.lp` with matching semantics:

| Paper Symbol | `emdash2.lp` Status | Notes |
| :--- | :--- | :--- |
| `Cat`, `Obj`, `Hom_cat` | **Present** | Core classifiers. |
| `Functor_cat`, `fapp0`, `fapp1_func` | **Present** | Functor infrastructure. |
| `fapp1_fapp0` | **Present** | "Stable head" for hom-action on 1-cells. |
| `Transf_cat` | **Present** | Transformation category. |
| `tapp0_fapp0` | **Present** | Diagonal component (pointwise). |
| `tapp1_fapp0` | **Present** | Off-diagonal/arrow-indexed component. |
| `Catd`, `Fibration_cov_catd` | **Present** | Displayed categories and Grothendieck construction. |
| `fib_cov_tapp0_fapp0` | **Present** | Strict Grothendieck object transport. |
| `homd_cov` | **Present** | Dependent comma category. Paper correctly notes it computes for Grothendieck totals. |
| `homd_cov_int` | **Present** | Internalized version. Paper correctly notes this is currently abstract/draft. |
| `adj` | **Present** | Adjunction interface (at the end of the file). |

### 2.2. Computational Claims
The paper makes specific claims about what "computes definitionally" (via rewrite rules) versus what is "abstract." These claims match the code:

*   **Triangle Identity:** Section 8.2 claims the triangle law is a rewrite rule.
    *   *Verification:* `emdash2.lp` (lines ~3660) contains a rewrite rule for `comp_fapp0` involving `LeftAdj`, `RightAdj`, etc., which implements this.
*   **Grothendieck Transport:** Section 10.1 mentions `fib_cov_tapp0_fapp0` has strict functoriality rules.
    *   *Verification:* `emdash2.lp` contains rules `fib_cov_tapp0_fapp0 ... id ... ↪ u` and recursive packing for composition.
*   **Opposites/Products:** The paper claims these compute.
    *   *Verification:* `emdash2.lp` has explicit rewrite rules for `Op_cat`, `Product_cat`, etc.

### 2.3. Methodology and Philosophy
The paper's narrative about "rewrite hygiene" (using stable heads like `fapp1_fapp0` instead of unfolding large definitions) is visibly strictly adhered to in the `emdash2.lp` comments and rule structure. The distinction between the "globular" iteration (via `Hom_cat`) and the "simplicial" organization (via `homd_cov` over base arrows) is accurately reflected in the types and comments of the kernel.

## 3. Relationship to Context Files

*   **`emdash_cpp2026.md` (v1 Report):** The paper correctly frames this as the "executable evidence" for the elaboration strategy (functorial elaboration), while clarifying that v2 (`emdash2.lp`) is the "kernel specification" targeting Lambdapi directly.
*   **`cartierSolution*.lp` (Warm-ups):** The paper cites these appropriately as "warm-ups" that validated the approach (e.g., "1+2=3 via adjunctions") but acknowledges they used an older/different encoding. This avoids confusion between the different Lambdapi files.

## 4. Suggestions and Minor Observations

*   **Draft Status:** The paper is honest about the "draft" status of simplicial iteration (`fdapp1_funcd`) and the abstract nature of `homd_cov_int`. This is good practice.
*   **Sanity Checks:** The paper mentions "Sanity" assertions. These are indeed present throughout `emdash2.lp` (`assert ... ⊢ ... ≡ ...`), confirming that the code is not just a definition list but a checked logic.

## 5. Conclusion

The paper `print/public/index.md` is a faithful and high-quality representation of the `emdash2` project. It accurately summarizes the technical content of the kernel, respects the distinction between implemented features and future work, and correctly contextualizes the supporting files. No structural or factual corrections are required for the "Initial Version."
