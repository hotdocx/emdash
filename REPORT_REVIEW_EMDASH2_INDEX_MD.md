# Review Report: `emdash2` Research Paper (`print/public/index.md`)

**Date:** January 23, 2026
**Reviewer:** Gemini CLI Agent
**Subject:** Comprehensive Review of `print/public/index.md` against `emdash2.lp` and Context Files.

## 1. Executive Summary

Following a complete verification of all referenced source files (including full reads of `emdash2.lp`, `cartierSolution*.lp`, and `emdash_cpp2026.md`), the draft paper `print/public/index.md` is confirmed to be **highly coherent, consistent, and technically accurate**.

The paper correctly distinguishes between:
1.  **The Current Kernel (`emdash2.lp`):** The primary subject, accurately described as a "kernel specification" targeting Lambdapi with specific design patterns (stable heads, off-diagonal components).
2.  **The Executable Prototype (`emdash_cpp2026.md`):** Correctly cited as the "v1 TypeScript kernel" providing evidence for the elaboration pipeline.
3.  **Methodological Precursors (`cartierSolution*.lp`):** Correctly cited as "warm-up" developments that validated the mathematical approach (e.g., "1+2=3 via 3 methods") using an earlier encoding style.

## 2. Detailed Verification of Claims

### 2.1. `emdash2.lp` (The Kernel)
I have verified the existence and semantics of every kernel symbol mentioned in the paper against the full `emdash2.lp` file (3682 lines).

*   **Triangle Identity as Rewrite (Paper §8.2):**
    *   *Claim:* The triangle identity $\epsilon_f \circ L(\eta_g) \rightsquigarrow f \circ L(g)$ is a definitional reduction.
    *   *Verification:* `emdash2.lp` (lines ~3660) contains an explicit `rule @comp_fapp0 ...` matching this pattern, involving `LeftAdj`, `RightAdj`, `UnitAdj`, `CoUnitAdj`. **Confirmed.**

*   **Grothendieck Transport (Paper §10.1):**
    *   *Claim:* Transport on fibre objects is strict and computes definitionally.
    *   *Verification:* `emdash2.lp` defines `fib_cov_tapp0_fapp0` with rules `M(id)(u) ↪ u` and `M(g)(M(f)(u)) ↪ M(g∘f)(u)`. **Confirmed.**

*   **Dependent Comma Category `homd_cov` (Paper §6.2):**
    *   *Claim:* It computes definitionally in the Grothendieck case.
    *   *Verification:* `emdash2.lp` (lines ~2140) contains a `rule` for `fapp0 (@homd_cov ... (@Fibration_cov_catd ...))` that reduces to a `Hom_cat` in the fibre. **Confirmed.**

*   **Internalization Strategy:**
    *   The paper describes `homd_cov_int` as an internal pipeline built from stable heads. `emdash2.lp` contains `homd_cov_int_base` (line ~2018) constructed exactly as described (using `Total_func`, `prodFib_func_func`, `op_val_func`), while keeping `homd_cov_int` itself abstract (`constant symbol`, line ~2033). **Confirmed.**

### 2.2. Contextual Files
*   **`cartierSolution14.lp.txt`:** The paper mentions "1+2=3 via 3 methods". Reading the file confirmed the implementation of:
    1.  `nat_cat` (datatype).
    2.  `inat_func` (adjunction-based).
    3.  `construct_inductively_limit` (colimit-based).
    **Confirmed.**

*   **`cartierSolution16.lp.txt`:** The paper mentions "sieves, sheaves, and schemes". Reading the file confirmed the definitions of `sieve`, `smod` (sheaves), `glue`, `asheme` (affine schemes), and `scheme` (locally ringed sites). **Confirmed.**

*   **`emdash_cpp2026.md`:** The paper refers to this as the report on the "v1 executable kernel" with "functorial elaboration". Reading the markdown confirmed it describes a TypeScript implementation with `MkFunctorTerm` and `CoherenceError`. **Confirmed.**

## 3. Methodology Review
The paper's narrative about "rewrite hygiene" (using stable heads like `fapp1_fapp0` instead of unfolding definitions) is strictly adhered to in the codebase. Every major operation in `emdash2.lp` (e.g., `fapp1_func`, `tapp0_func`, `fib_cov_tapp0_func`) has a corresponding `*_fapp0` stable head and a canonicalization rule. This confirms the paper's claim that this is a deliberate design discipline.

## 4. Conclusion
The paper `print/public/index.md` is a faithful representation of the project. It accurately summarizes the `emdash2.lp` kernel's capabilities and limitations (e.g., acknowledging the "draft" status of simplicial iteration) and correctly situates it within the broader project history. No discrepancies were found.