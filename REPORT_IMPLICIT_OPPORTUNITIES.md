# Report: Implicit Argument Opportunities in `emdash2.lp`

## Goal
Improve readability and robustness of rewrite rules by maximizing the use of implicit arguments and type inference, reducing the need for explicit `@Symbol` applications and redundant argument matching.

## Analysis
Many rewrite rules in `emdash2.lp` currently use explicit application (`@Symbol`) to provide implicit arguments. While necessary in some cases (for pattern matching on the implicit argument), in many cases it is redundant because the implicit arguments can be inferred from the explicit ones.

Redundancy leads to:
1.  **Verbosity**: Harder to read.
2.  **Fragility**: "Complex computable terms" (like `Path_cat ($x=$y)`) in implicit positions can cause matching issues or require the user to manually sync the implicit arg with the explicit one.
3.  **Maintenance burden**: Changing a symbol's implicits requires updating all explicit rules.

## Design & Architecture

The refactoring follows these principles:

### 1. Symbols without implicit arguments
**Rule:** Remove `@` prefix.
**Example:**
- `rule @id (Op_cat $A) $X ...`  ⟶  `rule id (Op_cat $A) $X ...`
- `id` takes explicit `A`.

### 2. Redundant Implicit Arguments in LHS
**Rule:** If an implicit argument is strictly inferred from an explicit argument (via type dependency) and is *not* structurally matched, omit it.
**Mechanism:**
- If *all* implicits are inferred/redundant: Remove `@` and the implicit args.
- If *some* implicits are needed (for capture): Use `_` for the redundant ones.

**Examples:**
- `rule @fapp0 _ _ (@Op_func $A $B $F) $xA`
  ⟶ `rule fapp0 (@Op_func $A $B $F) $xA`
  (`fapp0` implicits `A`, `B` are inferred from `Op_func` type).

- `rule @fapp1_func _ _ (@Core_incl_func $C) ...`
  ⟶ `rule fapp1_func (@Core_incl_func $C) ...`

- `rule @fapp1_fapp0 $A $B (@sfunc_func $A $B $Fs) ...`
  ⟶ `rule fapp1_fapp0 (@sfunc_func $A $B $Fs) ...`
  (Redundant capture of `$A`, `$B`).

### 3. Essential Implicit Arguments in LHS
**Rule:** Keep `@` and the explicit argument if it is required for:
- **Structural Matching:** Restricting the rule to a specific constructor.
  - e.g. `rule @Hom_cat (Op_cat $A) ...` (Must match `Op_cat`).
  - e.g. `rule @Hom_cat Cat_cat ...` (Must match `Cat_cat`).
- **Variable Capture:** Binding a variable used in the RHS that isn't present in explicit args.
  - e.g. `rule @fapp1_fapp0 _ _ op $A1 $A2 $F ... ↪ @Op_func $A1 $A2 $F`
    (Here `fapp1_fapp0` has implicits `[A B]` and `[X Y]`. `A,B` are `Cat_cat` (can be `_`), but `X,Y` are `$A1, $A2` which we need for RHS. So we must use `@` to reach them).

### 4. Complex Terms in Implicits
**Rule:** Remove explicit matching of complex terms in implicit positions if they are implied by the explicit arguments.
**Example:**
- `rule @fapp0 (Path_cat ($x = $y)) _ (@path_to_hom_func $C $x $y) $p`
  ⟶ `rule fapp0 (@path_to_hom_func $C $x $y) $p`
  (`path_to_hom_func` return type forces the first implicit of `fapp0` to be `Path_cat ...`. Explicit matching is redundant and potential source of "computable term" issues).

### 5. RHS Simplification
**Rule:** Always prefer implicit application in RHS.
**Example:**
- `... ↪ @comp_fapp0 $A $Z $Y $X $f $g`
  ⟶ `... ↪ comp_fapp0 $f $g`

## Implementation Plan

1.  **Sanitize `id`**: Replace `@id` with `id` globally.
2.  **Simplify `fapp0` rules**: Remove `@fapp0 ...` where `F` determines domains.
3.  **Simplify `fapp1_func/fapp1_fapp0` rules**: Remove `@` and redundant implicits.
4.  **Simplify `comp_fapp0` rules**: Remove `@` in RHS. In LHS, keep `@` only if matching `Op_cat`, `Path_cat`, `Cat_cat`.
5.  **Simplify `Op_func` rules**: Remove redundant captures.
6.  **Review `unif_rule`**: Keep explicit if capturing for constraints, simplify otherwise.

## Specific Candidates Identified

| Symbol | Case | Proposed Change |
| :--- | :--- | :--- |
| `id` | Explicit arg | `rule @id ...` ⟶ `rule id ...` |
| `fapp0` | `Op_func` | `rule @fapp0 _ _ (@Op_func ...) ...` ⟶ `rule fapp0 (@Op_func ...) ...` |
| `fapp0` | `path_to_hom` | `rule @fapp0 (Path_cat ...) ... (@path_to_hom_func ...) ...` ⟶ `rule fapp0 (@path_to_hom_func ...) ...` |
| `fapp0` | `op` | `rule @fapp0 _ _ op ...` ⟶ `rule fapp0 op ...` |
| `fapp0` | `comp_cat` | `rule @fapp0 ... (@comp_cat_fapp0 ...)` ⟶ `rule fapp0 (@comp_cat_fapp0 ...)` |
| `fapp1_func` | `Core_incl` | `rule @fapp1_func _ _ (@Core_incl_func ...) ...` ⟶ `rule fapp1_func (@Core_incl_func ...) ...` |
| `fapp1_fapp0` | `sfunc` | `rule @fapp1_fapp0 $A $B (@sfunc_func $A $B $Fs) ...` ⟶ `rule fapp1_fapp0 (@sfunc_func $A $B $Fs) ...` |
| `Op_func` | `Op_func` | `rule Op_func (@Op_func $A $B $F) ...` ⟶ `rule Op_func (Op_func $F) ...` |
| `Pullback_catd` | `Fibration` | `rule @Pullback_catd $A $B (@Fibration_cov_catd $B $E) $F` ⟶ `rule Pullback_catd (@Fibration_cov_catd $B $E) $F` |

