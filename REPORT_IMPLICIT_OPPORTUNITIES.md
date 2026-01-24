# Report: Implicit Argument Refactoring Opportunities in `emdash2.lp`

## Analysis

The `emdash2.lp` file uses a "kernel-like" style where many arguments are made explicit (`@Symbol`) in rewrite rules. This was likely done to ensure matching robustness or to workaround unification limitations in earlier Lambdapi versions. However, modern Lambdapi handles implicit arguments well, and the excessive use of `@` makes the code verbose and harder to maintain.

## Design Principles

1.  **Remove redundant `@`**: If an argument is implicit in the symbol's definition, do not make it explicit in the rewrite rule LHS unless necessary for structural matching.
2.  **Keep structural `@`**: If a rule matches on a specific constructor in an implicit position (e.g., matching `Op_cat $A` in the category argument of `id`), keep the `@` application or use the explicit argument syntax to ensure the pattern matcher sees the constructor.
3.  **Preserve capture**: If an implicit argument matches a variable `$A` that is *required* in the RHS and cannot be inferred from other arguments in the LHS, keep it explicit (or ensure it can be inferred from the context, though explicit capture is safer).
4.  **Symbol Declarations**: Identify symbols where arguments are declared explicitly `(...)` but are uniquely determined by subsequent arguments, and change them to implicit `[...]`.

## Implementation Plan

### 1. Symbol Declarations (Refactoring Types)

Change the following symbols to use implicit arguments for their category parameters:

- `id`: `(A : Cat)` -> `[A : Cat]`
- `Terminal_catd`: `(A : Cat)` -> `[A : Cat]`
- `Terminal_func`: `(A : Cat)` -> `[A : Cat]`

### 2. Rewrite Rules (Refactoring LHS/RHS)

#### `id`
- `rule @id (Op_cat $A) $X ...` -> `rule id {Op_cat $A} $X ...` (or keep `@id` if cleaner).
- `rule @id (Path_cat $A) $X ...` -> `rule id {Path_cat $A} $X ...`.
- `rule @id Cat_cat $A ...` -> `rule id {Cat_cat} $A ...`.
- `rule @id (Product_cat $A1 $A2) ...` -> `rule id {Product_cat $A1 $A2} ...`.
- `rule @id Terminal_cat ...` -> `rule id {Terminal_cat} ...`.
- **Note**: Since `id` becomes implicit `[A]`, we can remove `@id` and use `{Term}` for the implicit arg if it matches a pattern. Or we can just keep `@id` for these specific pattern-matching rules as they are "structural" on the implicit arg.
- **Decision**: For `id`, the implicit argument is the *primary discriminator* for these rules. Keeping `@id` or using explicit syntax `{}` is required.
    - `rule id {Op_cat $A} $X` vs `rule @id (Op_cat $A) $X`. Both are valid. The latter is fine.
    - However, usages of `id` in RHS should definitely be implicit: `id $A` (if explicit) -> `id` (inferred).

#### `fapp0` / `fapp1_*`
- Remove `@fapp0` where the functor argument uniquely determines the categories.
- Example: `rule @fapp0 _ _ (@Op_func $A $B $F) $xA` -> `rule fapp0 (Op_func $F) $xA`. (Lambdapi infers `_ _`).
- Verify if `Op_func $F` captures `$A $B`. `Op_func : Π [A B], ...`. `$F` does not capture `$A $B` if `$F` is a variable. But here `$F` is a variable.
    - `Op_func` has implicit A B.
    - LHS: `Op_func $F`. Does this match `Op_func {A} {B} F`? Yes.
    - But we need `$A` and `$B` in the RHS?
    - RHS: `@fapp0 $A $B $F $xA`.
    - If we remove `$A $B` from LHS, we lose them for RHS?
    - `Op_func` applied to `$F` implies `$F` has type `Functor A B`.
    - If `$F` is a variable `τ (Functor A B)`, we don't know `A` and `B` unless matched.
    - `Op_func` return type is `Functor (Op_cat A) (Op_cat B)`.
    - Wait, `Op_func` arguments are `[A B : Cat]`.
    - LHS `Op_func $F`. The pattern matcher will instantiate implicit args.
    - Can we bind them? `Op_func {$A} {$B} $F`.
    - So `rule fapp0 (Op_func {$A} {$B} $F) $xA ↪ ...`
    - This is cleaner than `rule @fapp0 _ _ (@Op_func $A $B $F) ...`.

#### `comp_fapp0`
- Similar simplification.

### 3. Cleanup
- Run `make check` after each group of changes.