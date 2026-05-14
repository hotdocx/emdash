# emdash3_1 Mixed-Variance Cleanup Plan

## Summary

Refactor `emdash3_1.lp` into a cleaner v3.1 core by removing the
provisional `Catd` compatibility layer, making `Sigma` and `homd` use
canonical root symbols, and replacing the over-general `hom2_int` root
with the simpler one-parameter `hom_int F : A^op -> B -> Cat`.

The goal is not to add new theory beyond the current typechecking slice;
it is to make the current architecture less redundant and closer to the
intended directed `Fam` foundation.

## Key Changes

- Add a canonical Sigma functor root:

  ```text
  Sigma_func K : Functor (Fam_cat K) Cat_cat
  fapp0 (Sigma_func K) E -> Sigma_cat E
  fapp1_fapp0 (Sigma_func K) eta -> sigma_map_func eta
  ```

  Keep `Sigma_cat` and `sigma_map_func` as stable heads, but make them
  object/action projections of `Sigma_func`.

- Replace the hom root hierarchy:

  ```text
  hom_int [A B] (F : Functor B A)
    : Functor (Op_cat A) (Functor_cat B Cat_cat)

  fapp0 (hom_int F) W -> hom_ F W
  fapp0 (hom_ F W) y -> Hom_cat A W (fapp0 F y)
  ```

  Remove primitive `hom2_int`. If a two-functor hom is needed later,
  derive it as:

  ```text
  comp_cat_fapp0 (hom_int F) (Op_func G)
  ```

- Make `hom_con` non-independent by defining it through `hom_` over
  opposites:

  ```text
  hom_con A W B F -> hom_ (Op_func F) W
  ```

  using the fully explicit opposite-category arguments in Lambdapi.

- Keep `fib_cov_tapp0_fapp0` and its identity/composition rules for now.
  Add a comment clarifying that these are operational stable-head rules
  for Cat-valued functor action; they are mathematically functoriality
  consequences, but not yet derived from generic `fapp1_fapp0` laws in
  this skeleton.

- Rename and rationalize dependent hom symbols:

  ```text
  Homd_cat [Z] (E : Fam Z) : Cat
  Homd [Z] (E : Fam Z) : Grpd := Obj (Homd_cat E)
  homd_int [Z] (E : Fam Z) : Homd E

  homd_eval_func [Z E] (h : Homd E) x u y v
    : Functor (Op_cat (Hom_cat Z x y)) Cat_cat

  homd_ E x u y v
    := homd_eval_func (homd_int E) x u y v
  ```

  Add the canonical computation:

  ```text
  homd_eval_func (homd_int E) x u y v -> sigma_hom_fam E x u y v
  ```

  Remove `Homd_int_cat`, `Homd_int`, and `Homd_func`.

- Keep `sigma_hom_fam` as the endpoint normal form used by the Sigma hom
  rule:

  ```text
  Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
    -> Op_cat (Sigma_cat (sigma_hom_fam E x u y v))
  ```

- Remove the `Core/Catd compatibility layer` entirely from
  `emdash3_1.lp`, including `Core_incl_func`, `Catd_cat`, `Catd`,
  `Fibration_cov_catd`, `Catd_func`, `Catd_fam`, and their assertions.

- Leave the generic Sigma/Pi weakening helpers deferred. Update the TODO
  wording to clarify: the declarations/rules were syntactically
  plausible, but their intended beta assertions did not validate as
  rewrite normal forms. They should get a separate focused pass after the
  canonical core stabilizes.

## Test Plan

Run after each small group of edits:

```bash
lambdapi check -w emdash3_1.lp
```

Final validation:

```bash
lambdapi check -w emdash3.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check -- emdash3_1.lp reports/emdash3_1_mixed_variance_cleanup_plan.md
```

Required regression assertions to keep or add:

```text
fapp0 (Sigma_func K) E == Sigma_cat E
fapp1_fapp0 (Sigma_func K) eta == sigma_map_func eta
comp_cat_fapp0 (Sigma_proj1_func D) (sigma_map_func eta) == Sigma_proj1_func E

fapp0 (hom_int F) W == hom_ F W
fapp0 (hom_ F W) y == Hom_cat A W (fapp0 F y)
fapp0 (hom_con W F) x == Hom_cat A (fapp0 F x) W

fapp0 (fapp0 (Edge_fam Z) x) y == Op_cat (Hom_cat Z x y)
fapp0 (Homd_target_fam E) x == Pi_cat (Functor_fam E (fapp0 (HomPresheaf_fam Z) x))

homd_eval_func (homd_int E) x u y v == sigma_hom_fam E x u y v
fapp0 (sigma_hom_fam E x u y v) f == Hom_cat (Fam_app_cat E y) (fib_cov_tapp0_fapp0 E f u) v
```

## Assumptions

- `emdash3_1.lp` is allowed to break compatibility with the old `Catd`
  vocabulary.
- `hom_int` remains the canonical name for now; later renaming to `hom_`
  can wait until the architecture settles.
- `fib_cov_tapp0_fapp0` remains an explicit stable head even though its
  laws are semantically functoriality laws.
- Generic Sigma/Pi weakening helpers are not part of this cleanup pass.
