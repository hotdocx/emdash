# emdash3_1 Homd Endpoint Projection Plan

## Summary

Clean up the dependent-hom endpoint in `emdash3_1.lp` so that `homd_`
is the only endpoint name, but not an independent endpoint computation
primitive. The endpoint should be definitionally the old `sigma_hom_fam`
normal form:

```text
homd_ E x u y v
  := hom_con v (fam_tapp0_func E x y u)
```

The endpoint object computation is therefore a regression assertion/check,
not a primitive rewrite rule. It follows through `hom_con`, `hom_`,
`fam_tapp0_func`, and `fib_cov_tapp0_fapp0`.

The implemented architecture is:

```text
homd_int E      : fully internal mixed-variance Homd object
Homd_source_fam : named source family op o E
Homd_section_fam: named inner section family
homd_src_func   : component functor after projecting homd_int at x
homd_src_sec    : source-fixed section after evaluating homd_int at x,u
homd_tgt_func   : endpoint functor after projecting homd_src_sec at y
homd_           : final endpoint alias for hom_con v (fam_tapp0_func E x y u)
```

## Key Changes

- Remove:

  ```text
  homd_eval_func
  sigma_hom_fam
  ```

  Keep the meaning of `sigma_hom_fam` by defining `homd_` directly as
  `hom_con v (fam_tapp0_func E x y u)`.

- Keep named abbreviations for the source and inner section families:

  ```text
  Homd_source_fam E
    := fapp0 (op_val_func Z) E

  Homd_section_fam E x
    := Functor_fam E (fapp0 (HomPresheaf_fam Z) x)
  ```

- Do not use those named abbreviations as rewrite-rule LHS heads when the
  canonical reduced head is different. In particular, LHSs use
  `fapp0 (op_val_func Z) E` and `Functor_fam ...`.

- Split the old wrapped projection/evaluation rules into progressive
  stable-head steps:

  ```text
  tapp0_fapp0[fapp0 (op_val_func Z) E, Homd_target_fam E] x (homd_int E)
    -> homd_src_func E x

  fapp0 (homd_src_func E x) u
    -> homd_src_sec E x u

  piapp0[Functor_fam E (fapp0 (HomPresheaf_fam Z) x)] (homd_src_sec E x u) y
    -> homd_tgt_func E x u y

  fapp0 (homd_tgt_func E x u y) v
    -> homd_ E x u y v
  ```

- Define `homd_` as the final endpoint shortcut:

  ```text
  homd_ E x u y v
    : Functor (Op_cat (Hom_cat Z x y)) Cat_cat
    := hom_con v (fam_tapp0_func E x y u)
  ```

- Route Sigma homs through `homd_`:

  ```text
  Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
    -> Op_cat (Sigma_cat (homd_ E x u y v))
  ```

## Quick Cleanup

- Remove `Total_cat` and `Total_proj1_func` aliases if they remain unused.
- Keep `fam_tapp0_func` as the transport-functor component of `homd_`.
- Do not add a direct object-action rule for `homd_`; the endpoint beta
  should reduce via the definition above.
- In rewrite-rule LHSs, follow the `emdash2.lp` hygiene rule. The fully
  minimal projection forms:

  ```text
  rule tapp0_fapp0 $x (@homd_int $Z $E) -> ...
  rule piapp0 (@homd_src_sec $Z $E $x $u) $y -> ...
  ```

  were still too under-constrained for subject reduction. The accepted
  compromise is to make only the projection family arguments explicit, using
  canonical heads rather than new abbreviation heads:

  ```text
  rule @tapp0_fapp0 Z Cat_cat (fapp0 (op_val_func Z) E) (Homd_target_fam E) x (homd_int E)
    -> homd_src_func E x

  rule @piapp0 (Op_cat Z) (Functor_fam E (fapp0 (HomPresheaf_fam Z) x)) (homd_src_sec E x u) y
    -> homd_tgt_func E x u y
  ```

  The evaluation rules then have stable LHS heads:

  ```text
  rule fapp0 (homd_src_func E x) u -> homd_src_sec E x u
  rule fapp0 (homd_tgt_func E x u y) v -> homd_ E x u y v
  ```

## Validation

Run incrementally:

```bash
lambdapi check -w emdash3_1.lp
```

Final validation:

```bash
lambdapi check -w emdash3.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
git diff --check -- emdash3_1.lp reports/emdash3_1_homd_endpoint_stable_head_plan.md
```

Implementation note: the projection fold rules are part of the
infrastructure. The reliable regression assertions for this slice are:

```text
fapp0 (homd_ E x u y v) f
  == Hom_cat (Fam_app_cat E y) (fib_cov_tapp0_fapp0 E f u) v

Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
  == Op_cat (Sigma_cat (homd_ E x u y v))
```

Both should pass without a direct endpoint beta rule for `homd_`.

The raw projection fold assertions for `tapp0_fapp0` and `piapp0` remain
deferred: the rules are accepted and appear in the decision trees, but
Lambdapi's assertion conversion is still brittle on those projection terms.
The stable-head evaluation assertions for `homd_src_func` and
`homd_tgt_func` pass.
