# emdash3_1 Homd Endpoint Stable-Head Plan

## Summary

Clean up the dependent-hom endpoint in `emdash3_1.lp` so that `homd_`
is the only endpoint normal form. Remove the temporary compound
projection head `homd_eval_func` and the duplicate endpoint alias
`sigma_hom_fam`.

The intended architecture is:

```text
homd_int E      : fully internal Homd object
homd_src_sec    : source-fixed section after evaluating homd_int at x,u
homd_           : final endpoint functor over Hom_Z(x,y)^op
```

## Key Changes

- Remove:

  ```text
  homd_eval_func
  sigma_hom_fam
  ```

- Declare a single intermediate stable head:

  ```text
  homd_src_sec E x u
    : Obj (Pi_cat (Functor_fam E (fapp0 (HomPresheaf_fam Z) x)))
  ```

  It externalizes only the source data `x,u` and keeps `y,v` internal.

- Fold the elementary projection of `homd_int` to `homd_src_sec`:

  ```text
  fapp0 (tapp0_fapp0 x (homd_int E)) u
    -> homd_src_sec E x u
  ```

- Declare `homd_` as the final sequential endpoint head:

  ```text
  homd_ E x u y v
    : Functor (Op_cat (Hom_cat Z x y)) Cat_cat
  ```

- Fold section evaluation to `homd_`:

  ```text
  fapp0 (piapp0 (homd_src_sec E x u) y) v
    -> homd_ E x u y v
  ```

- Give `homd_` the endpoint object beta directly:

  ```text
  fapp0 (homd_ E x u y v) f
    -> Hom_cat (Fam_app_cat E y)
         (fib_cov_tapp0_fapp0 E f u)
         v
  ```

- Route Sigma homs through `homd_`:

  ```text
  Hom_cat (Sigma_cat E) (Struct_sigma x u) (Struct_sigma y v)
    -> Op_cat (Sigma_cat (homd_ E x u y v))
  ```

## Quick Cleanup

- Remove `Total_cat` and `Total_proj1_func` aliases if they remain unused.
- Keep `fam_tapp0_func` as optional transport-functor infrastructure for
  now; it is not an endpoint synonym.

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
infrastructure, but the reliable regression assertions for this slice are
the public endpoint beta for `homd_` and the Sigma hom routing through
`homd_`. The raw `tapp0_fapp0`/`piapp0` projection chains are still
rewrite-matching pressure points for the later Pi/transfor evaluation pass.
