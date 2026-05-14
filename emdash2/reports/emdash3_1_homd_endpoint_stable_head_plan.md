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
Homd_source_fam : stable name for op o E
Homd_section_fam: stable name for Functor_fam E (HomPresheaf_fam x)
homd_src_sec    : source-fixed section after evaluating homd_int at x,u
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

- Declare stable helper heads for the two dependent families that otherwise
  appear as compound inferred arguments:

  ```text
  Homd_source_fam E
    := op o E

  Homd_section_fam E x
    := Functor_fam E (fapp0 (HomPresheaf_fam Z) x)
  ```

- Declare the source-fixed section head:

  ```text
  homd_src_sec E x u
    : Obj (Pi_cat (Functor_fam E (fapp0 (HomPresheaf_fam Z) x)))
  ```

  It externalizes only the source data `x,u` and keeps `y,v` internal.

- Fold the elementary projection of `homd_int` to `homd_src_sec`:

  ```text
  fapp0 (tapp0_fapp0[Homd_source_fam E, Homd_target_fam E] x (homd_int E)) u
    -> homd_src_sec E x u
  ```

- Define `homd_` as the final endpoint shortcut:

  ```text
  homd_ E x u y v
    : Functor (Op_cat (Hom_cat Z x y)) Cat_cat
    := hom_con v (fam_tapp0_func E x y u)
  ```

- Fold section evaluation to `homd_`:

  ```text
  fapp0 (piapp0[Homd_section_fam E x] (homd_src_sec E x u) y) v
    -> homd_ E x u y v
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
- In rewrite-rule LHSs, follow the `emdash2.lp` hygiene rule: avoid spelling
  out inferred/implicit arguments with compound expressions. The fully
  minimal forms:

  ```text
  rule fapp0 (tapp0_fapp0 $x (@homd_int $Z $E)) $u -> ...
  rule fapp0 (piapp0 (@homd_src_sec $Z $E $x $u) $y) $v -> ...
  ```

  were too under-constrained for subject reduction. The accepted compromise
  is to name the relevant families first, then use those stable heads in the
  LHS:

  ```text
  rule fapp0
        (@tapp0_fapp0 Z Cat_cat (Homd_source_fam E) (Homd_target_fam E) x (homd_int E))
        u
    -> homd_src_sec E x u

  rule fapp0
        (@piapp0 (Op_cat Z) (Homd_section_fam E x) (homd_src_sec E x u) y)
        v
    -> homd_ E x u y v
  ```

  This still avoids the problematic raw compound expressions
  `comp_cat_fapp0 ...` and `Functor_fam ...` in inferred positions.

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

The raw projection fold assertions remain deferred: the rules are accepted
and usable as rewrite infrastructure, but Lambdapi's assertion conversion is
still brittle on these transfor/Pi projections.
