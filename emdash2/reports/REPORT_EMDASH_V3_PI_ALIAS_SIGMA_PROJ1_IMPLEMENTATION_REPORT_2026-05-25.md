# emdash v3.2 Pi Alias / Sigma Projection Pullback Implementation Report

Date: 2026-05-25.

Implementation target: `emdash3_2.lp`.

Plan source:
`reports/REPORT_EMDASH_V3_PI_ALIAS_SIGMA_PROJ1_PLAN.md`.

## Summary

The main kernel changes from the plan are now implemented:

- `Pi_cat` is a defined alias for
  `Functord_cat (Const_catd K Terminal_cat) E`.
- The old primitive `Pi_cat` rewrite/unification surface has been removed.
- Constant-family section collapse now belongs to the canonical
  `Functord_cat` head.
- `Sigma_proj1_pullback_catd` implements the special projection-pullback
  comprehension case.
- The terminal-specialized `piapp1_int_*` projection chain has been retired.
- Raw covariant representable and `PathOut` notation have been added.
- A first directed/path-dependent induction primitive has been added, with a
  computation rule through `fib_cov_tapp0_func`.
- The projection-pullback specialization of directed induction reduces to the
  existing `fib_cov_transf`.

## Implemented Changes

### Pi Alias

`Pi_cat` is now:

```lambdapi
symbol Pi_cat [K : Cat] (E : τ (Catd K)) : Cat
≔ @Functord_cat K (@Const_catd K Terminal_cat) E;
```

The old rules targeting `Pi_cat` directly were removed:

- `Functord_cat ConstTerminal E -> Pi_cat E`;
- `Pi_cat (Const_catd K A) -> Functor_cat K A`;
- `Obj(Pi_cat ...)` unification helper;
- `Hom_cat(Pi_cat E) -> Transfd_cat ConstTerminal E`.

The constant-family rule is now installed on canonical `Functord_cat`:

```lambdapi
rule @Functord_cat $K (@Const_catd $K Terminal_cat) (@Const_catd $K $A)
  ↪ Functor_cat $K $A;
```

### Canonical Section Helpers

`pi_eval_transf`, `section_pullback_func`, and `section_pullback_sec` now use
canonical `Functord_cat` source/target forms in their declarations and rules.

The `section_pullback_func` application rule uses the helper head as the
discriminator and leaves source/target category slots inferred:

```lambdapi
rule @fapp0 _ _ (@section_pullback_func $A $B $F $E) $s
  ↪ @section_pullback_sec $A $B $F $E $s;
```

This was necessary because the pullback target normalizes through its defined
composition form before matching.

### Sigma Projection Pullback

Added:

```lambdapi
injective symbol Sigma_proj1_pullback_catd [K : Cat]
  (R D : τ (Catd K))
  : τ (Catd (@Sigma_cat K R));
```

with rules:

- exact fold from `comp_cat_fapp0 D (Sigma_proj1_func R)`;
- fibre computation at `Struct_sigma k r`;
- comprehension bridge:

```lambdapi
rule @Functord_cat
      (@Sigma_cat $K $R)
      (@Const_catd (@Sigma_cat $K $R) Terminal_cat)
      (@Sigma_proj1_pullback_catd $K $R $D)
  ↪ @Functord_cat $K $R $D;
```

Regression assertions cover the pullback fold, fibre projection, `Pi_cat`
bridge, and hom-category bridge to `Transfd_cat R D`.

### `piapp1_*` Audit

Temporary probes showed that the terminal-specialized projection chain could be
removed without losing typechecking:

- `piapp1_int`;
- `piapp1_int_src_transf`;
- `piapp1_int_src_app`;
- `piapp1_int_tgt_transf`;
- rules projecting from `fdapp1_int_transfd`/`tdapp0_fapp0` into those heads.

The remaining `piapp1_func` and `piapp1_fapp0` names are retained as surface
section-action notation. They are no longer the target of a Pi-specific
internal projection pipeline.

The retained generic displayed route is:

```text
tdapp1_int_fapp0_transfd(id_transfd FF)
  -> fdapp1_int_transfd FF
```

with the existing assertions still checking that identity-specialized
displayed action computes through `fdapp1_int_transfd`.

### Raw Representable And `PathOut`

Added raw covariant representable notation distinct from `Edge_catd_func`:

```lambdapi
symbol Rep_catd_func [Z : Cat]
  : τ (Functor (Op_cat Z) (Catd_cat Z))
≔ @hom_int Z Z (@id_func Z);

symbol Rep_catd [Z : Cat] (x : τ (Obj Z)) : τ (Catd Z)
≔ @fapp0 (Op_cat Z) (Catd_cat Z) (@Rep_catd_func Z) x;
```

Thus:

```text
Rep_Z(x)[y] = Hom_Z(x,y)
```

while the existing `Edge_catd_func` remains the pointwise opposite:

```text
Edge_Z(x)[y] = Hom_Z(x,y)^op
```

Added outgoing-arrow total-category notation:

```lambdapi
symbol PathOut_cat [Z : Cat] (x : τ (Obj Z)) : Cat
≔ @Sigma_cat Z (@Rep_catd Z x);
```

with object helpers:

- `pathout_obj Z x y p`;
- `pathout_refl_obj Z x`;
- `pathout_refl_arrow Z x y p`.

`pathout_refl_arrow` is currently a constant head. It names the canonical arrow
from `(x,id_x)` to `(y,p)` in `PathOut_Z(x)`. Its internal construction from
Sigma hom normal forms remains future work.

### Directed Induction

Added:

```lambdapi
symbol path_ind_sec [Z : Cat] (x : τ (Obj Z))
  (E : τ (Catd (@PathOut_cat Z x)))
  (u : τ (Obj (Fibre_cat E (@pathout_refl_obj Z x))))
  : τ (Obj (Pi_cat E));
```

The computation rule evaluates the section at `(y,p)` by existing fibre
transport over the base `PathOut_Z(x)`:

```text
path_ind_sec(x,E,u)[(y,p)]
  = fib_cov_tapp0_func(E, (x,id_x), (y,p), u)(pathout_refl_arrow x y p)
```

The rewrite rule intentionally matches the canonical unfolded base

```text
Sigma_cat (hom_ Z Z (id_func Z) x)
```

instead of the defined `PathOut_cat`/`Rep_catd` names. A probe with a broader
underscore LHS timed out, so the final rule keeps the discriminating shape
narrow.

### Specialization To Ordinary Transport

The special case:

```text
E = Sigma_proj1_pullback_catd (Rep_catd x) D
```

reduces to the existing ordinary transport package:

```lambdapi
rule @path_ind_sec $Z $x
      (@Sigma_proj1_pullback_catd $Z (@hom_ $Z $Z (@id_func $Z) $x) $D)
      $u
  ↪ @fib_cov_transf $Z $D $x $u;
```

This rule also uses the canonical unfolded representable in the LHS; the
`Rep_catd` spelling normalized too early in the probe and did not fire.

## Validation

Commands run successfully:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

The full check covers:

- `emdash2.lp`;
- `emdash3_1.lp`;
- `emdash3_2.lp`.

## Probe Notes

The following temporary probes were used and removed:

- `tmp_piapp1_audit.lp`: verified that the `piapp1_int_*` chain and then
  `piapp1_int` itself could be removed after deleting only the assertions that
  mentioned those retired heads.
- `tmp_path_ind_probe.lp`: verified the directed-induction declarations,
  computation rule, and specialization rule.

One attempted overly broad rule:

```text
tapp0_fapp0 _ Cat_cat _ E (Struct_sigma y p) (path_ind_sec ...)
```

timed out under a 30 second bounded check. The final implementation therefore
uses the narrower canonical base/source family in the LHS.

## Remaining Work

- Construct `pathout_refl_arrow` from Sigma hom/dependent-hom normal forms
  instead of leaving it as a constant.
- Decide whether `piapp1_func` should eventually become a fully defined alias
  over the generic displayed action path, or remain surface notation.
- Continue the internalized-constructor audit for surface syntax, especially
  around `Pi_func`, `Sigma_func`, and future syntax elaboration.
