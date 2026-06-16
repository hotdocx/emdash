# EMDASH v2 Retirement Audit

Date: 2026-06-16

Status: current retirement audit for the obsolete v2 reference files
`emdash2.lp` and `reports/REPORT_EMDASH2_CONSOLIDATED.md`.

## Conclusion

`emdash2.lp` should no longer be part of the normal v3.2 development workflow.
The active source of truth is `emdash3_2.lp`, with executable diagnostics in
`emdash3_2_checks.lp`.

No v2 block should be ported directly into v3.2. The useful v2 lessons have
already been absorbed, but usually in corrected v3.2 form:

- the old displayed-category layer `Catd : Cat -> TYPE` is superseded by
  directed Cat-valued families, with `Catd_cat K` as the canonical normal form
  of `Functor_cat K Cat_cat`;
- old Grothendieck-specific total machinery is superseded by `Sigma_cat`,
  `Sigma_func`, `sigma_map_func`, and the `homd_int` projection architecture;
- old `Homd_func` / `homd_curry` experiments are superseded by the generalized
  `homd_int(FF)` owner and its stable projection ladder;
- old parameterized `adj` evidence is superseded by first-class
  `Adjunction(R,L)` data and stable projections;
- old rewrite/unification hygiene has been consolidated into the v3.2 SOP and
  the opening conventions of `emdash3_2.lp`.

## Useful v2 Ideas Kept As Future Design Material

The following v2 ideas are worth remembering, but not as direct code ports:

- `path_to_hom_func` and `Core_incl_func`: possible future equality-to-arrow
  bridge around `Path_cat` and `Core_cat`. This should remain separate from the
  kernel until equality/univalence work becomes active.
- `isEquiv` and univalence bridge sketches: mathematically relevant, but
  currently deferred by the v3.2 foundations report. Reintroduce only as a
  focused extension after the equivalence interface is designed for v3.2.
- `Product_catd` / `prodFib`: possible future products of directed motives or
  families. In v3.2 this should be expressed through `Catd_cat K = K ⊢ Cat`
  and `Product_cat_func`, not by restoring the old v2 Grothendieck layer.
- `comp_func`: useful only if ordinary composition must become a first-class
  functor argument. Current v3.2 composition, evaluation, curry, and structural
  logic are sufficient for the active milestone.
- strict/cartesian specializations: do not restore v2 `StrictFunctor_cat`.
  Instead, add constructor-specific folds when a concrete strict family
  constructor should make `fdapp1_int_cell` collapse to an identity/cartesian
  component.
- external modification packaging: v2's `tapp1_fapp1_func` /
  `tdapp1_fapp1_func` idea is represented in v3.2 by internal hom-action heads
  such as `tapp1_int_fapp1_func_transf` and
  `tdapp1_int_fapp1_func_transfd`. External capped interfaces can remain
  deferred until a consumer needs them.

## Retirement Action

The obsolete files were moved to the ignored scratchpad path:

```text
.scratchpad/retired/2026-06-16_v2_reference/
```

Normal validation now checks only the active v3.2 files:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

If historical recovery is explicitly requested later, use the scratchpad copy.
Otherwise, do not consult archived v2 files during normal v3.2 work.
