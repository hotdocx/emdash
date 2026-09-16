# EMDASH Reviewer Milestones

These examples are small checked entry points for external readers. They do not
replace `emdash3_2_checks.lp`; they select representative normal forms that
show why the kernel is meaningful.

For an affected feature, use its focused reviewer and the resource profile in
`../AGENTS.md`. The complete example aggregate is available when the scope
requires it:

```bash
make examples
```

Current milestone files:

- `path_category.lp`: path categories and equality-as-arrows.
- `products_eval_curry.lp`: products, evaluation, curry, and uncurry.
- `sigma_total.lp`: Sigma totals, projections, and Sigma-map action.
- `dependent_hom_laxity.lp`: dependent hom projection, whole displayed
  laxity extraction, ordinary post/pre witnesses, and the projected
  normal-lax functor compositor.
- `path_induction_transitivity.lp`: path induction producing composition /
  transitivity.
- `adjunction_triangles.lp`: ordinary adjunction triangle cut-elimination.
- `profunctor_weighted_limits.lp`: profunctor tensor/closed computation,
  weighted representability, and right-adjoint preservation.
- `directed_join.lp`: directed join inclusions, cross cell, recursor betas, and
  the non-product boundary.

Native universality and homology reading route:

- `one_cat_adjunction_families.lp`: whole postcomposition adjunctions and mates.
- `one_cat_diagram_reconstruction.lp` and
  `one_cat_terminal_family_universality.lp`: ordinary structural DefIso
  presentations and their endpoint computations.
- `one_cat_product_families.lp` and
  `one_cat_kernel_pullback_universality.lp`: whole pairing and the derived
  native kernel pullback comparison.
- `freyd_native_diagram_exactness.lp`: the displayed native LES certificate
  interface. The [final audit](../../docs/TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md)
  routes to its concrete nonsplit workflow and the native snake evidence.

This is a selected reading route, not an exhaustive check catalog. The
[consolidation review](../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_REVIEW.md)
distinguishes structural declarations, derived constructions and older
reference interfaces; its proposed source cleanup has not yet been performed.
