# emdash2 Consolidated Reference

## Current Source of Truth

`emdash2.lp` is the v2 reference development. It remains important as the
largest tested Lambdapi specification and as the source of rewrite/unification
SOP used by `emdash3_1.lp`, but active v3 architecture work should use
`emdash3_1.lp` and `REPORT_EMDASH_V3_CONSOLIDATED.md`.

The old `PLAN_*.md` and emdash2 `REPORT_EMDASH_LOGIC_DEV*.md` files were
development-time plans. Their useful lessons are consolidated here; the files
themselves are retired into `.scratchpad/backup/2026-05-15_emdash2_reports_retirement/`.

The older surface-syntax note `docs/SYNTAX_SURFACE.md` was v2-specific and
pre-v3.1. It is retired into
`.scratchpad/backup/2026-05-15_project_docs_retirement/SYNTAX_SURFACE.md`;
recover it only when revisiting the v2 surface elaboration story.

## Stable Kernel Discipline

- Keep primitives small and make computational behavior explicit through
  rewrite rules and local unification helpers.
- In rewrite-rule LHSs, avoid spelling reducible compound terms in inferred
  implicit arguments. Use `_` unless the argument is an actual discriminator.
- Prefer functor-level stable-head folds over capped object-level rewrites when
  the result should remain iterable to higher cells.
- For chosen classifier heads, keep local unification helpers that recover
  implicit structure, such as `Hom_cat`, `Functor_cat`, `Fibre_cat`,
  `Functord_cat`, `Transf_cat`, and `Transfd_cat`.
- Add small assertions or computes when adding rewrite rules so the intended
  normal form is exercised immediately.

## Implemented v2 Architecture

- Core category layer:
  `Cat`, `Obj`, `Hom_cat`, `Op_cat`, `Path_cat`, `Functor_cat`, `Grpd_cat`,
  `Cat_cat`, `id_func`, `comp_cat_fapp0`, `Op_func`, and internalized
  `hom_`, `hom_con`, `hom_int`.
- Displayed category layer:
  `Catd`, `Fibre_cat`, `Fibre`, `Functord_cat`, `Catd_cat`, `Catd_func`,
  `Terminal_catd`, `Pullback_catd`, `Lift_catd`, `Op_catd`, and
  `Fibration_cov_catd` / `Fibration_con_catd`.
- Pointwise displayed constructors:
  `Functor_catd` and `Transf_catd` are implemented fibrewise. They intentionally
  do not assert a general transport/cleavage semantics for arbitrary `Catd Z`.
- Total categories:
  `Total_cat E` now has an always-Sigma object layer for arbitrary displayed
  categories, with `Total_proj1_func` computing on `Struct_sigma`.
  Terminal/lift collapses still exist as shortcuts and must be handled
  carefully when extending total-category rules.
- Grothendieck transport:
  `fib_cov_tapp0_fapp0`, `fib_cov_transf`, `fib_cov_tapp0_func`, and
  `comp_hom_con_fib_cov` provide strict opfibration-style object transport and
  the induced hom-family shape for Cat-valued functors.
- Internal dependent hom:
  `homd_int` is a typed internal packaging head.
  `homd_` has a concrete Grothendieck/Grothendieck pointwise computation.
  `homd_curry`, `homd_curry_base_fam`, `homd_curry_base`,
  `homd_curry_fapp0`, and `homd_curry_fapp0_uncurry` provide the current
  internal projection pipeline.
  `Homd_func` is the current total-hom classifier head in v2 and routes
  `Hom_cat (Total_cat E)` through the curry pipeline, with a Groth shortcut.
- Transformation layer:
  `Transf_cat` / `Transf`, `tapp0_func` / `tapp0_fapp0`,
  `tapp1_func_funcd`, `tapp1_fapp0_funcd`, `tapp1_int_func_transf`,
  `fapp1_int_transf`, and `tapp1_fapp1_func` package ordinary transfors and
  modifications.
- Displayed transformation layer:
  `Transfd_cat` / `Transfd`, `tdapp0_func` / `tdapp0_fapp0`,
  `Fibre_transf`, `tdapp1_func_funcd`, `tdapp1_fapp0_funcd`,
  `tdapp1_int_func_transfd`, `fdapp1_int_transfd`, and `tdapp1_fapp1_func`
  package displayed transfors and displayed modifications.
- Draft law layer:
  strict ordinary naturality for `tapp1_fapp0` is present as cut-elimination
  rewrite rules; displayed analogues remain less complete.
  The adjunction interface is present with projection unification helpers and
  one draft triangle cut-elimination rule.

## Retired Plan Status

- `REPORT_EMDASH_LOGIC_DEV.md` planned `Functor_catd`, `Transf_catd`, and
  `Fibre_transf`; these are now implemented in `emdash2.lp`.
- `REPORT_EMDASH_LOGIC_DEV_2.md` planned a parallel `TotalΣ_cat` /
  `homd_int_alt*` migration. The current file instead made `Total_cat` itself
  always-Sigma on objects and moved to the `homd_curry` / `Homd_func` pipeline.
- `PLAN_EMDASH_INTERNALIZED_CATEGORY_LAYER.md` and
  `PLAN_EMDASH_FUNCTOR_CATD_TRANSF_CATD.md` describe TypeScript-facing
  implementation slices for infrastructure that already exists in the
  Lambdapi reference.
- `PLAN_EMDASH_STRICT_ACCUMULATION_ORDINARY.md` corresponds to the strict
  `tapp1_fapp0` accumulation rules now present in `emdash2.lp`.
- `PLAN_EMDASH_TYPESCRIPT_ELABORATION*.md` files are older TypeScript
  elaboration plans tied to the v2 `homd_curry`/`Catd` design. They are not
  current v3 guidance and should be recovered from scratchpad only when the
  TypeScript layer is explicitly revisited.

## Validation SOP

For the v2 reference, run:

```bash
lambdapi check -w emdash2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

`make check` also checks `emdash3_1.lp`, because v3.1 is now active.
