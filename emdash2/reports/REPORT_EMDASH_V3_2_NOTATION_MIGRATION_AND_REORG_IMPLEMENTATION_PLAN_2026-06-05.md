# emdash v3.2 Notation Migration And Reorganization Implementation Plan

Date: 2026-06-05

Status: implementation started; notation cleanup and assertion split completed.
The first temporary reorganization pass has also been promoted into
`emdash3_2.lp`.

## Purpose

`emdash3_2.lp` is now large enough that notation cleanup and file
reorganization should happen before the next feature pass. The immediate goal
is to eliminate the old surface syntax from active comments and docs, then
split diagnostics and eventually split library/thematic material from the core
presentation.

This plan is subordinate to the current notation settlement recorded in:

```text
reports/REPORT_EMDASH_V3_2_FUNCTOR_STRUCTURAL_LOGIC_PRELIM_PLAN_2026-06-04.md
```

especially the section:

```text
Postscript 2026-06-05: Shaped Turnstile And Indexed Hom Notation
```

## Canonical Notation To Preserve

The canonical notation to use in active v3.2 comments and new syntax docs is:

```text
A ⊢ B
  := Functor_cat A B

z :^n Z ; E[z] ⊢ D[z]
  := Functord_cat E D

Π (z :^n Z), D[z]
  := Pi_cat D

a ->^C b
  := Hom_cat C a b

a -> b
  := Hom_cat C a b
     when C is clear

aa[z^-] ->_[z]^R bb[z]
  := Hom_catd R aa bb

aa[z^-] ->_[z] bb[z]
  := Hom_catd R aa bb
     when R is clear

A[z^-] ⊢_[z] B[z]
  := Functor_catd A B

A[z^-] ->_[z]^Cat B[z]
  := Hom_catd (Const_catd Z Cat_cat) A B
   ↪ Functor_catd A B

F => G
  := Transf_cat F G

FF[z^-] =>_[z] GG[z]
  := Transf_catd A B FF GG
```

Important parser/syntax principles:

- `->` and `->_` are distinct operators, not one operator with optional
  decoration.
- `⊢` and `⊢_` are distinct operators. Do not silently collapse `⊢_` to plain
  `⊢`.
- Ambient category/family annotations use superscripts, for example `->^C` and
  `->_[z]^R`.
- Subscripts are reserved for displayed indices and later substitution syntax,
  for example `->_[z]`, `⊢_[z]`, and eventually `->_[z:=f]`.
- `Π` remains the visible notation for terminal-shape section categories.
- The shaped quantification form has no explicit dummy object variable:
  use `z :^n Z ; E[z] ⊢ D[z]`, not `z :^n Z ; e : E[z] ⊢ D[z]`.

## Immediate Implementation Order

## Progress 2026-06-05

Completed:

- created `REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`;
- replaced the older v3 faithful surface-syntax plan with the canonical syntax
  report;
- added a canonical notation banner to `emdash3_2.lp`;
- normalized active `emdash3_2.lp` syntax comments away from the old
  functor/transformation arrow glyphs;
- extracted 314 top-level diagnostic `assert` checks from `emdash3_2.lp` into
  `emdash3_2_checks.lp`;
- updated `scripts/check.sh` and `Makefile` so `make check` checks the active
  v3.2 implementation and diagnostics.
- added notation-warning banners to older reports that still preserve
  pre-2026-06-05 notation.
- created the temporary reorganization workbench files
  `emdash3_2_tmp.lp` and `emdash3_2_tmp_checks.lp`;
- started the tmp-only ordering pass:
  - moved the encoded object-level Sigma block next to the object/groupoid
    foundations;
  - clarified the large early functor/universe section with subsections for
    ordinary functors, universe categories, displayed-family classifiers,
    elementary functor packages, and internalized constructor packages;
  - clarified the path-induction/presheaf section with subsections for
    representables, `PathOut` motives, Sigma-total path induction, and the
    transitivity/presheaf benchmark layer;
  - clarified directed-family constructors with subsections for fibre/pullback
    transport, constant/opposite/displayed composition packages, Pi/section
    action, and dependent-hom endpoint notation;
  - clarified directed Sigma categories with subsections for total categories
    and Sigma homs, Sigma maps and canonical transport arrows, and families
    over Sigma totals;
- renamed the late helper section to record that it contains delayed
  projection rules, especially product-pair telescope rules waiting on
  `const_section_func` and path-induction projections waiting on
  `tdapp0_fapp0`.
- promoted the checked temporary layout from `emdash3_2_tmp.lp` into
  `emdash3_2.lp`.

Latest tmp validation:

```text
timeout 60s lambdapi check -w emdash3_2_tmp.lp
timeout 60s lambdapi check -w emdash3_2_tmp_checks.lp
timeout 60s lambdapi check -w emdash3_2.lp
timeout 60s lambdapi check -w emdash3_2_checks.lp
```

Both temporary checks and both active v3.2 checks pass after promotion.

Still deferred:

- consider deeper definition-level file splits after the assertion split has
  settled.
- do not move `Product_pair_tele_func` computation rules earlier until the
  constant-section machinery is available at their destination;
- do not move `PathInd_transfd` or `Sigma_transfd_funcd` component projection
  rules earlier than the generic displayed component head `tdapp0_fapp0`.

## Reorganization Workbench Policy

Before splitting `emdash3_2.lp` into definition-level modules, do a cleanup and
ordering pass in temporary files:

```text
emdash3_2_tmp.lp
emdash3_2_tmp_checks.lp
```

The active baseline remains:

```text
emdash3_2.lp
emdash3_2_checks.lp
```

The temporary checks file should require the temporary implementation:

```text
require open emdash.emdash3_2_tmp;
```

Every temporary reorganization stage must pass:

```text
lambdapi check -w emdash3_2_tmp.lp
lambdapi check -w emdash3_2_tmp_checks.lp
```

Only after the temporary layout is stable should the same edits be applied to
the active `emdash3_2.lp` and `emdash3_2_checks.lp`.

Recommended temporary stages:

1. Comment/section cleanup only:
   - fix stale section names left by the assertion split;
   - add missing or clearer section headings;
   - split huge conceptual sections with subsection comments without moving
     declarations.
2. Dependency-preserving local moves:
   - keep `τΣ_` and object-level encoded Sigma near the foundations;
   - keep ordinary `Product_cat` before any ordinary functor/transfor code that
     projects products;
   - consolidate product telescope rules with the constant-section machinery
     they depend on, or document why they are delayed;
   - keep ordinary `Transf` core separate from Product/Eval/Curry/Internal
     action material.
3. Larger thematic regrouping, only after successful temporary checks:
   - separate ordinary category/functor/transfor core;
   - separate directed-family constructors (`Catd`, `Functord`, `Transfd`,
     `Pi`, `Sigma`);
   - separate mixed-variance constructors (`Hom_catd`, `Functor_catd`,
     `Transf_catd`);
   - separate path-induction, displayed internal hom/action, and
     Sigma-laxity-oriented projection pipelines.

Do not reorder a declaration merely because the target layout is nicer. First
identify the symbols/rules that depend on it, move a small block in the
temporary file, and re-run both temporary checks.

### 1. Establish One Current Syntax Authority

Create a new canonical syntax report:

```text
reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md
```

Then retire the old active-looking syntax plan in favor of the new canonical
report. The old report used pre-2026-06-05 arrow/transformation glyphs; leaving
it as active guidance would create confusion during the file split.

### 2. Normalize Active Syntax Comments In `emdash3_2.lp`

Before splitting files, update syntax comments in `emdash3_2.lp` so the file
uses the canonical notation consistently. This is a documentation/comment pass
only; it should not change symbol declarations, rewrite rules, or assertions
except where comments are embedded in examples.

Priorities:

- add a short canonical notation banner near the top of the file;
- replace ordinary functor-category comments written with old ASCII arrows
  with `A ⊢ B`;
- replace displayed-functor comments written with the old arrow glyphs with
  `k :^n K ; E[k] ⊢ D[k]`;
- replace mixed-variance functor comments written with old indexed arrow glyphs with
  `A[k^-] ⊢_[k] B[k]`;
- replace generic indexed hom comments with `aa[k^-] ->_[k]^R bb[k]`;
- replace transformation comments written with old double-arrow glyphs with `F => G` and indexed
  transformation comments with `FF[k^-] =>_[k] GG[k]`;
- keep `Π (k :^n K), E[k]` for `Pi_cat E`.

Do not use this pass to redesign the kernel. If a comment cannot be updated
faithfully without theory work, leave a local TODO noting the missing
construction rather than inventing a misleading notation.

### 3. Retire Or Update Older Reports

Reports that remain active should use the canonical notation directly or point
to the canonical syntax report as their notation authority. Historical dated
reports that still use older notation should be archived rather than left in
`reports/` with warning banners.

### 4. Split Diagnostics After Notation Cleanup

After notation comments are normalized, move diagnostic/debug-style `assert`
checks out of `emdash3_2.lp` into:

```text
emdash3_2_checks.lp
```

The checks file should require the main development:

```text
require open emdash3_2;
```

and `scripts/check.sh` should check:

```text
emdash3_2.lp
emdash3_2_checks.lp
```

This first split keeps `emdash3_2.lp` as the authoritative module, avoiding
module-qualified-name churn while reducing the active implementation file.

### 5. Split Definitions Later, Driven By Dependencies

Only after the assertion split should we consider splitting definitions. A
likely eventual organization is:

```text
emdash3_2.lp                 public entry / wrapper
emdash3_2_core.lp            Cat, Obj, Hom, Op, Path, Functor, Catd/Functord/Transfd classifiers
emdash3_2_hom.lp             ordinary internal hom and hom action
emdash3_2_transf.lp          ordinary transfors and transfor projections/actions
emdash3_2_directed.lp        Pullback_catd, Const_catd, Pi_cat, Sigma_cat
emdash3_2_mixed.lp           Hom_catd, Functor_catd, Transf_catd
emdash3_2_products.lp        Product_cat and product maps
emdash3_2_curry.lp           Eval, curry, uncurry
emdash3_2_homd_sigma.lp      homd/Sigma/fibcov/pathout thematic infrastructure
emdash3_2_structural.lp      weakening, exchange, contraction once implemented
```

This list is provisional. The actual split should follow the dependency graph
found during the assertion split and typechecking probes.

## Validation

After each batch:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
```

After adding `emdash3_2_checks.lp`, also check it directly:

```bash
timeout 60s lambdapi check -w emdash3_2_checks.lp
```
