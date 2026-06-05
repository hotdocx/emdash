# emdash v3.2 Notation Migration And Reorganization Implementation Plan

Date: 2026-06-05

Status: proposed implementation plan, to preserve context before larger edits.

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

### 1. Establish One Current Syntax Authority

Create a new canonical syntax report:

```text
reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md
```

Then replace the old active syntax plan:

```text
reports/REPORT_EMDASH_V3_FAITHFUL_SURFACE_SYNTAX_PLAN.md
```

with a short supersession/redirect to the new canonical report. The old report
uses pre-2026-06-05 arrow/transformation glyphs; leaving it as an
active-looking document would create confusion during the file split.

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

### 3. Add Banners To Other Active/Current Reports

For reports that remain useful but still contain older notation, add a banner
near the top:

```text
Notation warning: this report predates the 2026-06-05 canonical surface syntax.
Use REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md for current
notation.
```

Use in-place full rewrites only for currently active reports where the notation
is central to the report. Historical dated reports can keep old notation behind
the warning banner.

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
emdash2.lp
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
