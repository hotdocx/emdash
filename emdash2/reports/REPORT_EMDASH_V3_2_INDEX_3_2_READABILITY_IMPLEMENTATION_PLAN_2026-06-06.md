# EMDASH v3.2 `index_3_2.md` Readability Implementation Plan

Date: 2026-06-06

Status: implementation plan for rewriting `print/public/index_3_2.md` for an
external expert reader.

## Summary

Recommendation: keep the v3.2 theorem as the paper's promise, but insert a
standard type-theory-style foundation layer before the detailed `PathOut` and
`PathInd` development. The current draft is technically aligned with
`emdash3_2.lp` and passes validation, but it introduces too many
project-internal identifiers before the reader has a model of directed
families, dependent sums, sections, and dependent homs.

Current checks already pass:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
npm run validate:paper
npm run check:render
```

## Key Changes

- Rewrite the introduction as a reader contract: emdash v3.2 internalizes
  category-theoretic arrow induction computationally, not HoTT identity-path
  induction.
- Add an early "Foundation" section before the current main theorem narrative:
  `A : Cat`, `x : A`, `Hom_A(x,y)` as a category; `E : K |- Cat`, fibres
  `E[k]`, transport `E[f](u)`; `Sigma_k E[k]` as total category;
  `Pi_k E[k]` as section category; and dependent homs
  `homd_E(x,u,y,v)[f] = Hom_{E[y]}(E[f](u), v)`.
- Explain that Sigma homs and section actions share this same dependent-hom
  core.
- Move most kernel identifiers out of the early prose. Main text should use
  mathematical notation first, then give kernel names in compact implementation
  callouts or the glossary.
- Use `χ^{FF}_{p,u}` (read as `cmp(FF,p,u)`) for displayed
  transport-comparison components. Avoid `λ`-style notation for laxity or
  comparison data, since `λ` should remain visually reserved for lambda
  abstraction in type-theoretic prose.
- Rebuild the theorem narrative after the foundation:
  representables, outgoing-arrow categories, canonical `rho`, fixed-source
  arrow induction, primary telescope theorem, derived Sigma-total theorem, and
  composition/transitivity benchmark.
- Keep the old `print/public/index.md` only as rhetorical inspiration. Do not
  reuse stale v2-centered claims about `Catd`, Grothendieck probes, old binder
  modes, or adjunction status.

## Paper Shape

Use this replacement outline for `print/public/index_3_2.md`:

1. Introduction: problem, promise, checked result preview.
2. A Type-Theoretic Foundation For Directed Families.
3. Dependent Hom, Sigma Totals, And Sections.
4. Outgoing Arrows And The Canonical `rho` Arrow.
5. Arrow Induction: Fixed Source, Telescope Form, Sigma-Total Form.
6. Composition As The Main Computation.
7. Surface Syntax And Kernel Names.
8. Normalization Discipline And Checked Evidence.
9. Supporting Examples, Limitations, Future Work.
10. Conclusion.
11. Appendices: identifier glossary, selected checked normal forms, diagram
    notes.

## Interfaces

No Lambdapi API or type changes are planned. The public-facing change is
editorial:

- `print/public/index_3_2.md` becomes the readable long-form v3.2 article
  workbench.
- The main-text notation follows
  `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`.
- Checked claims are cited from `emdash3_2_checks.lp`; long expanded Lambdapi
  terms stay in Appendix B.

## Test Plan

After editing:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
npm run validate:paper
npm run check:render
```

Also run text-level sanity checks:

```bash
rg "Catd|Functord|Transfd|homd_|PathInd|PathOut|Fibration_cov|Total_cat|StrictFunctor" print/public/index_3_2.md
```

Use that pass to ensure early sections are mathematical first, stale v2 terms
are absent or explicitly historical, and kernel identifiers are concentrated in
implementation callouts and appendices.

## Assumptions

- Target reader is an external expert in dependent type theory or HoTT, not an
  emdash contributor.
- The article should be long-form and explanatory, not a compressed conference
  version yet.
- `PathInd_transfd(Z)` remains the primary theorem; `PathInd_funcd(Z)` is
  presented only as derived.
- The foundation section should explain current v3.2 mathematics, not future
  planned structural functor logic.
