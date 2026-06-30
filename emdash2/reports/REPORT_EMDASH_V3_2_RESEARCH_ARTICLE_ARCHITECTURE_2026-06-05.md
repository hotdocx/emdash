# EMDASH v3.2 Research Article Architecture

Date: 2026-06-05
Last updated: 2026-07-01

Plan-ID: EMDASH-V3-2-RESEARCH-ARTICLE-2026-06-05
Depends-On: EMDASH-V3-2-INDEX-READABILITY-2026-06-06, EMDASH-V3-2-NOTATION-REORG-2026-06-05
Supersedes: none
Side-Task-Ledger: none
Infinity-Codex-Origin: pre-infinity-codex
Infinity-Codex-Decision-Responses: none

Status: active article architecture for the long v3.2 paper workbench. The
original 2026-06-05 design centered the article on synthetic arrow induction
and computational composition. The 2026-07-01 update keeps that as the opening
reader-facing theorem, then extends the article to cover the now-active
profunctor, tensor/internal-hom, weighted-limit, duality, join-category,
DefIso/comparison, and MathOps/Infinity-Codex developments.

## Goal

The new article should not be a line-by-line update of the v2 paper. The v2
paper is useful as a rhetorical baseline and for reusable diagrams, but its
technical center is now obsolete. The v3.2 article should be organized around
the new synthetic arrow/path-induction package and the directed composition
benchmark:

```text
PathOut_Z(x) = Σ y :^n Z, Hom_Z(x,y)
rho_{x,y,p} : (x,id_x) ->^PathOut_Z(x) (y,p)

PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x]

path_comp_sec(x)[p][z](q) = q o p.
```

The leading reader promise should be:

> emdash v3.2 internalizes a category-theoretic arrow induction principle as a
> computational theorem in Lambdapi. The theorem is expressed using shaped
> functor categories and displayed transformations, and its most visible
> regression is that directed transitivity/composition computes by normalization.

## 2026-07-01 Expansion Plan

### Review Findings

Since the first `print/public/index_3_2.md` draft, the active kernel and
diagnostics have moved well beyond the initial PathOut theorem.

Implemented and checked developments that should now enter the long article:

- Cat-valued profunctors:
  `Prof_cat(A,B) = Catd_cat(A^op × B)`, `ProfMap`, representables
  `Hom_prof_along(F,G)`, endpoint reindexing by `Prof_reindex`, and the
  internal right-representable embedding `Hom_prof_func`.
- Tensor/co-Yoneda/internal-hom calculus:
  symbolic `Prof_tensor`, fixed tensor functor `Prof_tensor_func`, fixed
  vertical tensor map `Prof_tensor_map`, shaped composition
  `Prof_tensor_hom_hom`, fixed co-Yoneda transformations
  `Prof_coyoneda_cov_transf`/`Prof_coyoneda_con_transf`, and the covariant and
  contravariant implication/eval/lambda cores `Prof_imply_*`,
  `Prof_eval_*_map`, and `Prof_lambda_*_map`.
- Weighted limits as representability:
  `WeightedCone_prof`, ordinary `IsWeightedLimit_cov_iso`, computational
  `IsWeightedLimit_cov_comp`/`WeightedLimit_cov`, arbitrary-probe
  `weighted_limit_cov_push/pull`, and selected universal/cone maps.
- Adjunction preservation:
  `Adjunction_hom_prof_comparison`, transparent mate views
  `Adjunction_prof_transpose/untranspose`,
  `right_adjoint_preserves_weighted_limit_cov_comp`, its ordinary evidence
  projection, and the public `right_adjoint_preserves_weighted_limit_cov`
  alias.
- Duality:
  stable semantic `Op_prof`/`Op_prof_func`, opposite adjunctions,
  `WeightedColimit_con`, `Op_weighted_limit_cov`,
  `Op_weighted_colimit_con`, and
  `left_adjoint_preserves_weighted_colimit_con` by applying the right-adjoint
  theorem to `Op_adjunction`.
- Directed-inductive stress test:
  primitive `Join_cat(A,B)`, inclusions, internally natural
  `join_cross_transf`, shaped `join_cross_hom`, and `join_elim_func` with
  inclusion and cross-cell beta computation.
- Evidence and comparison infrastructure:
  the groupoid/equality/univalence staging, stable `DefIso`, and the
  migration of public `ProfComparison` compatibility through DefIso and the
  hom-action owners.
- MathOps/DevOps:
  active report index, health/check catalog generation, rewrite-LHS audit,
  warning summaries, examples, and the Infinity Codex final-response archive
  and compaction-recovery hooks.

The most important architectural correction for the paper is the
runtime/proof-time boundary around hom-action and composition heads:

```text
hom_postcomp_* / hom_precomp_along_* / hom_postcomp_fapp0
  runtime cut-elimination and reusable hom-action owners

comp_fapp0 / comp_cat_fapp0 / comp_catd_fapp0
  ordinary composition heads, proof-time comparison surfaces, and generic
  functor/category composition normal forms
```

The article should explain that some Cat-specialized heads are retained only
when they expose Cat-only transfor projections such as `tapp0_fapp0`,
`tapp1_func`, or `tapp1_fapp0`. It should not present Cat/Catd
specializations as a license to duplicate ordinary functoriality.

### Revised Article Strategy

Keep `print/public/index_3_2.md` as the long article workbench. Do not promote
it to `index.md` or derive a short `index_0.md` in this pass.

The revised article should have two arcs:

1. **Readable theorem arc.** Sections 1-9 continue to introduce directed
   families, dependent homs, Sigma/Pi, PathOut, synthetic arrow induction, and
   the composition benchmark.
2. **Broader calculus arc.** New sections after the normalization-method
   discussion introduce Cat-valued profunctors, tensor/co-Yoneda/internal hom,
   weighted limits and adjoint preservation, duality, primitive join, DefIso
   and univalence staging, and the artifact/MathOps story.

This ordering is deliberate. The PathOut theorem remains the first complete
computation a reader can understand. The profunctor material then shows that
the same normalization discipline scales to a larger fragment of categorical
programming.

### Planned Article Edits

1. Update the title/subtitle, abstract, and contribution list so they mention
   the profunctor-weighted-limit layer, dual colimits, join category, DefIso,
   and MathOps without burying the PathOut theorem.
2. Keep Sections 2-9 largely intact, but adjust the checked-computation prose
   to mention that the latest transitivity diagnostics use
   `hom_postcomp_fapp0(id,q,p)` as the runtime normal form while retaining a
   typed proof-time view against ordinary `comp_fapp0(q,p)`.
3. Replace the old one-section "Supporting Examples, Limitations, And Future
   Work" with a longer sequence:

   ```text
   10. Cat-valued profunctors and representables
   11. Tensor, co-Yoneda, and internal hom
   12. Weighted limits, adjunctions, and duality
   13. Directed-inductive join categories
   14. Equality, DefIso, and normalization boundaries
   15. Formal artifact and validation
   16. Conclusion
   ```

4. Add checked-normal-form summaries for:
   `Hom_prof_along`, `Prof_reindex`, `Prof_tensor_func`,
   `Prof_coyoneda_*`, `Prof_imply_*`, `WeightedLimit_cov`,
   `right_adjoint_preserves_weighted_limit_cov`, dual weighted colimits,
   `Join_cat`, `Op_prof`, and `DefIso`/`ProfComparison`.
5. Expand the identifier glossary with the new public names, but keep long
   expanded terms in prose or appendices rather than in the narrative.
6. Update limitations conservatively:
   no general coend/coinserter semantics for `Prof_tensor`; no semantic
   collage implementation for `Join_cat`; no generic dependent join
   eliminator; no complete bicategory/equipment coherence; no full weak
   omega-category semantics; Cat/Grpd univalence is a staged computational
   interface, not a completed semantics of all categories.
7. Update `tmp/EMAIL.md` in the same announcement style. It should still open
   with the directed dependent-hom/path-induction pitch, then say that the new
   draft also contains the checked profunctor, weighted-limit, duality, and
   join developments.

### Validation Plan

For this documentation-only pass:

```bash
EMDASH_TYPECHECK_TIMEOUT=60s make check
npm run validate:paper
npm run check:render
```

Run `make catalog` or `make health` only if the check catalog or health report
is edited or if validation reveals a stale generated artifact. No Lambdapi
source edits are planned in this pass.

## Print Pipeline Facts

The current print pipeline is documented in `print/AGENTS.md`.

- Full paper source: `print/public/index.md`.
- Short/conference variant: `print/public/index_0.md`.
- Renderer: `print/src/App.tsx`.
- Supported embedded artifacts: KaTeX, Mermaid, Vega-Lite, Arrowgram.
- Validation:

```bash
npm run validate:paper
npm run check:render
```

The validator auto-discovers `print/public/index*.md`, so a temporary
development variant such as `index_3_2.md` will be validated automatically.

## Recommended File Strategy

Use a staged paper migration rather than editing the old v2 text in place.

1. Draft the new long v3.2 article as:

   ```text
   print/public/index_3_2.md
   ```

   This keeps the old v2 article available for comparison while the v3.2 paper
   architecture is still being settled. Preview with:

   ```text
   /?paper=index_3_2.md
   ```

2. Once the long version is coherent and render-clean, promote it to:

   ```text
   print/public/index.md
   ```

3. Derive the short/conference version from the long version as:

   ```text
   print/public/index_0.md
   ```

4. Retire the v2 article sources to an ignored `.scratchpad/retired/...`
   folder at promotion time. Do not keep a legacy v2 paper under an `index*.md`
   name, because the validator treats those files as current paper variants.

## What To Reuse From The v2 Paper

Reusable:

- the opening motivation: coherence as computation, normalization as diagram
  chasing;
- the stable-head explanation, especially the distinction between rewrite
  rules and unification rules;
- the expository technique of showing kernel identifiers next to mathematical
  notation;
- Arrowgram figures for off-diagonal transformation components, after updating
  notation and labels;
- the implementation/evaluation section pattern: checked file, check command,
  diagnostics module, and limitations.

Retire or demote:

- v2-specific `Catd`, `Fibration_cov_catd`, `Total_cat`, `homd_int_base`,
  `StrictFunctor_cat`, and old `Product_catd` exposition as central material;
- old binder modes `x : A`, `x :^- A`, `x :^o A` as notation authorities;
- claims that the adjunction layer is merely a v2 draft with one incomplete
  triangle regression. In v3.2 ordinary adjunctions now have a first-class
  `Adjunction(R,L)` interface and checked left/right component-level triangle
  reductions, but this should be a supporting example rather than the main
  theorem;
- the old "February 9, 2026 snapshot" implementation section.

## Core Narrative Spine

The full article should start from the computation readers can understand, not
from all kernel foundations.

### 1. The Computation First

Open with the directed composition benchmark.

For `p : x ->^Z y` and `q : y ->^Z z`, path induction on the composition motive
produces:

```text
path_comp_func(p)[z][q] = q o p.
```

Then explain that this is not an isolated rewrite. It is the normal form of a
chain:

```text
PathOut_Z(x)
rho_{x,y,p}
PathInd_transfd(Z)
CompMotive_Z(x)
path_comp_sec(x)
path_comp_func(p)
q o p.
```

This should be the first mathematical diagram and the first major theorem.

### 2. Outgoing Arrows And The Canonical Rho Arrow

Define:

```text
PathOut_Z(x) = Σ y :^n Z, Hom_Z(x,y)
reflout_x    = (x,id_x)
```

Explain:

```text
rho_{x,y,p} : reflout_x ->^PathOut_Z(x) (y,p)
rho_{x,y,p} = sigma_transport_arrow(Rep_Z(x), p, id_x).
```

The article should emphasize that `rho` is constructed from existing Sigma and
representable computation, not postulated as a primitive induction path.

### 3. Fixed-Source Path Induction

State the fixed-source theorem:

```text
E : Catd(PathOut_Z(x))
u : E[reflout_x]

path_ind_sec(Z,x,E,u) : Π q :^n PathOut_Z(x), E[q]
```

and its computation:

```text
path_ind_sec(Z,x,E,u)[(y,p)] = E[rho_{x,y,p}](u).
```

In implementation terms:

```text
PathInd_func(Z,x)
  : E :^n Catd(PathOut_Z(x)) ; E[(x,id_x)] ⊢ Π q, E[q]
PathInd_func(Z,x)[E](u) = path_ind_sec(Z,x,E,u).
```

### 4. Varying-Source Telescope Theorem

State the primary v3.2 theorem as a displayed transformation:

```text
PathInd_transfd(Z)
  : x :^n Z ; PathOutReflEval_Z[x] => PathOutPi_Z[x]
```

where:

```text
PathOutReflEval_Z[x][E] = E[(x,id_x)]
PathOutPi_Z[x][E]       = Π q :^n PathOut_Z(x), E[q].
```

The article should stress that this telescope/displayed-transformation form is
primary. The Sigma-total form is derived:

```text
PathInd_funcd(Z) = Sigma_transfd_funcd(PathInd_transfd(Z)).
```

### 5. Transitivity/Composition As A Regression Theorem

Define:

```text
CompTarget_Z(x)[y] = Rep_Z(y) ⊢ Rep_Z(x)
CompMotive_Z(x)[(y,p)] = Rep_Z(y) ⊢ Rep_Z(x).
```

Then:

```text
path_comp_sec(x)
  = path_ind_sec(CompMotive_Z(x), id_Rep_Z(x))

path_comp_sec(x)[p] = path_comp_func(p)
path_comp_func(p)[z][q] = q o p.
```

The article should show both checked routes:

- through the primary telescope theorem `PathInd_transfd`;
- through the derived Sigma-total theorem `PathInd_funcd`.

Both routes should end in the same runtime hom-action normal form:

```text
hom_postcomp_fapp0 Z Z (id_func Z) x y z q p.
```

The article should also mention the typed ordinary-composition view
`comp_fapp0 Z x y z q p`, but only as the proof-time comparison surface, not
as the current runtime owner of the benchmark.

### 6. Syntax And Expressibility

Only after the theorem is visible should the paper introduce the new surface
syntax. The key table should be much shorter than the v2 table and use the
current canonical notation:

```text
a ->^C b
aa[z^-] ->_[z]^R bb[z]
A ⊢ B
z :^n Z ; E[z] ⊢ D[z]
Π (z :^n Z), D[z]
A[z^-] ⊢_[z] B[z]
F => G
FF[z^-] =>_[z] GG[z]
```

The nested telescope stress test should appear as an expressibility example:

```text
k :^n K ; C[k] ⊢ (z :^n Z ; E[k^-;z] ⊢ D[k;z])
```

This should be presented as evidence that v3.2 can express nested shaped
program categories, not as the main theorem.

### 7. Kernel Infrastructure, In The Order Needed By The Theorem

The foundations section should be dependency-driven:

1. `Grpd`, `Cat`, `Obj`, `Hom_cat`;
2. `Functor_cat`, `Transf_cat`, stable application heads;
3. `Catd_cat`, `Functord_cat`, `Transfd_cat`;
4. `Pi_cat`, `Sigma_cat`, `sigma_arrow`, `sigma_transport_arrow`;
5. `Functor_catd`, `Hom_catd`, `Transf_catd`;
6. representables `Rep_catd`, `PathOut_cat`, and path induction.

This should replace the v2 article's broad tour of older Grothendieck and
dependent-hom infrastructure.

### 8. Supporting Computational Examples

After the main theorem, include smaller examples that reinforce the same
kernel discipline:

- product-valued functors and product projections;
- semantic curry/uncurry object and capped hom-action checks;
- ordinary adjunctions as a cut-elimination example:

```text
counit[f] o left(unit[g]) -> f o left(g)
right(counit[g]) o unit[f] -> right(g) o f.
```

Adjunctions should be a sidebar or later section, not the lead narrative.

### 9. Implementation And Validation

Record:

```bash
timeout 60s lambdapi check -w emdash3_2.lp
timeout 60s lambdapi check -w emdash3_2_checks.lp
EMDASH_TYPECHECK_TIMEOUT=60s make check
npm run check:render
```

Explain the source split:

- `emdash3_2.lp` contains definitions and rewrite rules;
- `emdash3_2_checks.lp` contains executable assertions/regressions;
- `reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md` is the
  status/SOP authority;
- `reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md` is the
  notation authority.

### 10. Limitations And Deferred Work

Be explicit and conservative:

- structural functor logic is planned but not implemented;
- general dependent adjunctions `Σ_F ⊣ F^* ⊣ Π_F` remain future work;
- arbitrary Sigma-map transport is not strict without strict/cartesian
  specialization;
- whole-transfor displayed laxity is deferred;
- full product/curry adjunction coherence is future work;
- `section_total(s) : K ⊢ Σ_K E` is not yet a named presentation facade.

## Proposed Full Article Outline

```text
Title
  emdash v3.2: Synthetic Arrow Induction And Computational Composition

Abstract

1. Introduction
   1.1 Coherence as computation
   1.2 The v3.2 contribution
   1.3 What is checked

2. The Main Computation
   2.1 Outgoing-arrow category PathOut_Z(x)
   2.2 The canonical rho arrow
   2.3 Fixed-source path induction
   2.4 Composition/transitivity as the benchmark

3. The Telescope Theorem
   3.1 PathOutReflEval and PathOutPi
   3.2 PathInd_transfd as the primary theorem
   3.3 Sigma-total presentation as a derived form
   3.4 Source and target transport along moving x

4. The Surface Language
   4.1 Ordinary and indexed homs
   4.2 Shaped functor categories
   4.3 Section categories
   4.4 Mixed-variance families
   4.5 Nested telescope stress test

5. Kernel Foundations
   5.1 Categories, hom-categories, and omega iteration
   5.2 Functors and transfors
   5.3 Directed Cat-valued families
   5.4 Pi and Sigma categories
   5.5 Representables and PathOut

6. Computational Normalization Discipline
   6.1 Stable heads
   6.2 Rewriting versus unification
   6.3 Semantic owners before helper aliases
   6.4 Why diagnostics are in a separate checks file

7. Supporting Constructions
   7.1 Products and semantic curry/uncurry
   7.2 Sigma/Pi helper laws
   7.3 Ordinary adjunction cut-elimination

8. Implementation
   8.1 Files and validation commands
   8.2 The checked regression catalog
   8.3 Diagram and article pipeline

9. Limitations And Future Work

10. Conclusion

Appendix A. Identifier glossary
Appendix B. Selected checked normal forms
Appendix C. Diagram source notes
```

## Proposed Short Article Outline

The short/conference version should be derived after the long version
stabilizes.

```text
Abstract

1. Introduction
2. Synthetic Arrow Induction
3. Computational Composition
4. Surface Syntax And Kernel Architecture
5. Implementation And Checks
6. Limitations And Outlook

Appendix/compact table: identifiers and notation
```

The short version should omit most supporting products/curry/adjunction detail
unless needed as examples of the normalization style.

## Figure Plan

Use Arrowgram for category-theoretic diagrams and ordinary tables for syntax.

1. `PathOut_Z(x)` as a total category of outgoing arrows:
   nodes `x`, `y`, `z`; objects `(y,p)`, `(z,q)`.

2. The canonical `rho_{x,y,p}` arrow:

   ```text
   (x,id_x) -> (y,p)
   ```

   over base arrow `p : x -> y`, with the fibre identity folded by
   `Rep_Z(x)[p](id_x) = p`.

3. Motive transport:

   ```text
   E[(x,id_x)] --E[rho]--> E[(y,p)]
   ```

4. Telescope theorem:

   ```text
   PathOutReflEval_Z[x] => PathOutPi_Z[x]
   ```

   drawn as a displayed-transformation component over `x`.

5. Composition benchmark:

   ```text
   p : x -> y
   q : y -> z
   path_comp_func(p)[z][q] = q o p
   ```

6. Sigma-total derived form:

   ```text
   (x,E) -> (y,p_*E)
   ```

7. Nested syntax stress test as a typography/table figure, not necessarily a
   commutative diagram.

8. Optional later figure: ordinary adjunction triangle cut-elimination.

## Checked Normal Forms To Cite

The article should cite normal forms that are actually covered by
`emdash3_2_checks.lp`, in prose rather than line-number dependent references.

Core PathOut/rho checks:

```text
PathOut_transport_func(p)[(z,q)] = (z,q o p)
PathOut_transport_func(p)[reflout_y] = (y,p)
Rep_Z(x)[p](id_x) = p
pathout_refl_arrow(x,y,p) = sigma_transport_arrow(Rep_Z(x),p,id_x)
rho_{x,z,q o p} = PathOut_transport(p)(rho_{y,z,q}) o rho_{x,y,p}
```

Path induction checks:

```text
PathInd_func(Z,x)[E] = path_ind_func_fapp0(Z,x,E)
PathInd_func(Z,x)[E](u) = path_ind_sec(Z,x,E,u)
PathInd_transfd(Z)[x] = PathInd_func(Z,x)
PathInd_transfd(Z)[x][E](u) = path_ind_sec(Z,x,E,u)
PathInd_funcd(Z)[(x,E)] = path_ind_func_fapp0(Z,x,E)
```

Composition benchmark checks:

```text
path_ind_sec(CompMotive_Z(x), id_Rep_Z(x)) = path_comp_sec(x)
path_comp_sec(x)[p] = path_comp_func(p)
path_comp_func(p)[z][q] = q o p
```

The fully expanded telescope and Sigma-total benchmark checks should be quoted
as the main evidence:

```text
expanded(PathInd_transfd, CompMotive, p, q) = q o p
expanded(PathInd_funcd, CompMotive, p, q) = q o p
```

## Style Rules For The New Article

- Lead with one working computation before introducing all syntax.
- Use the current v3.2 notation authority; do not reintroduce old binder modes.
- Distinguish "implemented and checked" from "planned" or "deferred".
- Prefer mathematical names in prose and kernel identifiers in small code
  blocks or glossary tables.
- Keep code snippets short; use appendix for long normal forms.
- Use diagrams to explain objects and arrows, not to replace the checked
  computation statements.
- Avoid claiming full weak omega-category semantics. Say v3.2 provides a
  strict/lax omega-oriented internal language foundation with checked
  computational constructors.
- Avoid presenting `PathInd_funcd` as primitive. The primitive theorem is
  `PathInd_transfd`; the Sigma-total form is derived.

## Recommended Next Step

Create a new long-form workbench article:

```text
print/public/index_3_2.md
```

Start with only:

1. frontmatter;
2. abstract;
3. Section 1 introduction;
4. Section 2 "The Main Computation";
5. placeholder headings for the rest of the outline;
6. two initial Arrowgram diagrams: `PathOut_Z(x)` and `rho_{x,y,p}`.

Then run:

```bash
npm run validate:paper
npm run check:render
```

Only after this skeleton renders cleanly should the old v2 `index.md` be
replaced and the short `index_0.md` regenerated.
