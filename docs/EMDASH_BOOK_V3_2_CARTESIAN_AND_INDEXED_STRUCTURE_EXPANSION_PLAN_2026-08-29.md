# Emdash Book v3.2 Cartesian And Indexed Structure Expansion Plan

Date: 2026-08-29 (America/Toronto)

Plan-ID: `EMDASH-BOOK-CARTESIAN-INDEXED-STRUCTURE-EDITION-V0.7`

Status: **active implementation plan; mathematical prose and source registries
green, final deterministic release and visual QA in progress**.

Branch: `goal/emdash-book-categorical-structures-v3.2`

Worktree: `/home/user1/emdash1-book-categorical-structures-v3.2`

Baseline: `75a0b04`, the clean integrated checkpoint containing the completed
monad, triangular-product, terminal-object, pullback, whole-mate, functor
property-profile, and slice-dependent-product developments.

Last book-source checkpoint: `6180c41`, the dependent-simplex projection
exposition correction for the current `0.6.1-dev` edition.

Depends-On: active Lambdapi owners and focused reviewers; root, `emdash2`, and
print `AGENTS.md`; `emdash2/book/book.json`, `expansion.json`, `STYLE.md`,
`evidence.json`, `README.md`, and `RELEASE.md`; completed book plans through
the dependent-simplex edition; completed monad/product/terminal/pullback/
dependent-product plans; completed functor property-profile plan; current
Foundations, canonical syntax, and status/SOP.

Supersedes: no completed book plan. It extends the current five-spiral
`0.6.1-dev` edition with one sixth spiral and targeted corrections. It does not
reopen the central WalkingEnd theorem, rewrite the geometry or groupoidal
spirals, or supersede their completed editorial ledgers.

Side-Task-Ledger: `BCIS-00`, `BCIS-BASELINE-1`, `BCIS-ARCH-2`,
`BCIS-EVIDENCE-3`, `BCIS-CH9-4`, `BCIS-CH12-5`, `BCIS-CH30-6`,
`BCIS-LAX-7`, `BCIS-XCUT-8`, `BCIS-FORMAL-9`, `BCIS-RENDER-10`,
`BCIS-RELEASE-11`, and `BCIS-CLOSE-12`.

Infinity-Codex-Origin: session `01a02f68-6142-7e53-993a-4505aa8e2cbe`,
review response
`0039_2026-08-29T15-32-46Z_01a04e1a-db32-7d21-9f2e-3dd88e02fb24.md`
and the user's immediate approval, whole-mate promotion decision, and explicit
request to begin the book-update goal.

Infinity-Codex-Decision-Responses:
`infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a04e1a-db32-7d21-9f2e-3dd88e02fb24`
and the user's 2026-08-29 clarification and authorization immediately
following it.

## 1. Objective

Produce a globally coherent new development edition of *Functorial Type
Theory: Univalent Foundations for Mathematics* that explains the recently
completed computational categorical structures as mathematics rather than as
a release-note inventory.

The governing reader question is:

> How does the calculus of cuts grow from one adjunction into algebraic,
> cartesian, and indexed dependent structure while retaining whole higher
> action?

The checked answer has two movements.

First, an adjunction produces a monad whose whole extension and ambient
triangular cuts compute. Chosen binary products and a terminal object then
show the same introduction/elimination discipline at finite cartesian shape.

Second, those finite structures become indexed. Postcomposition in slices
gives `Σᵤ`; chosen pullbacks give `u*`; chosen dependent products give `Πᵤ`;
and the existing adjunction calculus supplies

```text
Σᵤ ⊣ u* ⊣ Πᵤ.
```

The primary deliverables are authoritative book source, synchronized evidence
and architecture registries, a checked local `0.7.0-dev` PDF, comprehensive
visual QA, and local promotion to the tracked book artifacts. The overview
article is outside this goal unless a concrete correctness issue is discovered
during shared-evidence checking.

## 2. Authority And Recovery Order

Use this order on every continuation:

1. active Lambdapi owners and focused reviewers at baseline `75a0b04`;
2. root, Lambdapi, and print `AGENTS.md` instructions;
3. current Foundations, canonical syntax, and status/SOP;
4. `book.json`, `expansion.json`, `STYLE.md`, `evidence.json`, provenance,
   and `RELEASE.md`;
5. this living plan and its decision/side-task ledgers;
6. completed implementation plans for the mathematics being presented;
7. completed book plans through the dependent-simplex edition;
8. pinned external references and provenance records; and
9. archived responses only as recovery evidence.

The book is exposition, never a mathematical authority. If prose and active
code differ, repair the prose and evidence record.

## 3. Git, Artifact, And Publication Boundary

The user authorizes:

- the dedicated branch and worktree named above;
- implementation under this living plan;
- bounded local checkpoint commits after green, synchronized tranches;
- deterministic assembly, browser rendering, PDF production, PDF inspection,
  and local promotion of the checked book pair; and
- a persistent goal delegating exact execution to this plan.

This authorization does not include:

- push, PR, tag, GitHub Pages deployment, Zenodo, or remote publication;
- amend, rebase, reset, squash, force push, or other history rewriting;
- deleting branches or worktrees;
- changing Lambdapi or TypeScript semantics for expository convenience; or
- expanding the overview article without a separately recorded need.

The PDF skill's required artifact-operation marker was run successfully once
before the first authored plan/source edit, with operation `edit`, one expected
PDF output, and format `pdf`.

## 4. Reviewed Baseline

### 4.1 Git and integration

The historical project worktree `/home/user1/emdash1` now has `main` at
`75a0b04`. The update from `9fe0683` was a clean seven-commit fast-forward.
All retained book branches are ancestors of this baseline:

- the original book branch;
- the groupoidal/final-maintenance branch;
- the dependent-simplex book branch; and
- the tracked front-page branch.

They are historical evidence, not viable continuation worktrees. This goal
uses a fresh worktree from the integrated `main` baseline.

### 4.2 Current book artifact

The current tracked book is:

```text
editionVersion: 0.6.1-dev
publicationDate: 2026-08-22
status: draft
ordered sources: 44
PDF pages: 355
page size: US Letter
tagged PDF: yes
```

Read-only Poppler review covered the title, contents, Chapter 28, Chapter 29,
the opening evidence table, and Appendix G. Typography, hierarchy, margins,
mathematics, tables, and page transitions are visually sound at this baseline.

### 4.3 Baseline checks

`book:typography` and strict KaTeX checking pass with 44 source files and
2,916 mathematical spans.

`book:check` currently fails for one exact post-integration reason:

```text
WHOLE-SLICE-AFFINE-REALIZATION
  owner slice_domain_func
  recorded in emdash3_2_commutative_algebra_ringed_space_restrictions.lp
  now owned by emdash3_2_presheaves.lp.
```

The symbol moved during the generic slice/pullback correction; the theorem and
consumer remain active. This is an evidence-provenance repair, not a
mathematical regression. It is the first edit and must be green before new
claims are added.

### 4.4 Delta since the last book source

The integrated baseline is 77 commits beyond the last book-source checkpoint
`6180c41`. The reader-facing delta includes:

- primary monad computation and adjunction-derived usability;
- enhanced triangular binary products;
- computational terminal objects and the thin cartesian package;
- chosen pullbacks as whole slice base change, including full Došen
  rectangles, whole/point mates, and guarded whole cancellation;
- chosen slice dependent products and `Σᵤ ⊣ u* ⊣ Πᵤ`;
- the functor property-profile migration used by Gray/cubical consumers; and
- documentation/evidence changes following those implementations.

The current book already contains the dependent-simplex chapter and a
substantial whole-laxity/Gray chapter. Those subjects require a stale-claim
audit, not duplicate chapters.

## 5. Editorial Thesis

The sixth spiral is governed by one principle:

> A universal property becomes computational when its introduction form,
> elimination form, and smaller-cut normal form remain visible together with
> their whole higher action.

Chapter 9 introduced that principle abstractly. Chapter 12 applied it to an
adjunction. The new material follows the principle through four increasingly
structured settings:

```text
adjunction
  → monad extension and triangular multiplication
  → binary and empty products
  → pullback reindexing in slices
  → dependent right adjoints and local cartesian structure.
```

The narrative should never begin with Lambdapi records. It begins with the
mathematical detour being eliminated, then explains why the implementation
retains a particular whole owner or stable projection.

The new spiral also clarifies three distinctions:

1. the product functor `P:C×C→C` is selected whole structure, not the kernel's
   product category constructor;
2. categorical pullback `u*` is not generic family substitution
   `Pullback_catd`; and
3. slice `Πᵤ:C/X→C/Y` is not `Pi_cat(E)` and not the separately proposed
   general right-Kan `Pi_along_func`.

## 6. Book Architecture

Use a hybrid architecture:

- repair false status claims where their original concepts live;
- extend Chapter 12 with the monad generated by an adjunction;
- add one sustained Chapter 30 for cartesian and indexed dependent structure;
- update cross-cutting front matter and appendices;
- audit Chapter 28 against the merged property-profile implementation, editing
  only genuinely stale prose/evidence; and
- preserve all existing chapter numbers and the completed five spirals.

### 6.1 Chapter 9 repair: structural cuts are now checked

Chapter 9.4 currently says that arbitrary chosen binary products and their
beta rules are future mathematical development. That statement is now false.

Rewrite the section so that:

- the general product/projection benchmark is motivated first;
- `BinaryProducts(C,P)` supplies a selected whole product functor;
- `K1a`, `K2a`, whole pairing, point pairing, beta, distribution, eta, and
  selected normalizations are checked;
- generic product-category computation remains a separate lower-level owner;
- the weighted-product adapter remains assumption-explicit; and
- no global free-cartesian decision procedure is claimed.

Add terminality as the empty-product structural cut only briefly; Chapter 30
owns the sustained development.

### 6.2 Chapter 12 extension: an adjunction generates a monad

Insert a subsection after the hom-transposition discussion, without disrupting
the existing chapter-level anchor or equivalence ladder.

The subsection should explain:

- `T=G∘F` and the adjunction unit as monad unit;
- multiplication as the transparent `G ε F` composite;
- Kleisli extension as the computational triangular operation;
- the two ambient cuts

  ```text
  g* ∘ η(f) → g ∘ f
  g* ∘ f* → (g* ∘ f)*;
  ```

- the standard multiplication component `μ_X → (id_TX)*`;
- the distinction between ambient Došen computation and the separately gated
  explicit Kleisli category; and
- the precise status of adjunction-derived unit/multiplication usability.

Do not introduce comonads as a parallel chapter or duplicate the implementation
history. A concise duality sentence is enough if needed for mathematical
orientation.

### 6.3 New Chapter 30: Cartesian Structure And Dependent Products

Add:

```text
book/chapters/30-cartesian-structure-and-dependent-products.md
```

with stable anchor `chapter-30` and provisional title:

> **30. Cartesian Structure And Dependent Products**

This is the sixth spiral. Its reader question is:

> How do finite cartesian structure and dependent substitution become one
> internal computational calculus?

The chapter's narrative order is:

1. **Chosen binary products as a whole functor.** Introduce
   `P:C×C→C`, whole projection transfors, and pairing as a represented-family
   operation.
2. **The triangular product cuts.** Present `K₁ᵃ`, `K₂ᵃ`, pairing beta,
   distribution through composition, eta/uniqueness, and the direct comparison
   between generic `P[(f,g)]` and the triangular map.
3. **The empty product.** Present one selected terminal object, the whole
   transformation `!:id_C⇒Const_t`, off-diagonal action, Hom contractibility,
   and derived uniqueness without a variable-headed rewrite.
4. **The thin cartesian package.** Explain that the package pairs existing
   product and terminal capabilities and adds no computation.
5. **Slices and the always-existing `Σᵤ`.** Build `C/X`, explain
   postcomposition, and distinguish internal slice arrows from manually stored
   commuting squares.
6. **Chosen pullbacks as base change.** Present
   `SliceBaseChange(PB):Cᵒᵖ→Cat`, exact fibres, `u*:C/Y→C/X`, and
   `Σᵤ⊣u*`.
7. **Rectangles, mates, and the pullback object.** Present actual unit/counit
   transfors, their `tapp1` `γᶜ`/`φᵃ` operations, both full rectangles,
   point and guarded whole mate cancellation, and derivation of the pullback
   object/projections/square from `u*(g)` and the counit.
8. **Dependent products in slices.** Introduce
   `SliceDependentProduct(DP):C→Cat`, `Πᵤ:C/X→C/Y`, and `u*⊣Πᵤ`.
9. **The three-adjoint chain.** Develop `Σᵤ⊣u*⊣Πᵤ`, the second pair of
   Došen rectangles, transparent whole mate functors, and generic whole Hom
   comparison.
10. **The local-cartesian boundary.** Explain the neutral
    `SliceDependentProducts(C)` package and why the stronger
    convention-sensitive LCCC name, derived slice exponentials,
    Beck–Chevalley, and Frobenius remain later layers.

Use diagrams only where they materially clarify the variance. One compact
three-arrow display should carry the chapter:

```text
C/X  --Σᵤ-->  C/Y
C/X  <--u*--  C/Y
C/X  --Πᵤ-->  C/Y

Σᵤ ⊣ u* ⊣ Πᵤ.
```

Do not draw or store a cone record. A cone is an object of
`Hom(C/Y;Σᵤa,g)`.

### 6.4 Chapter 16 cross-reference

Chapter 16 should retain weighted representability as the general semantic
framework. Update its terminal-weight specialization to say:

- selected binary products and terminal objects now have direct computational
  owners;
- a supplied weighted-product comparison relates the triangular product to
  the stronger `DefIso`-based weighted presentation; and
- automatic construction of that weighted witness remains absent.

Pullbacks and dependent products should link forward to Chapter 30 instead of
being implied by terminal weights alone.

### 6.5 Chapter 28 property-profile audit

Chapter 28 already presents strictness as `IsStrictFunctor` evidence over an
existing compositor and `StrictFunctor` as a Sigma package. Audit it against
the merged final owner:

- remove any remaining implication that primitive strict-functor codes are
  active;
- name `IsPseudoFunctor` as a fixed-forward property of the existing readable
  compositor when relevant;
- preserve the explicit warning that global strict cuts remain a later
  profile-local migration; and
- avoid duplicating the Gray/cubical chapter merely because the implementation
  was merged after the last book source checkpoint.

If the current prose and evidence are already exact, record a no-churn audit
in this plan rather than editing for novelty.

### 6.6 Front matter and appendices

Update:

- edition notice, preface, how-to-read, and generated contents for a sixth
  spiral and Chapter 30;
- Appendix A notation for `Σᵤ`, `u*`, `Πᵤ`, triangular pairing, and
  terminal arrows;
- Appendix D glossary/index entries and stable cross-links;
- Appendix E computation/equality-mode examples for body-unfolded unifiers and
  guarded whole cancellation;
- Appendix F status matrix and future boundaries;
- Appendix G mathematical and Lambdapi presentations for monads, products,
  terminality, pullbacks, and dependent products;
- `book.json`, `expansion.json`, and `evidence.json`; and
- release/version metadata.

Appendix B remains generated from `evidence.json`.

## 7. Exact Evidence Architecture

Repair the moved-owner row first, then add a small checked evidence set.

### 7.1 Baseline repair

`WHOLE-SLICE-AFFINE-REALIZATION` should name `slice_domain_func` in
`emdash3_2_presheaves.lp`, while retaining the existing downstream restriction
owner/reviewer. Do not change the mathematical statement.

### 7.2 New evidence claims

Add these stable IDs:

1. `MONAD-TRIANGULAR-COMPUTATION`
   - owners: `Monad`, `kleisli_extend_func`, `kleisli_extend_fapp0`, unit and
     multiplication observations in `emdash3_2_monads.lp`;
   - reviewer: `examples/monads_comonads.lp`, restricted in prose to the monad
     side.
2. `TRIANGULAR-BINARY-PRODUCTS`
   - owners: `BinaryProducts`, whole projection transfors, `K1a`, `K2a`, and
     pairing owners in `emdash3_2_triangular_binary_products.lp`;
   - reviewer: `examples/triangular_binary_products.lp`.
3. `TERMINAL-OBJECT-COMPUTATION`
   - owners: `TerminalObject`, whole terminal transfor, component/action, and
     Hom-contractibility owners in `emdash3_2_terminal_objects.lp`;
   - reviewer: `examples/terminal_objects.lp`.
4. `PULLBACK-SLICE-BASE-CHANGE`
   - owners: `PullbackStructure`, `SliceBaseChange_catd`, selected adjunction,
     `γᶜ`/`φᵃ`, whole mate, pullback object/projection/square owners in
     `emdash3_2_pullbacks.lp`;
   - reviewer: `examples/pullbacks.lp`.
5. `SLICE-DEPENDENT-PRODUCTS`
   - owners: `DependentProductStructure`, `SliceDependentProduct_catd`, second
     adjunction, `γΠᶜ`/`φΠᵃ`, semantic mate, and total package owners in
     `emdash3_2_slice_dependent_products.lp`;
   - reviewer: `examples/slice_dependent_products.lp`.

Chapter 30's central evidence is `SLICE-DEPENDENT-PRODUCTS`, with
`TRIANGULAR-BINARY-PRODUCTS`, `TERMINAL-OBJECT-COMPUTATION`, and
`PULLBACK-SLICE-BASE-CHANGE` as its prerequisite spine.

Chapter 12 consumes `MONAD-TRIANGULAR-COMPUTATION` as secondary evidence; its
central theorem remains the adjunction triangle calculus.

## 8. Exact Mathematical Boundaries

The prose must not claim:

- a free-monad syntax or global commuting decision procedure;
- an explicitly constructed Kleisli category unless a later owner is added;
- every category has products, a terminal object, pullbacks, or dependent
  products;
- that the kernel product category constructor is the selected product
  structure on an arbitrary category;
- automatic equivalence between triangular products and weighted products;
- a cone record or manually supplied commuting square for pullbacks;
- that the ambient higher pullback square is a strict equality;
- that `Pullback_catd` is categorical pullback;
- Beck–Chevalley, Frobenius, pushouts, or derived slice exponentials;
- that `SliceDependentProducts(C)` is already the final convention-sensitive
  LCCC package;
- that `Pi_cat`, `Pi_along_func`, and slice `Πᵤ` are the same operation;
- global confluence, normalization, decidability, or canonicity for the combined
  rewrite system; or
- completed global migration of historical strict functoriality cuts.

## 9. Cross-Cutting Consistency Audit

Search every authored source for now-stale statements including:

```text
binary products are not implemented
terminal objects remain future
arbitrary pullbacks are absent
dependent adjunctions remain entirely future
no computational monad
primitive strict-functor codes
ReadablePseudoFunctorProfile
```

Classify every hit as:

- repaired now;
- historical/contextually correct;
- a distinct unimplemented stronger theorem; or
- generated artifact text owned elsewhere.

Do not mechanically replace words. For example, arbitrary pullbacks now exist
only under `PB : PullbackStructure(C)`, while arbitrary pullback *existence*
without such structure remains false.

## 10. Version And Release Strategy

Select:

```text
editionVersion: 0.7.0-dev
publicationDate: 2026-08-29
status: draft
```

This is a minor development-edition increment because it adds a complete new
spiral and chapter while preserving the central theorem and publication
status.

The final local artifact path is manifest-owned:

```text
output/pdf/functorial-type-theory-0.7.0-dev.pdf
```

After the full local release and visual gate pass, `book:promote` may update:

```text
docs/emdash-book.md
docs/emdash-book.pdf.
```

No remote publication is authorized.

## 11. Visual And Prose Quality Plan

### 11.1 Prose review

For every edited chapter:

- lead with the mathematical problem and the reduction being performed;
- keep implementation names in compact status notes;
- define every symbol before use;
- ensure equation orientations agree with active rewrite rules;
- state variance explicitly at every slice transition;
- make chapter transitions and backward/forward links read naturally;
- remove duplicated exposition; and
- read the assembled chapter continuously, not only as patches.

### 11.2 Render review

After each meaningful source tranche:

```bash
./scripts/pnpmw run book:assemble
./scripts/pnpmw run book:typography
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
```

At the final artifact boundary run:

```bash
./scripts/pnpmw run book:release
```

Render the final PDF with Poppler and inspect at least:

- title and edition metadata;
- all contents pages;
- first and last page of Chapter 12;
- every page of new Chapter 30;
- Chapter 28's edited/profile-audited pages;
- the evidence table rows for all five new IDs;
- notation, status, computation, and formal-presentation appendix pages;
- bibliography, credits, and license;
- any page containing a wide table or long displayed formula; and
- every page flagged by overflow, replacement-character, font, or blank-page
  diagnostics.

Require zero clipped text, overlaps, malformed math, black boxes, broken links,
unreadable tables, replacement glyphs, or inconsistent heading hierarchy.

Generate the final PDF twice from clean generated state and require identical
SHA-256 checksums before promotion.

## 12. Proportional Validation Policy

### Plan/evidence repairs

- exact diff review;
- book evidence checker;
- source assembly/check;
- typography and strict KaTeX;
- no browser/PDF run until prose architecture is stable.

### Each prose tranche

- `book:assemble`;
- `book:typography`;
- `book:check`;
- targeted source/evidence searches;
- `book:render` after chapter-level completion.

### Final local release

- clean generated state;
- `book:release` twice;
- deterministic checksum comparison;
- Poppler metadata/text/font checks;
- page-image visual QA;
- exact tracked promotion diff;
- no unrelated kernel, TypeScript, article, or repository-wide aggregate unless
  a concrete cross-layer issue requires it.

## 13. Execution Ledger

| ID | State | Deliverable |
| --- | --- | --- |
| `BCIS-00` | complete | Fast-forwarded clean historical `main` to `75a0b04`; created and bootstrapped the dedicated branch/worktree. All old book branches are ancestors and remain untouched. |
| `BCIS-BASELINE-1` | complete diagnosis | Current `0.6.1-dev` artifact is 355 pages/44 sources and visually sound at representative pages. Typography/KaTeX pass. `book:check` exposes one moved-owner evidence regression for `WHOLE-SLICE-AFFINE-REALIZATION`; no prose or renderer failure is hidden. |
| `BCIS-ARCH-2` | complete design | Selected Chapter 12 monad insertion, one new Chapter 30 sixth spiral, targeted Chapter 9/16 repairs, Chapter 28 no-churn-first profile audit, and cross-cutting appendix/front-matter updates. |
| `BCIS-EVIDENCE-3` | complete | Repaired the moved `slice_domain_func` owner and added five checked evidence claims. The evidence gate resolves all 164 cited owners/reviewers. |
| `BCIS-CH9-4` | complete | Replaced the stale future-product claim with the checked triangular product and terminal boundary while preserving generic product-category computation as a distinct layer. |
| `BCIS-CH12-5` | complete | Added the adjunction-generated monad, ambient Došen cuts, multiplication-component bridge, and explicit free-syntax/Kleisli-category nonclaims. |
| `BCIS-CH30-6` | complete prose | Added the sustained sixth-spiral chapter from chosen binary/empty products through slices, pullback base change, mates, and `Sigma_u |- u* |- Pi_u`. |
| `BCIS-LAX-7` | complete audited profile | Chapter 28 already states the final property/evidence architecture. Its closing transition now reaches the sixth spiral; the stale decoded-code summary in Chapter 14 and matching appendix descriptions now use the active `IsStrictFunctor` property and exact functor/evidence package. |
| `BCIS-XCUT-8` | complete source synchronization | Synchronized the prologue, front matter, Chapter 16, Chapter 28/29 transitions, notation, glossary, computation, status, formal presentation, credits, architecture, version metadata, links, and the report map. |
| `BCIS-FORMAL-9` | complete source gate | Assembly, typography, strict KaTeX, evidence, source-order, anchor, and link checks pass with 45 ordered sources, 3,091 math spans, 164/164 evidence citations, and source fingerprint `578b85cc8d586b1677ec4335148adeb443057d24`. The stale-claim search leaves no false authored-source hit. |
| `BCIS-RENDER-10` | complete development render | Browser pagination completed at 374 US-Letter pages with zero console, page, request, or render errors. Final-PDF Poppler review remains owned by `BCIS-RELEASE-11`. |
| `BCIS-RELEASE-11` | pending | Produce two deterministic `0.7.0-dev` PDFs, complete structural/font/text/visual QA, and locally promote the checked pair. |
| `BCIS-CLOSE-12` | pending | Synchronize this ledger, exact diff, checksums, page count, source/evidence/math counts, and local checkpoint history. |

## 14. Decision Ledger

| ID | State | Decision |
| --- | --- | --- |
| `D-BCIS-001` | accepted | New material is a sixth conceptual spiral, not a module changelog. |
| `D-BCIS-002` | accepted | Monads extend Chapter 12 because they are generated by the adjunction calculus. |
| `D-BCIS-003` | accepted | Products, terminality, pullbacks, and dependent products form one sustained Chapter 30 because finite cartesian structure becomes indexed through slices. |
| `D-BCIS-004` | accepted | Chapter 9's stale future-product status is a correctness repair, while Chapter 30 owns the full exposition. |
| `D-BCIS-005` | accepted | Weighted products remain a comparison layer, not the definition of the triangular product interface. |
| `D-BCIS-006` | accepted | Pullback cones are Hom objects; no manual square record appears in prose or diagrams. |
| `D-BCIS-007` | accepted | `SliceDependentProducts(C)` is the neutral checked total; the stronger LCCC name remains a boundary. |
| `D-BCIS-008` | accepted | Chapter 28 receives a no-churn-first property-profile audit because much of the merged work is already correctly present. |
| `D-BCIS-009` | accepted | The new edition is `0.7.0-dev`, book-only, locally releasable/promotable, and not remotely publishable under this goal. |
| `D-BCIS-010` | accepted | Generated Markdown and PDFs are never hand-edited; visual QA uses the final generated PDF and Poppler page images. |

## 15. Acceptance And Stop Conditions

The goal is complete only when:

- the baseline evidence regression is repaired;
- all five new evidence IDs resolve to active owners and focused reviewers;
- Chapter 9 no longer understates chosen products/terminality;
- Chapter 12 accurately presents adjunction-generated monad computation;
- Chapter 30 forms one coherent mathematical narrative through
  `Σᵤ⊣u*⊣Πᵤ`;
- Chapter 28 is verified against the final property-profile owners;
- every stale-status search result is classified;
- front matter, architecture, notation, glossary, evidence, status,
  computation, and formal-presentation sources agree;
- the local book checks and browser render pass;
- two clean PDF releases have identical checksums;
- complete representative visual QA finds zero defects;
- the checked `0.7.0-dev` book is locally promoted to tracked docs artifacts;
- this ledger records exact sources, claims, math spans, pages, checksum, and
  validation results; and
- no unrequested article, remote publication, or mathematical implementation
  change occurs.

If a checked mathematical statement cannot be supported by active evidence,
downgrade its status or stop that section. Never add kernel rules merely to
make book prose stronger.

## 16. Persistent-Goal Launch Prompt

> Continue the Emdash book Cartesian/indexed-structure expansion in
> `/home/user1/emdash1-book-categorical-structures-v3.2` on branch
> `goal/emdash-book-categorical-structures-v3.2`, delegating exact architecture,
> source ownership, evidence, status labels, sequencing, validation, artifact
> handling, Git discipline, and stop conditions to
> `docs/EMDASH_BOOK_V3_2_CARTESIAN_AND_INDEXED_STRUCTURE_EXPANSION_PLAN_2026-08-29.md`.
> Begin from integrated baseline `75a0b04`. Preserve the first five spirals and
> the WalkingEnd theorem; repair the moved slice evidence owner first; extend
> Chapter 12 with adjunction-generated monad computation; repair Chapter 9's
> stale product boundary; add one Chapter 30 sixth spiral from triangular
> products and terminality through pullbacks and `Σᵤ⊣u*⊣Πᵤ`; audit Chapter
> 28 against the final property-profile owners; and synchronize all front
> matter, registries, appendices, version metadata, and cross-links. Follow the
> book style/evidence contract, use active code rather than reports as
> mathematical authority, keep implementation names in compact status notes,
> and preserve exact nonclaims. Run proportional source checks during
> authoring, then two deterministic local `0.7.0-dev` releases, complete
> Poppler visual QA, and local book promotion. Local green checkpoint commits
> are authorized; remote publication, article expansion, history rewriting,
> branch cleanup, and mathematical implementation changes are not.
