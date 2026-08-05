# Emdash Book v3.2 Post-Integration Expansion Plan

Date: 2026-08-04
Status: complete; final local artifacts promoted and review worktree retained
Branch: `goal/emdash-book-v3.2`
Worktree: `/home/user1/emdash1-book-v3.2`
Baseline: `62e9e1009b8f3ccb25c8e8cbf39a1ec68433a363` (`main` at launch)

## 1. Objective

Expand *Functorial Type Theory: Univalent Foundations for Mathematics* from
its July 30 development edition into a coherent post-integration edition that
explains the new mathematics as mathematics. The primary new arc runs from
presheaves and sieves, through sites, descent, and a direct categorical-HIT
sheafification, to constructive commutative algebra, affine schemes,
site-relative schemes, and the supplied projective-line boundary.

The book must not become a module catalogue, checkpoint history, test report,
or contributor manual. Its organizing questions are instead:

1. How can an object be studied through all arrows into it?
2. Which families of local tests count as covers?
3. When do compatible local data determine global data?
4. Can sheafification itself be presented as a computing universal
   construction?
5. How does localization turn invertibility into geometry?
6. How do affine charts and their inherited overlaps present a scheme?
7. What has actually been constructed for the projective line, and what
   remains to construct for projective space?

The concise overview article in `docs/emdash3_2.md` is a secondary deliverable.
Repository, kernel-report, and MathOps maintenance is a supporting lane only
where it removes stale public claims, restores ownership, or is required by
the book and article gates.

This document is the one active control document for the goal. Update it when
a source review changes an editorial decision, a tranche advances, a check
changes state, or a proposed claim proves stronger or weaker than its active
owner.

## 2. Authority And Recovery Order

Use the following order on every continuation:

1. root, nested Lambdapi, and print `AGENTS.md` instructions;
2. active Lambdapi owners and their checked examples;
3. the current SOP, Foundations, and canonical-syntax report;
4. `emdash2/book/book.json`, `expansion.json`, `STYLE.md`, `evidence.json`,
   and the provenance ledger;
5. this living plan;
6. completed PSSS, computational-schemes, elaborator, adjunction-usability,
   record-usability, browser, and publication plans as implementation history;
7. cited third-party mathematics and the user's sieve-centered review; and
8. raw archived responses only when this plan explicitly links one.

Book prose is never a mathematical authority. If the book and an active owner
disagree, correct the book and its evidence metadata.

## 3. Authorization And Git Boundary

The user explicitly authorized a new branch and worktree from current `main`,
the book and article changes, generated public PDF refreshes, and a persistent
goal. That authorization has been implemented as the branch/worktree named in
the header.

No commit authorization was given. Until the user expands the boundary:

- keep changes uncommitted in this worktree;
- do not push, merge, publish, release remotely, create a PR, tag, rebase,
  amend, reset, squash, delete branches, or remove worktrees;
- local deterministic PDF generation and checked promotion to the tracked
  `docs/` distribution paths are in scope because those artifacts are explicit
  deliverables;
- `book:release` and `article:release` mean local reproducible artifact gates,
  not a remote publication; and
- preserve all unrelated worktrees and ignored evidence.

## 4. Reviewed Baseline

### 4.1 Repository and artifact state

- The launch worktree was clean at integrated `main` commit `62e9e10`.
- The previous authored-book checkpoint is `4387065` from 2026-07-30.
- The tracked July 30 book PDF is version `0.3.0-dev`, 199 pages.
- The integrated authored source already contains a small August 1
  presheaf/sieve/site addendum in Chapter 13 and renders to 201 pages.
  Consequently, the tracked PDF was already two pages behind current source
  before this goal began.
- The concise article is version `0.1.0-dev`, 15 pages, and remains centered
  on directed dependency and the TypeScript elaborator.
- `book:check` and `book:render` are green at baseline. The current-source
  render reports 201 pages with no console, page, request, overflow, link,
  math, or accessibility failures.
- The current book has 17 numbered chapters. Chapter 13 contains only a
  compact, implementation-shaped preview of the earliest presheaf, sieve, and
  topology work. It has no sustained local-to-global narrative.
- The current source checker encodes the completed 1-8 and 9-17 expansion
  shape explicitly. Adding chapters therefore requires a small owned schema
  generalization, not a bypass of the architecture contract.

### 4.2 Post-book work inventory

Since `4387065`, the integrated tree changes 337 paths and adds approximately
158,000 lines. That raw scale must not determine the book's size or chapter
count. The reader-facing classification is:

| Work family | Reader-facing mathematical content | Book destination | Excluded detail |
| --- | --- | --- | --- |
| Presheaves, Yoneda, slices, higher sieves | Objects studied through all probes; Cat-valued coefficient systems over slices | Chapters 13 and 18 | facade heads, warning counts, unifier history |
| Ordinary sieves and sites | Subterminal local questions, pullback, maximality, stability, local character, generated topologies | Chapters 18-19 | evidence-package eta and phase IDs |
| Direct cover completion | matching, restriction, glue, silent, recursor, locality, Hom universality, Cat-valued reflector | Chapters 19-20 | projection ladders and critical-pair ledgers |
| Commutative algebra | set-carrier rings, structured maps, polynomial and localization universal properties, finite covers | Chapter 21 | per-module API inventory |
| Sieve-valued invertibility | `D_U(s)` as all arrows along which the restricted section is a unit | Chapters 18 and 22 | internal helper names except in status notes |
| Affine geometry | functor of points, represented basic opens, intersections, big Zariski topology, coordinate presheaf | Chapter 22 | checkpoint chronology |
| Schemes by covers | global-first site-relative scheme presentations, selected affine generators, inherited restrictions and overlaps | Chapter 23 | claims of representation independence or classical equivalence |
| Laurent overlap and supplied projective line | actual chart intersection with coordinate inversion | Chapter 24 | any claim that `Proj`, a global object, or non-affineness was constructed |
| Adjunction and record usability | concise authoring presentations for already-selected mathematics | Appendix G and compact Chapter 12 cross-reference | macro implementation internals |
| TypeScript binders, variables, text adapter | readable bound variables compile to explicit Core under checked profiles | Chapters 2/9 only where mathematically illuminating; principally Appendix G | tranche chronology, digests, test matrices |
| Browser reviewer | a reader can inspect source, Core, type, and computation client-side | reading guide and Appendix G | bundler and deployment internals |
| DevOps and MathOps | reproducible evidence and artifact ownership | Appendices B/E/F and repository docs only | CI transcript in main prose |

### 4.3 Mathematical non-claims inherited from the active owners

The edition must keep the following distinctions visible:

- a higher sieve is Cat-valued descent data, not automatically an ordinary
  proposition-valued sieve;
- a Grothendieck topology is separate from a presentation by generating cover
  families and from a sheafification reflector;
- the constructed direct-cover reflector currently realizes the Cat-valued
  sheaf facade; CommRing-valued lifting and left exactness remain deferred;
- a localization is presented by a universal property, not by a chosen
  fraction syntax;
- `D_U(s)` need not be represented by one open object on a general site;
- the active affine and scheme interfaces are assumption-explicit and
  computational;
- the general scheme package is site-relative, not yet Zeuner's functorial
  qcqs-scheme, a classical locally ringed space, or a representation-independent
  semantic category of schemes;
- the projective-line module packages a supplied global scheme and its actual
  Laurent overlap; it does not construct `Proj`, standard `P^n`, or
  non-affineness; and
- successful checking does not establish global normalization, confluence,
  canonicity, consistency, decidability, or semantic soundness.

## 5. Editorial Thesis

The new part of the book is a third spiral, **local-to-global geometry**.
Its governing sentence is:

> Geometry begins with probes. For a section `s` over `U`, the natural
> invertibility locus is the sieve `D_U(s)` of every arrow into `U` along which
> `s` becomes a unit.

This viewpoint relates, but does not confuse, two presentations.

1. In Zeuner's coherent/qcqs setting, an invertibility support may be
   represented by a largest compact open below `U`.
2. On a general site, the sieve of all invertibility probes is the primary
   object and may have no single representing open.
3. In a higher setting, a Cat-valued higher sieve may retain witnesses and
   coherence before ordinary subterminality is imposed.

The book must present the sieve-valued construction as a generalization, not
as a claim that Zeuner's compact-open definition is invalid. The interesting
comparison question is when the sieve is representable by a compact open.

The second governing insight concerns computation. Emdash does not need a
separate abstract modal object language in order to make local-to-global
semantics operational. Actual presheaves, sieves, sites, matching families,
and sheafification are expressed as categorical objects and functors in the
inner functorial type theory. The outer Lambdapi or TypeScript dependent LF
supplies rewrite, comparison, and unification machinery. Thus categorical
semantics itself becomes sufficiently internal and computational for the
checked development. This is a relative internality claim, not a denial that
modal internal languages can be useful.

## 6. Source And Attribution Strategy

### 6.1 Max Zeuner

Use Max Zeuner, *Univalent Foundations of Constructive Algebraic Geometry*,
arXiv:2407.17362v1, as a principal expository source for the constructive
algebraic-geometry arc. The official arXiv record identifies the work as
CC BY 4.0, so attributed adaptation is permitted.

Before adapted prose is added:

- register the exact arXiv version, license, section map, adaptation IDs, and
  targets in `book/references/third-party-sources.json`;
- add the full bibliography and credits entries;
- mark close adaptations as adapted and explain the sieve-valued change;
- prefer fresh prose whenever the book's architecture differs materially;
  and
- never import Zeuner's final comparison theorem as a checked emdash result.

The highest-value source map is:

| Zeuner section | Use in this book |
| --- | --- |
| 2.2, Zariski lattice | constructive motivation and basic-open algebra |
| 3.1, locally ringed lattices | contrast compact-open support with sieve-valued support |
| 3.2-3.3, spectrum and spectral schemes | mathematical-development background for affine and qcqs geometry |
| 4.1, Zariski coverage | cover families, locality, and functorial viewpoint |
| 4.2-4.3, compact opens and open subschemes | representation question for `D_U(s)` |
| 5, comparison theorem | research horizon only; not an implemented theorem |
| 6, finite presentation | later research orientation, not part of the first checked edition |

### 6.2 Sheafification sources

- Pierre-Marie Pedrot, *Pursuing Shtuck*, is CC BY 4.0 and is the closest
  source for the computational `return/glue/silent` intuition. Register any
  adapted passage before use.
- Pedrot, *Debunking Sheaves*, and Quirin-Tabareau,
  *Lawvere-Tierney sheafification in Homotopy Type Theory*, are reference
  sources unless a separately verified reuse license permits more. Use fresh
  prose for their conceptual comparisons.
- The book's distinctive presentation stays categorical: it explains the
  direct cover completion in actual presheaf, sieve, matching, and section
  semantics rather than replacing those objects by an abstract modality.

### 6.3 HoTT Book continuity

Keep the existing HoTT-inspired theorem-led method, formal-status system, and
adaptation ledger. The new geometry chapters should resemble the HoTT Book in
pedagogy - question first, examples before abstraction, universal properties
before implementation - without pretending that the HoTT Book contains this
algebraic-geometry development.

## 7. Target Book Architecture

The existing first two spirals remain:

1. Chapters 1-8: foundations through the WalkingEnd/Nat calculation.
2. Chapters 9-17: cuts, category theory, representability, universal
   constructions, duality, and join.

Add the following third spiral. These titles are selected but may receive
minor copy edits before their source file is first created.

### Chapter 18 - Presheaves And Sieves

Reader question: what information is visible when an object is tested by
every arrow into it?

Narrative:

- presheaves as coherent fields of views;
- representables and the Yoneda bridge from Chapter 13;
- the restriction-oriented arrow total and conventional slice;
- higher sieves as Cat-valued coefficient systems;
- ordinary sieves as the subterminal specialization;
- pullback and membership; and
- the first appearance of `D_U(s)` as an invertibility sieve.

Central checked claim: the active presheaf/Yoneda/slice construction and the
ordinary-sieve specialization retain whole pullback action.

Target length: 2,800-3,800 words.

### Chapter 19 - Sites, Covers, And Descent

Reader question: which local tests are sufficient to determine a global
object?

Narrative:

- maximality, pullback stability, and local character;
- cover families versus the covering sieves they generate;
- witness-rich generated topologies;
- matching families and restriction;
- topology-local presheaves as Hom equivalences; and
- sheaves as a local-to-global property, separate from sheafification.

Central checked claim: ordinary-sieve Grothendieck topologies and the
internally generated least accepting topology are active.

Target length: 3,200-4,200 words.

### Chapter 20 - Sheafification By Cover Completion

Reader question: can one freely add coherent solutions to every covering
question and retain a universal property?

Narrative:

- eligible cover questions;
- matching and section categories;
- `return`, whole `glue`, and `silent` as a categorical-HIT signature;
- recursion and glue preservation;
- the second inverse and conventional locality;
- whole Hom universality;
- assembly of the Cat-valued reflector and adjunction; and
- comparison with modal/internal presentations.

Central checked claim: for the selected fixed site and Cat-valued presheaves,
the direct cover completion has the whole Hom universal property into local
targets and instantiates the existing sheafification capability.

Target length: 3,500-4,800 words.

### Chapter 21 - Commutative Algebra By Universal Property

Reader question: which algebraic constructions remain computational without
choosing quotient or fraction syntax?

Narrative:

- commutative rings with set-valued carriers;
- structured maps and their category;
- products, the zero ring, and the two-element ring;
- finite unimodular families as cover data;
- polynomial algebras by free extension; and
- localization by contractible factorization, including unit, zero,
  idempotent, and iterated/product comparisons.

Central checked claim: one-element localization is characterized by a
contractible factorization space, and selected comparison maps satisfy whole
cancellation laws.

Target length: 3,500-4,800 words.

### Chapter 22 - Affine Geometry And The Sieve `D(f)`

Reader question: how does algebraic invertibility become a geometric basic
open?

Narrative:

- the affine functor of points;
- `D(f)` as the sieve of maps making `f` invertible;
- pointwise representation by `R[1/f]`;
- `D(fg)` as the intersection of `D(f)` and `D(g)`;
- the big affine slice and coordinate presheaf;
- the generated big Zariski topology;
- assumption-explicit structure sheaf and localization locality; and
- the thin computational affine-scheme presentation.

Central checked claim:

$$
D(f)(S) \simeq \operatorname{Hom}_{\mathrm{CommRing}}(R[1/f],S)
$$

for every selected localization and test ring, with both maps and inverse
laws constructed from the localization universal property.

Target length: 4,200-5,600 words.

### Chapter 23 - Schemes From Covering Charts

Reader question: what data must be supplied once a global object is already
present, and which overlap laws should be derived rather than restated?

Narrative:

- global-first versus atlas-first construction;
- one covering sieve with two selected affine generators;
- topology-local local-ring forcing;
- whole slice restrictions and affine-basis realizations;
- the binary site-relative scheme total;
- actual chart intersections derived from the global object; and
- the boundary between site-relative schemes and Zeuner's functorial qcqs
  comparison.

Central checked claim: a supplied global reflective ringed object, local-ring
certificate, constructively generated binary cover, and two affine
realizations form one site-relative computational scheme presentation whose
whole restrictions are inherited from existing owners.

Target length: 3,500-4,800 words.

### Chapter 24 - The Projective Line And The Boundary Of Construction

Reader question: how far can the existing cover-and-overlap machinery reach
without a general gluing theorem or `Proj` construction?

Narrative:

- two affine-line charts;
- their actual inherited intersection;
- Laurent coordinates and inversion on the overlap;
- the checked supplied projective-line presentation;
- what would be required to construct the global object rather than accept
  it; and
- graded rings, `Proj`, standard projective space, and non-affineness as
  explicit research boundaries.

Central checked conditional claim: once the global binary site-relative
scheme and actual chart intersection are supplied, the existing Laurent
owner packages the two coordinate-inversion maps on that inherited overlap.

Target length: 2,600-3,600 words.

The projected addition is approximately 23,000-32,000 words. Editorial
quality, dependency, and truthful status outrank hitting a word count.

## 8. Cross-Cutting Reconciliation

### 8.1 Existing chapters

- Revise Chapter 13.1 so it introduces presheaves and points forward to the
  third spiral instead of embedding a compact implementation-status report.
- Add only the mathematical cross-references needed from Chapters 12, 16,
  and 17 to the later adjunction, representability, and cover-completion
  applications.
- Avoid rewriting Chapters 1-17 merely to make the new material look
  retroactively inevitable.

### 8.2 Front matter and navigation

- Update the preface from two spirals to three.
- Add algebraic geometer and local-to-global reading paths.
- Keep the reviewer path concise; the browser is a way to inspect evidence,
  not the book's subject.
- Let generated contents own the complete chapter list.

### 8.3 Formal presentation and usability work

Appendix G remains the owner for the renewed TypeScript surface:

- summarize ordinary, natural, displayed-functorial, and displayed-natural
  binders through one mathematical running example;
- explain dependency transitions and independent siblings without listing
  compiler tranches;
- record the bounded text adapter and source-located failure boundary;
- add the direct TypeScript adjunction and structure declarations as
  elaboration conveniences that expand into ordinary explicit LF owners;
- state that neither macro adds a trusted Core node or Lambdapi semantic
  owner; and
- update the browser-reviewer paragraph to the current recursive section
  example.

Main mathematical chapters may use the convenient notation, but must not
organize their proofs around the TypeScript implementation.

### 8.4 Evidence and status appendices

- Add compact evidence claims for each new chapter's central theorem and only
  the secondary claims actually cited.
- Update the status matrix by mathematical capability, not module filename.
- Add new glossary entries for presheaf, higher sieve, ordinary sieve, site,
  cover, matching family, sheaf, sheafification, localization, basic open,
  affine scheme, and site-relative scheme.
- Keep raw check counts, warnings, health snapshots, and command transcripts
  out of the book.

## 9. Article Strategy

The overview article should remain concise and should not duplicate the seven
new chapters. After the book's central geometry claims stabilize:

1. revise the abstract so the executable architecture has one substantial
   mathematical application beyond WalkingEnd and binders;
2. add one section, approximately 1,200-1,800 words, centered on the chain

   ```text
   presheaf -> invertibility sieve D(f) -> localization -> affine chart
   ```

3. add a shorter paragraph on direct cover completion and the Cat-valued
   reflector;
4. keep detailed scheme and projective-line material in the book;
5. update the article evidence, references, metadata, page budget, and
   tracked PDF through the existing owner; and
6. preserve the article's two-column readability and concise role.

The likely article version is `0.2.0-dev`; the likely book version is
`0.4.0-dev`. Metadata changes occur only after the new source architecture is
stable.

`ARTICLE-02` began after the book claims stabilized. The unchanged 1,145-line
article passes its registry, paper, build, and browser-render baseline at 15
pages with no console, page, request, or render errors. Its current argument
is strong on synthetic arrow induction and binder compilation but predates
the local-to-global arc. It also retains three now-stale product-boundary
statements: ten rather than twelve reviewer examples, arbitrary displayed
depth rather than finite canonical dependency levels and sibling groups, and
an architecture diagram with no outer-LF declaration-expansion branch.

The bounded article architecture is therefore:

1. retain the title and the synthetic-arrow-induction spine;
2. revise the abstract and introduction so the second mathematical payoff is
   sieve-centered local geometry, not a catalogue of later modules;
3. correct the TypeScript architecture and boundary in place, including the
   four binder modes, finite canonical dependency depth, qualified finite Hom
   recursion, finite rigid section chains, twelve source presets, and the
   bounded adjunction/structure declaration conveniences;
4. replace the old broad-programme Section 8 with a 1,200-1,800-word argument
   in three movements: probes and $D_R(f)$; localization representation and
   finite Zariski generation; direct cover completion and its Cat-valued
   reflector;
5. end that section with only a compact assumption-explicit affine,
   site-relative scheme, and supplied-projective-line boundary; detailed
   schemes and Laurent calculations remain in the book;
6. retain the most important profunctor, weighted-universal, groupoidal, and
   WalkingEnd context as a short bridge rather than a second survey; and
7. update research boundaries, conclusion, and references before measuring
   the result. The existing 14-18-page budget remains authoritative unless
   the finished argument, not a layout defect, demonstrates otherwise.

This design keeps the article an account of two representative computations:
directed induction turns the canonical outgoing-arrow transport into
composition, while sieve-centered geometry turns invertibility under probes
into a representable local question and then a computing Cat-valued
sheafification. It does not compress Chapters 18-24 into a feature list.

`ARTICLE-02` is complete at the canonical authored owner
`emdash2/print/public/emdash-v3-2-overview.md`. The finished 1,362-line,
8,693-word article retains its arrow-induction spine, gives the abstract three
representative computations, corrects the current TypeScript and outer-LF
boundary, and adds a 1,321-word sieve-centered Section 8. Scheme and
projective-line claims remain compact and assumption-explicit; the article
does not reproduce the seven new book chapters. Its deterministic local PDF
has 17 pages within the unchanged 14-18-page budget. Metadata and tracked
distribution promotion remain release work.

## 10. Supporting Repository Maintenance

Maintenance is dependency-driven, not an invitation to rewrite every report.

### Required or likely

- add this plan to `emdash2/reports/INDEX.md` as the active cross-layer book
  goal;
- reconcile the integration plan's stale pre-fast-forward status with the
  actual `62e9e10` merged main boundary;
- revise root `README.md` so the reader-facing mathematical scope includes
  presheaves, sheafification, and constructive algebraic geometry without
  becoming a module list;
- replace the long module catalogue in `emdash2/README.md` with a grouped
  mathematical route while preserving precise authority links;
- update Foundations, canonical syntax, and the current SOP only where book
  claims expose missing or stale mathematical/notation/workflow summaries;
  and
- update DevOps/MathOps scripts only when an owned check, deterministic
  artifact, or current source shape requires it.

### Excluded by default

- Lambdapi semantic changes made only to simplify prose;
- speculative build-system refactors;
- hand-editing generated book Markdown or PDFs;
- changing lockfiles or dependency manifests without a demonstrated renderer
  need; and
- broad report rewrites whose only benefit is cosmetic consistency.

## 11. Implementation And Validation Ledger

| ID | Deliverable | State | Required evidence |
| --- | --- | --- | --- |
| BOOK-POSTINT-00 | Baseline, source, PDF, external-reference, and capability audit | complete | clean `62e9e10` worktree; baseline `book:check` and 201-page `book:render`; visual PDF inspection; source/owner review |
| BOOK-POSTINT-01 | This living plan and active index route | complete | exact diff and link hygiene reviewed; indexed by `emdash2/reports/INDEX.md`; authorization boundary recorded |
| BOOK-ARCH-02 | Generalize the book architecture checker from fixed 1-17 to a contiguous manifest/expansion contract | complete | pure contract tests cover Chapters 18 and 24 plus gaps, duplicates, and ordering; live source check and book render pass |
| BOOK-PSH-18 | Chapter 18 plus Chapter 13 bridge, evidence, provenance as needed, contents/preface path | complete | 2,798-word chapter; 113/113 evidence; 1,479 math spans; 210-page render/PDF; affected pages visually reviewed |
| BOOK-SITE-19 | Chapter 19 and site/descent glossary/status updates | complete | 3,147-word chapter; generated-topology and locality evidence checked; pages 142–149 visually reviewed |
| BOOK-SHEAF-20 | Chapter 20 and Pédrot provenance/citations | complete | 3,504-word chapter; 120/120 evidence; 234-page render/PDF; pages 150–158 visually reviewed |
| BOOK-ALG-21 | Chapter 21 and algebra notation/glossary/evidence | complete | 3,587-word chapter; 126/126 evidence; 250-page checked PDF; pages 159–167 visually reviewed |
| BOOK-AFFINE-22 | Chapter 22, Zeuner adaptation ledger, and `D(f)` narrative | complete | 4,650-word chapter; six affine evidence claims; Zeuner adaptation registered before prose; 132/132 evidence; 268-page checked PDF; pages 167–179 and contents visually reviewed |
| BOOK-SCHEME-23 | Chapter 23 and site-relative/Zeuner comparison boundary | complete | 3,984-word chapter; five checked evidence claims; Zeuner adaptation registered before prose; 137/137 evidence; 286-page checked PDF; pages 178-188 and contents visually reviewed |
| BOOK-PROJ-24 | Chapter 24 and projective-space research boundary | complete | 2,723-word chapter; four checked evidence claims; Zeuner comparison registered before prose; 141/141 evidence; 296-page checked PDF; pages 187-195 and contents visually reviewed |
| BOOK-XCUT-25 | Front matter, Appendix G, evidence/status/glossary, browser/usability reconciliation | complete | 39 sources; 141/141 evidence; 2,361 math spans; 299-page checked PDF; affected reader, status, glossary, and Appendix G pages visually reviewed |
| ARTICLE-02 | Concise article expansion and deterministic article PDF | complete | 1,362 lines; 8,693 words; 1,321-word geometry section; 17-page checked PDF; all pages visually reviewed |
| REPO-DOC-03 | Reader-first README and narrowly required report/MathOps maintenance | complete | grouped mathematical README route; focused report reconciliation; integration record closed; diff and 12 focused documentation contracts green; no unsupported tooling change |
| BOOK-RELEASE-04 | Edition metadata, deterministic book PDF, visual QA, and checked promotion to `docs/emdash-book.{md,pdf}` | complete | `0.4.0-dev`; two identical 299-page releases; PDF and visual checks green; Markdown/PDF promotion byte-identical |
| ARTICLE-RELEASE-05 | Deterministic article PDF and checked promotion to `docs/emdash3_2.{md,pdf}` | complete | `0.2.0-dev`; two identical 17-page releases; PDF and visual checks green; Markdown/PDF promotion byte-identical |
| GOAL-CLOSE-06 | Final authority/evidence/diff audit and handoff | complete | exact staged/unstaged inventory reviewed; all rows complete; baseline/main/worktrees preserved; no excluded repository or remote mutation |

At most one prose tranche should be in progress at a time. A chapter is not
complete because it renders: its main theorem, examples, status labels,
evidence IDs, boundaries, transitions, and source attributions must also read
as one argument.

## 12. First Bounded Tranche

The first implementation tranche is `BOOK-ARCH-02` plus the beginning of
`BOOK-PSH-18`:

1. make the expansion checker derive the contiguous numbered range from the
   manifest and structured architecture instead of hard-coding Chapter 17;
2. add a complete Chapter 18, not an outline placeholder;
3. simplify Chapter 13.1 to a mathematical bridge and move detailed sieve/site
   exposition into Chapter 18;
4. add the exact checked evidence claims used by Chapter 18;
5. update manifest/expansion/front-matter navigation only as needed for the
   new chapter;
6. run book source, evidence, typography, KaTeX, browser render, and visual
   page inspection; and
7. synchronize this ledger before selecting Chapter 19.

This slice intentionally does not yet bump the edition version, promote a
PDF, modify the article, or rewrite public READMEs.

### 12.1 Completed evidence

The first tranche completed on 2026-08-04 with the following bounded
evidence:

- the chapter contract derives its terminal chapter from the ordered manifest,
  retains Chapters 1-8 as the inherited range, and requires the structured
  expansion entries to cover every chapter from 9 through that terminal;
- focused Node tests accept terminal chapters 18 and 24 and reject gaps,
  duplicates, and out-of-order chapter IDs;
- the evidence validator now derives eligible implementation owners from the
  kernel-health source registry, excludes the diagnostics module from the
  owner role, and retains diagnostics/examples as independent reviewers;
- the book assembles 33 sources with 113 declared and cited evidence claims,
  validates 1,479 KaTeX spans, and passes source, typography, accessibility,
  local-link, and paper checks;
- the browser render has 210 pages with no console, page, request, render,
  overflow, link, math, or accessibility errors;
- the local development PDF has 210 tagged pages, 16 embedded fonts, no
  JavaScript, and SHA-256
  `d3e7aa1ebc656dedfb748cf232627be62013c573a70f3ef4a269fc4f17034118`; and
- pages 135-142, including the Chapter 18 opener, every chapter page, the
  pullback square, status notes, the invertibility-sieve discussion, and the
  appendix transition, were inspected as page images and found clean.

No version bump or tracked artifact promotion belongs to this tranche.

### 12.2 Sites and descent evidence

`BOOK-SITE-19` completed on 2026-08-05 with the following bounded evidence:

- the 3,147-word chapter separates cover families, covering sieves, generated
  topology, matching families, locality, and sheafification instead of
  collapsing them into one definition;
- its central theorem states the impredicatively generated least accepting
  topology, while the status note explicitly excludes derivation syntax,
  normalization, and decidable coverhood;
- matching and section categories are expressed as whole presheaf Hom
  categories, and the varying eligible-question layer supplies the exact
  transition into cover completion;
- evidence `GROTH-TOPOLOGY-SIEVE-LAWS`, `GENERATED-GROTH-TOPOLOGY`, and
  `SIEVE-MATCHING-LOCALITY` resolve to active owners and independent
  reviewers; and
- PDF pages 142–149, together with the Chapter 18 transition on page 141 and
  the Chapter 20 opener on page 150, were inspected at page-image resolution
  and found clean.

### 12.3 Direct cover sheafification evidence

`BOOK-SHEAF-20` completed on 2026-08-05 with the following bounded evidence:

- the 3,504-word chapter presents return, whole glue, and silent as one
  categorical-HIT argument, derives the second inverse and topology-locality,
  states the recursor and whole Hom universal property, and concludes with the
  Cat-valued reflective adjunction;
- Pédrot's *Pursuing Shtuck*, HAL `hal-04251754v1`, is version-pinned and
  registered under CC BY 4.0 before the conceptual return/glue/silent
  adaptation; the ledger explicitly excludes transfer of the paper's internal
  type theory, metatheory, universes, and dependent-elimination results;
- four new evidence claims distinguish the primitive categorical-HIT
  boundary, derived locality, whole Hom universality, and constructed
  Cat-valued reflector;
- the book assembles 35 sources with 120 declared and cited evidence claims,
  validates 1,744 KaTeX spans, and passes source, typography, accessibility,
  local-link, and paper checks;
- expansion from 210 to 234 pages exposed the old 60-second book render budget
  as a deterministic capacity boundary; the book-only budget is now a bounded
  90 seconds while the article remains at 60 seconds, and the complete shared
  print gate passes both the 15-page article and 234-page book with no console,
  page, request, render, overflow, link, math, or accessibility errors;
- the local development PDF is tagged, has 234 pages and 16 embedded fonts,
  contains no JavaScript, and has SHA-256
  `88c3fa21ab8cc4fb99b6848eea74aea3a33904679ed89222144b428c795d4519`; and
- contents page 7, every Chapter 20 page 150–158, the Chapter 19 transition,
  every wide display and evidence note, and the Appendix A transition on page
  159 were inspected as images and found clean.

The root workspace check and root typecheck are green for the print registry
changes. The intentionally untouched root TypeScript suite also completed
green after its full compute-bound run: 1,424 tests, 1,371 passed, 53 skipped,
zero failures, and 4,694.254 seconds total duration. No version bump or tracked
artifact promotion belongs to these chapter tranches.

### 12.4 Commutative algebra evidence

`BOOK-ALG-21` completed on 2026-08-05 with the following bounded evidence:

- the 3,587-word chapter treats set-carrier commutative rings, structured
  maps, finite unit-ideal certificates, free polynomial extension,
  one-element localization, concrete unit/zero/idempotent models, and the
  iterated/product-localization equivalence as one representation-free
  argument rather than an inventory of library modules;
- the source audit distinguishes general universal-property interfaces from
  existence: the checked arbitrary-input statements are conditional on
  supplied polynomial/localization packages, while the empty-variable,
  already-unit, zero, fixed-idempotent, and split-idempotent cases are the
  selected constructed models;
- six evidence claims resolve the structured ring category, finite
  unimodular presentations, polynomial universality, localization
  universality, selected localization models, and both whole cancellation
  laws for product versus iterated localization to active owners and
  independent examples;
- the chapter explicitly excludes a categorical product universal property,
  arbitrary package identity, global polynomial/localization existence,
  monomial or fraction syntax, and any inference that affine geometry has
  already been constructed;
- front-matter routes, the structured expansion, the notation table, the
  glossary, and the status matrix now incorporate Chapter 21 without a
  version bump or tracked-artifact promotion;
- the book assembles 36 sources with 126 declared and cited evidence claims,
  validates 1,941 math spans, and passes source, typography, accessibility,
  local-link, paper, and browser-render checks;
- the local development PDF is tagged, has 250 letter-sized pages and 16
  embedded fonts, contains no JavaScript, and has SHA-256
  `6fdb8dd76dd823d3f71f5cf5c372ebf960e07b7ce64e7a275bced0a5ad355bdb`; and
- contents page 7, the Chapter 20 transition on page 158, every Chapter 21
  page 159–167, and the Appendix A transition on page 168 were inspected as
  page images and found clean.

### 12.5 Affine geometry evidence

`BOOK-AFFINE-22` completed on 2026-08-05 with the following bounded evidence:

- the 4,650-word chapter develops one reader-facing chain from generalized
  affine points through the ordinary invertibility sieve, pointwise
  localization representation, multiplicative intersection, the big affine
  slice and coordinate presheaf, finite Zariski generation, and the
  assumption-explicit structure-sheaf/locality boundary;
- Zeuner Sections 2.2, 4.1, 4.2, and 5.1 were registered under adaptation
  `ZEUNER-CH22-AFFINE-BASIC-OPEN` before chapter prose was drafted; the
  structural adaptation makes the actual sieve of invertibility probes
  primary, treats localization or a compact open as a representation when
  available, and explicitly excludes importing the qcqs comparison theorem,
  compact-open classification, or general scheme theorem;
- six evidence claims distinguish the pointwise equivalence
  `Hom(R[1/f],S) ~= D(f)(S)`, the pointwise product/intersection theorem, the
  whole big-slice coordinate presheaf, the constructed least generated big
  Zariski topology, the supplied reflective structure-sheaf presentation,
  and the supplied whole localization-locality/thin affine presentation;
- the chapter explicitly declines to promote component equivalences to a
  whole natural equivalence, to identify the big and small Zariski sites, or
  to claim CommRing-valued sheafification, subcanonicity, stalks, a
  stalk-local-ring theorem, a representation-independent category of affine
  schemes, or Zeuner's qcqs comparison;
- the book assembles 37 sources with 132 declared and cited evidence claims,
  validates 2,111 math spans, and passes source, typography, accessibility,
  local-link, paper, and browser-render checks with 268 pages and no console,
  page, request, render, overflow, link, math, or accessibility errors;
- the local development PDF is tagged, contains no JavaScript, has 268
  letter-sized pages and 16 embedded fonts, and has SHA-256
  `9aaeb17651cee3ce4181ad29dad3b6b14f97adc84bbe4195e56d440003216ca0`; and
- contents page 7, the Chapter 21 transition on page 167, every Chapter 22
  page 168–178, and the Appendix A transition on page 179 were inspected as
  page images. That review caught an inline list continuation, a crowded
  equation number, and an awkwardly split formal-status block; the list was
  rewritten as prose, the affine-presentation display was aligned over two
  lines, the status note was moved intact, and the corrected pages were
  rerendered and re-inspected cleanly.

No metadata version bump or tracked-artifact promotion belongs to this
chapter tranche.

### 12.6 Site-relative scheme authority and provenance

`BOOK-SCHEME-23` began on 2026-08-05 only after an exact owner and provenance
audit:

- the retained global package supplies a reflective CommRinged site, a whole
  object, one ordinary covering sieve, and its existing whole structure
  presheaf; Grothendieck stability derives pullback covers, but the package
  constructs neither affineness nor a scheme;
- two selected members generate that retained sieve only through the
  witness-rich `BinarySelectedCoverGeneration`: every member computes a
  Boolean branch, a factor map through one generator, and its triangle;
  an arbitrary member is therefore a refinement of an affine generator, not
  itself asserted affine;
- the whole presheaf on an actual slice is constructed by precomposition with
  the slice-domain functor, while the reflective slice site, its topology,
  sheafification boundary, and whole comparison with that ambient restriction
  remain explicitly supplied;
- an affine chart realization supplies a coordinate ring, thin affine scheme
  presentation, affine-basis functor, sheaf-basis equivalence, and whole
  ambient-to-coordinate comparison; it does not construct a raw equivalence
  of base sites or transport a general exactness theorem;
- the topology-local ring capability is the executable categorical form of
  `D(0)=bottom` and `D(s+t)<=D(s) join D(t)`: if zero is a unit the empty
  sieve covers, while an invertible sum selects a covering sieve on whose
  members one summand is invertible; it is not a stalk theorem or a raw-sieve
  join construction;
- totaling the global object, whole-object local certificate, constructively
  generated binary affine cover, and both whole chart realizations produces
  `BinarySiteRelativeSchemePresentation`; the site-relative qualifier remains
  essential and no overlap, transition, cocycle, or gluing field is duplicated;
- an actual binary chart overlap is available only after a selected binary
  product with whole universal property is supplied in the conventional
  slice; its projections, base arrows, overlap ring, and both restriction
  homomorphisms are then derived from existing whole owners; and
- Zeuner Sections 3.3, 4.2, 5.1, and 5.3 were registered under adaptation
  `ZEUNER-CH23-SITE-RELATIVE-SCHEMES` before prose. The finite affine-cover
  architecture is comparative only: the chapter imports no atlas-gluing
  theorem, compact-open classifier, qcqs comparison, or
  representation-independent category of schemes.

The completed tranche adds a 3,984-word Chapter 23, five evidence claims, and
the corresponding contents, preface, notation, glossary, status, bibliography,
and provenance integration. Its final source gates covered 38 source files,
137 cited claims, and 2,261 math spans. The browser renderer produced 286 pages
with no console, page, request, or render errors. The checked development PDF
has 16 embedded fonts and SHA-256
`0dd6cdddb5673fdc960439ce181c4d42ed1dcba1e52c3dc0ba82b56fa3d1e711`.

The visual review covered the contents, the Chapter 22-to-23 transition, every
page of Chapter 23, and the Appendix A transition (pages 178-188). It caught
and corrected an orphaned contents heading, crowded equation numbers in
(23.4) and (23.15), and an awkward line break in the local-presentation prose;
the affected pages were rerendered and re-inspected cleanly. No metadata
version bump or tracked-artifact promotion belongs to this chapter tranche.

### 12.7 Laurent and supplied-projective authority audit

`BOOK-PROJ-24` began only after the following exact owner audit and before any
chapter prose:

- the generic Laurent owner consumes existing one-variable polynomial-algebra
  packages and supplied localizations at their distinguished coordinates;
  polynomial universality constructs the map sending one coordinate to the
  inverse of the other, localization universality extends it to the two
  Laurent rings, and reversing the inputs constructs the opposite map;
- those two generic transition maps are not asserted inverse for arbitrary
  inputs. For two literal maps into one shared ring, the
  `CommRingLaurentOverlapPresentation` supplies whole paths identifying both
  internally constructed endomorphisms with the identity of that exact ring;
- the literal one-variable localization presentation supplies its base map,
  coordinate, polynomial universal property, and localization universal
  property. No polynomial syntax, fraction normalizer, runtime fold, or
  chosen global localization is constructed by the Laurent layer;
- the actual-scheme adapter adds one common base ring and instantiates the
  generic Laurent package at the two retained chart rings, the actual inherited
  overlap ring, and the two structure-presheaf restrictions. It does not infer
  that package without data or add a disconnected overlap isomorphism;
- `SuppliedProjectiveLinePresentation(K)` is exactly the dependent total of an
  already-global binary site-relative scheme, a selected actual chart
  intersection, and that Laurent package. Its observations compute by Sigma
  projection; the package does not construct its global object from charts,
  prove the object projective or non-affine, or establish representation
  independence; and
- no active Lambdapi source declares a graded ring, homogeneous localization,
  degree-zero construction, irrelevant ideal, `Proj`, or general projective
  space. Those are mathematical-development and research boundaries, not
  hidden consequences of the supplied total.

Four checked claims were registered before prose:
`LAURENT-TRANSITIONS-BY-UNIVERSALITY`,
`LAURENT-COMMON-OVERLAP`,
`ACTUAL-SCHEME-LAURENT-OVERLAP`, and
`SUPPLIED-P1`. Zeuner Sections 2.2, 3.3, 4.2, and
5.3 were registered under adaptation `ZEUNER-CH24-PROJECTIVE-BOUNDARY`. The
adaptation imports the finite-cover rhythm and comparison boundary only;
Zeuner's thesis is not represented as a source of the Laurent construction,
`Proj`, projective space, or non-affineness.

The completed tranche adds a 2,723-word Chapter 24 with those four checked
claims. Its final source gates covered 39 source files, 141 evidence claims,
and 2,348 mathematics spans. The browser render and owner-generated PDF both
completed at 296 pages; the PDF check found 16 embedded fonts and SHA-256
`90579215b586fe29cc56e411d080875aa7414ae6621b2c9058e8211529862bbd`.
Pages 187-195 and the contents were inspected as page images. That review
caught and corrected an orphaned contents transition, an equation-number
collision in (24.11), cramped nested sums in (24.13), overlong evidence
labels, an orphaned summary introduction, and a split research-boundary
callout. No metadata version bump or tracked-artifact promotion belongs to
this chapter tranche.

### 12.8 Cross-cutting reader-surface audit

`BOOK-XCUT-25` began with a read-only comparison of the current TypeScript
sources, completed usability plans, book status prose, and public reviewer:

- `CORE_BROWSER_REVIEWER_BOUNDARY` records twelve source presets across
  ordinary, natural, displayed-functorial, and displayed-natural binders,
  finite canonical sibling/Sigma contextual abstraction, qualified
  depth-generic finite Hom-category recursion, arbitrary finite rigid
  indexed-section chains, source-located edited text, the three-part report,
  generated book, and preserved minimal-Core playground;
- the current recursive section example is
  `λ^n k : K. (GG k) ((FF k) (s k))`; it reuses the existing contextual
  program, explicit Core, and generic LF rather than adding a browser-only
  checker or action table;
- the adjunction outer-LF macro expands already typed rectangular data, or a
  counit and whole hom transpose, into ordinary declarations and proof-time
  agreements. It adds no new runtime equation or Lambdapi owner;
- the structure macro is limited to an unparameterized, nonrecursive,
  single-constructor dependent package with named primitive projections and
  ordered subject-reducing projection betas. It adds no eta, eliminator,
  recursion, positivity result, general inductive facade, trusted Core node,
  text grammar, browser profile, or Lambdapi change; and
- the public reviewer route returned HTTP 200 during the audit, but its
  deployed lazy asset still declared the preceding eleven-preset profile. The
  book's live-or-local instruction therefore does not promise an exact count;
  Appendix G states the current source profile exactly. No deployment, push,
  or publication mutation is authorized by this tranche.

The stale book statements were the glossary's “future elaborator” and
four-layer descriptions, Appendix F's one-telescope/unrestricted-depth
summary, the compact Chapter 12 authoring boundary, and the absence of the
current reviewer and declaration conveniences from Appendix G. Product
behavior is unchanged, so no focused TypeScript or browser regression is
required by this prose tranche; the previously completed root aggregate
remains the applicable unchanged-boundary evidence.

The completed cross-cutting pass now gives the book one reader-facing account
of the renewed product boundary. The reading guide points to the live or local
client reviewer without freezing deployment-specific counts. Chapter 12
briefly locates adjunction authoring. Appendices B and F distinguish MathOps
provenance from mathematical authority. The glossary, evidence statement,
third-party adaptation boundary, and Appendix G now agree on contextual
elaboration, explicit Core, the four binder modes, finite canonical
dependency levels and sibling groups, qualified finite Hom recursion, finite
rigid section chains, outer-LF declaration conveniences, located text, and
the client-side reviewer.

Final tranche evidence is:

- the book assembles 39 source files with 141 declared and cited evidence
  claims and 2,361 mathematics spans;
- source, typography, KaTeX, paper, browser-render, and PDF checks pass; the
  browser render has 299 pages with no console, page, request, or render
  errors;
- the checked local development PDF has 299 letter-sized pages, 16 embedded
  fonts, and SHA-256
  `5f3dd845b6eaff70a9a0b9c42be22ea6a3a2b2a0fe9d1a3b04a411cda7279dd2`;
- page-image review covered the reading guide, Chapter 12 insertion,
  Appendix B, the changed glossary sequence, Appendix F-to-G transition,
  architecture diagram, split ownership map, all of G.5, and the G.6
  transition (pages 5, 88, 201, 259-261, 271-274, 282-283, and 287-293);
  it caught and corrected stranded formulas and headings, a wrapped evidence
  pipeline, glossary punctuation, an oversized ownership table, raw internal
  terms that split from their prose, and a page-boundary word division; and
- no product behavior, edition metadata, tracked distribution artifact,
  public deployment, or remote repository state changed in this tranche.

### 12.9 Concise article evidence

`ARTICLE-02` began from the 15-page article baseline and preserved its title,
two Arrowgram figures, synthetic-arrow-induction argument, and explicit
research-draft status. The accepted source adds the sieve-before-open
argument, pointwise localization representation, finite generated topology,
direct categorical-HIT cover completion, and an exact affine/scheme/projective
boundary. It also reconciles the four binder modes, twelve reviewer presets,
finite canonical dependency levels and sibling groups, qualified finite Hom
recursion, finite rigid section chains, and the bounded adjunction/structure
declaration conveniences.

Final tranche evidence is:

- the canonical authored source has 1,362 lines and 8,693 words; Section 8 has
  1,321 words and remains within the planned 1,200-1,800-word argument;
- `article:check`, `article:render`, `article:pdf`, and
  `article:pdf:check` pass; the browser render reports no console, page,
  request, or render errors;
- the checked local PDF has 17 pages, 14 embedded fonts, 726,991 bytes, and
  SHA-256
  `35f973b33131776e6cba46b635b8a49f88a2d9de77f0dffd7fc2f717c34914ab`;
- all 17 pages were inspected as page images. The visual pass caught the
  initial authored-source/distribution mismatch, three stranded Section 6
  subsection headings, an unsuitable narrow-column ASCII architecture
  diagram, and two boundary widows; the accepted PDF corrects all four
  classes of issue; and
- no product behavior, edition metadata, public deployment, remote repository
  state, or final tracked-artifact promotion changed in this tranche.

### 12.10 Supporting-document audit

`REPO-DOC-03` completed as a dependency-driven reconciliation rather than a
general documentation rewrite:

- the root README now names the local-to-global mathematical scope and its
  exact constructed/supplied boundary while preserving the deployed-reviewer
  product contract;
- `emdash2/README.md` replaces its stale per-module catalogue with a grouped
  mathematical route through directed structure, representability,
  presheaves/sites, direct cover sheafification, constructive algebra, affine
  geometry, site-relative schemes, and the supplied projective line;
- Foundations and the current SOP received only the missing summary boundary,
  while the canonical-syntax report now distinguishes its broad mathematical
  notation from the implemented bounded TypeScript binder text and records the
  generated-topology/direct-cover owners;
- the parallel-integration plan now records the verified direct-parent merge,
  local-main fast-forward, and three preserved artifact archives as complete;
- the title notice and prologue now route the reader into the third
  local-to-global spiral instead of ending their architecture at Chapter 17;
  and
- no additional DevOps/MathOps code or kernel semantics changed: the audit
  found no stale owner, failed check, or source-shape requirement that would
  justify such a change.

`git diff --check` passes. The two focused release-policy suites pass 11/11,
and the focused browser/README integration contract passes 1/1. Historical
full-TypeScript and integrated-kernel evidence is carried forward because this
tranche changes no shared TypeScript or Lambdapi behavior. `BOOK-RELEASE-04`
then became the sole tranche in progress.

### 12.11 Local release and promotion evidence

The stabilized source architecture advances the book to `0.4.0-dev` and the
article to `0.2.0-dev`, both dated 2026-08-05. Their edition names and explicit
draft statuses are intentionally retained.

- Two complete cold `book:release` runs produced the identical SHA-256
  `7f74207baefedd04134a89eee1e7d7fa9e4c3d995835f9b1260292615aededcf`.
  The checked PDF is 2,628,925 bytes, 299 letter-sized tagged pages, has 16
  embedded fonts and no JavaScript, and its fixed metadata names version
  `0.4.0-dev` with draft status.
- Two complete cold `article:release` runs produced the identical SHA-256
  `d2bebb2da8b1456ade8d258a03b7ea48e04adde03a6ae227602769f97a235bec`.
  The checked PDF is 726,992 bytes, 17 letter-sized tagged pages within the
  unchanged 14-18-page budget, has 14 embedded fonts and no JavaScript, and its
  fixed metadata names version `0.2.0-dev` with draft status.
- Both releases repeated source/registry, paper, production-build, browser,
  console, request, render, deterministic-export, and structural PDF checks.
  No console, page, request, render, link, math, accessibility, metadata,
  tagging, font, or replacement-character defect was found.
- Earlier tranche reviews cover every changed article page, each new book
  chapter, dense displays, evidence/status material, and affected back matter.
  Final page-image review rechecked the versioned book cover, expanded-edition
  notice, new prologue bridge and Chapter 1 transition, plus the article title
  and abstract; all are clean.
- The checked owners promoted both Markdown and PDF distributions byte for
  byte. `docs/emdash-book.pdf` and `docs/emdash3_2.pdf` match their versioned
  owner PDFs, while their tracked Markdown files match the assembled book and
  canonical article sources respectively.

This is a local deterministic release and tracked-artifact promotion only. No
remote publication, push, tag, PR, commit, merge, deployment, or history
mutation occurred. `GOAL-CLOSE-06` then became the sole tranche in progress.

### 12.12 Goal-closure audit

The final audit found 36 expected tracked modifications and ten expected new
source files: this plan, seven complete chapters, and the book-architecture
owner plus its focused test. The staged diff is empty, `git diff --check`
passes, both tracked distributions are byte-identical to their owners, and
`qpdf --check` reports no syntax or stream errors for either PDF. No unrelated
file or generated-owner violation is present.

The recent 1,424-test green root suite covers the print registry/architecture
changes, and the integrated `62e9e10` baseline supplies the unchanged full
kernel/cross-layer qualification. Those multi-minute aggregates are carried
forward under the repository's proportional-validation rule because the later
tranches changed only prose, metadata, and local publication artifacts. Fresh
book/article source, evidence, typography, KaTeX, registry, browser-render,
console/request, deterministic PDF, focused README-policy, PDF-structure, and
promotion checks cover the changed boundary directly.

The goal branch still points at baseline `62e9e10`; local `main` is clean at
the same commit; the dedicated worktree and every pre-existing worktree remain
in place. The reproducible temporary page-image renders were removed after
visual review. No commit, push, merge, tag, PR, remote publication, deployment,
history rewrite, branch deletion, or worktree removal occurred. Every ledger
row is complete.

## 13. Validation Policy

### 13.1 Each authored chapter tranche

From the goal worktree root:

```bash
./scripts/pnpmw run book:typography
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
git diff --check
```

Render affected PDF page ranges when a PDF exists and inspect them as images.
Check the chapter opener, every wide display/table, transitions at preceding
and following chapter boundaries, and any page that changed pagination.

### 13.2 Checker or renderer changes

If `emdash2/print/` behavior changes, run the closest focused tests plus:

```bash
./scripts/pnpmw --dir emdash2/print run validate:paper
./scripts/pnpmw --dir emdash2/print run check:render
```

Use the full shared-pipeline gate only when shared rendering actually changes.
A book-architecture contract change does not authorize unrelated renderer
refactoring.

### 13.3 Final book artifact

Use the existing owners:

```bash
./scripts/pnpmw run book:release
./scripts/pnpmw run book:release
./scripts/pnpmw run book:promote
```

The two releases must produce identical SHA-256 checksums. Inspect page images
for the title, contents, every new chapter opener, evidence tables,
bibliography, credits, license, and representative dense pages. Confirm
metadata, embedded fonts, tagging, page numbers, no replacement characters,
and no external requests. Never patch a PDF directly.

### 13.4 Article artifact

Use the existing article owner and checked promotion route. Adjust its page
budget only after measuring the edited source, never to conceal layout
failure.

### 13.5 Lambdapi and TypeScript gates

The integrated baseline already has a complete green cross-layer gate. Carry
that evidence forward for unchanged semantic boundaries.

- Pure prose/evidence-reference changes do not require a fresh kernel CI run.
- Run a bounded kernel check if a new checked claim depends on a disputed or
  newly changed owner.
- Run focused TypeScript/browser tests only if reader examples or reviewer
  behavior changes.
- Run `check:ts` once at the end of a tranche that changes shared TypeScript
  behavior.
- Run `check:all` only at a genuine affected cross-layer or publication
  boundary.

## 14. Decision Ledger

| ID | Decision | State |
| --- | --- | --- |
| BOOK-D-001 | Organize the new material as a third local-to-global spiral, not a developer chronology. | accepted |
| BOOK-D-002 | Use `D_U(s)` as the recurring geometric idea: the sieve of invertibility probes is primary; a compact open is a representation when available. | accepted |
| BOOK-D-003 | Present Zeuner's compact-open support as valid in its coherent/qcqs scope and the sieve as a generalization, not a refutation. | accepted |
| BOOK-D-004 | Explain categorical semantics as computationally internal inside the outer LF, without requiring a separate modal object language. | accepted |
| BOOK-D-005 | Add Chapters 18-24 with one complete chapter per bounded prose tranche. | accepted |
| BOOK-D-006 | Give direct cover completion its own chapter because construction, locality, universality, and reflector assembly form one mathematical proof. | accepted |
| BOOK-D-007 | Keep the supplied projective line distinct from constructed `Proj` and general projective space. | accepted |
| BOOK-D-008 | Keep elaborator, macro, browser, and MathOps work in compact cross-cutting destinations rather than the geometry narrative. | accepted |
| BOOK-D-009 | Generalize the fixed chapter checker through its owner before adding Chapter 18. | accepted |
| BOOK-D-010 | Do not bump metadata or promote artifacts until the expanded source architecture is stable. | accepted |
| BOOK-D-011 | Use selective attributed adaptation from CC BY sources; default to fresh prose where the emdash viewpoint differs. | accepted |
| BOOK-D-012 | No local commits without additional explicit authorization. | active constraint |

## 15. Risks And Guards

### Risk: the book becomes an implementation report

Guard: every section must answer a mathematical question before naming an
owner. Move identifiers, limitations, and traceability to compact formal-status
notes.

### Risk: breadth destroys pedagogy

Guard: use one recurring chain - probe, sieve, cover, glue, localization,
chart - and introduce no structure before its motivating problem.

### Risk: assumption-explicit packages are narrated as constructions

Guard: use “given”, “supplied”, “selected”, and “constructed” consistently.
Make the input/output boundary part of each central theorem statement.

### Risk: pointwise results are promoted to natural equivalences

Guard: distinguish an equivalence for each test ring from equality or
equivalence of whole presheaves. Cite only the active strength.

### Risk: projective-line language overclaims projective space

Guard: title and central status say “supplied projective line”; put `Proj`,
`P^n`, construction of the global object, and non-affineness in the research
boundary.

### Risk: adapted prose loses provenance

Guard: provenance entry first, prose second. Verify license, version, section,
target, adaptation type, attribution, and change description.

### Risk: artifact success substitutes for visual quality

Guard: PDF gates are necessary but not sufficient. Render page images and
inspect spacing, hierarchy, math, tables, transitions, headers, and footers.

### Risk: side maintenance consumes the primary goal

Guard: perform repository/report/tooling edits only when a completed book or
article tranche exposes a concrete stale claim or failing owner.

## 16. Persistent Goal Objective

Use the following objective for the persistent goal:

> In `/home/user1/emdash1-book-v3.2` on
> `goal/emdash-book-v3.2`, continue from baseline
> `62e9e1009b8f3ccb25c8e8cbf39a1ec68433a363` and treat
> `docs/EMDASH_BOOK_V3_2_POST_INTEGRATION_EXPANSION_PLAN_2026-08-04.md`
> as the active living editorial, implementation, validation, and recovery
> ledger. Expand the emdash book as a high-quality theorem-led mathematical
> work, not a developer report. Build the third local-to-global spiral through
> Chapters 18-24: presheaves and sieves; sites, covers, and descent; direct
> categorical-HIT sheafification; constructive commutative algebra by
> universal property; affine geometry centered on the invertibility sieve
> `D_U(s)`; site-relative schemes from covering charts; and the supplied
> projective-line boundary. Use Zeuner's CC BY 4.0 thesis with explicit
> provenance and from the sieve-centered viewpoint that a compact
> invertibility open is a representation of the more general invertibility
> sieve when such a representation exists. Explain how actual categorical
> semantics can be computationally internal inside the outer Lambdapi or
> TypeScript LF without replacing it by an abstract modal object language.
> Keep checked, formal-consequence, mathematical-development, and
> research-boundary claims exact; distinguish supplied packages from
> constructed objects, higher from ordinary sieves, pointwise from whole
> equivalence, site-relative schemes from the deferred Zeuner comparison, and
> the supplied projective line from deferred `Proj` and `P^n`. Reconcile the
> TypeScript binder/text, adjunction/record usability, browser reviewer, and
> MathOps work only in compact reader-facing destinations. Update the concise
> article after the book claims stabilize, make only dependency-driven
> repository/report/tooling maintenance, validate every bounded tranche
> proportionally, visually inspect changed PDFs, and use the existing
> deterministic owners for final promotion to `docs/emdash-book.pdf` and
> `docs/emdash3_2.pdf`. Update the living plan whenever evidence changes a
> decision or row. Branch/worktree and local artifact generation are
> authorized; commits, push, merge, remote publication, PRs, history rewrite,
> cleanup, branch deletion, and worktree removal are not authorized.

## 17. Completion Definition

The goal is complete only when:

- every ledger row is complete, rejected with durable evidence, or deferred
  behind a named prerequisite accepted in this plan;
- the third spiral reads as one mathematical argument with smooth transitions
  from the existing book;
- every theorem-like claim has the correct status and evidence;
- every adapted passage has complete compatible attribution;
- book and article sources, structured manifests, evidence, glossary, status,
  and public-facing repository claims agree;
- deterministic book and article artifacts pass their owners, receive visual
  QA, and are promoted byte-for-byte to the tracked `docs/` paths;
- the exact staged and unstaged diff is reviewed and contains no unrelated or
  generated-owner violation; and
- no excluded Git, publication, destructive, or remote operation occurred.

Token or time pressure is not completion. Leave the branch and worktree
intact for review unless the user separately requests cleanup.
