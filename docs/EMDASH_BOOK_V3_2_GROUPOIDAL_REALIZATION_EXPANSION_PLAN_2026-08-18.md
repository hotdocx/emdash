# Emdash Book v3.2 Groupoidal Realization Expansion Plan

Date: 2026-08-18 (America/Toronto)

Plan-ID: `EMDASH-BOOK-GROUPOIDAL-REALIZATION-EDITION-V0.5`

Status: **active fourth-spiral book continuation**. The cumulative baseline,
book contract, stale-claim inventory, evidence boundary, and chapter
architecture have been reviewed. `BGR-00` and `BGR-ARCH-1` are complete;
`BGR-REPAIR-2`, `BGR-CH25-3` through `BGR-CH28-6`, `BGR-XCUT-7`, and
`BGR-ARTICLE-8` and `BGR-RELEASE-9` are complete, and `BGR-CLOSE-10` is the
active final authority/diff/plan synchronization row.

Branch: `goal/emdash-book-groupoidal-v3.2`

Worktree: `/home/user1/emdash1-book-groupoidal-v3.2`

Baseline: `f4d9303411a09f143912832315153c234807e724`

Parent mathematical ledger:
`emdash2/reports/REPORT_EMDASH_V3_2_INTERNAL_LAXITY_AND_GROUPOIDAL_REALIZATION_CONTINUATION_PLAN_2026-08-17.md`

Predecessor editorial ledger:
`docs/EMDASH_BOOK_V3_2_POST_INTEGRATION_EXPANSION_PLAN_2026-08-04.md`

Side-Task-Ledger: `BGR-00`, `BGR-ARCH-1`, `BGR-REPAIR-2`,
`BGR-CH25-3`, `BGR-CH26-4`, `BGR-CH27-5`, `BGR-CH28-6`, `BGR-XCUT-7`,
`BGR-ARTICLE-8`, `BGR-RELEASE-9`, and `BGR-CLOSE-10`

Infinity-Codex-Origin: session
`019ffe39-2eb9-7080-88e3-06b77d69b8d1`; architectural decision response
`0056`, archived at
`/home/user1/emdash1/emdash2/tmp/ai-responses/sessions/2026-08-14_019ffe392eb9/responses/0056_2026-08-18T10-33-36Z_01a0146c-3a14-75e0-9e92-8380e1686fef.md`.
Active code, the book contract, and this living plan outrank the archive.

## 1. Objective

Expand *Functorial Type Theory: Univalent Foundations for Mathematics* from
the completed 0.4.0 local-to-global edition into a globally coherent
groupoidal-realization edition. The new mathematics must be presented as a
fourth conceptual spiral, not as a list of recently added Lambdapi modules.

The governing question is:

> What becomes of directed motion when it is realized in the groupoidal
> world, and how much of that realization can still compute?

The primary deliverable is the theorem-led book and its checked local PDF.
The concise overview article is a secondary deliverable. Repository and
renderer maintenance are supporting work only where demanded by the book's
structured owners or release gates.

This goal must preserve the completed first three spirals:

1. foundations and the WalkingEnd/Natural-number calculation;
2. cut calculus, category theory, and universal constructions;
3. local-to-global algebraic geometry; and
4. the new return from directed arrows to groupoidal paths, free inversion,
   and Gray-shaped coherence.

## 2. Authority And Recovery Order

Use the following order on every continuation:

1. root, Lambdapi, and print `AGENTS.md` instructions;
2. active Lambdapi owners and focused reviewers;
3. current Foundations, SOP, and canonical-syntax reports;
4. `emdash2/book/book.json`, `expansion.json`, `STYLE.md`, `evidence.json`,
   provenance records, and `RELEASE.md`;
5. this living plan;
6. the completed groupoidal, laxity, truncation, Gray, Circle, interval, and
   generic-groupoidification child plans;
7. the completed 0.4.0 book ledger and publication/article plan;
8. pinned third-party sources; and
9. explicitly linked archived responses only for recovery.

Book prose never becomes a mathematical authority. If prose and an active
owner disagree, correct the prose and evidence register.

## 3. Git And Publication Boundary

The user authorized a new branch/worktree from the cumulative mathematical
checkpoint, implementation under a living plan, and a persistent goal. The
standing thread instruction also authorizes local green checkpoint commits
following the repository checkpoint SOP.

This authorization does not include:

- push, merge, tag, PR, GitHub Pages deployment, Zenodo publication, or other
  remote release;
- rebase, amend, squash, reset, force push, history rewrite, branch deletion,
  or worktree removal;
- modifying the completed `/home/user1/emdash1-book-v3.2` worktree; or
- changing Lambdapi or TypeScript semantics merely to simplify exposition.

Local deterministic generation and promotion to the tracked `docs/` paths
are in scope because they are explicit book/article deliverables. Remote
publication remains a separately authorized final release step.

## 4. Reviewed Baseline

### 4.1 Git and mathematical baseline

The new branch starts cleanly at `f4d9303`. That commit is a descendant of:

- current local `main` at `86042df`;
- the completed 0.4.0 book at `716cd47`;
- internal-laxity closeout;
- path-realized pseudo-laxity;
- computational truncation and Circle connectedness;
- profiled Gray right closure and interchanger;
- Circle/Integer and WalkingEnd--Circle universality;
- dependent judgmental Circle-loop computation;
- the groupoidal interval and WalkingArrow universality; and
- generic category-indexed groupoidification through `f4d9303`.

The resulting branch remains linearly fast-forwardable if later publication
is authorized.

### 4.2 Current book

The completed predecessor edition has:

- version `0.4.0-dev`, publication date 2026-08-05, and draft status;
- 299 checked PDF pages;
- 39 ordered source files;
- 24 numbered chapters and seven appendices;
- approximately 61,900 chapter words;
- 141 checked/formal-status evidence claims; and
- 2,363 mathematical spans at the cumulative baseline.

`workspace:check` and `book:check` pass in the new worktree. The latter
reassembles all 39 sources, checks all 141 cited evidence identifiers, checks
typography and KaTeX, and validates the registered generated book.

The predecessor book worktree is clean and retained. No source after that
edition changed except the focused Chapter 5 reader-facing TypeScript
PathOut-evidence explanation. The tracked 299-page book artifact itself is
therefore the correct visual baseline.

### 4.3 Current article

The overview article is already 18 pages, the maximum registered page budget.
It contains the completed Circle/Integer and representative product-closure
result, but not the later whole WalkingEnd--Circle theorem, interval theorem,
generic `Groupoidify(C)`, or selected Gray realization. The article must be
rebalanced and rewritten, not merely appended to.

### 4.4 Stale reader-facing claims

The audit found concrete claims that were correct in 0.4.0 but are now false
or materially incomplete:

- Chapter 7 and evidence `TRUNC-REFLECTOR` still say that no computational
  truncation reflector is active.
- Chapter 8 says that a future Circle comparison or group completion must be
  constructed and that no comparison functor is active.
- Appendix C says that group completion and the `BInt`/Circle bridge remain
  future work.
- Chapter 6 names directed intervals only as future tests, although the
  groupoidal interval and WalkingArrow comparison are active.
- evidence `WE-GROUP-COMPLETION` says that no Circle comparison exists.
- evidence `FUNCTORD-WHOLE-LAXITY` still describes a whole laxity facade as
  deferred, although whole post/left and pre/right surfaces are active.
- the preface, reading guide, prologue road map, contents, glossary, status
  appendix, and evidence appendix describe only three spirals.

These are correctness repairs, not optional embellishments. They must be
resolved before the new edition can close.

## 5. Editorial Thesis

The fourth spiral is governed by two linked sentences:

> Direction is visible in the difference between natural and integer powers.

> Free groupoidal realization does not erase higher action; it makes the
> directed coherence witnesses invertible.

The WalkingEnd theorem says that one noninvertible generator has natural
powers. The Circle theorem says that one invertible loop has integer powers.
The comparison is not a renaming: it is a whole functor whose mapping theorem
expresses free inversion. The WalkingArrow/interval theorem then tests
different endpoints, and category-indexed `Groupoidify(C)` abstracts the
same universal property without reducing the input to an object graph.

This supplies the principal narrative arc:

```text
directed arrow and explicit higher action
    -> realization as paths
    -> invertible pseudo coherence
    -> Circle and Integer loop calculation
    -> concrete free inversion of WalkingEnd and WalkingArrow
    -> category-indexed groupoidification
    -> selected Gray-shaped interchanger back in the directed world.
```

The Gray material belongs at the end of the spiral because it answers a
different question. Product transport in the groupoidal layer does not imply
that the directed tensor should be Gray. The selected Gray right closure
instead exposes lax transformations and an oriented interchanger. This is a
bridge back to directed higher category theory, not an alternative proof of
the Circle theorem.

## 6. Book Architecture

Use a hybrid architecture:

- add four sustained chapters after Chapter 24;
- make concise, targeted repairs and forward references in existing chapters;
- preserve all existing chapter numbers and avoid renumbering the completed
  geometry spiral; and
- centralize technical owner names in evidence notes and appendices rather
  than the main prose.

### Chapter 25 — Paths And The Groupoidal Shadow

Reader question: how does equality-local homotopy sit inside the directed
categorical calculus without becoming a second foundation?

Narrative:

- one primitive equality eliminator and its structured categorical reading;
- `Path(A)` as the groupoidal shadow of a classifier;
- ordinary functions as iterable path functors;
- product paths and the explicit split/join equivalence;
- direct versus sequential product transport and the coherence diamond;
- path realization of the generic compositor;
- why a directed lax witness becomes an invertible pseudo witness in a path
  category; and
- the distinction among groupoidal closure, truncation, and free inversion.

Central checked claim: product path transport agrees with both coordinate
orders and with the existing structured `J`/`PathOut` presentations.

Secondary checked claim: the generic functor compositor has an invertible
Path realization with one retained higher action.

Target length: 2,500–3,300 words.

### Chapter 26 — The Circle And The Integer Line

Reader question: why does reversibility change the arithmetic answer from
natural numbers to integers?

Narrative:

- the successor telescope localization and transparent Integer facade;
- Circle formation, base, loop, induction, and the exact computation
  boundary;
- judgmental dependent loop computation versus propositional ordinary
  `ap` computation;
- the universal Integer cover and successor monodromy;
- integer-indexed positive and negative loop powers;
- endpoint-dependent encode/decode;
- the based-loop and categorical-Hom equivalences with Integer;
- a self-equivalence as Circle monodromy;
- mere connectedness and contractibility of the set truncation; and
- an explicit comparison with the HoTT Book proof architecture.

Central checked claim:

```text
Hom(Circle,Circle) ≃ Integer.
```

The prose must distinguish the intrinsic based-loop `TypeEquiv`, the
categorical `OmegaEquiv`, and the absence of a category-head rewrite.

Target length: 3,400–4,400 words.

### Chapter 27 — Free Inversion And Groupoidification

Reader question: can the Circle and interval be characterized by what maps
out of them do, rather than only by their constructors?

Narrative:

- the concrete WalkingEnd-to-Circle functor and its action on powers;
- restriction and extension against every groupoidal target;
- whole beta/eta and the monodromy consumer;
- the directed WalkingArrow and the two-endpoint groupoidal interval;
- dependent segment computation and the whole mapping theorem;
- category-indexed `Groupoidify(C)`, its whole unit, and computing recursor;
- the arbitrary-source mapping-object equivalence;
- the explicit nonidentity unit compositor and retained next action;
- recovery of `Groupoidify(WalkingArrow) ≃ Interval`; and
- why `Core`, truncation, and groupoidification have different variances and
  universal properties.

Central checked claim:

```text
Hom(Groupoidify(C),G) ≃ Functor(C,Path(G))
```

for arbitrary `C : Cat` and `G : Grpd` at the active fixed-forward whole
mapping boundary.

The chapter must state that source action, `Groupoidify_func`, and the
packaged adjunction with `Path_cat_func` remain deferred. It must not call the
current construction a completed functorial left adjoint.

Target length: 3,200–4,100 words.

### Chapter 28 — Laxity, Interchange, And The Gray Direction

Reader question: where does directed two-dimensional coherence live when it
is not collapsed to an equation?

Narrative:

- whole internal action before componentwise naturality;
- displayed laxity and its ordinary post/left and pre/right projections;
- the explicit compositor as an identity-transfor specialization;
- recursion through the next `homd_`/Sigma action;
- strict functors as computational codes inside a shared lax-capable action
  calculus;
- `GrayHom_lax` as a strict-object/lax-arrow profile;
- the selected right-closed transpose boundary;
- the four vertices and two coordinate directions of the walking square;
- the interchanger projected from existing laxity; and
- the exact boundary between this selected slice and a full Crans–Gray
  monoidal structure.

Central checked claim: the walking-square interchanger is a nonidentity
directed cell obtained from the whole internal-action owner and retains one
next action.

Target length: 2,700–3,600 words.

### Why four chapters

One combined chapter would conflate three different universal problems:
groupoidal closure of formers, free inversion of directed categories, and
Gray-style directed coherence. More than four chapters would make the book
follow the implementation chronology. Four gives each major theorem one
reader question and keeps the final edition near a 40–55 page expansion
rather than an open-ended manual.

## 7. Cross-Cutting Revision Map

### Front matter

- Update the edition notice, preface, reading paths, contents, and prologue
  road map from three spirals to four.
- Keep the WalkingEnd/Natural-number theorem as the first mathematical centre;
  present the Circle/Integer theorem as the deliberate return to its missing
  inverse powers.
- Do not announce a final non-draft edition before release review.

### Existing chapters

- Chapter 4: connect universe paths to Circle monodromy without duplicating
  Chapter 26.
- Chapter 5: retain the one-`J` architecture and forward-reference structured
  product transport.
- Chapter 6: distinguish selected Circle/interval/groupoidification HITs from
  a still-absent generic declaration compiler.
- Chapter 7: replace the stale reflector boundary with the classified
  `NType_cat`/`Trunc_ntype` construction and Circle connectedness consumer.
- Chapter 8: preserve the directed Nat proof, replace the false future
  Circle-comparison claim, and point to Chapters 26–27.
- Chapters 9 and 11: update the whole-laxity boundary and point to Chapter 28
  without importing implementation ledgers.
- Chapter 12: explain the mapping-object equivalence while keeping source
  functoriality and the adjunction deferred.
- Chapter 14: distinguish computational strict profiles from global strict
  endpoint cuts and from pseudo/lax higher cells.

### Appendices

- Appendix A: add only stable book notation for Circle, interval,
  groupoidification, and Gray profiles.
- Appendix B: remain generated from `evidence.json`.
- Appendix C: rewrite from a prospective comparison into an actual
  WalkingEnd/Circle and Nat/Integer comparison.
- Appendix D: add stable conceptual index entries and cross-references.
- Appendix E: state the exact runtime/propositional boundaries for Circle,
  interval, truncation, and generic groupoidification.
- Appendix F: update the implementation matrix and research boundary.
- Appendix G: add compact formal rules for the new selected HITs and whole
  mapping properties without reproducing kernel declarations line by line.

## 8. Evidence Architecture

Every checked theorem in Chapters 25–28 needs an evidence identifier with an
active owner and reviewer. Existing false entries must be replaced or
reclassified; they must not survive merely to preserve identifiers.

The planned evidence families are:

| Evidence family | Representative active owner | Reviewer |
| --- | --- | --- |
| path category and structured `J` | `emdash3_2.lp`, `emdash3_2_groupoidal_closure.lp` | `examples/groupoidal_structured_j_eq1.lp`, `examples/groupoidal_product_transport.lp` |
| path-realized pseudo-laxity | `emdash3_2_path_pseudo_laxity.lp` | `examples/path_pseudo_laxity.lp` |
| Integer facade and induction | `emdash3_2_integer_localization.lp` | `examples/integer_localization.lp` |
| Circle HIT and loop computation | `emdash3_2_circle_hit.lp` | `examples/circle_loop_space.lp`, `examples/circle_judgmental_loop_computation.lp` |
| Circle connectedness/truncation | `emdash3_2_truncation_reflector.lp`, `emdash3_2_circle_connectedness.lp` | `examples/computational_truncation_facade.lp`, `examples/circle_connectedness.lp` |
| WalkingEnd–Circle comparison and universality | `emdash3_2_walking_circle_*.lp` | corresponding `examples/walking_circle_*.lp` reviewers |
| interval and WalkingArrow universality | `emdash3_2_groupoidal_interval_hit.lp`, `emdash3_2_walking_interval_*.lp` | `examples/groupoidal_interval_hit.lp`, `examples/walking_interval_groupoidification.lp` |
| generic groupoidification | `emdash3_2_groupoidification_*.lp` | `examples/generic_groupoidification*.lp` |
| whole laxity surfaces | active owners in `emdash3_2.lp` | `examples/dependent_hom_laxity.lp` plus central diagnostics |
| selected Gray profile/closure/interchanger | `emdash3_2_gray_*.lp` | `examples/gray_*.lp` |

At minimum, the stale `TRUNC-REFLECTOR`, `WE-GROUP-COMPLETION`, and
`FUNCTORD-WHOLE-LAXITY` entries must be corrected. New claims should be
coarse enough to support prose, not one identifier per kernel helper.

## 9. Attribution And Research Sources

### HoTT Book

The pinned HoTT Book source is already registered under the same CC BY-SA
3.0 license. Extend its source/adaptation map before writing close adaptations
for:

- Circle induction and its universal property;
- the universal cover and encode/decode proof of
  `Omega(S1) ≃ Integer`;
- truncation and connectedness; and
- the comparison between reversible loop powers and directed powers.

Prefer fresh prose and explicit emdash differences. The chapter must not make
the HoTT proof appear to establish emdash's generic groupoidification or Gray
interfaces.

### Gray and higher-category references

Use primary sources already reviewed in the mathematical plans:

- Gurski for the low-dimensional Gray interchanger;
- Bourke–Gurski for the factorization perspective;
- Ara–Maltsiniotis for strict-omega lax/oplax internal homs and biclosed
  structure; and
- Hadzihasanovic for the combinatorics of higher-categorical diagram shapes.

Until a compatible reuse license is verified, treat these as mathematical
references and write fresh prose. The book must call the active construction
a selected profiled right-closed Gray slice, not the complete established
Crans–Gray tensor.

## 10. Concise Article Strategy

The article is secondary and remains bounded to 14–18 pages. It is already at
18 pages, so the update must replace and compress rather than append.

Required changes:

- revise the abstract and contributions list to include computational
  groupoidal realization;
- consolidate the current Circle/Integer paragraph into a short theorem-led
  section containing the whole WalkingEnd/Circle result, interval test, and
  generic mapping property;
- mention Gray only as the selected coherence stress test;
- update the research-boundary paragraph to defer source functoriality,
  adjunction packaging, full Gray monoidality, and global strict-cut migration;
  and
- keep all implementation-history and health metrics out of the main article.

If the article cannot remain at or below 18 pages without harming clarity,
reduce less central implementation exposition before requesting a page-budget
change.

## 11. Diagrams And Visual Design

Use diagrams only where they materially shorten an explanation:

1. a directed-to-groupoidal ladder connecting WalkingEnd/Nat with
   Circle/Integer;
2. the restriction/extension mapping-object equivalence for
   `Groupoidify(C)`; and
3. the walking square with its oriented interchanger.

Prefer the existing Arrowgram/Mermaid-capable renderer or accessible native
HTML/CSS/SVG owned by the book pipeline. Every figure needs useful alt text,
legible print contrast, a stable anchor, and a prose explanation. Decorative
AI imagery is not part of the mathematical pages.

## 12. Execution Ledger

| Row | Status | Deliverable and acceptance boundary |
| --- | --- | --- |
| `BGR-00` | complete | Create the dedicated branch/worktree at cumulative checkpoint `f4d9303`; bootstrap the pinned workspace; verify clean staged/unstaged state, ancestry, and `workspace:check`; run the green 39-source/141-evidence `book:check`; audit current chapters, article, evidence, provenance, and the 299-page artifact; record the fourth-spiral architecture and exact non-claims. |
| `BGR-ARCH-1` | complete | `book.json` and `expansion.json` now extend contiguously through Chapters 25–28. Four stable anchored chapter owners contain reader-facing theorem previews and exact boundaries; four coarse checked evidence entries point to active owners/reviewers. A real provenance-growth consumer generalized the checker's fixed 13-entry assumption to a nonempty/unique/well-formed contract with focused tests. Release metadata remains at 0.4.0-dev. `book:check` passes for 43 sources and 145 evidence claims. |
| `BGR-REPAIR-2` | complete | Corrected the stale truncation-reflector, WalkingEnd–Circle free-inversion, and whole-laxity evidence/status boundaries; repaired Chapters 4, 6–9, 12, and 14 plus Appendices C, D, and F; registered the Chapter 26 HoTT adaptations; preserved the directed Nat theorem's original strength. Focused architecture tests pass 5/5, `book:check` passes at 2,410 math spans, the browser render is green at 313 pages, and the review-only PDF passes at 313 pages/16 fonts with representative pages visually inspected. |
| `BGR-CH25-3` | complete | Chapter 25 is a 2,783-word theorem-led account of the Path-category bridge, homwise product closure, the product-transport diamond, agreement of structured transport and `PathOut` with primitive right-J, and target-induced pseudo-laxity. Two focused evidence claims separate product split/join and path-realized compositor strength. `book:check` passes at 147 cited claims/2,478 math spans; the 319-page review PDF passes with 16 embedded fonts, and all seven Chapter 25 pages were inspected with Poppler. |
| `BGR-CH26-4` | complete | Chapter 26 is a 3,748-word proof-led account of successor-localized Integer, judgmental dependent Circle-loop computation, universal-cover encode/decode, intrinsic and categorical loop-space equivalences, arbitrary self-equivalence monodromy, and connectedness/set-truncation. Four focused evidence claims supplement the central Circle/Integer theorem and the HoTT adaptation boundary is explicit. `book:check` passes at 151 cited claims/2,580 math spans; the 328-page review PDF passes with 16 embedded fonts, and all ten Chapter 26 pages were inspected with Poppler after three crowded displays were repaired. |
| `BGR-CH27-5` | complete | Chapter 27 is a 3,667-word progression from WalkingEnd/Circle and WalkingArrow/Interval to arbitrary category-indexed groupoidification, including whole units, computation, target extension/restriction, beta/eta, the explicit unit compositor and next action, generic Interval recovery, and a variance comparison with Core/truncation. Two focused evidence claims supplement the reused WalkingEnd and generic claims. `book:check` passes at 153 cited claims/2,683 math spans; the 336-page review PDF passes with 16 embedded fonts, and all nine Chapter 27 pages were inspected after repairing one clipped continuation, an overwide table, and a stranded final fragment. |
| `BGR-CH28-6` | complete | Chapter 28 is a 3,089-word derivation from whole internal laxity through computational strict-functor codes, the shared strict-object/lax-arrow profile, one selected right closure, coevaluation-derived walking square, and an oriented nonidentity interchanger with retained next action. Two focused evidence claims supplement the whole-laxity and interchanger records; Hadzihasanovic's Gray-product/oriented-cube source is registered as comparative reference only. `book:check` passes at 155 cited claims/2,740 math spans; the 343-page review PDF passes with 16 embedded fonts, and all eight Chapter 28 pages were inspected with Poppler. |
| `BGR-XCUT-7` | complete | Front matter and transitions now present four spirals; notation, HoTT correspondence, glossary, computation/status/formal appendices, credits, bibliography, and provenance agree with Chapters 25–28 and their exact non-claims. Generated contents/evidence remain owner-generated. A book-only table pagination rule removes inherited title-only table pages without changing article layout. `book:check` passes at 43 sources/155 claims/2,775 math spans; renderer checks pass for the 18-page article and 343-page book; the review PDF passes at 343 pages/16 fonts and representative changed pages were inspected. |
| `BGR-ARTICLE-8` | complete | Rebalanced rather than appended: one over-detailed mixed-telescope passage now funds a theorem-level groupoidification/Gray subsection; the abstract, roadmap, boundaries, conclusion, and references agree. The article remains 18 pages, passes its release gate with 14 embedded fonts, and is byte-deterministic across two exports. Poppler QA repaired two overwide displays and a split reference. The checked owner pair is promoted byte-identically to `docs/emdash3_2.{md,pdf}`. |
| `BGR-RELEASE-9` | complete | Stabilized the book at expanded development edition `0.5.0-dev`, dated 2026-08-18 with draft status. Two complete cold `book:release` passes produced the same 343-page/16-font hash. Final Poppler QA covered metadata/title, contents, all new chapter openings, transport and walking-square figures, status/evidence/formal tables, appendices, bibliography, credits, and license. The checked Markdown/PDF pair is promoted byte-identically to `docs/emdash-book.{md,pdf}`. |
| `BGR-CLOSE-10` | active | Synchronize this plan, parent `ILGR-BOOK-1`, report index, public README/status claims, exact artifact hashes/page counts, and clean staged scope. Run no unrelated kernel/TypeScript aggregates; carry forward `f4d9303` semantic health unless a semantic source changes. Leave remote publication for explicit authorization. |

### 12.1 Architecture Implementation Record — 2026-08-18

The first implementation row changes only structured book sources:

- the manifest appends Chapters 25–28 before the appendices;
- the architecture contract records a distinct conceptual owner, prior
  spiral dependencies, checked central theorem, and explicit boundary for
  each chapter;
- each chapter begins with one stable anchor, a mathematical question,
  theorem preview, checked evidence marker, and scope note rather than an
  empty placeholder;
- `evidence.json` adds four reader-scale claims for product transport,
  Circle/Integer, generic groupoidification, and the Gray interchanger; and
- the edition version/date/status and output artifact name remain unchanged
  until the prose architecture stabilizes.

The existing `deriveNumberedChapterContract` already derives its final
chapter and expansion count from the manifest, and its tests already cover
later appended chapters. The first provenance expansion exposed one separate
fixed-count assumption in `check_book.mjs`. Its owner is now generalized to a
nonempty, unique, well-formed requirement list, with focused tests accepting
13, 15, and 28 entries and rejecting absent, duplicate, and malformed lists.
No rendering behavior changed.

The owning gate is green:

```text
book:check
  43 assembled source files
  145 checked/cited evidence identifiers
  2,394 typography and KaTeX math spans
  source, provenance, architecture, link, and document validation: passed
```

`BGR-REPAIR-2` therefore became active before any chapter was expanded. This
ordering prevents the new prose from coexisting with known false future-work
claims in the earlier reader path.

### 12.2 Stale-Claim And Provenance Repair Record — 2026-08-18

Three former research-boundary identifiers are now checked at their current
owners:

- `TRUNC-REFLECTOR` records classified `NType_cat` formation, restricted
  elimination, and whole map action;
- `WE-GROUP-COMPLETION` records the concrete whole WalkingEnd–Circle mapping
  theorem without claiming a reverse `BNat` functor or monoid package; and
- `FUNCTORD-WHOLE-LAXITY` records the whole displayed owner, ordinary
  post/pre surfaces, and functor-compositor specialization without claiming
  all-coherence or completed strict-cut migration.

The corresponding false future-work statements are removed from Chapters
7–9, Appendix C, Appendix D, and the status matrix. Short bridges in Chapters
4, 12, and 14 locate Circle monodromy, the target-side groupoidification
mapping equivalence, and computational strict-functor profiles without
duplicating the future chapters. Chapter 6 now distinguishes the selected
groupoidal interval from a still-absent generic directed-HIT compiler.

The HoTT provenance map now registers the Chapter 26 Circle-HIT and universal-
cover adaptations before full proof prose is written. The credits and
Chapter 7 adaptation description are synchronized.

Validation is proportional and green:

```text
book architecture tests: 5/5
book:check: 43 sources, 145 cited claims, 2,410 math spans
book:render: 313 pages, no console/page/request/render failure
book:pdf:check: 313 pages, 16 embedded fonts
review PDF sha256: a23d9b97c7ba297eb8f6b94e80f089f7cdd9f1fb3748f89632ea2159efab70d3
```

Pages containing the repaired Chapter 7 reflector, Chapter 8 free-inversion
comparison, Chapter 9 laxity boundary, Chapter 12 mapping equivalence,
Chapter 14 strict-profile table, Appendix C comparison, and all four new
chapter openings were rendered with Poppler and visually inspected. The PDF
is a local review artifact under unchanged 0.4.0-dev metadata; it is not
promoted or released.

### 12.3 Chapter 25 Record — 2026-08-18

Chapter 25 now occupies seven pages and 2,783 source words. Its exposition is
organized around three checked theorems rather than module chronology:

1. the canonical comparison from `Path(A x B)` to
   `Path(A) x Path(B)` is judgmentally identity on objects and an explicit
   split/join equivalence on each hom;
2. direct product transport agrees with both sequential coordinate orders,
   and the two comparisons induce the expected coherence diamond; and
3. the generic compositor of `Path(f)` is an equality between paths, gains an
   inverse by symmetry, compares propositionally with its readable
   `ap`/concatenation endpoints, and retains one next hom action.

The chapter uses those results to distinguish groupoidal closure, truncation,
and free inversion before handing the reader to the Circle calculation. It
states explicitly that the product comparison is not promoted to a category-
head conversion or whole equivalence, that structured transport comparisons
are propositional rather than competing runtime rules, and that retained
higher action is not a complete weak-omega-groupoid theorem.

Two focused evidence records were added:
`GROUPOIDAL-PRODUCT-CLOSURE` and `PATH-PSEUDO-LAXITY`. No Lambdapi,
TypeScript, renderer, package, or release semantics changed. The preceding
local checkpoints are `bbc7ffd` for architecture, `e53dbaa` for stale-
claim/provenance repair, and `54bfd4a` for Chapter 25.

Proportional validation is green:

```text
chapter source words: 2,783
book:check: 43 sources, 147 cited claims, 2,478 math spans
book:render: no console/page/request/render failure
book:pdf:check: 319 pages, 16 embedded fonts
review PDF sha256: 363d1386097d807140e64d2e98e371d74a773a0da97204d3ece8a1c354f26a1b
```

Poppler review covered every Chapter 25 page, 198–204. The opening, equations
(25.1)–(25.20), three formal-status boxes, transport diamond, page breaks,
final synthesis, and Chapter 26 transition are legible, uncropped, and free
of accidental blank or sparsely stranded pages. The PDF remains an ignored
review artifact under unchanged 0.4.0-dev metadata; promotion belongs only to
`BGR-RELEASE-9`.

### 12.4 Chapter 26 Record — 2026-08-18

Chapter 26 now occupies ten pages and 3,748 source words. It follows the HoTT
Book's Circle and universal-cover encode–decode architecture under explicit
attribution while changing the computational centre of gravity:

- Integer is the transparent set-truncated telescope localization of Nat
  successor, with stage representatives `[n,x]`, inverse shift, univalence
  path, and set-targeted elimination;
- Circle point and canonical dependent loop action both compute
  judgmentally, while the ordinary `ap` loop equation remains propositional;
- the code family has Integer base fibre and successor monodromy;
- endpoint-dependent encode and decode are inverse, yielding both intrinsic
  `TypeEquiv` and separate whole categorical `OmegaEquiv` presentations;
- arbitrary self-equivalences produce Circle monodromy and recover their
  WalkingEnd representation under restriction; and
- mere connectedness proves the classified set truncation contractible
  without replacing its carrier by Unit.

Four focused evidence records were added:
`INTEGER-LOCALIZATION-LINE`, `CIRCLE-HIT-COMPUTATION`, `CIRCLE-MONODROMY`,
and `CIRCLE-CONNECTED-TRUNCATION`. The central
`CIRCLE-LOOP-INTEGER` record remains the owner of the endpoint-dependent
round trips and the intrinsic/categorical equivalence packages. No semantic,
renderer, package, or release source changed.

Proportional validation is green:

```text
chapter source words: 3,748
book:check: 43 sources, 151 cited claims, 2,580 math spans
book:render: 328 pages, no console/page/request/render failure
book:pdf:check: 328 pages, 16 embedded fonts
review PDF sha256: bd0879203a1be8a5f678e6e9446ba05dee9ad428add579e3a47796f8802653e4
```

Poppler review covered every Chapter 26 page, 205–214. The first review found
crowded equation tags at (26.14), (26.17), and (26.29); all three displays
were converted to aligned multi-line forms and re-inspected. The opening,
equations (26.1)–(26.32), attribution/status boxes, comparison table, page
breaks, and Chapter 27 transition are now legible and uncropped. One final PDF
attempt reached the existing 90-second pagination ceiling; cleanup completed
and one bounded retry passed without changing the timeout. The PDF remains an
ignored review artifact under unchanged 0.4.0-dev metadata.

The Chapter 26 prose/evidence checkpoint is `258585c`.

### 12.5 Chapter 27 Record — 2026-08-18

Chapter 27 now occupies nine pages and 3,667 source words. It develops the
universal property through three scales:

1. WalkingEnd maps to the Circle, positive powers agree, and whole
   restriction/extension classify path-valued one-point representations;
2. WalkingArrow maps to the two-endpoint Interval, whose judgmental
   dependent-segment computation and whole mapping theorem test endpoint
   variation; and
3. arbitrary `C : Cat` has category-indexed `Groupoidify(C)`, one whole unit,
   a recursor computing on represented objects and dependent first cells,
   target-varying whole extension/restriction, beta/eta, an explicit
   nonidentity path-valued compositor, and retained next actions.

The fixed-forward arbitrary-source mapping theorem is stated at full mapping-
category strength without calling it object-only. The chapter separately
records the missing source action, `Groupoidify_func`, and adjunction package.
Specialization at WalkingArrow recovers the independently formed Interval by
explicit inverse maps and cancellation paths. A compact comparison table
distinguishes free inversion from Core and truncation without claiming an
unimplemented three-adjunction chain.

Two focused evidence records were added:
`WALKING-INTERVAL-GROUPOIDIFICATION` and
`GROUPOIDIFICATION-INTERVAL-RECOVERY`. The chapter also reuses the checked
`WE-GROUP-COMPLETION` and `GENERIC-GROUPOIDIFICATION-MAPPING` records. No
Lambdapi, TypeScript, renderer, package, or release semantics changed.

Proportional validation is green:

```text
chapter source words: 3,667
book:check: 43 sources, 153 cited claims, 2,683 math spans
book:pdf:check: 336 pages, 16 embedded fonts
review PDF sha256: 1ed14fb5f4293221469bd2c8b2295da90c391febb32d1cbdb711b087351e6782
```

The owning full browser render passed all source/evidence/typography/KaTeX
checks and completed its build, then reached the existing 90-second console-
pagination ceiling without a reported content error. A clean direct PDF
export, which performs its own pagination and browser-error gate, passed and
produced the checked artifact above. Poppler review covered every Chapter 27
page, 215–223. It found a clipped continuation at the original page 222, an
overwide four-column table whose tag crowded its final cell, and a two-line
stranded final verso. Substantive reflow, a three-column table, and a tightened
transition repaired all three; the final pages were re-exported and
re-inspected. The PDF remains an ignored 0.4.0-dev review artifact.

The Chapter 27 prose/evidence checkpoint is `0757d37`.

### 12.6 Chapter 28 Record — 2026-08-18

Chapter 28 now occupies eight pages and 3,089 source words. It follows one
checked chain rather than presenting Gray terminology as a feature catalogue:

```text
whole displayed/internal laxity
  -> ordinary post/left and pre/right surfaces
  -> functor compositor
  -> computational strict-functor codes
  -> strict-object/lax-arrow GrayHom profile
  -> one selected right closure
  -> coevaluation-derived I tensor I square
  -> oriented nonidentity interchanger
  -> one retained next action
```

The chapter distinguishes a path-valued pseudo constraint from computational
strictness, reuses the ambient transformation/modification tower rather than
duplicating it, and states the typed post/left cell direction as the authority
for the lax naming. Its exact non-claim includes the mirror closure, tensor
functoriality, associativity/unit coherence, full Crans–Gray biclosed monoidal
structure, and global migration of historical strict endpoint cuts.

Two focused evidence records were added: `GRAY-COMPUTATIONAL-PROFILE` and
`GRAY-RIGHT-CLOSURE`. The chapter also reuses `FUNCTORD-WHOLE-LAXITY` and
`GRAY-WALKING-INTERCHANGER`. Amar Hadzihasanovic's
*Combinatorics of higher-categorical diagrams*, arXiv:2404.07273v2, is now a
bibliographic/comparative reference for Gray products and oriented cubes;
its arXiv license and exact section map are recorded with no textual
adaptation claim. No semantic, renderer, package, or release source changed.

Proportional validation is green:

```text
chapter source words: 3,089
book:check: 43 sources, 155 cited claims, 2,740 math spans
book:render: 343 pages, no console/page/request/render failure
book:pdf:check: 343 pages, 16 embedded fonts
review PDF sha256: 0defe20cd69ee11e395c34776a51a9b16df016aa2138f309a98ee3645e8a9b2a
```

Poppler review covered every Chapter 28 page, 224–231. The wrapped chapter
title, equations (28.1)–(28.16), four formal-status boxes, right-closure
display, walking-square diagram, interchanger, research-boundary list, final
comparison table, and fourth-spiral transition are legible and uncropped.
The initially sparse closing page was filled with a concise reusable
whole-owner/profile/consumer discipline and re-inspected. The PDF remains an
ignored 0.4.0-dev review artifact.

### 12.7 Cross-Cutting Integration Record — 2026-08-18

The edition now reads as four conceptual spirals everywhere a reader enters
or navigates the book:

- the edition notice, preface, reading guide, prologue road map, and Chapter
  24 transition introduce the path/Circle/groupoidification/Gray return
  without displacing the WalkingEnd/Nat theorem as the first centre;
- the manifest-generated contents expose Chapters 25–28 without a manually
  edited duplicate;
- Appendix A adds only stable fourth-spiral notation;
- Appendix C now follows the analogy in both directions, from Circle/Integer
  to WalkingEnd/Nat and back through checked free inversion;
- Appendix D adds Circle, compositor, Integer, Interval, groupoidification,
  selected Gray profile, interchanger, laxity, and path-realized
  pseudo-laxity as conceptual entries;
- Appendix E states the exact distinction among dependent constructor beta,
  propositional ordinary `ap`, whole mapping-object beta/eta, and
  profile-local strictness;
- Appendices F and G synchronize the status matrix, selected groupoidal HIT
  rule packages, category-indexed mapping property, whole laxity, and the
  one-sided Gray boundary; and
- credits and source provenance identify Hadzihasanovic as comparative
  bibliography only, with no textual adaptation or full Crans–Gray claim.

Appendix B remains generated from the evidence register. The final stale scan
finds no three-spiral or prospective generic-groupoidification claim in the
structured book sources. References to the *third* spiral now mark its actual
beginning and end rather than the size of the whole edition.

Visual review exposed one inherited renderer defect: long book tables were
moved off their opening page even though they were subsequently split. The
book-only table rule now permits splitting between retained rows, so Appendix
A and other long tables begin beneath their headings. The article-specific
table layout is unchanged. This reclaimed four otherwise sparse pages, keeping
the expanded review artifact at 343 pages despite the new cross-cutting prose.

Proportional validation is green:

```text
book:check: 43 sources, 155 cited claims, 2,775 math spans
renderer registry/architecture tests: 14/14
validate:paper: article and book passed
check:render: article 18 pages; book 343 pages; no console/page/request/render errors
book:pdf:check: 343 pages, 16 embedded fonts
review PDF sha256: 98cf977b2f8f70a35f2f8830fee3521e5940861b7849f1c0d1098c7c8a9a9b51
```

Poppler review covered the edition notice, fourth-spiral preface, reading-path
table, generated contents, prologue and Chapter 24 transitions, notation
table, revised HoTT correspondence, every new glossary-entry page, computation
and status additions, both new formal-presentation sections, and the updated
credits. The review PDF remains ignored under unchanged 0.4.0-dev metadata;
artifact promotion belongs to `BGR-RELEASE-9`.

### 12.8 Concise Article Record — 2026-08-18

The overview article remains a concise architecture paper rather than a
miniature copy of the book. Its 8,929 words and 18 pages now include the
fourth-spiral results by replacement:

- the abstract and opening claim add the target-side universal mapping
  property of `Groupoidify(C)` and name the profiled Gray interchanger;
- a duplicated implementation-level mixed-telescope walkthrough is
  compressed while retaining the decisive object/action validation;
- §8.4 now moves from Path-product closure and Circle computation through the
  WalkingEnd/Circle and WalkingArrow/Interval tests to the arbitrary-source
  mapping-object equivalence;
- the same subsection derives the compositor from whole laxity, distinguishes
  path-induced pseudo behaviour from computational strict codes, and states
  the selected right Gray closure and walking interchanger;
- the research-boundary list now defers source functoriality and adjunction
  packaging rather than the already-active generic object/mapping boundary,
  and separately defers full Gray monoidality and strict-cut migration; and
- the conclusion and bibliography include the groupoidal payoff and
  Hadzihasanovic comparison without importing implementation chronology.

The first visual pass found two display equations exceeding a two-column
measure—the groupoidification mapping equivalence and the Gray right closure.
Both now use aligned two-line layouts. It also found a bibliography item split
between columns; the citation was tightened without losing its artifact role.
The abstract, compressed mixed-telescope page, §8.4, research boundaries,
conclusion, and references were re-rendered with Poppler and inspected.

Validation and promotion evidence:

```text
article source: 8,929 words
article:check: 14 registry/architecture tests; Markdown/math validation passed
article:render: 18 pages; no console/page/request/render errors
article:pdf:check: 18 pages, 14 embedded fonts
two consecutive PDF hashes: d5ef1d47aa693229e92f52ae84e762d36b620912bf3b16e178456ab3448ed3db
promoted Markdown sha256: b30908661134c2c9dcb6619cb5c6752658e35875fdb6bbfd859fbd5b8fd9f935
promoted PDF sha256: d5ef1d47aa693229e92f52ae84e762d36b620912bf3b16e178456ab3448ed3db
```

`docs/emdash3_2.md` and `docs/emdash3_2.pdf` are byte-identical to the checked
article owner and generated PDF. Their 0.2.0-dev research-draft metadata is
unchanged; local promotion is not remote publication.

### 12.9 Local Book Release And Promotion Record — 2026-08-18

The manifest now owns the stabilized groupoidal-realization snapshot:

```text
edition: expanded development edition
version: 0.5.0-dev
publication date: 2026-08-18
status: draft
generated PDF: output/pdf/functorial-type-theory-0.5.0-dev.pdf
```

The explicit draft status is retained: this is a new checked development
edition, not a claim of external peer review or a final foundation. The
versioned output path preserves the completed 0.4.0 comparison rather than
overwriting its identity in the manifest.

Two complete cold `book:release` passes independently repeated assembly,
evidence/provenance/source validation, typography and KaTeX checks, TypeScript
build, bounded browser pagination, console/page/request/render checks, PDF
export, metadata normalization, `qpdf` verification, extracted-text checks,
blank-page checks, and font inspection. Both produced exactly:

```text
pages: 343 US Letter, tagged
embedded fonts: 16
PDF bytes: 3,013,229
PDF sha256: 54a11407eb9ca1203979413f3231003ada85021ef2578e247ab922fccd918ad7
```

Final Poppler QA covered pages 1–2; both contents pages; all four new chapter
openings; the product-transport diamond; the Gray walking square and
interchanger theorem; notation and generated-evidence tables; the revised
HoTT correspondence, glossary, computation, status, and formal-presentation
appendices; bibliography; both credit pages; and the license. This complements
the earlier all-page review of Chapters 25–28. No clipping, overlap, accidental
blank page, malformed table, stranded fragment, or unreadable status block was
found.

Local promotion is byte-identical to the checked owners:

```text
docs/emdash-book.md sha256: e26fcb960a5dae0abd24a106035fa79a45f570a1c77edfa33727c6b0d0127604
docs/emdash-book.pdf sha256: 54a11407eb9ca1203979413f3231003ada85021ef2578e247ab922fccd918ad7
```

No Lambdapi or TypeScript semantic source changed. In accordance with the
goal's proportional-validation policy, the prior `f4d9303` semantic health
boundary is carried forward and the long repository/kernel aggregate was not
rerun merely for document release. Local promotion is not a push, tag, PR,
deployment, or remote publication.

## 13. Proportional Validation Policy

### Planning and architecture changes

- exact diff and JSON validation;
- report header/reference lint;
- `workspace:check` when package boundaries are implicated;
- `book:check`; and
- the focused book-architecture unit test if its owner changes.

### Each prose/evidence tranche

- `book:assemble` and freshness check;
- evidence registry check;
- semantic typography and KaTeX checks;
- `book:check`;
- focused rendering of affected chapter pages; and
- Poppler page-image inspection of the changed transitions, figures, display
  mathematics, status boxes, headers, and footers.

Pure prose does not require Lambdapi or TypeScript aggregates. A disputed
claim may trigger the nearest focused source/reviewer check, each bounded by
the existing 90-second policy. Carry forward the exact green 208-target
kernel health boundary when semantic sources remain unchanged.

### Local release

- `book:release` twice from clean generated state and equal SHA-256 hashes;
- `article:release` and page-budget verification;
- `book:promote` and `article:promote` only from checked owners;
- byte equality between tracked distributions and generated owners;
- `qpdf`, Poppler metadata/text/font/blank-page checks;
- final page-image QA; and
- no repository-wide aggregate unless a changed cross-layer contract makes
  its omission a genuine blocker.

Remote publication has its own authorization and may impose an additional
integration gate.

## 14. Risks And Guards

### Risk: the fourth spiral becomes a kernel report

Guard: organize each chapter around a question and theorem. Put source names
in evidence notes; omit checkpoint chronology, warning counts, and rule LHS
details from the mathematical line.

### Risk: the Circle proof simply duplicates the HoTT Book

Guard: use the HoTT proof as an attributed expository template, but emphasize
the exact emdash computation boundary, telescope-localized Integer, whole
categorical action, and comparison with directed WalkingEnd.

### Risk: groupoidal closure, truncation, and groupoidification blur together

Guard: give each its own universal direction and a comparison table in
Chapter 27. `Core` retains invertible arrows, truncation lowers homotopy
level, and `Groupoidify` freely realizes directed arrows as paths.

### Risk: the generic construction is overstated as a completed adjunction

Guard: state the active arbitrary-`C`/`G` mapping-object equivalence and
computing unit/recursor; mark source action, `Groupoidify_func`, and adjunction
packaging deferred wherever the theorem is summarized.

### Risk: Gray terminology overclaims the implementation

Guard: use “selected profiled right-closed Gray slice.” State the absent
mirror closure, tensor functoriality, associativity/unit data, full
biclosedness, and monoidal coherence.

### Risk: stale old chapters contradict new chapters

Guard: make the stale-claim inventory a blocking row before final chapter
closeout; search for every future/not-yet occurrence in the affected concept
families and classify it individually.

### Risk: article growth breaks concision

Guard: treat 18 pages as a hard initial ceiling and replace lower-value detail
rather than append.

### Risk: visual QA waits until the end

Guard: render each chapter at its own checkpoint and inspect page images. The
final release reruns representative whole-book inspection rather than being
the first visual review.

## 15. Persistent Goal Objective

```text
In the authorized dedicated worktree
/home/user1/emdash1-book-groupoidal-v3.2 on branch
goal/emdash-book-groupoidal-v3.2, complete
EMDASH-BOOK-GROUPOIDAL-REALIZATION-EDITION-V0.5 according to the living plan
docs/EMDASH_BOOK_V3_2_GROUPOIDAL_REALIZATION_EXPANSION_PLAN_2026-08-18.md
and the active book/print contracts. Preserve the completed 0.4.0 edition and
build a globally coherent fourth spiral through Chapters 25–28: Paths and the
groupoidal shadow; the Circle and Integer line; free inversion and generic
groupoidification; and laxity/Gray interchange. Correct stale earlier
chapters and evidence, update front matter and appendices, rebalance the
concise article within its 18-page maximum, and produce deterministic locally
promoted book/article artifacts with page-image QA. Treat the book as
theorem-led mathematical prose, not a developer report. Follow proportional
checks, preserve exact formal-status boundaries, and use authorized local
green checkpoint commits. Do not change mathematical or TypeScript semantics,
run unnecessary long aggregates, push, merge, publish remotely, tag, rewrite
history, delete branches, or remove worktrees.
```

## 16. Completion Definition

The goal is complete only when:

- all ledger rows are complete, rejected with durable evidence, or explicitly
  deferred behind an accepted concrete prerequisite;
- Chapters 25–28 form one coherent fourth spiral and each has a clear reader
  question, proof architecture, checked central theorem, and honest boundary;
- every affected stale claim in earlier chapters/appendices is corrected;
- evidence, provenance, bibliography, notation, glossary, contents, reading
  paths, and formal-status notes agree with active sources;
- the article remains concise and accurately states the new boundary;
- deterministic book and article releases pass their owners;
- final PDFs receive visual page-image review with no layout defect;
- tracked `docs/` artifacts are byte-identical to their checked owners;
- the worktree is clean at reviewed local checkpoints; and
- remote publication remains untouched unless separately authorized.
