# Emdash Book And Article Dependent-Simplex Expansion Plan

Date: 2026-08-21 (America/Toronto)

Plan-ID: `BOOK-DEPENDENT-SIMPLEX-EXPANSION-V3.2`

Status: **completed implementation, integration, and deployment plan**.

Branch: `goal/emdash-book-simplicial-v3.2`

Worktree: `/home/user1/emdash1-book-simplicial-v1`

Baseline: completed variable-dimensional ordinal-simplex checkpoint
`a70ea4440101f38ba0a4e068f472f14ec23f4d67`.

Integrated release checkpoint:
`6b85c2fd991b5ada7282f713a5ce34215d0c0a74`.

GitHub Pages deployment: successful run
[`32532377691`](https://github.com/hotdocx/emdash/actions/runs/32532377691)
at <https://hotdocx.github.io/emdash/>.

Primary artifacts:

- `docs/emdash-book.pdf`;
- `docs/emdash3_2.pdf`.

The mathematical implementation is already complete at the selected boundary.
This plan governs editorial architecture, evidence traceability, deterministic
artifact production, visual review, local Git checkpoints, final integration,
GitHub push, and affected deployment verification. It does not authorize new
kernel semantics merely to simplify exposition.

## 1. Objective

Extend *Functorial Type Theory: Univalent Foundations for Mathematics* with a
theorem-led account of the newly checked simplicial substrate and the
variable-dimensional dependent-simplex construction. Update the concise
overview article with the same result at article scale.

The exposition must answer one mathematical question:

> Can the combinatorial standard simplex and its faces be realized internally
> through the dependent-hom structure already present in functorial type
> theory, with computation and higher action retained?

The checked answer is positive at the following precise boundary:

1. augmented injective face codes compute and form an internal
   semi-simplex category;
2. directed ordinal shapes `Delta[n]` are built recursively by adjoining one
   terminal vertex with directed join;
3. a native dependent simplex is a flag of outgoing-path categories, so every
   successor step is another `PathOut` or, equivalently, another canonical
   `homd_`/Sigma layer;
4. intrinsic dependent-simplex codes decode to those native categories rather
   than reimplementing their semantics;
5. nonempty faces act by whole functors and retain higher action;
6. a canonical ordinal source is computed internally for variable `n`, maps
   under every `H : Functor(Delta[n],C)`, and has selected computations checked
   through dimensions zero to four; and
7. the tetrahedron and four-simplex expose the expected lower faces and a
   retained next action.

The book must present these as mathematics, not as a module inventory or an
internal development report.

## 2. Authority And Recovery Order

Use the following authority chain:

1. active Lambdapi declarations and focused reviewers on this branch;
2. `emdash2/AGENTS.md`, the current SOP, Foundations, and canonical syntax;
3. the completed implementation plans for the simplicial substrate,
   dependent-hom simplexes, coherent-nerve bridge, ordinal tetrahedron, and
   ordinal dimension-four recursion;
4. this living editorial plan and its ledger; and
5. archived Infinity Codex responses only as recovery evidence.

The principal implementation authorities are:

- `emdash3_2_semisimplicial_face_codes.lp` and
  `emdash3_2_semisimplicial_index.lp`;
- `emdash3_2_simplex_shapes.lp`, `emdash3_2_face_realization.lp`, and
  `emdash3_2_semisimplicial_diagrams.lp`;
- `emdash3_2_dependent_simplex_bridge.lp`,
  `emdash3_2_dependent_simplex_codes.lp`, and
  `emdash3_2_dependent_simplex_faces.lp`;
- `emdash3_2_pathout_transformation_lift.lp` and
  `emdash3_2_ordinal_join_pathout_successor.lp`;
- `emdash3_2_dependent_simplex_ordinal_dimension4.lp`; and
- `emdash3_2_dependent_simplex_ordinal_recursive.lp`.

## 3. Editorial Thesis And Chapter Placement

Add one numbered chapter after Chapter 28, provisionally titled:

> **Simplexes From Dependent Homs**

This placement is deliberate. Chapter 17 introduces directed join; Chapters
25--27 compare directed cells with paths and free groupoidal realization; and
Chapter 28 recovers a directed interchanger from whole internal laxity. The new
chapter uses those same owners recursively. It therefore closes the higher
categorical spiral by showing how a simplex can be built from a base cell, a
dependent cell above it, and the next whole action.

Do not insert a long source-oriented subsection into Chapter 17 or Chapter 28.
Use short backward links there only if the new chapter needs them. Generated
contents must own the chapter list.

The chapter's narrative order is:

1. the simplex as a mathematical shape, not first as a code;
2. injective faces and the augmented semi-simplex category;
3. outgoing paths as the recursive native simplex former;
4. the triangle and tetrahedron as the first dimensions where dependent
   structure becomes visible;
5. the ordinal realization and the four faces of a tetrahedron;
6. intrinsic codes as an internal recursion device subordinate to the native
   semantics;
7. the variable-dimensional ordinal source and its structural successor;
8. the five faces of the four-simplex and retained higher action; and
9. the exact boundary beyond the result.

Use no line-by-line Lambdapi walkthrough. Kernel identifiers belong in compact
formal-status notes and the evidence register.

## 4. Mathematical Presentation

### 4.1 Three simplex presentations

Keep these presentations distinct and relate them explicitly:

| Presentation | Mathematical role | Active owner |
| --- | --- | --- |
| `Delta[n]` | the finite ordinal category with `n+1` vertices | `DirectedSimplex_cat(n)` |
| standard semisimplex | the representable presheaf `Hom(-,[n])` on injective faces | `StandardSimplex(succ n)` |
| dependent simplex | a recursively flagged outgoing-path object | `DependentSimplexCode`, its decoded category, and fixed native classifiers |

The first is a source shape, the second is its Yoneda view, and the third is a
native dependent normal form for a selected simplex. Do not identify them
judgmentally or conflate an object package with a mapping category.

### 4.2 Native recursion

The main mathematical recursion should be presented before the code layer.
For a category `C`, begin with

```text
S_0(C) = C.
```

After a flag object `s_n : Obj(S_n(C))` has been selected, continue by

```text
S_{n+1}(C,s_n) = PathOut_{S_n(C)}(s_n).
```

An object of the successor is a new endpoint together with an arrow from the
selected flag. Since `PathOut` is a Sigma of a representable hom, this is the
same base-cell-plus-dependent-cell pattern exposed by `homd_` and dependent
Sigma. Whole functor and transfor action, rather than a separate coherence
record, propagate the recursion.

### 4.3 Tetrahedral geometry

The tetrahedron must make the recursive geometry readable. A dependent
triangle has a base arrow and a fibre arrow above transport. An arrow between
two such triangles is a tetrahedral cell. Besides its ordinary source and
target triangles, two whole projections expose:

- the base surface; and
- the endpoint-action surface.

This gives the four faces `012`, `013`, `023`, and `123` without postulating a
standalone tetrahedron filler. The next hom action remains available.

### 4.4 Structural ordinal successor

For the canonical ordinal source, the successor must be explained through one
whole transformation stage. If the previous source is `s`, a stage supplies
two whole maps `F,G` and a transformation `epsilon : F => G`; then

```text
code'   = step(code,F[s]),
source' = (G[s],epsilon[s]).
```

The first stage comes from the identity extension of `Delta[n] * 1`; each
later flag lifts the same transformation through `PathOut`. Nat recursion
therefore produces one internal canonical source for variable `n`, not a
source-text generator and not a second omega-category theory.

## 5. Exact Formal Claims

Register a small evidence set before or with prose:

1. `SEMISIMPLICIAL-FACE-SUBSTRATE` -- computing injective face codes,
   internal index category, ordinal shapes, representable standard
   semisimplices, and whole diagram realization;
2. `DEPENDENT-SIMPLEX-INTERNAL-ACTION` -- the homd_/Sigma triangle,
   tetrahedron map, base and endpoint face projections, visible higher
   constructor, and retained action;
3. `ORDINAL-DEPENDENT-FOUR-SIMPLEX` -- one canonical ordinal four-simplex,
   arbitrary-target mapping, five coface observations, selected profiles,
   noncollapse, and retained action; and
4. `ORDINAL-DEPENDENT-SIMPLEX-RECURSION` -- the intrinsic Nat-indexed source,
   structural successor, arbitrary-target observation, generic nonempty-face
   access, checked dimensions zero through four, and retained next action.

The central theorem for Chapter 29 is
`ORDINAL-DEPENDENT-SIMPLEX-RECURSION`; the other three are secondary checked
evidence.

## 6. Explicit Nonclaims

The chapter and article must not claim:

- degeneracies or the full simplex category;
- a complete simplicial, Kan, Segal, Rezk, complicial, or oriental theory;
- a whole equivalence
  `Functor_cat(Delta[n],C) ~= DependentSimplex_cat(C,n)`;
- that the present `DependentSimplexObservation(C,n)` is already that whole
  right-hand category;
- judgmental equality between every code-selected face and every historical
  fixed-dimensional native projection;
- judgmental equality between the uniform source and every earlier finite
  presentation;
- broad join, Sigma, or functor extensionality; or
- a global normalization, confluence, canonicity, consistency, or semantic
  soundness theorem.

`RecursiveSimplex(C,n)` was earlier planning shorthand and is not an active
owner. Use `DependentSimplexObservation(C,n)` for the current object package,
and reserve a provisional `DependentSimplex_cat(C,n)` for the future whole
classifier required by the mapping-category theorem.

## 7. Article Architecture

The overview article remains concise and within its existing 14--18-page
budget. It must not reproduce Chapter 29.

Add one compact synthesis, preferably as a new final subsection of Section 8,
that:

1. begins with the recursive equation `S_{n+1}=PathOut(S_n,s_n)`;
2. explains that face codes and ordinal shapes provide the combinatorial side;
3. states the variable-dimensional canonical source and arbitrary-target
   observation;
4. names the zero-through-four and retained-action validation boundary; and
5. states the missing whole mapping-category equivalence and degeneracies in
   the research-boundary section.

Revise the abstract and conclusion by one or two sentences so the new result
is visible without displacing arrow induction, sieve-centered geometry,
groupoidification, Gray laxity, or the TypeScript elaborator. Tighten existing
prose if pagination exceeds 18 pages; do not enlarge the article budget merely
to preserve redundant wording.

## 8. References And Attribution

The chapter should situate the construction against, without copying prose
from:

- Astra Kolomatskaia and Michael Shulman, *Displayed Type Theory and
  Semi-Simplicial Types*, arXiv:2311.18781v2;
- Hugo Herbelin and Ramkumar Ramachandra, *A Parametricity-Based Formalization
  of Semi-Simplicial and Semi-Cubical Sets*, arXiv:2401.00512v2; and
- Hugo Herbelin and Ramkumar Ramachandra, *The Very Dependent Recursive
  Structure of Iterated Parametricity in Indexed Form*, arXiv:2602.12689v1.

These sources are comparisons, not prose donors. The chapter should explain
the emdash-specific move: use the already-internal category, `PathOut`,
dependent hom, Sigma, and whole action as the semantic recursion, while codes
only internalize the varying boundary. Add human-readable bibliography
entries. No third-party adaptation record is required unless text is later
adapted rather than freshly written.

## 9. Metadata And Artifact Policy

After the source architecture is stable:

- advance the book to `0.6.0-dev` and date it 2026-08-21;
- advance the article to `0.3.0-dev` and date it 2026-08-21;
- keep both artifacts explicitly draft;
- assemble the book through its owner; never edit generated
  `print/public/emdash-book.md` by hand;
- export and check deterministic local PDFs;
- promote the owner-generated Markdown/PDF to the existing `docs/` paths; and
- render the final PDFs to PNGs and inspect every changed page, both chapter
  transitions, contents, evidence/status material, and representative dense
  displays.

Do not change Zenodo metadata or create a version tag merely because the draft
artifacts changed. Repository integration and the existing GitHub deployment
path occur only after the checked source and tracked artifacts are stable.

## 10. Proportional Validation

Use only affected gates:

```bash
./scripts/pnpmw run book:check
./scripts/pnpmw run book:render
./scripts/pnpmw run book:release
./scripts/pnpmw run article:check
./scripts/pnpmw run article:render
./scripts/pnpmw run article:release
```

Use `book:typography` after notation edits. Run deterministic release twice
only at the final artifact boundary if the existing release owner does not
already verify reproducibility in one invocation. Do not run kernel CI,
TypeScript aggregates, `check:all`, or other repository-wide gates for this
prose/evidence/artifact-only goal. Carry forward the completed focused kernel
evidence from `a70ea44`.

## 11. Git, GitHub, And Deployment Boundary

The user authorizes the dedicated local branch/worktree and SOP-compliant
local checkpoint commits after bounded green tranches. Every checkpoint must:

1. have the ledger synchronized;
2. pass its affected source or artifact gates;
3. contain only intended files; and
4. preserve unrelated worktrees and ignored evidence.

After the final editorial/artifact checkpoint, the user also authorizes:

1. a fresh remote and worktree audit;
2. fast-forwarding `main` in its actual registered worktree when ancestry and
   cleanliness still permit it;
3. pushing the integrated `main` branch to the configured GitHub remote;
4. observing the affected CI and GitHub Pages deployment to a terminal state;
5. making narrowly scoped maintenance corrections required for those gates;
   and
6. checkpointing and pushing such corrections through the same review loop.

Do not force-push, rewrite history, create a tag or PR, delete branches or
worktrees, or broaden deployment credentials/contracts without a concrete
need and a separately recorded decision. If `main` cannot be fast-forwarded,
stop and audit the divergence rather than silently merging unrelated work.

## 12. Living Ledger

| ID | State | Deliverable |
| --- | --- | --- |
| `BDS-00` | complete | Created the dedicated branch/worktree from clean `a70ea44`; bootstrapped its pnpm graph; audited current book/article architecture, active owners, completed plans, exact nonclaims, and the mapping-category naming boundary; baseline `book:check` and `article:check` are green. |
| `BDS-PLAN-1` | complete | Adopted this editorial architecture, evidence map, article boundary, artifact policy, integration/deployment authority, and persistent-goal launch prompt. The active goal delegates to this living plan and preserves the whole mapping-category equivalence as a later foundational theorem. |
| `BDS-EVIDENCE-2` | complete | Registered the four checked evidence claims, their active owners/reviewers, and the Chapter 29 manifest/expansion contract. The source gate reports 159 declared and cited claims. |
| `BDS-CHAPTER-3` | complete | Added the 3,119-word Chapter 29 with the mathematical sequence from ordinal shapes and injective faces through native PathOut/homd recursion, tetrahedral projection geometry, intrinsic codes, ordinal successor, the four-simplex, the variable-dimensional theorem, comparisons, and exact nonclaims. Source, evidence, typography, KaTeX, paper, render, and page-image review are green. |
| `BDS-CROSSCUT-4` | complete | Synchronized the prologue, preface, reading paths, Chapter 28 transition, notation, glossary, status matrix/research direction, bibliography, and generated contents ownership for the fifth spiral. |
| `BDS-ARTICLE-5` | complete | Added the compact §8.5 synthesis; revised the abstract from four to five computations, the simplicial research boundary, conclusion, date, and `0.3.0-dev` artifact metadata. The first 396-word insertion rendered at 19 pages and was deliberately compressed to 186 words; the resulting 9,209-word article renders at the unchanged 18-page maximum with no console, page, request, or render error. Comparative literature remains in Chapter 29 rather than consuming article pages. |
| `BDS-BOOK-QA-6` | complete | `book:release` passes for the tagged 355-page, 16-font `0.6.0-dev` PDF, SHA-256 `4116c6aaa586e55dc7c54b5faa6e379b3a376bb56fb86fec392f7981a72276b3`. Poppler review covered metadata/front matter, contents, the repaired prologue theorem preview, Chapter 28 transition, every Chapter 29 page, notation, all new evidence rows, glossary entries, status matrix/direction, and bibliography. It caught and corrected a stale fourth-spiral notice, a two-line reader-guide orphan, a literal blockquote marker around the prologue display, and an orphan bibliography note; the final rerender is clean. |
| `BDS-ARTICLE-QA-7` | complete | `article:release` passes for the 18-page, 14-font `0.3.0-dev` PDF, SHA-256 `c3afdc85c9d7ee7640d8114c4a550bf9a43b6f2b04b3707ddda1e12400b70dcf`. All 18 pages were inspected. The first synthesis exceeded the page ceiling; the compressed version exposed one two-column formula collision; the final inline recurrence removes the collision while retaining the 18-page maximum. |
| `BDS-PROMOTE-8` | complete | Owner promotion copied the assembled 842,558-byte book Markdown and 3,117,927-byte book PDF to `docs/emdash-book.{md,pdf}`, and the 67,231-byte article Markdown and 739,139-byte article PDF to `docs/emdash3_2.{md,pdf}`. Both public PDFs are byte-identical to their checked owner artifacts. |
| `BDS-MAINT-8A` | complete | Updated the root reader route and edition size, the emdash2 book summary, active current-status artifact record, report index, and both long/short external-email appendices. The root README no longer calls dimension four future work; all public prose keeps the whole dependent-simplex category/equivalence and degeneracies explicit. |
| `BDS-INTEGRATE-9` | complete | Audited all 25 registered worktrees as clean, fetched the remote, established that release checkpoint `6b85c2fd991b5ada7282f713a5ce34215d0c0a74` was exactly 73 commits ahead of and zero behind the prior `main` checkpoint `e1dc41484e4b906cadf094dc63fc7bddba526a41`, fast-forwarded the registered `main` worktree, and pushed `main` without a merge commit, rebase, or force. GitHub Pages run [`32532377691`](https://github.com/hotdocx/emdash/actions/runs/32532377691) completed both `build` and `deploy` successfully for that exact head. The HTTPS site returns 200, and its fingerprinted 3,117,927-byte book and 739,139-byte article PDFs reproduce the checked SHA-256 hashes recorded above. |
| `BDS-CLOSE-10` | complete | Synchronized this final ledger and the report index in a documentation-only closeout checkpoint after the terminal deployment audit. No source, generated artifact, or dependency changed; consequently no build or aggregate was repeated. The final push is audited by exact equality of local `main` and `origin/main`, while the release branch remains an intact backtracking checkpoint. |

## 13. Completion Definition

The goal is complete only when:

1. Chapter 29 reads as a coherent mathematical chapter rather than a report;
2. every checked claim has active evidence and every limitation is stated at
   its exact level;
3. the concise article remains within 18 pages and retains its existing
   narrative spine;
4. both deterministic PDFs pass their owning structural checks;
5. final page-image inspection finds no clipping, overlap, broken math,
   stranded headings, poor transitions, or unreadable evidence blocks;
6. the `docs/` Markdown/PDF distributions come from their declared owners;
7. the living ledger and exact Git diff are synchronized;
8. a local checkpoint preserves the completed result;
9. clean ancestry permits a reviewed fast-forward of `main`, or any divergence
   is reported instead of hidden;
10. the integrated branch is pushed to GitHub; and
11. affected CI and GitHub Pages deployment are observed to a terminal green
    state, with any exception recorded precisely.

The still-future whole equivalence
`Functor_cat(Delta[n],C) ~= DependentSimplex_cat(C,n)` is not a completion
condition. It should become a separately scoped foundational goal after this
editorial release if it is selected next.
