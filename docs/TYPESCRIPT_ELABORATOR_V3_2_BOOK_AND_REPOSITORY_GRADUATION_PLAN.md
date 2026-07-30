# TypeScript Elaborator v3.2 — Book And Repository Graduation Plan

Date: 2026-07-30
Plan-ID: TS-ELAB-V3.2-BOOK-REPOSITORY-GRADUATION
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md),
the completed book architecture plan
[`REPORT_EMDASH_V3_2_FUNCTORIAL_TYPE_THEORY_BOOK_ARCHITECTURE_PLAN_2026-07-20.md`](../emdash2/reports/REPORT_EMDASH_V3_2_FUNCTORIAL_TYPE_THEORY_BOOK_ARCHITECTURE_PLAN_2026-07-20.md),
and the completed category/formal-presentation expansion plan
[`REPORT_EMDASH_V3_2_FUNCTORIAL_TYPE_THEORY_BOOK_CATEGORY_THEORY_AND_FORMAL_PRESENTATION_EXPANSION_PLAN_2026-07-20.md`](../emdash2/reports/REPORT_EMDASH_V3_2_FUNCTORIAL_TYPE_THEORY_BOOK_CATEGORY_THEORY_AND_FORMAL_PRESENTATION_EXPANSION_PLAN_2026-07-20.md)
Status: selected and dependency-ready post-syntax product-graduation route.
Syntax parity is final-green through `SYNTAX-PARITY-1D1` at
`59a5ebe9d11c51b62d64f9508b7cfde895b0c00c`. The exact zero-behavior
`SYNTAX-PARITY-GRADUATE-1` proposal is checkpointed at
`be1eb6cf1e33c17c88615d243fae8a58d1d8cbba` and approved as proposed by a
separate immutable D010 unattended review with human supersession. The exact
review checkpoint is
`38e0bc2b177773db0faba36e8aaafd12d5e50982`. `BOOK-DELTA-0A` is complete
in
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_DELTA_AUDIT.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_DELTA_AUDIT.md);
`BOOK-NARRATIVE-0B` is complete in the frozen
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_PROPOSAL.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_PROPOSAL.md).
H-DTTLF-BOOK-REPOSITORY-01 / D-DTTLF-BOOK-REPOSITORY-001 is approved
exactly as proposed by the separate immutable
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_D001_REVIEW.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_D001_REVIEW.md)
under the standing unattended delegation with human supersession.
`BOOK-REVIEWER-BRIDGE-1A` is complete at exact local checkpoint
`93d20cfa12b6308a0e2ef9abe81f98dd8cbeceb0`.
`BOOK-PROSE-1A` is final source-green with its local checkpoint pending.
`BOOK-ARTIFACT-1B` is the next row after that checkpoint. No generated
artifact, remote release/publication, or bulk scale change is yet included.
Human-Direction: on 2026-07-30 the user explicitly confirmed this sequence as
the high-yield continuation after syntax parity: reconcile the mathematical
book from the `8217aa3...` baseline without turning it into an internal
technical report, deterministically refresh `docs/emdash-book.pdf`,
consolidate the root repository introduction, and move remaining bulk scale
qualification to a future persistent goal.

## Objective

After user-syntax parity reaches its separately reviewed graduation boundary,
update the mathematical book and public repository presentation so that an
external reader can understand and exercise the emdash research programme as
it actually exists.

This is the final reader-facing continuation of the current product goal:

```text
integrated reviewer
  -> mathematical text/direct-TypeScript parity
  -> capability-delta audit for the book
  -> theorem-led narrative and evidence update
  -> reproducible public book artifact
  -> concise repository introduction and reviewer path
  -> current product-goal graduation
```

The remaining bulk systematic-transfer rows are valuable architecture
qualification, but they are not prerequisites for this reader-facing
graduation. They remain pending in the scale ledger and move to a future
persistent goal. This plan does not claim that they are complete or
unnecessary.

## Verified Editorial Baseline

The user identified
`8217aa3d30a1086c45e28eb666969b5acec90a6b` as the approximate point after
which new work needs to be reconciled with the book. Repository history
confirms the useful boundary:

- the completed expanded-edition prose culminates in the July 20 C7 baseline,
  with the final bibliography correction at
  `8408c3f6fc84fc6bbee651f37d7d18314c6b73ef`;
- the tracked public PDF was added at
  `2ea30b4a789d303d9c255f7d3e1009b87f669130`;
- `8217aa3d30a1086c45e28eb666969b5acec90a6b` updates mathematical evidence,
  examples, and maintenance infrastructure; and
- the following `3965df1d221ff14ee93e2496aaece010b685b708`
  commit changes repository/release infrastructure rather than writing a new
  reader-facing edition.

`8217aa3...` is therefore the primary delta-audit anchor requested by the
user. The earlier C7 prose and PDF commits remain exact editorial/artifact
baselines. The audit must classify mathematical and product capabilities; it
must not copy the subsequent Git log into the book.

## Governing Book Architecture

This plan extends the completed B/C book plans. It does not reopen or rewrite
their completion history.

The following invariants remain mandatory:

- the book is theorem-led mathematical exposition, not a kernel symbol
  catalogue, implementation manual, or developer diary;
- each chapter begins from a mathematical question, construction, or theorem;
- implementation names occur only in compact formal-status/evidence notes
  when they materially support a claim;
- checked, formal-consequence, mathematical-development, and research-boundary
  claims remain distinct;
- the categorical computational kernel remains conceptually prior to its
  convenient surface elaborator;
- no successful test run is promoted into a global confluence,
  normalization, consistency, canonicity, or decidability theorem;
- active Lambdapi sources and checks outrank book prose; and
- `emdash2/book/book.json`, `emdash2/book/STYLE.md`, the evidence/provenance
  ledgers, and authored Markdown sources retain their existing ownership.

In particular, the new TypeScript work corrects one now-stale C6/C7 boundary:
the parent TypeScript code is no longer merely an obsolete read-only
prototype. A renewed explicit-Core checker/evaluator, outer dependent LF,
categorical elaboration layer, and reviewer product now exist. The book should
explain that development accurately without making the implementation the
organizing subject of the mathematics.

## Capability-Delta Contract

`BOOK-DELTA-0A` must inventory work from `8217aa3...` through the eventual
syntax-parity graduation checkpoint and classify every candidate item as one
of:

1. **mathematical narrative change** — changes how an existing construction,
   dependency, or theorem should be explained;
2. **formal-presentation change** — changes the accurate relationship among
   surface language, outer LF, explicit Core, categorical kernel, checking,
   computation, and the Lambdapi oracle;
3. **new checked evidence for an existing mathematical claim** — updates a
   compact status note or evidence record but does not require new main-line
   prose;
4. **reader workflow change** — affects how a reader runs or explores a
   checked example;
5. **developer-only implementation detail** — remains in plans, source,
   tests, or the handoff and does not enter the book; or
6. **future research/scale boundary** — belongs in a short status boundary,
   not as implemented mathematics.

The audit must cover at least:

- the renewed minimal outer dependent LF and backend-neutral explicit Core;
- the small TypeScript checker, conversion, evaluator, runtime rewriting, and
  proof-time unification boundary;
- generic checked transfer of declarations, runtime rules, and proof-time
  rules, stated only to the demonstrated envelope;
- ordinary functorial variables and recursive bracket abstraction;
- indexed/natural, displayed-functorial, and displayed-natural abstraction
  evidence, including the exact bounded dependent-context envelope;
- object-, arrow-, and selected higher-action ownership through internal
  categorical constructions;
- the integrated browser reviewer, terminal report, and optional Lambdapi
  conformance role;
- the graduated text syntax and its exact fail-closed boundary; and
- unresolved whole-library transfer, arbitrary displayed depth/variance,
  groupoidal closure, and global metatheory.

Every retained item must name its intended reader question and destination.
An item without a reader-facing mathematical or formal-presentation purpose
is excluded from the book by default.

## Reader-Facing Narrative Design

`BOOK-NARRATIVE-0B` must freeze a small exact editorial proposal before prose
changes. The likely high-yield destinations are:

- the preface and reading guide, for one concise route from mathematical
  notation to executable evidence;
- Chapter 1, only where the outer LF/checking/computation distinction changes
  the explanation of judgments;
- Chapter 2 and/or Chapter 9, only where usable functorial, natural, or
  displayed variables materially clarify categorical substitution and cut;
- Appendix G, as the principal owner of the corrected four-layer formal
  presentation; and
- the evidence/status appendices, for exact implementation and research
  boundaries.

The proposal should prefer one continuous running example over a list of
features. After syntax parity, that example should show a convenient bound
variable occurring recursively inside a categorical expression, the inferred
application/action, the elaborated explicit Core, and a meaningful
object/arrow or displayed observation. A second example is justified only if
it is necessary to distinguish ordinary from genuinely dependent/displayed
binding.

The exact notation must be taken from the graduated canonical-syntax and
syntax-parity records. Experimental spellings must not be retrospectively
presented as settled book notation.

### What must not enter the main prose

The following remain developer documentation unless a separately justified
reader-facing sentence is needed:

- plan IDs, decision IDs, checkpoint hashes, test counts, command-selection
  ordinals, export digests, and worktree history;
- acquisition-contract layering and browser chunk boundaries;
- per-owner transfer inventories;
- rejected implementation spikes and Git/DevOps recovery procedure; and
- a chronological list of completed TypeScript tranches.

The book may say that a capability is checked and link it to compact evidence.
It should explain the mathematics and architecture before naming how the
repository happens to organize that evidence.

## Public Book Artifact And Repository Presentation

The authored book remains under `emdash2/book/`. Generated Markdown and PDF
remain non-authoritative artifacts owned by the existing book pipeline.

The repository currently has two distinct PDF roles:

- the manifest-owned ignored release artifact under `emdash2/output/pdf/`;
  and
- the tracked public distribution copy at `docs/emdash-book.pdf`, which is
  the stable repository/GitHub Pages URL.

Before updating the tracked public copy, `BOOK-ARTIFACT-1B` must identify and
freeze one deterministic ownership route. The preferred small solution is a
checked promotion command that:

1. consumes only the already validated manifest-owned PDF;
2. copies it byte-for-byte to `docs/emdash-book.pdf`;
3. verifies the expected source/destination checksum and metadata; and
4. never edits the PDF or assembled Markdown by hand.

If an existing equivalent owner is found, reuse it. Do not add a second
render/export pipeline.

`REPO-PRESENT-1C` then consolidates the root presentation around a reader
rather than a contributor ledger:

1. what emdash is and its central mathematical thesis;
2. the canonical book link, `docs/emdash-book.pdf`;
3. the shortest truthful way to run the integrated reviewer;
4. the active Lambdapi-kernel versus TypeScript-product authority boundary;
5. exact current limitations; and
6. a compact route to contributor/internal plans.

Detailed histories, validation counts, and tranche ledgers belong in the
handoff and plans, not in the opening repository narrative. Existing useful
developer commands remain discoverable without dominating the introduction.

No GitHub Pages workflow, remote publication, release, tag, or push is implied
by preparing the static artifact and README.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| BOOK-DELTA-0A | **complete at `9f3d744010d1bba210d1dcd1762df0afc35cf270`** | syntax-parity graduation and `8217aa3...` audit anchor | [`TYPESCRIPT_ELABORATOR_V3_2_BOOK_DELTA_AUDIT.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_DELTA_AUDIT.md) classifies the mathematical, formal-presentation, evidence, workflow, developer-only, and future-boundary deltas without prose mutation |
| BOOK-NARRATIVE-0B | **complete; proposal checkpoint `3f5cfab9082c2f863304395658c9d54824c81f44`** | complete delta matrix and book authorities | [`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_PROPOSAL.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_PROPOSAL.md) freezes two running examples, ten authored/structured book sources, three evidence claims, one reviewer preset, one PDF-promotion owner, README scope, non-claims, and proportional validation |
| H-DTTLF-BOOK-REPOSITORY-01 / D-DTTLF-BOOK-REPOSITORY-001 | **approved exactly as proposed at review checkpoint `9a14695b401c696f9f55dc785689f2e4e49d7a5b`; human supersession retained** | immutable proposal at `3f5cfab9082c2f863304395658c9d54824c81f44` | [`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_D001_REVIEW.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_D001_REVIEW.md) approves only the exact authored sources, evidence/manifest effects, one derived preset, artifact ownership, README scope, validation, and Git boundary |
| BOOK-REVIEWER-BRIDGE-1A | **complete at `93d20cfa12b6308a0e2ef9abe81f98dd8cbeceb0`** | exact D001 approval | The tenth `nested-exchange` preset exactly equals its direct TypeScript construction, exposes `exchange-functor-abstraction`, and has a root `reviewer:dev` alias; no parser/checker/kernel change |
| H-DTTLF-BOOK-SOURCE-CONTRACT-01 / D-DTTLF-BOOK-REPOSITORY-002 | **approved exactly as proposed at review checkpoint `1dee8fe414b63973e5f848936ae6d3c9d2319b35`; human supersession retained** | measured stale validator literal and proposal `21b5ebdbb9d82ba8d9139319aaa2ae1f8f96f881` | Replace only the retired formal-layer literal in `check_book.mjs`; retain every other source/render contract |
| BOOK-PROSE-1A | **final source-green; checkpoint pending** | exact D001/D002 approvals and green reviewer bridge | The ten authored/structured sources now present fibrewise contexts, base change/evaluation, fibred cuts, binder notation, the bounded TypeScript architecture, three new checked evidence claims, and exact retained boundaries as theorem-led prose |
| BOOK-ARTIFACT-1B | **next after BOOK-PROSE-1A checkpoint** | final-green authored edition and exact D001 approval | Run the single final book release, one necessary repeat PDF generation, visual QA, and deterministic promotion to `docs/emdash-book.pdf` |
| REPO-PRESENT-1C | gated | validated book artifact and exact separate review | Consolidate root README/public entry points around the book and integrated reviewer, with internal details routed to handoff/plans |
| PRODUCT-BOOK-GRADUATE-1 | gated | BOOK-PROSE-1A through REPO-PRESENT-1C | Freeze exact reader-facing capabilities, commands, artifact checksum, limitations, and the future-scale handoff |
| FUTURE-SCALE-GOAL | deferred/out of scope for this persistent goal | later explicit user goal | Resume pending SCALE-STRESS-3C, SCALE-BATCH-1, SCALE-GRADUATE-1, and other preserved scale rows without implying they were completed here |

## Acceptance

Reader-facing graduation requires:

- the capability-delta matrix is complete and excludes developer-only detail;
- the edited book still reads as one mathematical argument rather than a
  release note;
- every changed theorem-like claim has the correct formal status and evidence;
- every implemented-syntax example is accepted by the graduated text adapter
  and agrees with its direct TypeScript construction;
- any direct TypeScript or Lambdapi evidence cited by the book is current and
  reproducible;
- `book:check`, `book:render`, and `book:release` pass under the existing
  source/typography/provenance/evidence/accessibility contracts;
- affected pages and all pagination-sensitive pages receive visual review;
- repeated release generation is deterministic;
- `docs/emdash-book.pdf` is byte-identical to the checked promoted artifact;
- the root README’s book and reviewer commands resolve from a fresh worktree;
- the README states the current authority and limitation boundary without
  burying the mathematical introduction in internal status detail; and
- no bulk-scale completion, deployment, publication, or global metatheory
  claim is introduced.

### Proportional validation policy

The acceptance gates above belong to the boundary they validate; they are not
commands to rerun after every planning or editorial checkpoint.

- Plan/audit-only changes require exact diff review and Markdown/diff hygiene,
  not TypeScript, browser, kernel, or book-render aggregates.
- A bounded TypeScript reviewer-preset change requires its focused corpus plus
  TypeScript typecheck/lint; unchanged kernel/conformance boundaries retain
  their recorded evidence.
- Authored prose/evidence changes require the bounded book source, evidence,
  and typography checks selected by the affected files.
- The full book render/release, deterministic-PDF comparison, and visual
  inspection run once at `BOOK-ARTIFACT-1B`, after the reviewed authored
  edition is complete. They are rerun only if a later change can affect the
  artifact.
- Multi-minute repository aggregates are exceptional: use them only for an
  actually changed covered boundary or the final reviewed release gate, not
  for reassurance about unchanged code.

## Scale Relationship

Deferring bulk scale from this persistent goal is a priority boundary, not a
technical verdict.

The current implementation already supplies enough varied evidence to present
a truthful, nontrivial programme: outer DTT/LF, ordinary and genuinely
displayed categorical binding, explicit Core, checking/computation, generic
transfer mechanisms, a text adapter, and a client-side reviewer. Completing
the selected text parity and explaining that system well has higher immediate
reader value than adding another large internal transfer batch.

The scale plan continues to own the eventual claims that:

- the WalkingEnd/HIT mechanism class transfers through the generic path;
- a larger dependency-closed batch needs no compiler change; and
- the residual whole-library mechanical-transfer envelope is qualified.

This current product graduation must state those as pending. A specifically
measured capability required by the book’s selected running example may still
be promoted early through its own bounded proposal and separate review; the
book is not blanket authority for scale work.

## Git And Persistent-Goal Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Current authority permits only bounded green local checkpoint commits in the
dedicated goal branch/worktree after synchronized ledgers, exact staged-diff
review, and `git diff --cached --check`.

This route authorizes no push, merge, PR, deployment, publication, release,
tag, rebase, amend, reset, history rewrite, branch/worktree removal, generated
artifact cleanup, or unrelated mutation. Updating the tracked public PDF is a
future separately reviewed repository change, not authorization to publish it
remotely.

## Persistent `/goal` Launch Prompt

```text
Continue the current reader-facing TypeScript emdash v3.2 product goal through
the next dependency-ready reviewed row in
docs/TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md,
docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md, and
docs/TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md.
Use docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md for recovery and retain
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md as the preserved
future architecture-qualification ledger, not as authority to resume bulk
scale during this goal.

Recover current code/tests, all worktrees and ancestry, staged and unstaged
state, active root and nested authorities, and living decisions before
acting. Follow the next reviewed row rather than a stale task snapshot.

Recover the completed integrated reviewer and exact approved syntax
graduation; do not re-open or reimplement them. Begin with `BOOK-DELTA-0A`:
audit capability deltas from 8217aa3... without mutating prose. Then update
the book as theorem-led mathematical prose, not a developer report. Correct
the formal-presentation boundary, use a small compelling running example,
update compact evidence/status records, validate and visually review the
generated edition, establish one deterministic owner for
docs/emdash-book.pdf, and consolidate the root README around the book and
integrated reviewer.

Keep SCALE-STRESS-3C, SCALE-BATCH-1, SCALE-GRADUATE-1, and other bulk
systematic-transfer rows pending for a future explicit goal. Promote only a
specific missing dependency required by the selected reader-facing example,
and only through a measured, separately reviewed bounded proposal.

Existing Git authority permits only bounded green local checkpoints on the
dedicated goal branch after synchronized ledgers and exact staged review. Do
not push, merge, publish, deploy, release, tag, amend, rebase, reset, rewrite
history, delete branches/worktrees, or perform unrelated cleanup.
```

## Change Log

- **2026-07-30 — `BOOK-PROSE-1A` final source-green.** The exact ten
  authored/structured sources now form the `0.3.0-dev` edition. Chapter 2
  develops independent fibrewise siblings, genuine dependency, asymmetric
  base-change totalization, and constant-domain displayed evaluation;
  Chapter 9 adds fibred structural cuts. Appendices A, F, and G state the
  intrinsic binder modes, actual bounded TypeScript architecture, historical
  prototype distinction, and complete-surface/scale boundaries. The evidence
  register has 110/110 cited claims, including the three approved new checked
  claims. Assembly consistency, typography, 1,317 KaTeX spans, source
  contracts, and paper validation pass. The first combined check exposed
  only the retired `optional future elaborator` literal in the source
  validator. The exact D002 proposal/review at
  `21b5ebdbb9d82ba8d9139319aaa2ae1f8f96f881` /
  `1dee8fe414b63973e5f848936ae6d3c9d2319b35` authorizes its one-line
  replacement; the failed and previously unreached stages then pass. No PDF,
  renderer build, kernel gate, TypeScript aggregate, or publication ran.
  Local implementation checkpoint pending.
- **2026-07-30 — `BOOK-REVIEWER-BRIDGE-1A` completed.** The integrated
  reviewer now exposes the already graduated
  `λ^f x : A. λ^f y : B. E y x` witness as its tenth preset. Parsed text is
  exactly equal to the direct TypeScript construction and reports the
  existing `exchange-functor-abstraction` prerequisite. The root
  `reviewer:dev` alias starts the same client-only Vite workbench. The
  focused 12/12 affected tests, root typecheck/lint, and browser fixture
  typecheck/build pass. No aggregate, kernel, book-render, parser, checker,
  Core-owner, or Lambdapi behavior was run or changed. Exact local
  implementation checkpoint:
  `93d20cfa12b6308a0e2ef9abe81f98dd8cbeceb0`.
  `BOOK-PROSE-1A` is now dependency-ready.
- **2026-07-30 — H-DTTLF-BOOK-REPOSITORY-01 /
  D-DTTLF-BOOK-REPOSITORY-001 approved as proposed.** A separate immutable
  [D001 review](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_D001_REVIEW.md)
  checks the frozen proposal at
  `3f5cfab9082c2f863304395658c9d54824c81f44` against active mathematical
  owners/checks, both working examples, theorem-led editorial scope, evidence
  discipline, notation, artifact ownership, public presentation,
  proportional validation, and Git authority. Under the standing unattended
  delegation with human supersession, it approves only that exact scope.
  Exact local review checkpoint:
  `9a14695b401c696f9f55dc785689f2e4e49d7a5b`.
  `BOOK-REVIEWER-BRIDGE-1A` is the next row.
- **2026-07-30 — `BOOK-NARRATIVE-0B` proposal frozen.** The exact
  [book/repository proposal](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_PROPOSAL.md)
  selects the existing nested exchange/currying witness and mixed displayed
  context, ten authored/structured book files, three Lambdapi-backed evidence
  claims, one derived browser preset, one root reviewer command, a
  deterministic canonical/compatibility PDF promotion owner, a reader-first
  README outline, exact non-claims, and proportional validation.
  H-DTTLF-BOOK-REPOSITORY-01 / D-DTTLF-BOOK-REPOSITORY-001 is now the
  dependency-ready separate review; no prose, product, artifact, or README
  mutation has started.
- **2026-07-30 — `BOOK-DELTA-0A` completed.** The dedicated
  [capability audit](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_DELTA_AUDIT.md)
  classifies the active fibred-context mathematics, renewed TypeScript
  formal-presentation/product boundary, checked evidence additions, reviewer
  workflow, developer-only exclusions, and future scale boundaries. It
  selects a nested ordinary primary example and mixed displayed secondary
  example, recommends no evidence-checker expansion, and makes
  `BOOK-NARRATIVE-0B` dependency-ready without mutating book prose or product
  behavior. Proportional validation now explicitly reserves the expensive
  aggregate render/release gate for the actual artifact boundary. Exact local
  audit checkpoint: `9f3d744010d1bba210d1dcd1762df0afc35cf270`.
- **2026-07-30 — `BOOK-DELTA-0A` is dependency-ready.** Exact D010 syntax
  graduation is approved with human supersession after final-green 1D1. The
  current goal now enters the capability-oriented delta audit; no prose,
  generated artifact, repository presentation, or bulk scale work has
  started early.
- **2026-07-30 — Post-syntax priority explicitly reaffirmed.** The user
  confirmed that book reconciliation, the stable public PDF, and the root
  repository presentation are the current goal's high-yield successor to
  syntax parity. Pending general scale qualification is preserved as future
  work and must not be resumed implicitly during this goal.
- **2026-07-30 — Reader-facing post-syntax graduation selected.** Recorded
  the user’s direction to update the book and repository presentation after
  syntax parity, keep the book mathematical rather than developer-facing,
  retain `docs/emdash-book.pdf` as the canonical public link through a
  deterministic artifact owner, and defer remaining bulk scale work to a
  future persistent goal.
