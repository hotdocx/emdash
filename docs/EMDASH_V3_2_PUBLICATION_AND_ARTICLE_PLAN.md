# Emdash v3.2 Publication And Overview-Article Plan

Date: 2026-07-30
Plan-ID: EMDASH-V3.2-PUBLICATION-AND-ARTICLE
Status: active living publication plan; ownership audit complete; implementation
in progress

Depends-On:

- [`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md)
- [`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md)
- [`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md)
- [`../emdash2/reports/REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md`](../emdash2/reports/REPORT_EMDASH_V3_2_RESEARCH_ARTICLE_ARCHITECTURE_2026-06-05.md)
- [`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)

Supersedes:

- the retained compatibility meaning of `docs/emdash3_2.pdf` as a second copy
  of the full book;
- the 2026-07-22 decision to keep the v2 print sources registered indefinitely;
  and
- the deferred publication row `BROWSER-STATIC-DEPLOY-0A`.

It does not rewrite the completed history of the plans above. It records the
user's later publication direction and owns the resulting continuation.

## Human Direction And Authorization

On 2026-07-30 the user selected one consolidated public objective:

1. retire the obsolete `spec/` snapshot and legacy root document artifacts
   after a reference and ownership audit;
2. make the complete book available as both
   `docs/emdash-book.md` and `docs/emdash-book.pdf`;
3. restore `docs/emdash3_2.md` and `docs/emdash3_2.pdf` to their intended role
   as a shorter, high-quality v3.2 research article rather than book aliases;
4. derive the first new article from the larger book and current checked
   implementation through an overall or overview perspective;
5. retire the obsolete v2 print workbenches and replace the ambiguous
   `index*.md` routes with a descriptive active article route;
6. ignore local `.playwright-cli/` browser-tool output;
7. present emdash as a new proof-assistant or programming-language research
   project on a polished landing page with the live reviewer on the same page;
8. fast-forward the completed goal branch into local `main`, push the reviewed
   result to `hotdocx/emdash`, configure GitHub Pages, and verify
   `https://hotdocx.github.io/emdash/`.

The user authorized bounded green checkpoint commits, deletion of the exact
audited obsolete tracked paths, local fast-forward integration, upstream push,
and GitHub Pages publication. This does not authorize force push, rebase,
amend, reset, branch or worktree deletion, publication to a research venue, a
versioned release claim, or unrelated cleanup.

## Objective

Turn the already checked mathematical, TypeScript, and reviewer work into a
coherent public research artifact:

```text
active mathematical and TypeScript authorities
  -> theorem-led full book
  -> concise overview article
  -> one browser landing/reviewer experience
  -> reproducible public artifacts
  -> GitHub Pages
```

The result should let an external reviewer understand the research thesis,
read a short paper or the full book, run representative binder examples,
inspect explicit Core and evidence, and reach the active Lambdapi source
without first learning the repository's internal tranche history.

## Non-Goals

This goal does not:

- change the active Lambdapi mathematics or TypeScript Core semantics;
- resume whole-library scale qualification;
- claim a finished generic proof assistant, parser, elaborator, metatheory, or
  groupoidal closure;
- submit the article to a venue or select venue-specific formatting;
- create a server backend when the measured reviewer remains client-side;
- preserve obsolete generated artifacts merely because Git once tracked them;
  or
- turn the article or landing page into an internal developer report.

## Completed Ownership And Reference Audit

### Git and publication state

- Dedicated worktree:
  `/home/user1/emdash1-elaborator-goal`
- Dedicated branch:
  `goal/typescript-elaborator-v3.2`
- Audited starting checkpoint:
  `7664234d15309ffd1e8d1da3f2a8111e77d6880d`
- Local `main`:
  `e7c4928f56b7015cd70f4ec49b3a36caafbe5753`
- The goal branch is a descendant of local `main` with no divergence.
- The GitHub repository is `hotdocx/emdash`; the authenticated account has
  repository administration permission.
- GitHub Pages is not configured and the requested project URL currently
  returns 404.

### Book artifacts

The active book sources are the chapter-sized files ordered by
`emdash2/book/book.json`. The assembled
`emdash2/print/public/emdash-book.md` is generated and ignored. The checked
PDF is generated under `emdash2/output/pdf/` and is ignored.

The tracked public book PDF is:

```text
docs/emdash-book.pdf
pages: 199
bytes: 1,850,797
sha256: b34b7e430deacf4b91ce354c5e5eb3d2674ef08e93d3bcbd4ca7618ea37f41d7
```

No tracked `docs/emdash-book.md` currently exists. It should be promoted
byte-for-byte from the checked assembled Markdown, never edited independently.

### Article artifacts

`emdash2/print/public/index_3_2.md` is the current authored v3.2 article
workbench. The article architecture report already recommends a
computation-first narrative centered on synthetic arrow induction, then a
broader categorical calculus. It deliberately deferred deriving a short paper
until a human editorial decision. The user's current direction supplies that
decision.

The tracked `docs/emdash3_2.pdf` is currently byte-identical to the 199-page
book. It is not an article. `docs/emdash3_2.md` is a stale 413,485-byte
assembled snapshot rather than the current 427,754-byte book assembly or the
59,014-byte article workbench. Both public `emdash3_2` paths therefore need a
new, explicit article owner.

### Obsolete tracked material

The following exact paths have no active source, build, test, README, or
authority consumer outside their own historical prose:

```text
spec/emdash2.lp
spec/emdash_specification_lambdapi.lp

docs/emdash.md
docs/emdash.pdf
docs/emdash2.md
docs/emdash2.pdf
docs/emdash2-shorter.md
docs/emdash2-shorter.pdf
```

The two `spec/` files entered at commit
`9a7705d6ef6f914a9fa18f59aa8ecc0e5d796208`; the old document paths retain
their own Git histories. Git is sufficient recovery storage. Copying them to
an ignored `.scratchpad/` would duplicate stale source and binary artifacts
without an owner, so the selected implementation deletes the tracked paths
and records this ledger instead.

The print registry also retains:

```text
emdash2/print/public/index.md
emdash2/print/public/index_0.md
```

as renderable v2 archives. Their present-tense mathematics is obsolete and
their generic names make them look current. The user's direction supersedes
their indefinite retention. Git history at
`8217aa3d30a1086c45e28eb666969b5acec90a6b` and earlier remains the recovery
route.

### Tool output

`.playwright-cli/` contains local browser automation state and screenshots,
not repository source. The root ignore policy should own it. Existing
untracked contents must not be staged.

## Selected Artifact Ownership

| Public artifact | Canonical owner | Generated intermediate | Promotion rule |
| --- | --- | --- | --- |
| `docs/emdash-book.md` | `emdash2/book/book.json` and its ordered sources | `emdash2/print/public/emdash-book.md` | checked byte-for-byte copy |
| `docs/emdash-book.pdf` | book manifest and deterministic book renderer | `emdash2/output/pdf/functorial-type-theory-0.3.0-dev.pdf` | checked byte-for-byte copy |
| `docs/emdash3_2.md` | one descriptively named authored overview article under `emdash2/print/public/` | none | checked byte-for-byte copy |
| `docs/emdash3_2.pdf` | the same overview article and article-PDF metadata | ignored article PDF under `emdash2/output/pdf/` | checked byte-for-byte copy |
| GitHub Pages site | `emdash-template/src/` plus reviewed root TypeScript browser entry | `emdash-template/dist/` | Actions Pages artifact |

The distribution copies are not authoring locations. Promotion is scripted,
atomic, manifest- or registry-driven, and verified by size and digest.

The first article remains an authored paper because a high-quality overview
requires its own argument, compression, transitions, and limitations. It may
adapt facts and diagrams from the book, but it is not assembled by blindly
concatenating book sections. Avoiding synchronization drift means one
canonical article source plus checked promotion, not forcing the book and
paper to share every paragraph.

Future papers should use additional descriptive filenames and registry rows,
not `index_0.md`, numbered copies, or hand-maintained files under `docs/`.

## First Overview Article

### Reader and thesis

Primary readers are type theorists, proof-assistant implementers, programming
language researchers, and category theorists assessing whether emdash is a
feasible research programme.

Working thesis:

> Emdash treats functoriality, naturality, and directed dependency as
> computational structure. Its Lambdapi kernel supplies checked categorical
> owners and reductions, while a small TypeScript logical framework elaborates
> ordinary, functorial, natural, displayed-functorial, and
> displayed-natural binders into explicit backend-neutral Core.

The paper should explain one architecture through two representative
computations:

1. synthetic arrow induction computing directed composition; and
2. recursive ordinary and displayed contextual abstraction compiling usable
   binders to internal categorical operations.

This overview perspective connects the mature mathematical kernel, recent
TypeScript work, and runnable reviewer better than a catalogue of every
construction.

### Target shape

- approximately 16 US Letter pages after the existing print pipeline
  paginates the paper;
- a draft overview article, not a venue-specific submission;
- high-quality academic prose with a clear mathematical arc;
- compact implementation evidence and explicit limitations;
- short code or notation examples only where they advance the argument;
- no tranche IDs, checkpoint catalogues, CI anecdotes, or DevOps narrative in
  the main prose.

### Proposed outline

```text
Title and abstract

1. Why categorical variables should compute
2. A two-layer executable architecture
3. Directed families, totals, and sections
4. Synthetic arrow induction and computational composition
5. Usable functorial and displayed binders
6. From surface terms to explicit Core and checked normal forms
7. What the artifact demonstrates
8. Boundaries and research programme
9. Conclusion

Compact notation/evidence appendix, if pagination permits
```

The paper may reuse the existing `PathOut`, `rho`, motive-transport, and
composition figures after checking them against the current notation. It
should add at most one compact pipeline figure or table for:

```text
text or typed TypeScript surface
  -> recursive typed contextual elaboration
  -> explicit Core
  -> TypeScript check/evaluation
  -> optional Lambdapi conformance
```

### Evidence discipline

Every implemented mathematical claim must resolve to active Lambdapi owners
or checks. Every TypeScript product claim must resolve to current tests or the
browser reviewer. The article must distinguish:

- checked kernel computation;
- checked TypeScript elaboration/evaluation;
- architectural interpretation;
- bounded demonstrated envelope; and
- future programme.

The article must not infer global normalization, consistency, completeness,
decidability, arbitrary displayed depth, whole-library transfer, or full
groupoidal DTT from the existing evidence.

## Landing Page And Reviewer Brief

### Product position

The page is a research-language landing page with the live reviewer embedded
on the same page, not a separate marketing shell around a hidden demo.

Primary value:

> Write representative dependent and functorial categorical binders, elaborate
> them to explicit Core, and inspect checked output in the browser.

Primary CTA: `Try the live reviewer`

Secondary CTA: `Read the book`

Tertiary route: active Lambdapi source.

Verified proof points:

- 10 reviewed example presets;
- 4 categorical binder modes in the graduated text envelope;
- 3 report panels;
- a 199-page development book; and
- client-side execution for the published reviewer.

These are bounded artifact facts, not claims of ecosystem adoption.

### Selected visual and copy direction

Use an editorial research-tool aesthetic: strong typography, restrained color,
mathematical source/output surfaces, generous spacing, responsive layout, and
an explicit `Research draft` status. Avoid generic SaaS gradients,
testimonials, fabricated usage statistics, and stock imagery.

Selected headline:

> Make categorical structure compute.

Selected primary CTA:

> Try the live reviewer

Retained alternatives for later comparison:

1. `Dependent and functorial type theory, running in your browser.`
2. `An executable language for directed dependency.`
3. `Explore a computational foundation for functors, transfors, and directed
   families.`

CTA alternatives:

1. `Elaborate an example`
2. `Open the workbench`
3. `Inspect the Core`

The page should include:

1. a concise hero and transparent research-draft boundary;
2. a compact evidence strip;
3. a three-step explanation from binders to checked Core;
4. the existing categorical/evidence/Core workbench under a stable
   `#reviewer` anchor;
5. short routes to the overview article, full book, active source, and GitHub;
6. a limitations section that is readable without internal project history.

## GitHub Pages Architecture

The selected deployment is a project Pages site built from `main` by GitHub
Actions:

- no generated `gh-pages` branch;
- no committed `dist/`;
- Vite retains relative `base: './'` for project-path portability;
- the workflow builds `emdash-template` with its standalone retained npm
  lockfile;
- the workflow uploads only `emdash-template/dist`;
- deployment uses the official Pages artifact and OIDC workflow;
- Pages is configured with `build_type: workflow`.

This is easier to reproduce and review than maintaining a second generated
branch. A `gh-pages` branch remains a fallback only if the official Actions
route fails for a measured repository constraint.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| PUBLICATION-0A | complete | user direction | Git/reference/ownership audit, exact retirement inventory, artifact roles, Pages state |
| PUBLICATION-PLAN-0B | complete at `72747ec791f648ede3f743052a5705a1e7c3c38f` | PUBLICATION-0A | This living plan plus links from the prior article, book, browser, and handoff ledgers |
| PUBLICATION-CLEAN-1A | complete and focused-green at `72747ec791f648ede3f743052a5705a1e7c3c38f` | PUBLICATION-PLAN-0B | Ignore `.playwright-cli/`; remove exact audited `spec/`, legacy docs, and v2 print sources; update registry and references |
| PUBLICATION-OWNERS-1B | complete and focused-green at `fcf925af85cf078f4956a2208e220fd2dd078909`; real article artifact acceptance belongs to ARTICLE-ARTIFACT-1F | PUBLICATION-CLEAN-1A | Separate book and article promotion owners; add full-book Markdown distribution; remove book-to-article compatibility copying |
| LANDING-REVIEWER-1C | complete and focused-green at `bb6ebee5cb63f950e71040a44be534d67530ed17` | PUBLICATION-PLAN-0B | Responsive landing page and same-page reviewer using the frozen brief |
| ARTICLE-THESIS-1D | in progress; current workbench measured at 23 pages against the selected 14-18 page budget | PUBLICATION-PLAN-0B | Freeze title, abstract promise, outline, evidence map, and page budget against active authorities |
| ARTICLE-PROSE-1E | pending | ARTICLE-THESIS-1D | Rewrite the active v3.2 workbench as the descriptive overview source and register it |
| ARTICLE-ARTIFACT-1F | pending | PUBLICATION-OWNERS-1B, ARTICLE-PROSE-1E | Targeted validation, deterministic PDF, all-page visual QA, and promoted `docs/emdash3_2.{md,pdf}` |
| PUBLICATION-CHECKPOINT-1G | pending | LANDING-REVIEWER-1C, ARTICLE-ARTIFACT-1F | Exact staged review, focused green gates, synchronized ledgers, bounded local checkpoint |
| PUBLICATION-INTEGRATE-1H | pending | PUBLICATION-CHECKPOINT-1G | Fetch, verify ancestry, fast-forward local `main`, and preserve worktree |
| PUBLICATION-PAGES-1I | pending | PUBLICATION-INTEGRATE-1H | Push `main`, configure Actions Pages, monitor deployment, and verify the live reviewer/book/article routes |
| PUBLICATION-GRADUATE-1J | pending | PUBLICATION-PAGES-1I | Freeze the exact public capability, recovery state, and remaining research boundaries |

Rows may be split when a measured issue crosses an ownership boundary. The
living plan must record the split before implementation. A formatting problem
does not authorize mathematical changes.

## Change Log

- **2026-07-30 - `PUBLICATION-0A`, `PUBLICATION-PLAN-0B`, and
  `PUBLICATION-CLEAN-1A` complete and focused-green.** Audited the exact Git,
  remote Pages, source, generated-output, and distribution state. Recorded the
  selected book/article/landing ownership and linked it from the handoff,
  completed book, browser, and historical article ledgers. Added
  `.playwright-cli/` to the root ignore policy without staging its existing
  contents. Removed only the two unreferenced legacy `spec/` sources, six
  legacy root document artifacts, and two v2 print sources recorded above.
  The v3.2 article is now the sole default live article route; all five
  document-registry tests and diff hygiene pass. Historical reports retain
  their path references as provenance, while Git retains the removed bytes.
  No TypeScript semantic, Lambdapi, book, article-render, browser-build, or
  repository aggregate gate was run.
- **2026-07-30 - `PUBLICATION-OWNERS-1B` implementation and focused
  contracts complete.** Replaced the book-only compatibility copier with an
  atomic book artifact promoter that owns both
  `docs/emdash-book.{md,pdf}` and no article path. The promoted Markdown is
  byte-identical to the 427,754-byte manifest assembly with SHA-256
  `e3293ceaf13cbfd4dc33278f4fca6a5e480bfcd506f061ca10728ff134b0f446`;
  the already checked 199-page PDF retains SHA-256
  `b34b7e430deacf4b91ce354c5e5eb3d2674ef08e93d3bcbd4ca7618ea37f41d7`.
  Added one future-multiple-paper registry with safe source, generated-PDF,
  distribution, metadata, required-text, and 14/16/18-page contracts, plus
  focused export, structural check, and atomic promotion commands. All nine
  registry/manifest tests, article diagram validation, script syntax checks,
  and diff hygiene pass. A single targeted build/browser render reports the
  current 8,293-word workbench at 23 two-column pages with no console, page,
  request, or render error. This proves that the requested paper needs
  substantive compression before the new article artifact can pass; it is
  not a tooling blocker. No root TypeScript, Lambdapi, conformance, complete
  print, or book render aggregate was run.
- **2026-07-30 - `LANDING-REVIEWER-1C` complete and focused-green at
  `bb6ebee5cb63f950e71040a44be534d67530ed17`.** Reframed the static React
  fixture as one responsive editorial
  landing and reviewer under a stable `#reviewer` anchor, with transparent
  research boundaries and routes to the overview paper, full book, and
  active Lambdapi source. Preserved the existing ten-preset text adapter,
  three-panel report, and minimal Core API rather than adding a browser-only
  checker. The standalone TypeScript/Vite production build passes. Real
  browser QA at 1440x1000 and 390x844 exercised an ordinary preset, the mixed
  displayed telescope preset, the explicit three-part research report, and
  the editable Core script with no console error or failed static request.
  The mobile full-page visual inspection found no overlap, clipping, or
  unreadable panel. The UI explicitly explains that the embedded report's
  historical “browser promotion: no” line belongs to its pre-browser semantic
  graduation snapshot. Paper and book currently deduplicate only because the
  tracked `docs/emdash3_2.pdf` is still the old book alias; final distinct-link
  acceptance belongs to `ARTICLE-ARTIFACT-1F`.

## Targeted Validation

Avoid unchanged multi-minute repository aggregates. The completed semantic
checkpoints remain the baseline because this plan does not edit their owners.

Use proportional checks:

### Retirement and ownership

```bash
git diff --check
rg <retired-paths>
./scripts/pnpmw --dir emdash2/print run test:registry
```

### Landing and reviewer

```bash
./scripts/pnpmw --dir emdash-template --ignore-workspace run typecheck
./scripts/pnpmw --dir emdash-template --ignore-workspace run build
```

Then exercise the built landing page at desktop and mobile widths, run at
least one ordinary and one displayed preset, inspect all three panels, follow
the book/article links, and require no page, console, or failed-request error.

### Article

```bash
./scripts/pnpmw --dir emdash2/print run test:registry
./scripts/pnpmw --dir emdash2/print exec node scripts/validate_paper.mjs --group=articles
./scripts/pnpmw --dir emdash2/print run build
```

Export the article, run structural/text/font checks, render every page to
images, and visually inspect every page. Iterate until there is no clipping,
overlap, malformed math, broken diagram, orphaned heading, blank page, or
obvious pagination defect.

Do not rerun root TypeScript, Lambdapi, conformance, full print, or full book
aggregates unless the implementation changes their owning files or a focused
check finds evidence that makes the larger gate necessary.

## Checkpoint And Publication Procedure

For every checkpoint:

1. inspect staged and unstaged state separately;
2. stage only exact plan-owned paths;
3. review `git diff --cached --stat`, the full staged diff, and
   `git diff --cached --check`;
4. commit only an internally coherent focused-green tranche;
5. record the checkpoint and next dependency-ready row here.

Before integration:

1. fetch `origin`;
2. verify the branch remains a zero-divergence descendant of both local and
   remote `main` or stop and reconcile without rewriting;
3. fast-forward local `main`;
4. do not remove the goal worktree or branch.

Before publication:

1. push reviewed `main` without force;
2. configure Pages for `workflow` builds;
3. monitor the exact deployment run;
4. inspect the public URL in a real browser;
5. verify reviewer behavior and public book/article links;
6. record the deployed commit and URL.

## Persistent `/goal` Launch Prompt

```text
Continue the next dependency-ready slice in
docs/EMDASH_V3_2_PUBLICATION_AND_ARTICLE_PLAN.md. Treat that file as the
living objective and keep it synchronized when evidence changes the next
slice. Use docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md for recovery, the active
Lambdapi and print authorities for claims and ownership, and
docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md for Git checkpoints.

The objective is one public research product: audited repository retirement,
single-owner book and overview-article artifacts, a polished same-page
landing/reviewer, and verified GitHub Pages publication. Keep general
whole-library scale qualification outside this goal.

Prefer targeted validation. Do not rerun unchanged multi-minute aggregate
gates unless a changed owner or focused failure makes one necessary. Preserve
unrelated work and untracked tool output. The user authorizes bounded green
local checkpoints, deletion of only the exact audited obsolete paths,
fast-forward integration into local main, upstream push, and GitHub Pages
configuration/publication. No force push, history rewriting, branch/worktree
deletion, venue submission, release claim, or unrelated cleanup is
authorized.
```
