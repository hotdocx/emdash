# TypeScript Elaborator v3.2 — Integrated External-Reviewer Plan

Date: 2026-07-30
Plan-ID: TS-ELAB-V3.2-INTEGRATED-REVIEWER
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md)
Status: active correction and approved exact proposal; implementation is
dependency-ready under D-DTTLF-PRODUCT-REVIEWER-001 with human supersession

## Human Correction And Product Intent

The external-review CLI, the client-side directed browser, and the
categorical text adapter are not three independent finished products. They
are ingredients of one intended reviewer journey:

1. open one convenient browser workbench;
2. enter and edit ordinary mathematical syntax;
3. run the actual TypeScript emdash elaborator, checker, evaluator, and
   rewrite machinery;
4. inspect explicit Core, inferred type, structural lowering, computation,
   and source-located rejection;
5. run the broader outer-LF, ordinary categorical, and genuinely displayed
   dependent evidence from the same surface; and
6. read the emdash book alongside that executable evidence to assess whether
   the kernel/book form a feasible large-scale research programme.

The documentation-only PRODUCT-GRADUATE-1 proposal and immutable
D-DTTLF-PRODUCT-GRADUATE-001 review remain valid evidence for exactly the
documentation scope they approved. They did not authorize a browser
integration. The user's later explicit clarification supersedes their route
back to scale as a product-completion boundary. Product graduation now
requires the integrated reviewer journey in this plan.

This correction does not say that every TypeScript API or every Lambdapi
owner must be exposed in the first browser. It says that the existing
capabilities must be composed into one truthful, runnable reviewer product
rather than merely documented as separate commands.

## Existing Ingredients

All semantic ingredients for the first integrated journey already exist:

- `runCoreProductReviewDemo` and `formatCoreProductReviewDemo` compose the
  same three structured witnesses used by `demo:external-review`:
  - outer dependent lambda/Pi/Sigma-telescope checking and reduction;
  - ordinary recursive functorial bracket abstraction; and
  - one genuine displayed dependency edge with object- and arrow-level
    evidence;
- `elaborateCoreCategoricalText` accepts editable ordinary `λ^f` syntax,
  recursive whitespace application, optional checked source annotation,
  exact spans, and type-directed whole-Hom action;
- `CoreCategoricalProgram` lowers both direct TypeScript and text resolution
  through the same categorical surface, explicit Core, checker, evaluator,
  and runtime;
- `browser_directed.ts` and `emdash-template` already prove a fully
  client-side Vite/React build and preserve the frozen minimal-Core
  playground; and
- `docs/emdash-book.pdf` is the generated current book artifact.

The missing layer is therefore product composition and one packaging
dependency correction. It is not another AST, parser, checker, evaluator,
categorical action table, or mathematical kernel.

## Measured Integration Audit

### Direct categorical browser probe

A disposable Vite entry imported `CoreCategoricalProgram` and
`elaborateCoreCategoricalText` directly rather than through the broad
`src/v3_2/index.ts` barrel. The unmodified graph failed after 101 transformed
modules because `lf_transfer_acquisition.ts` imports `createHash` from
`node:crypto`.

The graph has more than one route to that one Node builtin. Representative
paths are:

```text
categorical_program
  -> categorical_displayed_nd_higher_target_transfer
  -> categorical_displayed_nd_higher_audit
  -> lf_transfer_acquisition
  -> node:crypto

categorical_program
  -> categorical_surface
  -> categorical_fibred_transfd_transfer
  -> scale_stress_2_representation
  -> scale_stress_2_acquisition
  -> lf_transfer_acquisition
  -> node:crypto
```

The included graph contains no other Node builtin. The runtime
representations import only the immutable selection-contract type and
`createCoreLfCanonicalSelectionContract`; they do not acquire source text or
compute a digest during normal checking.

### Disposable boundary substitution

A disposable Vite-only substitution for the unavailable Node hash function
was used as a diagnostic, not as the proposed implementation:

- the real categorical program and text adapter built successfully:
  101 modules, 913.10 kB minified JavaScript / 202.03 kB gzip;
- a headless Chromium load executed the real ordinary program and rendered
  the checked explicit Core `(free "x")`; and
- the only console event was an irrelevant missing favicon.

The substitution proves that the packaging blocker is the acquisition hash
edge. It is not acceptable as the committed design because a throwing
browser crypto stub would leave acquisition and immutable runtime-contract
ownership inverted.

### Combined report probe

The disposable entry then added the existing `runCoreProductReviewDemo`
module:

- production build: 106 modules, 931.88 kB minified JavaScript /
  207.79 kB gzip;
- Chromium executed the text term and all three existing report candidates:
  `emdash-v3.2-dttlf-directed-1`,
  `emdash-v3.2-usability-1d`, and
  `emdash-v3.2-displayed-chain-1a`; and
- the full report took roughly one minute in this orientation probe.

The observed time is not a performance SLA. It is sufficient to reject eager
full-report execution on page load. The initial page should remain
responsive, and the heavy report should run only after an explicit reviewer
action with visible progress. Dynamic import may keep the categorical/report
closure out of the initial directed/minimal chunk.

## Selected Architecture

```text
generated emdash book PDF
             |
             v
integrated browser reviewer shell
   |              |                    |
   |              |                    +--> preserved minimal Core playground
   |              |
   |              +--> editable categorical text
   |                    -> existing parser/resolver adapter
   |                    -> existing CoreCategoricalProgram
   |                    -> explicit Core/checker/evaluator/runtime
   |
   +--> explicit "Run full review"
          -> existing runCoreProductReviewDemo
          -> outer LF + ordinary bracket + displayed dependency

Node-only development/conformance side
   -> source/export text + SHA-256 + Lambdapi acquisition
   -> verifies the same immutable selection contracts
```

### Acquisition/runtime ownership correction

Add a small browser-safe contract module that owns:

- canonical command-expectation and selection-contract data types;
- exact contract-shape validation;
- deep freezing; and
- `createCoreLfCanonicalSelectionContract`.

Keep these Node/developer-only operations in
`lf_transfer_acquisition.ts`:

- source and canonical-export text acquisition;
- SHA-256 computation;
- canonical Lambdapi export parsing; and
- command digest/fact comparison.

`lf_transfer_acquisition.ts` re-exports the contract API for compatibility.
The six existing contract-data consumers import the browser-safe contract
module directly. Node tests continue to verify the complete acquisition path
against Node's SHA-256 implementation and active source/export evidence.

This is a dependency inversion, not a new LF feature. It changes no
declaration, rule, policy, checker, evaluator, or Core semantics.

### Browser capability boundary

Add one narrow `browser_reviewer.ts` module. It must:

- expose structured text presets and a runner for editable ordinary
  categorical text;
- expose the existing three-panel report and formatter behind an explicit
  runner;
- import concrete modules directly, never the broad `src/v3_2/index.ts`
  barrel;
- keep `CoreCategoricalProgram` and acquisition APIs out of the browser's
  public editable JavaScript object;
- advertise exact capabilities and non-claims in one deeply frozen boundary;
  and
- invoke no Lambdapi process, network service, filesystem, or Node builtin.

The current three profile-gated `require` seams in
`categorical_program.ts` are not exercised by the selected ordinary or
displayed-chain reviewer profiles. The browser entry does not expose an
arbitrary profile constructor. The production build and runtime closure must
prove that these dormant internal seams neither request a Node module nor
escape the selected capability. Removing the circularity seams repository-
wide is not a hidden prerequisite unless the measured build/runtime falsifies
that isolation.

### Reviewer experience

The first page should explain one short review path:

1. open the book;
2. edit and run an ordinary categorical expression;
3. inspect explicit Core, inferred type, structural owners, and diagnostics;
4. run the full three-panel research witness when ready; and
5. read the exact supported/deferred boundary.

The page should preserve the minimal-Core playground as implementation-level
evidence. The directed-only view may remain as a fast witness, but it is no
longer presented as a separate product.

The book link should use Vite's asset pipeline from the generated
`docs/emdash-book.pdf`; no hand-copied or hand-edited PDF enters the fixture.
The static output should remain project-subpath-compatible. A GitHub Pages
workflow, remote deployment, custom domain, and publication remain separate
operations.

## Demo-Driven Scale Priority

Scale qualification is evidence and infrastructure for the product, not an
artificially later silo. If a compelling reviewer witness needs one
particular currently planned scale item, that exact dependency may be
promoted before the bulk scale order.

Such promotion must identify:

- the exact Lambdapi owner, declaration, runtime rule, proof-time rule, or
  unification mechanism;
- why the reviewer witness cannot truthfully express the intended concept
  without it;
- the smallest dependency closure;
- the positive consumer and fail-closed negative/non-collapse witness; and
- a separately reviewed bounded implementation proposal.

This policy does not authorize bulk acquisition, arbitrary parser work, or a
generic claim that “the demo needs scale.” The current measured integrated
journey already has an outer-DTT, ordinary categorical, and genuinely
displayed dependent witness, so no new scale semantic is a prerequisite for
the first browser integration. Reviewer feedback or a later selected
mathematical story may justify a specific promotion.

## H-DTTLF-PRODUCT-REVIEWER-01 — Frozen Exact Proposal

Decision:
`D-DTTLF-PRODUCT-REVIEWER-001`

Separate review:
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_D001_REVIEW.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_D001_REVIEW.md)

Status: approved exactly as proposed under the user's standing unattended
delegation with human supersession after proposal checkpoint `f94d770`

### Exact implementation

1. Extract the browser-safe immutable acquisition-contract layer described
   above and retain the complete Node acquisition adapter as its compatible
   verifier/consumer.
2. Update only existing selection-contract data consumers to import the
   contract layer directly.
3. Add `src/v3_2/browser_reviewer.ts` with:
   - three immutable ordinary text presets covering recursive pointwise
     application, fixed-inner evaluation, and whole-Hom action;
   - one request runner returning input, expected mode, explicit Core,
     inferred type, structural prerequisites, and exact diagnostic data;
   - the existing full product-report runner/formatter; and
   - a deeply frozen capability/non-claim boundary.
4. Update `emdash-template` into one reviewer workbench:
   - the default interactive categorical-text view;
   - a research-evidence view with an explicit, non-eager full-report action
     and visible running state;
   - the preserved minimal-Core playground;
   - a generated-book link and concise reviewer path; and
   - an exact current-boundary panel.
5. Load the heavy reviewer module lazily if the production measurement
   confirms that doing so keeps initial rendering materially smaller or
   avoids eager work.
6. Add `check:browser-reviewer` as the current product-facing strict
   TypeScript/Vite command while retaining `check:browser-directed` as a
   compatibility alias until a later cleanup decision.
7. Add focused tests for:
   - all three text presets and an edited/source-located failure;
   - exact equality with the existing text/direct-program path where
     applicable;
   - execution of the unchanged three report candidates;
   - the immutable browser boundary;
   - a Node-free selected transitive closure containing the contract layer
     but not the Node acquisition implementation;
   - generated book-asset wiring;
   - the preserved frozen minimal browser entry; and
   - strict production build plus a real-browser interaction of text,
     full-report, book-link, and minimal-Core views.
8. Update the external-review guide and all living navigation so the
   integrated browser is the primary reviewer product and the CLI remains
   its reproducible terminal form.

### Expected tracked scope

Runtime/refactor:

- new `src/v3_2/lf_transfer_acquisition_contract.ts`;
- modified `src/v3_2/lf_transfer_acquisition.ts`;
- direct import updates in:
  - `src/v3_2/scale_stress_1_acquisition.ts`;
  - `src/v3_2/scale_stress_1b_proposal.ts`;
  - `src/v3_2/scale_stress_2_acquisition.ts`;
  - `src/v3_2/scale_stress_3_acquisition.ts`;
  - `src/v3_2/scale_stress_3b_acquisition.ts`; and
  - `src/v3_2/categorical_displayed_nd_higher_audit.ts`;
- new `src/v3_2/browser_reviewer.ts`; and
- additive exports from `src/v3_2/index.ts` only where needed for root
  TypeScript consumers; the browser imports the concrete entry directly.

Product surface:

- `emdash-template/src/App.tsx`;
- `emdash-template/src/emdash_api.ts`;
- `emdash-template/src/styles.css`;
- root and fixture package scripts only as required for
  `check:browser-reviewer`; and
- no dependency or lockfile change.

Tests and documentation:

- one focused browser-reviewer test module wired into
  `tests/main_tests.ts`;
- existing acquisition/browser/product tests updated only for the corrected
  module boundary and product entry;
- this plan plus the product, browser, syntax, scale, handoff,
  external-review, and README navigation.

If implementation evidence requires another tracked runtime file, stop and
amend/review this proposal rather than silently broadening it.

### Acceptance

The row is complete only when:

- contract creation remains expression-for-expression compatible with the
  existing Node acquisition tests;
- the full acquisition and active-source conformance gates still pass;
- focused text, product-report, browser, and acquisition tests pass;
- root typecheck and lint pass;
- the aggregate TypeScript suite has zero failures;
- the standalone fixture strict typecheck and Vite production build pass;
- the selected browser closure has no Node builtin or Lambdapi process;
- the page initially renders without executing the full report;
- a real browser runs one edited positive text term, one source-located
  negative, the explicit full report, and the minimal-Core example;
- the book link resolves to the Vite-emitted current PDF asset;
- observed bundle/startup/full-report behavior is recorded without claiming
  an SLA;
- exact staged diff review and `git diff --cached --check` pass; and
- living plans record the result, non-effects, and next dependency-ready
  product or selectively justified scale row.

### Explicit non-authorization

This proposal authorizes no:

- new mathematical owner, declaration, runtime rule, proof rule,
  unification rule, checker/evaluator branch, Core node, or semantic profile;
- second parser, AST, resolver, checker, evaluator, or browser-only action
  table;
- displayed text syntax, additional binder mode, final notation decision,
  or arbitrary displayed telescope claim;
- Node crypto polyfill or disabled/faked source-integrity gate;
- dependency or lockfile change;
- Lambdapi source change;
- automatic eliminator generation, source inductive API, or deferred
  declaration-refinement feature;
- bulk transfer, WalkingEnd/HIT, batch, groupoidal closure, or whole-library
  graduation claim;
- GitHub Pages workflow, deployment, publication, push, merge, PR, release,
  rebase, amend, reset, history rewrite, branch/worktree deletion, or
  unrelated cleanup.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| REVIEWER-INTEGRATE-0A | complete measured audit | existing product/browser/text rows | Combined Vite and Chromium feasibility, exact Node boundary, bundle/runtime orientation, and selected architecture |
| H-DTTLF-PRODUCT-REVIEWER-01 | approved exactly as proposed under D-DTTLF-PRODUCT-REVIEWER-001 with human supersession; proposal checkpoint `f94d770` | REVIEWER-INTEGRATE-0A | Exact runtime-contract split, browser entry, UI, book link, tests, and non-claims |
| REVIEWER-INTEGRATE-1A | dependency-ready under D-DTTLF-PRODUCT-REVIEWER-001 | exact review | Implement and validate the integrated reviewer workbench |
| REVIEWER-GRADUATE-1 | gated | REVIEWER-INTEGRATE-1A | Freeze the runnable reviewer path, performance observation, exact evidence envelope, and next product/scale priority |
| SELECTIVE-DEMO-SCALE-* | conditional, none selected now | measured missing reviewer concept plus separate proposal | Promote only a named scale dependency required by a compelling witness |

## Git And Persistent-Goal Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Existing authority permits bounded green local checkpoint commits on
`goal/typescript-elaborator-v3.2` after synchronized ledgers, exact staged
diff review, and `git diff --cached --check`.

It authorizes no push, merge, PR, publication, release, deployment, rebase,
amend, reset, history rewrite, branch/worktree removal, or unrelated cleanup.

## Persistent `/goal` Launch Prompt

```text
Continue the dependency-ready work routed by
docs/TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md, with
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md retained as the
top-level architecture-qualification ledger and
docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md as the recovery entry point.

Treat the living plans and their Persistent /goal Launch Prompts as part of
the objective. Recover actual state from active code/tests, all worktrees,
staged and unstaged changes, branch ancestry, current authorities, and the
decision/side-task ledgers. Follow root AGENTS.md and the nested emdash2 SOP
for every Lambdapi action.

The current product objective is one external-reviewer browser journey that
joins the existing three-panel report, ordinary categorical text adapter,
minimal browser evidence, and generated emdash book. Preserve one existing
checker/evaluator, backend-neutral explicit Core, and direct typed TypeScript.
Do not introduce another semantic frontend or copy a browser action table.

Follow only separately reviewed exact implementation scopes. A compelling
reviewer witness may promote one specifically identified scale dependency
ahead of bulk order, but only after a measured need and separately reviewed
bounded proposal. This is not authority for bulk acquisition or arbitrary
scale work.

Existing Git authority permits only bounded green local checkpoints in the
dedicated goal worktree after synchronized ledgers and exact staged-diff
review. Do not push, merge, publish, deploy, release, amend, rebase, reset,
rewrite history, delete branches/worktrees, or perform unrelated cleanup.
```

## Change Log

- **2026-07-30 — D-DTTLF-PRODUCT-REVIEWER-001 recorded.** After no immediate
  human objection to checkpoint `f94d770`, applied the user's standing
  unattended delegation with human supersession through a separate immutable
  review. Only the exact contract-layer, narrow reviewer entry, UI/book,
  tests, and documentation scope is authorized; no semantics, dependencies,
  Lambdapi source, deployment, bulk scale, or broader Git action is approved.
- **2026-07-30 — Integrated product intent corrected and measured.** Recorded
  the user's clarification that CLI, browser, text syntax, and book are one
  reviewer journey. A direct categorical browser probe isolated the single
  Node builtin to acquisition hashing. A disposable boundary substitution
  Vite-built and Chromium-ran the real text program and the existing
  three-panel report. Selected a browser-safe acquisition-contract split,
  lazy explicit full-report action, editable text panel, generated-book link,
  and preserved minimal playground. Froze
  H-DTTLF-PRODUCT-REVIEWER-01 / D-DTTLF-PRODUCT-REVIEWER-001 without
  self-authorization.
