# TypeScript Elaborator v3.2 — Integrated External-Reviewer Plan

Date: 2026-07-30
Plan-ID: TS-ELAB-V3.2-INTEGRATED-REVIEWER
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_USER_SYNTAX_PLAN.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md)
Status: approved implementation is present and focused/browser-green under
D-DTTLF-PRODUCT-REVIEWER-001 with human supersession; all reviewed and
proportional final gates are green at exact local checkpoint
`18ca2547bb2f5795127a6589d0531bba87317f19`

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

## REVIEWER-INTEGRATE-1A Implementation Result

The approved implementation is present in the goal worktree:

- `lf_transfer_acquisition_contract.ts` now owns the browser-safe immutable
  selection-contract types, validation, freezing, error identity, and
  contract creator;
- `lf_transfer_acquisition.ts` retains Node-only source/export acquisition,
  canonical parsing, and SHA-256 verification while compatibly re-exporting
  the contract API;
- the six reviewed contract-data consumers import the browser-safe layer
  directly;
- `browser_reviewer.ts` exposes exactly three immutable ordinary text presets,
  one typed text runner, the unchanged three-panel report runner/formatter,
  and a deeply frozen capability boundary;
- the Vite fixture presents editable categorical text by default, runs the
  research report only after an explicit action, preserves the minimal-Core
  playground, links the Vite-emitted book PDF, and states the exact boundary;
  and
- `check:browser-reviewer` is the product-facing fixture gate while
  `check:browser-directed` remains the compatibility alias.

The selected browser closure reaches the contract module but not the Node
acquisition implementation. The error class is shared rather than duplicated,
so Node acquisition and browser contract validation retain identity and
behavior. The fixture's local TypeScript command disables only fixture-level
style diagnostics that would otherwise be reimposed on the whole imported
root research closure; root typecheck and lint remain mandatory.

Measured production output:

- 140 transformed modules;
- generated book asset: 1,789.55 kB;
- initial JavaScript: 428.80 kB / 116.73 kB gzip;
- lazy reviewer chunk: 717.86 kB / 158.56 kB gzip; and
- CSS: 5.67 kB / 2.13 kB gzip.

The chunk-size warning is an observation, not an SLA failure. Real Chromium
rendered the default page, accepted an edited ordinary term, rejected
`λ^f x. K C` at the exact source span, kept the full report non-eager,
ran all three report candidates after the explicit action, opened the
fingerprinted book PDF, and ran the preserved minimal-Core example. The final
browser console contained zero errors, warnings, or other messages.

Focused acquisition, text, reviewer, browser, product, and release/migration
contracts are green. The first aggregate baseline ran 1,135 tests and exposed
only two stale fixture-README wording contracts; both have been corrected and
their focused 11-test suite now passes. Bounded Lambdapi validation,
conformance, browser production, and the active acquisition inventory are
green. The final aggregate result and its exact mechanical correction are
recorded below.

No checker, evaluator, Core node, mathematical owner/rule, semantic profile,
dependency, lockfile, Lambdapi source, deployment, or publication changed.

## Final Validation Corrections

The approved
[`D-DTTLF-PRODUCT-REVIEWER-002`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_D002_REVIEW.md)
correction aligns the current canonical export digest, its one additional
rule/clauses count, and all 48 reordered acquisition-command ordinals. Fresh
live evidence now selects all 73 commands in all eight active core contracts
exactly, and `check:scale-inventory` passes.

The following final aggregate ran all 1,135 tests for 2,080,318 ms:

```text
pass 1077
skip 51
fail 7
```

Every failure is the literal stale expected-ordinal array in the first pinning
test of one derivative representation suite. All remaining tests in those
seven suites—including their declaration/runtime/proof compilation and
execution—pass with the corrected contracts.

### H-DTTLF-PRODUCT-REVIEWER-CORRECTION-02

Proposed decision:
`D-DTTLF-PRODUCT-REVIEWER-003`

Status: frozen, bounded, non-self-authorizing correction addendum

The correction may change only the literal expected ordinal arrays in:

```text
tests/v3_2_scale_stress_2_representation_tests.ts
tests/v3_2_scale_stress_2b_representation_tests.ts
tests/v3_2_scale_stress_2b2_representation_tests.ts
tests/v3_2_scale_stress_2b3_representation_tests.ts
tests/v3_2_scale_stress_3a1_representation_tests.ts
tests/v3_2_scale_stress_3a2a_representation_tests.ts
tests/v3_2_scale_stress_3a2b_representation_tests.ts
```

Each array must become exactly the already-measured active ordinal array
reported by the failed assertion. No test assertion, test name, source
contract, representation, policy, phase, compiler, or runtime behavior may
otherwise change.

Proportional post-correction validation is:

1. the seven exact affected test files;
2. root typecheck and lint;
3. `check:scale-inventory`;
4. `git diff --check`; and
5. exact path-scoped staged review plus `git diff --cached --check`.

The completed full aggregate already executed every other assertion after the
current source/contract correction and isolated these seven data-only
expectations. Repeating its 35-minute computation is therefore not required
by this addendum. This is not a weakening of a test or a substitute for an
unknown failure.

This addendum authorizes no semantic, Lambdapi, product, parser, browser,
dependency, lockfile, deployment, bulk-scale, or broader Git change.
Implementation requires a separate exact review with human supersession.

That separate review is now recorded as
[`D-DTTLF-PRODUCT-REVIEWER-003`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_D003_REVIEW.md).
Only the seven literal arrays above changed. The seven exact affected suites
then passed 27 active tests with seven intentional skips and zero failures.
Root typecheck and lint, isolated `check:scale-inventory` (14/14), bounded
active-kernel validation, conformance, browser production, and
`git diff --check` pass.

The earlier 1,135-test aggregate is therefore retained as the complete
repository execution record: its only seven failures were the now-corrected
data expectations, while every semantic assertion in those suites already
passed. Repeating that 35-minute aggregate is not proportionate after the
exact reviewed correction and focused zero-failure rerun. No test was removed,
weakened, skipped, or behaviorally changed.

## Selected Successor — Syntax Parity, Then Reader-Facing Graduation

The user's direct clarification selects
[`TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md)
as the next product-facing plan after this checkpoint. Its first row inventories
the mathematical construction surface already exposed by direct TypeScript
and maps it to deterministic text routes, prioritizing `^n`, `^fd`, and
`^nd`.

This means:

- grammar parsing remains deterministic;
- syntactically valid input may still fail typed elaboration or internal
  categorical factorization;
- application selection is classifier/expected-type directed, never
  heuristic;
- existing callback APIs are scoped construction mechanisms rather than
  arbitrary JavaScript syntax that text must reproduce; and
- arbitrary pointwise data is never promoted to a coherent functor or
  transformation.

The first syntax-parity inventory is complete, and its exact separately
reviewed `SYNTAX-PARITY-1A` implementation now extends this same reviewer
with three additional presets:

```text
λ^n  k : K. (FF k) (s k)
λ^fd a : E. GG (FF a)
λ^nd k : K. composeCells (theta k) (eta k)
```

Those inputs use the existing dependent-section, displayed-functor, and
displayed-transformation builders and the existing application/cell
composition paths. They do not add another checker, action table, or browser
semantics. Nested/dependent contexts and general structural-constructor text
remain later parity rows.

The updated production build still transforms 140 modules. Its initial
JavaScript is 429.10 kB / 116.78 kB gzip, its lazy reviewer chunk is
723.61 kB / 159.58 kB gzip, and the existing informational chunk warning
remains non-blocking. Real Chromium selected and accepted the exact `^nd`
preset, displayed its backend-neutral explicit Core and inferred/expected
types, and reported zero console errors or warnings.

After exact syntax graduation, the selected route is
[`TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md):
a capability-delta audit, theorem-led book update, deterministic public book
artifact, and consolidated repository introduction.

Bulk scale no longer resumes automatically inside the current persistent
goal. SCALE-STRESS-3C, SCALE-BATCH-1, SCALE-GRADUATE-1, and related pending
rows remain preserved for a future goal. One exact scale dependency may still
move earlier only when the selected reviewer/book example demonstrably needs
it and a separate bounded review authorizes it.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| REVIEWER-INTEGRATE-0A | complete measured audit | existing product/browser/text rows | Combined Vite and Chromium feasibility, exact Node boundary, bundle/runtime orientation, and selected architecture |
| H-DTTLF-PRODUCT-REVIEWER-01 | approved exactly as proposed under D-DTTLF-PRODUCT-REVIEWER-001 with human supersession; proposal checkpoint `f94d770` | REVIEWER-INTEGRATE-0A | Exact runtime-contract split, browser entry, UI, book link, tests, and non-claims |
| REVIEWER-INTEGRATE-1A | final-green under D-DTTLF-PRODUCT-REVIEWER-001 at `18ca2547bb2f5795127a6589d0531bba87317f19` | exact review | Browser-safe contract split and narrow lazy reviewer workbench joining report, text, book, and minimal Core |
| H-DTTLF-PRODUCT-REVIEWER-CORRECTION-01 | complete and approved exactly as proposed under D-DTTLF-PRODUCT-REVIEWER-002 | final active acquisition validation | Refresh only current export/count/ordinal evidence; preserve historical digest evidence and all semantics |
| H-DTTLF-PRODUCT-REVIEWER-CORRECTION-02 | complete and approved exactly as proposed under D-DTTLF-PRODUCT-REVIEWER-003; focused zero-failure correction gate green | D-DTTLF-PRODUCT-REVIEWER-002 plus exact seven failures | Refreshed only seven literal derivative expected-ordinal arrays; no test or behavior delta |
| REVIEWER-GRADUATE-1 | final-green at `18ca2547bb2f5795127a6589d0531bba87317f19` | REVIEWER-INTEGRATE-1A | Runnable reviewer path, observed bundle/runtime envelope, exact non-effects, and syntax-parity successor |
| SYNTAX-PARITY-0A | complete at `d73195b`; D001 separately approved at `55161be` | REVIEWER-GRADUATE-1 and direct TypeScript surface | Executable 68-method/14-capability API-to-text inventory and bounded `^n`/`^fd`/`^nd` proposal |
| SYNTAX-PARITY-1A | final-green at `2e7cc3c44802a5218858ca6747e7591d3bfc4859` | approved D-DTTLF-PRODUCT-SYNTAX-PARITY-001 | Same reviewer exposes the three single-binder modes through existing typed program methods; focused 35/35 and aggregate 1,149/1,149 gates are green |
| SYNTAX-PARITY-1B0 | focused-green zero-delta audit; D002 proposal pending separate review | final-green 1A | Measured direct-green/text-unknown `indexOf` weakening seam and split 1B1 contextual index from 1B2/1B3 multi-binder contexts |
| BOOK-DELTA-0A | selected post-syntax successor | SYNTAX-PARITY-GRADUATE-1 | Capability-oriented book delta audit followed by theorem-led prose/artifact/repository graduation under its dedicated plan |
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
docs/TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_PLAN.md and, after its
green checkpoint, docs/TYPESCRIPT_ELABORATOR_V3_2_SYNTAX_PARITY_PLAN.md and
docs/TYPESCRIPT_ELABORATOR_V3_2_BOOK_AND_REPOSITORY_GRADUATION_PLAN.md, with
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md retained as the
future architecture-qualification ledger and
docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md as the recovery entry point.

Treat the living plans and their Persistent /goal Launch Prompts as part of
the objective. Recover actual state from active code/tests, all worktrees,
staged and unstaged changes, branch ancestry, current authorities, and the
decision/side-task ledgers. Follow root AGENTS.md and the nested emdash2 SOP
for every Lambdapi action.

Finish and preserve the external-reviewer browser journey joining the existing
three-panel report, ordinary categorical text adapter, minimal browser
evidence, and generated emdash book. Then inventory text parity with the
mathematical direct-TypeScript construction surface, prioritizing existing
`^n`, `^fd`, and `^nd` capabilities. Preserve one checker/evaluator,
backend-neutral explicit Core, and direct typed TypeScript. Do not introduce
another semantic frontend or copy a browser action table.

After syntax graduation, follow the book/repository plan: audit capability
deltas from `8217aa3...`, write theorem-led mathematical prose rather than an
implementation diary, validate and deterministically promote the public book
artifact, and consolidate the root README around the book and reviewer.
Preserve bulk systematic-transfer rows as pending work for a future goal.

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

- **2026-07-30 — Final reviewer corrections green; reader-facing successor
  selected.** D-DTTLF-PRODUCT-REVIEWER-003 approved only seven stale ordinal
  arrays. Their exact suites now pass with zero failures, and all proportional
  TypeScript, inventory, conformance, kernel, browser, and diff gates are
  green. After syntax parity, the current product goal now routes to a
  theorem-led book/repository graduation; bulk scale remains pending for a
  future goal.
- **2026-07-30 — REVIEWER-INTEGRATE-1A implemented and successor selected.**
  Added the browser-safe acquisition-contract boundary, narrow lazy reviewer
  entry, consolidated Vite workbench, emitted book link, focused tests, and
  product gate. Production and real-browser measurements satisfy the reviewed
  path. The first aggregate found only two stale fixture-README contracts;
  their focused correction is green. The final aggregate isolated seven
  stale derivative ordinal arrays, and D003's exact proportional correction
  is now zero-failure.
  The user's direct clarification selects a dedicated syntax-parity audit
  against the mathematical direct-TypeScript surface before deferred bulk
  scale.
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
