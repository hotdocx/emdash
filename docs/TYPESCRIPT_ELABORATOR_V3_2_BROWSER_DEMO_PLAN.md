# TypeScript Elaborator v3.2 — Browser Demonstration Plan

Date: 2026-07-29
Plan-ID: TS-ELAB-V3.2-BROWSER-DEMO
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md),
[`TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md`](./TYPESCRIPT_ELABORATOR_V3_2_EXTERNAL_REVIEW_DEMO.md),
and
[`TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`](./TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md)
Supersedes: no mathematical profile, checker, Core owner/rule set, release
profile, or user-syntax decision
Status: active product subplan; measured BROWSER-0A audit complete;
BROWSER-DIRECTED-1A is approved exactly as proposed under
D-DTTLF-PRODUCT-BROWSER-001 with human supersession, implemented, and
final-green; categorical promotion and static publication remain separately
gated

## Purpose

The repository has substantial checked TypeScript functionality, but an
external reviewer currently reaches the strongest examples through root
command-line programs. This plan adds a browser experience without treating
packaging as new mathematical evidence and without weakening the deliberately
narrow, frozen `emdash-v3.2-mvp-1` browser API.

The browser work is split into two independently truthful products:

1. an inexpensive outer-dependent-LF demonstration whose complete dependency
   graph is already browser-safe; and
2. a later categorical/directed-DTT promotion that first separates immutable
   runtime transfer specifications from Node-only acquisition and audit
   evidence.

This split is not a retreat from the categorical product goal. It prevents a
Node packaging issue from being misdiagnosed as a categorical-kernel gap, and
it makes a useful browser artifact available while the larger runtime
boundary is corrected.

The selected deployment model is a fully client-side static build, with
`https://hotdocx.github.io/emdash/` as the likely eventual host. Sandpack
compatibility is no longer a requirement. The current checker/evaluator
closure needs no backend; a Node service remains a fallback only for a later
capability that cannot be made browser-safe. Static-site workflow creation
and publication are separate Git/remote operations and are not authorized by
this plan.

## Authority And Non-Claims

The active Lambdapi v3.2 kernel remains the mathematical authority. Browser
execution reuses the same TypeScript checker, evaluator, explicit Core, and
already reviewed continuation code as the root demos. It does not:

- invoke Lambdapi, a shell, a filesystem API, or a network service;
- add or change a mathematical owner, runtime rule, proof rule, unification
  rule, or checker judgment;
- change `CORE_MVP_MANIFEST` or claim that a root-only continuation has become
  part of the frozen MVP release profile;
- add a second checker, evaluator, or browser-only semantic implementation;
- claim categorical-browser support merely because the outer LF demo builds;
  or
- claim whole-library mechanical-transfer graduation.

The existing [`src/v3_2/browser.ts`](../src/v3_2/browser.ts) remains the
frozen minimal browser entry. New capabilities use additive, explicitly named
browser entries so old consumers retain the exact reviewed boundary.

## BROWSER-0A — Completed Measured Audit

### Existing browser fixture

`emdash-template` is a standalone React/Vite distributable fixture rather
than a contributor workspace package. Its `src/emdash_api.ts` re-exports the
frozen `src/v3_2/browser.ts` entry. Its current page:

- exposes an editable explicit-Core JavaScript example through a local
  `new Function` call;
- constructs and checks a category-polymorphic identity;
- displays `CORE_MVP_MANIFEST.revision`; and
- production-builds without a Node polyfill or Lambdapi.

That page is a functioning minimal-Core playground. It is not presently a
categorical contextual-binder playground, and this plan will not relabel it
as one.

### Static dependency-closure measurement

A source-import closure walk produced these orientation measurements:

| Entry | Files | TypeScript source bytes | Node boundary |
| --- | ---: | ---: | --- |
| `src/v3_2/browser.ts` | 13 | 291,932 | none |
| directed dependent demo | 38 | 705,727 | none |
| ordinary categorical bracket demo | 119 | 3,327,145 | reaches `node:crypto` |
| displayed-chain demo | 118 | 3,320,034 | reaches `node:crypto` |
| three-panel product report | 121 | 3,354,869 | reaches `node:crypto` |

These are source-graph measurements, not minified bundle sizes or a
performance SLA. Type-only and dynamically selected edges make them useful
for comparison rather than release accounting.

### Actual build and runtime probes

A temporary Vite production build that imported the full three-panel product
report failed. The path reaches
`src/v3_2/lf_transfer_acquisition.ts`, which imports `createHash` from
`node:crypto`; Vite correctly externalized the Node builtin and then rejected
the unavailable browser export.

The reachability is not inherent to the categorical checker:

```text
product report
  -> categorical demos/program assembly
  -> transferred profile/audit representations
  -> source acquisition and digest evidence
  -> node:crypto
```

The same categorical program assembly also retains a small number of runtime
`require` seams used to break circular profile dependencies. Those seams
must be removed or isolated before categorical browser promotion.

By contrast, a temporary Vite production build of the directed dependent demo
succeeded:

- 41 transformed modules;
- 0.866-second observed build;
- 221.72 kB JavaScript, 52.25 kB gzip; and
- no Node builtin, process, filesystem, or Lambdapi dependency.

The built page was served locally and exercised in a real Chromium session.
It displayed the complete dependent report: direct TypeScript input, explicit
Core, inferred and reduced dependent types, the two-step reduction trace, and
the negative diagnostic. The only console event was an irrelevant missing
favicon. Temporary build, server, and browser artifacts were removed after
the audit.

### Diagnosis

The full-report failure is a source/runtime layering issue:

- immutable declarations and rules needed at runtime are currently obtained
  through modules that also own source provenance and content-digest checks;
- the digest and canonical-source evidence is correctly Node-only developer
  infrastructure;
- the already compiled runtime specifications themselves need not depend on
  Node; and
- no mathematical owner or LF feature is missing because of this boundary.

The intended correction is therefore to separate browser-safe immutable
runtime transfer specifications from build-time acquisition, hash, source,
and conformance evidence. The Node gate must continue to verify that the
runtime specifications agree with the active source. A browser bundle must
not polyfill `node:crypto`, skip source-integrity checks while pretending to
perform them, or duplicate the checker and categorical program.

## Alternatives Considered

### A. Bundle a Node crypto polyfill

Rejected. It increases the browser boundary and hides an architectural
dependency inversion. A browser never needs to recompute the repository
source digest in order to evaluate a frozen runtime specification.

### B. Copy only the demo's final strings into the UI

Rejected as the product implementation. Static screenshots or strings are
useful documentation, but they would not demonstrate that the checker and
evaluator execute in the browser.

### C. Duplicate a browser-specific categorical catalog

Rejected. It would create two semantic profile assemblies and allow the
browser to drift from the root checker.

### D. Delay all browser work until every categorical module is clean

Not selected. The complete outer-DTT demo is already browser-safe and useful.
Publishing it behind an additive entry does not constrain the later
categorical architecture.

### E. Stage the promotion

Selected:

1. add the proven directed dependent browser entry and page;
2. preserve the existing minimal playground;
3. separately refactor runtime specifications away from Node audit modules;
4. prove an ordinary categorical bracket bundle first; and
5. only then consider the displayed-chain or combined report.

## Selected Browser Architecture

```text
frozen src/v3_2/browser.ts
        |
        +--> existing explicit-Core playground

additive src/v3_2/browser_directed.ts
        |
        +--> same frozen browser exports
        +--> run/format directed dependent demo
        |
        +--> fixed browser demonstration panel

later browser_categorical.ts (not yet authorized)
        |
        +--> browser-safe immutable runtime specs
        +--> existing CoreCategoricalProgram
        +--> ordinary/displayed demos after measured qualification
```

Browser entries are capability boundaries, not new semantic profiles.
`browser_directed.ts` must say explicitly that the continuation remains
opt-in and root-authority-aligned rather than part of
`CORE_MVP_MANIFEST`.

## BROWSER-DIRECTED-1A — Frozen Exact Proposal

Gate:
`H-DTTLF-PRODUCT-BROWSER-01 / D-DTTLF-PRODUCT-BROWSER-001`

Separate review:
[`TYPESCRIPT_ELABORATOR_V3_2_BROWSER_D001_REVIEW.md`](./TYPESCRIPT_ELABORATOR_V3_2_BROWSER_D001_REVIEW.md),
approved as proposed under the user's standing unattended delegation with
human supersession after proposal checkpoint `2d0583e`.

### Proposed implementation

1. Add `src/v3_2/browser_directed.ts` as an additive browser-safe entry. It
   re-exports the frozen minimal browser API and only the structured
   `runCoreDirectedDependentDemo` / `formatCoreDirectedDependentDemo`
   interface needed by this witness.
2. Add a small immutable boundary record describing:
   - the opt-in `emdash-v3.2-dttlf-directed-1` result identity;
   - zero production Lambdapi/process/filesystem dependency;
   - the unchanged `CORE_MVP_MANIFEST`; and
   - the fact that categorical bracket/displayed profiles are absent.
3. Update `emdash-template` to offer two explicit views:
   - the existing editable minimal-Core playground; and
   - a fixed “Dependent LF demo” that runs the actual browser-safe demo and
     renders its deterministic report.
4. Keep the existing example available and do not silently execute arbitrary
   editable text when the fixed dependent demo is selected.
5. Add focused root tests that:
   - import and execute the additive entry;
   - validate its exact boundary record and result;
   - walk its transitive local import closure and reject Node builtins; and
   - prove the old `browser.ts` source and frozen manifest are unchanged.
6. Add one bounded browser-fixture check command or documented command that
   performs strict TypeScript compilation and a Vite production build.
7. Configure relative production asset URLs so the build works from a static
   project subpath such as `/emdash/`, without retaining the obsolete
   Sandpack-only public HTML fixture.
8. Exercise the built page in a real browser and record its visible result
   and console status before checkpointing.

### Exact exclusions

BROWSER-DIRECTED-1A does not authorize:

- changing `src/v3_2/browser.ts` or `CORE_MVP_MANIFEST`;
- exporting `CoreCategoricalProgram` or a categorical demo to the browser;
- a string parser, editor language service, worker, or server;
- a GitHub Pages workflow, remote deployment, or publication;
- Node polyfills;
- Lambdapi invocation in production;
- a new owner, rule, checker/evaluator case, transfer engine, or profile;
- categorical-browser, usability, or mechanical-transfer graduation; or
- remote Git or publication actions.

### Acceptance

The row is complete only when:

- focused tests pass;
- root TypeScript checking passes;
- the standalone fixture passes strict TypeScript and Vite production build;
- a real browser displays the dependent witness;
- the transitive entry closure contains no Node builtin;
- the exact staged diff contains no unrelated work; and
- the living product, browser, scale, and handoff ledgers record the result
  and non-effects.

## BROWSER-DIRECTED-1A Completion

The approved additive slice is implemented.

### Product entry and boundary

[`src/v3_2/browser_directed.ts`](../src/v3_2/browser_directed.ts):

- re-exports the exact frozen `browser.ts` API without modifying that file;
- exports the existing structured directed-dependent result and formatter;
- provides `runCoreDirectedBrowserDemo` as an import-side-effect-free browser
  smoke seam;
- checks the base manifest and continuation result identities at runtime; and
- publishes the deeply frozen `BROWSER-DIRECTED-1A` boundary with zero Node,
  parser, categorical-profile, or production-Lambdapi dependency.

The SHA-256 of `src/v3_2/browser.ts` remains
`9923a7a85672d6fbf6441f23f69f1062c702764167338ee40e1a65be9e42cfcc`.
`CORE_MVP_MANIFEST` retains its exact reviewed content hash. The additive
entry does not enter the frozen browser module's own exports.

### Browser experience

The existing `emdash-template` fixture now has two explicit views:

1. **Dependent LF demo.** The default fixed view runs the actual
   `emdash-v3.2-dttlf-directed-1` TypeScript checker/evaluator witness and
   displays its input path, assumptions, explicit Core, inferred/reduced
   dependent types, two-step computation trace, wrong-family rejection, and
   production boundary.
2. **Minimal Core playground.** The former editable
   `emdash-v3.2-mvp-1` JavaScript playground remains available and still
   checks the category-polymorphic identity through a fresh session.

The historical v1 `emdash-template` at `f50ecb5` was inspected before the UI
edit. It used essentially the same editable-JavaScript shell, but depended on
the retired global reset and legacy elaborator. The new page preserves only
that useful interaction continuity; it uses no v1 state, parser, term model,
or compatibility API.

### Static-hosting correction

Following the user's explicit clarification, Sandpack is not a requirement.
The fixture now has a Vite configuration with `base: './'`, removes the
obsolete Sandpack-only public HTML file, and emits relative production asset
URLs. The exact generated page references:

```text
./assets/index-BrtZm8tA.js
./assets/index-BjwqK14e.css
```

This makes a client-only project-subpath deployment such as
`https://hotdocx.github.io/emdash/` feasible. No backend, workflow, push, or
publication was added. The retained package/directory identity is a fixture
compatibility detail, not a Sandpack product commitment.

### Strict fixture hygiene

The larger browser closure exposed four pre-existing declarations rejected by
the fixture's stricter `noUnusedLocals` setting. The implementation removed
one unused proposal helper and three unused imports. This is a mechanical
zero-runtime-effect cleanup; no declaration, rule, checker, evaluator, or
surface behavior changed.

The MIGRATE-2 fixture invariant now requires the additive entry and separately
requires that it re-export the frozen base. It continues to audit the original
minimal entry's Node-free closure.

### Validation

- focused BROWSER-DIRECTED-1A: 5/5 pass;
- focused MIGRATE-2 browser/fixture regression: 6/6 pass;
- root typecheck and affected lint: pass;
- aggregate TypeScript runtime suite: 1,114 tests, 1,063 active passes,
  51 intentional skips, zero failures, 806,550 ms;
- standalone strict TypeScript plus Vite production gate: pass;
- production build: 75 transformed modules, 421.35 kB JavaScript /
  114.31 kB gzip, 1.83 kB CSS / 0.77 kB gzip;
- transitive local entry closure: at least 38 modules and zero Node builtin;
  and
- real Chromium: both views run, the dependent report contains every
  reviewed evidence field, and the final console has zero errors and zero
  warnings.

The first aggregate run usefully exposed the two stale MIGRATE-2 fixture
expectations. After updating those exact invariants, their focused suite and
the repeated full aggregate pass. This was a product-boundary synchronization,
not a semantic correction.

### Exact non-effects

The completion adds no parser, dependency/lock change, categorical browser,
Lambdapi source/process, mathematical owner, runtime/proof/unification rule,
checker/evaluator branch, contextual compiler case, backend, worker, remote
workflow, publication, or scale/graduation claim.

## BROWSER-CATEGORICAL-0A — Deferred Runtime-Boundary Refactor

This row is architecture work, not a browser styling task. Before any
categorical browser entry is proposed, it must:

1. identify every runtime import from categorical program assembly into
   acquisition, digest, source-text, audit, proposal, or review modules;
2. extract only immutable declaration/rule/runtime specification data into
   Node-independent modules;
3. retain source hashes and active-Lambdapi comparisons in Node-only gates
   that verify those exact specs;
4. remove runtime `require` seams from the selected browser closure without
   broad barrel imports;
5. preserve a single `CoreCategoricalProgram` and one checker/evaluator;
6. Vite-build and browser-run the ordinary bracket witness;
7. measure bundle/startup cost; and
8. freeze a separate exact proposal before exposing displayed dependency or
   the combined product report.

The ordinary bracket is the first categorical candidate because it exercises
recursive variable occurrence, diagonal, exchange, evaluation, and
object/arrow-aware application with less transfer closure than the displayed
chain. Successful ordinary promotion will not automatically approve the
displayed profile.

## Work Ledger

| Row | Status | Depends on | Deliverable |
| --- | --- | --- | --- |
| BROWSER-0A | complete | PRODUCT-DEMO-1B | Measured static closure, actual Vite success/failure, real-browser directed witness, and packaging diagnosis |
| BROWSER-DIRECTED-1A | complete and final-green; local implementation checkpoint to be recorded immediately after this synchronized tranche | BROWSER-0A and D-DTTLF-PRODUCT-BROWSER-001 | Additive directed browser entry, two-view fixture, focused safety tests, portable static production build, and real-browser evidence |
| BROWSER-CATEGORICAL-0A | deferred; not selected by D-001 | BROWSER-DIRECTED-1A or independent priority | Separate immutable runtime specs from Node acquisition/audit evidence and qualify the ordinary bracket bundle |
| BROWSER-CATEGORICAL-1A | gated | BROWSER-CATEGORICAL-0A plus separate review | Additive ordinary categorical browser entry and UI |
| BROWSER-DISPLAYED-1A | gated | browser-safe displayed closure plus separate review | Displayed-chain browser witness without widening the claimed usability envelope |
| BROWSER-STATIC-DEPLOY-0A | deferred; publication not authorized | BROWSER-DIRECTED-1A and an explicit deployment priority | Audit the existing repository CI/pages configuration and freeze an exact static artifact/workflow/domain proposal; no Node backend unless a measured client-side blocker exists |
| BROWSER-GRADUATE-1 | complete for the selected directed slice; does not graduate categorical/deploy rows | BROWSER-DIRECTED-1A | Exact browser capability, package/runtime boundary, observed build, static-host feasibility, residual categorical/deployment gates, and product-plan handoff recorded above |

## Git Boundary

This plan inherits
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Existing authority permits bounded green local checkpoint commits only in
the dedicated goal branch/worktree after exact staged-diff inspection and
ledger synchronization.

No push, merge, PR, release, publication, rebase, amend, reset, history
rewrite, branch/worktree deletion, or unrelated cleanup is authorized.

## Persistent `/goal` Launch Prompt

```text
Continue the next dependency-ready reviewed row routed by
docs/TYPESCRIPT_ELABORATOR_V3_2_BROWSER_DEMO_PLAN.md, while retaining
docs/TYPESCRIPT_ELABORATOR_V3_2_PRODUCT_DEMO_PLAN.md as the product ledger,
docs/TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md as the top-level
architecture ledger, and docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md as the
recovery entry.

Recover actual code, tests, worktrees, ancestry, staged and unstaged state,
and living decisions before acting. Preserve the frozen minimal browser API
and all completed semantic checkpoints. Browser entries are additive
capability boundaries, not new mathematical profiles.

Take only separately reviewed rows. Keep the browser free of Node builtins,
production Lambdapi, duplicated checkers, duplicated categorical catalogs,
and source-acquisition/hash work. If categorical promotion reaches Node-only
audit modules, fix the runtime/audit layering through a measured proposal;
do not polyfill around it or invent kernel mathematics.

The user's standing unattended delegation permits separate approval of a
narrowly frozen dependency-ready proposal after no immediate response, with
human supersession and the Git checkpoint SOP. It does not authorize broader
browser, parser, semantic, publication, or Git effects.
```

## Change Log

- **2026-07-29 — BROWSER-0A completed.** Measured the existing fixture and
  root continuation closures. The full product report fails a Vite build
  because categorical profile assembly reaches Node-only acquisition/digest
  evidence; the directed dependent report builds at 221.72 kB / 52.25 kB
  gzip and runs correctly in Chromium. Classified this as a runtime/audit
  layering issue, selected a cheap additive directed browser slice, and
  deferred categorical promotion to a dedicated runtime-spec separation
  audit.
- **2026-07-29 — D-DTTLF-PRODUCT-BROWSER-001 recorded with human
  supersession.** After no immediate objection to proposal checkpoint
  `2d0583e`, the user's standing unattended delegation approved only the
  additive directed-dependent entry, two-view fixture, focused Node-free
  tests, production build, and browser smoke run. Categorical promotion,
  parsing, dependencies, semantics, and broader Git effects remain closed.
- **2026-07-29 — BROWSER-DIRECTED-1A implemented and final-green.** Added
  the opt-in browser entry and exact frozen boundary, retained the unchanged
  minimal entry, exposed fixed dependent-LF and editable minimal-Core views,
  made Vite output portable to a static `/emdash/` project path, and removed
  the obsolete Sandpack-only public page. Five focused browser checks, six
  MIGRATE-2 checks, strict fixture build, real Chromium with a clean console,
  and the 1,114-test aggregate pass. No categorical browser, parser,
  dependency, backend, semantics, or publication was added.
