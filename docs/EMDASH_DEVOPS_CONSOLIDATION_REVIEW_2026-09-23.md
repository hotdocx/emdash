# Emdash DevOps Consolidation Review

Date: 2026-09-23
Status: review complete; implementation stages below are proposals, not selected work.
Reviewed baseline: local `main` at `44f50587`, initially clean and four commits
ahead of the local `origin/main` tracking ref. No remote refresh was performed.

This review concerns repository development, mathematical validation, evidence,
agent handoffs, and publication. It does not change mathematical scope or reopen
the deferred Op/profile, six-term comparison, or spectral work. Other documentation
edits appeared during the review and were left untouched.

User constraint: the pre-existing emdash book design, architecture and
implementation are the basis for every book-related recommendation. External
textbook projects supply ideas to adapt within those owners.

The governing instructions remain [root AGENTS](../AGENTS.md),
[Lambdapi AGENTS](../emdash2/AGENTS.md), and
[print AGENTS](../emdash2/print/AGENTS.md). This review extends the operational
analysis in the [September reassessment](TYPESCRIPT_EMDASH_FOUNDATIONS_DEVOPS_AND_CONTINUATION_REVIEW.md).
The [earlier MathOps plan](../emdash2/reports/REPORT_EMDASH_MATHOPS_DEVOPS_IMPLEMENTATION_PLAN_2026-06-16.md)
is completed history; its implemented catalog, health, audit, and recovery tools
are the starting point here.

## Assessment

The highest-value work is to consolidate check selection, execution, and evidence
around the existing tools. Emdash has substantial local validation and unusually
explicit research qualifications. Its operational contracts have become spread
across scripts, package commands, registries, plans, and publication workflows.
That creates avoidable uncertainty about what a command checks and what a saved
success actually covers.

There are concrete issues to address before adding more agent orchestration:
ordinary checker paths do not consistently use the resource guard; an imported
LP dependency is absent from the health content snapshot; two focused TypeScript
test files are outside the aggregate runner; and the checked-in GitHub workflows
do not provide general pull-request validation.

The longer-term opportunity is a connected account of each mathematical claim:
its source, formal owner, assumptions, computational profile, checks, review,
and published artifact. Most of the ingredients already exist. Build adapters
and generated views over them before introducing another database or goal system.

## Existing strengths to preserve

| Area | Existing foundation | Consolidation should preserve |
| --- | --- | --- |
| Workspace | Pinned pnpm, shared lock, worktree bootstrap, workspace contract | Four contributor packages; independent mutable dependency graphs per worktree; the standalone template's intentional npm lock exception |
| Mathematical review | Owner-position probes, subject reduction, negative controls, warning-family review | Semantic review in addition to passing checks; no automatic zero-warning rule |
| Resources | Serial resource guard, measured GC profiles, selected deadline/memory extensions | Default 2 GiB/90 seconds and explicit exceptional profiles, applied per invocation |
| Inventories | Check catalog, source TOC, health snapshots, report lifecycle checks | Stable IDs and source ownership; generated reports remain generated |
| Proof product | Explicit Core, exact source replay, theorem dependency checks, semantic diff, repair proposals | Small browser-safe checker and its bounded transferred profile |
| Publications | Book/document manifests, evidence links, render/PDF gates, checked artifact promotion | Local fonts, deterministic metadata, exact artifact identity, renderer ownership |
| Package release | Tag/ancestry preflight, verified tarball, isolated publish job, provenance | Publish the same verified bytes; keep source execution out of the publish job |
| Recovery | Living plans, audit recipes, exact-response archive | Active source and current decisions outrank chronological logs |

These are substantial assets. The strongest existing package workflow is a useful
internal model for the other publication paths:
[npm-publish.yml](../.github/workflows/npm-publish.yml).

## The existing emdash book is the architectural starting point

The [book workspace](../emdash2/book/README.md) already has a theorem-led spiral,
chapter-sized source, conceptual ownership, formal-status distinctions, provenance,
an evidence appendix, deterministic assembly and a qualified publication pipeline.
Its current source manifest identifies edition `0.9.2-dev`. Those capabilities
are existing implementation, not work to be introduced from Lean tooling.

| Existing owner | Responsibility to retain |
| --- | --- |
| [book.json](../emdash2/book/book.json) | Metadata, source order, render input and artifact target |
| [expansion.json](../emdash2/book/expansion.json) | Chapter-group architecture, conceptual owners, central claims, terminology and translation contracts |
| [STYLE.md](../emdash2/book/STYLE.md) and chapter sources | Exposition, formal-status conventions and source-owned prose |
| [evidence.json](../emdash2/book/evidence.json) | Existing claim IDs, statements, formal owners, reviewers and the four formal-status categories |
| [Source provenance](../emdash2/book/references/third-party-sources.json) | External revisions and adaptation attribution |
| [documents.json](../emdash2/print/documents.json) and the [shared pipeline](../emdash2/print/src/pipeline/commonMarkdownPipeline.tsx) | Registered loading, Markdown/KaTeX/Arrowgram rendering, sanitization and pagination |
| [RELEASE.md](../emdash2/book/RELEASE.md) and existing release scripts | Clean-install, browser, PDF, visual-review and promotion requirements |

The proposed addition is operational linkage: associate existing evidence IDs
with exact execution receipts and artifact provenance, and derive useful views
from that linkage. A chapter-to-claim view should read the existing architecture
and evidence manifests. It should not require a second manually maintained
blueprint, chapter taxonomy or status vocabulary. Source-linked runnable examples
are a later authoring enhancement only where they improve the existing book.

No adoption of Verso, MkDocs or Lean Blueprint as the book implementation is
proposed. The current renderer and pedagogical architecture remain the baseline.

## Findings from the current repository

### F1. Resource policy and execution paths disagree

[probe.sh](../emdash2/scripts/probe.sh) invokes the
[resource guard](../emdash2/scripts/lambdapi_resource_guard.sh), which requires its
tools, takes a serial lock, enforces memory/file/core limits, and uses a hard
deadline. Its systemd mode additionally constrains aggregate descendant memory
and swap; the prlimit fallback is explicitly weaker.

The ordinary paths in [check.sh](../emdash2/scripts/check.sh),
[check_examples.sh](../emdash2/scripts/check_examples.sh),
[check_warning_summary.sh](../emdash2/scripts/check_warning_summary.sh), and
`check_metrics.py:run_command` instead use `timeout --signal=INT` without a hard
kill escalation. They also permit direct execution when `timeout` is missing.
They do not themselves apply the guard's memory or serialization policy.

The TypeScript [probe adapter](../src/v3_2/probe.ts) independently spawns Lambdapi
with a millisecond timeout and `SIGINT`. Consolidation must cover this adapter
too, without adding an OS-process dependency to the browser-safe checker.

There is also routing drift: the health runner selects the registered 6 GiB/180s
native-snake pair wrapper for `examples/freyd_native_snake_pair_exactness.lp`,
while `check_examples.sh` sends that reviewer through its ordinary path.

Recommendation: make every repository checker adapter resolve the same named
target profile and use one bounded execution contract. Retain special staged
object builds, applying the guard to each child invocation rather than wrapping
an entire group around another locked guard. Record the effective backend and
limits. A missing guard facility should fail explicitly.

The existing resource/profile test files under `emdash2/scripts/` are useful,
but the explicit unit-test list in [Makefile](../emdash2/Makefile) does not run
`test_lambdapi_resource_guard.py`, `test_native_snake_pair_profile.py`, or
`test_native_snake_gc_profile.py`. Syntax compilation does not execute them.
Include them in the appropriate tooling gate when consolidating dispatch.

### F2. Saved health evidence does not fingerprint every imported source

[check_metrics.py](../emdash2/scripts/check_metrics.py) registers 746 root LP
targets and 546 reviewer files, for 1,292 files. There are 747 root LP files.
The extra file is
[emdash3_2_prof_reindex_terminal_normalization.lp](../emdash2/emdash3_2_prof_reindex_terminal_normalization.lp).
It is a real current owner, named in the architecture report and imported by
the registered
[prof_reindex_terminal_normalization reviewer](../emdash2/examples/prof_reindex_terminal_normalization.lp).
It is also directly listed by `check.sh`.

`check_content_snapshot` hashes the registered file list, not a resolved import
closure. Consequently a change confined to that imported owner does not change
the health content digest. Under otherwise identical identity fields,
`--resume` can accept predecessor success for a reviewer whose dependency has
changed. This is a source-level finding; the review did not modify the owner or
run a stale-cache experiment.

The existing identity already includes useful flags, GC settings and hashes of
the guard and two special wrappers. It still uses a Lambdapi version string and
does not hash all isolated-group scripts, the runner implementation, package
resolution configuration, or a resolved artifact/dependency environment.

Recommendation: fix dependency completeness before making caching more
aggressive. Include the exact transitive source closure, resolution configuration,
relevant runner/tool identity, and any compiled-object provenance. An unresolved
dependency must make evidence non-reusable. Keep only successful checks reusable;
keep failed attempts separately for diagnosis.

### F3. Check membership needs an executable contract

The direct target list in `check.sh` contains 589 entries, while the health list
contains 746. There are 158 health-only entries and the one check-only owner
described above. Different focused and integration suites can legitimately have
different membership; these counts do not establish that 158 modules are
unchecked, since imports also check dependencies. They do establish that command
scope cannot be inferred from a single maintained list.

Several isolated-chain membership sets and dispatch decisions are repeated in
shell and Python. [Book evidence validation](../emdash2/scripts/check_book_evidence.py)
even derives its active-owner allowlist by regex-scanning `check_metrics.py`.
An operational Python implementation has become a cross-language data registry.

The TypeScript aggregate has 446 direct test imports. A transitive import walk
accounts for indirect research-goal and benchmark tests, but still leaves these
two files unreachable from [main_tests.ts](../tests/main_tests.ts):

- [v3_2_pathout_presentation_proposal_tests.ts](../tests/v3_2_pathout_presentation_proposal_tests.ts)
- [v3_2_pathout_presentation_review_tests.ts](../tests/v3_2_pathout_presentation_review_tests.ts)

Their [owning plan](TYPESCRIPT_ELABORATOR_V3_2_PATHOUT_STANDARD_LIBRARY_PLAN.md)
describes them as focused proposal/review tests. Classify and register them, or
record a deliberate separate gate. Do not silently assume all test-shaped files
belong in the same expensive aggregate.

Recommendation: one declarative target/profile registry, with generated command
membership and cross-language readers. Validate reachability, duplicate IDs,
unknown targets, import coverage, and explicit exclusions. Distinguish owners,
reviewers, non-library audits and historical fixtures. Start with operational
metadata; do not duplicate mathematical declarations in the registry.

### F4. Local validation is much stronger than checked-in hosted CI

The only workflows in the root `.github/workflows/` are
[Pages](../.github/workflows/pages.yml) and npm publication. Neither provides a
general `pull_request` gate.

Pages installs the standalone template and runs `npm run build`. That command
is `vite build`; the template's separate `check` also invokes TypeScript. The
workflow does not run root tests, conformance, kernel validation, or publication
evidence checks. The npm workflow has strong artifact handling, but does not run
the root behavior-test suite or lint as part of its release build.

The root `check:all` runs `check:ts`, the selected MVP conformance command, and
`make -C emdash2 ci`. It does not include packed-package checks, browser rendering,
PDF release validation, or every opt-in directed/scale conformance suite. Its
name should not be treated as proof that every shipped boundary was tested.

Recommendation: publish an explicit gate matrix and make hosted CI execute it.
Use a stable required summary job that explains which gates ran, which were
reused, which were out of scope, and which remain missing. Use the same selection
logic locally and in CI. Missing required checks must fail rather than become
green skips.

Private repository rulesets, environment approvals, npm account settings, and
live workflow history were not audited. This finding concerns checked-in
workflows and command definitions, not the absence of all external protection.

### F5. Source freshness, successful checks, and mathematical review need distinct status

The current committed health report is source-current: the read-only snapshot
check passed. Its timing rows have blank exit/duration fields while their
evidence column says `current`. That is what `--no-check` produces. It is a
source inventory, not a fresh successful typechecking receipt. Likewise, the
book evidence checker validates references and ownership; it does not execute
the cited formal claims.

Both are useful checks. Their results should be presented with explicit kinds:
inventory-current, passed-fresh, passed-reused, failed, timeout, resource-limit,
not-run, and out-of-scope. An expected negative audit needs its own expectation
and observed outcome; an arbitrary checker error must not satisfy it.

Mathematical status is a separate axis. The
[current Foundations](../emdash2/reports/EMDASH_FOUNDATIONS.md) and
[README boundaries](../README.md#current-boundaries) document known
variance/soundness defects and restricted interpretations. A successful check
in that research theory is not a consistency certificate. A green dashboard
must retain the theory revision, profile qualifications, supplied model
contracts, and unresolved semantic boundaries.

### F6. Reproducibility and publication can be connected more tightly

Contributor JavaScript dependencies are pinned well. The bootstrap does not
install a pinned Lambdapi/OCaml toolchain. The older MathOps plan explicitly
chose to record a development build without enforcing it, to permit exploration.
That is a reasonable exploratory policy, but a reproducible CI/release lane
needs a precise toolchain recipe and machine-readable identity.

Use a pinned verification environment and allow separately labelled exploratory
environments. A doctor command should report required versions and tools,
including resource-guard capabilities, Python, Chromium, qpdf and Poppler where
relevant. A container is one possible packaging choice, not a prerequisite for
the first consolidation tranche.

The book promotion script already verifies copied bytes and PDF checks validate
metadata/content. Extend this with a durable manifest binding source closure,
book/document manifest, renderer/browser versions, validation receipt, PDF,
Markdown and deployed bundle digests. A successful copy or Pages build is not
itself that source-to-publication linkage.

The npm workflow's exact verified artifact is the pattern to reuse. Pages can
adopt its job-scoped permissions, pinned action identities, explicit job budgets,
and validation-to-deploy dependency. Test the package's advertised Node consumer
floor separately from the newer contributor pnpm requirement. Publication remains
a distinct authorized action after validation.

### F7. Navigation and test cost are measured maintenance work

The initial review snapshot had a 3,005-line elaborator handoff, 740-line nested
AGENTS file and 1,344-line report index. The September reassessment already
recommends separating current routing from chronology. Follow that recommendation:
short contributor entry points, one current status owner, explicit active/deferred/
completed routes, and linked historical receipts.

The [test-performance plan](TYPESCRIPT_TEST_PARALLELISM_PLAN.md) contains useful
July measurements: a fair two-worker comparison was slower than a shared-process
control; duplicate immutable compilation and eager fixtures dominated several
costs. Those are historical measurements, not a fresh timing of today's larger
suite. Reconfirm the expensive paths before implementation.

Prioritize successful immutable-result caching, lazy fixtures, then compiled-JS
or qualified lighter runtime execution. Only then consider small dependency-aware
shards. Preserve serial Lambdapi execution and aggregate import-interaction
checks. A large number of CPU cores does not justify many duplicate checker heaps.

## What to adapt from the comparison projects

Sources were inspected on 2026-09-23. These are design references, not dependencies
installed or services used for submissions. The user confirmed Verso, Lean
Blueprint and Mathematics in Lean as representative textbook examples.

| Project and observed practice | Useful adaptation to emdash |
| --- | --- |
| [Prove2Me](https://prove2.me/about) separates immutable targets from proofs and decomposes missions through dependency-linked sketches. Its [public description](https://prove2.me/) identifies Formalpedia as the reusable results library. | Stable claim identities, exact target matching, alternative proof decompositions, and a searchable verified-result view. Reuse the existing theorem DAG and replay mechanisms. Audit definitions and permitted rule environments as well as the headline claim. |
| [Palomar](https://palomar-registry.org/about) records pinned repository snapshots, statement/proof comparison, independent checking, and separately described informal correspondence review. | Release receipts tying a precise claim to exact source, checker and dependency identities. Keep proof checking and mathematical correspondence review visibly separate. Lean Comparator and its independent kernels are not drop-in validators for Lambdapi or emdash Core. |
| [Lean Pool](https://github.com/Vilin97/lean-pool/blob/main/CONTRIBUTING.md) uses project/challenge registries, fixed challenge statements, deterministic gates, provenance and per-project builds. | Explicit manifests, protected target contracts, focused local gates and integration checks. Adapt the admission rules to our primitives and rewrite theory; a literal Lean axiom whitelist or zero-warning policy would be inappropriate. |
| [TheoremDB](https://www.theoremdb.org/how-it-works/) relates statements, attempts, evidence and revisions, distinguishing exact from advisory structural matches. Its [agent documentation](https://www.theoremdb.org/docs/) asks for durable source identity and useful failures with retry conditions. | Index compact experiment outcomes and replay triggers from existing audits. Keep structural retrieval advisory and replay candidates in the exact current environment. Retain timeout/allocation results as resource observations. |
| Current [AutoformBot main](https://github.com/facebookresearch/autoform-bot) uses Markdown roadmaps, validated dependency links, generated views, doctor/audit commands and review preparation. Autonomous orchestration is a separate `execution` branch. | A small validated roadmap/target vocabulary and generated views fit the repository well. Keep coordination optional. Its lexical declaration lookup is explicitly distinct from compilation; preserve that distinction in our own evidence UI. |
| [ATLAS v1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/README.md) associates textbook targets with evaluation reports and browsable formalizations. The [current root](https://github.com/facebookresearch/atlas-lean/blob/main/README.md) preserves v1 while preparing v2. | Show book claim, formal owner, computational checks and review qualifications together. Measure covered claims and reusable interfaces, not just declaration or line counts. Keep automated faithfulness scores advisory. |
| [Verso](https://verso.lean-lang.org/) integrates checked examples with documentation. [Lean Blueprint](https://github.com/PatrickMassot/leanblueprint) connects exposition, declaration names and dependencies. [Mathematics in Lean](https://github.com/leanprover-community/mathematics_in_lean) pairs sections with runnable examples and exercises. | Link execution receipts to emdash's existing evidence IDs. Derive optional views from its existing chapter architecture and evidence registry. Consider source-owned runnable examples where useful; preserve the established book implementation. |

The research-kernel distinction is decisive. These Lean workflows generally
formalize statements within a pinned logical environment. Emdash also evolves
declarations, runtime rewrites, proof-time agreements and their interpretations.
A proof task should hold its theory/profile contract fixed. Changing that
contract is a different review task and must not count as solving the original
proof obligation. This also applies to supplied proof–CAS model contracts.

## Proposed operating model

Use a thin repository tooling layer over the existing owners:

```mermaid
flowchart TD
    A[Source owners and existing manifests] --> B[Target and dependency registry]
    B --> C[Bounded runners]
    C --> D[Immutable validation receipts]
    A --> E[Claim and assumption records]
    D --> F[Local status and CI summary]
    E --> F
    D --> G[Qualified artifact manifests]
    G --> H[Authorized publication]
```

The target registry owns operational facts: target ID, source/input resolution,
dependencies, execution adapter, profile and applicable gates. Mathematical
signatures remain in source. Book order remains in `book.json`, pedagogical and
conceptual structure in `expansion.json`, and claim identity in `evidence.json`.
Document allowlisting remains in `documents.json`. Existing manifests should
reference stable IDs rather than copy each other's data.

A receipt should capture:

- Target ID, schema version, actual command, working directory and run identity.
- Exact source/dependency contents, including dirty/untracked inputs when used;
  commit SHA alone is insufficient for a local experiment.
- Checker/tool/runtime and runner identities, effective flags, GC, timeout,
  memory/file limits and guard backend.
- Fresh or reused execution, exit classification, wall time, observed peak RSS
  when available, warning inventory and raw-log/artifact digests.
- For reuse, the predecessor receipt and exact invalidation rationale.

Never fabricate a per-target measurement by presenting an apportioned group time
as measured wall time. The current health runner already labels isolated-group
time shares; retain that distinction in the schema. Do not equate heap allocation,
heap size, process RSS and aggregate descendant memory.

Extend or project the existing claim records to link the informal assertion,
exact formal target, semantic owner, prerequisites, profile/assumptions, positive
and relevant negative consumers, and review evidence. Record whether the owner
is a derived definition, declared structural operation, runtime computation or
proof-time comparison. Validation, semantic qualification and publication are
separate fields.

Build on [research_goal_graph.ts](../src/v3_2/research_goal_graph.ts),
[lf_development_diff.ts](../src/v3_2/lf_development_diff.ts),
[lf_proof_maintenance.ts](../src/v3_2/lf_proof_maintenance.ts),
[the benchmark evaluator](../src/v3_2/lf_proof_agent_benchmark.ts), and the current
workspace/source contracts. They already distinguish advisory proposals and
fresh proof replay. The research graph explicitly does not authenticate people,
compute cryptographic hashes, or perform I/O. Put receipt acquisition and identity
verification in an outer adapter; do not quietly grant those guarantees to the
pure graph or force build jobs into theorem nodes.

Illustrative future developer commands could be `scripts/emdash dev doctor`,
`dev targets`, `dev check --explain`, and `dev status`. These commands do not yet
exist. Keep existing Make/pnpm entry points as adapters during migration, and
keep basic diagnostics inexpensive to load.

## Gate selection and evidence reuse

| Change boundary | Required intent |
| --- | --- |
| Documentation/plan only | Exact diff, local links and the owning document checks; no unrelated semantic aggregate |
| TypeScript behavior | Focused tests plus typecheck/lint; one full `check:ts` at the required shared-behavior tranche boundary |
| Workspace/package setup | Existing workspace/typecheck/test requirements and affected print checks; packed consumer tests for distribution changes |
| Lambdapi semantics | Owner-position controls, bounded focused checks, warning comparison, affected reviewers, catalog/health synchronization, and full CI where the SOP requires it |
| Renderer/book | Existing owning source, typography, browser and artifact gates according to the print SOP |
| Cross-layer integration/release | Explicit union of affected product, formal, package and publication gates; exact artifact/source receipt |

The matrix should become executable without weakening the existing policy.
Begin with coarse conservative groups. Source imports alone may underdescribe
rewrite interactions: changes to shared rule environments, checker semantics,
registry logic or toolchain identity should widen invalidation. Preserve joint
import tests at integration boundaries. Keep the TypeScript transferred-profile
conformance inventory explicit; a selected MVP differential run does not qualify
every Lambdapi module.

Scheduled checks can test toolchain upgrades and catch broader drift. They do
not replace required pre-integration semantic gates. Expensive successful
evidence may be reused only with a validated closure and matching environment,
not merely because the previous commit was green.

## Proposed implementation sequence

No row below is implementation authorization or a new persistent goal.

| Stage | Bounded deliverable | Acceptance evidence |
| --- | --- | --- |
| 0. Close inventory gaps | Resolve the missing health dependency; classify the two TS suites and unwired resource tests; document command scopes | All current owners/reviewers/tests are reachable or explicitly classified; changing any dependency invalidates affected reuse; no mathematical edits |
| 1. Consolidate one execution slice | Named profiles and receipt schema for an ordinary check, an imported reviewer, and an existing exceptional native target | Existing commands select the same effective policy; hard deadline/limit/failure tests pass; each actual invocation is bounded; raw diagnostics and subject reduction retained |
| 2. Add reproducible CI | Pinned verification recipe, doctor output, shared gate selector, PR summary and artifact retention | A clean CI checkout reproduces selected gates; missing required checks fail; changed shared owners widen scope; release/deploy consumes matching validated artifacts |
| 3. Consolidate navigation and claims | Short handoff, current status owner, linked history; one claim-to-source-to-receipt view from book evidence | Each displayed status has an identifiable source; no manual second status database; theory limitations and supplied contracts remain visible |
| 4. Reduce measured iteration cost | Reconfirm hotspots; cache immutable compilation, defer fixtures, qualify test runtime; split diagnostic groups where justified | Equivalent test/check inventory, preserved negative controls and joint imports, recorded time/memory improvement; shard only if measurements justify it |
| 5. Add optional coordination | Compact task packets, experiment retrieval, work claims and integration queue if concurrent work warrants them | Each packet fixes target/theory/scope and budgets; stale claims expire; submissions replay at integration; agents cannot self-certify semantic promotion |

For Stage 1, use the existing resource limits and narrowly selected consumers.
Migrate one wrapper at a time, retaining equivalent bounded legacy adapters
while the shared route is qualified. Select proportional validation in its
implementation plan; do not run the 1,292-file gate after every
metadata edit. Shared TypeScript changes still receive their required final
aggregate, and substantial semantic changes still receive the nested SOP gates.

Diagnostic splitting is separate from a nucleus reorganization. The existing
catalog's mathematical areas can supply stable groups, but every assertion must
survive exactly once and an aggregate interaction target must remain. Moving
Lambdapi declarations changes qualified identities, linkage and rewrite
environments; defer that migration to its mathematical/dependency plan.

An initial coordination packet can remain a small tracked record: exact base and
target, source owner, allowed files, active decision links, expected positive and
negative checks, named resource profile, outcome, and retry trigger. Reuse the
existing plan/archive hierarchy. TheoremDB-style failure retrieval should prevent
repeating unchanged dead ends, while allowing reconsideration when a recorded
prerequisite changes. Persistent process state is not proof authority.

The useful metrics are selection accuracy, required-test coverage, receipt
completeness, time to a focused verdict, gate wall time and memory, explicit reuse
rate, repeated-failure cost, and publication/source mismatches. Baseline them
before setting targets. Raw theorem counts and automated review scores should
not serve as the primary progress measure for an evolving foundation.

## Review evidence and limits

Executed during this review:

- `node scripts/check-workspace.mjs`: passed; pnpm 11.16.0, Node 24.11.1.
- `python3 emdash2/scripts/check_metrics.py --no-check --check-report --brief`:
  passed for 1,292 registered files; Lambdapi checks explicitly skipped.
- `python3 emdash2/scripts/generate_check_catalog.py --check --strict`: current.
- `python3 emdash2/scripts/lint_report_headers.py`: passed.
- `python3 emdash2/scripts/check_book_evidence.py`: passed, 187 claims and 187
  cited evidence IDs; reference validation only.
- From `emdash2`, `python3 -m unittest tests.test_check_metrics`: 26 tests passed.
  Printed timeout examples came from mocked failure cases, not real checker runs.
- Static target-list comparison, transitive TypeScript test-import inspection,
  workflow/command tracing, and the primary-source comparisons linked above.

No full TypeScript/kernel aggregate, new performance benchmark, browser render,
PDF build, independent mathematical audit, or hosted-service implementation
audit was performed. No external proof submission, package installation, Git
checkpoint, branch/worktree change, push, deployment or publication was made.
The new review file passed scoped diff/whitespace inspection and validation of
38 local links, referenced heading anchors and balanced code fences.
