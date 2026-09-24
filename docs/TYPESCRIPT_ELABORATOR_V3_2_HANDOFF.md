# TypeScript Elaborator For Emdash v3.2 — Start Here

Reviewed: 2026-09-24. This is current orientation; detailed qualification lives
with the source contracts and plans linked below. The former running narrative
is preserved in [handoff history](history/TYPESCRIPT_ELABORATOR_HANDOFF_THROUGH_2026-09-23.md).

## Current Work And Qualification

The [repository consolidation ledger](EMDASH_REPOSITORY_CONSOLIDATION_PLAN.md)
records the completed bounded maintenance. The [DevOps guide](DEVOPS.md) owns commands
and gate selection. The [repair ledger](TYPESCRIPT_PROFILE_AND_PERFORMANCE_REPAIR_PLAN.md)
owns the latest source requalification and matcher/reference-cache results.
The corrected complete TypeScript gate and bounded conformance gate now pass;
their exact receipts and main integration are recorded in the consolidation
ledger. Earlier aggregate counts remain dated receipts; full formal CI and
hosted qualification are separate boundaries.

For mathematical status use the
[current architecture report](../emdash2/reports/REPORT_EMDASH_V3_2_CURRENT_STATUS_AND_SOP_2026-05-26.md)
and [Foundations](../emdash2/reports/EMDASH_FOUNDATIONS.md). The native whole
homology/universality interfaces and proof–CAS examples have explicit ordinary,
model, normality and interpretation contracts. The current unrestricted
Op/Sigma/Homd package has recorded defects. The completed action-profile branch
awaits separate integration and does not silently change main or the TypeScript
transfer. Preserve the six-term, profile/variance and spectral deferrals.

The [September reassessment](TYPESCRIPT_EMDASH_FOUNDATIONS_DEVOPS_AND_CONTINUATION_REVIEW.md)
records those boundaries, the qualified binder direction and sibling-template
roles. The [newer consolidation review](EMDASH_DEVOPS_CONSOLIDATION_REVIEW_2026-09-23.md#broader-repository-and-ecosystem-reassessment)
adds context/research ownership and the future design reference.

## Trust And Compilation Boundary

```text
TypeScript construction/authoring (optional text adapters)
    -> scope, constraints, binder roles and implicit recovery
    -> explicit backend-neutral emdash Core
        -> small TypeScript checker/evaluator for its qualified profile
        -> deterministic Lambdapi emission/conformance where required
```

Arbitrary TypeScript, AI proposals, cached artifacts and diagrams are not proof
authority. Successful proof development ends in fresh Core checking against the
selected declarations and rules. Runtime rewrites select computational normal
forms; proof-time comparison rules do not automatically become evaluation.
Lambdapi is the active mathematical specification and required conformance/
subject-reduction oracle at recorded profile-change boundaries; it is not a
per-term production dependency of the graduated TypeScript profiles.

Qualification is profile-specific. The [MVP manifest](../src/v3_2/manifest.ts),
[release policy](../src/v3_2/release.ts) and
[directed graduation](../src/v3_2/directed_graduation.ts) record exact trust
boundaries. RELEASE-READY is complete for the exact deployed
`emdash-v3.2-mvp-1` profile: 16 owners and three runtime rules. That historical
release does not certify today's complete contributor suite. Lambdapi retains
acceptance authority for five selected semantic-boundary changes: selected
owner signatures, runtime-rule shape/authority, profile promotion of an owner
or rule, termination/confluence/subject-reduction claims, and shared-corpus
backend bindings. General confluence remains withheld, as does standalone
TypeScript subject reduction.

Newer transferred/authoring profiles carry their own contracts and
consumers; no historical graduation qualifies every later Lambdapi owner.
General metatheory and closed CAS/provider semantics are not inferred from
passing concrete examples. Preserve source-pin failures as review signals.

The retired category-specific feasibility API stays retired. `src/v3_2/`
contains the generic LF/Core checker, compiler, authoring and bounded profiles.
The [root barrel](../src/v3_2/index.ts), browser boundary and the package's
selected barrels have different scopes; root-only APIs do not become public
by appearing in a demonstration. The [package manifest](../packages/emdash/package.json)
and [package guide](../packages/emdash/README.md) own the public exports.

## Choose The Relevant Owner

Read [root guidance](../AGENTS.md), then the source and task-specific portions
of the [formal SOP](../emdash2/AGENTS.md) and its authority order. Consult
[canonical syntax](../emdash2/reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md)
for mathematical notation/text-profile questions. Do not read every completed
ledger as an onboarding prerequisite.

| Task | Current route and scope |
| --- | --- |
| Checker/compiler or a new transfer | Generic LF/Core source and nearest tests; [scale plan](TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md) records retained architecture and deferred bulk work; [source requalification](TYPESCRIPT_PROFILE_SOURCE_REQUALIFICATION_2026-09-23.md) records current reviewed pins |
| Categorical/dependent binders | [Mixed-introduction continuation](TYPESCRIPT_ELABORATOR_V3_2_MIXED_INTRODUCTION_PUBLIC_CONTINUATION_PLAN.md) and [compositional binder plan](TYPESCRIPT_ELABORATOR_V3_2_COMPOSITIONAL_NATURAL_BINDER_PLAN.md); their qualified bodies and structural prerequisites, not unrestricted binder synthesis |
| Proof development, classes, automation or maintenance | [Proof-assistant plan](TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md) and source-visible [capabilities](../src/v3_2/ai_native_capabilities.ts); exact source, named goals and fresh checking remain the essential workflow |
| Workspace/source transport and publication adapters | [AI-native workspace plan](TYPESCRIPT_EMDASH_AI_NATIVE_WORKSPACE_AND_PROOF_PLAN.md); source identity, supplied files, cache validation and hosted transport have separate contracts |
| Native CAS/homology or universal operations | [Native final audit](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md), [universality final audit](TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_FINAL_AUDIT.md), then their source owners and selected model contracts |
| Book/reviewer | Existing [book architecture](../emdash2/book/README.md), evidence and source manifests; [print guidance](../emdash2/print/AGENTS.md) applies to renderer work |
| Historical design, failed experiment or reproducible receipt | [Handoff history](history/TYPESCRIPT_ELABORATOR_HANDOFF_THROUGH_2026-09-23.md), exact task ledger and [report index](../emdash2/reports/INDEX.md); reopen only when its recorded prerequisite or task scope changes |
| Literature or checker implementation research | [Local resource index](../emdash2/research/LOCAL_RESOURCES.md) and existing reading reviews; availability is separate from reading/build/transfer evidence |

The public benchmark is a developer fixture. Its separate agent canary is
parked; a new proof-assistant consumer does not restart that experiment or
require a general goal-graph platform. See the
[terminal decision](TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md#terminal-v4-result-and-benchmark-stream-refocus).

## Work And Validation

Inspect staged/unstaged state and locate definitions/consumers with `rg` before
editing. Follow [persistent-goal Git rules](PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)
for an authorized long-running task. Bootstrap each new worktree with
`./scripts/bootstrap-worktree.sh`; never share mutable `node_modules` trees.

```bash
./scripts/emdash dev doctor
./scripts/emdash dev check --explain
rg -n 'OWNER' src/v3_2 tests -g '*.ts'
rg -n 'OWNER' emdash2/emdash3_2*.lp emdash2/examples
```

Replace `OWNER` with the actual symbol or family. Search chapter sources for
book prose. The narrow root `.rgignore` excludes extracted histories and the
assembled book copy from ordinary searches; retrieve them deliberately with:

```bash
rg --no-ignore -n 'DECISION_OR_SYMBOL' docs/history emdash2/reports/history
```

Explicit positive `-g` globs can override ignore rules; use scoped directories
or a Markdown type filter when the history should stay excluded.

Documentation changes receive document checks. Behavior changes receive the
nearest focused tests plus applicable typecheck/lint and their owning gates.
This handoff also has executable consumers in `v3_2_release_policy_tests.ts`
and `v3_2_release_completion_tests.ts` under `tests/`; run those focused suites
when changing its trust/release statements.
Shared-behavior integration needs its recorded aggregate qualification;
explicit user waivers must remain visible. Do not equate focused success
with a full run. Formal changes require owner-position/negative consumers,
warning review and the nested bounded-check SOP. The gate matrix in DEVOPS is
the operational reference, and receipts do not promote mathematical status.
