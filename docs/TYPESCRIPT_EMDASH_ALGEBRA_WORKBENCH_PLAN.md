# Emdash Algebra Workbench: Shared Polynomial Workflow

Date: 2026-09-24
Plan-ID: `TS-EMDASH-ALGEBRA-WORKBENCH`
Status: active; scope checkpoint prepared, owner audit in progress
Baseline: `df061c52338f4c28565133b2f9dae70de4d5ce39`
Branch: `goal/algebra-workbench-polynomial-v3.2`
Worktree: `/home/user1/emdash1-algebra-workbench-v1`

## Objective and authority

Implement the first bounded consumer accepted from the
[OSCAR/workbench review](EMDASH_OSCAR_AND_ALGEBRA_WORKBENCH_REVIEW_2026-09-24.md):
one source-owned polynomial/ideal workspace, one external computational backend,
one useful derived view, and one explicit formal goal. Reuse the existing
[focused CAS](TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md) and
[proof–CAS delegation](TYPESCRIPT_EMDASH_PROOF_CAS_DELEGATION_PLAN.md) owners.
This plan owns execution, decisions, validation and recovery for that consumer;
the review owns its rationale. Those completed architecture plans retain their
original scope and dated receipts.

Follow [root guidance](../AGENTS.md), the
[current handoff](TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md), the
[formal SOP](../emdash2/AGENTS.md), and the
[persistent-goal Git workflow](PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
Active source outranks plans and archived responses. Formal interpretation is
limited to the selected existing ring owners and their recorded qualifications.

The user's 2026-09-24 continuation accepts the consolidated recommendations,
authorizes a dedicated local branch/worktree, implementation, validated local
checkpoint commits and a persistent goal delegated to this living plan.
The two accepted review changes were copied exactly from main; their original
working copies remain untouched. No push, main integration, publication,
history rewriting, branch deletion or worktree removal is authorized here.

Recovery evidence:

- Prior design response:
  `emdash2/tmp/ai-responses/sessions/2026-09-23_01a0cf02983d/responses/0008_2026-09-24T17-43-31Z_01a0d476-8cf0-7ce1-9132-e6a47f3e2a07.md`
  in the original main worktree.
- Accepted consolidation response:
  `emdash2/tmp/ai-responses/sessions/2026-09-24_01a0d560b19a/responses/0001_2026-09-24T21-52-38Z_01a0d566-55a7-7d80-a9ef-27c2befd6fae.md`
  in the original main worktree. The archive is evidence, not authority.

## Selected consumer and trust boundary

Use R = Q[x,y], f1 = y - x², f2 = xy - 1, I = (f1,f2), and g = x³ - 1.
The computational identity is g = (-x)f1 + f2. A small TypeScript entry point
should construct these objects once and reuse them for native computation,
external computation, independent witness arithmetic, a real-locus view and
the selected formal claim. Ordinary function calls remain the entry point.

```text
parent-aware TypeScript polynomial objects
  -> existing native ideal operations
  -> bounded external backend exchange -> coefficients -> arithmetic check
  -> explicit rational-to-real sampling -> derived plot
  -> selected formal realization -> named goal -> fresh Core checking
```

The initial external backend is Singular, already installed on this host.
Julia is absent. This selects one supported OSCAR-ecosystem computation without
requiring a new installation or claiming general OSCAR interoperability.
Inspect and reuse the existing Singular transport, canonical encodings and
operation contracts before extending them. Backend handles never become
mathematical identity or proof evidence.

Retain coefficient domain, ordered variables, monomial order, ordered ideal
generators, exact query, backend identity and source binding. Reject wrong
parents, malformed output, changed inputs and altered witnesses. The witness
checks positive membership only; it does not certify negative answers, complete
Gröbner bases or the topology of a numerical plot.

Runtime TypeScript checks and exact arithmetic do not by themselves produce a
Core proof. Audit the existing goal/realization/adoption route. Prefer checked
reconstruction when existing owners support the actual consumer. If they do
not, show the named goal as open and record the precise missing reconstruction
or interpretation contract. Do not add assumptions automatically, relabel
trusted adoption, or expand the kernel to make the demonstration pass.

Whole functors, adjunctions and universal maps retain their existing owners;
this ordinary polynomial slice does not alter them. Proof goals, computation
graphs and research tasks retain distinct evidence policies. No scheduler,
notebook platform, plugin bus, universal serialization schema or goal ontology
is selected. Native module/homology reuse is a later consumer, not this goal.
Profile/variance repair, action-profile integration, six-term comparison,
spectral work, benchmark canary and sibling integrations remain deferred.

## Bounded implementation and acceptance

| Row | State | Deliverable and acceptance |
| --- | --- | --- |
| 0. Preserve scope and baseline | Complete | Dedicated worktree, bootstrapped links, accepted reviews and routed living plan; document checks and exact staged review; local checkpoint |
| 1. Audit and select existing seams | In progress | Current source/consumers, formal owners and baseline gates; record backend exchange, facade/view owner and exact formal target/reconstruction boundary |
| 2. External positive membership | Pending | Bounded Singular operation retaining original-generator coefficients; native comparison and independent exact identity checking; round-trip, wrong-parent, malformed/altered-result and cancellation/error controls |
| 3. Shared-object workbench | Pending | Small reusable TypeScript facade and runnable example with a derived curve view and explicit named formal goal; source changes invalidate previous results; no second handwritten plotting formula |
| 4. Qualification and handoff | Pending | Focused tests, typecheck/lint, actual backend/example run, visual inspection, required full TypeScript gate, synchronized decisions/docs, reviewed local implementation checkpoint and clean goal worktree |

Keep one row in progress. Rows 2–3 form one bounded shared-behavior tranche;
checkpoint their implementation after row 4's full TypeScript gate. Independent
document/decision checkpoints may precede it. Stop when this consumer answers
whether the existing contracts support useful shared-object work. Record a
concrete deferred formal obligation if reconstruction is unsupported; this
does not justify broadening the mathematical theory or hiding the open goal.

## Validation

Use [DEVOPS](DEVOPS.md) and existing gates. Documentation receives exact diff,
local-link, heading/fence and whitespace checks. Bootstrap uses the pinned pnpm
and shared lockfile; do not modify package setup without a concrete need.

Before behavioral edits run workspace verification, root typecheck and nearest
CAS/oracle/delegation tests. Read the relevant active kernel, architecture,
Foundations, canonical syntax and task ledgers. If the selected formal route
depends on current kernel names/computation, run the required bounded
`EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 check` baseline. Further formal
checks stay focused unless actual mathematical source changes require more.

Run meaningful positive and negative controls for each new behavior, wire new
test suites into `tests/main_tests.ts`, and run typecheck/lint. Exercise the
installed external backend under an explicit short timeout and output bound.
Inspect the generated view; numerical sampling is explicitly approximate.
After the tranche is focused-green, run one complete
`./scripts/pnpmw run check:ts` (the equivalent receipt-producing TypeScript
gate may wrap it). Do not substitute focused tests for this shared-behavior gate.
No unrelated full formal, print, package-release or hosted aggregate is selected.

Carry forward the baseline's recorded complete TypeScript and bounded
conformance successes as historical evidence only. This new implementation
needs its own affected-boundary checks. Preserve source-pin failures as review
signals, and record exact timeouts/failures without promoting mathematical status.

## Decisions and receipts

- Start: no persistent goal was active. All 64 registered worktrees were
  inspected; only main's two accepted review changes were dirty. Main and the
  completed consolidation branch both point to `df061c52`. The new goal
  worktree starts at that exact baseline, preserving main's staged/unstaged state.
- Recovery: Infinity Codex verifies 1,264 archived responses. No hook changes
  are needed; the user supplied this session's saved response.
- Backend: `/usr/bin/Singular` is available; Julia is not installed. Selection
  is limited to a positive ideal-membership workflow and does not promise
  parity with OSCAR's breadth, performance or formal assurance.
- Row 0: bootstrap passed with Node 24.11.1 and pnpm 11.16.0; all 373 packages
  reused the shared store, with this worktree's own dependency links. Document
  hygiene passes 75 local links; whitespace and fence review pass. The accepted
  continuation is linked from both existing CAS/delegation plans. The persistent
  goal is active with the prompt below; no token budget was requested.

## Persistent goal prompt

Complete the bounded shared-polynomial algebra-workbench consumer governed by
`docs/TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md` in
`/home/user1/emdash1-algebra-workbench-v1`, on
`goal/algebra-workbench-polynomial-v3.2`. Let that living plan own ordering,
scope, decisions, validation, stopping conditions and recovery. Follow current
repository/formal authorities, preserve unrelated work and make validated
local checkpoint commits. Complete the selected rows and final handoff; resolve
an unsupported formal reconstruction with concrete evidence under the plan's
stopping rule while still completing the computational workflow and its checks.
No push, main merge, publication,
history rewriting, worktree cleanup or deferred mathematical migration is
included.
