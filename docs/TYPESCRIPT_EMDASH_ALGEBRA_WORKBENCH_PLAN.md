# Emdash Algebra Workbench: Shared Polynomial Workflow

Date: 2026-09-24
Plan-ID: `TS-EMDASH-ALGEBRA-WORKBENCH`
Status: active; focused implementation qualified, full TypeScript gate running
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
| 1. Audit and select existing seams | Complete; broader baseline limit recorded below | Current source/consumers, formal owners and baseline gates; selected backend exchange, facade/view owner and exact formal target/reconstruction boundary |
| 2. External positive membership | Implemented; focused-green, awaiting shared checkpoint | Bounded Singular adapter retains original-generator coefficients; native comparison and independent exact identity checking; round-trip, wrong-parent, malformed/altered-result and cancellation/error controls |
| 3. Shared-object workbench | Implemented; focused-green, awaiting shared checkpoint | Small reusable TypeScript facade and runnable example with a derived curve view and explicit named formal goal; source changes invalidate previous results; no second handwritten plotting formula |
| 4. Qualification and handoff | In progress | Focused tests, typecheck/lint, actual backend/example run and visual inspection pass; required full TypeScript gate running before synchronized final checkpoint |

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
- Scope checkpoint: `aa28caf0` preserves this plan and both accepted reviews,
  with continuation routes in the existing CAS/delegation plans. Main's original
  two working changes remain intact.
- Baseline: root typecheck and the three existing ideal/oracle/ideal-delegation
  suites pass (20 tests, 8.17 seconds). The oracle baseline uses injected
  transport; the new live Singular controls are recorded separately below.
- Owner decision: reuse the native ideal operations and original-generator
  transformations, existing parent/polynomial encodings, Node oracle transport,
  goal/delegation/adoption owners, and opaque formal ring signature mirrors.
  The external adapter is an ordinary function returning a positive witness
  or a negative observation. A new general engine, graph or serialization
  framework is unnecessary for this consumer. The existing membership result
  additionally carries a native basis and reduction trace; do not fabricate
  those fields for an external coefficient witness.
- Protocol decision: Singular variables are renamed by position (`v1`, `v2`,
  ...), preserving the original parent outside the process. Parse explicit
  coefficient/exponent rows, require complete unique framing, then multiply and
  add against the original generators. The
  [upstream Singular reference](https://github.com/Singular/Singular/blob/spielwiese/doc/reference.doc)
  documents `lift`'s transformation matrix and the unit factor being identity
  for polynomial rings; only global `lp`/`Dp`/`dp` orders are selected here.
  Independent arithmetic checking remains decisive for a positive witness.
- Bounds: rational coefficients, 1–16 variables, at most 64 generators,
  10,000 input/output terms, exponent ceiling 4096, 30-second external deadline
  and 1,000,000 output bytes. The reused transport is shell-free and uses
  `--no-rc`. Cancellation is checked before dispatch and after return; an
  in-flight process remains bounded by the existing timeout, not a new live
  cancellation protocol.
- Formal decision: retain the actual claim `x³ = 1`, with the two reified
  generator-zero equations as explicit supplied premises in the declaration
  environment. Fresh Core checking retains the named open root goal. Native
  delegation produces a claim and typechecked coefficient data, not a proof
  plan. The current mirror has operation signatures but no ring-law proof
  constructors or normalization reconstruction. The underlying LP ring laws
  do exist; transferring and using them for proof reconstruction is a distinct
  future consumer, not a missing-kernel claim. No trusted computation is adopted.
  This formal helper uses integer coefficients of magnitude at most 4096;
  rational-field interpretation and denominator cancellation remain unsupported.
  An additional bounded control uses `I=(2x)` and target `x=0`: native rational
  membership returns coefficient `1/2`, and formal interpretation rejects it
  with `INVALID_INTERPRETATION` retaining the underlying missing rational-field
  interpretation diagnostic. It does not infer cancellation in an arbitrary ring.
- View decision: direct rational-to-floating-point evaluation of the same sparse
  terms, uniform-grid edge interpolation and SVG rendering. Ambiguous cells
  are omitted and counted. Repeated-factor/tangency controls show why this is
  an approximate view, with no certified component count or topology.
- Focused qualification: all 15 new tests pass with both live opt-ins enabled
  in 11.05 seconds. Actual Singular 4330 checks all three orders, rational
  coefficients, empty/zero generators and negative observations. Negative
  controls reject changed queries/generator order/parents, altered witnesses,
  malformed/truncated replies and changes during execution. Actual child
  processes verify the inherited timeout/output bounds. Typecheck, changed-owner
  lint and registration pass; 455 test suites are reachable.
- Formal consumer qualification: the exact emitted goal and coefficient types
  pass the guarded Lambdapi probe, and using the first premise as the goal's
  proof fails with a typing diagnostic. The current TypeScript probe adapter
  caps callers at 60 seconds, so these two serial probes use that smaller
  deadline with the normal 2 GiB guard. This is formation/data conformance,
  not a completed theorem.
- Broader baseline limit: the required `EMDASH_TYPECHECK_TIMEOUT=90s make -C
  emdash2 check` stops on unchanged
  `emdash3_2_commutative_algebra_affine_glue.lp` with allocation failure during
  minor GC (exit 134). Receipt
  `20260924T220828Z-2316ce2e5bb04b5885befe366551d939` measures 36.60 seconds and
  maximum child RSS 1,818,656 KiB. The SOP control with
  `OCAMLRUNPARAM=o=20,v=1024` and warnings also exits 134 at 28.64 seconds,
  1,818,944 KiB (receipt `20260924T221334Z-c7361ddc850c4c7383fc0a87d604ccb7`).
  Both use the same input snapshot `0fb8f933…`, 2 GiB/90s/systemd profile.
  No source, checker, theory or ceiling changed. The broader baseline is
  incomplete; this unaffected gluing owner is outside the selected consumer.
  Its resource diagnosis remains separate from the passing focused ring probe.
- Proportional gate decision: `dev check --explain` conservatively selects
  package/reviewer and broad conformance gates for any root source addition.
  An import-closure inspection of all four packed-package entries and all five
  template source entries reaches none of the new owners or the changed root
  barrel. Their exports, code and setup are unchanged. Apply the root
  proportional-validation policy: full TypeScript plus this consumer's focused
  conformance and rendered-view checks; no package/reviewer, scale, full formal,
  print/book or release aggregate is selected for an unaffected boundary.
- Full TypeScript gate started at 2026-09-24 22:22 UTC, with implementation
  staged and source/test inputs fixed. Its log is
  `emdash2/logs/devops/typescript-20260924T222204Z-e42853789d7a4e94b5fb01368849e54f.log`.
  Workspace, registration, typecheck and lint have passed; the complete test
  phase is still running at this documentation checkpoint. Do not treat that
  partial run as a pass or start a duplicate aggregate on continuation.
- Artifact review repaired an extra newline in the example's source-file
  writer. A fresh real-backend example run verifies that the saved canonical
  source and formal-profile bytes match every recorded SHA-256 fingerprint.
  This outer example is outside the TypeScript gate's input set; its own typed
  execution and byte comparisons qualify the writer correction. No shared
  source or test input changed while the aggregate was running.

## Run and inspect the consumer

From this worktree's Git root, with the bootstrapped dependencies and Singular
on PATH:

```bash
node --require ts-node/register examples/v3_2_algebra_workbench.ts
```

This writes `index.html`, `curves.svg`, `source.json`, `formal-profile.json`
and `result.json` under
the ignored `emdash2/tmp/probes/algebra-workbench/` directory. An optional
`--output DIRECTORY` selects another artifact location. Open the HTML locally,
or serve that directory on loopback. Generated outputs are not tracked source.
The example hashes the exact canonical workspace and formal profile in its
outer Node adapter; portable owners do not acquire I/O or hash authority.
The source/profile files contain the exact hashed bytes, without an added
newline. Their digests can be independently compared with `result.json`.

| Source owner | Responsibility |
| --- | --- |
| [algebra_ideal_witness.ts](../src/v3_2/algebra_ideal_witness.ts) | Exact source binding and independent positive-witness arithmetic |
| [algebra_ideal_singular.ts](../src/v3_2/algebra_ideal_singular.ts) | Bounded positional exchange and original-generator coefficients |
| [algebra_polynomial_workbench.ts](../src/v3_2/algebra_polynomial_workbench.ts) | Single example construction, ordinary-call facade, invalidation and existing formal delegation |
| [algebra_polynomial_plot.ts](../src/v3_2/algebra_polynomial_plot.ts) | Explicit numerical interpretation and reusable sampled SVG |
| [algebra_polynomial_workbench_view.ts](../src/v3_2/algebra_polynomial_workbench_view.ts) | Source-derived HTML result view, assumptions and open proof status |
| [Runnable example](../examples/v3_2_algebra_workbench.ts) | Node transport, actual fingerprints and artifact writing |

These are contributor-workbench APIs, exported from the root barrel. They are
not new npm package exports or a hosted product. To change the example, edit
its polynomial construction once and rerun; plotting formulas are never copied
into a second evaluator. Prior result reuse is checked against the complete
workspace, including both sides of the formal equality even when their
polynomial difference is unchanged.

Focused validation (real Singular and two bounded Lambdapi probes):

```bash
EMDASH_RUN_SINGULAR_WORKBENCH=1 EMDASH_RUN_WORKBENCH_CONFORMANCE=1 \
  node --require ts-node/register --test --test-concurrency=1 \
  tests/v3_2_algebra_ideal_witness_tests.ts \
  tests/v3_2_algebra_polynomial_workbench_tests.ts
```

Both suites are registered in the root aggregate. Their two live external
checks are opt-in; ordinary regression coverage uses injected transport.
Desktop (1440×1100) and mobile (390×844) views were inspected with Playwright,
including disclosure controls and absence of horizontal overflow. Screenshots
are under the generated directory's `output/playwright/`. The browser's initial
favicon request was resolved with a data favicon; no new runtime library is used.

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
