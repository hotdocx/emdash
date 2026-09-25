# Emdash Algebra Workbench: Shared Polynomial Workflow

Date: 2026-09-24
Plan-ID: `TS-EMDASH-ALGEBRA-WORKBENCH`
Status: public package and Vega-Lite consumer active; aggregate waiver retained
Current continuation baseline: `40cfad997c2f6c4664c9f8e5de9f2f0084bb8712`
Original consumer baseline: `df061c52338f4c28565133b2f9dae70de4d5ce39`
Branch: `goal/algebra-workbench-polynomial-v3.2`
Worktree: `/home/user1/emdash1-algebra-workbench-v1`

Main integration: the previous implementation and host/ecosystem review are
integrated through `40cfad99`. The user now selects the review's package consumer
and a new persistent goal. The existing dedicated branch/worktree and local
checkpoint authorization continue; no new main integration, push, publication,
release, history rewrite or worktree removal is selected. The aggregate waiver
remains in force.

## Current continuation: public package and Vega-Lite consumer

Selected on 2026-09-24 after the accepted
[host/ecosystem review](EMDASH_TYPESCRIPT_HOST_AND_ECOSYSTEM_REVIEW_2026-09-24.md#recommended-next-consumer).
Demonstrate **public package import → exact polynomial computation → a derived
interactive Vega-Lite view of the same mathematical source**. Use a clean
consumer of an actual locally packed artifact. No repository source aliases,
handwritten duplicate plotting formula, proof goal or formal assumption is
required for ordinary computation and rendering.

### Owners and selected slice

- Extend the existing `@hotdocx/emdash` package with one curated browser-safe
  `/algebra` entry for rational-polynomial construction, arithmetic, ideal
  membership, exact witness checking and the existing bounded curve sampler.
  Reuse the current parent/exact/polynomial/ideal/witness/plot owners; inspect
  the complete runtime and declaration closures. Keep Core, formal signatures,
  external-process transport and visualization-library dependencies outside
  this entry. Do not export the whole contributor barrel.
- The package manifest, build script, declaration configuration, workspace
  contract and packed-install verifier remain the package authorities. The
  registry's `0.3.0` and a newly packed checkout artifact are distinct evidence.
  This continuation changes local package contents without publishing a release.
- Add a small tracked external-consumer fixture with ordinary TypeScript
  application code and Vega/Vega-Lite. Prepare its own dependency graph in a
  temporary directory using pinned pnpm and the shared content store. Never
  copy/symlink the worktree's `node_modules` into the consumer.
- Reuse R=Q[x,y] and the polynomial family `(y-x², xy-c)` with exact rational
  parameter `c`. Derive the query `x³-c` from that same parameter and compute
  ideal membership with retained coefficients. Parameter and viewport changes
  update the source-derived curve samples and normal Vega-Lite segment view.
- Keep exact computation separate from numeric interpretation failure. Retain
  source/revision binding for asynchronous rendering and stale results, clear
  obsolete views on invalid input, and preserve the sampler's approximation
  limits. Avoid a new scheduler, worker framework, book renderer or language.

### Package continuation acceptance

| Row | State | Acceptance evidence |
| --- | --- | --- |
| PK-0. Scope and baseline | Complete at planning checkpoint | All 65 worktrees clean; main/goal branch equal to `40cfad99`; current authorities and package owners audited; workspace/typecheck and nearest 32-test baseline pass with one unchanged opt-in skip |
| PK-1. Curated package API | In progress | A bounded `/algebra` surface reuses exact owners; focused public-entry controls and ESM/CJS/declaration/browser packed checks; no Core/process/visualization runtime dependency |
| PK-2. External ecosystem consumer | Planned | Clean artifact install with own dependency graph; TypeScript app and actual Vega-Lite rendering of source-derived segments; exact parameter/viewport interaction and current-source binding |
| PK-3. Qualification and handoff | Planned | Relevant negative controls, artifact identity, desktop/mobile browser inspection, synchronized docs/plan and validated local checkpoint |

Keep one row in progress. Package qualification must exercise the actual
tarball; importing a sibling source entry or only drawing custom SVG cannot
complete this continuation. If an existing helper couples native computation
to formal environments or Node transport, use its narrower existing owners
or make the smallest justified separation. The optional formal workflow remains
at its existing owners and does not gate the new consumer.

Validation: workspace contract, root typecheck, changed-file lint, focused
algebra/public-entry tests and registration; package build/packed-install and
release-preflight contract checks; consumer typecheck/build and browser
interaction. User-waived full TypeScript/root-test and repository aggregates
remain skipped. No formal signature, kernel name or computation changes are
selected, so no Lambdapi aggregate or rerun of the unrelated allocation failure
is needed. Print sources/dependencies are unchanged; carry their qualification
forward unless this consumer actually changes that boundary.

### Package continuation decisions and evidence

- PK-0: workspace verification and root typecheck pass. The polynomial, ideal
  and predecessor workbench suites pass 31 tests with one unchanged live-LP
  opt-in skip (32 total, 2.58 seconds). No aggregate ran.
- Package audit: build and declaration inputs enumerate four existing entries;
  workspace and release-preflight contracts intentionally pin their export map.
  Update those owners together for the new entry and retain their existing
  compatibility checks. Public npm metadata/declaration inspection from the
  accepted review remains dated release evidence.
- The browser inspection uses the Playwright CLI skill. It is a consumer
  interaction check, not a new end-to-end test platform or renderer migration.

### Active package persistent goal prompt

Complete the public-package-and-Vega-Lite continuation governed by the current
continuation section of `docs/TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md` in
`/home/user1/emdash1-algebra-workbench-v1`, on
`goal/algebra-workbench-polynomial-v3.2`, from its current descendant state.
Let the evolving plan own concrete implementation, ordering, decisions,
validation and recovery. Deliver a curated computational package surface and
an actual clean packed-artifact consumer that uses an ordinary ecosystem
visualization library on the same exact mathematical source. Follow current
repository authorities and the user's aggregate waiver; preserve unrelated
work and make validated local checkpoints. Complete the selected rows and
synchronized handoff. Automatic certification/proof reconstruction, publication,
new main integration, history rewriting and deferred foundational migrations
are outside this continuation.

## Completed continuation: external result and internal reuse

Selected by the user on 2026-09-24 after the
[integration-mechanism clarification](EMDASH_OSCAR_AND_ALGEBRA_WORKBENCH_REVIEW_2026-09-24.md#follow-up-integration-mechanisms-and-optional-certification).
Implement **external result → typed internal object or explicit adopted
declaration → reuse in another mathematical construction**. Certification of
the CAS algorithm or automatic proof reconstruction is not an acceptance
criterion. Mathematical interpretation, source identity and explicit assumption
status remain part of the integration contract.

Reuse this existing dedicated branch/worktree from `dde9f23d`; main and this
branch were clean and equal at selection, and all 65 registered worktrees were
inspected. The earlier local-checkpoint authorization continues to apply.
The completed first-consumer fast-forward is recorded below. At selection,
this continuation authorized local checkpoints; its later user-selected main
integration is recorded above. No push, publication, branch/worktree removal
or history rewrite is selected. The user's waiver of full TypeScript and
repository-wide aggregates remains in force.

### Selected mathematical consumer

Retain the polynomial input R=Q[x,y], f1=y−x², f2=xy−1 and g=x³−1. Request
the actual Singular coefficients a=(a1,a2) with g=a1*f1+a2*f2. Preserve those
returned polynomials, even when Singular selects a different valid coefficient
vector from the native reference algorithm. Native recomputation may check or
compare the result; it must not silently replace the external output used by
the internal consumer.

Form the row D=(f1,f2,g): R³→R and the column
s=(a1,a2,−1): R→R³. Their composite is zero. This gives a concrete two-step
finite free complex `R ← R³ ← R`. It supplies a module-level reuse consumer
without claiming that this one relation generates the whole kernel, or that
the complex is a resolution, exact sequence or computed homology object.

The selected path is:

```text
Singular coefficient vector, with exact input/result binding
  -> existing polynomial/module values and arithmetic checks
  -> typed Core vector/matrix using the actual returned coefficients
  -> explicit adoption of any required computed equation
  -> an internal construction using existing module/complex owners
  -> a further typed use of the resulting object
```

Audit the existing finite-module, bounded-complex and chain-map interfaces
before finalizing the last consumer. Prefer a whole constructed complex and
an actual projection/module action or chain-map use. The existing native
complex/chain-map operations and formal recursive constructors are the starting
point. The current TypeScript complex bridge retains reified matrices and a
constructor recipe; audit whether a small Core-term assembly/mirror is needed
to consume the whole object. A metadata-only recipe or a second display of the
same coefficients does not satisfy internal reuse.

Adoption is an explicit caller action with a recorded decision, not a change
to Core conversion or a new mathematical axiom in the library. If a law is
adopted without a proof body, retain its exact type, source/result provenance,
classification and downstream dependency. Typed data without adoption remains
usable where its consumers require no law. Never assume an entire complex or
universal construction when existing constructors can assemble it from retained
data and explicitly supplied equations.

### Existing owners and fixed boundaries

- The external exchange and independent arithmetic check remain in
  `algebra_ideal_singular.ts` and `algebra_ideal_witness.ts`.
- `algebra_polynomial_module.ts`, `algebra_polynomial_presentation.ts` and
  `algebra_polynomial_bounded_complex.ts` own native vectors, maps, complexes
  and chain-map operations. Retain their ordered bases, ranks and maps.
- `algebra_formal_finite_module.ts`, `algebra_formal_bounded_complex.ts`,
  their signature environments, existing delegation/adoption and assumption
  source owners supply typed internal data, claims and explicit declarations.
- The [bounded free-complex plan](TYPESCRIPT_EMDASH_FORMAL_BOUNDED_FREE_COMPLEXES_PLAN.md)
  and active LP owners `emdash3_2_commutative_algebra_bounded_free_complexes.lp`
  and `emdash3_2_commutative_algebra_bounded_free_chain_maps.lp` own the recursive
  formal representation. New frontend assembly must follow those owners.
- Root guidance, the elaborator handoff and nested formal SOP continue to
  govern all work. No global Op/profile/variance repair, six-term comparison,
  spectral work, general proof reconstruction, new CAS framework or second
  external backend is selected by this continuation.

### Continuation acceptance and checkpoints

| Row | State | Acceptance evidence |
| --- | --- | --- |
| ER-0. Scope and owner audit | Complete; planning checkpoint `f08398bf` | Current authorities, exact owners/consumers, focused baseline and this scoped plan; aggregate waiver retained |
| ER-1. Actual external output in Core | Complete at focused qualification | Returned Singular coefficients are reified directly into typed module data; different valid coefficient choices remain distinct; no native membership solver is called by the new path |
| ER-2. Internal construction and reuse | Complete at focused qualification | Existing constructors assemble a transparent Core complex from retained matrices and one explicitly adopted equation; its projected upper differential is used in a typed internal matrix action |
| ER-3. Runnable workflow and qualification | Complete at focused qualification | Both example modes, artifact hashes, actual Singular and focused Core/LP controls pass; synchronized document/staged review and local implementation checkpoint |

Keep one continuation row in progress. Finish the actual external-data-to-
internal-reuse path; do not resolve this goal merely by noting that an adoption
API exists. If the owner audit identifies missing frontend assembly, implement
the bounded missing piece. A genuinely unsupported semantic prerequisite must
be identified at its owner and cannot be hidden by substituting native output,
postulating an opaque whole object, or merely showing a claim. Any material
change of the selected mathematical consumer must preserve the accepted end
state and be recorded here with evidence.

Use focused tests and bounded serial Lambdapi probes under the existing
2 GiB/default-deadline policy. No repository-wide aggregate or repeat of the
unrelated gluing-owner allocation failure is selected. Carry forward unchanged
qualification and add tests for actual external-data provenance, altered and
foreign-parent results, dimension errors, stale sources/results, and explicit
adoption/reuse. Source-pin failures remain review signals. A source change
requiring new mathematical rules is outside the intended frontend slice and
must be diagnosed before promotion under the formal SOP.

### Continuation decisions and evidence

- ER-0 baseline: all 65 worktrees were clean, and main/goal branch matched
  `dde9f23d`. The existing worktree's dependency graph is reused; workspace
  verification and root typecheck pass. The three nearest witness/complex/law-
  delegation suites pass 11 tests with one unchanged live-Singular opt-in skip
  (15.77 seconds). No aggregate was run.
- Owner audit: the formal complex library supplies nil/cons, whole-complex
  constructors and projections. The TypeScript bridge currently returns typed
  matrices and a recursive recipe. Complete that frontend assembly, then use
  the constructed complex's upper differential through the existing matrix-
  application owner. Native chain-map identity/composition exists; the formal
  source does not expose matching general identity/composition function names.
  Do not invent such an owner or count a native-only operation as internal reuse.
- The selected internal consumer will retain the actual external column in the
  whole complex and apply its projected differential to a typed formal input.
  Focused LP observations must confirm that the projection retains the returned
  column, alongside typechecked Core construction/application. This is a
  module action, not a claim about a complete kernel or homology calculation.
- This planning checkpoint links the accepted review and existing complex
  ledger. A new persistent goal is active with the prompt below and no token
  budget; scope and mathematical qualifications stay in this plan.
- Planning checkpoint: `f08398bf`. The existing bounded-complex emitted-Core
  conformance baseline also passes with its live opt-in (one test, 16.54 seconds).
- ER-1: `createAlgebraPolynomialWorkbenchReifier` extracts the existing pure
  reification step so the new path does not run native ideal membership.
  `algebra_external_module_reuse.ts` checks the actual external witness,
  retains its coefficients in the column `(a1,a2,-1)`, and creates the existing
  native module maps/complex plus typed Core matrices and composition.
  Source identity includes both the input workspace and chosen external result,
  including backend/version/request and coefficient encodings. Equivalent
  membership answers with different coefficient vectors cannot be silently
  interchanged during internal reuse.
- ER-2: `algebra_formal_bounded_complex_assembly.ts` adds 11 source-aligned
  opaque signature mirrors and assembles existing nil/cons/successor terms.
  Its source pin is the active complex owner SHA-256 `7d4b1373…`; no LP source,
  Core kernel owner, rewrite or unification rule changes. Existing law
  delegation checks composites of the retained external-derived matrices and
  records one `computed-equation` assumption after an explicit caller decision.
  The whole `external_reuse_complex` is a transparent definition with a
  constructor body. It is not a body-free assumed whole object.
- Internal reuse: the source's projections extract the upper differential
  from that complex reference, and `comm_ring_matrix_apply` consumes it with
  a supplied formal argument. `external_reuse_image` is a further transparent
  typed definition. Core checks construction and use; the focused LP oracle
  verifies that projection recovers the exact external column and that the
  action agrees with direct application of that column. The TypeScript
  mirrors remain opaque; this does not newly qualify standalone TypeScript
  evaluation of the complex's projection reductions.
- Controls: two distinct valid external coefficient vectors produce distinct
  Core columns and source identities. Wrong parents, altered coefficients,
  changed input/result identity, wrong ranks and absent adoption decisions
  are rejected. A valid rational alternative witness is accepted by exact
  arithmetic but rejected by the bounded integer-only formal interpretation;
  the code does not fall back to a native integral witness. Nonmembership
  observations cannot produce the internal construction.
- Focused qualification: the new six-case suite and the predecessor workbench
  suite pass 13 tests with one unchanged predecessor conformance opt-in skip
  (14 tests total, 12.51 seconds). The new live case runs actual Singular 4330,
  a positive constructor/projection/action LP probe, and a negative assertion
  against a different valid column. The negative is an assertion failure,
  not a syntax/unknown-name error. Both LP invocations use the normal serial
  2 GiB guard and a 60-second deadline. Root typecheck, changed-owner/test lint
  and registration pass; 456 suites are reachable. No aggregate was run.
- Probe envelope: only the exact consumer inputs, adopted equation and new
  definitions are emitted through the existing Core-to-LP expression serializer.
  An initial envelope included the checker environment's intrinsic defaults
  and used the wrong assertion prefix; correcting that test envelope required
  no mathematical source or rule changes. Raw attempts remain under
  `emdash2/logs/check-runs/`.
- ER-3: the runnable example passes in data-only and explicit-adoption modes.
  Their separate ignored output directories contain exact external coefficients,
  Core terms/types, the derived complex/action and assumption status. The
  source bytes and each adopted goal's source/profile bytes independently match
  their recorded SHA-256 identities. The example's rank display derives from
  the constructed modules. No book, browser renderer or hosted app is changed.

### Run the external-result continuation

From this worktree, the default mode returns typed matrices and their internal
composition without adopting any equation:

```bash
node --require ts-node/register examples/v3_2_external_module_reuse.ts
```

To explicitly select the existing assumption route, build the whole internal
complex and use its projected differential:

```bash
node --require ts-node/register examples/v3_2_external_module_reuse.ts \
  --adopt-computed-equation
```

The example writes `overview.md`, `source.json` and `result.json` under
`emdash2/tmp/probes/external-module-reuse/data/` or `adopted/`. The adopted mode
also writes the exact `law-1.source.json` and `law-1.profile.json` bytes used
by the proof-document fingerprint. `--output DIRECTORY` selects another path.
These are generated artifacts; the example and source owners remain authoritative.

The formal argument is an explicit input to the module action, not an inferred
numeric vector or another computed-equation assumption. No exactness, complete
kernel, resolution, homology result or automatically reconstructed proof is
claimed. The new source-freshness helper checks input/result identity; it does
not certify deserialized Core artifacts without fresh checking.

Focused live validation:

```bash
EMDASH_RUN_EXTERNAL_MODULE_REUSE=1 node --require ts-node/register --test \
  tests/v3_2_algebra_external_module_reuse_tests.ts
```

The completed path answers this continuation's mechanism question: actual
external output can survive typed internal realization, explicit law adoption,
whole-object construction and a further internal operation. Richer coefficient
interpretations, multiple external engines, foreign-object lifecycle and
broader OSCAR mechanism parity retain the review's untested boundaries.

The continuation is complete under the standing aggregate waiver. No complete
TypeScript or repository-wide aggregate is claimed. Implementation checkpoint
`9de1a48f` followed planning checkpoint `f08398bf` on the existing goal branch.
The user subsequently selected main integration, and main was fast-forwarded
cleanly from `dde9f23d` to `9de1a48f`. All 65 worktrees were clean at the follow-up
review; there were no temporary uncommitted changes to discard. No LP source,
formal rule, book/renderer source, package setup or lockfile changed.

The broader host/ecosystem follow-up is a documentation review. Its recommended
next consumer joins curated public package APIs to a real plotting library,
with computation useful independently of proof adoption. If selected, activate
its bounded acceptance rows here; retain one execution plan and the existing
source owners. The completed external-reuse goal remains complete.

### Completed persistent goal prompt

Complete the external-result-to-internal-reuse continuation governed by the
current continuation section of `docs/TYPESCRIPT_EMDASH_ALGEBRA_WORKBENCH_PLAN.md`
in `/home/user1/emdash1-algebra-workbench-v1`, on
`goal/algebra-workbench-polynomial-v3.2`, from its current descendant state.
Let the living plan own the concrete consumer, ordering, decisions, validation
and recovery. Preserve actual external output through typed internal realization
and reuse in another mathematical construction. Keep any adopted equations
explicit; automatic certification/proof reconstruction is not required.
Follow current repository/formal authorities and the user's aggregate waiver,
preserve unrelated work and make validated local checkpoints. Complete the
selected continuation rows and synchronized handoff without substituting a
native result or metadata-only demonstration. No push, new main integration,
publication, history rewriting, worktree cleanup or deferred foundational
migration is included.

## First consumer: objective and authority

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
working copies were preserved through the implementation goal. The original
authorization excluded main integration; the separate follow-up below authorizes
a fast-forward and removal of verified duplicate review changes. No push,
publication, history rewriting, branch deletion or worktree removal is authorized.

Validation update (2026-09-24): the user explicitly directs that the full
TypeScript gate and other repository-wide aggregates be skipped for now.
This supersedes this goal's original pre-checkpoint aggregate requirement.
The selected implementation is checkpointed on its completed focused checks;
the cancelled aggregate remains incomplete evidence, not a pass. This waiver
does not promote any mathematical profile. Main integration has its separate
subsequent authorization below.

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
| 2. External positive membership | Complete at focused qualification | Bounded Singular adapter retains original-generator coefficients; native comparison and independent exact identity checking; round-trip, wrong-parent, malformed/altered-result and cancellation/error controls |
| 3. Shared-object workbench | Complete at focused qualification | Small reusable TypeScript facade and runnable example with a derived curve view and explicit named formal goal; source changes invalidate previous results; no second handwritten plotting formula |
| 4. Qualification and handoff | Complete under explicit aggregate waiver | Focused tests, typecheck/lint, actual backend/example run, visual inspection and document checks pass; cancelled full-gate receipt retained; synchronized local implementation checkpoint |

Keep one row in progress. Rows 2–3 form one bounded shared-behavior tranche;
checkpoint their implementation on row 4's focused qualification under the
user's explicit aggregate waiver. Independent document/decision checkpoints
may precede it. Stop when this consumer answers
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
The original plan required one complete `./scripts/pnpmw run check:ts` after
focused qualification. The user's later instruction explicitly waives that
gate and other repository-wide aggregates for now. Keep the complete gate
incomplete in the handoff; do not report focused checks as its equivalent.
No further aggregate is selected while this instruction applies.

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
  Workspace, registration, typecheck and lint passed. The test phase was still
  running at documentation checkpoint `167d1da2`. The user subsequently
  instructed that this gate and other repository-wide aggregates be skipped
  for now. Sending SIGTERM to its owning DevOps runner invoked the existing
  process-group cancellation path; no group members remained afterward.
  Receipt `typescript-20260924T222204Z-e42853789d7a4e94b5fb01368849e54f`
  records `cancelled`, command exit 130, and 1,536.60 seconds. All recorded gate
  input hashes still match. Cancellation diagnostics are not a completed
  regression verdict; no full TypeScript pass is claimed and no replacement
  aggregate is selected under the user's instruction.
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

## Completion boundary

The selected consumer is implemented: one source constructs the polynomials,
both engines compute with them, exact arithmetic checks positive witnesses,
the derived plot reuses their terms, and fresh Core checking retains the named
formal goal with its explicit premises. The focused suite covers all 15 new
tests, including real Singular and guarded positive/negative Lambdapi probes.
Source changes invalidate prior results; altered parents/witnesses and
unsupported coefficient interpretations are rejected. Saved source/profile
bytes have been independently checked against their recorded hashes.

Checked proof reconstruction is optional and was not selected for this
consumer. This is consistent with the computation-first CAS/delegation design;
it is not a prerequisite for typed internal data or explicit opaque declaration
adoption. If reconstruction of this exact equality is later selected, it needs
the relevant existing ring-law proof interface and a replayable proof plan.
No completed theorem, general rational-field interpretation, unrestricted
higher profile, certified plot topology or complete negative certificate is
claimed. A native module/homology consumer remains later work.

The local implementation checkpoint uses the user's explicit aggregate waiver.
The incomplete TypeScript aggregate and the unrelated gluing-owner allocation
failure stay visible above. Full formal CI, package/release, hosted and broad
integration qualification are not claimed. The original goal completed at
`75b3ecdb` without changing main. The subsequent fast-forward is recorded below;
no push, publication, history rewrite or worktree removal was performed.

## Main integration and clarification follow-up

On 2026-09-24 the user requested fast-forwarding main and clearing its temporary
uncommitted review changes. Main was verified at baseline `df061c52`, with no
staged work and exactly those two pending paths. The DevOps review matched the
branch byte-for-byte; the original OSCAR review was recovered exactly from the
committed version by removing its added continuation paragraph and restoring
the earlier status line. No review body or unique evidence was discarded.

Exact original files and SHA-256 hashes are retained under main's ignored
`emdash2/tmp/probes/workbench-main-integration-20260924T231925Z/`. The verified
duplicate working changes were cleared and main fast-forwarded to `75b3ecdb`,
leaving it clean. This same follow-up authorizes the further fast-forward of
the clarification/regression checkpoint; the goal branch/worktree remain.
The aggregate waiver persists and no aggregate is rerun for this integration.

The user also clarified that computational/internal integration is primary and
CAS certification is optional. The
[OSCAR review follow-up](EMDASH_OSCAR_AND_ALGEBRA_WORKBENCH_REVIEW_2026-09-24.md#follow-up-integration-mechanisms-and-optional-certification)
now records the exact current boundary. The existing
`adoptAlgebraFormalTrustedComputation` already accepts this example's native
delegation result and produces a typed, body-free opaque declaration with a
trusted-assumption artifact and ordinary goal patch. A new focused regression
verifies that route and leaves the original environment/document unchanged.
The workbench suite passes seven tests with one unchanged opt-in conformance
case skipped; its prior positive/negative Lambdapi evidence remains applicable.
Changed-test lint passes. No runtime or mathematical source changed.

The default demo still displays an open goal; it does not automatically assume
the claim. Its formal delegation currently uses native CAS output. Directly
feeding the returned Singular coefficient vector through the formal data path,
and exposing an explicit adoption control in the example, remain consumer
wiring that does not require proof reconstruction first. The broader OSCAR
mechanism-parity assessment is plausible architecture with bounded evidence,
not an established full-parity result. The review lists the untested mechanisms;
this follow-up does not launch a new implementation goal.

## Persistent goal prompt

This is the completed original goal prompt. The later main-integration
authorization above supersedes its no-main-merge restriction for this follow-up.

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
