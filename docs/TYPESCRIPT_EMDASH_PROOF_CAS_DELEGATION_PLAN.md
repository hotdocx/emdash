# TypeScript/emdash Proof–CAS Delegation And Formal Adoption Plan

Date: 2026-08-31

Plan-ID: `TS-EMDASH-PROOF-CAS-DELEGATION`

Status: active implementation on a dedicated branch/worktree; initial
architecture and Git boundary frozen, owner audit in progress.

Baseline: `79f3bb7fd05446fe14739bfb056b7dc2d254affd`

Branch: `goal/proof-cas-delegation-v3.2`

Worktree: `/home/user1/emdash1-proof-cas-delegation-v1`

Decision-Response-Evidence:
`infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a05814-7de7-77d2-82fa-914065369d34`

## Purpose

This plan governs the first goal-aware usability bridge between the completed
TypeScript/emdash proof-assistant infrastructure and the focused algebra
engine. The individual endpoints already exist:

- typed algebra operations, engines, exact results, and computation graphs;
- stable named proof goals and replayable inert proof plans;
- parent-aware computational-to-formal affine realizations;
- explicit Core construction for selected formal covers, localizations, and
  Čech presentations; and
- declaration/workspace infrastructure for checked definitions, checked
  theorem bodies, and explicitly reviewed opaque assumptions.

What does not yet exist is the protocol connecting those endpoints:

```text
named formal goal + explicit computational realization
                         |
                         v
               typed AlgebraOperation request
                         |
                         v
          native TypeScript / graph / selected oracle
                         |
                         v
              typed computation artifact
                         |
             +-----------+----------------+
             |           |                |
             v           v                v
          observe     reify data      adopt formal claim
                                          |
                                  checked reconstruction
                                  or explicit assumption
```

The goal is computation-first. It does not organize the bridge around proof
certificates or require that the native CAS be verified. It does require the
formal development to distinguish an ordinary checked proof from an explicit
assumption introduced because an author chose to trust a computation.

## Authority And Prerequisites

The direct computational authorities are:

- `src/v3_2/algebra_engine.ts` for operations, engines, algorithms, exact
  result quality, assumptions, diagnostics, limits, and reusable artifacts;
- `src/v3_2/algebra_graph.ts` for explicit backend-neutral computation
  graphs and direct graph execution;
- the focused algebra, quotient, ideal, Zariski, localization, presented
  module, affine, and Čech owners under `src/v3_2/algebra_*.ts`;
- `docs/TYPESCRIPT_EMDASH_FOCUSED_CAS_AND_CATEGORICAL_ENGINE_PLAN.md` for the
  computation-first and CAP/homalg-aware architecture; and
- the completed affine, presented-module, and varying-ring Čech plans for
  later candidate consumers.

The proof-assistant and authoring authorities are:

- `src/v3_2/proof_plan.ts` and `proof_plan_patch.ts` for inert, replayable
  proof plans and named-hole replacement;
- `src/v3_2/lf_declaration_fragment_authoring.ts`, `lf_workspace.ts`, and the
  checked transfer/compiler owners for explicit declaration and workspace
  construction;
- `docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md` for stable
  proof identity, proof authority, evidence distinctions, and replay; and
- `docs/TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md` and the active explicit-Core
  authorities named there.

The formal mathematical authority remains the active Lambdapi v3.2
development under `emdash2`, especially the existing finite-family,
commutative-ring, unimodular, Zariski-cover, equality, and localization
owners. The bridge reuses those owners. A missing TypeScript route does not
authorize a new Lambdapi symbol or rewrite rule.

The root and nested `AGENTS.md` files and
`docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md` govern implementation,
validation, recovery, and checkpointing.

The historical `CAS-FORMAL-BRIDGE-10` row was correctly deferred when the
focused-CAS branch completed. The later affine formal-bridge goal activated
and completed its one-way realization component. This plan does not restart
that work: it adds goal-aware delegation and result adoption above it.

## Current Architectural Seam

The algebra side already has:

```text
AlgebraOperation<I,O>
AlgebraEngine
AlgebraComputed<O>
AlgebraComputationGraph
```

An `AlgebraComputed<O>` retains operation, engine, algorithm, quality,
normalized output, assumptions, diagnostics, and reusable intermediates.
This is the correct computational result boundary.

The proof side already has stable named holes and complete checked replay:

```text
CoreProofPlan
CoreProofPlanHole
CoreProofPlanPatch
CoreProofPlanExecution
```

Those plans are intentionally inert. Their nodes are `exact`, `intro`,
`apply`, `have`, and `hole`; every semantic step delegates to the existing
checked refiner. An effectful or asynchronous `compute` node must not be added
to this grammar merely for convenience.

The affine formal bridge already reifies canonical computational quotient
elements into a selected formal ring and constructs existing formal objects
when actual formal law terms are supplied. It deliberately enforces:

```text
trusted-computation metadata != formal equality inhabitant.
```

That invariant remains valid. The new layer introduces a separate, explicit
authoring action that may install a visible assumption at the exact goal type.
It does not reinterpret a Boolean or status tag as a proof inside the affine
adapter.

One additional gap is now explicit: `serializeAlgebraComputationGraph`
serializes topology only and intentionally excludes runtime input values.
Consequently, graph identity is insufficient for replay or stale-result
detection. The delegation artifact needs adapter-owned canonical input and
output encodings in addition to operation, schema, graph, engine, and
algorithm identities.

## Governing Principles

1. Computation runs at the authoring/elaboration/workspace layer, not in Core
   conversion, kernel normalization, Lambdapi rewriting, or proof-time
   unification.
2. Native in-process TypeScript is the default engine. Existing graphs and
   optional oracles remain interchangeable behind the same operation
   contract.
3. A formal computation adapter interprets one exact algebra operation for
   one explicit formal/computational realization. Runtime schemas alone do
   not establish a logical interpretation.
4. The first surface is direct TypeScript construction. No string parser,
   command language, or TypeScript macro syntax is a prerequisite.
5. Adapters are explicit scoped values in the first version. Do not introduce
   a mutable global realization, tactic, or operation registry.
6. Arbitrary Core AST decompilation is not selected. Acquisition starts from
   an explicit parent-aware realization and an exact named goal.
7. Every request binds the selected goal/context, realization, operation,
   input, engine policy, limits, and desired interpretation. Every result
   retains the actual engine, algorithm, quality, assumptions, diagnostics,
   output, and reusable intermediates.
8. Observation, data reification, checked proof reconstruction, and trusted
   adoption are distinct outcomes. None silently escalates to another.
9. Computed data may be reified and checked without making a theorem claim.
10. Trusted adoption is an explicit authoring decision. It installs a
    body-free declaration at the exact checked target and records its
    computational origin; it does not pretend that the declaration has a
    checked theorem body.
11. An AI or provider may propose trusted adoption but may not silently
    approve it.
12. The existing affine `trusted-computation` no-law behavior remains
    unchanged. A trusted-adoption declaration supplies an actual Core
    reference only after the separate adoption step.
13. Proof plans remain ordinary inert checked data. A successful checked or
    trusted adoption ultimately supplies an ordinary `exact` plan or hole
    replacement in the appropriately extended declaration workspace.
14. Negative, unsupported, partial, or failed computations remain useful
    observations and diagnostics. They do not close positive goals.
15. The first implementation accepts exact native computations. General
    probabilistic, heuristic, partial, or assumption-laden adoption requires
    a later explicit policy and consumer.
16. Request/result replay compares canonical payload bytes as well as stable
    identities. Topology-only graph JSON cannot authorize reuse.
17. No recent module, Čech, or homological CAS type receives a fabricated
    formal counterpart merely to demonstrate the bridge. A suitable active
    formal owner or explicit interpretation is required.
18. Whole outputs remain primary. Coefficients, reductions, combinations,
    witnesses, diagnostics, and reusable computations are retained after a
    Boolean projection is observed.
19. Validation is proportional and affected-boundary-first. Repository-wide
    `check:all`, print, book, release, and unrelated kernel gates are outside
    ordinary rows.

## Proposed Core Contracts

The exact types and names follow the owner audit. The intended separation is
conceptually:

```text
FormalComputationAdapter<Input,Output> {
  operation
  acquire(goal, realization) -> Input
  encodeInput(input) -> canonical bytes
  encodeOutput(output) -> canonical bytes
  interpret(goal, realization, output) -> FormalInterpretation
}

FormalComputationRequest {
  stable goal and target identity
  explicit realization identity
  operation and schema identities
  canonical normalized input
  engine/algorithm/limit policy
}

FormalComputationResult {
  exact request identity
  AlgebraComputed output
  canonical output encoding
  formal interpretation
  freshness/replay data
}
```

An interpretation may expose one or more of:

```text
observation
explicit Core data
exact formal claim type
checked Core proof / CoreProofPlan
trusted-adoption proposal
```

The adapter does not itself mutate a workspace or approve an assumption.

## Adoption Modes

### Observe

Execute the request, retain the whole result, and expose its mathematical
projection and diagnostics. No Core term or declaration is installed.

### Reify data

Translate computed coefficients, elements, matrices, maps, covers, or other
selected outputs into explicit Core. Check every resulting term against its
selected type and declaration environment. This route introduces no theorem
claim.

### Checked reconstruction

When a concrete adapter can build a genuine proof term or ordinary proof
plan, independently check it and return a normal `CoreProofPlanPatch`. This
is optional and consumer-driven; it is not the primary CAS architecture.

### Trusted adoption

After an explicit caller action, create a narrowly scoped opaque declaration
whose type is exactly the selected formal claim. Record a canonical companion
artifact containing the request/result identity and the explicit adoption
decision. Extend the declaration workspace through the existing authoring and
transfer infrastructure, then close the selected goal with an ordinary
reference to that declaration.

The sequence is:

```text
computed result
  -> explicit trusted-adoption action
  -> checked body-free declaration at the exact claim type
  -> ordinary Core reference
  -> ordinary exact proof-plan replacement
```

This is an explicit development assumption, not an opaque equality bridge in
the mathematical kernel. It introduces no global Core owner, reduction, or
unification rule. The declaration's type is checked; its missing body remains
visible in the workspace policy and artifact.

## First Concrete Consumer: Unimodular Zariski Cover

The first vertical slice is the current finite basic-open cover law. It is
selected because both endpoints already exist:

- the Zariski operation computes a whole unimodular combination, including
  coefficients, combination, remainder, basis, and membership computation;
- the affine formal realization reifies generators and coefficients into one
  selected formal ring;
- the formal bridge knows the exact right-associated dot-product equality and
  constructs `CommRingUnimodularPresentation` and
  `CommRingZariskiCoverPresentation`; and
- the current missing input is precisely a formal law term.

The intended route is:

```text
formal ring and generator realization
  -> typed native unimodular request
  -> retained exact coefficients and equation
  -> reified coefficient family
  -> exact formal dot-product-equals-one target
  -> observe, checked reconstruction, or explicit trusted adoption
  -> existing comm_ring_unimodular_intro
  -> existing comm_ring_zariski_cover_intro
```

The ordinary trusted-computation realization must continue to reject formal
cover construction before adoption. After adoption, the actual opaque Core
reference is an explicit law term supplied through the ordinary formal-data
route. Its external trusted origin remains attached to the companion
adoption artifact rather than being mislabeled as a checked theorem body.

The positive fixture should use a nontrivial cover such as
`D(x), D(1-x)` or the existing ternary affine-plane cover. A negative
non-unimodular family must produce a useful result or diagnostic and leave the
goal open.

## Second Consumer: Ideal Membership / Quotient Equality

A second ring-level consumer must demonstrate that the contracts are not
hard-coded to Zariski covers. The initial candidate is ideal membership or
the corresponding quotient-equality claim:

```text
p - q belongs to I
  -> computational quotient values agree
  -> adapter constructs the selected formal equality target
  -> observe or explicitly adopt the claim.
```

The owner audit must state the realization assumptions needed for this
interpretation. The active formal library has universal-property polynomial
algebras rather than the CAS's concrete quotient syntax; the adapter must not
claim that an arbitrary supplied formal ring respects the computational ideal
without explicit data or trusted adoption. If no sound exact interpretation
is available at the selected boundary, record that result and choose another
existing ring-level consumer rather than inventing a formal quotient owner.

Negative membership is an observation or counter-result and cannot close a
positive equality goal.

## CAP/homalg Relationship

CAP and homalg remain major design inspirations:

- CAP specifies categorical operations, derives constructions, selects
  implementations dynamically, and specializes programs through
  CompilerForCAP;
- homalg expresses broad homological algorithms over matrix/ring backends and
  external CAS dictionaries; and
- both ecosystems have substantially greater algorithmic breadth and
  maturity than the current focused emdash CAS.

Emdash can nevertheless integrate the proof-assistant/CAS loop more directly
for its own architecture:

| Concern | CAP/homalg | Emdash target |
| --- | --- | --- |
| operation selection | dynamic categorical methods and backend dictionaries | typed `AlgebraOperation` and explicit schemas |
| computation program | GAP operations, derivations, specialized compiler output | explicit typed categorical/algebra graph |
| parent identity | runtime category/ring objects | stable computational parents plus formal realizations |
| formal goal | outside the system's responsibility | stable named Core goal and exact context |
| logical interpretation | external/manual | explicit operation-specific adapter |
| adoption | not a proof-assistant concern | observe, reify, reconstruct, or explicitly assume |
| backend | GAP and external CAS ecosystem | native TypeScript by default, optional oracle engines |

The intended advantage is architectural integration, not a claim that emdash
already subsumes CAP/homalg's functional coverage. The complete retained path
is:

```text
formal object
  <-> computational realization
  -> categorical/algebra operation
  -> selected algorithm
  -> whole computed result
  -> formal interpretation
  -> explicit adoption policy.
```

Typed construction avoids recovering an enhanced syntax tree from arbitrary
dynamic host-language execution. Whole universal constructions and direct
efficient representations may coexist, with CAP-style projections and
derived facades layered above them.

## Proposed Implementation Sequence

### 1. Exact owner and consumer audit

Trace the exact APIs for:

- in-memory named proof goals and their stable serialized identities;
- proof-plan hole replacement and checked replay;
- declaration-fragment creation, body-free free declarations, workspace
  extension, and exact theorem references;
- affine formal ring/element/cover realization and deterministic reification;
- Zariski operation input/output construction and native execution;
- formal dot-product law target construction; and
- canonical serialization already available for every selected payload.

Record whether the first goal is closed under a declaration environment or
requires abstraction over a local context. The first implementation may be
restricted to closed, meta-free declaration-scope goals if that gives the
complete end-to-end consumer without a new local-assumption mechanism.

### 2. Delegation contracts and canonical artifacts

Implement immutable browser-safe request, adapter, interpretation, result,
and artifact contracts. Validate exact operation/schema identities, selected
realization, normalized payloads, goal target, engine policy, quality, and
limits.

Adapters must supply canonical payload serialization. The artifact must not
pretend that topology-only graph JSON contains the execution input.

### 3. Native execution and observation

Run one exact operation directly or through the existing graph/engine
boundary. Preserve failure atomicity, cancellation, limits, whole result
metadata, and exact diagnostics. Bind the result to the selected named goal
without changing the proof plan or workspace.

### 4. Explicit-data and checked adoption

Implement selected Core-data reification and independent type checking.
Provide the generic route for an adapter-supplied checked proof term or proof
plan to become an ordinary hole replacement. No checked reconstruction is
required merely to advance the trusted consumer.

### 5. Explicit trusted adoption

Implement a separate explicit action that validates a fresh exact result,
constructs one reviewed opaque declaration at the exact goal type, records
its computation/adoption artifact, extends the workspace, and produces an
ordinary exact proof-plan replacement.

The action must reject stale targets, mismatched contexts, foreign
realizations, nonexact quality, changed payloads, and implicit approval.

### 6. Zariski-cover vertical slice

Connect the existing native unimodular operation, affine formal reifier,
formal dot-product target, explicit adoption routes, and existing cover-term
builder. Test positive observed/trusted construction and negative no-close
behavior.

### 7. Second ring-level consumer

Implement ideal membership / quotient equality if the owner audit validates
the interpretation boundary. Otherwise record the obstruction and select the
smallest existing ring-level formal consumer that exercises the generic
contracts without adding a new formal theory.

### 8. Replay, invalidation, and direct TypeScript usability

Serialize requests, results, and adoption decisions canonically. Reuse a
stored computation only when goal, context, realization, operation, schemas,
input, engine, algorithm, quality, assumptions, and output fingerprints still
match. Expose concise direct TypeScript helpers; defer parsing and tactic
syntax.

## Implementation Ledger

| Row | Status | Dependency | Deliverable and acceptance boundary |
| --- | --- | --- | --- |
| `PCD-PLAN-0` | complete; plan checkpoint pending | reviewed continuation and completed computational/formal/proof endpoints | this living plan, isolated branch/worktree, exact baseline, architecture, staged rows, trust boundary, validation, and Git limits |
| `PCD-AUDIT-1A` | pending | `PCD-PLAN-0` | exact proof-goal/declaration/adoption, algebra-operation, realization, Zariski-target, and serialization owner map; first positive/negative fixtures; no behavior change |
| `PCD-CONTRACT-2A` | pending | `PCD-AUDIT-1A` | immutable adapter/request/interpretation/result/artifact contracts, canonical payload encoding, exact identity and quality validation, focused negatives |
| `PCD-DELEGATE-3A` | pending | `PCD-CONTRACT-2A` | native/graph exact execution bound to one named goal and realization, observation result, limits/cancellation/diagnostics, no proof or workspace mutation |
| `PCD-ADOPT-4A` | pending | `PCD-DELEGATE-3A` | explicit Core-data checking, optional checked-plan route, explicit trusted opaque-declaration adoption, ordinary exact patch, stale/implicit/foreign rejection |
| `PCD-ZARISKI-5A` | pending | `PCD-ADOPT-4A` | end-to-end unimodular-cover delegation, coefficient reification, exact formal law target, observed and trusted paths, existing cover construction, negative open-goal behavior |
| `PCD-IDEAL-5B` | pending | `PCD-ADOPT-4A`, audit-approved interpretation | second ring-level ideal-membership/quotient-equality consumer or documented obstruction plus smallest sound replacement consumer |
| `PCD-REPLAY-6A` | pending | both concrete consumers | canonical request/result/adoption serialization, exact freshness/invalidation, deterministic direct-TypeScript usability surface |
| `PCD-CONFORMANCE-7A` | pending | all preceding active rows | representative portable artifacts, direct/native-graph agreement where applicable, exact checked workspace behavior, focused live Lambdapi conformance only if emitted terms or owner bindings change |

Rows may be split into lettered subtranches. A row completes only after
implementation, focused positive and negative tests, proportional validation,
synchronized decisions/results, and a local checkpoint.

## Initial Decision Ledger

| Decision | Status | Rationale |
| --- | --- | --- |
| `D-PCD-001` | accepted | The next goal is a typed proof–CAS delegation and formal-adoption layer, not another isolated mathematical CAS extension. |
| `D-PCD-002` | accepted | Effectful computation belongs outside the inert `CoreProofPlan` grammar and outside Core/kernel normalization. |
| `D-PCD-003` | accepted | `AlgebraOperation`/`AlgebraComputed` remain the computational owner; adapters add exact logical interpretation rather than duplicating algorithms. |
| `D-PCD-004` | accepted | Adapters and realizations are explicit scoped values in v1; no mutable global tactic or realization registry is introduced. |
| `D-PCD-005` | accepted | Observation, data reification, checked reconstruction, and trusted adoption are noncoercive distinct outcomes. |
| `D-PCD-006` | accepted | Trusted adoption is a separate explicit user-level assumption action, not a conversion of `trusted-computation` metadata into an equality inhabitant. |
| `D-PCD-007` | accepted | Ordinary proof plans remain checked and replayable; adoption lowers to existing declaration/workspace infrastructure plus an ordinary exact patch. |
| `D-PCD-008` | accepted | The first trusted-adoption policy is exact-quality native computation only; heuristic/probabilistic/partial adoption is separately gated. |
| `D-PCD-009` | accepted | Adapter-owned canonical payload bytes are required because computation-graph serialization intentionally omits runtime values. |
| `D-PCD-010` | accepted | The first vertical consumer is the existing unimodular Zariski-cover law over an explicit formal/computational realization. |
| `D-PCD-011` | accepted | A second ring-level consumer must test genericity; ideal membership/quotient equality remains audit-gated by its formal realization assumptions. |
| `D-PCD-012` | accepted | Recent module, Čech, and homological computation remains computational data until a genuine formal owner/interpretation is selected. |
| `D-PCD-013` | accepted | Emdash targets tighter proof/CAS architectural integration than CAP/homalg, not a present claim of greater algorithmic coverage or maturity. |
| `D-PCD-014` | accepted | Direct TypeScript authoring is the initial UX; parser, tactic language, CLI, hosted service, and public-package promotion are deferred. |
| `D-PCD-015` | accepted | No new Core owner, checker rule, Lambdapi symbol, rewrite, unification rule, or formal quotient theory is a prerequisite. |
| `D-PCD-016` | accepted | Local validated checkpoint commits are permitted on this dedicated branch; push, merge, publication, release, history rewriting, and cleanup are not. |
| `D-PCD-017` | accepted | `main` was fast-forwarded only to the completed `79f3bb7` Čech-cochains baseline before this branch was created; orthogonal path-cubical/strictness work remains excluded. |

## Validation Policy

Use proportional checks:

- exact diff and staged-diff hygiene for plan/documentation changes;
- `workspace:check`, focused affected tests, root typecheck, and affected-file
  lint for TypeScript implementation rows;
- one complete `check:ts` at the actual shared TypeScript integration boundary
  if required by the root `AGENTS.md`, not after every tranche;
- focused deterministic artifact/replay tests for every request and adoption
  mode;
- the bounded active-kernel check when a target depends on current kernel
  owner names or computation, as required by the root handoff;
- owner-position probes, warning comparisons, audits, catalog/health updates,
  and bounded CI only if Lambdapi semantics change; and
- no repository-wide `check:all`, print, book, release, or unrelated
  aggregate merely for reassurance.

Every Lambdapi invocation is bounded to at most 90 seconds.

## Git Authorization And Checkpoints

The user authorizes the dedicated branch/worktree and continuation according
to this plan, including local validated checkpoint commits as work
progresses. Each checkpoint requires a coherent bounded tranche, synchronized
living plan, focused green evidence, exact path-scoped staging, staged-diff
review, and `git diff --cached --check`.

This authorization does not include push, merge, rebase, amend, reset,
history rewriting, publication, release, PR creation, branch deletion,
worktree removal, or integration of the orthogonal path-cubical/strictness
branches.

## Non-Goals

- proving the native CAS correct;
- organizing the architecture around proof certificates;
- making computation part of kernel reduction or proof-time unification;
- adding an effectful `compute` tag to `CoreProofPlan`;
- arbitrary goal mining or arbitrary Core AST decompilation;
- a global mutable tactic/provider/realization registry;
- automatic trusted adoption by an AI or computation engine;
- trusting probabilistic, heuristic, partial, or unacknowledged-assumption
  results in the first version;
- inventing formal polynomial-quotient, module, complex, Čech, or cohomology
  owners merely to expose existing CAS data;
- recreating GAP filters/dynamic dispatch or CompilerForCAP AST recovery as
  the public TypeScript architecture;
- string parsing, a general tactic language, hosted execution, or package
  publication; or
- pushing, merging, releasing, or cleaning up the goal branch/worktree.

## Completion Boundary

This goal is complete when every active ledger row is implemented, rejected
with durable evidence, or explicitly deferred behind a concrete
prerequisite; the exact request/result/adoption boundaries are documented;
the Zariski consumer runs end to end from named goal and realization through
native computation to observed and explicitly trusted formal use; a second
consumer or sound documented obstruction tests genericity; stale or implicit
adoption fails closed; all affected proportional gates pass; and every
bounded tranche is checkpointed with the living plan synchronized.

Completion does not require proof certificates, verification of the CAS,
formal module/cochain theory, a parser, a public tactic, external CAS
execution, a repository aggregate, integration into `main`, or publication.

## Persistent `/goal` Launch Prompt

Work in `/home/user1/emdash1-proof-cas-delegation-v1` on
`goal/proof-cas-delegation-v3.2`. Implement the proof–CAS delegation and
formal-adoption objective with every evolving API choice, owner discovery,
trust-boundary decision, consumer selection, validation result, checkpoint,
and completion condition delegated to this living plan. Re-read root and
nested guidance plus the current plan on every continuation; inspect all
worktrees, staged/unstaged state, and baseline ancestry; preserve the
completed `79f3bb7` baseline and exclude orthogonal path-cubical/strictness
work. Keep computation outside Core/kernel and inert proof plans; reuse typed
`AlgebraOperation`/graphs, explicit formal realizations, checked declaration
workspaces, and ordinary proof-plan patches. Prioritize the native exact
Zariski vertical consumer, then one audit-approved generic ring consumer.
Use proportional affected tests and bounded Lambdapi checks, avoid unrelated
aggregates, and make only local validated checkpoint commits authorized by
this plan. Do not push, merge, publish, release, rewrite history, remove
worktrees, or broaden the formal/kernel theory without separate user
authorization.
