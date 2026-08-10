# TypeScript/emdash Proof Assistant And Goal Graph Plan

Date: 2026-08-10

Plan-ID: `TS-EMDASH-PROOF-ASSISTANT`

Status: living architecture and implementation ledger; reviewed strategy
recorded; qualified predecessor baseline integrated into public `main`;
`DEV-CATALOG-1`, `DEV-CLI-2A`, and `DEV-CLI-2B` implemented and
final-proportional-green under the persistent 2026-08-10 long-aggregate
policy recorded below; `PLAN-DECOMPOSE-3A/3B` complete and the selected-
constructor base-plan macro final-proportional-green;
`PLAN-DECOMPOSE-3B1A/3B1B` complete and contextual `have` plus its coordinated
v2 source/artifact family final-proportional-green; the general `refine` tag
audit and root-scoped typed-term template macro are complete and final-
proportional-green; the cross-goal coupling audit and its separate portable
direct-dependency graph are complete and final-proportional-green;
the stateless development-graph command audit and its exact projection are
complete and final-proportional-green;
the simplifier audit has separated proof-level rewriting from definitional
computation; its bounded proof-checker conversion prerequisite is implemented
and final-proportional-green; the first proof-producing simplifier has an
exact frozen v1 contract and is the sole semantic row in progress;
later search, library, external-automation, and general goal-graph rows remain
dependency-gated

Branch: `goal/typescript-emdash-proof-assistant-v1`

Worktree: `/home/user1/emdash1-classes-v1`

Baseline: `9c633c85b66efb4ac7619912e8d15f928b32d733`
(`docs: close classes goal readiness audit`)

Git-Boundary: local and public `main` are exactly the qualified predecessor
`9c633c8`; the frozen plan checkpoint is `671c56a`; the `DEV-CATALOG-1`
semantic checkpoint is `fcc4547`; its synchronized ledger checkpoint and the
dedicated branch's preceding published baseline are `2484e23`; the
`DEV-CLI-2A` architecture, semantic, and ledger checkpoints are `ee31ab9`,
`c60d09e`, and `fa84b05`; the `DEV-CLI-2B` architecture and semantic
checkpoints are `a6f0fbe` and `b5a4cb2`. The branch has not been merged into
`main`, tagged, released, or published to npm; the `DEV-CLI-2B` synchronized
ledger checkpoint is `238bddf`; the proof-plan audit checkpoint is `144afda`
and the corrected selected-constructor semantic checkpoint is `934bf13`; the
contextual-`have` audit checkpoint is `d25e550` and its semantic checkpoint is
`b20595b`; the general-`refine` audit checkpoint is `27233be` and its
management-only template semantic checkpoint is `39d9fc8`.
The cross-goal coupling audit checkpoint is `48405eb` and its semantic
checkpoint is `de971de`; its synchronized ledger checkpoint is `d90db3b`.
The development-graph command audit checkpoint is `e0d3e4f` and its semantic
checkpoint is `8e21afb`; its synchronized ledger checkpoint is `3628315`.
The proof-checker conversion audit checkpoint is `3c102ec` and its semantic
checkpoint is `7c9d8f7`; its synchronized ledger checkpoint and current clean
published goal-branch tip are `74e6de8`.

Depends-On:

- [`TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`](./TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md);
- [`TYPESCRIPT_EMDASH_AI_NATIVE_WORKSPACE_AND_PROOF_PLAN.md`](./TYPESCRIPT_EMDASH_AI_NATIVE_WORKSPACE_AND_PROOF_PLAN.md);
- [`TYPESCRIPT_EMDASH_STRUCTURES_CLASSES_AND_INSTANCE_SYNTHESIS_PLAN.md`](./TYPESCRIPT_EMDASH_STRUCTURES_CLASSES_AND_INSTANCE_SYNTHESIS_PLAN.md);
- [`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md);
- [`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md);
- the active emdash v3.2 authority chain under `emdash2/`; and
- the explicit Core, checker/evaluator, session/refiner, proof-document,
  workspace, structures/classes, and instance-synthesis implementations.

Decision-Response-Evidence:
`emdash2/tmp/ai-responses/sessions/2026-08-10_019fe959bb57/responses/0001_2026-08-10T02-00-51Z_019fe960-8d4d-7110-af94-6dfda8f1730c.md`.
The ignored archive is historical reasoning evidence only. This plan, active
code, and repository SOP are authoritative.

## Executive Decision

Emdash should expand in two deliberately separated stages.

1. It should first become a genuinely usable **AI-native proof-engineering
   system** over its qualified TypeScript checker and backend-neutral explicit
   Core.
2. It may then reuse the same immutable graphs, stable holes, patches,
   fingerprints, and provenance for a broader **AI-native goal assistant**.

The second stage must be layered beside mathematical proof authority rather
than obtained by weakening the meaning of `proved`. A theorem, a deterministic
verification, an experimental observation, a human approval, an AI proposal,
and a completed external task are different evidence classes. The goal layer
must never silently promote one into another.

The product architecture is therefore:

```text
human or AI author
        |
        v
reviewable TypeScript builders + inert data + proposed patches
        |
        +---------------- proof-engineering services ----------------+
        |  development graph | plans | search | simp | providers     |
        +-------------------------------------------------------------+
        |
        v
backend-neutral, explicit, meta-free emdash Core
        |
        +---------------------------+
        |                           |
        v                           v
small TypeScript checker       optional deterministic
(production authority)         Lambdapi emitter/oracle

separate later plane:
typed goal/evidence graph -> policy-derived status -> Arrowgram/browser view
```

This is not “Lean with different syntax.” The intended competitive advantage
is a compact trusted kernel surrounded by inspectable, patchable, replayable,
content-addressable proof artifacts designed from the beginning for
human--AI collaboration.

## Why The Baseline Is Ready

The selected baseline already supplies the hard lower layers:

- generic explicit Core and a small TypeScript checker/evaluator;
- transactional contextual metavariables, unification, and proof-state
  inspection;
- inert `exact`, `intro`, `apply`, and stable named `hole` proof plans;
- deterministic complete/incomplete proof artifacts;
- declaration, fragment, and exact-closure workspace graphs;
- mounted fixed-file verification and source-absent offline cache reuse;
- direct TypeScript authoring without a declaration text parser;
- parameterized structures, named construction, class schemas, strict
  multiple inheritance with canonical ancestor sharing;
- immutable instance scopes, bounded recursive synthesis, output and
  semi-output scheduling, and saturated class-call elaboration; and
- a locally qualified, browser-safe `@hotdocx/emdash@0.1.0` package boundary
  plus token-free release engineering.

The remaining gap is mostly above the checker: general development
management, richer proof decomposition, rewriting and routine automation,
premise discovery, proof maintenance, library activation, evaluation, and
external certificate integration. The repository inventory found no current
general simplifier, theorem-search index, proof-repair engine, tactic
combinator suite, model finder, or general development command. Those are
product gaps, not reasons to alter the mathematical kernel.

## Product Success Criteria

Emdash becomes a competitive proof assistant when an author or agent can:

1. define and check a multi-module development through a stable public API;
2. inspect all theorems and open goals without a resident editor process;
3. decompose a proof into compact, named, replayable transitions;
4. find accessible premises and explain why each is in scope;
5. perform routine simplification and bounded obvious-proof search while
   retaining an explicit proof term and trace;
6. diagnose implicits, instances, rewrites, coercions, and failed refinements;
7. refactor declarations and measure downstream proof impact;
8. package, share, reproduce, and independently check artifacts;
9. use AI, ATP, SMT, or model-finding services as replaceable proposal
   providers rather than semantic authorities; and
10. translate a selected corpus of ordinary Lean developments at the semantic
    level without reproducing Lean's parser, kernel, tactic runtime, or
    declaration-recency behavior.

Evaluation must measure more than “eventually found a proof”:

- held-out proof completion rate;
- checker calls, wall time, and agent token cost;
- proof-term and proof-plan size;
- byte-stable replay under a pinned profile;
- survival under harmless module reorderings and refactors;
- ambiguity and stale-artifact detection;
- dependency-index precision and premise-retrieval recall; and
- independent final Core checking.

## Non-Goals

This plan does not select or authorize:

- a new trusted Core constructor or checker branch for tactics, typeclasses,
  goals, automation, or workflow state;
- extending the retired category-specific root feasibility surface;
- a declaration text parser as the architectural starting point;
- Lean/Coq tactic-language, parser, binary, or API compatibility;
- a general end-user `inductive` declaration frontend, positivity checker, or
  automatic eliminator generator;
- unrestricted TypeScript callbacks retained as canonical tactic state;
- a mandatory LSP, MCP, HTTP, or long-lived prover process;
- an unbounded Prolog engine or monolithic autonomous prover;
- hidden vector search, embeddings, or model output as proof authority;
- promoting every active Lambdapi declaration into an npm standard library;
- treating successful property tests or a missing counterexample as proof;
- one universal philosophical logic or ontology presented as objective truth;
- treating an ordinary completed task as an inhabited mathematical theorem;
  or
- weakening repository, Git, publication, credential, or external-action SOP.

## Proof-Engineering Architecture

### A. General development catalog and command boundary

The fixed proof demo and the exact-root `workspace check` command are useful
qualification fixtures, not a general development product. The next public
semantic layer should combine an existing declaration-workspace plan with a
finite set of proof documents and expose one canonical catalog.

The browser-safe catalog owns no filesystem, hash computation, arbitrary
module loading, or process execution. It should:

- compile a declaration workspace once;
- order proof inputs canonically by `(moduleId, declarationId)`;
- reconstruct and check each theorem against its exact transitive module
  closure through the existing workspace-proof compiler;
- reject duplicate proof identities and absent owner modules before producing
  a catalog;
- expose complete and incomplete theorem status, stable goal IDs, and exact
  closure membership;
- serialize one deterministic portable artifact; and
- permit exact theorem selection without process-local object identity.

In the first revision, proofs are independent leaves over declaration
modules. A theorem cannot silently become a premise of a later theorem. A
later row may make proved theorem exports explicit declaration fragments once
the owner/interface/fingerprint consequences are frozen.

Node-owned acquisition and the CLI come after this semantic boundary. A
future command family may include:

```text
emdash check [module-or-theorem]
emdash goals [module-or-theorem]
emdash build
emdash graph
emdash diff
emdash why
emdash explain
```

Files and deterministic JSON/text are canonical. A server may cache these
operations but never own their meaning.

### B. Declarative proof-plan expansion

The current `exact`, `intro`, `apply`, and `hole` nodes remain the stable
base. Candidate additions are:

```text
refine
have / suffices
let
constructor
cases via an explicit eliminator
induction via an explicit eliminator or recursor
rewrite
change
sequence
focus
bounded first-success
```

Every node must be inert, immutable, serializable data. Its interpreter must
delegate semantic checking to the existing checker/refiner and emit a
deterministic trace. Composition nodes are added only for measured consumers;
there is no generic tactic callback escape hatch.

`cases` and `induction` do not require a general inductive-declaration
frontend. They compile through curated eliminators, recursors, and categorical
or directed HIT interfaces. `constructor` is ordinary application of a
selected constructor handle. A new node name is not authority for new
mathematical computation.

A genuine `refine` node requires an inert expression-template or explicit
placeholder contract. It must not embed session-local metas in source data or
merely rename the existing `apply`. That contract is audited before
implementation.

### C. Stable goal and metavariable coupling graph

Visible goals need more than a flat list. The verified artifact should expose
which named goals occur in the target or context of which other goals. The
public graph uses stable source goal IDs; process-local metavariable ordinals
remain private.

An expected goal snapshot may appear beside source for human/AI readability,
but it is advisory until replay verifies its source, dependency, profile, and
checker fingerprints. Arbitrary TypeScript cannot be statically interpreted
as a dependent proof state. The product therefore preserves the existing
declared-view versus verified-view distinction.

### D. Four separate automation mechanisms

The implementation must keep these mechanisms distinct:

1. kernel runtime computation and reviewed rewrite rules;
2. elaboration and proof-time unification rules;
3. class/dictionary instance synthesis; and
4. proof-level propositional equality rewriting and simplification.

They may share deterministic indexing, matching, budget, and trace utilities,
but they have different trust, termination, and evidence consequences.

The proof-level simplifier should have an explicit versioned profile,
deterministic orientation, conditional-premise handling, congruence rules,
loop/fuel bounds, and a complete trace. It must construct equality/transport
evidence and never silently promote a simplification theorem into kernel
reduction.

### E. Uniform automation-provider protocol

Local search, AI agents, external ATPs, and SMT solvers should share a pure
proposal boundary conceptually shaped as:

```ts
propose({
  goalSnapshot,
  accessiblePremises,
  allowedProfiles,
  budget,
  seed
}): CandidateProofPlanPatch[]
```

A candidate records:

- exact precondition fingerprints;
- the proposed proof-plan patch or explicit term;
- exact dependencies and visibility evidence;
- provider identity and version;
- budget, seed, cost, and complete trace; and
- no hidden mutable session state.

Candidate search is transactional: providers may explore branches, but only a
candidate which replays and checks against current Core becomes an accepted
artifact. CLI, MCP, HTTP, or GetPaidX are transport choices, not semantics.

### F. Premise discovery and semantic index

Premise selection is a first-class proof-assistant feature. The index should
record:

- stable declaration identity;
- exact type and normalized head symbols;
- subterm/operator fingerprints;
- module visibility and imported-interface provenance;
- class, instance, parent, and coercion relationships;
- dependencies and known uses;
- package/version/digest provenance; and
- optional human-facing descriptions.

Embeddings may rank already accessible candidates. They may not establish
visibility, applicability, identity, or correctness. Search results always
resolve to exact declaration IDs and explain the relevant scope path.

### G. Curated standard library

An immediately useful library profile should eventually cover the exact
consumer-selected subset of:

- equality and its eliminators;
- Unit and Empty;
- Pi, Sigma, products, and sums;
- Nat and finite families;
- lists and options where demanded;
- decidability and finite computation;
- algebraic structures/classes;
- category-theoretic foundations; and
- separately reviewed categorical/directed HIT packages.

Activation remains behind the generated-owner and scale/stress decisions in
the existing ledgers. Transfer-qualified fixtures are not silently promoted
to public mathematical authority. Expert hand-written LF/HIT extensions use
an explicit reviewed or unsafe extension profile which states that successful
checking alone does not prove consistency, confluence, normalization, or
semantic justification.

### H. Proof maintenance and counterevidence

Proof engineering should expose:

- semantic diffs and dependency-impact reports;
- stable declaration IDs across source movement;
- rename/module-move/signature-migration assistance;
- old/new goal-fingerprint comparison;
- proof-repair candidates as ordinary reviewed patches;
- `why` traces for implicits, instances, coercions, rewrites, and premise
  accessibility; and
- proof-plan minimization after successful search.

Finite evaluation, property-based testing, and model finding are useful
counterevidence providers. A found counterexample refutes the tested claim
under its exact interpretation. Failure to find one never becomes a proof.

### I. External certificates

External ATP/SMT integration is later and untrusted by default. A result must
either be reconstructed into explicit emdash Core or checked through a
reviewed certificate format and checker. Alethe-like proof objects are a
useful model for the latter. Raw `sat`, `unsat`, or generated prose is never a
Core proof.

### J. AI evaluation protocol

The canonical agent operation is a patch proposal against immutable state:

```text
GoalSnapshot + allowed scope + budget
    -> CandidateProofPlanPatch[]
    -> replay/check
    -> accepted checked artifact or stable diagnostics
```

Natural-language drafts remain non-authoritative. A typed sketch with stable
holes is the bridge between mathematical direction and bounded proof search.
The evaluation corpus should include small translated Lean developments,
emdash-native functorial examples, refactor/replay tests, deliberately
ambiguous searches, and stale-artifact negatives.

## AI-Native Goal Assistant Extension

### Separate semantic plane

The goal assistant reuses proof infrastructure but has its own typed node and
evidence model. Its evaluator derives status from an explicit acceptance
policy; it is not a second truth kernel.

Candidate node kinds are:

```text
TheoremGoal
VerificationGoal
TaskGoal
DecisionGoal
QuestionGoal
ExternalActionGoal
Assumption
Risk
Artifact
```

Candidate edge kinds are:

```text
requires       // AND decomposition
oneOf          // OR alternatives
refines
blocks
discharges
supports
contradicts
produces
authorizedBy
delegatedTo
```

Status is derived from typed decomposition, evidence, policy, and freshness;
it is never a mutable “done” bit.

### Evidence classes

The initial evidence ordering is deliberately non-coercive:

1. kernel-checked explicit emdash proof;
2. deterministic tool verification;
3. signed or externally attributable attestation;
4. observation or experiment;
5. explicit human approval;
6. AI-generated proposal; and
7. unsupported informal assertion.

An evidence item cannot silently move upward. A software deployment task may
be discharged by a deployment receipt plus required human approval. A theorem
is discharged only by its checked proof policy. An external action additionally
requires explicit authorization evidence; a terminal objective never broadens
authority by itself.

### Logic-library profiles

There should be no single universal “goal logic.” Versioned profiles may
cover:

- mathematical proof;
- research planning;
- software verification and release;
- assurance cases;
- decision and risk analysis;
- ontology-backed knowledge workflows; and
- personal or organizational task management.

Each profile declares node kinds, edge meanings, inference rules, evidence
classes, freshness rules, and completion policies. OWL profiles, W3C PROV,
and argument-graph formats may inform interchange adapters. Imported
reasoning remains explicitly labeled with its logic profile unless a checked
translation raises it to emdash proof status.

### Revision, functoriality, and visualization

Goal/evidence state varies over source revisions, contexts, organizations,
and permissions. A revision morphism should reindex stable goal identities,
retain evidence whose fingerprints still match, and expose stale obligations.
A refinement edge maps child obligations into the discharge policy of a
parent. This is genuinely compatible with emdash's functorial orientation,
but the first API should be a transparent typed graph rather than an
over-general categorical facade.

Arrowgram should render the canonical graph; the rendering is a view rather
than authority. GetPaidX/LastRevision may own hosted workspaces, collaboration,
permissions, action execution, and publication. Emdash owns semantic
artifacts, evidence types, profile rules, and checking. Public or in-review
GetPaidX MCP/API contracts remain additive and versioned.

## Work Ledger

| Row | Scope | State | Dependency / exit gate |
| --- | --- | --- | --- |
| `BASELINE-INTEGRATE-0` | Fast-forward the qualified `9c633c8` predecessor into local/public `main` | complete | local and `origin/main` both exactly `9c633c8`; non-force push verified |
| `DEV-CATALOG-1` | General browser-safe multi-module/multi-proof development catalog | complete | focused/package gates green; one long aggregate directly waived after interrupted evidence became unrecoverable |
| `DEV-CLI-2A` | Canonical supplied-data proof-development source and reconstruction | complete | `c60d09e`; focused/static/browser/packed gates green; long aggregate intentionally omitted |
| `DEV-CLI-2B` | Explicit-root Node acquisition and general `check/goals/build` commands | complete | `b5a4cb2`; focused semantic/static/browser gates green; long aggregate intentionally omitted |
| `DEV-CLI-2C` | Stable `graph` command projection | complete | `8e21afb`; focused semantic/static/workspace/shell gates green; no browser/package or long aggregate rerun |
| `PLAN-DECOMPOSE-3A` | Audit inert `refine/have/constructor/rewrite` representation | complete | base-plan macro lowering selected; template and equality boundaries separated below |
| `PLAN-DECOMPOSE-3B` | Implement selected-`constructor` base-plan macro | complete | `934bf13`; focused semantic/static/browser/packed gates green; long aggregate intentionally omitted |
| `PLAN-DECOMPOSE-3B1A` | Audit contextual `have`, retention, and revision boundary | complete | contextual substitution plus per-refiner retained source obligations selected below |
| `PLAN-DECOMPOSE-3B1B` | Implement versioned contextual `have` plan/refiner | complete | `b20595b`; focused semantic/static/research/packed gates green; long aggregate intentionally omitted |
| `PLAN-DECOMPOSE-3C` | Audit versioned explicit-placeholder `refine` representation after contextual `have` | complete | a new tag/refiner is no longer justified; root-scoped templates lower exactly to base plans |
| `PLAN-DECOMPOSE-3C1` | Implement root-scoped explicit-placeholder `refine` macro | complete | `39d9fc8`; focused semantic/static/browser/packed gates green; no source/artifact migration or long aggregate |
| `GOAL-COUPLING-4A` | Audit stable cross-goal dependency semantics and revision boundary | complete | direct target/context dependency graph selected below; proof-state v2 remains unchanged |
| `GOAL-COUPLING-4B` | Implement portable direct cross-goal coupling graph | complete | `de971de`; focused semantic/static/browser/packed gates green; no source/artifact migration or long aggregate |
| `SIMP-5A` | Rewrite/simplifier profile and trace audit | complete | mechanism separation, equality/transport inventory, deterministic trace/budget contract, and staged scope frozen below |
| `SIMP-5B0` | Proof-checker bounded beta/conversion prerequisite | complete | `7c9d8f7`; exact LF environment, beta/delta transport replay, lambda-callee inference still closed; focused/browser/packed/full-TypeScript gates green |
| `SIMP-5B1` | Deterministic unconditional proof-producing simplifier | in progress | green 5B0 proof-document replay boundary; exact v1 API, matching, transport, budget, and rejection contracts frozen below |
| `SIMP-5B2` | Conditional/local/under-binder simplification extensions | deferred | concrete 5B1 consumer plus congruence and premise-discharge contract |
| `INDEX-SEARCH-6` | Accessible-premise semantic index and exact-ID search | pending | general catalog and module-visibility corpus |
| `OBVIOUS-PROOF-7` | Bounded explicit obvious-proof provider | pending | plan patches, index, and budget/trace contract |
| `STDLIB-8` | Curated public library profile | gated | existing generated-owner/stress decisions, exact product profile, public base-package trust boundary |
| `REFACTOR-9` | Semantic diff, dependency impact, and proof repair | pending | stable declaration index and two-revision corpus |
| `COUNTEREVIDENCE-10` | Finite testing/model-finding provider | pending | one executable consumer and explicit evidence labeling |
| `EXTERNAL-CERT-11` | ATP/SMT proposal and certificate adapter | pending | one concrete solver/certificate consumer and independent checker |
| `AGENT-EVAL-12` | Reproducible proof-agent benchmark harness | pending | catalog, plans, index, and at least one bounded provider |
| `PACKAGE-RELEASE-13` | First npm publication and OIDC hardening | external gate | classes-plan `PACKAGE-12B2`; public integrated commit, protected environment, bootstrap credential, verification, trust configuration, cleanup |
| `GOAL-GRAPH-14A` | Typed goal/evidence graph with one research-planning profile | pending | stable proof artifact IDs and explicit acceptance-policy design |
| `GOAL-GRAPH-14B` | Arrowgram view and hosted additive adapters | gated | 14A, published package, sibling SOP audits, compatible controller/runtime |

Only one semantic row is in progress at a time. A later row may be
repartitioned or rejected when evidence contradicts this plan.

## DEV-CATALOG-1 Frozen First Tranche

Hypothesis: the fixed-demo limitation can be removed at the browser-safe
semantic API by composing already qualified workspace and proof-document
owners, without adding filesystem acquisition, hashing, a CLI, a new checker,
or proof-to-proof declaration semantics.

Implementation boundary:

1. Add one browser-safe `lf_proof_development.ts` module.
2. Define a versioned input containing a declaration-workspace plan and a
   finite nonempty list of `CoreLfWorkspaceProofDocumentInput` values.
3. Validate a portable development revision, canonical `(moduleId,
   declarationId)` identities, unique theorem identity, and existing owner
   modules before compiling proofs.
4. Compile the workspace once through `compileCoreLfDeclarationWorkspace`.
5. Canonically order proofs and compile each through
   `compileCoreLfWorkspaceProofDocument`, preserving its exact-closure
   reconstruction and independent checking.
6. Return a deeply frozen portable artifact containing the workspace snapshot
   plus ordered full workspace-proof artifacts, and a process-local result
   which retains the checked workspace and proof compilations.
7. Expose exact proof lookup by `(moduleId, declarationId)` and deterministic
   serialization. Lookup failure returns `undefined`; malformed source fails
   with a stable coded error.
8. Export the module through the contributor v3.2 barrel and the curated
   browser-safe `./workspace` package entry.

Acceptance corpus:

- at least two proofs over a multi-module workspace, including one complete
  and one stable open proof;
- canonical artifact bytes under proof-input permutation;
- exact lookup and stable goal projection;
- duplicate theorem identity rejection;
- absent owner-module rejection;
- deeply frozen arrays/artifacts;
- Node-builtin-free transitive browser closure; and
- packed `@hotdocx/emdash/workspace` availability.

Non-effects:

- no Core/checker/session/refiner semantic change;
- no proof-plan node or artifact revision change;
- no proof-to-proof imports or theorem export into a module interface;
- no runtime/proof-rule fragment widening;
- no filesystem, hashing, network, cache, parser, CLI, MCP, or hosted code;
- no Lambdapi execution or mathematical owner/rule; and
- no npm/GitHub Release mutation.

Rejection conditions:

- the catalog needs ambient mutable state to compile independent proofs;
- input order affects proof artifacts;
- unrelated modules leak into exact proof closures;
- a complete artifact cannot be independently rechecked by existing owners;
  or
- the public package closure acquires a Node builtin.

Proportional gates:

- focused new development-catalog tests;
- nearest existing declaration-workspace, workspace-proof, and proof-plan
  suites;
- browser-closure test;
- workspace check, typecheck, and changed-file lint;
- package build/packed consumer check because `./workspace` changes; and
- one complete `check:ts` because the public barrel/package workspace boundary
  changes, only after the focused tranche is green.

No `check:all`, Lambdapi, kernel, print, book, or sibling-repository aggregate
is required because this tranche adds no cross-layer semantic dependency.

## DEV-CATALOG-1 Completion Record

Date: 2026-08-10

Result: accepted at the frozen boundary.

Checkpoints: frozen architecture `671c56a`; implementation and synchronized
evidence `fcc4547`, pushed to the same-named dedicated remote branch. Public
`main` remains at the separately integrated predecessor `9c633c8`.

Implementation:

- added browser-safe `src/v3_2/lf_proof_development.ts`;
- added the source-visible `emdash-lf-proof-development-v1` profile, with
  independent proof leaves, canonical module/declaration ordering, no Node
  builtin, no I/O or hashing, and no production Lambdapi dependency;
- added inert plan creation with portable revision/identity checks, exact
  owner-module validation, duplicate rejection, and canonical proof order;
- compiled the declaration workspace once, then delegated each independent
  theorem to the existing exact-closure workspace-proof compiler;
- added a deeply frozen portable artifact containing the workspace snapshot,
  ordered workspace-proof artifacts, aggregate status, and open-goal count;
- added process-local exact theorem lookup and a stable aggregate named-goal
  projection without serializing checker sessions or object identity;
- exported the catalog from the contributor v3.2 barrel and the curated
  browser-safe `@hotdocx/emdash/workspace` entry;
- extended the packed ESM, CommonJS, strict NodeNext, and browser consumers;
  and
- added positive, permutation, closure-nonleakage, deep-freeze, malformed,
  duplicate, missing-owner, and Node-free closure tests.

Focused and package evidence:

```text
./scripts/pnpmw run workspace:check
  passed

./scripts/pnpmw run typecheck
  passed

changed-file ESLint and complete `eslint src tests`
  passed

node --require ts-node/register --test \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_lf_workspace_tests.ts \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_browser_directed_tests.ts
  36 tests / 5 suites: 36 passed, 0 failed

./scripts/pnpmw run package:check
  passed: build plus packed ESM/CommonJS/strict NodeNext/browser consumers

git diff --check
  passed before ledger synchronization
```

Aggregate disposition: the one attempted `check:ts` visibly passed workspace,
typecheck, and full lint before entering the root test runner. After about 26
minutes of CPU-active testing, an unexpected tool/session interruption made
its eventual output and exit status unrecoverable. It is not counted as green.
A replacement root-test run was started, then intentionally terminated after
114 seconds when the user directly requested that this particular long
aggregate be avoided. That termination is a validation waiver, not a test
failure and not positive aggregate evidence. Under direct instruction, the
focused semantic matrix, full static checks, browser closure, and packed
consumer are the final proportional evidence for this tranche. The preceding
1,570-test classes aggregate remains historical baseline evidence only; it is
not misreported as checking this new source.

No Core/checker/session/refiner semantics, proof-plan/artifact revision,
Lambdapi source, mathematical owner/rule, parser, Node acquisition, CLI,
network/cache, print/book, sibling repository, npm registry, GitHub Release,
or hosted deployment changed. At that checkpoint `DEV-CLI-2` was nominally
next; the subsequent audit repartitioned it below and selected the now
completed `DEV-CLI-2A` row.

## DEV-CLI-2 Acquisition Audit And Frozen 2A Tranche

Date: 2026-08-10

Status: architecture audit complete; `DEV-CLI-2` repartitioned;
`DEV-CLI-2A` frozen and approved for implementation by the user's direct
continuation instruction and standing unattended-approval authorization.

The audit found two distinct existing source paths:

1. `ai_proof_cli.ts` imports and checks one fixed TypeScript demo. Reading its
   own source bytes contributes a fingerprint, but the command does not
   acquire an arbitrary proof development.
2. `lf_remote_workspace_*` safely reads exact locked files under explicit
   project/data roots and reconstructs a canonical fragment-module graph.
   That graph is intentionally a different semantic profile from the
   declaration-workspace plus proof-plan input consumed by
   `DEV-CATALOG-1`.

There is no current canonical file consumer for
`CoreLfProofDevelopmentPlan`, no general `*.emdash.ts` loader, and no
repository sandbox which would make importing an arbitrary host-language
module safe. Same-process dynamic import would grant filesystem, network,
environment, subprocess, clock, randomness, and ambient-package authority.
A child process changes isolation and cancellation properties but does not by
itself make hostile TypeScript trustworthy. The proof CLI must therefore not
silently execute a user path and call the result checked source.

The architecture separates three claims:

```text
reviewable *.emdash.ts builders       optional, explicitly authorized macro run
                |                                      |
                +---------- emits portable data -------+
                                       |
                              exact canonical source
                                       |
                    constructor replay + shape validation
                                       |
                         CoreLfProofDevelopmentPlan
                                       |
                         existing catalog/compiler
```

Only the reconstructed portable plan and its subsequent checker replay are
semantic inputs. Host execution remains an acquisition effect outside the
checker trust boundary. A future restricted TypeScript runner may improve the
authoring workflow, but it needs an independently reviewed isolation model;
it is not a prerequisite for checking already materialized canonical data.

### DEV-CLI-2A implementation boundary

Hypothesis: the missing exact catalog consumer can be added as a browser-safe
canonical-data contract without filesystem access, hashing, host execution,
new checker rules, or a user-language declaration/term parser.

1. Add a dedicated browser-safe proof-development source module rather than
   coupling Node policy to `lf_proof_development.ts`.
2. Define a versioned source snapshot containing the development revision,
   declaration-workspace revision, canonical declaration-module source
   snapshots, and canonically ordered proof inputs.
3. Serialize through the existing canonical workspace JSON owner. JSON is a
   portable envelope for explicit Core data, not a textual emdash
   declaration or expression grammar.
4. Parse only JSON whose bytes equal the canonical serialization of a fully
   reconstructed snapshot.
5. Reconstruct explicit Core expressions and proof-plan nodes by a closed
   tag dispatch. Reject unknown/missing fields, process-local Core metas,
   invalid provenance, invalid binders/arguments, cycles, and unsupported
   plan nodes. Never cast an arbitrary nested record directly into proof
   authority.
6. Re-run the existing module, transfer-policy, declaration-linkage,
   declaration-workspace, proof-fingerprint, proof-plan, and development
   constructors/validators. Do not duplicate their mathematical decisions.
7. Return a deeply frozen source snapshot, canonical text, and inert
   `CoreLfProofDevelopmentPlan`. Checking remains an explicit later call to
   `compileCoreLfProofDevelopment`.
8. Export the contract from the contributor v3.2 barrel and the existing
   browser-safe `@hotdocx/emdash/workspace` entry. Add no Node builtin to its
   transitive closure.

Acceptance corpus:

- a multi-module development with one complete and one named-open proof
  round-trips byte-identically and compiles to the same artifact;
- canonical bytes are independent of source module/proof input permutation;
- parsed data and arrays are deeply frozen;
- malformed JSON, noncanonical whitespace/key order, extra or missing fields,
  unknown expression/plan tags, a serialized Core meta, malformed source
  provenance, and invalid fingerprints fail with stable acquisition errors;
- existing catalog, workspace-proof, proof-plan, and browser-closure tests
  remain green; and
- the packed ESM, CommonJS, strict NodeNext, and browser consumers can use the
  new source contract.

Non-effects:

- no arbitrary TypeScript/JavaScript execution or dynamic import;
- no filesystem, path discovery, symlink policy, hashing, cache, transport,
  CLI, MCP/LSP, or server state;
- no new Core node, checker/refiner behavior, proof-plan node, theorem import,
  declaration parser, term parser, Lambdapi dependency, or mathematical rule;
  and
- no `graph` artifact before `GOAL-COUPLING-4` defines its stable meaning.

Proportional gates are focused source-contract/catalog/workspace-proof/plan
tests, workspace check, typecheck, changed-file lint, the Node-free browser
closure assertion, packed-package consumers, exact diff review, and
whitespace hygiene. Under the user's persistent 2026-08-10 instruction, no
long aggregate is run unless omitting that exact aggregate would block
overall progress; omission is recorded and is never presented as a pass.

## DEV-CLI-2A Completion Record

Date: 2026-08-10

Result: accepted at the frozen boundary.

Checkpoints: architecture `ee31ab9`; implementation `c60d09e`; this
completion record is a separate descendant documentation checkpoint.

Implementation:

- added browser-safe `src/v3_2/lf_proof_development_source.ts` with the
  source-visible `emdash-lf-proof-development-source-v1` profile;
- separated exact canonical explicit-Core data from host-language execution,
  declaration/term syntax, filesystem acquisition, hashing, and commands;
- projected direct constructor output to portable plain data while omitting
  only absent optional record fields and rejecting functions, symbols,
  cycles, class instances, accessors, hidden fields, sparse arrays, extra
  array properties, and non-finite numbers;
- decoded provenance, binder modes, every current meta-free explicit-Core
  expression tag, and every current inert proof-plan tag by closed dispatch;
- rejected process-local metas, unsupported tags, malformed fields,
  noncanonical source objects/bytes, and dangling Core variables before a
  source reconstruction can be returned;
- reran existing module, transfer-policy, declaration-linkage,
  declaration-workspace, proof-fingerprint, proof-plan, and development
  constructors/validators rather than duplicating their semantic ownership;
- returned a deeply frozen source snapshot, inert development plan, and exact
  canonical source text; checker replay remains the separate
  `compileCoreLfProofDevelopment` call;
- exported the contract from the contributor v3.2 barrel and the browser-safe
  `@hotdocx/emdash/workspace` package entry, documented that boundary, and
  extended packed ESM/CommonJS/strict NodeNext/browser consumers; and
- added positive round-trip, permutation, checked-artifact equivalence,
  deep-freeze, malformed JSON, noncanonical bytes/data, extra/missing field,
  accessor non-execution, sparse array, unknown plan/expression tag,
  dangling-bound, serialized/direct-meta, provenance, fingerprint, and
  Node-free transitive-closure coverage.

Focused evidence:

```text
./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

./scripts/pnpmw run typecheck
  passed

changed-file ESLint
  passed

node --require ts-node/register --test \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_lf_workspace_tests.ts \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_browser_directed_tests.ts
  40 tests / 6 suites: 40 passed, 0 failed

./scripts/pnpmw run package:check
  passed: build plus packed ESM/CommonJS/strict NodeNext/browser consumers

git diff --cached --check
  passed before semantic checkpoint c60d09e
```

Aggregate disposition: no `check:ts`, root-test, or `check:all` aggregate was
run. Its omission does not block this row because the exact semantic,
transitive-browser, type, lint, workspace, and packed public-consumer
boundaries are directly green. This is an intentional omission under
`D-PA-019`, not a pass and not evidence about unrelated suites.

No Core/checker/session/refiner semantics, proof-plan/artifact revision,
mathematical owner/rule, theorem import, filesystem/path policy, hashing,
cache, network, dynamic import, CLI, MCP/LSP, Lambdapi source, kernel,
print/book, sibling repository, npm registry, GitHub Release, or hosted
deployment changed. `DEV-CLI-2B` is the next nominal row, subject to a frozen
fixed-file/explicit-root/size/symlink/output contract. `PLAN-DECOMPOSE-3A`
remains dependency-ready as a semantic alternative after this completed
catalog consumer.

## DEV-CLI-2B Audit And Frozen Command Tranche

Date: 2026-08-10

Status: existing mounted-store and command compatibility audit complete;
contract frozen and approved for implementation by direct continuation and
the standing bounded self-approval authorization.

The audit confirms that `lf_remote_workspace_store.ts` already demonstrates
the required POSIX mounted-file discipline—canonical absolute real roots,
fixed child names, `O_NOFOLLOW`, regular-file checks before reading, byte
bounds, and exact UTF-8—but its lock/cache/error model belongs to the distinct
remote fragment-workspace profile. `ai_proof_cli.ts` must also remain the
byte-compatible fixed demo behind legacy `./scripts/emdash check|goals`.
Therefore `DEV-CLI-2B` adds a separate read-only proof-development adapter and
an exact shell namespace rather than widening either owner.

### Fixed source acquisition

1. Add a Node-only mounted proof-development store with fixed filename
   `emdash.proof-development.source.json` and a 64 MiB maximum.
2. Its sole input is `{ projectRoot }`. The root must be a normalized absolute
   existing real directory whose `realpath` is byte-identical, so symbolic
   root components are rejected. There is no current-directory, environment,
   `HOME`, upward-search, manifest-search, URL, arbitrary source-path, or data
   root default.
3. Open only the fixed direct child with `O_RDONLY | O_NOFOLLOW |
   O_NONBLOCK`; require a regular file; check the stat size and bytes actually
   read; and require an exact UTF-8 round trip.
4. Parse through `parseCoreLfProofDevelopmentSourceText`, then compute a
   `sha256:` digest of those exact canonical bytes. Hashing is acquisition
   evidence and does not replace proof fingerprints or checker replay.
5. Return a frozen process-local result containing canonical root/source
   paths, byte count, digest, source text, and the pure reconstruction. Paths
   and source text never enter public command output.
6. This row performs no writes, cache mutation, transport, credential read,
   dynamic import, TypeScript execution, Git operation, Lambdapi invocation,
   or backend selection.

### Command contract

The additive command family is:

```text
./scripts/emdash development <check|goals|build> \
  --project-root ABSOLUTE_PATH \
  [--module MODULE_ID --declaration DECLARATION_ID] \
  [--format jsonl|text]
```

1. The shell wrapper recognizes only an exact leading `development`, removes
   it, and execs a separate thin launcher. Existing exact `capabilities` and
   `workspace` namespaces and every legacy fixed-demo argument vector remain
   unchanged.
2. `--project-root` is mandatory. Module and declaration selection are
   optional but must occur together. Options accept `--name value` and
   `--name=value`; duplicates, missing values, positional targets, unknown
   flags/commands/formats, absent proofs, and partial selectors fail closed.
3. Every invocation parses canonical source and freshly calls
   `compileCoreLfProofDevelopment`; there is no retained checker session,
   daemon, registry, source callback, filesystem injection hook, or MCP/LSP
   authority.
4. Without a selector the scope is the complete development. With a selector
   it is the exact `(moduleId, declarationId)` proof already checked as part
   of that development. Selection never changes visibility or compilation.
5. Default JSONL for `check` emits one deterministic path-free summary record.
   `goals` emits that summary followed by zero or more ordered goal records.
   `build` emits one deterministic record containing the selected full
   portable proof/development artifact. Every record includes the backend,
   exact acquisition-source digest, development revision, scope, status, and
   appropriate stable IDs/counts; none includes an absolute path, source text,
   timestamp, process ID, environment value, credential, session identity, or
   process-local checked object.
6. `--format text` is a compact human projection: summary plus formatted
   named goals when requested. For `build` it confirms the verified build
   summary; full portable artifact emission is the JSONL form. Formatting
   never triggers a second compilation.
7. Complete `check`/`build` and every successful `goals` inspection exit zero.
   Incomplete `check`/`build` emit their selected report, write one concise
   incomplete diagnostic to stderr, and exit one. Parse, acquisition,
   selection, or checking failure emits no stdout, writes
   `emdash: <message>` to stderr, and exits two.
8. The launcher owns only argv and exit-code plumbing. The reusable async CLI
   accepts stdout/stderr sinks for deterministic tests but no semantic or
   acquisition-operation replacement.

### Acceptance and non-effects

Focused coverage must include complete/incomplete whole-development check,
goal inspection, exact proof selection, full build artifact, text projection,
parser failures, missing/oversized/non-UTF-8/symlink/non-regular source,
relative/symbolic roots, source validation failure, output privacy, actual
shell routing, and unchanged legacy proof/workspace/capability routes.

The tranche may add a direct-TypeScript multi-proof demo plus a stdout-only
materializer example to make the authoring-to-canonical-data handoff concrete.
That example is explicitly executed macro code, not silently trusted checker
input.

No public npm entry, browser barrel, dependency/lockfile, Core/checker/
refiner/proof-plan semantics, source profile, mathematical rule, cache,
network, host sandbox claim, Lambdapi source, kernel, print/book, sibling
repository, npm registry, release, or deployment changes. Proportional gates
are the new store/CLI tests, nearest legacy CLI/source/catalog tests, actual
shell smoke and `sh -n`, workspace check, typecheck, changed-file lint,
forbidden-effect/output scans, exact diff review, and whitespace hygiene. No
long aggregate runs unless its omission becomes progress-blocking under
`D-PA-019`.

## DEV-CLI-2B Completion Record

Date: 2026-08-10

Result: accepted at the frozen boundary.

Checkpoints: architecture `a6f0fbe`; implementation `b5a4cb2`; this
completion record is a separate descendant documentation checkpoint.

Implementation:

- added Node-only `src/v3_2/lf_proof_development_store.ts` with the
  source-visible `emdash-lf-mounted-proof-development-v1` profile;
- accepted only one plain `{ projectRoot }` data record, rejected accessors
  without invoking them, required a normalized absolute real directory, and
  opened only its fixed `emdash.proof-development.source.json` child;
- required `O_RDONLY | O_NOFOLLOW | O_NONBLOCK`, a regular file, a 64 MiB
  stat and actual-byte ceiling, bounded chunked reads, and exact UTF-8 before
  canonical source reconstruction and SHA-256 acquisition evidence;
- added stateless `development check|goals|build` commands with an exact
  paired module/declaration selector, strict option parsing, fresh whole-
  development checking, stable JSONL/text projections, and distinct
  complete, incomplete, and command/error exit statuses;
- kept absolute paths, source text, timestamps, process identity, checked
  objects, credentials, and environment values out of command records;
- added a pure direct-TypeScript two-proof demo, an explicit stdout-only
  canonical-data materializer, a thin process launcher, and exact additive
  shell dispatch while preserving legacy proof, workspace, and capability
  command vectors;
- revised the source-visible capability record to v2, replacing the now-
  completed general-source/command deferrals with the narrower optional
  host-execution and stable graph gates; and
- documented the authoring-to-data-to-checking handoff and added positive,
  incomplete, selection, build, text, malformed-option, path/privacy,
  accessor, symlink, non-file, size, UTF-8, canonical-source, shell-routing,
  legacy-compatibility, and materializer coverage.

Focused evidence:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_development_cli_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_lf_remote_workspace_tests.ts
  53 tests / 11 suites: 53 passed, 0 failed

node --require ts-node/register --test \
  tests/v3_2_browser_api_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts
  17 tests / 4 suites: 17 passed, 0 failed

./scripts/pnpmw run typecheck
  passed

changed-file ESLint
  passed

./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

sh -n scripts/emdash
  passed

forbidden-effect and command-output scans
  passed

git diff --cached --check
  passed before semantic checkpoint b5a4cb2
```

Aggregate disposition: no `check:ts`, root-test, `check:all`, package, kernel,
print, or book aggregate was run. No public npm entry, curated browser barrel,
package metadata, dependency, or package consumer changed, so package
repacking was not an affected boundary. The exact Node acquisition, command,
legacy compatibility, source/catalog/workspace, browser API, type, lint,
workspace, shell, effect, output, and whitespace boundaries are directly
green. Under `D-PA-019`, omitting a long aggregate does not block this row;
the omission is intentional, is not a pass, and provides no evidence about
unrelated suites.

No Core/checker/session/refiner behavior, proof-plan or source revision,
mathematical owner/rule, theorem import, declaration or term parser, cache,
network, dynamic host import, MCP/LSP, Lambdapi source, kernel, print/book,
sibling repository, npm registry, GitHub Release, or hosted deployment
changed. `DEV-CLI-2C` remains gated on `GOAL-COUPLING-4` so the command layer
does not invent a second graph authority. `PLAN-DECOMPOSE-3A` is the next
dependency-ready row.

## PLAN-DECOMPOSE-3A Audit And Frozen 3B Macro Tranche

Date: 2026-08-10

Status: audit complete; `PLAN-DECOMPOSE-3B` frozen and approved for
implementation under the direct continuation instruction and standing
bounded self-approval authorization.

### Material findings

1. The current inert tree already has the correct semantic base: `exact`,
   `intro`, `apply`, and stable `hole`. Validation rejects every source-level
   Core meta, execution creates session metas only behind the refiner, and the
   canonical development decoder uses closed tag dispatch.
2. `CoreProofRefiner.apply` infers a selected term, traverses its complete Pi
   telescope, creates ordered contextual subgoals, and checks the resulting
   call against the current target. A selected data constructor therefore
   needs no special proof rule: `constructor c` is precisely `apply c` with a
   clearer direct-TypeScript authoring name.
3. The initial audit hypothesis was that a local `have h : T` could also be
   expressed without a new plan tag. For an explicitly recorded current
   target `G`, the proposed meta-free cut term was

   ```text
   cut(T,G) = λ witness : T,
                λ continue : (Π h : T, G),
                  continue witness

   have h : T := proof; body
     ↦ apply cut(T,G) [proof, intro h body]
   ```

   A focused implementation probe rejected this hypothesis before semantic
   checkpointing. The frozen `CoreChecker` deliberately returns
   `CANNOT_INFER_LAMBDA` when `apply` tries to infer that lambda callee;
   annotated-lambda inference exists only in the separate candidate LF
   checker. Enabling it globally or manufacturing a hidden cut declaration
   would widen an unrelated trusted boundary. A real `have` therefore needs
   an explicit inert node plus a generic contextual refiner operation that
   creates the fact and continuation goals without serializing their session
   metas. Its nested profile/artifact revisions and treatment of an unused
   open fact must be frozen in `PLAN-DECOMPOSE-3B1`.
4. Lean's implementation confirms why general `refine` is materially
   different: it elaborates a term containing holes, assigns the old goal to
   that term, and promotes the newly reachable holes to goals. Emdash source
   cannot copy that process representation because its metas carry session
   identity. A genuine emdash `refine` therefore needs a closed, versioned
   expression-template AST with explicit placeholder identities, scopes,
   ordering, and types, plus a source/artifact compatibility decision. It is
   not approved as an alias for `apply`.
5. Propositional `rewrite` is likewise not definitional reduction. Equality,
   reflexivity, eliminators, and transport are generic imported LF
   declarations in the current TypeScript backend rather than built-in Core
   owners. A sound rewrite node must select an equality profile, occurrence
   policy, direction, transport constructor, proof-producing trace, and
   dependent-target behavior. That work belongs to `SIMP-5A/5B`; this tranche
   must not interfere with active Lambdapi mathematics or disguise a runtime
   rewrite as a theorem proof.

### Corrected frozen PLAN-DECOMPOSE-3B contract

Add one browser-safe, source-visible authoring macro in the existing
`proof_plan` package boundary:

```text
coreProofPlanConstructor(callee, premises, options?)
  -> CoreProofPlanApply
```

1. Publish an immutable `emdash-proof-plan-macros-v1` capability profile.
2. `constructor` delegates exactly to `coreProofPlanApply`; the caller selects
   the constructor handle and supplies all ordered premise plans. Automatic
   constructor search is a later index/provider feature.
3. The generated root uses the caller's optional ID/provenance; no callback,
   registry, session, meta, goal lookup, environment lookup, filesystem,
   process state, or backend selection is retained.
4. Output is an ordinary deeply inspectable base-plan tree. Canonical source,
   proof-state, artifact, JSONL, and CLI revisions do not change; serialized
   plans contain only the existing `apply`, `intro`, `exact`, and `hole` tags,
   and traces report those actual primitives.
5. Failures remain ordinary validation/checking failures. An ill-scoped or
   meta-bearing callee, wrong constructor, or premise mismatch must fail
   through current owners rather than a parallel macro checker.

Focused acceptance covers constructor parity with direct `apply`, complete
and named-open constructor premises, wrong-constructor and arity rejection,
base-tag-only serialization, exact canonical source round-trip, browser
closure, and the packed workspace consumer. Run the focused proof-plan/source/
workspace suites, workspace check, typecheck, changed-file lint, browser
closure, package build/packed consumers, exact diff review, and whitespace
hygiene. Under `D-PA-019`, no long root or repository aggregate is run unless
omitting it becomes progress-blocking.

Non-effects: no new Core expression, proof-plan tag, refiner/checker/session
method, proof/source/artifact revision, declaration or term parser,
constructor discovery, equality/rewrite semantics, theorem import, Lambdapi
source, mathematical owner/rule, Node adapter, CLI, cache/network, MCP/LSP,
print/book, sibling repository, release, registry, or deployment change.
At this boundary, `PLAN-DECOMPOSE-3B1` retained contextual `have`,
`PLAN-DECOMPOSE-3C` retained general explicit-placeholder refinement, and
`SIMP-5A/5B` retained propositional rewriting. Their later audit outcomes are
recorded below.

### PLAN-DECOMPOSE-3B completion record

Semantic checkpoint: `934bf13` (`feat: add selected constructor proof plans`).

The public browser-safe workspace entry now exports
`coreProofPlanConstructor` and immutable
`emdash-proof-plan-macros-v1`. The macro accepts an explicitly selected Core
callee and ordered premise plans, then returns exactly the existing frozen
`apply` node. Complete execution and traces therefore remain checked by the
ordinary refiner, named dependent premises remain ordinary source holes, and
wrong constructors or arities fail atomically through existing owners. The
static AI-native capability record advances from v2 to v3 solely to advertise
the implemented profile. Canonical proof-development source remains v1 and
round-trips the lowered `apply` tree; there is no serialized `constructor`
tag or hidden selection search.

Final proportional evidence:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts \
  tests/v3_2_lf_workspace_proof_tests.ts
  35 tests / 7 suites: 35 passed, 0 failed

node --require ts-node/register --test \
  tests/v3_2_browser_api_tests.ts
  2 tests / 1 suite: 2 passed, 0 failed

./scripts/pnpmw run typecheck
  passed

changed-file ESLint
  passed

./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

./scripts/pnpmw run package:check
  package build plus packed ESM, CJS, strict-TypeScript, and browser
  consumers passed

git diff --cached --check
  passed before semantic checkpoint 934bf13
```

Aggregate disposition: no `check:ts`, root-test, `check:all`, kernel,
Lambdapi, print, book, or publication aggregate was run. The affected proof-
plan, capability, canonical-source, browser, and public-package boundaries are
directly green. Under `D-PA-019`, omission of the long aggregates does not
block this bounded row; it is intentional, is not a pass, and says nothing
about unrelated suites.

No Core expression or proof-plan tag, checker/refiner/session rule,
proof-state/document/artifact/source revision, declaration or term parser,
constructor discovery, theorem import, equality/rewrite behavior, Lambdapi
source, mathematical owner/rule, Node adapter, CLI, cache/network, MCP/LSP,
print/book, sibling repository, npm registry, GitHub Release, or hosted
deployment changed. The rejected lambda-cut `have` probe was never
checkpointed. `PLAN-DECOMPOSE-3B1A` is the next contract audit.

## PLAN-DECOMPOSE-3B1A Contextual Have Audit And Frozen 3B1B Tranche

Date: 2026-08-10

Status: audit complete; `PLAN-DECOMPOSE-3B1B` frozen and approved for bounded
implementation under the standing self-approval and checkpoint policy.

### Material findings

1. A generic `have` does not require inferred lambdas, a hidden cut theorem,
   or a new Core expression. For a goal `Γ ⊢ G` and source binder `h : T`, a
   refiner can allocate contextual session metas

   ```text
   Γ       ⊢ ?fact : T
   Γ, h:T  ⊢ ?body : shift(G, 1)

   Γ ⊢ ?body[?fact/h] : G
   ```

   and solve the old goal with the final contextual occurrence. The existing
   meta-spine substitution, scope checker, and final fresh proof-document
   recheck remain authoritative. When both subplans close, zonking produces
   ordinary explicit Core with no source or artifact meta.
2. Term reachability alone is insufficient for source obligations. If the
   continuation solves `?body` with a term that ignores `h`, substitution can
   erase an unsolved `?fact`. The theorem term may no longer need that fact,
   but the explicit source plan still asked the agent to prove it. Silently
   dropping that hole would violate the existing rule that plan execution
   cannot ignore or invent an obligation.
3. The smallest honest correction is a per-`CoreProofRefiner` ordered retained-
   obligation set. `have` registers the fact goal; inspection reports every
   unsolved registered fact before other root-reachable goals and marks a
   detached goal `retained-source-obligation` with occurrence count zero.
   Solving the meta removes it from reported state automatically. The set is
   session-local, transaction-aware, recreated by deterministic source replay,
   absent from source/artifacts, and never becomes a hidden prover service or
   global registry.
4. Source execution visits the fact subplan before the continuation subplan.
   This keeps source goal order stable and allows the fact to be refined while
   it is still term-reachable. Even if later continuation refinement erases
   its occurrence, the refiner retains it until solved. A replay with a patched
   fact starts from a fresh session and reconstructs the same obligations.
5. This is a real serialized-language and diagnostic change: `have` is a new
   inert plan tag, trace operation, and goal reachability value. Reusing v1
   revision strings would make exhaustive consumers silently stale. The npm
   package has not yet been published and there are no tracked canonical v1
   proof-development files, so this tranche performs one coordinated
   pre-release v2 migration rather than carrying a dual reader with no actual
   external consumer.

### Frozen PLAN-DECOMPOSE-3B1B contract

Add the inert browser-safe node and direct authoring constructor:

```text
have(binding, proof, body)

coreProofPlanHave(binding, proof, body, options?)
  -> CoreProofPlanHave
```

1. `binding` is an explicit `KernelBinder`; exact plicity and
   functorial/natural/object-only variation are preserved. Its type and both
   child plans must be meta-free, scoped, portable data. No callback,
   environment lookup, declaration search, or implicit instance search is
   retained.
2. `CoreProofRefiner.have` checks `T : TYPE` in the selected goal context,
   creates the fact and weakened continuation metas, solves the old goal by
   contextual spine instantiation, registers the fact as a retained source
   obligation, and returns `[fact, body]` in source order. All mutation is
   failure-atomic, including retention metadata.
3. `CoreProofRefiner.inspect` continues to derive ordinary goals from the
   root term, then prepends unsolved retained obligations without duplicates.
   Every goal exposes `reachability` as `term-reachable` or
   `retained-source-obligation`; only the latter may have occurrence count
   zero. A solved retained meta is never reported.
4. Plan execution records one `have` trace step, maps its two exact child
   goals, executes proof before body, and requires stable hole IDs as before.
   A complete execution is freshly rechecked by `CoreChecker`; an unresolved
   retained fact makes the plan and every enclosing artifact incomplete even
   when the current term no longer mentions it.
5. Canonical source uses closed tag dispatch for `have`, reconstructs its
   binder through existing explicit Core decoders, and rejects old/malformed,
   extra-field, meta-bearing, cyclic, or noncanonical data. There is no
   declaration text parser and no serialized session identity.
6. Advance the directly affected profile family coherently:

   | Boundary | New revision family |
   | --- | --- |
   | proof plan | `emdash-proof-plan-v2` |
   | proof document/compiler/state/artifact/JSONL | v2 |
   | exact-closure workspace proof/compiler/artifact | v2 |
   | proof development/artifact/source | v2 |
   | mounted proof development | v2 with an explicit source-profile pin |
   | development CLI summary/goal/build | v2 |
   | research-document binding/snapshot | v2 |
   | pinned research overview browser/files management | v2 with recomputed deterministic pins |
   | AI-native capability record | v4 |

   The declaration-workspace/module/runtime profiles, Core serialization,
   constructor macro profile, and mathematical ownership revisions do not
   change. Package version remains `0.1.0`; publication is still separately
   gated.

Focused acceptance covers direct-refiner complete and open cases, a
continuation that both uses and ignores `h`, retained-goal ordering and zero-
occurrence reporting, dependent outer contexts, every binder variation,
transaction rollback, plan preflight, canonical source round-trip and stale-v1
rejection, complete/incomplete artifact recheck, exact-closure/development/CLI
projection, research-pin parity, browser closure, and packed ESM/CJS/strict-
TypeScript/browser consumers. Run the affected focused suites, typecheck,
changed-file lint, workspace check, package check, exact diff review, and
whitespace hygiene. Under `D-PA-019`, do not run a long root or repository
aggregate unless omitting it becomes progress-blocking.

Non-effects: no new Core expression or checker rule, lambda-inference change,
cut axiom, hidden declaration, theorem import, equality/rewrite behavior,
constructor search, term/declaration parser, arbitrary host execution,
filesystem policy expansion, network/cache/MCP/LSP, Lambdapi source,
mathematical owner/rule, print/book, sibling repository, npm publication,
GitHub Release, or hosted deployment change. At this boundary, general
placeholder `refine` remained reserved for `PLAN-DECOMPOSE-3C`;
propositional rewrite remains `SIMP-5A/5B`.

### PLAN-DECOMPOSE-3B1 completion record

Semantic checkpoint: `b20595b` (`feat: add contextual have proof plans`).

The browser-safe workspace API now exports immutable
`emdash-proof-plan-v2` and `coreProofPlanHave(binding, proof, body)`. The
refiner checks the fact type, creates fact and continuation metas in their
exact contexts, and solves the selected goal by contextual meta-spine
substitution. A per-refiner ordered retention map keeps an unused open fact
visible as `retained-source-obligation` with zero occurrences; used facts and
all completed plans zonk to ordinary meta-free Core and pass a fresh checker
recheck. Fact-before-body execution, dependent outer contexts, explicit and
implicit plicity, all three binder variations, and failure atomicity are
covered directly.

Canonical proof-development data reconstructs the closed `have` tag and its
explicit binder without host execution or term/declaration parsing. A stale
v1 source envelope is rejected. Proof state, proof documents and artifacts,
exact-closure workspace proofs, development catalogs and source, mounted-file
and CLI projections, research bindings and release pins, and the static
capability record advance together to the v2/v4 families frozen above. The
mounted store and CLI now expose their exact lower-profile pins. The unchanged
selected-constructor macro remains `emdash-proof-plan-macros-v1`.

Final proportional evidence on 2026-08-10:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_state_tests.ts \
  tests/v3_2_proof_refinement_tests.ts \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_proof_document_tests.ts \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_proof_development_cli_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts
  passed: 74/74 tests, 12 suites

./scripts/pnpmw run typecheck
  passed

eslint over every changed TypeScript/JavaScript file
  passed

./scripts/pnpmw run workspace:check
  passed: pnpm@11.16.0; Node 24.11.1

./scripts/pnpmw run package:check
  passed: package build plus packed ESM, CJS, strict-TypeScript, and browser
  bundle consumers
```

The separate `emdash-template` wrapper could not bootstrap its standalone
dependencies because this worktree has no fixture-local `node_modules` and
the Corepack-launched pnpm process could not self-spawn `pnpm`; direct
TypeScript/Vite probes consequently found the same missing dependencies. A
broader reviewer test was stopped after 70 seconds under `D-PA-019` and is not
reported as green evidence. Browser-safe research replay and parity are in
the 74 focused tests, while the actual packed browser bundle is in
`package:check`. No long root/repository aggregate, Lambdapi/kernel, print,
book, npm publication, release, deployment, or sibling-repository operation
was run.

## PLAN-DECOMPOSE-3C Audit And Frozen 3C1 Macro Tranche

Date: 2026-08-10

Status: `PLAN-DECOMPOSE-3C` audit complete; `PLAN-DECOMPOSE-3C1` frozen and
approved for bounded implementation under the standing self-approval and
checkpoint policy.

### Material findings

1. Lean's `refine` elaborates syntax with fresh process-local metavariables,
   assigns the main goal to the resulting term, and promotes the new metas to
   goals. That is appropriate inside Lean's resident elaborator state, but it
   is not a serializable emdash source contract: emdash metas deliberately
   carry an opaque session identity and cannot appear in inert plans.
2. Before contextual `have`, an arbitrary expression skeleton appeared to
   require a new plan tag and refiner operation. `PLAN-DECOMPOSE-3B1B` removes
   that necessity for placeholders declared in the selected goal context. For
   bindings `h₁:T₁, ..., hₙ:Tₙ` and a meta-free Core-shaped template `E`, the
   pure source expansion is

   ```text
   have h₁ : T₁ := proof₁
   ...
   have hₙ : Tₙ := proofₙ
   exact E[h₁, ..., hₙ]
   ```

   Existing contextual substitution, retained-obligation reporting, and
   final checker replay provide all semantics. A new `refine` plan tag would
   merely duplicate those owners and force an unnecessary immediate v3
   source/artifact migration.
3. The useful authoring input is still not a host callback or a Core term with
   fake names. It is a small immutable template AST with `core`, `placeholder`,
   `application`, `call`, `pi`, and `lambda` nodes. `core` wraps an ordinary
   meta-free Core subtree; `placeholder` refers to one explicitly declared
   term binding. Structural expression children may contain placeholders,
   including bodies beneath Pi/lambda binders; binder annotations remain
   ordinary meta-free Core.
4. Placeholder bindings are unique, explicitly ordered, and formed in the
   selected goal context. Their types therefore cannot depend on binders
   introduced inside the same template. Occurrences may appear repeatedly and
   beneath template binders: lowering weakens root-context variables and maps
   every repeated occurrence to the same nested-`have` bound variable. A hole
   that genuinely depends on a newly introduced binder is authored by
   composing `intro` and a nested refine macro at that goal, keeping scope
   visible rather than encoding path-dependent hidden context.
5. Explicit binding order is source goal order. Every binding must be used at
   least once, every placeholder reference must resolve, all identifiers and
   binder modes must be portable, and template/binding/proof data must be
   finite, acyclic, and meta-free. Expansion returns an ordinary inspectable
   plan immediately; it retains no template, callback, session, environment,
   registry, or runtime goal handle.
6. The representative ergonomic consumer is a higher-order skeleton whose
   callee is a typed placeholder and whose argument is fixed Core, with a
   second case sharing one placeholder at multiple positions. These would be
   verbose manual `have` programs but need no new semantics. Complete and open
   variants must replay identically to their direct base-plan expansion.
7. A focused type-position probe establishes a necessary v1 limit. Binding a
   type placeholder would require `have A : TYPE`, while contextual `have`
   deliberately checks its declared type against `TYPE` and the frozen sort
   discipline gives `TYPE : KIND`. Template binder annotations therefore do
   not contain placeholders. Supporting universe-level placeholders would be
   a separate sort-polymorphic contextual-binding design, not a template-only
   extension.

### Frozen PLAN-DECOMPOSE-3C1 contract

Add one browser-safe management-only module and profile:

```text
CORE_PROOF_REFINE_TEMPLATE_PROFILE
  revision = emdash-proof-refine-template-v1

coreProofPlanRefine(template, bindings, options?)
  -> nested CoreProofPlanHave(... CoreProofPlanExact(...))
```

1. `bindings` contain an explicit term-level `KernelBinder` and child proof
   plan; the binder name is the placeholder identity. Names are unique and
   declaration order is stable. Placeholder references may repeat, but unused
   or unknown identities fail before returning a plan. Pi/lambda binder types
   are ordinary meta-free Core, not template expressions.
2. The template has no meta node and never becomes Core or canonical source.
   Lowering shifts ordinary root-context indices around the new `have`
   binders, preserves indices belonging to template-local Pi/lambda binders,
   and maps a placeholder occurrence under local depth `d` to its exact
   shared fact index.
3. The output contains only existing `have` and `exact` plan tags and is
   validated through the ordinary plan validator. Execution, traces, named
   holes, retained unused obligations, checking, artifacts, source round-trip,
   and CLI projection remain exclusively owned by the v2 base-plan family.
4. Publish the profile, template builders, and macro from the curated
   browser-safe workspace package; add the exact implemented profile to an
   AI-native capability record v5. The constructor macro remains v1. Proof
   plan/document/state/artifact/source/workspace/research revisions and pins
   do not change because canonical data sees only the already-versioned v2
   expansion.
5. Reject cycles, duplicate bindings, unknown or unused placeholders,
   malformed owners/plicity/variation, process-local metas, and wrong proof-
   plan IDs structurally before returning a plan. Scope and type errors remain
   ordinary checker/refiner failures during replay with the existing per-
   tactic transaction boundary; whole-plan rollback is not added. No
   automatic placeholder discovery, inference, reordering, or search is
   permitted.

Focused acceptance covers byte/deep equality to a hand-written base-plan
expansion, complete/open higher-order callee templates, repeated occurrence
sharing, two-binding ordering, root-context shifting beneath a template
binder, malformed/cyclic/meta-bearing inputs, direct source round-trip of the
expanded output, capability and public-barrel visibility, typecheck,
changed-file lint, workspace check, and packed ESM/CJS/strict-TypeScript/
browser consumers. Under `D-PA-019`, no long root or repository aggregate is
run unless omission becomes progress-blocking.

Non-effects: no new Core expression, proof-plan tag, refiner/checker/session
rule, canonical template/source decoder, proof/source/artifact/research
revision or pin, declaration or term parser, arbitrary host execution,
equality/rewrite behavior, theorem import, Lambdapi source, mathematical
owner/rule, Node adapter, CLI, network/cache/MCP/LSP, print/book, sibling
repository, npm publication, release, or deployment change.

### PLAN-DECOMPOSE-3C1 completion record

Semantic checkpoint: `39d9fc8` (`feat: add refine template proof macro`).

The browser-safe workspace API now exports immutable
`emdash-proof-refine-template-v1` data and `coreProofPlanRefine`. Explicitly
ordered, selected-goal-context term placeholders lower immediately to nested
contextual `have` nodes followed by one `exact`; repeated occurrences share
the same fact. Core leaves are weakened around generated facts, and template
bodies are weakened correctly beneath Pi/lambda binders. Valid Core owner
applications and generic calls are rebuilt through the existing constructors.
The result retains no template, callback, meta, environment, or new plan tag.

The macro preflights duplicate, unknown, unused, cyclic, meta-bearing, wrong-
arity, forged-owner, malformed-plicity/mode, and invalid child-plan inputs.
Semantic scope/type checking remains owned by ordinary plan replay and its
per-tactic transactions. The canonical v2 source round-trip sees only the
expanded `have`/`exact` tree and contains no `placeholder` or `refine` tag.
Accordingly no proof-plan, proof-document, source, artifact, workspace, CLI,
or research revision/pin changed; only the static AI-native capability record
advanced from v4 to v5.

Two final-checker boundaries remain deliberate. Template placeholders are
term facts: a type-position placeholder would need the separately unapproved
sort-polymorphic contextual binding described above. Also, solving a callee
placeholder with an annotated lambda can close every session meta while the
substituted final term still fails fresh inference with
`CANNOT_INFER_LAMBDA`. Complete positive fixtures therefore use an inferable
declared function, and the fresh checker/artifact compiler—not absence of
session goals—remains final authority. This tranche does not widen lambda
inference or introduce a hidden declaration.

Final proportional evidence on 2026-08-10:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_template_tests.ts \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts
  passed: 35/35 tests, 7 suites

node --require ts-node/register --test \
  tests/v3_2_browser_directed_tests.ts
  passed: 13/13 tests, 1 suite; transitive local closure has no Node builtin

./scripts/pnpmw run typecheck
  passed

eslint over every changed TypeScript/JavaScript file
  passed

./scripts/pnpmw run workspace:check
  passed: pnpm@11.16.0; Node 24.11.1

./scripts/pnpmw run package:check
  passed: package build plus packed ESM, CJS, strict-TypeScript, and browser
  bundle consumers

git diff --cached --check
  passed before semantic checkpoint 39d9fc8
```

The standalone `emdash-template` reviewer wrapper was not retried: its known
fixture-local dependency/Corepack self-spawn limitation is unchanged, while
the actual packed browser bundle consumer passed. Under `D-PA-019`, no long
`check:ts` or repository aggregate was run because the focused semantic,
static, closure, workspace, and packed-consumer gates exercised every changed
boundary directly. No Lambdapi/kernel, print/book, npm publication, release,
deployment, or sibling-repository operation was run.

## GOAL-COUPLING-4A Audit And Frozen 4B Graph Tranche

Date: 2026-08-10

Status: `GOAL-COUPLING-4A` audit complete; `GOAL-COUPLING-4B` frozen and
approved for bounded implementation under the standing self-approval and
checkpoint policy.

### Material findings

1. The v2 proof-state snapshot already replaces open process metas in terms,
   targets, context types, and provenance details with stable source hole
   names. The dependent fixture therefore renders a witness target as
   `plan_P(explicit:?index[])`. Parsing that diagnostic string back into a
   graph would make presentation syntax an accidental semantic authority.
2. A graph can instead be derived while the fresh execution still owns both
   structured Core and the total meta-to-hole labeling. This does not require
   another proof-state/source/artifact migration. The graph is a separate
   immutable portable product returned by process-local execution and proof-
   document compilation; canonical v2 proof artifacts remain byte-stable and
   continue to own proof status and checked Core.
3. A direct edge means exactly that an open prerequisite meta occurs in the
   dependent goal's zonked target or in one of its local-context binding
   types. Root-term co-occurrence, proof-plan nesting, source order, and the
   mere fact that two goals were introduced by the same tactic do not create
   edges. A retained source obligation is a graph node but creates no special
   dependency by retention alone.
4. Edge direction is explicit: `dependentGoalId -> prerequisiteGoalId`.
   Target and context occurrence counts are kept separately. An occurrence in
   a meta spine counts structurally; solved metas are zonked away; unknown or
   unrelated session metas cannot become public endpoints. Repeated
   occurrences collapse to one edge with positive counts.
5. The graph records direct coupling, not a materialized transitive closure.
   Reachability, scheduling layers, strongly connected components, and
   transitive impact are deterministic derived views over the direct graph.
   No search or proof-order policy is smuggled into the semantic artifact.
6. Nodes follow the existing stable proof-goal order. Edges follow dependent
   node order and then prerequisite node order, so serialization is byte-
   stable across fresh sessions without exposing session symbols or numeric
   meta IDs. Complete proofs produce the same profile with empty nodes and
   edges.
7. The existing indexed application is the measured target-dependency
   consumer: `witness` directly requires `index`. A second fixture introduces
   a local binder whose type mentions `index`, establishing a context-only
   edge. An independent two-premise fixture must produce two nodes and no
   edge. These cases distinguish semantic dependency from mere siblinghood.
8. Lean's local `MVarId.getMVarDependencies` implementation likewise examines
   a metavariable's type and local declarations, but computes transitive
   resident-state dependencies. Emdash adopts the useful structural scope
   while publishing direct stable source-ID edges from a disposable replay.
9. `DEV-CLI-2C` remains a separate next row. It will wrap these per-proof
   graphs with exact module/declaration identity and expose JSONL/text without
   recomputing dependency semantics in the Node adapter.

### Frozen GOAL-COUPLING-4B contract

Add one browser-safe graph profile and portable shape:

```text
CORE_PROOF_GOAL_COUPLING_PROFILE
  revision = emdash-proof-goal-coupling-v1
  graphRevision = emdash-proof-goal-coupling-graph-v1

CoreProofGoalCouplingGraph
  nodes[] = { id, reachability }
  edges[] = {
    dependentGoalId,
    prerequisiteGoalId,
    targetOccurrenceCount,
    contextOccurrenceCount
  }
```

1. Build the graph from the final freshly inspected goals, their zonked Core
   targets and local-context types, and the complete stable hole-label map.
   Every edge endpoint must be one of the graph's unique nodes, every edge has
   a positive total occurrence count, self-edges are omitted, and output is
   deeply frozen.
2. `CoreProofPlanExecution.goalGraph` exposes the graph beside, not inside,
   `snapshot`. `CoreProofDocumentCompilation.goalGraph` carries the same
   portable value so exact-closure and development compilers can project it
   without retaining the checker session. Provide deterministic JSON and text
   renderers as the first exact views.
3. Keep `emdash-proof-state-v2`, proof-document/artifact/JSONL v2, exact-
   closure/development/source/store/CLI v2, and research revisions and pins
   unchanged. The graph is additive compilation output and is not silently
   inserted into an existing canonical envelope. Advance only the static AI-
   native capability record to v6 and replace its graph prerequisite with the
   remaining exact command-projection row.
4. Publish the graph profile, types, and renderers through the curated browser-
   safe workspace entry. The module performs no checking, I/O, hashing,
   parsing, callback retention, graph search, Node import, or Lambdapi call.
5. Fail closed if internal construction ever lacks a stable endpoint or sees
   a foreign session meta. Construction happens only after proof-plan replay
   has already required every open goal to have a unique portable hole ID.

Focused acceptance covers empty complete graphs, independent siblings, one
target-dependent edge, one context-only edge, repeated-occurrence counts,
fresh-session byte equality, deep immutability, no raw meta/session identity,
proof-document propagation, capability/public-barrel visibility, typecheck,
changed-file lint, workspace check, browser closure, and packed ESM/CJS/
strict-TypeScript/browser consumers. Under `D-PA-019`, no long root or
repository aggregate is run unless omission becomes progress-blocking.

Non-effects: no Core expression, checker/session/refiner/tactic or proof-plan
tag, canonical plan/source decoder, proof-state/artifact/source/workspace/CLI/
research revision or pin, graph command, graph persistence, declaration or
term parser, proof search/scheduling, theorem import, equality/rewrite,
Lambdapi source, mathematical owner/rule, Node acquisition, filesystem,
network/cache/MCP/LSP, print/book, sibling repository, npm publication,
release, or deployment change.

### GOAL-COUPLING-4B completion record

Semantic checkpoint: `de971de`
(`feat: add portable proof goal coupling graphs`).

The browser-safe workspace API now exports
`emdash-proof-goal-coupling-v1`. Every proof-plan execution derives one deeply
frozen portable graph after all open goals have stable source IDs. Nodes keep
existing proof-goal order and reachability. Direct edges point from dependent
goals to prerequisites and separately count occurrences in the zonked target
and local-context binding types; solved metas disappear, repeated occurrences
collapse into one counted edge, independent siblings remain disconnected, and
complete proofs produce empty graphs.

`CoreProofPlanExecution.goalGraph` and
`CoreProofDocumentCompilation.goalGraph` expose the same value beside the v2
snapshot/artifact. JSON and text views are deterministic across fresh
sessions and contain no session symbol or numeric meta identity. Construction
rejects missing, duplicate, or nonportable stable endpoints. The exact-
closure and development layers can reach the graph through their existing
proof compilation without retaining a checker session, which makes
`DEV-CLI-2C` a projection task rather than a second dependency analysis.

Canonical proof state, document/artifact/JSONL, exact-closure workspace,
development/source/store/CLI, and research revisions and pins remain v2 and
byte-compatible because no graph field entered those envelopes. The static
AI-native capability record alone advances from v5 to v6 and now reports the
implemented coupling profile while leaving the command projection deferred.

Final proportional evidence on 2026-08-10:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_proof_document_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts
  passed: 37/37 tests, 5 suites

node --require ts-node/register --test \
  tests/v3_2_proof_template_tests.ts \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_proof_development_cli_tests.ts
  passed: 28/28 tests, 6 suites

./scripts/pnpmw run typecheck
  passed

eslint over every changed TypeScript/JavaScript file
  passed

./scripts/pnpmw run workspace:check
  passed: pnpm@11.16.0; Node 24.11.1

node --require ts-node/register --test \
  tests/v3_2_browser_directed_tests.ts
  passed: 13/13 tests, 1 suite; transitive local closure has no Node builtin

./scripts/pnpmw run package:check
  passed: package build plus packed ESM, CJS, strict-TypeScript, and browser
  bundle consumers

git diff --cached --check
  passed before semantic checkpoint de971de
```

Under `D-PA-019`, no long `check:ts` or repository aggregate was run because
the focused proof, compilation, downstream development, static, closure,
workspace, and packed-consumer gates exercised every changed boundary
directly. The standalone `emdash-template` reviewer wrapper was not retried;
its known environment limitation is unchanged and the actual packed browser
consumer passed. No Lambdapi/kernel, print/book, npm publication, release,
deployment, or sibling-repository operation was run.

## DEV-CLI-2C Audit And Frozen Graph-Command Tranche

Date: 2026-08-10

Status: audit complete; the bounded implementation below is frozen and
approved under the standing self-approval and checkpoint policy.

### Material findings

1. `GOAL-COUPLING-4B` leaves no dependency semantics for the Node adapter to
   invent. Each fresh proof compilation already carries one portable direct
   graph with stable node IDs, exact edge direction/counts, deterministic
   order, and its own semantic revision.
2. The command must wrap each graph with `moduleId` and `declarationId` because
   hole IDs are unique only within one proof. Whole-development selection
   emits one wrapper for every proof in canonical proof order, including an
   empty graph for a complete proof. Exact proof selection emits exactly one.
   Omitting empty graphs would make proof membership implicit in status text
   and prevent a complete graph view of the selected development.
3. JSONL begins with the existing summary record and then ordered graph
   wrappers. Text begins with the same summary view and then one explicitly
   identified graph view per proof. Neither representation contains a project
   root, source text, checker/session object, numeric meta identity, or parsed
   diagnostic expression.
4. `graph` is an inspection command like `goals`: an incomplete development
   with a successfully derived graph exits zero. `check` and `build` retain
   exit one for incomplete proofs, and acquisition/parse/selection failures
   retain exit two. No mutable status or success inference is added.
5. The CLI profile's command tuple and summary record's closed `command` union
   gain `graph`; both therefore advance from v2 to v3. The new exact wrapper is
   `emdash-lf-proof-development-graph-v1`. Goal and build record revisions,
   mounted source, development/source/artifact, and coupling-graph revisions
   remain unchanged.
6. The static AI-native capability record advances from v6 to v7, adds the
   exact `development-graph` command, and removes only its now-satisfied
   deferred entry. The browser-safe npm workspace remains free of the Node
   adapter; no package entry or proof artifact changes.

### Frozen DEV-CLI-2C contract

Extend the existing command namespace:

```text
./scripts/emdash development graph \
  --project-root ABSOLUTE_PATH \
  [--module MODULE_ID --declaration DECLARATION_ID] \
  [--format jsonl|text]

CoreLfProofDevelopmentGraphRecord
  revision = emdash-lf-proof-development-graph-v1
  kind = proof-development-goal-graph
  moduleId
  declarationId
  graph = CoreProofGoalCouplingGraph
```

1. Reuse the current fixed canonical filename, explicit-real-root acquisition,
   fresh development compilation, exact proof selection, and option parser.
   Add only the literal `graph` command; no positional path, backend switch,
   root discovery, arbitrary host source, output file, or new I/O authority.
2. Selected-development assembly carries ordered graph wrappers alongside the
   existing summary/goals/artifact values. It reads
   `proof.proofCompilation.goalGraph`; the CLI never traverses Core or metas.
3. JSONL graph output is `[summary, ...graphRecords]`. Text output is the
   summary followed by an exact proof identity and the existing graph text
   renderer for every record. Both formats end with one newline and are
   deterministic across repeated fresh invocations.
4. Advance the CLI profile and summary wrapper to v3, add graph-wrapper v1 and
   pin `emdash-proof-goal-coupling-v1`. Keep goal/build v2 and every canonical
   proof/source/artifact revision unchanged. Advance the static capability
   record to v7 as described above.
5. Preserve old `check`, `goals`, `build`, top-level proof, workspace, and
   capability routes byte-for-byte except for the intentionally advanced
   summary revision/profile claim. An incomplete `graph` or `goals` command
   returns zero; incomplete `check` or `build` returns one; malformed commands
   and unknown proof selection return two.

Focused acceptance covers whole-development and exact-proof JSONL, complete
and open graphs, canonical proof order, empty graph retention, text rendering,
repeat-run byte equality, no root/source/session/meta leakage, incomplete exit
semantics, malformed/unknown selection failures, actual shell routing,
unchanged legacy routes, exact capability/profile parity, typecheck,
changed-file lint, workspace check, shell syntax, exact diff review, and
whitespace hygiene. Under `D-PA-019`, no long root/repository aggregate is run
unless omission becomes progress-blocking.

Non-effects: no coupling semantics or graph traversal, Core/checker/session/
refiner/proof-plan change, canonical proof state/artifact/source/development or
research revision/pin, browser-package entry, declaration/term parser, proof
search/scheduling, theorem import, equality/rewrite, Lambdapi source,
mathematical owner/rule, additional filesystem/network/cache/MCP/LSP
authority, output write, print/book, sibling repository, npm publication,
release, or deployment change.

### DEV-CLI-2C completion record

Semantic checkpoint: `8e21afb`
(`feat: add proof development graph command`).

The explicit-root Node adapter now accepts `development graph` over the same
fixed canonical source and fresh checked compilation as `check`, `goals`, and
`build`. Whole-development JSONL contains the summary followed by one module/
declaration-qualified graph wrapper for every proof in canonical order;
exact-proof selection contains one wrapper. Complete proofs retain empty
graphs, incomplete graph inspection exits zero, and text output delegates to
the existing portable graph renderer. The adapter reads only
`proof.proofCompilation.goalGraph`; it performs no second Core/meta traversal.

The development CLI and summary profiles advance from v2 to v3, the new graph
wrapper is v1, and the static capability record advances from v6 to v7. Goal
and build records remain v2. Canonical proof state, source, development,
artifact, coupling-graph, and research revisions remain unchanged. The
capability record now advertises the exact command and no longer lists its
completed projection as deferred.

Final proportional evidence on 2026-08-10:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_development_cli_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts
  passed: 24/24 tests, 5 suites; includes actual shell routing

./scripts/pnpmw run typecheck
  passed

eslint over every changed TypeScript/JavaScript file
  passed

./scripts/pnpmw run workspace:check
  passed: pnpm@11.16.0; Node 24.11.1

sh -n scripts/emdash
  passed

git diff --cached --check
  passed before semantic checkpoint 8e21afb
```

Under `D-PA-019`, no long `check:ts` or repository aggregate was run: focused
command semantics, exact static records, typecheck, changed-file lint,
workspace integrity, shell routing/syntax, and exact diff review exercised the
changed Node/static boundary directly. Browser closure and packed-package
consumers were not rerun because this tranche adds no browser-safe package
module or entry and does not change the already-qualified coupling graph;
their green `GOAL-COUPLING-4B` evidence is historical unchanged-boundary
evidence, not a current pass. No Lambdapi/kernel, print/book, npm publication,
release, deployment, or sibling-repository operation was run.

## SIMP-5A Audit And Frozen Proof-Checker Prerequisite

The audit found four mechanisms which must remain distinct even when a user
experiences all four as “automation”:

1. kernel/runtime definitional computation decides conversion without
   constructing a propositional proof;
2. proof-time unification assigns scoped metavariables while elaborating one
   checked term;
3. instance synthesis selects explicit dictionary evidence under its own
   scope, ambiguity, cycle, and budget policy; and
4. propositional simplification applies equality theorems and must return the
   resulting proof term and a replayable trace.

Lean's local source was inspected as comparative evidence, especially its
ordered theorem sets, pre/post traversal, congruence, dischargers, caches,
global step bound, and proof production. Those are useful product lessons,
not an instruction to reproduce a global mutable simp registry or Lean's
tactic runtime. Emdash v1 instead selects explicit immutable rules per call,
uses deterministic order and bounded work, and treats fresh checker replay as
authority.

The active Lambdapi v3.2 equality owners were inspected read-only. They
provide equality, reflexivity, primitive right path induction, guarded beta,
and derived symmetry/application principles. No mathematical declaration is
missing, and this row does not edit or reinterpret presheaves, sites,
sheafification, schemes, or any other active mathematics. The historical
`scale_stress_1b_proposal.ts` acquisition is useful signature evidence but is
not product authority and is not imported by the simplifier.

### Material checker seam

An occurrence-specific rewrite lowers through path induction with a lambda
motive. Its inferred result type therefore contains a generic lambda call
which must beta-convert to the user's target. The released proof-document
compiler currently creates a plain `CoreElaborationSession` and
`CoreChecker`; that frozen checker deliberately excludes generic-call beta.
Consequently, a sound proof-producing simplifier cannot replay its ordinary
transport term through the current proof-document boundary.

Three apparent workarounds are rejected:

- manufacturing a hidden global declaration specialized to each motive;
- exposing a beta-expanded implementation target to the source author; or
- emitting a simplifier result which the canonical proof document cannot
  independently check.

This is a TypeScript proof-document conversion seam, not a Lambdapi or
mathematics gap. `SIMP-5B` is therefore repartitioned into a narrow checker
prerequisite, an unconditional first simplifier, and later congruence/premise
extensions.

### Frozen SIMP-5B0 contract

Add a browser-safe `CoreProofChecker` and immutable profile with these exact
properties:

1. It checks against one exact `CoreLfDeclarationEnvironment` and reuses the
   existing `CoreLfElaborationSession` plus `coreLfDefinitionalCompare`.
   Conversion is bounded by the existing exported 256-step global comparison
   budget and orders zonking, generic beta, transparent checked delta, and the
   reviewed built-in runtime exactly as the existing combined comparator.
2. It does **not** opt into annotated-lambda inference. A lambda is still
   accepted only while checking against an expected Pi; a generic call whose
   callee itself is an annotated lambda remains `CANNOT_INFER_LAMBDA`. This
   preserves the earlier `have`/`refine` decision while allowing lambda
   motives supplied as checked arguments.
3. It accepts no runtime callback, theorem hook, simplifier rule, instance
   provider, or Lambdapi process. The ordinary reviewed runtime is the only
   runtime component. Checker comparison records remain process-local
   diagnostics and never enter proof artifacts.
4. `compileCoreProofDocument` requires the rich LF environment and creates a
   fresh proof checker/session for every compilation. Exact-closure workspace
   proofs pass the already-owned reconstructed LF environment, not its lossy
   body-free Core projection. The direct proof demo is migrated to construct
   the same opaque LF environment explicitly.
5. The positive semantic fixture checks an ordinary transport/path-induction
   term whose explicit lambda motive requires beta at the final target. A
   transparent-definition fixture establishes exact delta ownership; a
   negative fixture proves that lambda-callee inference remains closed.
6. The migration is one coordinated pre-release semantic-profile update:

   | Boundary | Revision after SIMP-5B0 |
   | --- | --- |
   | proof checker | new `emdash-core-proof-checker-v1` |
   | proof document/compiler | v3; checker named `CoreProofChecker` |
   | proof state/artifact/JSONL and explicit Core | unchanged v2/v2/v2/v1 |
   | exact-closure workspace proof/compiler | v3; artifact schema remains v2 |
   | proof development profile | v3; artifact schema remains v2 |
   | canonical development source | v3; payload shape otherwise unchanged |
   | mounted development | v3 with the exact v3 source-profile pin |
   | development CLI profile | v4; summary/goal/build/graph record schemas remain v3/v2/v2/v1 |
   | research-document binding/snapshot | unchanged v2 |
   | pinned research overview, files, and browser replay | v3 with recomputed exact hashes |
   | AI-native capability profile/record | v8, including the new proof-checker profile |

   Fingerprints change because the serialized proof profile changes. Existing
   v2 artifact *shapes* remain sufficient: their current fingerprint and
   enclosing profile/compiler fields make stale semantic results rejectable,
   so inventing v3 JSON envelopes would conflate schema with checker policy.
7. Package version remains `0.1.0`; this row does not publish. The workspace
   package explicitly exports the checker because proof-document public types
   now expose its LF environment boundary. The narrow core-only entry remains
   unchanged.

Acceptance uses new proof-checker/proof-document cases, the affected proof,
workspace, development, CLI, research-pin, browser-closure, and packed ESM/
CJS/strict-TypeScript/browser consumers, plus typecheck, changed-file lint,
workspace integrity, exact staged-diff review, and whitespace hygiene. No
Lambdapi/kernel, print/book, sibling-repository, deployment, or publication
gate is relevant. Under `D-PA-019`, long aggregates remain omitted unless a
changed boundary cannot be validated proportionally; the root SOP's shared-
TypeScript aggregate rule is reconciled at checkpoint time rather than used
as a pre-edit or iterative rerun.

### SIMP-5B0 completion record

Semantic checkpoint: `7c9d8f7`
(`feat: add bounded proof checker conversion`).

The browser-safe workspace product now exports
`emdash-core-proof-checker-v1`. `CoreProofChecker` is constructed only from an
exact `CoreLfDeclarationEnvironment`; it reuses the existing combined
zonk/beta/delta/reviewed-runtime comparison and its 256-step global budget.
Its constructor exposes no catalog runtime, and its protected lambda policy
continues to reject annotated lambdas in inference position.

`compileCoreProofDocument` now creates this checker in a fresh session.
Exact-closure workspace proofs pass the reconstructed LF environment instead
of discarding checked transparent bodies through `.coreEnvironment`. The
direct proof demo constructs an opaque LF environment through the same public
owner. The new decoded-groupoid transport fixture checks
`P : τ A -> Grpd`, `u : τ(P x)`, and a path-induction-shaped transport whose
lambda motive requires beta; its user target additionally unfolds one exact
transparent family alias. The comparison trace contains both beta and delta,
while a generic call with that lambda as callee still fails with
`CANNOT_INFER_LAMBDA`.

The semantic profile chain advances exactly as frozen: proof document and
workspace proof are v3, proof development and canonical source are v3,
mounted development is v3, development CLI is v4, pinned research overview/
files/browser replay are v3, and the capability record is v8. Proof state,
standalone and workspace/development artifact envelope shapes, JSONL, goal/
build/graph record shapes, explicit Core, and research-document binding stay
at their existing revisions. Exact proof-source, serialized-profile,
management-source, and proof-artifact SHA-256 pins were recomputed and then
verified by both Node materialization and browser replay.

Final validation on 2026-08-10:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_checker_tests.ts \
  tests/v3_2_proof_document_tests.ts \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_proof_development_cli_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts
  passed: 46/46 tests, 10 suites

node --require ts-node/register --test \
  tests/v3_2_browser_directed_tests.ts
  passed: 13/13 tests, 1 suite

./scripts/pnpmw run typecheck
  passed

eslint over every changed TypeScript/JavaScript file
  passed

./scripts/pnpmw run workspace:check
  passed: pnpm@11.16.0; Node 24.11.1

./scripts/pnpmw run package:check
  passed: build plus installed ESM, CJS, strict-TypeScript, and browser bundle

./scripts/pnpmw run check:ts
  passed: 1607 tests, 243 suites; 1553 pass, 54 skip, 0 fail
  duration: 1603213 ms (about 26 minutes 43 seconds)

git diff --cached --check
  passed before semantic checkpoint 7c9d8f7
```

The complete `check:ts` was run once only because current root `AGENTS.md`
explicitly makes it a pre-checkpoint gate when the shared checker/compiler or
public package barrel changes. Its high systemic cost reinforces
`D-PA-019`; it is not a precedent for iterative or reassurance reruns. No
`check:all`, Lambdapi/kernel, print/book, sibling-repository, npm publication,
GitHub Release, deployment, or other long aggregate was run.

Non-effects: no Core constructor, proof-plan tag, source/artifact field,
mathematical equality/J owner, simplifier rule, typeclass behavior, theorem
import, declaration/term parser, arbitrary host execution, callback registry,
MCP/LSP/server, filesystem/network/cache authority, or trusted Lambdapi
dependency was added. `SIMP-5B1` remains a management-layer proof-producing
consumer of this checked boundary.

### Frozen SIMP-5B1 first simplifier scope

After 5B0 is green, the first simplifier is a browser-safe management layer,
not a checker extension. It receives an explicit immutable equality/transport
adapter and ordered immutable theorem rules; validates rule shapes through the
proof checker; and returns ordinary explicit Core evidence, an expanded base
proof plan, and a complete immutable trace. No rule registry, attribute,
callback, process meta, declaration parser, or retained checker session is
canonical state.

The v1 strategy is deterministic postorder, left-to-right traversal over the
selected root target, first matching rule in caller order, then restart. It
uses structural first-order matching, explicit orientation, separate safe-
integer rewrite and visit/attempt budgets, and cycle detection. Every trace
entry records rule ID, occurrence path, before/after terms, orientation, and
proof origin. Final checking, not the trace, is proof authority.

The first positive scope is unconditional globally declared equality
theorems over decoded/groupoid propositions. The result lowers to existing
`have` plus `exact` plans with one simplified-target continuation; no new Core
node, proof-plan tag, source decoder, or artifact field is added by 5B1.
Conditional theorem premises, local-hypothesis rule discovery, reverse rules
requiring synthesized symmetry, rewriting beneath binder bodies, dependent
congruence, associative/commutative normalization, simprocs, indexing, and
external premise discharge remain `SIMP-5B2` or later work. This staged scope
is deliberately useful for ordinary definitional theorem cleanup while
keeping every dependent extension evidence-producing and reviewable.

#### Frozen SIMP-5B1 API and semantic contract

The first implementation owns one additive browser-safe
`emdash-proof-simplifier-v1` management profile. Its public operation receives
one exact `CoreLfDeclarationEnvironment`, a closed canonical root target,
an explicit equality/backward-transport adapter, ordered theorem rules, one
ordinary continuation `CoreProofPlan`, source provenance, an optional stable
`have` binder name, and explicit bounded limits. It returns the original and
simplified targets, exact counters, a complete frozen trace, the checked
transport body when rewriting occurred, and an expanded existing base plan.
It retains no checker, environment mutation, callback, registry, cache, or
metavariable.

The adapter consists of two globally declared free Core references and is
validated before traversal:

1. equality has canonical outer-LF shape
   `Π [A : Grpd], τ A -> τ A -> Grpd`; and
2. backward transport has canonical `ind_eq` shape
   `Π [A] [x] [y], τ (Eq A x y) ->
   Π P : (τ A -> Grpd), τ (P y) -> τ (P x)`.

The structural adapter check is provenance-insensitive but plicity- and
direction-sensitive. Definitionally aliased adapter signatures are outside
v1: callers must select their canonical checked owners explicitly. The
transport's motive-binder mode is retained when constructing the lambda
motive. A malformed, missing, forward-only, or differently ordered adapter is
rejected even when no rule would happen to fire.

Each v1 rule has a unique stable ID, explicit `forward` orientation, and one
globally declared theorem reference. The proof checker must infer a telescope
ending syntactically in `τ (Eq A lhs rhs)`. Nested `Pi`, lambda, and meta nodes
inside `A`, `lhs`, or `rhs` are rejected for this first-order tranche, and a
bare telescope variable cannot be the entire left side. Every leading theorem
binder must be recoverable by matching `A` and `lhs`; this excludes conditions
and right-only variables while still allowing ordinary implicit classifier
parameters. The theorem reference is applied to all recovered arguments in
outer-to-inner binder order, and the resulting proof is freshly checked
against the instantiated equality before it becomes trace evidence.

The root target must be closed, meta-free, well-formed, and syntactically
`τ goalClassifier`. Traversal is over `goalClassifier`, not over a serialized
term. Owner arguments and generic-call callee/arguments are visited
postorder, left to right. `Pi` and lambda nodes are opaque: v1 neither descends
through their annotations/bodies nor claims dependent congruence. At each
candidate, rules are attempted in caller order. The first checked structural
match rewrites that occurrence, then traversal restarts from the new root.
Provenance never affects matching.

Limits are three nonnegative safe integers: maximum successful rewrites,
maximum visited candidate nodes, and maximum rule attempts. Defaults are part
of the profile; counters have the following exact meaning:

- a visit is charged immediately before inspecting one candidate node;
- an attempt is charged immediately before structurally trying one rule at
  that node; and
- a rewrite is charged only after structural matching and theorem checking
  succeed, immediately before accepting the new root.

Exhausting any needed budget rejects the whole operation with its distinct
error code. Canonical explicit-Core serialization keys every accepted root,
including the initial root; revisiting a root rejects with a cycle error.
Budget or cycle rejection never returns a partially simplified plan.

Every accepted trace entry contains the one-based step, rule ID, `forward`
orientation, stable root-relative occurrence path, global theorem origin,
whole classifier before/after, occurrence before/after, inferred element
classifier, and freshly checked equality proof. Trace order is rewrite order.
The trace is diagnostic and replay evidence, not a second proof authority.

For an occurrence `lhs -> rhs` in classifier context `C[-]`, lowering builds
the checked backward term

```text
ind_eq proof (lambda t : tau A, C[t]) futureProof
    : tau (C[lhs])
```

and composes transport terms in reverse trace order. When at least one rule
fires, the output plan is exactly one existing contextual `have` whose fact
target is `τ finalClassifier`, whose proof child is the caller's continuation,
and whose body is one existing `exact` node containing the checked nested
transport. When no rule fires, the continuation is returned unchanged. This
is why the caller may provide an ordinary stable named hole without knowing
the simplified target in advance, while the result still exposes that target
for the next AI/human patch.

The first standalone consumer uses a generic wrapper theorem over a decoded
classifier, demonstrates inner-first restart on a nested term, and compiles
the generated plan to a complete proof document. Negative cases cover rule
order, malformed or conditional rules, opaque binders, cycle detection, each
budget, and rejection of reversed/invalid transport. The fixture is isolated
from the active presheaf/site/scheme mathematics.

This additive management row does not revise Core, proof-plan, proof-source,
proof-state, proof-artifact, workspace, or CLI schemas. It adds its profile to
the static capability record and exports the browser-safe API from the
contributor and workspace package entries; the core-only package entry stays
unchanged. Focused simplifier/proof-document tests, browser closure, packed
ESM/CJS/strict-TypeScript/browser consumers, typecheck, changed-file lint,
workspace integrity, exact staged-diff review, and whitespace hygiene are the
direct gates. Because the public workspace barrel changes, current root SOP
requires one complete `check:ts` only after those bounded gates are green and
before checkpoint; it is not an iterative test and `check:all` remains
irrelevant.

## Decision Ledger

| ID | Decision | Reason |
| --- | --- | --- |
| `D-PA-001` | Build the proof-engineering plane before the general goal plane. | The checked proof foundation is ready; prematurely mixing task evidence with proof authority would weaken both products. |
| `D-PA-002` | Keep explicit Core and the TypeScript checker as production authority; keep Lambdapi optional as emitter/oracle. | Preserves the qualified trust boundary and browser/hosted portability. |
| `D-PA-003` | Use inert source and candidate patches, not an authoritative tactic server. | AI agents need inspectable, replayable state with stable preconditions rather than cursor/process identity. |
| `D-PA-004` | First generalize the semantic development catalog, then file acquisition and CLI targeting. | It separates mathematical/workspace ownership from Node path and execution policy. |
| `D-PA-005` | Preserve independent proof leaves in catalog v1. | Theorem-to-theorem imports require an explicit interface/export and fingerprint design; list order must not imply proof authority. |
| `D-PA-006` | Keep computation, unification, instance synthesis, and propositional simplification separate. | They have distinct trust, termination, and proof-production obligations. |
| `D-PA-007` | Require automation providers to return replayable candidate patches or certificates. | Search success cannot certify its own result. |
| `D-PA-008` | Permit embeddings only to rank already accessible exact declarations. | Visibility and correctness remain symbolic, reviewable facts. |
| `D-PA-009` | Implement `cases`/`induction` through curated eliminators and recursors. | Provides ordinary proof usability without a general inductive frontend. |
| `D-PA-010` | Keep expected source states advisory until checker replay verifies them. | Arbitrary TypeScript and dependent reduction cannot be soundly evaluated by source inspection alone. |
| `D-PA-011` | Treat counterexamples/tests as labeled counterevidence, not proof. | Avoids collapsing execution evidence into theorem authority. |
| `D-PA-012` | Give the later goal assistant a policy/evidence evaluator, not a second truth kernel. | Tasks, decisions, approvals, observations, and theorems have different discharge conditions. |
| `D-PA-013` | Status is derived; no mutable `done` field is authoritative. | Makes goal graphs reproducible and exposes stale or insufficient evidence. |
| `D-PA-014` | Logic libraries are versioned profiles with explicit consequence/evidence rules. | Different reasoning domains require visible expressivity and trust choices. |
| `D-PA-015` | Arrowgram renders canonical goal/proof graphs; GetPaidX owns hosted actions and permissions. | Separates semantic artifacts from views, collaboration transport, and external effects. |
| `D-PA-016` | Do not require npm publication for `DEV-CATALOG-1`. | Publication is valuable but the first bootstrap has credential, provenance, 2FA, and trust-hardening prerequisites unrelated to local semantic progress. |
| `D-PA-017` | Fast-forward the already qualified predecessor baseline to `main` before accumulating new proof-assistant semantics. | Produces a clear public integration boundary while the new goal remains isolated on its descendant branch. |
| `D-PA-018` | Accept focused/static/browser/packed evidence for `DEV-CATALOG-1` without completing its long root aggregate. | The first aggregate became unverifiable after an unexpected interruption; the replacement was directly waived by the user. The waiver is tranche-specific and is not positive aggregate evidence or blanket permission to skip future exact gates. |
| `D-PA-019` | Treat long repository aggregates as last-resort blocking gates throughout this persistent goal. | The user explicitly directed that focused evidence be preferred and long reruns be avoided unless their omission would block overall progress; every omission remains visible and is not positive evidence. |
| `D-PA-020` | Repartition `DEV-CLI-2` into canonical supplied-data reconstruction, Node fixed-file commands, and a later stable graph projection. | No safe general proof-development file consumer exists, and arbitrary TypeScript import is not a sandbox. The split preserves direct TypeScript authoring without confusing host execution with checked source. |
| `D-PA-021` | Add an exact `development` command namespace over one fixed canonical file and preserve all older command vectors. | Namespacing keeps Node acquisition asynchronous and separate from the fixed proof demo; fixed-file explicit-root input avoids arbitrary host import/path authority. |
| `D-PA-022` | Prefer source-expanded proof-plan macros whenever a convenience form lowers faithfully to the existing inert base. | It improves AI/human authoring without multiplying trusted tags, decoders, trace semantics, or process state. |
| `D-PA-023` | Implement explicit selected-`constructor` first; reserve contextual `have` and general `refine` for versioned plan/refiner contracts and `rewrite` for the equality/simplifier audit. | Only constructor has an exact base-plan lowering under the frozen checker; the other forms require contracts that cannot be recovered safely by renaming `apply` or runtime reduction. |
| `D-PA-024` | Reject the proposed lambda-cut expansion of `have` after the focused checker probe. | `CoreProofRefiner.apply` must infer its callee, while the frozen `CoreChecker` intentionally rejects annotated-lambda inference; widening that checker or injecting a hidden declaration is outside the macro tranche. |
| `D-PA-025` | Elaborate `have` by contextual meta-spine substitution and retain its fact as an explicit per-refiner source obligation until solved. | It produces ordinary finally checkable Core while preventing an unused continuation from silently erasing an open source task. |
| `D-PA-026` | Perform one coordinated pre-release v2 source/artifact migration for contextual `have`; do not silently widen v1 or build an unused dual reader. | The new plan tag, trace operation, and reachability state affect exhaustive consumers, while npm is unpublished and no tracked canonical v1 development source exists. |
| `D-PA-027` | Repartition general `refine` after contextual `have`: implement a pure root-scoped template macro and reject a new plan/refiner tag without a non-lowerable consumer. | Ordered typed placeholders now expand exactly to retained `have` obligations plus `exact`; keeping the template management-only avoids process metas and needless v3 artifact churn while preserving an explicit scope boundary. |
| `D-PA-028` | Keep refine-template v1 placeholders term-level and keep Pi/lambda binder annotations as meta-free Core. | Type-position placeholders would require `have A : TYPE`, but the frozen contextual binding checks its declared type against `TYPE` while `TYPE : KIND`; sort-polymorphic contextual binding is a distinct design. |
| `D-PA-029` | Keep fresh final checking authoritative when contextual substitution exposes an annotated lambda in inference position. | A plan can solve every session meta through a typed local fact yet produce a substituted lambda call which the deliberately frozen checker cannot infer; declared inferable callees work without weakening the checker. |
| `D-PA-030` | Claim structural macro preflight and existing per-tactic failure atomicity, not whole-plan transactional replay. | The current executor validates the complete inert tree first, then commits each checked refinement separately; the template macro must not overstate a rollback guarantee it does not add. |
| `D-PA-031` | Publish cross-goal coupling as a separate additive portable graph, not a parsed diagnostic string or silent field in proof-state v2. | Structured Core and the stable label map are available during fresh replay; a separate profile avoids making display syntax semantic or forcing an unrelated source/artifact migration. |
| `D-PA-032` | Define direct edges from dependent goals to open prerequisites occurring in zonked targets or local-context types, with separate occurrence counts. | This captures actual type dependency, distinguishes independent sibling goals, and leaves transitive closure and scheduling as explicit derived policies. |
| `D-PA-033` | Keep the Node `development graph` projection in `DEV-CLI-2C` after the browser-safe graph owner is qualified. | The command should wrap one semantic graph rather than reimplement meta traversal, labeling, or edge ordering at the acquisition boundary. |
| `D-PA-034` | Emit one module/declaration-qualified graph wrapper per selected proof, including complete proofs with empty graphs. | Hole IDs are proof-local, and omitting empty graphs would hide selected proof membership from the graph record stream. |
| `D-PA-035` | Treat `development graph` as successful inspection for incomplete proofs, matching `goals` rather than `check` or `build`. | Deriving an explicit open-goal graph is the intended successful result; it does not claim proof completion. |
| `D-PA-036` | Advance the development CLI/profile summary family to v3 and add graph-wrapper v1 while retaining goal/build and canonical artifact v2. | The closed command union changes, but existing goal/build payloads and every proof/source/artifact envelope do not. |
| `D-PA-037` | Keep proof-level simplification separate from definitional computation, unification, and typeclass synthesis. | Equality theorems require explicit proof evidence and their own rule, traversal, trace, and termination policy; none should become a hidden checker or synthesis rule. |
| `D-PA-038` | Add a dedicated bounded `CoreProofChecker` before implementing transport-based simplification. | An occurrence-specific path-induction motive leaves a beta-redex in the inferred target, while the current proof-document checker cannot replay it soundly. |
| `D-PA-039` | Reuse exact LF beta/delta/runtime conversion for proof documents but continue to reject annotated-lambda inference. | Lambda motives are checked arguments with expected Pi types; opening lambda-callee inference would revive the separately rejected `have`/`refine` semantic widening. |
| `D-PA-040` | Advance semantic profiles while retaining unchanged v2 artifact envelopes. | Current fingerprints and enclosing profile/compiler fields reject stale checker results; JSON schema revisions should not be inflated merely because the checking policy advances. |
| `D-PA-041` | Stage simplification as explicit unconditional root-target rewriting before conditional, local, or under-binder congruence. | The first scope yields ordinary replayable transport terms with deterministic behavior, while dependent premise and congruence evidence need separately reviewable contracts. |
| `D-PA-042` | Freeze v1 simplification as canonical decoded equality matching plus checked backward transport, lowered to one existing contextual `have`. | This gives AI agents a compact deterministic `simp`-like source expansion while keeping theorem application and the final nested transport independently checkable, browser-safe, and outside the trusted Core syntax. |

## Validation And Checkpoint Policy

Follow root `AGENTS.md`, nested `emdash2/AGENTS.md` for every affected kernel
path, and the persistent-goal Git workflow.

For each bounded row:

1. inspect all worktrees and staged/unstaged state separately;
2. recover the exact active row and predecessor checkpoint;
3. locate definitions and consumers with `rg`;
4. run only the proportional baseline and focused tests;
5. freeze or update the row contract before semantic widening;
6. implement the smallest positive consumer plus relevant negative cases;
7. synchronize this Work/Decision Ledger and validation evidence;
8. stage only owned paths and review the exact staged diff;
9. require `git diff --cached --check`; and
10. create a rollback-safe checkpoint only when the coherent row is green.

Long `check:ts`, root-test, and `check:all` aggregates are last-resort gates:
run one only when omitting that exact aggregate would block overall progress.
For shared TypeScript or public-package changes, use the smallest focused
semantic suites plus typecheck, lint, browser-closure, and packed-consumer
checks which directly exercise the changed boundary, and record the omitted
aggregate plainly. Carry prior aggregate evidence only as historical evidence
for unchanged boundaries. Every Lambdapi invocation remains bounded to 90
seconds. Never run large aggregates merely for reassurance.

`D-PA-018` records the exact `DEV-CATALOG-1` history. `D-PA-019` records the
user's subsequent persistent policy: long aggregates are eagerly avoided
unless omission becomes progress-blocking. Interrupted, terminated, waived,
or omitted runs are never green evidence.

The user's 2026-08-10 direction authorizes this dedicated descendant branch,
plan-scoped edits, proportional validation, rollback-safe local checkpoints,
and the explicitly audited fast-forward/push of the qualified predecessor to
`main`. It also permits remote/package operations when a recorded row makes
them necessary and all of that row's external prerequisites are met. This is
not permission to force-push, rewrite history, bypass protected review/2FA,
expose or persist credentials, publish unverified bytes, break sibling public
contracts, delete branches/worktrees, or perform cleanup. A persistent goal
must still record the exact remote/release row and evidence before any such
mutation.

## Baseline Evidence

At clean baseline `9c633c8` on 2026-08-10:

```text
./scripts/pnpmw run workspace:check
  passed; pnpm@11.16.0, Node 24.11.1

./scripts/pnpmw run typecheck
  passed

node --require ts-node/register --test \
  tests/v3_2_lf_workspace_tests.ts \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_proof_plan_tests.ts
  21 tests / 3 suites: 21 passed, 0 failed
```

The classes plan's latest green shared boundary—1,570 tests across 237 suites,
1,516 active passes, 54 intentional skips, zero failures—is carried forward.
No aggregate was rerun for the baseline.

## External Design References

These are design evidence, not repository authority:

- Pantograph's machine-oriented Lean interface and explicit metavariable
  coupling: <https://theory.stanford.edu/~barrett/pubs/ASM%2B25-abstract.html>;
- LeanDojo on program-analysis-backed premise selection:
  <https://arxiv.org/abs/2306.15626>;
- Draft, Sketch, and Prove on typed intermediate proof sketches:
  <https://arxiv.org/abs/2210.12283>;
- Isabelle/PIDE immutable document versions:
  <https://isabelle.in.tum.de/~nipkow/pubs/fac19.pdf>;
- Lean's indexed simplifier:
  <https://lean-lang.org/doc/reference/latest/The-Simplifier/Simp-sets/>;
- Isabelle Sledgehammer reconstruction:
  <https://isabelle.in.tum.de/website-Isabelle2016/dist/Isabelle2016/doc/sledgehammer.pdf>;
- Alethe proof certificates: <https://verit.loria.fr/documentation/alethe-spec.pdf>;
- QuickChick counterexample search: <https://github.com/QuickChick/QuickChick>;
- W3C PROV-O: <https://www.w3.org/TR/prov-o/>;
- OWL 2 profiles: <https://www.w3.org/TR/owl2-profiles/>; and
- Argument Interchange Format:
  <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B5398A5BC5ECB369AF119DE7913558AA/S0269888906001044a.pdf/towards-an-argument-interchange-format.pdf>.

## Persistent `/goal` Objective

Use the following objective after the first implementation checkpoint is
synchronized:

> Continue the long-running TypeScript/emdash proof-assistant and typed-goal-
> graph objective from `/home/user1/emdash1-classes-v1` on branch
> `goal/typescript-emdash-proof-assistant-v1`. Treat
> `docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md` as the living
> governing plan, together with every authority and SOP it names. On every
> continuation inspect all worktrees, branch/HEAD ancestry, staged and
> unstaged changes, current code, active plans, and recent proportional
> evidence; preserve unrelated work. Select only the next dependency-ready
> bounded row. Keep the production backend focused on the small
> TypeScript/emdash checker over backend-neutral explicit Core; retain
> deterministic Lambdapi emission/checking only as an optional conformance
> route. Keep computation, unification, instance synthesis, proof-level
> simplification, external automation, and workflow evidence distinct. Do not
> introduce declaration text parsing, a general inductive frontend, hidden
> process-global state, an authoritative MCP/LSP server, or a new trusted Core
> node by analogy.
>
> Start from the completed `DEV-CLI-2B` checkpoint once recorded. Continue
> through measured declarative proof-plan decomposition, stable goal
> coupling, proof-producing simplification,
> accessible-premise indexing, bounded providers, curated-library gates,
> proof maintenance, external certificates, and agent evaluation in the
> dependency order maintained by the living ledger. Begin `GOAL-GRAPH-14A`
> only after its proof-artifact and evidence-policy prerequisites are ready.
> Preserve the hard distinction between a kernel-checked theorem and every
> weaker task/observation/approval/AI evidence class.
>
> Run focused and nearest checks during implementation. Treat long
> `check:ts`, root-test, and `check:all` aggregates as last-resort gates and
> run one only if omitting that exact aggregate would block overall progress;
> record omissions without presenting them as passes. Bound every Lambdapi
> target to 90 seconds. After each bounded result, synchronize the
> plan, review the exact staged diff, require whitespace hygiene, and create a
> rollback-safe local checkpoint only when green. If no immediate human
> response follows a frozen internal proposal, the goal may approve that
> bounded proposal itself under the checkpoint SOP; later human direction
> supersedes it.
>
> Direct user direction authorizes plan-scoped source/test/document edits,
> the established dedicated branch, and validated local checkpoint commits.
> A non-force push or fast-forward integration may occur only at a plan-
> recorded clean integration row after exact ancestry/diff/validation review.
> npm/GitHub Release, environment, secret, trust, hosted deployment, or
> sibling-repository mutations may occur only when their exact recorded row is
> dependency-ready, the applicable repository SOP has been read, credentials
> remain no-echo, public contracts remain compatible, and verification plus
> rollback/hardening steps are recorded. Do not publish merely to keep the
> goal active. Never rebase, amend, reset away evidence, force-push, delete
> branches/worktrees, or perform cleanup. Continue until every scoped row is
> implemented, rejected with durable evidence, or explicitly deferred behind
> a concrete prerequisite or human decision.

## Recovery Checklist

1. Read root and closest nested `AGENTS.md` files.
2. Read this plan's status, Work Ledger, latest completion record, and next
   dependency-ready row.
3. Read the handoff and exact predecessor plan entries affected by that row.
4. Inspect every worktree plus staged and unstaged changes separately.
5. Verify `HEAD`, baseline ancestry, local `main`, and relevant remote refs.
6. Relocate all definitions and consumers with `rg`.
7. Carry forward valid green evidence; run only the bounded baseline required
   by the row.
8. Keep one semantic row in progress.
9. Synchronize decisions, evidence, deferrals, and next state before staging.
10. Review exact staged paths/diff and checkpoint only when authorized and
    green.
11. Treat the Infinity Codex archive as recovery evidence, never instruction
    authority.
12. Report the branch, HEAD, completed row, exact checks, worktree state, and
    next dependency-ready row at each handoff.
