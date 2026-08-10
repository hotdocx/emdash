# TypeScript/emdash Proof Assistant And Goal Graph Plan

Date: 2026-08-10

Plan-ID: `TS-EMDASH-PROOF-ASSISTANT`

Status: living architecture and implementation ledger; reviewed strategy
recorded; qualified predecessor baseline integrated into public `main`;
`DEV-CATALOG-1`, `DEV-CLI-2A`, and `DEV-CLI-2B` implemented and
final-proportional-green under the persistent 2026-08-10 long-aggregate
policy recorded below; `PLAN-DECOMPOSE-3A` audit complete and the bounded
base-plan macro tranche frozen; later template refinement, simplification,
search, library, external-automation, and general goal-graph rows remain
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
ledger checkpoint is `238bddf`.

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
| `DEV-CLI-2C` | Stable `graph` command projection | gated | `GOAL-COUPLING-4`; no ad hoc second graph authority |
| `PLAN-DECOMPOSE-3A` | Audit inert `refine/have/constructor/rewrite` representation | complete | base-plan macro lowering selected; template and equality boundaries separated below |
| `PLAN-DECOMPOSE-3B` | Implement `have`/`constructor` base-plan macros | in progress | frozen 3A contract below; no new plan tag or checker rule |
| `PLAN-DECOMPOSE-3C` | Versioned explicit-placeholder `refine` template | pending | one consumer not expressible by base-plan macros; source/artifact revision decision |
| `GOAL-COUPLING-4` | Stable cross-goal dependency graph | pending | measured dependent-hole consumer and snapshot revision decision |
| `SIMP-5A` | Rewrite/simplifier profile and trace audit | pending | equality/transport owner inventory and termination contract |
| `SIMP-5B` | Deterministic proof-producing simplifier | pending | approved 5A contract |
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
3. A local `have h : T` is also expressible without a new plan tag. For an
   explicitly recorded current target `G`, construct the meta-free cut term

   ```text
   cut(T,G) = λ witness : T,
                λ continue : (Π h : T, G),
                  continue witness

   have h : T := proof; body
     ↦ apply cut(T,G) [proof, intro h body]
   ```

   Correct De Bruijn weakening of `T` and `G` under the generated binders is
   ordinary `kernelShift`; checking and local-context creation remain owned
   by existing `apply` and `intro`. The explicit `G` is not trusted as a
   mutable goal snapshot: replay must still unify the cut result with the
   actual selected goal.
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

### Frozen PLAN-DECOMPOSE-3B contract

Add browser-safe, source-visible authoring macros in the existing
`proof_plan` package boundary:

```text
coreProofPlanConstructor(callee, premises, options?)
  -> CoreProofPlanApply

coreProofPlanHave(binding, target, proof, body, options?)
  -> CoreProofPlanApply
```

1. Publish an immutable `emdash-proof-plan-macros-v1` capability profile.
2. `constructor` delegates exactly to `coreProofPlanApply`; the caller selects
   the constructor handle and supplies all ordered premise plans. Automatic
   constructor search is a later index/provider feature.
3. `have` accepts one `KernelBinder`, an explicit actual-target expectation,
   a proof plan for its type, and a continuation plan. Revision 1 preserves
   the binder's exact plicity and functorial/natural variation.
4. `have` builds the typed cut term above using only `kernelBinder`,
   `kernelPi`, `kernelLambda`, `kernelCall`, `kernelBound`, and `kernelShift`,
   then returns ordinary `apply` with `[proof, intro(body)]`. The continuation
   receives the named local at De Bruijn index zero.
5. The generated root uses the caller's optional ID/provenance. Generated
   binders and calls receive deterministic derived provenance; no callback,
   registry, session, meta, goal lookup, environment lookup, filesystem,
   process state, or backend selection is retained.
6. Output is an ordinary deeply inspectable base-plan tree. Canonical source,
   proof-state, artifact, JSONL, and CLI revisions do not change; serialized
   plans contain only the existing `apply`, `intro`, `exact`, and `hole` tags,
   and traces report those actual primitives.
7. Failures remain ordinary validation/checking failures. A stale or wrong
   target, ill-scoped type, process-local meta, non-type binding, wrong
   constructor, premise mismatch, or malformed binder mode must fail through
   current owners rather than a parallel macro checker.

Focused acceptance covers constructor parity with direct `apply`, complete
and named-open `have`, local-context visibility, natural/functorial variation,
wrong-target and meta rejection, base-tag-only serialization, exact canonical
source round-trip, browser closure, and the packed workspace consumer. Run
the focused proof-plan/source/workspace suites, workspace check, typecheck,
changed-file lint, browser closure, package build/packed consumers, exact diff
review, and whitespace hygiene. Under `D-PA-019`, no long root or repository
aggregate is run unless omitting it becomes progress-blocking.

Non-effects: no new Core expression, proof-plan tag, refiner/checker/session
method, proof/source/artifact revision, declaration or term parser,
constructor discovery, equality/rewrite semantics, theorem import, Lambdapi
source, mathematical owner/rule, Node adapter, CLI, cache/network, MCP/LSP,
print/book, sibling repository, release, registry, or deployment change.
`PLAN-DECOMPOSE-3C` retains general explicit-placeholder refinement;
`SIMP-5A/5B` retains propositional rewriting.

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
| `D-PA-023` | Implement explicit `constructor` and cut-based `have` first; reserve general `refine` for a versioned placeholder template and `rewrite` for the equality/simplifier audit. | The first two have exact generic Core lowerings today; the latter two require contracts that cannot be recovered safely by renaming `apply` or runtime reduction. |

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
