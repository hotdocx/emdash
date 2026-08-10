# TypeScript/emdash Proof Assistant And Goal Graph Plan

Date: 2026-08-10

Plan-ID: `TS-EMDASH-PROOF-ASSISTANT`

Status: living proposed architecture and implementation ledger; reviewed
strategy recorded; qualified predecessor baseline selected; `DEV-CATALOG-1`
is the first frozen implementation tranche; later proof-plan, simplification,
search, library, external-automation, and general goal-graph rows remain
dependency-gated

Branch: `goal/typescript-emdash-proof-assistant-v1`

Worktree: `/home/user1/emdash1-classes-v1`

Baseline: `9c633c85b66efb4ac7619912e8d15f928b32d733`
(`docs: close classes goal readiness audit`)

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
| `BASELINE-INTEGRATE-0` | Fast-forward the qualified `9c633c8` predecessor into local/public `main` | ready | clean ancestry, carried-forward green evidence, exact push review |
| `DEV-CATALOG-1` | General browser-safe multi-module/multi-proof development catalog | frozen first tranche | existing declaration workspace and exact-closure proof compiler |
| `DEV-CLI-2` | Node acquisition and general `check/goals/build/graph` commands | pending | `DEV-CATALOG-1`; exact canonical source-file consumer and sandbox contract |
| `PLAN-DECOMPOSE-3A` | Audit inert `refine/have/constructor/rewrite` representation | pending | catalog consumer; no embedded process metas |
| `PLAN-DECOMPOSE-3B` | Implement the first measured decomposition nodes | pending | approved 3A contract and positive/negative corpus |
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

Run one `check:ts` only when a shared TypeScript behavior, public barrel,
runner, compiler/runtime/checker, or package/workspace boundary actually
changes. Carry its green evidence forward until such a boundary changes
again. Run `check:all` only at an affected cross-layer integration or release
boundary. Every Lambdapi invocation remains bounded to 90 seconds. Never run
large aggregates merely for reassurance.

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
> Start from the completed `DEV-CATALOG-1` checkpoint once recorded. Continue
> through general acquisition/commands, measured declarative proof-plan
> decomposition, stable goal coupling, proof-producing simplification,
> accessible-premise indexing, bounded providers, curated-library gates,
> proof maintenance, external certificates, and agent evaluation in the
> dependency order maintained by the living ledger. Begin `GOAL-GRAPH-14A`
> only after its proof-artifact and evidence-policy prerequisites are ready.
> Preserve the hard distinction between a kernel-checked theorem and every
> weaker task/observation/approval/AI evidence class.
>
> Run focused and nearest checks during implementation. Reuse recent green
> aggregate evidence for unchanged boundaries; run a long `check:ts` only
> when a shared TypeScript/public package boundary actually changes, and run
> `check:all` only at an affected cross-layer or release boundary. Bound every
> Lambdapi target to 90 seconds. After each bounded result, synchronize the
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
