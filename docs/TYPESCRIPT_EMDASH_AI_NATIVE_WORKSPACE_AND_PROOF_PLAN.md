# TypeScript/emdash AI-Native Workspace And Proof Plan

Date: 2026-08-08
Plan-ID: TS-EMDASH-AI-NATIVE
Status: active living proposal and implementation ledger; AI-PROOF-1,
AI-PROOF-2, AI-WORKSPACE-0, AI-WORKSPACE-1A, and AI-WORKSPACE-1B1 are
complete; AI-WORKSPACE-1B2A and AI-WORKSPACE-1B2B are final-green;
AI-REMOTE-1A is final-green; AI-REMOTE-1B0's exact-consumer audit is complete;
the TypeScript-only mounted-workspace/cache adapter AI-REMOTE-1B1 is
final-green; AI-REMOTE-1B2's audit is complete and partitioned; its frozen
local agent command AI-REMOTE-1B2A is final-green; hosted delivery remains
prerequisite-gated; AI-SYNTH-0's exact-consumer inventory is complete and its
frozen, pure-TypeScript AI-SYNTH-1A global-dictionary slice is final-green;
AI-SYNTH-1B remains consumer-gated
Baseline: `5027d5aabca191c088dfd9757a0bb8df4cb04a34` on local `main`
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md`](./TYPESCRIPT_ELABORATOR_V3_2_HANDOFF.md),
[`TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md`](./TYPESCRIPT_ELABORATOR_V3_2_SCALE_QUALIFICATION_PLAN.md),
the completed explicit-Core/checker/session/proof-refiner implementation, and
the active emdash v3.2 authority order under `emdash2/`
Supersedes: no completed mathematical authority, elaborator profile, parser,
or product surface; this plan adds an AI-native source/workspace/proof layer
above them
Persistent-Goal-Workflow:
[`PERSISTENT_GOAL_GIT_EXPERIMENTATION.md`](./PERSISTENT_GOAL_GIT_EXPERIMENTATION.md)
Git-Boundary: completed AI-PROOF/AI-WORKSPACE/AI-REMOTE-1A work is preserved
at local checkpoint `a3ba93a0fcc95434f411d94deca042f47b735c3a` on
`goal/typescript-emdash-ai-native`; the user-authorized one-time fast-forward
placed the same checkpoint on local `main`. Continuation work is again on the
dedicated goal branch in the `~/emdash1` worktree; the final-green
AI-REMOTE-1B2A command is preserved there at local checkpoint `a176ccc`.
The user's standing
unattended authority includes self-approval of a frozen plan tranche and
rollback-safe local checkpoint commits after the persistent-goal Git SOP is
satisfied. It does not authorize another merge, push, PR, publication,
release, deployment, history rewriting, cleanup, branch deletion, or worktree
removal. Existing history and every other worktree must be preserved.

## Executive Decision

The next TypeScript/emdash product abstraction should be an **AI-native proof
document and workspace**, not another stateful tactic server and not another
classical text parser.

The current TypeScript implementation is already substantially aligned with
this direction:

- `src/v3_2/categorical_program.ts` provides typed TypeScript construction and
  immediately lowers callbacks rather than retaining executable semantic
  state;
- `src/v3_2/lf_transfer.ts` defines a backend-neutral serializable module IR
  with module identifiers, dependencies, source hashes, declarations,
  inductives, runtime rules, and proof rules;
- `src/v3_2/proof.ts` provides generic proof-state inspection and a
  failure-atomic `CoreProofRefiner`;
- `src/v3_2/session.ts` provides contextual metavariables, constraints,
  persistent contexts, and transactions; and
- the active scale plan already makes audited typed TypeScript the initial
  mandatory producer while treating textual parsing as an optional
  acquisition adapter rather than the semantic architecture.

The missing product layer is therefore a restricted, serializable and
replayable workspace/proof protocol above explicit Core. It must make source
and derived proof state easy for an AI agent to inspect and edit while keeping
all proof authority in the existing checker and explicit Core term.

The central qualification is important: semantically correct residual goals
cannot in general be recovered merely by reading arbitrary TypeScript.
TypeScript is executable and Turing-complete, and a goal may depend on
reduction, unification, imported definitions, and solved metavariables. The
design must expose two complementary views instead of claiming an impossible
static result:

1. a **declared view**, visible in source through theorem types, structured
   proof steps, stable named holes, and optional expected-goal annotations;
2. a **verified view**, produced deterministically by checking and represented
   as compact, content-addressable text/JSON artifacts.

An agent should normally understand and edit a simple proof by reading the
source alone. When a transition is nontrivial or cached evidence is stale, it
should run one deterministic local command or inspect a derived artifact. No
opaque editor session, long-lived proof-assistant process, or mandatory MCP
round trip belongs in the canonical semantics.

## Goal

Build a source-first TypeScript/emdash environment in which a mathematician or
programmer can direct an AI agent to manage multi-file developments, construct
and refine proofs, inspect stable goal states, and assemble checked research
artifacts. The same canonical workspace files must work locally, in a rich
browser editor, and in remote GetPaidX/LastRevision-style workspaces.

The completed system should make the following workflow ordinary:

```text
mathematician/programmer direction
                 |
                 v
AI edits *.emdash.ts, paper source, and diagram source
                 |
                 v
deterministic acquire -> validate -> elaborate -> check
                 |
        +--------+------------------+
        |                           |
        v                           v
stable proof-state artifacts   explicit checked Core
        |                           |
        +-------------+-------------+
                      v
             paper/browser/publisher
```

The product must remain useful without a text parser, without Lambdapi at
runtime, and without an MCP server. Each of those may remain an optional
adapter or conformance route.

## Non-Goals

This plan does not authorize or imply:

- a new trusted kernel or a new Core term constructor;
- a second mathematical authority beside the active emdash v3.2 development;
- extending the stale root category prototype;
- making arbitrary TypeScript execution trusted;
- recovering verified semantic goals by static inspection of arbitrary host
  code;
- replacing the existing categorical text syntax, browser demo, or Lambdapi
  conformance backend;
- a Lean/Coq-compatible tactic language, language server, or MCP protocol;
- a general Prolog engine or theorem search facility in the first proof-plan
  tranche;
- treating `unif_rule` as a complete typeclass system;
- live network imports during proof checking;
- storing mutable cloud/server state as proof authority; or
- a Git push, merge, publication, release, or deployment.

## Design Principles

### Source is canonical; state is derived

Canonical inputs are ordinary reviewable files. A process-local session,
browser tab, language server, or hosted workspace is never the only location
of a proof decision. Derived state must carry enough fingerprints to prove
which source and dependency versions it describes.

### Explicit Core remains the semantic boundary

Proof plans, workspace manifests, TypeScript builders, synthesis requests,
paper blocks, and browser operations are acquisition or elaboration features.
They must all lower to the existing backend-neutral explicit Core and be
checked there. TypeScript's type system is ergonomic evidence, not dependent
proof authority.

### Easy proofs stay compact

Only mathematically informative names and transitions should need to appear.
An obvious `intro`/`exact` proof must not repeat its entire context and target.
Expected-state annotations are optional and become useful at long or fragile
transitions.

### Difficult proofs remain inspectable

Open goals receive stable, source-level names. Diagnostics and derived state
identify the module, declaration, proof node, goal name, local context,
target, relevant constraint, and source location. Process-local meta ordinals
never become public identity.

### Determinism before automation breadth

The first implementation prefers small explicit constructors, bounded search,
stable ordering, ambiguity errors, and complete traces. A larger search engine
may be added later only behind the same explicit checked-term boundary.

### Transport is optional

Files plus deterministic CLI/JSON form the canonical interface. MCP, LSP,
HTTP, hosted workflows, and browser bridges may expose the same operations but
must not own proof meaning or require a hidden long-lived session.

## Reviewed Baseline

### Direct TypeScript construction

`CoreCategoricalProgram` is explicitly a typed construction API rather than a
text parser. Its callbacks lower immediately through the scoped builder and
are not retained as executable semantic state. This is the correct precedent
for a future `defineModule`/`defineWorkspace` source facade.

### Module representation

`CoreLfModuleSpec` already records:

- `revision`, `moduleId`, and `fragmentId`;
- authority path and source SHA-256;
- canonical-export evidence when present;
- dependencies and external symbols;
- declarations and inductives;
- runtime and proof-time rules; and
- deterministically computed referenced symbols.

The AI-native manager should consume and validate this IR rather than invent a
parallel module model. Additional authoring metadata should either lower into
it or remain clearly non-semantic workspace metadata.

### Proof state and refinement

`CoreProofRefiner` already supports `exact`, `intro`, and `apply` over
session-owned reachable goals. Each tactic is failure-atomic through the
session transaction boundary. It constructs explicit lambdas and generic
calls and delegates all type correctness to `CoreChecker`.

The current `KernelMetaIdentity` intentionally includes a process-local
`symbol`; its numeric ordinal is deterministic only inside one session. This
is correct for the trusted implementation and deliberately unsuitable as a
workspace/public goal ID. The new layer therefore needs a stable source ID to
session-meta mapping without changing the Core identity.

### Product/workspace precedent

The Arrowgram/GetPaidX hybrid workflow already demonstrates the desired outer
shape: canonical workspace files are shared by Codex and a browser editor;
validation is explicit; browser and agent changes are mutually visible;
snapshots separate review points; and build/publication are later explicit
operations. Emdash proof and module artifacts should compose with that model
instead of replacing it with a prover-specific state server.

## Proposed Architecture

```text
*.emdash.ts + workspace manifest + dependency lock
                         |
             restricted acquisition/validation
                         v
          CoreLfModuleSpec + serializable ProofPlan
                         |
              existing elaborator/refiner
                         v
       explicit Core ---> TypeScript checker
              |                 |
              |                 +-- goals/state JSONL
              +-- optional deterministic Lambdapi oracle
```

The architecture has six layers.

### Layer A: declarative TypeScript source

An `.emdash.ts` file exports frozen, serializable data through constructors
such as `defineModule`, `definition`, `theorem`, `by`, and `hole`.

TypeScript remains a convenient authoring metalanguage, but arbitrary host
execution is not trusted. The acquisition phase must reject outputs
containing closures, methods, mutable/cyclic objects, symbols, unsupported
class instances, implicit ambient registries, or other nonserializable state.
Categorical callbacks that remain useful must continue to lower immediately.

A stricter authoring profile should eventually lint or sandbox source files:

- imports restricted to reviewed emdash construction packages and locked
  local modules;
- no filesystem, network, subprocess, clock, random, or environment access;
- no dynamic `require`/`import` for semantic dependencies;
- no top-level mutable registries;
- no retained function values in emitted module/proof data; and
- deterministic validation of the acquired value.

Executing this restricted source is an acquisition step comparable to
compiling a macro. The acquired explicit data, not the arbitrary host
execution, determines the checker input.

### Layer B: workspace and dependency manifest

A workspace manifest should record:

- workspace/profile revision;
- local module roots and deterministic module IDs;
- paper and diagram source roots;
- locked local or remote module references;
- content digests and immutable interface digests;
- selected checker/elaboration policy revision;
- output/snapshot locations; and
- optional publication metadata that has no proof-semantic effect.

Remote modules must be fetched outside checking, stored as immutable local
snapshots, and verified by digest. A module import should name both semantic
identity and content integrity. Live URL resolution must never influence a
checker run.

The initial manager should support only local modules. Remote acquisition is a
later slice after local dependency invalidation and interface hashing are
measured.

### Layer C: serializable proof-plan AST

The first concrete product layer is an immutable tree language interpreted by
`CoreProofRefiner`. Its initial node family is:

```text
exact(term)
intro(name?, body)
apply(callee, premises[])
hole(stableGoalId, expectedState?)
```

Later composition nodes may include `sequence`, `focus`, `all`, `first`, or a
small explicitly bounded combinator family, but they should be added only for
measured consumers. Arbitrary host callbacks must not become retained tactic
state.

Illustrative future source syntax:

```ts
theorem(
  "yoneda_naturality",
  yonedaNaturalityType,
  by(
    intro("F",
      intro("x",
        apply(yonedaStep, {
          naturality: hole(
            "naturality",
            expect({ target: naturalityTarget })
          )
        })
      )
    )
  )
);
```

This example is a design target, not an existing API contract. AI-PROOF-1
begins with lower-level `coreProofPlan*` constructors over current Core
expressions. A later ergonomic facade may provide the compact spelling.

#### Node and goal identity

Intermediate nodes may use deterministic structural paths when an explicit
ID would be noise. Open holes must have explicit stable IDs such as
`naturality`, `base_change`, or `cover_locality`.

During replay, the interpreter maintains a private mapping:

```text
stable source goal ID <-> current session-owned KernelMetaIdentity
```

The mapping is discarded with the session. Only the stable ID is serialized.
Duplicate or invalid IDs fail before semantic refinement.

#### Expected states

`expect` is optional. The initial exact contract may check:

- context depth; and
- an exact zonked Core target.

Later tranches may add named context entries, binder modes, and a
conversion-aware comparison service. Expected states are assertions checked
against the actual goal; they never define or replace it.

An easy transition omits `expect`. A long proof can place an assertion at the
point where a human reviewer or agent benefits from a locally visible
contract.

#### Execution and trust

Replaying a plan:

1. validates plan structure and stable IDs;
2. identifies the explicitly supplied root goal;
3. invokes only existing checked refinements;
4. maps introduced subgoals to ordered child plans;
5. records deterministic source-node trace entries;
6. requires every residual goal to terminate at a named `hole`; and
7. returns the zonked explicit Core term plus a serializable state view.

Each tactic retains current failure atomicity. A failed later node may leave
earlier successful steps available for diagnostics inside that disposable
build session; production builds should create a fresh session for each
replay.

### Layer D: stable proof-state artifacts

The verified state artifact should contain, for every open named hole:

- stable goal ID;
- local context depth;
- ordered local bindings with names, modes, indices, and formatted types;
- formatted target;
- occurrence count and source provenance;
- source/proof-plan fingerprint;
- imported interface hashes;
- compiler/profile/policy revisions; and
- complete, incomplete, or stale status.

No raw JavaScript `symbol`, object identity, closure, or process-local meta ID
may appear. If one open goal depends on another, formatted expressions should
refer to the other stable goal name rather than `?m17`.

The first slice provides deterministic in-memory snapshots and JSON
serialization. Workspace fingerprints and persisted files belong to the
manager slice because the proof-plan module should remain browser-safe and
free of Node filesystem/crypto ownership.

Likely CLI surface:

```text
emdash check
emdash goals [module-or-goal] --format text|jsonl
emdash build
emdash graph
emdash snapshot
```

These are ordinary deterministic artifact operations. They do not require an
interactive prover server.

### Layer E: incremental document manager

The manager should model a workspace as an immutable declaration/module DAG.
A cache key should include:

```text
module source hash
+ imported interface hashes
+ proof-plan/profile/policy revision
+ compiler/checker version
```

Changing one declaration invalidates that declaration and its downstream
consumers, not an unrelated workspace. Diagnostics should remain ordered by
module, declaration, proof-node path, and source location regardless of
parallel evaluation.

This layer can borrow the useful document-model idea from Isabelle/PIDE:
immutable source versions, explicit dependency edges, asynchronous evaluation,
and cached semantic markup. It need not adopt Isabelle's command language or
make a long-running protocol authoritative.

### Layer F: paper, diagram, browser, and hosted integration

Research prose and diagrams should refer to stable semantic declaration IDs
and checked artifact digests. A paper workspace may then render:

- checked source excerpts;
- theorem/proof completion badges;
- selected named goals;
- diagrams tied to declarations or examples; and
- an exact build/snapshot provenance record.

The same files remain editable by Codex and a rich browser. GetPaidX or
LastRevision may use MCP/HTTP/OAuth to move files, validate a workspace, save a
snapshot, build, or publish. Those transports remain outside proof semantics.

## HOL Light, Isabelle, Lean/Coq, And MCP

HOL Light contributes the right trust pattern but not literal static goal
inspection. A HOL Light tactic is executable OCaml of shape `goal ->
goalstate`; the resulting subgoals and justification function appear only
after execution. Emdash should borrow the small-kernel/programmatic-
construction discipline while making the public plan inert and serializable.

Isabelle/PIDE contributes an independently useful document insight: source
versions and dependency graphs can be immutable while semantic checking runs
incrementally and asynchronously. Emdash should borrow that artifact model,
not its entire proof language or editor protocol.

Lean/Coq integrations commonly expose goal state through language servers,
RPC, or newer MCP adapters. MCP itself is only a transport. The AI-native
criterion is therefore not an ideological ban on MCP; it is that no MCP
server owns the only current state or becomes necessary to reconstruct proof
meaning. A future adapter may expose `emdash goals` through MCP without
changing the canonical file/CLI/JSON contract.

Primary references:

- HOL Light tactic types and justifications:
  <https://github.com/jrh13/hol-light/blob/master/tactics.ml>
- Isabelle/PIDE document model:
  <https://arxiv.org/abs/1905.01735>
- Lambdapi Elpi/typeclass continuation:
  <https://github.com/Deducteam/lambdapi/pull/1378>
- earlier Lambdapi Elpi proof of concept:
  <https://github.com/Deducteam/lambdapi/pull/418>

## Typeclass And Synthesis Architecture

Three mechanisms must remain distinct:

1. runtime rewriting and definitional computation;
2. proof-time unification rules that transform stuck equality problems; and
3. instance/dictionary synthesis involving indexed, scoped search.

Lambdapi's `unif_rule` machinery rewrites a failed comparison into new
comparison constraints. It does not by itself provide instance enumeration,
recursive premise search, priority, scoping, ambiguity detection, or
coherence. Lambdapi PR 1378's separate Elpi-backed solver and dedicated
class/instance machinery reinforce this distinction; PR 418 remains useful
historical proof-of-concept evidence rather than a production contract.

The TypeScript product should eventually expose a backend-neutral elaboration
request of the conceptual form:

```text
synth(Class, parameters, lexical/module scope)
```

Resolution must produce an explicit dictionary/record term before Core
checking. The checker and Core remain typeclass-unaware.

The first resolver, when separately consumer-gated, should provide only:

- exact-head indexed instances;
- lexical and explicitly imported module scopes;
- explicit priorities with deterministic ordering;
- bounded depth/fuel;
- recursive premise resolution after required metas become known;
- ambiguity errors instead of silent first-match behavior; and
- a complete machine-readable resolution trace.

An Elpi process could later be an optional search provider. Every returned
term must be checked by the TypeScript kernel, and the provider must not become
the only repository of instance state.

Typeclass use needs particular care for categories, functors, displayed
structures, and coherence witnesses. Multiple structures on the same carrier
can affect normal forms and mathematical intent. Prefer local canonical
instances, explicit scopes, ambiguity errors, and explicit disambiguation in
published sources. Do not hide an active categorical owner choice behind
unbounded global search.

## Trust And Reproducibility Boundary

The intended trust chain is:

```text
untrusted/restricted TypeScript acquisition
                 |
                 v
validated immutable module/proof data
                 |
                 v
existing elaborator/refiner -> explicit Core
                 |
                 v
TypeScript checker
                 |
                 +-- deterministic derived artifacts
                 |
                 +-- Lambdapi differential oracle until recorded graduation
```

The following are not proof authority:

- TypeScript compile-time types;
- proof-plan expected-state annotations;
- cached JSON without matching fingerprints;
- browser UI state;
- an MCP response;
- a hosted workspace database;
- a tactic/search trace; or
- a paper rendering.

The checked explicit Core term and its validated environment remain the
product result. Lambdapi retains its existing conformance/specification role
at every boundary recorded by the active elaborator plans.

## Implementation Strategy

### AI-PROOF-1: immutable plan and stable holes

This first bounded slice is implemented and final-green. It adds:

- a new browser-safe `src/v3_2/proof_plan.ts` module;
- immutable `exact`, `intro`, `apply`, and named `hole` plan nodes;
- deterministic structural node paths with optional explicit node IDs;
- preflight validation of IDs and plan shape;
- replay through `CoreProofRefiner` without new checker semantics;
- optional exact expected context depth and target assertions;
- stable hole-to-session-meta mapping;
- deterministic trace and state snapshots with no serialized session symbol;
- stable meta names in formatted open-goal expressions; and
- public export plus focused tests.

The slice explicitly does not add filesystem management, a CLI, remote
modules, hashing, typeclasses, arbitrary tactic callbacks, Core nodes, checker
branches, categorical cases, Lambdapi changes, or a parser.

Reject or split this design if any of the following occurs:

- implementing a plan requires retaining executable callbacks;
- stable state requires changing `KernelMetaIdentity` itself;
- replay bypasses `CoreProofRefiner` or the checker;
- a failed tactic loses its current transaction guarantee;
- serialization exposes a `symbol` or unstable meta ordinal;
- apply-subgoal mapping silently ignores or invents a proof obligation; or
- generic implementation requires an emdash category-owner case.

### AI-PROOF-2: artifact and CLI qualification

AI-PROOF-2 is complete. It:

- puts fresh theorem-root creation behind a browser-safe proof-document
  compiler;
- defines JSONL diagnostics and immutable proof-artifact/state revisions;
- accepts validated source/profile/dependency fingerprints as browser-safe
  data while keeping hash computation and I/O in the Node CLI;
- adds `./scripts/emdash goals` and `./scripts/emdash check` over one local
  direct-TypeScript module;
- rejects stale artifacts before presenting them as current; and
- provides one compact complete identity and one intentionally named
  incomplete identity.

### AI-WORKSPACE-0: local workspace inventory

AI-WORKSPACE-0 is complete. Its read-only inventory:

- inventory current `CoreLfModuleSpec`, acquisition, mixed-program, and
  browser consumers;
- distinguish semantic module data, source-authoring metadata, compiled
  artifacts, and process-local execution state;
- measure existing dependency, linkage, ordering, interface-digest, and
  invalidation contracts;
- identify the smallest missing declarative workspace value and its trust
  boundary; and
- freezes the split AI-WORKSPACE-1A/1B acceptance tests before adding
  behavior.

### AI-WORKSPACE-1A: local declaration-module graph

AI-WORKSPACE-1A is complete. It:

- defines the smallest frozen semantic module/policy/linkage source unit and
  declaration-workspace plan;
- validates serializability and deterministic dependency-first declaration
  order;
- compiles a local graph through exact existing dependency interfaces;
- detects missing, duplicate, cyclic, and inconsistent module dependencies;
- reports only the changed module and its conservative dependency closure;
  and
- exposes canonical source/interface/workspace/closure/invalidation text for
  an outer hashing adapter.

### AI-WORKSPACE-1B: fragment and proof-document composition

The read-only audit partitioned this row at an existing trust boundary.

#### AI-WORKSPACE-1B1: exact-closure proof attachment

AI-WORKSPACE-1B1 is complete. It:

- derive and recompile exactly one selected module's dependency closure;
- reject any proof fingerprint whose module IDs differ from that closure;
- compile the proof document in the closure-only Core environment;
- retain the existing explicit-Core proof profile and fresh-root compiler;
  and
- return portable closure text plus the ordinary proof artifact without
  persisting a compiled workspace or checker session.

#### AI-WORKSPACE-1B2: explicit fragment and mixed-phase graph

The executable audit partitions this row again rather than conflating a
same-source fragment chain with a cross-module multi-provider graph.

##### AI-WORKSPACE-1B2A: exact same-module fragment chain

AI-WORKSPACE-1B2A is final-green. It:

- freeze a portable fragment identity distinct from module identity and
  compiled-object identity;
- require every `earlier-fragment` external symbol to name its exact source
  provider rather than infer one from order or spelling;
- plan declaration, runtime, and proof phases against the existing exact
  compiled dependency and prefix contracts;
- compose declaration, runtime, and proof artifacts for one pinned source
  module in exact source order without flattening compiled-object lineage;
  and
- keep filesystem hashing, cache writes, arbitrary path loading, and remote
  acquisition in explicit outer adapters.

##### AI-WORKSPACE-1B2B: cross-module fragment graph

AI-WORKSPACE-1B2B is final-green. It:

- combine 1B2A fragment chains with 1A module dependency graphs;
- compose exact ordered declaration providers into module interfaces without
  weakening public/protected/private visibility;
- name exact runtime providers in dependency-module order; and
- preserve per-module closure reconstruction and contamination tests before
  admitting remote snapshots.

### AI-REMOTE-1: locked remote snapshots

The audit partitions AI-REMOTE-1. AI-REMOTE-1A is final-green: it owns locked
canonical graph-source materialization and an immutable offline cache-entry
format without performing transport or storage. AI-REMOTE-1B0's platform
consumer audit and AI-REMOTE-1B1's TypeScript-only mounted-file/immutable-
cache adapter and AI-REMOTE-1B2A's explicit-root local command are final-green.
Hosted packaging/template delivery, real network fetch, authentication, and
platform HTTP/MCP adapters remain separately prerequisite-gated.

- define remote identity separately from content location;
- fetch outside checking;
- require content and interface integrity digests;
- cache an immutable local snapshot;
- support offline deterministic rebuilds; and
- prove changed remote content under an old lock is rejected.

### AI-SYNTH-1: explicit dictionary synthesis

The completed AI-SYNTH-0 inventory partitions this row. AI-SYNTH-1A is a
closed global-dictionary selection primitive over an explicit finite list of
qualified, already checked declarations. It has one structure-generated
capability consumer and returns an ordinary checked Core reference. It does
not scan an environment, execute `unif_rule`, recurse through premises, assign
priorities, retain callbacks, or know about source syntax.

AI-SYNTH-1B remains the authoring/workspace integration row: it must decide
how source declarations opt into candidate scopes, how local binders and
implicit synthesis requests are represented, and how those choices enter a
portable workspace snapshot. Indexed recursive premises, search tiers,
priorities, fuel beyond the finite-candidate measure, and any external Elpi
provider remain AI-SYNTH-2 and require another real consumer.

### AI-PAPER-1: research-workspace integration

- bind paper/diagram blocks to stable declaration IDs and artifact digests;
- render checked and incomplete states intentionally;
- synchronize agent and browser edits through canonical files;
- keep snapshot, build, publication, and deployment explicit; and
- exercise one local and one hosted-style workspace without changing proof
  authority.

## Work Ledger

Only one row may be in progress in this worktree.

| Row | State | Depends on | Exact outcome |
| --- | --- | --- | --- |
| AI-NATIVE-PLAN-0 | complete | reviewed current code/plans | This dedicated architecture, trust boundary, ledger, and recovery route exist. |
| AI-PROOF-1 | complete | existing proof/session/checker APIs | Immutable proof plans replay `exact`/`intro`/`apply`, expose named holes and stable serializable state, and pass focused/proportional gates. |
| AI-PROOF-2 | complete | AI-PROOF-1 | Fresh-root compilation, state schema/fingerprints, JSONL and local goal/check commands are qualified. |
| AI-WORKSPACE-0 | complete | AI-PROOF-1, AI-PROOF-2 | Existing module/acquisition consumers and missing workspace contracts are measured without behavior change. |
| AI-WORKSPACE-1 | partitioned | AI-WORKSPACE-0, AI-PROOF-2 | The local graph is split at the measured declaration-only versus fragment/runtime/proof boundary. |
| AI-WORKSPACE-1A | complete | AI-WORKSPACE-0 | A browser-safe declaration-only, one-fragment-per-module graph checks, serializes, and reports conservative dependency-closure invalidation deterministically. |
| AI-WORKSPACE-1B | partitioned | AI-WORKSPACE-1A, AI-PROOF-2 | The audit separates exact-closure explicit-Core proof attachment from same-module fragment/runtime/proof lineage. |
| AI-WORKSPACE-1B1 | complete | AI-WORKSPACE-1A, AI-PROOF-2 | Fresh proof documents compile in a rechecked exact module closure, require the exact closure fingerprint module set, and persist no process-local checker/workspace state. |
| AI-WORKSPACE-1B2 | partitioned | AI-WORKSPACE-1B1 | The audit separates a pinned same-module source chain from cross-module multi-provider composition. |
| AI-WORKSPACE-1B2A | complete | AI-WORKSPACE-1B1 | Exact provider identities drive one deterministic declaration/runtime/proof fragment chain for one pinned source module. |
| AI-WORKSPACE-1B2B | complete | AI-WORKSPACE-1B2A | Fragment chains compose through exact source-node identities, multi-provider dependency interfaces, explicit dependency runtimes, stable topological order, and portable local snapshots. |
| AI-REMOTE-1 | partitioned | AI-WORKSPACE-1B2B | Separate pure locked materialization/offline cache data from real transport and persistent cache ownership. |
| AI-REMOTE-1A | complete | AI-WORKSPACE-1B2B | Exact content lock plus canonical graph-source reconstruction, local compilation, compiled-snapshot verification, and immutable offline cache entry; no fetch or store. |
| AI-REMOTE-1B | partitioned | AI-REMOTE-1A plus exact hosted/local consumer | Separate the measured platform boundary, a TypeScript-only mounted-file/cache-store adapter, and any later authenticated network adapter. |
| AI-REMOTE-1B0 | complete | AI-REMOTE-1A plus `~/closerfans` workspace runtime | The exact GetPaidX/LastRevision/CloserFans consumer and its mounted-project, persistent-data, Git-snapshot, browser/MCP, and authentication boundaries are measured without changing either repository. |
| AI-REMOTE-1B1 | complete | AI-REMOTE-1B0 | Fixed canonical lock/source files under explicit mounted roots are verified by TypeScript, installed under an identity-derived atomic no-replace cache key, and fully reverified offline. |
| AI-REMOTE-1B2 | partitioned | AI-REMOTE-1B1 plus command and hosted consumers | Separate the runnable local agent command from hosted package/template delivery, whose runtime and distribution prerequisites are not yet met. |
| AI-REMOTE-1B2A | complete | AI-REMOTE-1B1 plus existing `./scripts/emdash` seam | The explicit-root `workspace check` namespace emits compact JSONL/text reports over the TypeScript mounted store while preserving existing proof commands exactly. |
| AI-REMOTE-1B2B | pending | distributable emdash runtime plus compatible hosted Node/template contract | Select package/source delivery, supported Node version, template-owned install, agent skill, and generic platform source capability before changing `~/closerfans` or claiming hosted availability. |
| AI-REMOTE-1B3 | pending | stable authenticated/public transport consumer | If a real consumer requires it, freeze a separate supplied-byte HTTPS/platform adapter with explicit timeout, redirect, authentication, and retry policy; signed URLs remain ephemeral acquisition inputs. |
| AI-SYNTH-0 | complete | AI-REMOTE-1B2A plus exact user-facing consumer | The checker/session, proof `unif_rule`, structure/adjunction metadata, active explicit-witness mathematics, and candidate authority were audited; the first executable consumer and resolver boundary are frozen below. |
| AI-SYNTH-1 | partitioned | AI-SYNTH-0 | Separate closed checked global selection from source/workspace integration and any later recursive indexed search. |
| AI-SYNTH-1A | complete | AI-SYNTH-0 plus structure-generated capability consumer | An explicit finite qualified-symbol scope selects zero, one, or multiple checked global dictionaries deterministically and emits only a rechecked explicit Core reference plus a complete trace. |
| AI-SYNTH-1B | pending | AI-SYNTH-1A plus source/workspace consumer | Freeze portable instance annotations, local scopes/binders, and an implicit-synthesis surface request without teaching Core or the checker about typeclasses. |
| AI-SYNTH-2 | pending | AI-SYNTH-1B plus recursive indexed consumer | Only if demanded, design recursive premise search, tiers/priorities/fuel, and a separately identified external-provider interface. |
| AI-PAPER-1 | pending | AI-PROOF-2, AI-WORKSPACE-1B2B | One canonical paper/diagram/proof workspace supports agent/browser editing and checked snapshots. |
| AI-NATIVE-GRADUATE-1 | pending | all accepted rows | Trust, determinism, stale-state, offline, browser, and conformance claims are synchronized and accurately documented. |

## Decision Ledger

| Decision | State | Decision |
| --- | --- | --- |
| D-AI-NATIVE-001 | accepted by direct user direction | Make TypeScript/emdash source, proof, and workspace operations AI-native for agent-authored developments. |
| D-AI-NATIVE-002 | accepted architecture | Add the AI-native layer above existing explicit Core/checker/refiner; do not add a new kernel. |
| D-AI-NATIVE-003 | accepted architecture | Distinguish declared source state from verified derived state; do not claim arbitrary TypeScript provides semantic goals statically. |
| D-AI-NATIVE-004 | accepted architecture | Use inert serializable proof-plan nodes and stable named holes rather than retained tactic callbacks. |
| D-AI-NATIVE-005 | accepted architecture | Keep files plus deterministic CLI/JSON canonical; allow MCP/LSP/HTTP only as outer transport adapters. |
| D-AI-NATIVE-006 | accepted architecture | Reuse `CoreLfModuleSpec` as the semantic module boundary and add only authoring/workspace metadata around it. |
| D-AI-NATIVE-007 | accepted architecture | Keep runtime rewriting, proof-time unification, and instance synthesis separate. |
| D-AI-NATIVE-008 | accepted architecture | Instance resolution, if selected, elaborates to explicit dictionaries and remains outside Core/checker trust. |
| D-AI-NATIVE-009 | accepted implementation sequence | Implement proof plans before the workspace manager and typeclass search. |
| D-AI-NATIVE-010 | accepted for AI-PROOF-1 | Expected targets use exact zonked Core equality; conversion-aware expectations require a separately measured generic comparison API. |
| D-AI-NATIVE-011 | accepted and qualified by AI-PROOF-2 | A browser-safe proof-document compiler owns fresh session/checker/root creation; callers never supply or persist a root meta. |
| D-AI-NATIVE-012 | accepted and qualified by AI-PROOF-2 | The persisted artifact schema accepts validated `sha256:` source/profile/dependency fingerprints as data; only the Node CLI computes hashes or performs I/O. |
| D-AI-NATIVE-013 | accepted and qualified by AI-PROOF-2 | JSONL is the canonical machine output: one proof record followed by ordered goal records. Human text is an optional rendering of the same artifact. |
| D-AI-NATIVE-014 | accepted and qualified by AI-PROOF-2 | The first local consumer is one direct-TypeScript module with a complete identity and an intentionally named incomplete identity; it is not a general workspace manager. |
| D-AI-NATIVE-015 | accepted and qualified by AI-PROOF-2 | `./scripts/emdash check|goals` is the first file-native command seam; MCP, a daemon, automatic artifact writes, and arbitrary module loading remain deferred. |
| D-AI-NATIVE-016 | accepted and qualified by AI-WORKSPACE-1A | A workspace source unit wraps existing frozen module, policy, and linkage data; it does not invent a second declaration AST or retain authoring callbacks. |
| D-AI-NATIVE-017 | accepted and qualified by AI-WORKSPACE-1A | The first executable graph is browser-safe, declaration-only, and one fragment per module. Stable topological order is by dependency then module ID, independent of input array order. |
| D-AI-NATIVE-018 | accepted and qualified by AI-WORKSPACE-1A | Compile through one persistent declaration environment and exact existing dependency interfaces; do not duplicate declaration checking or visibility semantics. |
| D-AI-NATIVE-019 | accepted and qualified by AI-WORKSPACE-1A | Canonical source, interface, workspace, and dependency-closure text are hash inputs, not browser-computed hashes. Node/filesystem adapters remain outside the graph. |
| D-AI-NATIVE-020 | accepted and qualified by AI-WORKSPACE-1A | First invalidation is a conservative deterministic dependency closure over exact source-bundle drift; it reports reuse boundaries but does not claim incremental execution or semantic no-op detection. |
| D-AI-NATIVE-021 | accepted split after AI-WORKSPACE-0 | Same-module fragments, runtime/proof phases, proof-document attachment, cache writes, and remote loading belong to AI-WORKSPACE-1B or later rather than hidden special cases in the declaration graph. |
| D-AI-NATIVE-022 | accepted split after AI-WORKSPACE-1B audit | Exact-closure proof attachment is AI-WORKSPACE-1B1; explicit same-module fragment and mixed-phase lineage is AI-WORKSPACE-1B2. |
| D-AI-NATIVE-023 | accepted and qualified by AI-WORKSPACE-1B1 | Recompile the selected module's exact dependency closure before proof checking so unrelated earlier modules in the global workspace environment cannot become undeclared proof dependencies. |
| D-AI-NATIVE-024 | accepted and qualified by AI-WORKSPACE-1B1 | The proof fingerprint must name exactly every module in the selected closure. SHA-256 values remain caller-supplied validated data; the browser-safe layer does not pretend to verify content hashes it cannot compute. |
| D-AI-NATIVE-025 | accepted and qualified by AI-WORKSPACE-1B1 | Retain the existing explicit-Core `CoreChecker` proof profile. An LF delta/runtime-aware checker needs a distinct artifact profile identity and is not smuggled through an execution callback. |
| D-AI-NATIVE-026 | accepted boundary for AI-WORKSPACE-1B2 | `earlier-fragment` availability identifies a relation but not its source provider. A fragment workspace must add explicit source-level provider identity before composing exact compiled runtime artifacts. |
| D-AI-NATIVE-027 | accepted and qualified by AI-WORKSPACE-1B1 | Persist the closure snapshot/text and ordinary proof artifact only; closure compilation objects, environments, checked terms, and sessions remain reconstructible process-local results. |
| D-AI-NATIVE-028 | accepted and qualified by AI-WORKSPACE-1B2A | Qualify one pinned same-module fragment chain as AI-WORKSPACE-1B2A before combining it with cross-module multi-provider interfaces in AI-WORKSPACE-1B2B. |
| D-AI-NATIVE-029 | accepted and qualified by AI-WORKSPACE-1B2A | Portable fragment identity is the exact module ID, fragment ID, module revision, policy revision, and linkage revision tuple; compiled runtime/proof identities remain derived evidence rather than source references. |
| D-AI-NATIVE-030 | accepted and qualified by AI-WORKSPACE-1B2A | Every `earlier-fragment` external names exactly the source fragment that locally provides it. Provider order is checked separately and never substitutes for provider identity. |
| D-AI-NATIVE-031 | accepted and qualified by AI-WORKSPACE-1B2A | All fragments belong to one module, authority path, source hash, dependency view, and canonical-export view, and their existing command orders form nonoverlapping strictly increasing ranges. |
| D-AI-NATIVE-032 | accepted and qualified by AI-WORKSPACE-1B2A | Once a runtime exists, every later fragment explicitly names the latest source fragment that locally produced the exact runtime closure; omission, branching, or inherited-only provider aliases fail closed. |
| D-AI-NATIVE-033 | accepted and qualified by AI-WORKSPACE-1B2A | The first executable profile admits nonempty declaration-only fragments and non-inductive mixed declaration/runtime/proof fragments. Pure runtime/proof fragments, inductives, compiler callbacks/oracles, and cross-module dependencies remain explicit later rows. |
| D-AI-NATIVE-034 | accepted and qualified by AI-WORKSPACE-1B2B | A cross-module source node is identified by module ID, authority/source/export pins, ordered dependency IDs, chain revision/profile, and the complete ordered list of exact fragment identities. No graph edge names a compiled object. |
| D-AI-NATIVE-035 | accepted and qualified by AI-WORKSPACE-1B2B | Every direct source dependency carries the exact source-node identity of its provider. Module order is a deterministic topological consequence and never substitutes for that edge identity. |
| D-AI-NATIVE-036 | accepted and qualified by AI-WORKSPACE-1B2B | Dependency symbols are checked through the provider module's existing multi-fragment compiled interface. Per-symbol graph edges do not duplicate interface visibility, linkage, type, or environment checks. |
| D-AI-NATIVE-037 | accepted and qualified by AI-WORKSPACE-1B2B | Every direct dependency with a local runtime has one explicit exact final local runtime-fragment source identity, in source dependency order. Transitive flattening and diamond deduplication remain owned by the existing runtime composer. |
| D-AI-NATIVE-038 | accepted and qualified by AI-WORKSPACE-1B2B | Reuse one internal fragment-chain compiler with explicit dependency interfaces and runtime inputs, but retain separate public profile identities: qualified 1B2A continues to reject dependency modules. |
| D-AI-NATIVE-039 | accepted and qualified by AI-WORKSPACE-1B2B | In the cross-module graph profile, free declarations must be local `earlier-fragment` or exact `dependency-module` externals. `existing-core` is restricted to intrinsic Core-owner linkage, preventing unrelated global free declarations from contaminating a node. |
| D-AI-NATIVE-040 | accepted and qualified by AI-WORKSPACE-1B2B | The first graph is local, browser-safe, and reconstructive. Canonical source/compiled snapshots are hash inputs; hashing, invalidation, incremental execution, filesystem/cache/remote acquisition, and proof-document profile expansion remain later rows. |
| D-AI-NATIVE-041 | accepted split after AI-REMOTE-1 audit | AI-REMOTE-1A qualifies content locking, canonical materialization, and immutable offline cache data without transport/storage; AI-REMOTE-1B separately owns real fetch and persistent cache adapters. |
| D-AI-NATIVE-042 | accepted and qualified by AI-REMOTE-1A | The remotely transferable unit is canonical AI-WORKSPACE-1B2B source-snapshot text. TypeScript modules, callbacks, environments, compiled classes, and generated backend text are not remote source authority. |
| D-AI-NATIVE-043 | accepted and qualified by AI-REMOTE-1A | Remote artifact identity includes logical workspace ID, workspace revision, source/compiled snapshot profile revisions, exact UTF-8 byte length, source SHA-256, and expected compiled-snapshot SHA-256. Transport locations are structurally separate and non-authoritative. |
| D-AI-NATIVE-044 | accepted and qualified by AI-REMOTE-1A | A browser-safe contract validates lock/location/cache shapes and canonically reconstructs graph source. A Node-owned materializer computes SHA-256 over supplied text; it performs no fetch, path read, cache write, or credential handling. |
| D-AI-NATIVE-045 | accepted and qualified by AI-REMOTE-1A | An immutable cache entry contains the exact artifact identity and canonical source text. Offline use revalidates identity, bytes, source hash, reconstruction, compilation, and compiled hash every time; it never trusts a stored digest or compiled object. |
| D-AI-NATIVE-046 | accepted and qualified by AI-REMOTE-1A | Only canonical serializer output is accepted. Source drift, alternate JSON encoding, workspace/profile drift, compiled-output drift, cache poisoning, or location-as-identity all fail closed. |
| D-AI-NATIVE-047 | accepted and qualified as an AI-REMOTE-1A non-effect | Persistent storage keys, eviction, atomic writes, concurrent population, HTTP policy, redirects, authentication, retries, signed URLs, and platform workspace APIs remain explicit AI-REMOTE-1B decisions. |
| D-AI-NATIVE-048 | accepted by direct user direction | Reuse recent green aggregate evidence for every unchanged boundary. Run another long repository aggregate only when the exact diff changes a shared boundary and the repository SOP strictly requires it; focused and nearest tests are the normal loop. |
| D-AI-NATIVE-049 | accepted by direct user direction | In an unattended continuation, the agent may approve a frozen proposed tranche itself and continue. It may make local rollback-safe checkpoint commits only after a clean transition to the dedicated goal branch/worktree and every checkpoint condition in the Git SOP; no external Git or publication mutation is implied. |
| D-AI-NATIVE-050 | accepted by direct user direction for this checkpoint only | Commit the completed current AI-native tranche on its dedicated local goal branch, then fast-forward local `main` to the exact reviewed checkpoint while retaining the branch as recovery evidence. Do not infer push or later merge authority. |
| D-AI-NATIVE-051 | accepted after exact-consumer audit | CloserFans, GetPaidX, and LastRevision are surfaces of the single `~/closerfans` platform repository. That platform owns sessions, authentication, mounted workspace transport, attachment transport, source authorization, Git snapshots, and publication; emdash must not duplicate those concerns inside proof semantics. |
| D-AI-NATIVE-052 | accepted after exact-consumer audit | The first real consumer is an in-container AI agent with persistent `/work/project` and `/work/data` mounts. Its first emdash adapter consumes fixed files below caller-supplied absolute roots; platform HTTP/MCP APIs are not the semantic or storage interface. |
| D-AI-NATIVE-053 | accepted and qualified by AI-REMOTE-1B1 after direct user clarification | AI-REMOTE-1B1 uses only the self-contained TypeScript backend. It reconstructs, checks, compiles, and revalidates backend-neutral explicit Core locally and neither invokes nor requires Lambdapi. The architecture continues to admit Lambdapi/emdash as a separately gated optional backend and conformance oracle; the present focus does not remove that route. |
| D-AI-NATIVE-054 | accepted and qualified by AI-REMOTE-1B1 | The persistent cache key is SHA-256 of the canonical artifact-identity serialization. The store never accepts a caller-selected cache key, never stores compiled process objects, and never treats a path, mirror, timestamp, ETag, or observed digest as authority. |
| D-AI-NATIVE-055 | accepted and qualified by AI-REMOTE-1B1 | Cache population uses a same-directory, fsynced temporary file and an atomic no-replace hard-link installation. Existing entries are fully reverified and byte-compared, never overwritten; concurrent identical population converges, while conflicts and symlinks fail closed. |
| D-AI-NATIVE-056 | accepted and qualified as an AI-REMOTE-1B1 non-effect | AI-REMOTE-1B1 has no fetch, redirect, retry, credential, environment, current-working-directory, Git, MCP, platform API, eviction, mutable cache, background daemon, Lambdapi, or publication behavior. Those concerns remain outer or separately consumer-gated. |
| D-AI-NATIVE-057 | accepted and qualified by AI-REMOTE-1B2A | Preserve `./scripts/emdash check|goals` by byte-compatible argument forwarding. The shell wrapper dispatches only an exact leading `workspace` namespace to a separate asynchronous Node adapter; no unified stateful command server is introduced. |
| D-AI-NATIVE-058 | accepted and qualified by AI-REMOTE-1B2A | `workspace check` requires explicit absolute project/data roots, defaults to one compact deterministic JSONL verification record, supports optional human text and explicit offline mode, and exposes no source text, compiled object, absolute path, credential, or platform token. |
| D-AI-NATIVE-059 | accepted and qualified as an AI-REMOTE-1B2A non-effect | The command is a projection of AI-REMOTE-1B1 verified results. It performs no discovery, lock regeneration, source authoring, fetch, authentication, Git snapshot, MCP call, daemon state, Lambdapi invocation, backend selection, cache mutation beyond 1B1, or publication. |
| D-AI-NATIVE-060 | accepted deferral after hosted-template audit | Hosted emdash template delivery is not yet a truthful executable consumer: the root package is private, has no `bin`/published files contract, depends on development-time `ts-node`, and declares Node 22.13+, while current GetPaidX workspace-controller variants use Node 20 and generic source capabilities remain deferred. AI-REMOTE-1B2B must select a distributable runtime and compatible template contract before cross-repository implementation. |
| D-AI-NATIVE-061 | accepted and qualified by AI-REMOTE-1B2A after direct user clarification | AI-REMOTE-1B2A reports the TypeScript/emdash backend actually executed. A future Lambdapi/emdash backend can implement a separately identified command/backend adapter over the same backend-neutral locked source; no current CLI flag may claim an unimplemented backend. |
| D-AI-NATIVE-062 | accepted after AI-SYNTH-0 audit | Ordinary flex-rigid/metavariable solving, ordered proof-time `unif_rule` transformation, and dictionary synthesis solve different problems. A synthesis resolver must not enumerate proof rules or reinterpret first-match equality transformation as instance choice. |
| D-AI-NATIVE-063 | accepted after AI-SYNTH-0 audit | The first candidate scope is the caller's complete explicit finite list of exact qualified symbols. Candidate terms and types come only from the checked `CoreLfMixedDeclarationBaseContext`; spelling, environment iteration, fragment order, callbacks, and caller-asserted types provide no authority. |
| D-AI-NATIVE-064 | accepted after AI-SYNTH-0 audit | The first executable consumer is a structure-macro-generated capability carrier with checked global capability values passed explicitly to an ordinary implicit binder. An `Adjunction R L F G` witness is the first mathematical follow-up once its pure-TypeScript dependency graph is available; existing duplicate adjunction witnesses already establish that ambiguity must be an error. |
| D-AI-NATIVE-065 | accepted and frozen for AI-SYNTH-1A | AI-SYNTH-1A accepts one closed meta-free target and only installed free declarations, canonicalizes exact candidate identity, validates each candidate independently with a fresh bounded `CoreLfChecker`, and terminates after the finite candidate list. It has no local binders, recursive premises, priorities, backtracking, runtime/proof program, ambient registry, or source/workspace annotation. |
| D-AI-NATIVE-066 | accepted and frozen for AI-SYNTH-1A | Zero matching candidates is a structured missing error, one returns a deeply frozen explicit checked Core reference and complete deterministic trace, and multiple matches are a structured ambiguity error listing every match. Input order and duplicates cannot silently choose a winner. Core, the checker, and backend semantics remain typeclass-unaware. |
| D-AI-NATIVE-067 | accepted and frozen for AI-SYNTH-1A | The present resolver executes only the pure TypeScript/emdash backend. Its result is backend-neutral explicit Core, so a future separately profiled Lambdapi/emdash conformance or execution adapter remains possible without entering the current trusted path. |

## AI-PROOF-2 Inventory And Exact Contract

Date: 2026-08-08

The read-only inventory found:

- no current product factory owns theorem-root creation; `freshMeta` plus
  `CoreProofRefiner` construction appears only in tests and isolated internal
  proof-engine operations;
- current public demos put reusable behavior in browser-safe `src/v3_2`
  modules and keep `examples/*.ts` as thin Node launchers;
- `src/v3_2/browser.ts`, `browser_directed.ts`, and `browser_reviewer.ts` are
  explicit narrow barrels, so a Node CLI need not enter a browser closure;
- data-level `sha256:` validation and module source hashes already belong to
  transfer contracts, while actual `node:crypto` computation lives in
  scripts/tests; and
- deterministic backend-neutral Core serialization already exists separately
  from source provenance and backend syntax.

Selected architecture:

1. `src/v3_2/proof_document.ts` remains browser-safe. It validates a fixed
   AI-proof profile and fingerprint schema, creates a fresh
   `CoreElaborationSession`/`CoreChecker`, checks that the theorem target
   inhabits `TYPE`, creates the sole root meta, executes the plan, rechecks a
   completed term, and returns a versioned artifact. It accepts hashes as
   immutable data and imports no Node builtin.
2. The artifact revision records module/declaration identity, compiler/profile
   revisions, source/profile/dependency fingerprints, proof state, and the
   canonical explicit Core serialization only when complete.
3. Artifact freshness is an exact comparison against a newly constructed
   current fingerprint. Source/profile/dependency drift raises a structured
   stale-artifact error before the artifact is displayed as current.
4. JSONL revision 1 emits one ordered proof record and then one record per
   named open goal. It contains no raw meta identity, `symbol`, closure, or
   process state.
5. `src/v3_2/ai_proof_demo.ts` is the first direct-TypeScript local module. It
   shares one checked declaration environment between two independently fresh
   theorem compilations: `complete_identity` and `open_identity` with stable
   hole `body`.
6. `src/v3_2/ai_proof_cli.ts` is explicitly Node-owned. It reads and hashes
   the local module source, hashes the frozen profile descriptor, compiles one
   selected declaration, validates freshness, and emits JSONL or optional
   text. `examples/v3_2_ai_native_proof_cli.ts` remains a thin process adapter,
   and `./scripts/emdash` supplies the initial `check`/`goals` command seam.

The first command contract is:

```text
./scripts/emdash check [declaration] [--format jsonl|text]
./scripts/emdash goals [declaration] [--format jsonl|text]
```

Defaults select the complete declaration for `check` and the incomplete
declaration for `goals`. `check` returns nonzero for an incomplete selected
proof; `goals` reports zero or more goals without treating incompleteness as a
command failure. Unknown commands, declarations, or formats fail closed.

This tranche deliberately does not load arbitrary TypeScript paths, write a
cache, define a workspace manifest, compute browser-side cryptographic hashes,
add package dependencies, change browser barrels, or claim remote/offline
module management. Those belong to AI-WORKSPACE-0/1 after this exact local
consumer proves the artifact boundary; AI-WORKSPACE-0 subsequently split the
first graph from fragment/proof composition.

Reject or split the implementation if fresh-root construction remains in the
CLI/demo, if the browser-safe module imports a Node builtin, if a stale stamp
can pass as current, if an incomplete proof is serialized as checked Core, or
if command execution requires a retained checker session.

## AI-WORKSPACE-0 Inventory And Frozen AI-WORKSPACE-1A Contract

Date: 2026-08-08

### Existing source and compilation layers

The read-only inventory found a strong semantic substrate but no graph owner:

1. `CoreLfModuleSpec` is already the correct backend-neutral semantic module
   value. It records revision, module/fragment identity, logical authority
   path, source and optional canonical-export hashes, ordered module imports,
   exact external-symbol availability, declarations, inductives, runtime
   rules, proof rules, and derived referenced symbols. Creation validates and
   deeply freezes the full representation.
2. `CoreLfTransferScopedBuilder` is an authoring convenience, not retained
   semantics. Its HOAS-like callbacks execute once and lower to explicit
   locally nameless transfer data. A workspace must consume the resulting
   module value rather than store a builder or callback.
3. Policy and non-semantic linkage are already separate frozen companions.
   The linkage is exact for every local declaration and external symbol;
   policy is exact for every selected source item. A workspace source unit
   should therefore be the existing `(module, policy, linkage)` triple, not a
   duplicate declaration language.
4. `compileCoreLfDeclarations` already performs all declaration checking,
   source visibility, intrinsic-owner conformance, persistent-environment
   extension, transparent-delta validation, and final environment audit.
   `CoreLfCompiledDeclarationModule` is an immutable executable artifact with
   methods and environment identity; it is not persistence data.
5. `CoreLfCompiledModuleInterface` already enforces public/protected/private
   exposition while retaining the provider's complete environment behind the
   interface. A consumer must receive the exact interface for each declared
   dependency module; general terms cannot use protected/private entries.
6. Runtime fragments and mixed modules have distinct exact dependency
   contracts. They distinguish dependency-module from earlier-fragment
   lineage, enforce import order, retain fragment identity, and reject cycles
   or raw-runtime ambiguity. They cannot safely be inferred from the plain
   module-ID graph.
7. Canonical Lambdapi acquisition is intentionally Node-owned because it
   reads supplied source/export text, parses it, and computes SHA-256. Its
   adjacent selection-contract creator is browser-safe. A browser-safe
   workspace must accept already validated specs/stamps as data rather than
   acquiring files itself.
8. The repository contains 73 `createCoreLfModuleSpec` call sites across 41
   source files and fifteen module-local `cachedCompilation` variables. These
   caches memoize fixed reviewed profiles by process identity; they do not
   form a keyed workspace cache, expose invalidation, or provide portable
   artifacts.
9. Root exports are broad while browser entry points are explicit narrow
   closures. None currently imports the LF workspace/compiler modules
   directly. A new reusable graph can remain browser-safe without silently
   becoming a browser product API.

### Missing ownership

No current value or service:

- owns a set of source modules and rejects duplicate module identity;
- resolves missing imports or computes a whole-graph cycle witness;
- produces input-order-independent topological compilation order;
- serializes an exact source bundle, compiled interface, workspace snapshot,
  or transitive module closure as canonical hash input;
- maps a changed source/policy/linkage bundle to the affected dependent
  closure; or
- connects a portable workspace snapshot to the proof-document fingerprint
  contract.

`CoreLfModuleSpec.dependencies` validates identifiers, duplicates, self
imports, and per-symbol dependency declarations, but it cannot validate
whether another module exists or whether a multi-module graph is acyclic.
Compiled interfaces have checked source exposition but no canonical digest.
The existing process caches have no input key. These are the precise gaps;
the checker, compiler, acquisition parser, runtime composer, and proof refiner
do not need replacement.

### First executable contract

AI-WORKSPACE-1A will add one browser-safe module whose accepted source is:

```text
workspace revision
  + frozen declaration-only CoreLfModuleSpec
  + its exact frozen policy
  + its exact frozen declaration linkage
```

The bounded profile permits one fragment per module ID. It rejects inductive,
runtime, or proof content and rejects multiple same-module fragments. This is
an evidence-based slice: declaration dependencies can already be compiled by
threading one persistent `CoreLfDeclarationEnvironment` and exact compiled
interfaces, whereas same-module fragments and runtime/proof phases require
additional explicit lineage inputs.

Planning must:

- reject an empty/invalid workspace revision, duplicate module ID, missing
  dependency, foreign policy/linkage, unsupported content, and a deterministic
  whole-graph cycle;
- compute dependency-first order with module-ID lexical tie-breaking, so
  permuting the input array cannot change compilation or serialization;
- preserve the source-declared order of each module's dependencies and
  declarations; and
- freeze all returned plan and diagnostic data.

Compilation must:

- start from `CoreLfDeclarationEnvironment.empty()`;
- compile in the planned order through `compileCoreLfDeclarations` only;
- pass only exact already compiled direct-dependency interfaces while using
  the accumulated persistent environment as checking substrate;
- create the existing `CoreLfCompiledModuleInterface` for each result; and
- retain no checker session, callback, filesystem handle, or mutable registry.

Portable output will have five canonical newline-terminated JSON forms:

1. a source-bundle record for one exact `(module, policy, linkage)` triple;
2. an own-interface record containing source identity and every compiled
   declaration's visibility, link, status, serialized type, and optional
   serialized checked body;
3. a workspace snapshot in dependency-first order; and
4. a transitive closure snapshot for one root module, also dependency-first;
   and
5. a structured conservative invalidation report.

Canonicalization sorts object keys and preserves semantically ordered arrays.
It rejects functions, symbols, non-finite numbers, cycles, and other
non-JSON state. It uses the existing provenance-free explicit-Core
serialization for types/bodies. These strings are stable **hash inputs**;
AI-WORKSPACE-1A does not compute or claim a cryptographic digest.

The first invalidation comparison is deliberately conservative. It compares
canonical source bundles between two valid snapshots, marks added/removed or
changed modules directly, and then marks only their transitive dependents in
the union graph. Unrelated branches remain reusable. It does not yet claim
that a source edit with an extensionally unchanged interface avoids dependent
rechecking, nor does it execute an incremental cache.

### Frozen acceptance matrix

AI-WORKSPACE-1A is accepted only if focused tests establish:

- the same provider/consumer declaration graph compiles identically from two
  different input-array orders;
- the consumer is checked against the exact existing public interface and
  accumulated environment;
- source, own-interface, whole-workspace, and root-closure serializations are
  byte-identical across repeat builds and contain no process-local symbol or
  session state;
- missing dependency, duplicate module ID, cycle, foreign companion, and
  non-declaration/multiple-fragment profiles fail with structured paths;
- a changed provider invalidates that provider and its consumer but not an
  independent sibling; and
- the new browser-safe transitive closure contains no Node builtin or
  acquisition adapter.

Reject or split this tranche if it needs to duplicate declaration checking,
guess a runtime fragment provider, execute an arbitrary source path, hash in
the browser-safe graph, persist a compiled class/session, or describe
conservative dependency invalidation as incremental compilation.

### AI-WORKSPACE-0 completion

The inventory changed no behavior. It selected D-AI-NATIVE-016 through
D-AI-NATIVE-021, partitioned AI-WORKSPACE-1 at the existing compiler boundary,
and made AI-WORKSPACE-1A the sole active row. Its proportional evidence is the
exact documentation diff, relative-link audit, and whitespace check; no
TypeScript, kernel, browser, print, book, or aggregate gate is triggered by
the inventory itself.

## AI-WORKSPACE-1A Completion Record

Date: 2026-08-08

Hypothesis: a useful multi-file/module development boundary can be added
without another parser, checker, registry, or server by planning existing
frozen LF source triples and delegating compilation to the current checked
declaration pipeline.

Result: accepted for the bounded declaration-only, one-fragment-per-module
profile.

Implementation:

- added browser-safe `src/v3_2/lf_workspace.ts` with explicit profile,
  structured errors, and no Node, filesystem, hashing, Lambdapi, or cache
  dependency;
- `defineCoreLfDeclarationWorkspaceModule` freezes one exact existing
  `(CoreLfModuleSpec, policy, linkage)` source unit without introducing a
  second declaration AST or retaining a builder callback;
- `createCoreLfDeclarationWorkspace` rejects invalid/empty revisions,
  foreign companions, unsupported inductive/runtime/proof content, missing
  imports, duplicate module IDs/multiple fragments, and deterministic graph
  cycles;
- planning is independent of input-array order: a stable Kahn ready queue uses
  lexical module-ID tie-breaking, while a separately deterministic DFS
  supplies a readable cycle witness;
- `compileCoreLfDeclarationWorkspace` starts from the existing empty
  persistent LF environment, threads that immutable environment through the
  planned order, and passes only exact already compiled direct-dependency
  interfaces to `compileCoreLfDeclarations`;
- no visibility, intrinsic-owner, typechecking, definition checking, delta,
  or dependency-link semantics are duplicated in the workspace layer;
- canonical newline-terminated JSON is available for the exact source unit,
  own compiled interface, whole workspace, transitive root closure, and
  invalidation report;
- canonicalization sorts record keys, preserves semantic array order, uses
  provenance-free explicit-Core serialization for checked types/bodies, and
  rejects functions, symbols, non-finite numbers, cycles, class instances,
  and other nonportable state;
- persisted workspace snapshots are revalidated against source/interface
  identities, exact dependency data, and a reconstructed canonical plan
  before closure extraction or comparison;
- invalidation detects source-bundle or compiled-interface drift, additions,
  and removals, then propagates only through the union dependency graph;
  unrelated siblings remain reusable; and
- the invalidation record states `executesIncrementally: false`: it is a
  deterministic reuse diagnostic, not a hidden mutable cache or incremental
  compiler claim.

Focused evidence:

```text
node --require ts-node/register --test \
  tests/v3_2_lf_workspace_tests.ts \
  tests/v3_2_lf_transfer_tests.ts \
  tests/v3_2_lf_transfer_compiler_tests.ts \
  tests/v3_2_lf_transfer_visibility_tests.ts \
  tests/v3_2_browser_directed_tests.ts

42 tests / 6 suites: 42 passed, 0 failed, 0 skipped
```

After the stable-ready-order and snapshot-hardening audit, the final nearest
rerun covered the changed graph plus exact visibility and browser closure:

```text
node --require ts-node/register --test \
  tests/v3_2_lf_workspace_tests.ts \
  tests/v3_2_lf_transfer_visibility_tests.ts \
  tests/v3_2_browser_directed_tests.ts

20 tests / 3 suites: 20 passed, 0 failed, 0 skipped
```

The eight workspace cases cover input-order-independent compilation,
lexically stable ready-module order, exact dependency interfaces, byte-stable
source/interface/workspace/closure artifacts, deep freezing, exclusion of
process-local state, conservative source and interface invalidation,
add/remove handling, independent-sibling reuse, missing/duplicate/cyclic
graphs, deterministic cycle text, foreign companions, the one-fragment
boundary, runtime-content rejection, nonportable data, malformed snapshots,
and unknown closure roots. The browser-directed suite adds one transitive
closure case that reaches the LF compiler/visibility/declaration substrate
while excluding the Node acquisition adapter and proof CLI.

Static and aggregate evidence:

```text
./scripts/pnpmw run workspace:check
  passed: pnpm 11.16.0; root + emdash2 + print; Node 24.11.1

./scripts/pnpmw run typecheck
  passed

changed-file ESLint
  passed

browser-safe Node-builtin source scan
  passed

git diff --check
  passed before completion-ledger synchronization

./scripts/pnpmw run check:ts
  workspace contract, typecheck, complete ESLint, and root tests passed
  1,453 tests / 220 suites: 1,400 passed, 53 opt-in skips, 0 failed
  observed root-test duration: 1,604,747 ms
```

This is an observed aggregate footer, not a count reconstruction. Its nine
new tests are the eight-case workspace suite plus one case in the existing
browser-directed suite.

No Core node, checker branch, LF compiler rule, categorical owner, Lambdapi
source, browser product barrel, package, dependency, lockfile, print/book
surface, remote protocol, cache writer, or publication boundary changed. No
kernel, browser build, print, book, or `check:all` gate was therefore
required.

Decision consequences:

- D-AI-NATIVE-016 through D-AI-NATIVE-020 now have direct implementation,
  determinism, rejection, serialization, and invalidation evidence;
- the AI-facing source of truth is ordinary frozen TypeScript data, while
  compiled classes/environments remain reconstructible process-local
  execution artifacts and canonical snapshots remain portable hash inputs;
- dependency visibility and mathematical validity remain owned by the
  existing compiler/checker rather than by the workspace graph; and
- at the AI-WORKSPACE-1A checkpoint, AI-WORKSPACE-1B became the sole active
  row and began with a read-only audit. The following audit and completion
  records preserve its later 1B1/1B2 split.

## AI-WORKSPACE-1B Audit And Frozen 1B1 Contract

Date: 2026-08-08

The audit found two different problems hidden in the original
AI-WORKSPACE-1B row. They do not share the same ready implementation
boundary and must not be forced into one abstraction.

The existing runtime and mixed-phase APIs identify compiled fragments by the
exact tuple `(moduleId, fragmentId, compiled revision)` and retain the exact
compiled dependency objects used to form a runtime closure. By contrast, an
LF source external symbol whose availability is `earlier-fragment` records
only that some prior fragment of the same module provides it. It does not name
that provider. Inferring the provider from array order, symbol spelling, or a
currently compiled object would make the portable source graph ambiguous and
would prevent deterministic reconstruction. Multiple compiled declaration
providers for one module and mixed declaration/runtime/proof programs are
already supported by lower layers, but a workspace above them therefore needs
an explicit source-level fragment/provider identity first. That design is the
separate AI-WORKSPACE-1B2 tranche.

Proof attachment has a smaller ready boundary. AI-PROOF-2 already owns a fresh
session and root meta, stable named holes and traces, explicit-Core rechecking,
and a portable proof artifact. AI-WORKSPACE-1A already owns a checked local
declaration graph and canonical module/interface/closure snapshots. The two
can be composed without changing either checker.

One subtlety makes direct attachment to the compiled workspace environment
unsound as a dependency-accounting operation. The declaration compiler
threads one persistent environment through the global deterministic order.
Consequently, the environment captured after a module can contain an
unrelated independent module that happened to sort earlier. The LF compiler
correctly prevents the module source from importing that declaration, but a
new proof checked directly in the accumulated environment could mention it.
Its fingerprint would then under-report a real free dependency.

AI-WORKSPACE-1B1 therefore freezes the following contract:

1. The input selects one existing declaration-workspace module and supplies
   an ordinary proof-document identity, explicit Core target, inert proof
   plan, provenance, and already constructed proof fingerprint.
2. The attachment layer derives the selected module's complete transitive
   closure, including the selected module itself, from the canonical checked
   workspace snapshot.
3. It constructs a new declaration-workspace plan from exactly those frozen
   source triples and recompiles that closure from an empty LF environment.
   This is deliberate validation, not a cache lookup or incremental compiler.
4. Every recompiled source and interface text must equal the corresponding
   text in the supplied compiled workspace. Any mismatch is rejected as
   closure drift before proof checking.
5. The canonical fingerprint is revalidated, and its dependency module IDs
   must equal the complete closure module-ID set exactly. Missing the selected
   module, omitting a transitive dependency, or adding an unrelated module is
   an error. Duplicate IDs remain rejected by the existing fingerprint
   constructor. The `interfaceSha256` values are caller-supplied stamps: this
   browser-safe layer validates their form and coverage but does not claim to
   compute or authenticate them.
6. The proof document is compiled with the selected module's environment from
   the closure-only recompilation. The proof profile remains the existing
   explicit-Core `CoreChecker` profile. LF delta/runtime-aware proof checking,
   if later justified, requires a distinct artifact/profile identity rather
   than an unrecorded checker callback.
7. The portable result contains a profile/revision marker, the source
   workspace revision, selected root module, canonical closure snapshot and
   closure text, and the ordinary AI-PROOF-2 artifact. Recompiled workspace
   objects, LF/Core environments, checker sessions, metas, and checked term
   objects are process-local derived results only.
8. The module remains browser-safe. It performs no filesystem access,
   cryptographic hashing, remote loading, cache writes, arbitrary-path
   execution, Lambdapi invocation, runtime-fragment inference, or MCP state
   management.

The bounded negative-test contract is equally important:

- input workspace permutation must produce byte-identical portable output;
- a complete proof over a dependency closure must recheck, while an open proof
  must expose only stable named state;
- missing or extra fingerprint module IDs must fail before proof execution;
- a declaration available only from an unrelated earlier module must remain
  unavailable in the closure-only proof environment;
- reconstructed source/interface drift must fail rather than silently attach
  a proof to a different closure;
- serialized output must contain no session, raw meta identity, class
  instance, or process-local environment; and
- the transitive browser import closure must not acquire Node-only proof CLI,
  filesystem, or hashing adapters.

This contract accepts recomputation as the smallest trustworthy composition.
It does not claim content-hash verification, incremental execution, or a full
multi-fragment development manager. Those are separately visible outer or
later boundaries rather than conveniences hidden in the proof path.

## AI-WORKSPACE-1B1 Completion Record

Date: 2026-08-08

Hypothesis: AI-PROOF-2 can attach to a checked AI-WORKSPACE-1A module without
granting the proof accidental access to unrelated modules in the global
compile order, duplicating either checker, or persisting process-local state.

Result: accepted for the explicit-Core, declaration-workspace profile.

Implementation:

- added browser-safe `src/v3_2/lf_workspace_proof.ts` with a distinct
  `emdash-lf-workspace-proof-v1` profile and structured errors;
- `compileCoreLfWorkspaceProofDocument` derives the selected root's canonical
  transitive closure from the checked workspace snapshot, rebuilds a plan
  from exactly those frozen source triples, and recompiles it from an empty
  LF environment;
- every reconstructed module must preserve canonical order and match the
  original compiled module's source and interface text before proof checking;
- the canonical proof fingerprint must name exactly the closure module set,
  including the selected root; both missing and unrelated module IDs fail
  before proof-plan execution;
- caller-supplied interface stamps remain validated data, not a false claim
  that browser-safe code computed or authenticated a cryptographic hash;
- the ordinary AI-PROOF-2 compiler receives only the selected module's
  closure-only `CoreDeclarationEnvironment`, retains its fresh session/root
  and plain `CoreChecker` profile, and remains the sole proof-state authority;
- the portable wrapper contains only version/profile identity, original
  workspace revision, selected root, canonical closure snapshot/text, and the
  ordinary proof artifact; and
- reconstructed workspace/environment objects and the optional checked term
  remain process-local compilation results outside serialization.

The five-case focused suite proves complete and named-open proof attachment,
input-permutation byte stability, exact fingerprint coverage, exclusion of an
unrelated lexically earlier module, reconstructed source drift, reconstructed
interface drift, deep freezing, and absence of raw session/meta/environment
state. The existing browser-directed suite adds a transitive import-closure
case that reaches the declaration compiler, proof compiler, and Core checker
but not the Node CLI or LF acquisition adapter.

Focused and static evidence:

```text
node --require ts-node/register --test \
  tests/v3_2_lf_workspace_proof_tests.ts \
  tests/v3_2_lf_workspace_tests.ts \
  tests/v3_2_lf_transfer_tests.ts \
  tests/v3_2_lf_transfer_compiler_tests.ts \
  tests/v3_2_lf_transfer_visibility_tests.ts \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_proof_document_tests.ts \
  tests/v3_2_browser_directed_tests.ts

62 tests / 9 suites: 62 passed, 0 failed, 0 skipped

./scripts/pnpmw run typecheck
changed-file ESLint
git diff --check
  passed
```

Shared-boundary aggregate evidence on the final reviewed code:

```text
./scripts/pnpmw run check:ts
  workspace contract, typecheck, complete ESLint, and root tests passed
  1,459 tests / 221 suites: 1,406 passed, 53 opt-in skips, 0 failed
  observed root-test duration: 1,597,995 ms
```

This is a directly observed footer. The six-test increase over the recorded
AI-WORKSPACE-1A aggregate is the five-case 1B1 suite plus one case in the
existing browser-directed suite.

No Core node, checker/refiner branch, LF declaration/visibility/runtime/proof
compiler, semantic owner, Lambdapi source, browser product barrel, parser,
package, lockfile, print/book surface, cache/remote protocol, or publication
boundary changed. No kernel, browser product build, print, book, or
`check:all` gate was therefore required.

Decision consequences:

- D-AI-NATIVE-023 through D-AI-NATIVE-025 and D-AI-NATIVE-027 now have direct
  success, rejection, determinism, contamination, portability, and aggregate
  evidence;
- a globally accumulated compile environment is explicitly not a proof
  dependency boundary; exact closure reconstruction is;
- the result remains honest about caller-supplied hash stamps and about
  recomputation rather than claiming content authentication or incrementality;
  and
- at the AI-WORKSPACE-1B1 checkpoint, AI-WORKSPACE-1B2 became the sole active
  row. The following audit preserves its later 1B2A/1B2B split.

## AI-WORKSPACE-1B2 Audit And Frozen 1B2A Contract

Date: 2026-08-08

The executable audit confirms that the lower layers already own the semantic
operations needed for a source-separated fragment chain:

- `CoreLfCompiledRuntimeFragment` gives each local runtime the exact derived
  identity `(moduleId, fragmentId, compiled revision)`, retains direct
  dependency relations, and flattens transitive execution prefixes only by
  exact compiled-object lineage;
- `compileCoreLfRuntimeFragment` validates dependency-module order,
  same-module `earlier-fragment` relations, cycles, duplicate identities, and
  conflicting artifacts before checking a local runtime program;
- `CoreLfMixedDeclarationContext` preserves a persistent declaration view
  over initial providers plus source-prior declaration phases;
- `planCoreLfMixedPhases` and `compileCoreLfMixedPhases` partition one source
  fragment by existing command order and delegate every declaration,
  inductive-signature, runtime, and proof phase to its current compiler;
- `CoreLfCompiledModuleInterface.fromCompiled` can retain multiple exact
  declaration providers for one module without merging their environments;
  and
- `composeCoreLfProofPrograms` preserves exact source programs, strict global
  proof-rule order, source-time runtime prefixes, one completed runtime, one
  queue/session, and one explicit comparison budget.

What is absent is not another compiler. It is a portable source graph that
can reconstruct those exact object relations. The source IR currently marks
an external merely as `earlier-fragment`; source order can prove that a
provider is prior, but cannot identify which fragment supplies the symbol.
Likewise, the runtime compiler accepts an exact compiled fragment object,
while persisted source needs a stable identity from which that object can be
rebuilt. A wrapper that stores the compiled object, infers the provider from
the nearest order, or names only `(moduleId, fragmentId)` would fail under
revision/policy/linkage drift.

The audit also separates two dimensions. A same-module fragment chain has one
pinned source/dependency view and a linear command order. A cross-module graph
must additionally compose multiple declaration providers into each imported
module interface, retain visibility, select exact dependency-module runtime
providers, and reconstruct a module closure without unrelated environment
contamination. The former is ready as 1B2A; the latter is 1B2B.

AI-WORKSPACE-1B2A therefore freezes this bounded contract:

1. A portable source fragment identity is the exact tuple of module ID,
   fragment ID, module revision, policy revision, and linkage revision.
   References copy this data; they never retain a source or compiled object.
2. One workspace contains fragments of one module and one pinned authority
   path, source SHA-256, empty dependency view, and canonical-export view.
   Fragment IDs and full identities are unique.
3. Existing command `order` values determine the canonical fragment order.
   Every fragment is nonempty, its command orders remain those validated by
   `CoreLfModuleSpec`, and ranges across fragments are strictly increasing and
   nonoverlapping. Input-array order has no meaning.
4. The first profile admits declaration-only fragments and mixed fragments
   containing at least two of declaration, runtime, and proof content.
   Inductives, pure runtime/proof fragments, arbitrary compiler-option
   callbacks, subject-reduction/proof oracles, and cross-module dependencies
   fail closed rather than becoming hidden special cases.
5. Every source external marked `earlier-fragment` has exactly one explicit
   `(symbol, provider identity)` entry. That provider must be prior, must
   locally compile the symbol, and must preserve the exact declaration link.
   Existing-Core externals have no provider entry; dependency-module
   externals are outside this same-module profile.
6. Runtime lineage is explicit and linear. Before the first local runtime no
   runtime provider is accepted. Once a runtime exists, every later fragment
   names the latest source fragment that locally produced it. A missing,
   stale, forward, inherited-only, or non-latest provider fails. A new local
   runtime is compiled with that exact prior compiled fragment and becomes the
   next provider.
7. Declaration-only fragments delegate to `compileCoreLfDeclarations` in the
   persistent mixed declaration context. Mixed fragments delegate to the
   existing mixed planner/compiler with the exact initial declaration context
   and runtime provider. No declaration, visibility, runtime, proof, or
   conversion rule is reproduced in the workspace.
8. Local proof programs are retained in global source order and composed once
   against the final declarations and completed exact runtime using
   `composeCoreLfProofPrograms`. Existing proof composition rejects source-pin,
   order, runtime-prefix, duplicate-rule, or budget drift.
9. Portable source and compiled snapshots retain identities, source bundles,
   provider edges, declaration-interface data, runtime/proof revisions and
   rule IDs, and final composed summaries. Environments, compiled classes,
   sessions, callbacks, and object identities stay process-local.
10. The implementation remains browser-safe and does no hashing, filesystem
    access, acquisition, cache write, remote load, Lambdapi execution, or
    incremental build.

The initial negative matrix must cover input permutation, missing/extra/
forward/stale external providers, a provider that does not locally own the
symbol, missing/non-latest/non-runtime runtime providers, overlapping command
orders, source-pin drift, dependency-module content, unsupported pure or
inductive fragments, duplicate identities, and serialized process-state
leakage. A positive vertical slice must compile at least three fragments,
carry declarations into later source, execute a runtime closure across a
fragment boundary, and compose proof programs under the final runtime.

AI-WORKSPACE-1B2B remains separately gated and begins with the read-only audit
below. Its active status is not permission to generalize 1B2A by silently
admitting dependency modules or by treating all globally earlier declarations
as an imported module interface.

## AI-WORKSPACE-1B2A Completion Record

Date: 2026-08-08

Hypothesis: exact source-level provider identities can reconstruct and compile
one pinned module's declaration/runtime/proof fragment chain through the
existing checked LF engines, without retaining process objects or inferring a
provider from global order.

Result: accepted for the bounded same-module fragment profile.

Implementation:

- added browser-safe `src/v3_2/lf_fragment_workspace.ts` with the explicit
  `emdash-lf-same-module-fragment-workspace-v1` profile and the portable
  identity tuple `(moduleId, fragmentId, moduleRevision, policyRevision,
  linkageRevision)`;
- validates and canonically orders nonoverlapping source ranges independently
  of input-array order, reconstructs each existing module/policy/linkage
  companion, and rejects a fabricated or noncanonical plan before compiling;
- maps every `earlier-fragment` external to an exact earlier source identity,
  then verifies that the compiled provider locally owns the symbol and that
  provider and consumer declaration linkage agree exactly;
- requires the latest source fragment that locally produced the runtime
  closure to be named after runtime begins, rejecting missing, stale,
  forward, inherited-only, or non-latest runtime providers;
- delegates declaration-only fragments to `compileCoreLfDeclarations`, mixed
  fragments to `compileCoreLfMixedPhases`, declaration visibility to the
  existing interface engine, runtime lineage to the existing runtime
  compiler, and final proof composition to `composeCoreLfProofPrograms`;
- composes all local proof programs once against the final declaration context
  and exact completed runtime, while preserving each source-time prefix; and
- serializes canonical portable source and compiled snapshots containing
  source bundles, exact provider edges, declaration-interface summaries,
  runtime/proof revisions and rule IDs, and final composed summaries, but no
  environments, compiled classes, sessions, callbacks, object identities,
  filesystem handles, or computed hashes.

The positive witness contains three fragments of one pinned module: a base
declaration fragment; a runtime/proof fragment; and a later
declaration/runtime/proof fragment. It carries declarations across both
boundaries, reduces through the two-fragment runtime closure, and solves a
later proof goal through the globally composed proof program. The negative
matrix rejects missing, extra, stale, forward, and non-owning providers;
linkage drift; missing and wrong runtime providers; duplicate or overlapping
fragments; source-pin drift; fabricated plans; pure unsupported fragments;
and dependency-module content. Source and compiled snapshot text is
byte-identical across input permutations and contains no process state.

Qualification:

- the nearest declaration/workspace/proof/runtime/visibility/browser matrix
  passed 69 tests across eight suites: 68 active passes, one intentional
  opt-in skip, and zero failures;
- root typecheck, changed-file ESLint, and `git diff --check` passed; and
- the required complete `./scripts/pnpmw run check:ts` passed 1,467 tests
  across 222 suites: 1,414 active passes, 53 intentional skips, and zero
  failures, in 1,631,078.601346 ms.

No Lambdapi source, active mathematical policy, browser product entry,
filesystem/remote adapter, lockfile, package graph, kernel, or trusted-Core
boundary changed. The next row is the separately gated AI-WORKSPACE-1B2B
cross-module provider-graph audit; this completion does not authorize its
design by extrapolation.

## AI-WORKSPACE-1B2B Audit And Frozen Contract

Date: 2026-08-08

The read-only audit found that the semantic compilers already expose the
required cross-module ingredients:

- `CoreLfCompiledModuleInterface.fromCompiled` accepts multiple exact
  declaration providers of one module, retains their complete checked
  environments, rejects duplicate symbols, and exposes one immutable
  public/protected/private interface;
- `CoreLfDependencyAccess` checks ordinary dependency uses against an exact
  interface, including environment membership, declaration linkage, checked
  type, exclusion state, and the distinction between general terms and
  protected runtime patterns;
- `compileCoreLfMixedPhases` accepts exact dependency interfaces and explicit
  dependency-module runtime fragments and passes them uniformly through
  declaration, runtime, and proof phases;
- `compileCoreLfRuntimeFragment` validates direct dependencies in the source
  module's dependency order, requires dependency modules before same-module
  prior fragments, rejects cycles and rule-ID collisions, and flattens
  transitive runtime diamonds once by exact compiled-artifact identity; and
- the final local runtime fragment already carries the complete imported plus
  same-module execution closure, while retaining its direct dependency edges.

The absent component is therefore a portable source graph, not another
declaration, visibility, runtime, or proof compiler. The graph must reconstruct
which source module supplies an interface and which exact source fragment
supplies each imported runtime. A module ID alone is insufficient under
source, policy, linkage, or fragment-order drift; a compiled interface or
runtime object is process-local and cannot be persisted.

The audit also exposed a contamination path that must be closed at this new
profile boundary. Existing declaration compilation accepts an initial
environment plus source-classified externals. A malicious source could label
an unrelated free declaration `existing-core` and find it in a globally
earlier environment. For 1B2B, `existing-core` therefore means an intrinsic
`core-owner` link only. Ordinary free names must be exact dependency-module
externals or same-module earlier-fragment externals. This lets one persistent
topological environment remain an implementation detail without granting
undeclared imports.

AI-WORKSPACE-1B2B freezes this first executable contract:

1. A graph contains at least two source modules. Each module contains one or
   more nonempty fragments under the already qualified declaration-only or
   non-inductive mixed content restrictions. At least one positive witness
   uses multiple fragments; single-fragment declaration nodes remain valid so
   the graph genuinely subsumes the 1A case.
2. Fragments of one node share module ID, authority path, source SHA-256,
   canonical-export evidence, and the same ordered dependency-module view.
   Their existing command ranges are unique, nonoverlapping, and strictly
   increasing. Input module and fragment array order is irrelevant.
3. A portable module-node identity copies the module ID, authority/source/
   export pins, ordered dependency IDs, chain revision and profile revision,
   and the complete ordered list of five-field fragment identities. It
   contains no object reference or newly computed digest.
4. Every direct dependency has one explicit provider-node identity exactly
   equal to the graph node named by the source dependency. Missing, extra,
   stale, foreign, duplicate, cyclic, or order-substituted edges fail before
   compilation. Canonical edge order is the source dependency order;
   deterministic module execution order is a stable topological sort with
   module-ID tie-breaking.
5. Every direct dependency node that locally produces a runtime has one
   explicit runtime-provider entry naming that node's exact latest local
   runtime-producing fragment identity. A dependency with no local runtime
   accepts no runtime entry. Missing, extra, inherited-only, stale, or
   non-latest identities fail closed.
6. All dependency-module free declarations are resolved through the exact
   compiled provider-node interface. That interface may contain multiple
   declaration fragments and remains the sole owner of visibility, linkage,
   type, and provider-environment checks. The graph does not add per-symbol
   dependency edges or flatten providers into a new declaration artifact.
7. `existing-core` externals in this profile must use `core-owner` linkage.
   Free-declaration linkage is admitted only for exact dependency-module or
   same-module earlier-fragment externals. This invariant is checked before
   any node compiles and receives an unrelated-module contamination test.
8. One shared internal chain compiler receives the accumulated declaration
   context, exact direct dependency interfaces, and exact direct dependency
   runtime fragments. It then delegates each source phase as in 1B2A. The
   public 1B2A constructors, profile, snapshots, and rejection of dependency
   modules remain unchanged.
9. Imported runtime fragments are supplied in source dependency order, then
   the current same-module runtime provider. The existing composer owns
   transitive flattening and diamond deduplication. A node's final local
   runtime and proof composition use the exact completed closure; a node with
   no local runtime may still check against its imported closure.
10. Canonical graph source and compiled snapshots retain module/fragment
    identities, exact dependency and runtime-provider edges, per-chain
    source/compiled summaries, interfaces, and final runtime/proof summaries.
    They retain no environment, class instance, session, callback, object
    identity, filesystem handle, or browser-computed hash.
11. The graph layer remains browser-safe and performs no path loading,
    hashing, cache write, remote fetch, Lambdapi execution, or incremental
    build. Snapshot invalidation belongs to the next evidence-driven row
    rather than being guessed here.

The minimum positive matrix will use a provider module whose interface spans
multiple declaration fragments and whose runtime is produced later, plus a
consumer module that imports public declarations from both providers, checks
a local rule against the imported runtime, and composes a local proof program.
An unrelated topologically earlier module must remain unavailable. Negative
tests will cover every graph identity/edge failure above, protected/private
general-term access, dependency/runtime order drift, runtime diamond conflict
or deduplication as applicable, input permutation stability, fabricated plan
reconstruction, and serialized process-state leakage.

This contract does not yet authorize remote identities, content acquisition,
automatic caching, semantic incremental reuse, general proof-document
checking under LF delta/runtime conversion, inductive fragments, pure runtime
fragments, or typeclass/dictionary search.

## AI-WORKSPACE-1B2B Completion Record

Date: 2026-08-08

Hypothesis: exact portable module-node and runtime-fragment identities can
compose locally authored fragment chains across a deterministic module graph
through existing multi-provider interfaces and runtime closures, without
persisting compiler objects or admitting undeclared global free names.

Result: accepted for the bounded local cross-module graph profile.

Implementation:

- added browser-safe `src/v3_2/lf_fragment_module_workspace.ts` with profile
  `emdash-lf-fragment-module-workspace-v1`, structured graph errors, exact
  portable module identities, stable dependency-first planning, compilation,
  lookup, and canonical source/compiled snapshots;
- each module identity copies its authority/source/export pins, ordered direct
  dependencies, chain revision/profile, and complete ordered five-field
  fragment identities; every direct dependency edge must reproduce that
  identity exactly;
- each direct dependency with a local runtime explicitly names the exact
  latest local runtime-producing source fragment; graph planning rejects
  missing, extra, duplicate, stale, inherited-only, and non-latest entries;
- refactored `src/v3_2/lf_fragment_workspace.ts` behind its qualified public
  behavior so one internal chain compiler can receive exact declaration
  context, dependency interfaces, and dependency runtime fragments; the
  original 1B2A profile and constructors still reject dependency modules;
- dependency-aware fragment constructors restrict `existing-core` externals
  to intrinsic `core-owner` linkage. Ordinary free declarations must be exact
  dependency-module or same-module earlier-fragment externals, closing the
  measured unrelated-global-environment contamination route;
- compilation reconstructs the full graph before execution, resolves exact
  provider nodes in stable topological order, supplies the provider's existing
  multi-fragment `CoreLfCompiledModuleInterface`, and supplies imported
  runtimes in the source module's direct dependency order;
- existing visibility checks continue to own public/protected/private access,
  and the existing runtime composer continues to own transitive flattening,
  source order, cycle/collision rejection, and shared-diamond deduplication;
  and
- canonical graph snapshots contain source identities/edges, chain source and
  compiled summaries, interface module IDs, runtime artifact identities, and
  final runtime/proof summaries, but no environments, sessions, callbacks,
  class/object identities, filesystem handles, or computed hashes.

The principal witness uses a two-fragment provider whose compiled interface
spans two declaration providers and whose later mixed fragment supplies
runtime and proof rules. A two-fragment consumer imports declarations from
both providers, checks and executes a local runtime rule against the imported
runtime, and composes a local proof program. A separate four-module witness
imports provider, consumer, and sibling runtimes into a top module and proves
that the shared provider runtime appears exactly once in the flattened
diamond, in direct source dependency order. Another witness places an
unrelated module genuinely earlier in the shared topological environment;
the consumer still receives only its declared provider interface, and an
attempted `existing-core` free-declaration alias fails before compilation.

The negative matrix also rejects missing/stale/extra dependency identities,
missing/wrong/extra runtime identities, private dependency use, missing and
duplicate modules, dependency cycles, and fabricated noncanonical plans.
Module and fragment input permutations produce byte-identical source and
compiled snapshot text with no process-state leakage.

Qualification:

- the nearest workspace/proof/mixed/runtime/visibility/browser matrix passed
  78 tests across nine suites: 77 active passes, one intentional opt-in skip,
  and zero failures;
- workspace typecheck, changed-file ESLint, the transitive browser closure
  audit, and `git diff --check` passed; and
- the required complete `./scripts/pnpmw run check:ts` passed 1,476 tests
  across 223 suites: 1,423 active passes, 53 intentional skips, and zero
  failures, in 1,646,704.086648 ms.

No Lambdapi source, active mathematical policy, kernel/trusted-Core boundary,
browser product entry, filesystem/remote adapter, cache, lockfile, package
graph, or publication surface changed. AI-REMOTE-1 begins as a separate
read-only audit; this local graph does not itself grant any location, network,
credential, cache, or content-integrity authority.

## AI-REMOTE-1 Audit And Frozen AI-REMOTE-1A Contract

Date: 2026-08-08

The read-only audit found:

- `lf_transfer_acquisition_contract.ts` already provides the correct split
  precedent: committed immutable selection-contract validation is
  browser-safe, while reading and hashing active content are explicitly not
  its responsibility;
- `lf_transfer_acquisition.ts` is Node-only, receives source and canonical
  export text from its caller, computes SHA-256 itself, checks exporter/import/
  command drift, and performs no file read, subprocess call, fetch, or cache
  write;
- current scale callers own repository-relative file reads and optional
  Lambdapi subprocess execution outside acquisition;
- LF module specs already validate source and canonical-export SHA-256 strings,
  while workspace/fragment serializers produce canonical portable JSON text
  and deliberately do not compute hashes in browser-safe layers;
- AI-WORKSPACE-1A has conservative local snapshot invalidation, but no remote
  identity or persistent cache semantics; and
- the repository has no product remote fetcher, HTTP policy, credential path,
  cache-store abstraction, atomic cache writer, eviction rule, or remote lock
  schema to reuse.

The first remote slice should therefore qualify the trust boundary before it
introduces I/O. The portable artifact is the canonical 1B2B graph source
snapshot. It contains enough module, policy, linkage, provider, and runtime
source data to reconstruct and compile the graph, whereas TypeScript source
modules contain executable authoring code and compiled graph objects retain
process-local state. A source digest alone is insufficient for reproducible
checking across compiler/schema drift, so the lock also pins the expected
canonical compiled snapshot digest and both serialization profiles.

AI-REMOTE-1A freezes this contract:

1. A lock has a lock revision, one immutable artifact identity, and zero or
   more non-authoritative mirror records. Artifact identity contains a stable
   logical workspace ID; exact workspace revision; exact source and compiled
   snapshot revisions/profile revisions; exact canonical source UTF-8 byte
   length and SHA-256; and exact expected canonical compiled-snapshot SHA-256.
2. Artifact identity contains no URI, path, credential, mutable branch/tag,
   cache key chosen by a store, timestamp, ETag, process object, or caller
   callback. Its canonical serialization is the cache/reuse comparison key.
3. Mirror locations are structurally separate hints. The first persisted
   profile accepts normalized credential-free HTTPS URLs with no fragment,
   query, username, or password; duplicates fail. A changed mirror with the
   same artifact identity does not invalidate a verified offline entry.
   Signed/ephemeral URLs belong to an acquisition-time outer adapter, not the
   committed lock.
4. The browser-safe contract layer validates and deep-freezes locks and cache
   entries, serializes them canonically, and reconstructs a graph plan from a
   parsed 1B2B source snapshot. Reconstruction re-runs every fragment/chain/
   graph constructor and requires byte-for-byte canonical source-snapshot
   equality; extra fields or alternate JSON whitespace/order fail.
5. A Node-only materializer receives a validated lock and caller-supplied
   source snapshot text. It computes UTF-8 byte length and SHA-256 itself,
   parses and canonically reconstructs the graph, checks logical workspace/
   profile identity, compiles locally through 1B2B, serializes the compiled
   snapshot, computes its SHA-256, and compares the expected compiled digest.
6. Materialization performs no `fetch`, filesystem read/write, subprocess,
   environment/credential lookup, redirect, retry, mutable cache update, or
   Lambdapi execution. The caller may obtain bytes from HTTP, a workspace
   attachment, a database, or a local file, but bytes cross one identical
   verifier before becoming checked source.
7. A successful materialization can emit an immutable portable cache entry
   containing only its cache revision, exact artifact identity, and canonical
   source text. It never stores a compiled object or trusts a previously
   stored observed digest.
8. Offline materialization receives the lock plus a cache entry. It requires
   exact artifact-identity equality, then repeats byte/hash/reconstruction/
   compilation/compiled-hash verification. A different mirror list is
   irrelevant; a poisoned identity or source fails closed.
9. Error codes distinguish invalid lock/location/cache shape, source byte/hash
   mismatch, noncanonical or invalid snapshot, workspace/profile identity
   mismatch, compiled digest mismatch, and cache identity/content drift.
10. Tests must prove direct and offline byte-identical materialization,
    mirror independence, source drift rejection, alternate-encoding rejection,
    workspace/profile drift, compiled-digest drift, poisoned-cache rejection,
    immutable portable serialization, and a Node-free contract closure with
    the Node hash materializer outside it.

AI-REMOTE-1B remains separately gated. It must choose a real consumer before
specifying storage roots, content-addressed filenames, atomic installation,
locking/concurrency, eviction, HTTP redirects/timeouts, authentication,
retries, platform APIs, or signed URL handling. AI-REMOTE-1A neither performs
nor authorizes any of those actions.

## AI-REMOTE-1A Completion Record

Date: 2026-08-08

Hypothesis: one canonical 1B2B graph-source snapshot can be moved or cached as
portable text and then reconstructed and compiled under an exact content lock,
without making its URL, cache location, caller, or a previously compiled
object part of proof authority.

Result: accepted for the bounded lock, supplied-text materialization, and
immutable offline-cache-data profile.

Implementation:

- added browser-safe `src/v3_2/lf_remote_workspace_contract.ts` with profile
  `emdash-lf-remote-workspace-lock-v1`, exact plain-data shape validation,
  structured errors, deep freezing, and canonical serializers for artifact
  identities, locks, and cache entries;
- the location-free artifact identity pins logical workspace and workspace
  revisions, both source/compiled snapshot and profile revisions, exact source
  UTF-8 byte length, source SHA-256, and expected compiled-snapshot SHA-256;
- zero or more persisted mirrors are separate non-authoritative hints. The
  first profile admits only canonical credential-free HTTPS URLs without
  query or fragment and rejects duplicates, noncanonical URLs, coercible
  primitive fields, class records, and extra ambient state;
- source parsing accepts only the exact canonical 1B2B source-snapshot bytes.
  It re-runs every dependency-aware fragment constructor, same-module chain
  constructor, cross-module graph constructor, and source serializer before
  returning a plan. Alternate JSON whitespace/order and fabricated fields
  therefore fail even when a caller supplies matching replacement digests;
- added Node-owned `src/v3_2/lf_remote_workspace.ts`. Its materializer receives
  caller-supplied text, computes byte length and SHA-256, reconstructs the
  canonical graph, checks workspace/profile pins, compiles through the
  qualified 1B2B engine, serializes the compiled snapshot, and checks its
  expected SHA-256;
- successful materialization emits an immutable cache entry containing only
  the exact artifact identity and canonical source text. Offline use compares
  artifact identities exactly and repeats byte, hash, reconstruction,
  compilation, and compiled-hash checks on every use; and
- the contract closure has no Node builtin. The adjacent materializer imports
  only Node cryptography and performs no fetch, filesystem read/write,
  subprocess, environment/credential lookup, cache mutation, or Lambdapi
  execution.

The principal witness is a two-module declaration graph. A provider exports
`Carrier`; a consumer declares `token : Carrier` through the provider's exact
source identity and compiled public interface. Direct materialization
reproduces byte-identical source and compiled snapshots, while offline
materialization from the emitted cache entry reproduces them again after the
mirror location changes.

The negative matrix rejects changed byte length, same-length source drift,
alternate JSON encoding, fabricated snapshot fields, workspace and profile
drift, compiled-output drift, poisoned cache identity, poisoned cached source,
unsafe or duplicate mirrors, extra lock fields, coercible numeric fields,
class-instance records, and non-string source input. The logical workspace ID
is an opaque stable label associated with the locked bytes; it is not inferred
from a URL or treated as a digest substitute.

Qualification:

- the focused remote suite passed 9 tests in one suite with zero failures;
- the remote/browser boundary pair passed 20 tests across two suites with
  zero failures;
- the nearest workspace/fragment/visibility/runtime/proof/mixed/acquisition/
  browser matrix passed 102 tests across 12 suites: 100 active passes, two
  intentional opt-in skips, and zero failures;
- workspace setup, TypeScript typecheck, changed-file ESLint, transitive
  browser-closure checks, source scans for forbidden I/O/process operations,
  and staged/unstaged diff hygiene passed; and
- because this tranche changed the public barrel and main test runner, the
  one required complete `./scripts/pnpmw run check:ts` passed 1,486 tests
  across 224 suites: 1,433 active passes, 53 intentional skips, and zero
  failures, in 1,645,729.955054 ms.

The complete aggregate is durable evidence for this unchanged shared
boundary and must not be rerun for reassurance. The subsequent AI-REMOTE-1B
audit and adapter rows use focused and nearest checks unless an exact final
diff independently triggers the repository's strict shared-boundary rule.

No Lambdapi source, kernel/trusted-Core owner, mathematical policy, browser
product entry, package/dependency/lockfile, filesystem, HTTP client, credential
path, persistent cache store, platform API, publication surface, or remote
resource changed. At this AI-REMOTE-1A boundary, AI-REMOTE-1B was authorized
only as a read-only exact-consumer audit; this completion did not itself
authorize transport or persistent storage.

## AI-REMOTE-1B0 Exact-Consumer Audit And Frozen 1B1 Contract

Date: 2026-08-08

The read-only consumer audit covered the current code and operational reports
in the single `~/closerfans` platform repository, whose product surfaces
include CloserFans, GetPaidX, and LastRevision. It found:

- a running GetPaidX workspace already supplies persistent mounted roots:
  `/work/project` for project source, `/work/data` for non-project persistent
  data, and `/work/artifact` for hydrated post attachments. Codex runs inside
  the controller and can use those files directly;
- the controller's snapshot operation initializes the project Git repository,
  stages the complete project with `git add -A`, commits a snapshot when dirty,
  and reports the resulting revision. Emdash therefore need not own hosted Git
  transport or snapshot lifecycle;
- current browser and curated MCP source-file operations deliberately admit
  only the four Arrowgram files `arrowgram.workspace.json`, `paper.md`,
  `paper.css`, and `diagram.json`. The platform plan explicitly defers moving
  that allowlist into a generic validated template capability contract;
- source read/write, diff, build, snapshot, attachment, signed-URL, and publish
  routes are authenticated platform services. Persisting their bearer tokens,
  cookies, controller tokens, or ephemeral signed URLs in an emdash lock would
  cross both the platform security boundary and the AI-REMOTE-1A identity
  boundary;
- Arrowgram's accepted file-first precedent is still directly useful: agent
  and browser edit canonical project files, Git snapshots establish review
  baselines, and generated publication artifacts remain distinct from editable
  source; and
- no current generic GetPaidX source API can yet name emdash files. An emdash
  template or generic source-capability extension is therefore a later
  integration consumer, not a prerequisite for an in-container agent that
  already sees the mounted files.

The selected first consumer is consequently the TypeScript/emdash process run
by an AI agent inside a mounted workspace. The platform transports and
snapshots bytes; emdash validates what those bytes mean. This avoids an MCP
server in the proof loop and also avoids coupling the checker to one hosted
platform. Local development can exercise the identical adapter by supplying
ordinary absolute project and data roots.

AI-REMOTE-1B is partitioned as follows:

1. AI-REMOTE-1B0, this audit, is complete and behavior-free.
2. AI-REMOTE-1B1 owns one mounted-filesystem and immutable-cache-store adapter.
   It is the only approved implementation row.
3. AI-REMOTE-1B2 may add an agent command and/or template integration only
   after 1B1 exposes an executable consumer and the exact command/file surface
   can be measured.
4. AI-REMOTE-1B3 reserves authenticated or public network acquisition. It is
   pending a stable real consumer and does not inherit approval from 1B1.

AI-REMOTE-1B1 freezes this contract:

1. The caller supplies two absolute existing directory roots: a project root
   and a persistent-data root. They must be canonical, disjoint, and
   non-overlapping so generated cache state cannot enter the Git-snapshotted
   project. The adapter never consults the current working directory, `HOME`,
   environment variables, platform metadata, or a discovery walk. For the
   first profile it reads exactly
   `emdash.workspace.lock.json` and `emdash.workspace.source.json` directly
   below the project root. The first filesystem profile targets the Node/POSIX
   mounted roots used by the Linux GetPaidX controller and makes no untested
   cross-platform atomicity claim.
2. Roots and fixed files are inspected without following symbolic links.
   Roots must be real directories; lock, source, and cache entries must be
   regular files. Fixed derived cache components are containment-checked and
   any symlink, special file, traversal, or non-absolute root fails closed.
3. The lock file is bounded to 256 KiB, parsed as plain JSON, validated by the
   existing AI-REMOTE-1A lock constructor, and required to equal the exact
   canonical lock serialization byte for byte. The canonical source file is
   bounded to 64 MiB and must have the exact byte size pinned by the lock
   before it crosses the existing 1A materializer.
4. The adapter invokes only the TypeScript 1B2B reconstruction/compiler and
   existing explicit-Core checker/runtime path. It verifies source bytes and
   SHA-256, reconstructs every graph constructor, compiles locally, and checks
   the expected canonical compiled-snapshot SHA-256. It does not invoke a
   Lambdapi executable or emit Lambdapi as a condition of acceptance. This
   does not retire deterministic Lambdapi/emdash emission or checking as a
   future optional backend/conformance adapter.
5. The cache namespace is the fixed
   `.emdash/cache/lf-remote-workspace-v1` subtree below the supplied data root.
   The filename is `artifact-<hex>.json`, where `<hex>` is SHA-256 of the exact
   canonical artifact-identity serialization. No caller or store chooses a
   semantic key.
6. A cache file is the exact canonical AI-REMOTE-1A cache-entry serialization.
   It contains the artifact identity and canonical source text, never compiled
   classes, callbacks, a trusted observed digest, a location, credentials, or
   platform state. Its read bound is derived from the locked source bound and
   the maximum JSON-string expansion plus bounded metadata.
7. A missing entry is populated through a mode-`0600` temporary regular file
   in the final cache directory. The adapter writes and fsyncs the complete
   canonical bytes, then uses an atomic hard-link create to install the final
   name without replacement. It unlinks the temporary name after success or
   failure and syncs the containing directory after installation where the
   filesystem supports it.
8. If another process wins installation, or an entry already exists, the
   adapter reads that entry without following symlinks, requires exact
   canonical encoding, fully re-runs offline 1A verification, and requires its
   bytes to equal the entry just materialized from project source. It never
   overwrites, repairs, truncates, or silently quarantines a conflicting cache
   entry.
9. Offline checking requires only the canonical project lock plus the derived
   cache entry. Every offline use repeats lock, cache shape, identity, byte,
   source-hash, graph reconstruction, TypeScript compilation, and compiled-hash
   verification. The source project file may be absent. A changed mirror list
   remains irrelevant because mirrors are not part of artifact identity.
10. The store returns the verified materialization, canonical resolved paths,
    derived cache key/path, mode (`source` or `offline`), and cache disposition
    (`installed` or `verified-existing`) as immutable result data. Errors
    distinguish roots/paths, bounds, noncanonical lock/cache text, missing
    offline cache, unsafe file type, install failure, and cache conflict while
    preserving the existing semantic integrity errors.
11. Focused tests must prove source-to-cache-to-source-absent offline parity,
    exact existing-entry reuse, poisoned-entry non-overwrite, concurrent
    identical population, noncanonical lock rejection, fixed-file symlink
    rejection, missing offline cache, and absence of fetch/credentials/
    Lambdapi/ambient-root behavior.
12. This row adds no public barrel export, main test-runner import, package,
    dependency, browser closure, kernel file, or platform-repository edit. Its
    tests extend the already registered remote-workspace suite. Focused tests,
    workspace setup, typecheck, changed-file lint, source-boundary scans, and
    diff hygiene are proportional; the recorded 1,486-test aggregate is reused
    because its shared boundary is unchanged.

Rejection conditions are concrete. Revise or stop 1B1 if the TypeScript
materializer cannot rebuild from the fixed mounted files; if correct atomic
no-replace behavior requires mutable cache authority; if the platform in fact
requires emdash to retain credentials; if cache validation would trust stored
compiled state; or if a proposed implementation needs current-directory,
environment, network, Git, MCP, Lambdapi, or background-service state.

This exact contract is self-approved under D-AI-NATIVE-049 after the clean
`a3ba93a` checkpoint and topology audit. Approval is limited to AI-REMOTE-1B1
source, focused tests, living-plan synchronization, proportional validation,
and a rollback-safe local goal-branch checkpoint after all gates pass. It does
not approve AI-REMOTE-1B2/1B3, changes in `~/closerfans`, another merge to
`main`, a push, or deployment.

## AI-REMOTE-1B1 Completion Record

Date: 2026-08-08

Hypothesis: an AI agent in a GetPaidX-style mounted workspace can verify one
locked emdash graph, populate a persistent immutable cache safely under
concurrency, and rebuild offline using only TypeScript/emdash, without moving
platform authentication, transport, Git, or publication into proof authority.

Result: accepted for the bounded Node/POSIX mounted-file and immutable-cache
adapter. The optional Lambdapi/emdash backend route remains available but is
not invoked or required by this profile.

Implementation:

- added Node-owned `src/v3_2/lf_remote_workspace_store.ts` with profile
  `emdash-lf-mounted-remote-workspace-store-v1`. Its only input is an exact
  plain record containing canonical absolute, disjoint project and data roots;
  it accepts no extra ambient state;
- the adapter reads only `emdash.workspace.lock.json` and
  `emdash.workspace.source.json` immediately below the project root. It opens
  fixed files without following final symlinks, rejects non-regular files and
  noncanonical roots, checks exact UTF-8, bounds lock/source bytes, and requires
  exact canonical lock text;
- the source path feeds the existing AI-REMOTE-1A TypeScript materializer. The
  materializer repeats source byte/SHA-256 checks, canonical graph
  reconstruction, explicit-Core TypeScript compilation/checking, and expected
  compiled-snapshot SHA-256 verification;
- the store key is SHA-256 of canonical artifact identity and the fixed cache
  path is `.emdash/cache/lf-remote-workspace-v1/artifact-<hex>.json` below the
  supplied data root. Mirrors and lock revisions do not perturb this key;
- cache text is the existing canonical immutable cache-entry format. A missing
  entry is written to a mode-`0600` same-directory temporary regular file,
  fsynced, then exposed through an atomic hard-link create that cannot replace
  an existing name. Cooperative concurrent writers converge on the exact same
  bytes;
- every existing or concurrently installed entry is opened without following
  its final symlink, bounded, canonically parsed, fully recompiled/reverified,
  and byte-compared with current verified source. Invalid or different entries
  produce a cache conflict and remain untouched;
- offline materialization reads the canonical lock and derived cache only. It
  does not create a missing directory or entry and succeeds after the project
  source file is removed; changing only mirror hints preserves the same cache
  key and result; and
- the adapter exports no browser API and was deliberately not added to the
  public v3.2 barrel or the main test-runner imports. It imports Node crypto,
  path, and filesystem primitives only; there is no network, process launch,
  credential/environment lookup, current-directory discovery, Git, MCP,
  Lambdapi, eviction, background service, or platform-repository behavior.

Durable tests extend the already registered
`tests/v3_2_lf_remote_workspace_tests.ts` suite. They cover first install,
source-absent offline parity, mirror-independent key reuse, exact existing
entry reuse, poisoned-entry non-overwrite, concurrent identical population
with no temporary debris, noncanonical lock and source-size rejection, source
and cache symlinks, read-only offline miss, explicit/disjoint roots, extra
ambient-field rejection, immutable result data, and the exact non-effect
profile.

Qualification:

- the focused AI-REMOTE-1A/1B1 file passed 15 tests across two suites with zero
  failures;
- the nearest TypeScript workspace/fragment/visibility/runtime/proof/mixed/
  acquisition/browser matrix passed 108 tests across 13 suites: 106 active
  passes, two intentional Lambdapi opt-in skips, and zero failures;
- workspace setup, root TypeScript typecheck, changed-file ESLint, forbidden
  network/process/environment/current-directory scan, and diff hygiene passed;
  and
- no public barrel, main runner, package/workspace setup, browser closure,
  generic LF compiler/checker/runtime, kernel, or publication boundary changed.
  Under D-AI-NATIVE-048 and the repository's proportional-validation rule, the
  recorded 1,486-test aggregate is carried forward and was not repeated.

No file in `~/closerfans` changed. No Lambdapi check was required because the
row neither changes nor depends on current kernel names and executes only the
already qualified TypeScript backend. AI-REMOTE-1B2 now begins as a read-only
audit of the existing `./scripts/emdash` command seam, management-code shape,
and one mounted template/agent consumer. It must freeze a separate exact
contract before any command, public export, template, platform, or backend
adapter implementation.

## AI-REMOTE-1B2 Audit And Frozen 1B2A Command Contract

Date: 2026-08-08

The read-only command and hosted-template audit found:

- `./scripts/emdash` is already an executable, fail-fast shell edge. It
  forwards all arguments unchanged to the synchronous Node-owned AI proof CLI,
  whose accepted public forms are `check|goals`, optional declaration, and
  `--format jsonl|text`;
- the proof CLI is deliberately a fixed local demo consumer. It computes
  fingerprints, creates fresh TypeScript proof state, writes only stdout/
  stderr, and retains no session. It should not absorb asynchronous workspace
  filesystem behavior or become a daemon;
- a leading shell namespace can route `workspace ...` to a separate process
  launcher while leaving every existing proof invocation and usage string
  unchanged. This is smaller and easier to test than a new async dispatcher
  wrapping the synchronous proof CLI;
- AI-REMOTE-1B1 already supplies the exact command operation: online
  verification/cache install and source-absent offline verification from two
  explicit roots. The command needs no new semantic/checker API and should
  summarize rather than serialize process-local compiled objects;
- the repository root package is private, has no `bin`, `files`, pack, or
  publication contract, and runs TypeScript through the development dependency
  `ts-node`. Its declared engine is Node 22.13 or newer;
- current GetPaidX controller images, including the LambdaPi variant, are based
  on Node 20. Existing hosted precedents either preinstall a runtime in a
  specialized pool (`lambdapi_cli`) or let a template install published
  template-owned packages (`arrowgram_web`);
- `emdash-template` is the standalone browser-reviewer fixture, not a hosted
  contributor/runtime package and not a GetPaidX workspace template; and
- the platform's curated browser/MCP source file allowlist is still
  Arrowgram-specific. Direct terminal/Codex access to mounted files is enough
  for a future packaged emdash template, but it does not solve runtime delivery
  or authorize cross-repository edits.

The audit therefore partitions AI-REMOTE-1B2:

1. AI-REMOTE-1B2A is one local agent-facing command over the already qualified
   TypeScript store. It is frozen and approved below.
2. AI-REMOTE-1B2B owns hosted runtime packaging and the GetPaidX template/
   skill/source-capability integration. It remains pending a deliberate choice
   among a published package, a versioned precompiled artifact, or reviewed
   template-owned source, plus a Node-version contract. It authorizes no change
   in `~/closerfans`.

AI-REMOTE-1B2A freezes this command contract:

1. `./scripts/emdash` recognizes only the exact first argument `workspace` as
   a namespace, removes it, and execs a separate thin TypeScript launcher. All
   other argument vectors continue to exec the existing proof launcher
   unchanged.
2. The sole first command is:

   ```text
   ./scripts/emdash workspace check \
     --project-root ABSOLUTE_PATH \
     --data-root ABSOLUTE_PATH \
     [--offline] [--format jsonl|text]
   ```

   Both roots are mandatory and may appear as `--name value` or
   `--name=value`. Missing values, duplicates, unknown flags, positional
   arguments, unknown commands, and repeated `--offline` fail closed. Root
   canonicality, existence, disjointness, and containment remain owned by
   AI-REMOTE-1B1.
3. There is no current-directory, environment, `HOME`, platform-path, or
   `/work/*` default. A GetPaidX agent will pass `/work/project` and
   `/work/data` explicitly after a compatible runtime exists; a local agent can
   pass any qualified roots.
4. Online mode calls `materializeCoreLfMountedRemoteWorkspace`; `--offline`
   calls `materializeCoreLfMountedRemoteWorkspaceOffline`. No command callback
   can replace these operations, and no backend selector is accepted.
5. The default format is JSONL and contains exactly one newline-terminated
   record with ordered fields: record revision, `kind=workspace-check`,
   `status=verified`, executed backend, mode, cache disposition, logical
   workspace ID, workspace revision, ordered module IDs, locked source SHA-256,
   locked compiled SHA-256, and identity-derived cache key. It contains no
   source text, compiled text/object, mirror, lock path, source path, cache
   path, project/data root, timestamp, process ID, or credential.
6. `--format text` is a compact projection of the same record: verified
   workspace/revision, executed backend, ordered module count/IDs, and cache
   mode/disposition/key. It does not trigger a second check.
7. Success writes only the selected report to stdout and exits zero. Parse,
   I/O, and semantic failure write `emdash: <message>` to stderr, write no
   stdout, and exit two. The command has no incomplete-proof exit state.
8. The launcher owns only `process.argv` and `process.exitCode`. The reusable
   CLI function is asynchronous and accepts stdout/stderr sinks solely for
   deterministic tests; it exposes no filesystem, checker, materializer,
   credential, or transport injection hook.
9. Focused tests cover online JSONL, offline text after source removal, exact
   field/privacy shape, parser failures and duplicate rejection, underlying
   verification failure, the actual shell-wrapper route, and unchanged legacy
   `check|goals` behavior.
10. This row adds no public barrel or main-runner import, package manifest,
    dependency/lockfile, generic checker/compiler/runtime, browser closure,
    kernel file, hosted template, platform source allowlist, Lambdapi backend,
    or `~/closerfans` change. Focused CLI/remote tests, shell syntax and process
    smoke, workspace setup, typecheck, changed-file lint, a nearest local
    matrix, and diff hygiene are proportional. The prior aggregate is reused.

Reject or revise 1B2A if shell namespacing changes an existing proof argv; if a
useful report requires process-local compiled state or paths; if the command
needs ambient root discovery, backend guessing, lock regeneration, or
credentials; or if it cannot exercise the exact 1B1 verifier without a new
semantic API.

This contract is self-approved under D-AI-NATIVE-049. Approval is limited to
the local CLI module, thin launcher, additive shell dispatch, focused tests,
living-plan synchronization, proportional validation, and a rollback-safe
goal-branch checkpoint. It does not approve packaging, a hosted template,
Node/controller changes, platform APIs, Lambdapi execution, another merge,
push, or deployment.

## AI-REMOTE-1B2A Completion Record

Date: 2026-08-08

Hypothesis: the existing stateless `./scripts/emdash` edge can expose the
qualified mounted-workspace verifier to an AI agent through one additive
namespace and compact report, without changing proof commands, discovering
ambient roots, or pretending a hosted or Lambdapi backend already exists.

Result: accepted for the bounded local TypeScript/emdash workspace-check
command. Hosted package/template delivery remains deferred under
D-AI-NATIVE-060.

Implementation:

- added Node-owned `src/v3_2/lf_remote_workspace_cli.ts` with command profile
  `emdash-lf-remote-workspace-cli-v1` and record profile
  `emdash-lf-workspace-check-record-v1`;
- exact parsing accepts only `check`, mandatory explicit project/data roots,
  optional `--offline`, and `--format jsonl|text`, including the two standard
  option-value forms. Missing, duplicate, positional, unknown, relative-root,
  and unimplemented backend arguments fail closed;
- online and offline commands directly call the two qualified AI-REMOTE-1B1
  operations. The CLI exposes no materializer/checker/filesystem callback and
  does not regenerate locks or source;
- the immutable path-free check record reports only its profile, verified
  status, actually executed `typescript-emdash-explicit-core` backend, source/
  offline mode, cache disposition, logical workspace/revision, ordered module
  IDs, locked source/compiled SHA-256, and identity-derived cache key;
- default JSONL emits exactly one ordered newline-terminated record. Optional
  text is a single projection of that record and triggers no second check;
- added thin `examples/v3_2_remote_workspace_cli.ts`, which owns only argv and
  exit-code plumbing; and
- `scripts/emdash` now dispatches an exact leading `workspace` argument to the
  new launcher. Every other argument vector is still passed unchanged to the
  existing proof launcher. Executable mode remains `0775`.

The existing remote-workspace test file now also covers online JSONL exact
field order/privacy, offline text after source removal, parser and duplicate
failures, relative/ambient roots, rejection of a premature `--backend
lambdapi`, propagation of source verification failure, the actual executable
shell route, and an actual legacy `check --format text` proof process.

Qualification:

- the focused AI-REMOTE-1A/1B1/1B2A file passed 19 tests across three suites
  with zero failures;
- the nearest proof-CLI/workspace/fragment/visibility/runtime/proof/mixed/
  acquisition/browser matrix passed 117 tests across 15 suites: 115 active
  passes, two intentional Lambdapi opt-in skips, and zero failures;
- workspace setup, TypeScript typecheck, changed-file ESLint, `sh -n`, actual
  process smoke, executable-mode check, forbidden network/process/environment/
  current-directory scan, and diff hygiene passed; and
- no public barrel, main test runner, package/workspace setup, dependency,
  generic checker/compiler/runtime, browser closure, kernel, hosted template,
  platform, or publication boundary changed. The 1,486-test aggregate is
  therefore reused under D-AI-NATIVE-048 rather than repeated.

No `~/closerfans` file changed, and the command invokes no Lambdapi process.
The backend-neutral lock remains compatible with a future separately profiled
Lambdapi/emdash adapter. AI-REMOTE-1B2B cannot start until runtime distribution
and Node compatibility are selected; AI-REMOTE-1B3 remains gated on a real
network consumer. The next dependency-ready work is AI-SYNTH-0's read-only
inventory and selection of one exact explicit-dictionary elaboration consumer;
that subsequent inventory is now recorded below.

## AI-SYNTH-0 Inventory And AI-SYNTH-1A Exact Contract

Date: 2026-08-08

AI-SYNTH-0 reviewed the current pure-TypeScript elaboration path before
approving any new search mechanism:

- `CoreChecker` and `CoreElaborationSession` insert and solve ordinary
  elaboration metavariables. Their structural flex-rigid solver and bounded
  Miller-pattern inversion solve equations created by checking one term; they
  do not enumerate declarations, rank alternatives, or establish an instance
  scope.
- `CoreLfElaborationSession` extends rigid comparison with bounded outer-LF
  beta/delta and runtime conversion. `CoreLfCompiledProofProgram` instead
  rewrites a stuck equality problem into ordered generated equality problems.
  Its source-ordered first-match rule semantics are proof evidence, not a
  coherent dictionary-selection policy, and synthesis must never execute it.
- Compiled declarations already contain the required authority. A
  `CoreLfMixedDeclarationBaseContext` exposes one exact checked environment
  plus qualified-symbol lookup. A checked ordinary declaration carries its
  installed status, checked type, and `free-declaration` link, so synthesis can
  derive the candidate term itself rather than trust a caller-supplied term or
  type.
- The record/structure macro expands to ordinary carrier, constructor,
  projection, and runtime-beta declarations. Its host handle is deliberately
  transient and no instance annotation survives into Core. A generated
  capability carrier with ordinary global inhabitants is therefore a real
  current consumer without adding a class node to the kernel.
- The adjunction macro already produces explicit `Adjunction R L F G`
  witnesses, and its tests intentionally admit two witnesses with identical
  endpoints. It is a strong subsequent mathematical consumer and proves that
  silent first-match selection would be unsound usability. It is not the first
  executable consumer because the complete active adjunction dependency graph
  has not yet graduated to the self-contained TypeScript backend.
- Active commutative-algebra, sheafification, affine-scheme, and scheme layers
  likewise use explicit Sigma records, presentations, and capability
  witnesses. Multiple structures on one carrier are meaningful. This rules
  out an ambient global-canonical-instance assumption and favors explicit
  scopes with hard ambiguity errors.

The selected first consumer is a direct-TypeScript outer-LF module whose
existing structure-macro-generated `Record` carrier is used as a capability
dictionary. The module has ordinary checked global values
`primaryCapability` and `secondaryCapability`, and an ordinary declaration
with an implicit `Record` binder. AI-SYNTH-1A must select an explicitly
enumerated unique value and then demonstrate that the returned Core reference
can be supplied to that binder and checked by the existing TypeScript/LF
checker. Enumerating both values must demonstrate ambiguity; a checked
declaration of a different carrier must demonstrate a complete rejected-
candidate trace.

### Frozen AI-SYNTH-1A API and trust boundary

The browser-safe module is
`src/v3_2/lf_dictionary_synthesis.ts`, with report revision
`emdash-lf-dictionary-synthesis-v1`. Its single operation accepts:

1. one `CoreLfMixedDeclarationBaseContext`, which is the complete checked
   declaration/environment authority;
2. one closed, meta-free `KernelExpression` target that checks as a type in
   that environment; and
3. one finite list of exact `CoreLfQualifiedSymbol` candidates, which is the
   complete candidate scope for this request.

It has no discovery operation. It does not iterate an environment, infer a
provider from spelling/order, query a global registry, retain a callback,
read a workspace, invoke a parser, perform I/O, consult MCP, or acquire remote
content. Before checking alternatives it canonicalizes candidate identities
by module ID and local name. A repeated identity is an input error rather than
two instances, and an unresolved, excluded, intrinsic/core-owner, or otherwise
non-installed candidate makes the supplied scope invalid. Every admissible
term is reconstructed from the checked `free-declaration` link; the caller
cannot forge its Core name, type, or body.

The target is first checked against `TYPE`. Each candidate is then tested
independently with a fresh `CoreLfChecker` over the exact supplied environment
and the existing fixed 256-step LF comparison bound. This admits checked
delta conversion but supplies no catalog runtime and executes no proof-time
program. An ordinary type mismatch is a traced rejection. A conversion limit
or another unexpected checking failure aborts rather than being mislabeled as
evidence that no dictionary exists.

Termination is the length of the finite canonical candidate list: there is
one bounded target check and at most one bounded candidate check per identity.
There are no recursive premises, local candidate binders, priorities, tiers,
backtracking trees, generated metavariables, or configurable search fuel in
this profile.

The deterministic report contains the revision, canonical explicit-Core
target text, fixed comparison bound, and every candidate in canonical order
with its exact identity and either `matched` or a stable rejected-checker code
and diagnostic. Outcomes are:

- no matches: `NO_MATCHING_DICTIONARY`, carrying the complete report;
- exactly one match: a deeply frozen result containing the report, selected
  qualified identity, checked target, and checked explicit Core reference; or
- more than one match: `AMBIGUOUS_DICTIONARY`, carrying the complete report
  and all matching identities.

Input order never chooses a winner. The successful explicit term is rechecked
at the public checker boundary and contains no residual metavariable. Core,
the checker, session unification, proof rules, runtime rules, declaration
compilation, and the mathematical owners remain unchanged and typeclass-
unaware. The result is backend-neutral Core produced and checked by the pure
TypeScript backend; optional later Lambdapi emission/conformance remains a
separate adapter.

### Explicit deferrals

AI-SYNTH-1B must use a real authoring/workspace consumer to decide portable
instance annotations, lexical/imported scope, local dictionary binders, and
the exact surface request that asks elaboration to synthesize an omitted
argument. AI-SYNTH-2 must use a genuinely recursive indexed consumer before
adding premise search, priority/tier coherence, independent fuel, or an Elpi
provider. Neither row may weaken 1A's explicit candidate authority or turn a
proof-time equality rule into an instance declaration.

This contract is self-approved under D-AI-NATIVE-049. Approval covers only the
new browser-safe resolver module, focused tests inside the already registered
structure-macro test file, this ledger, and proportional TypeScript checks. It
does not authorize a public barrel or test-runner change, a string parser,
workspace schema change, kernel/Lambdapi edit, platform integration, long
unchanged aggregate, external Git mutation, or publication.

### AI-SYNTH-1A Completion Record

Result: accepted and final-green for the closed global-dictionary profile.

Implementation:

- added browser-safe `src/v3_2/lf_dictionary_synthesis.ts` with the frozen
  `emdash-lf-dictionary-synthesis-v1` profile;
- validated the target as a closed meta-free type, canonicalized the caller's
  complete exact candidate list without mutating it, and rejected duplicate,
  unavailable, excluded, intrinsic/core-owner, or otherwise unsupported
  candidate identities;
- derived every candidate reference and declared type solely from the checked
  mixed-declaration context, then used a fresh bounded `CoreLfChecker` for
  every independent match attempt;
- returned one deeply frozen explicit checked Core reference and full trace,
  or structured missing/ambiguity errors carrying every canonical match and
  ordinary mismatch; and
- changed no Core node, checker/session algorithm, runtime/proof rule,
  declaration compiler, module/workspace snapshot, parser, public barrel,
  browser barrel, CLI, backend selector, kernel, or platform surface.

The already registered structure-macro suite now compiles a real generated
`Record` carrier, two ordinary global capability dictionaries, a wrong-carrier
dictionary, and an ordinary consumer with an implicit dictionary binder. It
checks successful explicit insertion, frozen output, nonmutation, input-order
independence, a complete rejected-candidate trace, empty and missing scopes,
duplicate rejection, ambiguity containing both matches, invalid target
rejection, and the final consumer call through the existing TypeScript/LF
checker.

Qualification:

- the focused structure-macro suite passed 11 tests: 10 active passes, one
  intentional Lambdapi opt-in skip, and zero failures;
- the nearest LF builder/conversion, structure, and mixed-phase matrix passed
  44 tests across four suites: 41 active passes, three intentional Lambdapi
  opt-in skips, and zero failures;
- workspace contract, root TypeScript typecheck, changed-file ESLint,
  browser-safety/forbidden-effect scan, and diff hygiene passed; and
- no shared aggregate boundary changed. The recent 1,486-test root aggregate
  is therefore reused under D-AI-NATIVE-048 instead of rerun.

No file below `emdash2/` or in `~/closerfans` changed, and no Lambdapi process,
network operation, MCP service, or external backend was invoked. Decisions
D-AI-NATIVE-062 through D-AI-NATIVE-067 now have direct implementation and
test evidence. AI-SYNTH-1B remains gated on an exact authoring/workspace
consumer; AI-SYNTH-2 remains gated on a genuinely recursive indexed consumer.

## AI-PROOF-2 Completion Record

Date: 2026-08-08

Hypothesis: a fresh proof can be compiled to a deterministic, freshness-bound
artifact above the existing Core/session/checker/refiner boundary, with a
browser-safe reusable implementation and only a thin Node-owned command
adapter.

Result: accepted for the bounded local artifact/CLI slice.

Implementation:

- added browser-safe `src/v3_2/proof_document.ts`, which validates artifact
  fingerprints, creates a fresh `CoreElaborationSession`, `CoreChecker`, and
  private theorem-root meta, checks the target as a type, replays one
  `CoreProofPlan`, and rechecks a completed term before serializing checked
  backend-neutral Core;
- an incomplete artifact carries deterministic named goals but never claims a
  checked Core term;
- artifact revision `emdash-proof-artifact-v1`, JSONL revision
  `emdash-proof-jsonl-v1`, proof-state revision `emdash-proof-state-v1`, and
  compiler/profile identity are explicit data;
- source, profile, and dependency stamps use validated `sha256:` values,
  canonical dependency order, duplicate rejection, and exact freshness
  comparison; no browser-safe module computes a cryptographic hash;
- canonical JSONL emits one proof record followed by ordered goal records;
  optional human text is a projection of that same artifact;
- added browser-safe `src/v3_2/ai_proof_demo.ts` with shared declaration
  environment `ai_native.local`, complete `complete_identity`, and
  intentionally open `open_identity` whose stable hole is `body`;
- added Node-owned `src/v3_2/ai_proof_cli.ts`, a thin
  `examples/v3_2_ai_native_proof_cli.ts` process launcher, and executable
  `./scripts/emdash` wrapper;
- exported only the browser-safe proof-document and demo modules from the
  public v3.2 barrel; the Node CLI remains outside that barrel and the narrow
  browser entry points; and
- wired focused artifact, CLI, and transitive browser-closure tests into the
  root runner.

Observed command behavior:

```text
./scripts/emdash check
  exit 0; one complete proof JSONL record with freshness stamps and checked Core

./scripts/emdash goals --format text
  exit 0; open_identity reports stable goal body at context depth 1

./scripts/emdash check open_identity --format text
  expected exit 1; the selected proof is incomplete and reports one open goal
```

Focused evidence:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_document_tests.ts \
  tests/v3_2_ai_proof_cli_tests.ts \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_proof_refinement_tests.ts \
  tests/v3_2_browser_directed_tests.ts

36 tests / 5 suites: 36 passed, 0 failed, 0 skipped
```

The artifact cases cover complete and incomplete fresh compilation,
byte-stable state, JSONL record order, canonical dependency stamps, malformed
and duplicate fingerprints, profile mismatch, stale source evidence, old
artifact revisions, and impossible checked-Core claims. The CLI cases cover
both commands, both renderings, incomplete-check status, and fail-closed
usage/declaration/format errors. The browser-directed test follows the local
transitive import closure: it reaches the proof document, plan, and checker,
while excluding the Node CLI.

Static and aggregate evidence:

```text
./scripts/pnpmw run typecheck
  passed

changed-file ESLint
  passed

git diff --check
  passed before ledger synchronization

./scripts/pnpmw run check:ts
  workspace contract, typecheck, and complete ESLint passed visibly
  the root worker completed, but its buffered footer was lost at context
  compaction

./scripts/pnpmw test
  recovery rerun on the identical tree exited 0
  1,444 tests / 219 suites: 1,391 passed, 53 opt-in skips, 0 failed
```

The final counts are the frozen AI-PROOF-1 aggregate of 1,432 tests / 217
suites plus twelve newly wired tests in two new suites: six proof-document
tests, five CLI tests, and one test added to the existing browser-directed
suite. The successful recovery rerun is the observed execution evidence; the
count decomposition records how the exact totals were recovered after the
first buffered footer was lost.

No Core node, checker branch, categorical owner, Lambdapi source, browser
barrel, package, dependency, lockfile, print/book surface, remote protocol,
MCP server, cache writer, or publication boundary changed. No kernel,
browser-build, print, book, or `check:all` gate was therefore required.

Decision consequences:

- D-AI-NATIVE-011 through D-AI-NATIVE-015 now have direct implementation and
  negative-boundary evidence;
- an agent can inspect checked or open proof state through deterministic files
  and commands without a resident proof server, while the actual proof claim
  is still reconstructed and checked in a fresh session;
- source freshness is honest data at the browser-safe boundary and actual
  filesystem/hash authority remains an explicit outer concern; and
- AI-WORKSPACE-0 subsequently completed that inventory and selected the
  bounded AI-WORKSPACE-1A declaration graph without authorizing arbitrary
  paths, cache writes, remote imports, or incremental execution.

## AI-PROOF-1 Completion Record

Date: 2026-08-08

Hypothesis: stable public proof identity and deterministic AI-readable state
can be added entirely above the existing session-owned metavariables and
checked refiner, without changing Core, the checker, categorical owners, or a
backend.

Result: accepted for the bounded first slice.

Implementation:

- added `src/v3_2/proof_plan.ts` with frozen `exact`, `intro`, `apply`, and
  named `hole` nodes;
- validates portable/unique node and hole IDs before refinement;
- rejects process-local Core metas embedded in plan expressions and directs
  authors to named holes instead;
- replays only through `CoreProofRefiner` and preserves its transaction
  boundary, including rollback when an `apply` node supplies the wrong number
  of premise plans;
- maps open session metas to stable source-level hole names without changing
  `KernelMetaIdentity`;
- supports optional exact expected context depth and zonked target assertions;
- exposes deterministic trace, context, target, term, source-provenance, and
  JSON state snapshots;
- substitutes stable names in dependent target expressions and sanitizes
  derived provenance that formerly mentioned a raw `?mN` ordinal;
- extends the existing diagnostic formatter through an optional meta-name
  callback while preserving its default output exactly;
- exports the new module through the root v3.2 barrel; and
- wires eight focused tests into the root runner.

Focused evidence:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_plan_tests.ts \
  tests/v3_2_proof_refinement_tests.ts \
  tests/v3_2_proof_state_tests.ts

24 tests / 3 suites: 24 passed, 0 failed, 0 skipped
```

The new cases cover a complete intro/exact identity, ordered two-premise
application, dependent open goals whose second target names the first stable
hole, repeat-run byte-identical JSON, an introduced local context, false
expected-target rejection, atomic apply-arity rollback, invalid/duplicate
IDs, and rejection of a process-local meta in source data.

Static and aggregate evidence:

```text
./scripts/pnpmw run typecheck
  passed

./scripts/pnpmw exec eslint \
  src/v3_2/proof.ts src/v3_2/proof_plan.ts src/v3_2/index.ts \
  tests/v3_2_proof_plan_tests.ts tests/main_tests.ts
  passed

local relative-Markdown-link audit
  passed for this plan, handoff, and scale-plan routing

git diff --check
  passed

./scripts/pnpmw run check:ts
  workspace contract, TypeScript, complete ESLint, and root tests passed
  1,432 tests / 217 suites: 1,379 passed, 53 opt-in skips, 0 failed
```

The aggregate was run exactly once after the focused tranche was green. No
kernel, Lambdapi, browser, print, book, package, dependency, lockfile, remote,
MCP, filesystem, typeclass, or publication boundary changed, so no
`make -C emdash2 check`, browser/print gate, or `check:all` was required.

Decision consequences:

- D-AI-NATIVE-003 through D-AI-NATIVE-005 now have direct implementation
  evidence for the declared/verified split, inert plans, stable named goals,
  and file/JSON-ready state without a server;
- D-AI-NATIVE-010 is accepted for the first slice as exact structural target
  assertion only; conversion-aware expectation remains an explicit later
  question rather than a hidden widening; and
- AI-PROOF-2 subsequently qualified the dependency-ready boundary without
  adding filesystem ownership to `proof_plan.ts`; AI-WORKSPACE-0 then
  completed the read-only inventory and selected AI-WORKSPACE-1A.

## Validation Matrix

| Change | Required evidence |
| --- | --- |
| Plan/document routing only | exact diff, relative-link audit, `git diff --check` |
| Proof-plan data/builders | focused immutability and invalid-ID tests, typecheck, changed-file lint |
| Proof-plan replay | complete identity, ordered apply premises, named incomplete goal, expected-state acceptance/rejection, tactic failure atomicity |
| Stable serialization | repeat-run byte equality, no `symbol`, no raw session object/meta identity, stable named cross-goal references |
| Public barrel/test runner | one complete `./scripts/pnpmw run check:ts` only after a bounded tranche actually changes this shared behavior; carry the result forward for unchanged boundaries |
| Module/workspace manager | focused graph/snapshot/invalidation tests plus nearest transfer/module suites; complete `check:ts` only at a newly changed shared boundary |
| Mounted remote store | focused canonical-file, offline, poison, concurrency, symlink, and root-boundary tests; workspace/typecheck/changed-file lint; nearest TypeScript workspace matrix; no Lambdapi or aggregate unless another exact boundary changes |
| Local workspace CLI | exact JSONL/text and parser tests, actual shell online route, unchanged proof route, shell syntax/mode, workspace/typecheck/changed-file lint, nearest local matrix; no aggregate for an unchanged barrel/runner/package/compiler boundary |
| Lambdapi/kernel-dependent target | `EMDASH_TYPECHECK_TIMEOUT=90s make -C emdash2 check` plus every nested-SOP gate actually triggered |
| Cross-layer release/publication | affected browser/print/kernel gates and eventually `check:all`; never run merely for reassurance |

AI-PROOF-1, AI-PROOF-2, AI-WORKSPACE-1A, AI-WORKSPACE-1B1,
AI-REMOTE-1B1, and AI-REMOTE-1B2A change only generic TypeScript
proof/workspace source, artifact, command-adapter, or Node-edge behavior. Their
proportional boundary is focused tests, typecheck/lint, diff/link and shell
hygiene, a nearest matrix where appropriate, and one complete shared
TypeScript gate only when a tranche actually changes that shared boundary.
Recent green aggregate evidence is carried forward and must not be repeated
merely for reassurance. No kernel, Lambdapi, browser-product build, print,
book, or `check:all` gate is required unless the exact diff expands into those
layers.

## Recovery Checklist

On every persistent continuation:

1. read root `AGENTS.md`, this plan, the handoff, and the persistent-goal Git
   workflow;
2. inspect every worktree and staged/unstaged state separately;
3. verify current `HEAD` and its relationship to the recorded checkpoint and
   baseline;
4. preserve all unrelated changes and completed elaborator history;
5. relocate current definitions and consumers with `rg`;
6. recover the one in-progress row and its exact diff;
7. run only its required bounded baseline/gates;
8. update this Work and Decision Ledger with evidence or a rejected
   hypothesis; and
9. continue on the established dedicated goal branch, self-approve only a
   frozen bounded proposal, and checkpoint only under every condition in the
   persistent-goal Git SOP; and
10. never infer push, merge, PR, publication, release, deployment, history
    rewriting, or cleanup authority from local checkpoint authority.

The Infinity Codex archive is recovery evidence only. Active code, current
authority/SOP, this living plan, and actual Git state outrank archived prose.

## Persistent `/goal` Objective

```text
Implement and qualify the AI-native TypeScript/emdash workspace and proof
architecture in
docs/TYPESCRIPT_EMDASH_AI_NATIVE_WORKSPACE_AND_PROOF_PLAN.md.

Treat AI-PROOF-1, AI-PROOF-2, AI-WORKSPACE-0, AI-WORKSPACE-1A, and the
exact-closure AI-WORKSPACE-1B1 proof attachment and AI-WORKSPACE-1B2A
same-module fragment chain and AI-WORKSPACE-1B2B cross-module fragment graph
and AI-REMOTE-1A locked supplied-text materialization/offline-cache-data slice
and AI-REMOTE-1B0 platform audit and AI-REMOTE-1B1 TypeScript mounted-file/
immutable-cache slice and AI-REMOTE-1B2A explicit-root local `workspace check`
command as complete. Preserve AI-REMOTE-1A's recorded 1,486-test, 224-suite
aggregate, AI-REMOTE-1B1's 108-test nearest matrix, and AI-REMOTE-1B2A's
117-test nearest matrix; do not repeat an unchanged long gate for reassurance.

Treat AI-REMOTE-1B2B hosted packaging/template delivery as deferred until a
distributable emdash runtime, compatible Node version, template-owned install
contract, agent skill, and generic platform source capability are selected.
Do not change `~/closerfans` merely to simulate those prerequisites.
AI-REMOTE-1B3 remains pending one real network consumer. Keep actual fetch,
platform HTTP/MCP integration, credentials, retries, redirects, signed URLs,
and publication unimplemented until their distinct audits select the smallest
consumer-backed contracts. Never treat a URL, mutable branch, observed digest,
or cached compiled object as authority.

Treat AI-SYNTH-0 and the final-green AI-SYNTH-1A finite global-dictionary
selection as complete. Preserve its explicit qualified candidate scope,
finite-list termination, missing/success/ambiguity behavior, fresh bounded
checking, deterministic complete trace, and rechecked explicit Core result.
Preserve its focused 11-test suite and nearest 44-test/four-suite matrix; do
not repeat the unchanged 1,486-test aggregate for reassurance. Ordinary
metavariable solving, proof-time `unif_rule`, and dictionary synthesis remain
separate, and the adjunction witness remains the first mathematical follow-up
after its pure-TypeScript dependency graph exists.

The next synthesis action is a read-only AI-SYNTH-1B exact-consumer audit of
the current TypeScript surface elaborator and workspace-source contracts. It
must identify one real omitted-implicit authoring path before freezing any
portable instance annotation, local/imported scope, or synthesis-request node.
Do not implement AI-SYNTH-1B merely by exposing 1A through a global registry or
string-parser special case. If no exact consumer is dependency-ready, leave it
explicitly gated and select another local row.
Do not infer a provider from fragment order, symbol spelling, or a current
compiled object. Preserve explicit backend-neutral Core and all existing
checker, session, compiler, runtime, proof, visibility, and
categorical-owner trust boundaries. Do not introduce a new kernel, duplicate
declaration AST/checker, guessed fragment providers, category-specific proof
cases, retained callbacks, mandatory parser, MCP-owned state, typeclass
search, remote imports, arbitrary-path execution, or browser-side
filesystem/hash authority.

After each bounded result, synchronize the plan's Work/Decision Ledgers and
run its proportional gates. Prefer focused and nearest checks and reuse recent
green aggregate evidence; run another long aggregate only when an exact new
shared-boundary diff and repository SOP strictly require it. Keep the
implemented backend focused on the small TypeScript/emdash checker/evaluator.
Retain backend-neutral explicit Core and deterministic Lambdapi/emdash
emission/checking as an optional later adapter and conformance route; do not
add a backend flag or claim Lambdapi execution until that separate path exists.
After AI-SYNTH-1A, continue with AI-SYNTH-1B only when an exact authoring/
workspace consumer can freeze portable annotations and local/implicit scope.
Recursive indexed search remains AI-SYNTH-2 and requires its own consumer.
Paper/browser integration remains separately consumer-gated.
Revise or reject a plan row when implementation evidence contradicts it; do
not preserve a failed architecture for narrative continuity.

On every continuation recover current authorities, plans, code, tests,
worktrees, staged/unstaged diffs, checkpoint ancestry, and validation evidence.
Follow root AGENTS.md and docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md; follow
emdash2/AGENTS.md for every action under emdash2. Preserve unrelated work.
This objective authorizes plan-scoped source/test/document edits and bounded
validation. By direct user direction on 2026-08-08, an unattended continuation
may self-approve a frozen proposed tranche and may create validated local
checkpoint commits on the established dedicated goal branch as required by
docs/PERSISTENT_GOAL_GIT_EXPERIMENTATION.md. Never checkpoint unrelated or
partial work. This does not authorize pushes, merges, PRs, publication,
release, deployment, history rewriting, cleanup, or removal of any existing
worktree. Direct user decision D-AI-NATIVE-050 authorized only the already
completed fast-forward of checkpoint `a3ba93a` into local `main`; it grants no
future merge authority.

Continue safe dependency-ready work until every scoped row is implemented,
rejected with durable evidence, or explicitly deferred behind a concrete
prerequisite or human decision. Do not mark the goal complete merely because
the two proof slices are green.
```
