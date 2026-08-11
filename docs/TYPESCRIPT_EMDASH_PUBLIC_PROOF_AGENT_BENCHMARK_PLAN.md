# TypeScript/Emdash Public Proof-Agent Benchmark Plan

Status: living plan; post-`STDLIB-8B` audit complete; exact non-authorizing
`AGENT-EVAL-12B1` proposal checkpoint `a181885` is separately approved by the
immutable review at `d271c33`. The internal corpus/interchange implementation
is proportionally qualified in the checkpoint containing the completion
record below; the exact checkpoint is pinned by the immediate ledger-only
follow-up.

Date: 2026-08-11

Branch: `goal/typescript-emdash-proof-assistant-v1`

Worktree: `/home/user1/emdash1-classes-v1`

Governing plan:
[`TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md`](./TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md).

Exact predecessors:

- public `@hotdocx/emdash@0.2.0` at release checkpoint `ab513f7`;
- internal `AGENT-EVAL-12A` evaluator at semantic checkpoint `f46ff9a`;
- CloserFans/GetPaidX TypeScript workspace at `bd4146b` and read-only goal
  graph workspace at `5c0d0c1`;
- root-source-qualified PathOut/PathInd profile at proposal/review checkpoints
  `85b560e`/`d7d7428`; and
- synchronized PathOut graduation ledger checkpoint `3135747`.

Post-`STDLIB-8B` audit and this initial plan are checkpointed at `7aeb783`.

This plan adds no behavior by itself. It records why public agent evaluation
is now the only dependency-ready product stream and prevents that product
work from silently widening proof authority, package authority, or hosted
action authority.

## Executive Decision

Emdash should expose a reproducible benchmark in the same form in which an AI
agent actually works: immutable source-backed proof tasks in, explicit inert
patch attempts out, and fresh TypeScript/emdash replay as the acceptance
authority. The semantic evaluator remains browser-safe and invokes no model.
Filesystem acquisition, process execution, model invocation, resource
enforcement, publication, and hosted workspace operation remain outer layers.

`AGENT-EVAL-12B` is therefore repartitioned into four ordered product slices:

1. qualify a representative source-backed corpus and canonical interchange;
2. add an explicit Node runner plus public package/browser presentation;
3. release an exact package version and install one additive CloserFans
   benchmark workspace; and
4. record reproducible real-agent runs and graduate only the claims that the
   measured corpus supports.

The next bounded action is not an npm release, sibling edit, model run, or
PathOut export. It is a non-authorizing executable proposal for slice 1.

## Post-`STDLIB-8B` Readiness Findings

### PathOut is not an LF patch-benchmark case

The newly graduated PathOut presentation has four finite expression forms and
an explicit transfer-backed semantic checker. The 12A evaluator instead
requires a canonical `CoreLfProofDevelopmentSourceSnapshot`, one freshly open
named proof goal, and an inert `CoreProofPlanPatch`. Those are different task
kinds with different trusted inputs.

PathOut proves that the TypeScript backend can host substantial curated
mathematics. It does not make a PathOut request a valid 12A case. This plan
forbids wrapping the static qualification report as a successful proof-agent
attempt or weakening the 12A case invariant. A future benchmark may add a
separately versioned `semantic-program` task family after it has its own
attempt and replay contract; 12B1 remains an LF proof-patch corpus.

### Why the agent-evaluation stream is now ready

Four independent prerequisites now exist:

1. `lf_proof_agent_benchmark.ts` already owns immutable cases, suites,
   attempts, runs, fresh replay, stable diagnostics, and integer metrics.
2. The public `/workspace` and `/authoring` entries expose canonical proof
   sources, plan patches, constructor/`have`/`refine` management, exact
   premise search, proof-producing simplification, structures, classes,
   ancestor-sharing metadata, and bounded instance synthesis.
3. CloserFans has a real ordinary-Node `emdash_ts` workspace whose TypeScript
   file is the source of authority and whose `goals`/`check` commands replay
   it without a proof server.
4. The current repository contains independently checked fixtures for the
   proof-management, automation, maintenance, and class/instance behaviors
   from which a reviewed corpus can be factored without inventing semantics.

These facts make corpus construction and interchange design actionable. They
do not make the current five-case 12A test fixture representative, public, or
hosted.

### Rows which remain deferred

| Row | Audit result | Concrete remaining prerequisite |
| --- | --- | --- |
| `SIMP-5B2` | deferred unchanged | No production or sibling consumer calls `simplifyCoreProofPlan`; PathOut uses transfer conversion rather than explicit equality evidence. Select a real 5B1 consumer and freeze congruence plus premise-discharge semantics first. |
| `INDEX-SEARCH-6B` | deferred unchanged | Current non-test consumers are proof maintenance, 12A evaluation, and the bounded obvious provider. There is no theorem-export owner, relationship/use graph, or measured retrieval corpus yet. The new 12B corpus may later satisfy the measurement prerequisite, but does not do so before it exists. |
| `COUNTEREVIDENCE-10` | deferred unchanged | No selected claim supplies a finite domain, interpretation, evaluator/model-finder contract, or counterexample-versus-no-counterexample evidence policy. Checker negatives are not countermodels. |
| `EXTERNAL-CERT-11` | deferred unchanged | No selected solver, certificate format, problem corpus, or independent reconstructor/checker exists. No relevant solver executable is present on the audited host. |
| `GOAL-GRAPH-14B4` | deferred unchanged | The goal-graph workspace is derived and read-only. No exact Emdash status mutation, actor/signature binding, idempotency key, permission rule, or audit contract has been selected. |

## Product Architecture

```text
TypeScript proof source + corpus provenance
                    │
                    ▼
       canonical benchmark corpus
                    │
        agent emits an inert attempt
                    │
                    ▼
       pure 12A evaluator and checker
                    │
                    ▼
       canonical report with evidence class

Node runner / model host / GetPaidX / publication
remain outside this semantic path.
```

### Layer 1: evaluator authority

The existing 12A evaluator remains the sole scoring authority. A corpus layer
may compose it but must not add an alternate checker, trust provider success,
accept a mutable “solved” flag, persist patched source, or present
provider-reported time/tokens as independently measured.

### Layer 2: reviewed corpus

A corpus is a versioned browser-safe manifest over exact 12A cases. Each
entry adds only curation data:

- stable case and track IDs;
- task kind, title, feature labels, and concise agent-facing instruction;
- origin `emdash-native` or `lean4-manual-translation`;
- exact source/provenance locator and translation note;
- the embedded canonical 12A case;
- allowed attempt profiles and expected evidence class; and
- optional public reference-attempt identity kept distinct from the task.

The manifest is not a theorem database, a model prompt, or a claim that its
feature labels were inferred by the kernel. Case reconstruction still proves
the open-goal and scope invariants; curation metadata is validated portable
data.

### Layer 3: canonical interchange

The browser-safe layer must provide strict parse/validate/serialize functions
for the corpus and the exact attempt/run/report records it exposes publicly.
Canonical bytes, explicit revisions, stable case binding, bounds, and fresh
reconstruction are mandatory. Unknown fields, unsupported revisions,
duplicate IDs, stale case bytes, nonportable values, or noncanonical data are
rejected. A JSON envelope is transport, never proof authority.

Agents may author attempts as direct TypeScript values and serialize them.
Language-neutral hosts may exchange the same canonical JSON. Neither route
requires an MCP/LSP proof server or an implicit process session.

### Layer 4: outer runner

The later Node runner owns explicit filesystem paths, stdout/stderr, exit
codes, optional process-level resource accounting, and any model/provider
adapter. It imports the browser-safe corpus/evaluator rather than duplicating
them. Its first contract reads a supplied suite and supplied run; it does not
invoke a model automatically.

### Layer 5: distribution and hosting

Public package export, package version, npm publication, and a CloserFans
workspace are separate rows. The hosted workspace should keep one visible
TypeScript attempt file as the AI patch point, regenerate canonical run/report
artifacts, and replay them statelessly. It must not add a privileged Emdash
MCP action or mutable proof-state service merely to host the benchmark.

## Representative Corpus Contract

The first corpus is representative of the currently public AI-proof workflow,
not of every Emdash mathematical profile. It must contain at least one freshly
replayed case from each of these six tracks and at least eight cases overall:

1. **explicit proof construction** — exact and one-step application with
   relevant-premise labels;
2. **source-level proof management** — constructor, contextual `have`, typed
   `refine`, or direct goal coupling, with at least two of those mechanisms
   represented across the track;
3. **bounded automation** — a candidate originating from exact search,
   obvious-proof generation, or proof-producing simplification, while final
   acceptance remains ordinary replay;
4. **structures and classes** — checked lowered structure/class declarations,
   explicit provider scope, instance synthesis, and one ancestor-sharing or
   ambiguity-sensitive case;
5. **maintenance and revision** — different previous/current canonical
   sources with conservative impact plus fresh selected-proof replay; and
6. **manual Lean-shaped translation** — at least one small binder/class-style
   theorem translated into explicit TypeScript/emdash with its original
   locator, license note, and a written semantic correspondence boundary.

The corpus must also include at least one intentional abstention or rejected
attempt in its conformance run. Public reference attempts are baselines, not
claims of optimality. No hidden test answer is required for the first
infrastructure release, and no composite leaderboard score is authorized.

The proposal must probe every track through existing owners before promising
the final case matrix. If a feature cannot inhabit a 12A case without changing
its trusted task kind, the proposal must record that incompatibility and
replace the case with a faithful same-track consumer rather than weakening
the evaluator.

## Work Ledger

| Row | State | Exit gate |
| --- | --- | --- |
| `AGENT-EVAL-12B0` | complete; read-only selection | Audit/plan checkpoint `7aeb783` proves the evaluator/public-workspace/host prerequisites and freezes the four-slice architecture without behavior. |
| `AGENT-EVAL-12B1` | implementation complete; exact checkpoint pending ledger pin | The full six-track/ten-case corpus and strict interchange satisfy the separately reviewed contract. Nine owner-generated ordinary patches pass fresh unchanged 12A replay; the genuine ambiguity case abstains. Focused semantic/static/browser gates are green without public or later-row effects. |
| `AGENT-EVAL-12B2` | next proposal selected; implementation gated | Requires the exact qualified 12B1 checkpoint, then a separately frozen/reviewed contract for the explicit Node runner, browser/documentation presentation, package capability/export, packed consumers, and one final shared-boundary gate. No publication. |
| `AGENT-EVAL-12B3` | gated | Requires qualified 12B2 plus a separately frozen package version/release and fresh CloserFans edit-time audit. Publish exact bytes, then add one additive ordinary-Node benchmark workspace on an isolated sibling branch. |
| `AGENT-EVAL-12B4` | gated | Requires the installed hosted consumer and one separately frozen provider/run policy. Record reproducible real-agent runs, preserve raw canonical attempts/reports where policy allows, and graduate only measured claims. |

The separately reviewed `AGENT-EVAL-12B1` implementation is complete. The
next bounded action is a non-authorizing `AGENT-EVAL-12B2` proposal after the
exact completion checkpoint is pinned. No public export, runner, package, or
release effect follows merely from selecting that proposal.

## `AGENT-EVAL-12B1` Proposal Requirements

The executable proposal must pin:

1. exact source/checkpoint digests for 12A, public package entries, selected
   proof/class owners, and the CloserFans starter consumer;
2. an exact feasible case matrix satisfying all six tracks and eight-case
   minimum, including which existing owner creates each source and reference
   patch;
3. additive corpus/interchange type and function names;
4. exact revisions, limits, canonical order, parser rejection policy, and
   deep-freeze requirements;
5. reference complete/incomplete/rejected/abstained outcomes and their
   evidence class;
6. browser closure and explicit denials of Node, model, network, filesystem,
   Lambdapi, source persistence, hidden sessions, and new Core/checker/rule
   authority;
7. absence from public barrels, package manifests, and sibling repositories
   during 12B1; and
8. focused tests, typecheck, changed-file lint, static non-export checks, and
   exact staged-diff hygiene.

The proposal may refine case names after executable feasibility probes, but it
must not reduce the six-track/eight-case representativeness boundary merely
to make implementation convenient. Any correction requires a new checkpoint
and separate review.

## `AGENT-EVAL-12B1` Frozen Proposal V1

Date: 2026-08-11

State: non-authorizing proposal complete at exact checkpoint `a181885` and
separately approved by the immutable review below.

The executable proposal is
[`lf_proof_agent_public_corpus_proposal.ts`](../src/v3_2/lf_proof_agent_public_corpus_proposal.ts),
with drift, digest, representativeness, authority, and non-export tests in
[`v3_2_proof_agent_public_corpus_proposal_tests.ts`](../tests/v3_2_proof_agent_public_corpus_proposal_tests.ts).

It pins thirteen current Emdash owners, exact Emdash/CloserFans/Lean
checkpoints, exact audited sibling/Lean file digests, and a ten-case matrix
over all six required tracks. The Lean-shaped case is a manual attributed
translation of Lean 4 `tests/elab/diamond1.lean` at checkpoint
`f29e9e488ea8242c875806e4b0564820c2d553b2`, under the recorded Apache-2.0
license. It is not a Lean parser or claimed syntax-level translation.

The matrix contains two explicit proof-construction cases, two source-level
management cases, two automation cases, two structure/class cases, one source-
revision maintenance case, and one Lean-shaped multiple-inheritance case.
The shared-diamond and ambiguity evidence is not aspirational: the current
class/inheritance/synthesis owners pass exact checked tests for canonical
diamond collapse, table hits, genuine equal-priority ambiguity, saturated
class-call insertion, and independently checked evidence. The proposal still
requires the corpus implementation to make every selected case inhabit the
unchanged 12A case/attempt/replay contract.

The proposal and focused test SHA-256 values are, respectively,
`ecbd67496a99775c13357d9175b623200e20e79346d62b00b8773bc5e7d08a60`
and
`b128059af3803eb077fc37b9438e9ef299eb2bf3fab6acb7143f07064ecf71d9`.

Proportional validation:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_agent_public_corpus_proposal_tests.ts
  passed: 8/8 tests, 1 suite

nearest evaluator, plan/template, simplifier/obvious, maintenance,
class-inheritance-lowering, and instance-scope command
  passed: 104/104 tests, 18 suites

./scripts/pnpmw exec tsc --noEmit --pretty false
  passed

eslint over proposal, proposal test, and test-runner owner
  passed

git diff --check
  passed
```

No browser build, package build, installed consumer, root `check:ts`,
`check:all`, kernel/Lambdapi, book/print, sibling mutation, registry,
deployment, model invocation, or long aggregate ran. This behavior-free,
non-export proposal changes none of those boundaries. Its test is directly
registered in `tests/main_tests.ts`; exact import plus its direct green run is
the registration evidence, not a claim that the root aggregate passed.

### Separate Review And Implementation Authority

The immutable review is
[`lf_proof_agent_public_corpus_review.ts`](../src/v3_2/lf_proof_agent_public_corpus_review.ts),
with focused tests in
[`v3_2_proof_agent_public_corpus_review_tests.ts`](../tests/v3_2_proof_agent_public_corpus_review_tests.ts).
It approves only proposal checkpoint `a181885` and proposal SHA-256
`ecbd67496a99775c13357d9175b623200e20e79346d62b00b8773bc5e7d08a60`
under delegated unattended authority, with later human supersession. The
exact review checkpoint is `d271c33`.

The review's SHA-256 is
`f3f38e47a84e365a7154ed3717f1375fdb62e332185fb0529770c34fef735e41`;
its focused test SHA-256 is
`ce9a31c6b7631e9cdf6c8f9a5f0836b942697c200d767e0c8190230c367ae999`.
Fourteen combined proposal/review tests, root typecheck, focused lint,
non-export checks, and diff hygiene are green.

Approval adds one precise implementation condition to the matrix: curation
labels never count as feature evidence. Each non-abstaining reference owner
must generate an ordinary patch accepted by fresh unchanged 12A replay. The
ambiguity case must retain finite synthesis evidence and abstain without a
hidden winner. The manually translated Lean case must retain source/license
attribution and a written semantic correspondence without parser-parity
claims.

The review authorizes only the two internal browser-safe modules and focused
tests named by the proposal. It does not authorize public barrels, a Node
runner, a browser product, a package version/release, sibling mutation, a
model invocation, hosted state, PathOut task conversion, or any Core/checker/
rule change. No long aggregate is rerun for this behavior-free review.

## `AGENT-EVAL-12B1` Implementation Completion Record

Date: 2026-08-11

State: implementation complete and proportionally qualified; the semantic
checkpoint is the commit containing this record and is pinned by the next
ledger-only commit.

The implementation adds exactly the two reviewed internal browser-safe
owners:

- [`lf_proof_agent_interchange.ts`](../src/v3_2/lf_proof_agent_interchange.ts)
  strictly parses canonical case, suite, attempt, run, and report bytes. It
  rejects malformed JSON, unknown fields at every nested level, unsupported
  revisions, noncanonical bytes, stale source identities, and forged derived
  reports. Accepted reports are freshly reconstructed and reevaluated by the
  unchanged 12A owner.
- [`lf_proof_agent_public_corpus.ts`](../src/v3_2/lf_proof_agent_public_corpus.ts)
  constructs, serializes, and strictly parses the fixed six-track/ten-case
  corpus. Every parsed corpus is rebuilt from current owners and its canonical
  bytes are compared before use; parsed values are deeply frozen.

The ten cases cover explicit `exact`/`apply`, contextual `have`, coupled
`refine`, bounded obvious proof, proof-producing transport simplification,
source-revision maintenance, finite shared-diamond instance synthesis,
genuine equal-priority ambiguity, and an attributed manual semantic
translation of Lean 4 `tests/elab/diamond1.lean`. The two class fixtures use a
real implicit structure parameter and remain standalone: they neither depend
on nor alter the existing presheaf, sieve, site, sheafification, or scheme
mathematics.

Fresh unchanged 12A evaluation yields exactly nine `accepted-complete`
results, zero incomplete results, zero rejected results, and one deliberate
`abstained` result for ambiguity. Every non-abstaining reference attempt is an
ordinary patch produced through its named existing owner and accepted by
fresh replay. Curation labels, the reference run, and the manually translated
Lean example are explicitly non-authoritative; no parser-parity claim is
made.

The exact source/test SHA-256 values at qualification are:

```text
lf_proof_agent_interchange.ts
  0df6d032d8f67162a499578e59f39f44fc724a08b4be4fa1a6a7c1bef5ce574d
lf_proof_agent_public_corpus.ts
  8d207b36ff5d4b645494bc696b681d23b08d0132b7d8b9831065b70a326c97e5
v3_2_proof_agent_interchange_tests.ts
  b730fdabdc22ef0bf762a32e136dace886a9a657bd7b82a8b2bc75eec5e60de3
v3_2_proof_agent_public_corpus_tests.ts
  f699b3cf7a26ea2aca2bef57cf7e8c790614b00be425554230911434c0046c9b
```

The canonical self-contained corpus is 5,884,285 UTF-8 bytes. That bounded
measurement is retained as a 12B2 transport/presentation design input; it is
not silently replaced with references or a looser parser in 12B1.

Proportional validation:

```text
strict interchange plus representative corpus
  passed: 18/18 tests, 2 suites

unchanged AGENT-EVAL-12A evaluator
  passed: 5/5 tests, 1 suite

browser-directed closure, including the new transitive corpus probe
  passed: 22/22 tests, 1 suite

./scripts/pnpmw exec tsc --noEmit
  passed

eslint over both implementation owners, both focused tests,
the browser-closure owner, and the test registry
  passed

git diff --check
  passed
```

The already-green 14 proposal/review tests and 104 nearest-owner tests are
carried forward because their frozen owners and digests did not change. Root
`check:ts`, root-test, `check:all`, package/installed-consumer, browser-product
build, Lambdapi/kernel, print/book, sibling, registry, deployment, model, and
hosted checks did not run. Public barrels, package manifests, semantic Core,
checker/rules, and every later-row surface remain unchanged; the omitted long
aggregates are not reported as passes.

## Validation Policy

`AGENT-EVAL-12B0` and the first non-behavioral proposal require only exact
document/source inventory, link/heading review, and diff hygiene.

During 12B1, use the new corpus/interchange suite plus nearest 12A,
proof-plan/refiner, simplifier/search/obvious, maintenance, and class/instance
tests. Run root typecheck and changed-owner lint. Run one browser closure probe
because the semantic boundary is browser-safe. Do not run `check:ts` or
`check:all` while public/package boundaries remain unchanged.

12B2 changes a public package barrel. Its final candidate therefore requires
workspace check, focused tests, typecheck/lint, browser closure/build, package
build and installed ESM/CommonJS/strict-NodeNext/browser consumers, followed
by one complete `check:ts` only if root `AGENTS.md` still requires it and no
direct human waiver supersedes that exact boundary. Never rerun that aggregate
for reassurance. Release, sibling, and hosted checks belong only to 12B3.

Every result must state skipped or waived aggregates as omissions, not passes.
No Lambdapi command is required unless the selected corpus unexpectedly
depends on active kernel names; any such command remains bounded to 90 seconds.

## Non-Goals

This stream does not authorize:

- a declaration/class parser or a general inductive/HIT frontend;
- a tactic language, mutable prover server, or authoritative MCP/LSP service;
- embedding an AI provider, prompt, API key, or network client in semantic
  modules;
- treating reported usage, curation labels, reference patches, or leaderboard
  rank as proof evidence;
- adding a second checker, new trusted Core node, unification rule, runtime
  rewrite, typeclass rule, or mathematical axiom;
- relabeling PathOut qualification as a proof-patch benchmark;
- public export, package versioning, npm/GitHub release, sibling mutation,
  push, merge, deployment, or cleanup before its exact later row; or
- changing the published/in-review GetPaidX MCP contract merely to expose the
  first benchmark.

## Recovery

On continuation:

1. inspect all worktrees, branch ancestry, staged/unstaged state, and current
   plan checkpoints;
2. read this plan and the governing master ledger;
3. preserve CloserFans' unrelated untracked review plan;
4. keep only one semantic row active;
5. treat 12B1 as complete only at the exact checkpoint pinned by its immediate
   ledger follow-up;
6. freeze and separately review a non-authorizing 12B2 proposal before any
   public runner, browser, barrel, package, or consumer implementation; and
7. synchronize both plans and exact evidence before every rollback-safe
   commit.
