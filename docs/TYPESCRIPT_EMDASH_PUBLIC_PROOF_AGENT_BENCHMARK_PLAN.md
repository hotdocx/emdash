# TypeScript/Emdash Public Proof-Agent Benchmark Plan

Status: living plan; post-`STDLIB-8B` audit complete; exact non-authorizing
`AGENT-EVAL-12B1` proposal checkpoint `a181885` is separately approved by the
immutable review at `d271c33`. The internal corpus/interchange implementation
is complete and proportionally qualified at exact checkpoint `d0d3764`. A
non-authorizing `AGENT-EVAL-12B2` public-surface proposal is complete at exact
checkpoint `ba49705` and is separately approved by the immutable review in the
exact checkpoint `8c9652a`. The bounded implementation is complete and
proportionally qualified at exact semantic checkpoint `93c9804`. The
read-only `AGENT-EVAL-12B3` package-release and CloserFans host audit is now
frozen in the proposal contract below; implementation remains gated on a
separate immutable review.

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

The first two slices are now implemented without an npm release, sibling edit,
model run, or PathOut task conversion. The exact 12B2 checkpoint is pinned,
and the next bounded action has therefore been limited to the non-authorizing
12B3 version/release and fresh CloserFans edit-time audit below—not
publication itself.

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
| `AGENT-EVAL-12B1` | complete at `d0d3764` | The full six-track/ten-case corpus and strict interchange satisfy the separately reviewed contract. Nine owner-generated ordinary patches pass fresh unchanged 12A replay; the genuine ambiguity case abstains. Focused semantic/static/browser gates are green without public or later-row effects. |
| `AGENT-EVAL-12B2` | complete at `93c9804` | The isolated package subpath, strict stateless repository adapter, v15 capability record, lazy browser presentation, transitive budgets, retained least-authority package policy, and installed consumer matrix satisfy all ten review conditions. |
| `AGENT-EVAL-12B3` | proposal/audit frozen; implementation review-gated | The commit containing the contract below freezes exact `0.3.0` release, workflow-maintenance, Pages-side-effect, and new ordinary-Node `emdash_benchmark` workspace boundaries. Its exact proposal checkpoint must be pinned and separately reviewed before any version, workflow, Git, registry, Release, deployment, or sibling mutation. |
| `AGENT-EVAL-12B4` | gated | Requires the installed hosted consumer and one separately frozen provider/run policy. Record reproducible real-agent runs, preserve raw canonical attempts/reports where policy allows, and graduate only measured claims. |

The separately reviewed `AGENT-EVAL-12B1` implementation is complete. The
separately approved `AGENT-EVAL-12B2` implementation is also complete and its
exact semantic checkpoint is `93c9804`. No release, version, sibling, model,
or hosted effect follows from either completion.

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

./node_modules/.bin/tsc --noEmit --pretty false
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

State: implementation complete and proportionally qualified at exact semantic
checkpoint `d0d3764`.

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

## `AGENT-EVAL-12B2` Frozen Proposal V1

Date: 2026-08-11

State: non-authorizing proposal complete at exact checkpoint `ba49705`;
separate immutable review remains mandatory.

The executable proposal is
[`lf_proof_agent_public_surface_proposal.ts`](../src/v3_2/lf_proof_agent_public_surface_proposal.ts),
with focused drift, digest, package, runner, browser-budget, authority, and
non-effect tests in
[`v3_2_proof_agent_public_surface_proposal_tests.ts`](../tests/v3_2_proof_agent_public_surface_proposal_tests.ts).
It pins all seventeen current evaluator/corpus, package, capability, runner,
and browser owners to the completed 12B1 ledger `3e3fcf8`.

The proposal makes four architectural choices:

1. Add one isolated browser-safe `@hotdocx/emdash/benchmark` subpath exporting
   the unchanged 12A evaluator, strict interchange, and fixed public corpus.
   The root, `authoring`, and `workspace` entries do not reexport it, so their
   consumers do not acquire the benchmark closure.
2. Keep the npm package's existing least-authority rule: no npm bin, install
   hook, runtime dependency, or packed CLI source. The explicit Node reference
   adapter is instead `./scripts/emdash benchmark`; a later CloserFans runner
   imports the browser-safe package API in 12B3.
3. Give that stateless adapter five artifact commands: compact `catalog`,
   canonical `case`, canonical full `corpus`, canonical `reference`, and
   strict `evaluate --run-file PATH`. Evaluation reads exactly one bounded
   file and freshly replays it; the adapter neither scans directories, writes
   files, spawns a provider, invokes a model, accesses a network, retains a
   session, nor claims to enforce provider-reported resource limits.
4. Add a user-triggered dynamic browser import. Page load neither constructs
   nor serializes the corpus. The panel shows exact tracks, cases, owners,
   features, nine accepted references, one honest abstention, and the explicit
   absence of a leaderboard or model-performance claim.

The payload decision is measured rather than guessed. Canonical corpus text
is 5,884,285 UTF-8 bytes. A standalone minified browser bundle of the current
corpus closure using esbuild 0.21.5 is 548,200 bytes / 136,817 gzip bytes; the
current Vite 5.4.19 initial page chunk is 436,361 bytes / 117,869 gzip bytes.
The proposal caps the candidate initial chunk at 465,000 / 130,000 gzip bytes
and the benchmark lazy closure at 650,000 / 175,000 gzip bytes. The initial
chunk must not contain the corpus revision; the lazy closure must.

Proposal/test SHA-256 values are, respectively,
`c820786bd4974313fff2eae5e3d459f29d46a2a18a5c97690047fe324364e759`
and
`d1bccbc2049330e686a9a2c148c36351c29a902c19432c6f7ab374d031b7045b`.

Proportional proposal validation:

```text
node --require ts-node/register --test \
  tests/v3_2_proof_agent_public_surface_proposal_tests.ts
  passed: 8/8 tests, 1 suite

./scripts/pnpmw exec tsc --noEmit
  passed

eslint over proposal, proposal test, and test registry
  passed

./scripts/pnpmw run package:build
  passed as current-package baseline

direct existing emdash-template tsc plus Vite build
  passed: 157 modules; initial chunk 436,361 bytes

git diff --check
  passed
```

The prescribed wrapper attempt for the unchanged standalone browser fixture
did not reach its build: pnpm's dependency-status subprocess could not find a
plain `pnpm` executable in this Corepack-only environment. Direct checked-in
fixture binaries then passed typecheck and Vite build. This is recorded as an
environmental wrapper limitation, not a wrapper pass; the 12B2 implementation
must still satisfy the exact browser gate.

No package verifier, installed consumer, release preflight test, root
`check:ts`, root-test, `check:all`, Lambdapi/kernel, print/book, sibling,
registry, release, deployment, model, or hosted operation ran for this
proposal. Those public-boundary checks belong to the implementation candidate;
the long aggregates remain subject to the direct standing waiver and are not
reported as passes.

### Separate Review And Implementation Authority

The immutable review is
[`lf_proof_agent_public_surface_review.ts`](../src/v3_2/lf_proof_agent_public_surface_review.ts),
with focused tests in
[`v3_2_proof_agent_public_surface_review_tests.ts`](../tests/v3_2_proof_agent_public_surface_review_tests.ts).
It approves only exact proposal checkpoint `ba49705`, proposal SHA-256
`c820786bd4974313fff2eae5e3d459f29d46a2a18a5c97690047fe324364e759`,
and proposal-test SHA-256
`d1bccbc2049330e686a9a2c148c36351c29a902c19432c6f7ab374d031b7045b`
under delegated unattended authority with later human supersession. The exact
review checkpoint is `8c9652a`.

The review/test SHA-256 values are, respectively,
`7421885c8f01f9c7fec5d3be628470b8af94550c671ecc41939ca79a838f8fb8`
and
`8b0d075341697331bf5f446b5ecba1e98ccf2040c330deb70a7e02ffcd68dbe7`.

Approval adds ten exact implementation conditions. The compact catalog must
be a revisioned canonical, deeply frozen, non-authoritative projection with no
case text. `evaluate` must enforce the raw byte ceiling before fatal UTF-8
decoding, read one explicit file, use the strict run parser and fresh unchanged
12A replay, and emit stable errors without stacks or artifact contents. Every
JSONL artifact command must use its owning newline-terminated serializer.

Only `@hotdocx/emdash/benchmark` may expose the benchmark owners; core,
authoring, and workspace entries remain exact and core-only consumers must not
acquire the corpus closure. Release preflight continues to reject npm bins,
install hooks, runtime dependencies, scripts, and packed CLI source. Browser
gates measure complete transitive initial/static and benchmark/dynamic
closures rather than one guessed chunk; page load is inert and the explicit
view remains a baseline presentation rather than proof or performance
authority. Packed ESM, CommonJS, strict NodeNext, and browser consumers are all
required.

Combined proportional review validation is green:

```text
proposal plus separate review
  passed: 16/16 tests, 2 suites

./scripts/pnpmw exec tsc --noEmit
  passed

eslint over proposal/review, focused tests, and test registry
  passed

git diff --check
  passed
```

The approval authorizes no change to 12A, 12B1, Core, checker, or rules; no
npm bin/dependency; no package version, publication, release, sibling edit,
real-agent run, model/network call, hosted action, push, merge, tag,
deployment, or aggregate-pass claim.

## `AGENT-EVAL-12B2` Implementation Completion Record

Date: 2026-08-11

State: implementation complete and proportionally qualified at exact semantic
checkpoint `93c9804`.

The implementation realizes the reviewed surface without changing 12A/12B1
semantics:

- [`package_benchmark.ts`](../src/v3_2/package_benchmark.ts) is the sole new
  browser-safe public source entry. It exports the unchanged evaluator,
  strict interchange, and representative corpus. Root, `authoring`, and
  `workspace` entries remain unchanged and exclude the corpus closure.
- [`lf_proof_agent_benchmark_cli.ts`](../src/v3_2/lf_proof_agent_benchmark_cli.ts)
  is an explicit stateless Node adapter behind `./scripts/emdash benchmark`.
  Its `catalog`, `case`, `corpus`, `reference`, and `evaluate --run-file`
  commands use exact canonical serializers. `evaluate` checks the 32 MiB raw
  ceiling before fatal UTF-8 decoding, reads exactly one explicit path,
  strictly parses, and freshly replays through unchanged 12A. Stable errors
  contain neither stacks nor artifact contents.
- `@hotdocx/emdash/benchmark` is isolated as a fourth package entry while the
  package remains version `0.2.0`, dependency-free at runtime, script-free,
  bin-free, and install-hook-free. The repository adapter is deliberately not
  packed as an npm CLI.
- The browser's fifth reviewer panel performs no corpus work on page load or
  tab selection. Its explicit button dynamically imports the corpus, freshly
  builds/replays it, then retains only the compact six-track/ten-case owner,
  feature, and outcome projection. It labels nine accepted baselines and one
  honest ambiguity abstention as neither proof authority nor agent/model
  performance.
- The capability record advances from v14 to v15 with four benchmark profiles
  and five explicit repository commands. Package documentation presents the
  same evidence and authority boundary.
- Historical 12B1/12B2 proposal tests now validate their immutable approved
  predecessor identities rather than incorrectly demanding that the later
  implementation tree still have no public surface. The proposal/review
  modules remain absent from every runtime owner.

Key implementation SHA-256 values are:

```text
lf_proof_agent_benchmark_cli.ts
  227a8d782d04ff2ea73b8e77be5ddf8dd7172f3433933578bfa651480fa781c1
package_benchmark.ts
  8fb8315d308ceb1e4855661d845f80cbf44c365a613b6674d89f935d87ff4a32
v3_2_proof_agent_benchmark_cli_tests.ts
  e1482d021be04d2be55083cf1ab890a47f9833d33a8a18ebfad3d02450d76ba0
v3_2_proof_agent_browser_integration_tests.ts
  0025f0043fd86d6b11e55c0c544b083014b171ef2480ceb3609057e7ea4496e1
emdash-template/src/App.tsx
  4684c3a298f296640ffe20fef9dfbebde27a8e1dce74871e639f10cd91281f1e
packages/emdash/package.json
  71bd329083cc66eb5157eacdc95eb254d2c4b472d6002ae1d2ff81e7aaed21d2
```

The normal Vite 5.4.19 build transforms 179 modules. The complete initial
static JavaScript closure is 441,288 raw / 119,383 gzip bytes. Vite shares
already-loaded Core with the benchmark, so the complete incremental dynamic
closure is measured after subtracting the initial closure while still walking
every static dependency: 447,783 raw / 115,747 gzip bytes. Both are below the
reviewed 465,000/130,000 and 650,000/175,000 caps. The corpus revision is
absent from the initial closure and present in the incremental lazy closure.

Proportional validation:

```text
stateless adapter and real repository dispatch
  passed: 8/8 tests, 1 suite

browser source/isolation plus built transitive-closure budgets
  passed: 26/26 tests, 2 suites

capability/command regression
  passed: 15/15 tests, 3 suites

historical 12B1/12B2 proposal and review integrity
  passed: 30/30 tests, 4 suites

release preflight policy
  passed: 3/3 tests

./scripts/pnpmw run workspace:check
  passed

./scripts/pnpmw exec tsc --noEmit --pretty false
  passed

focused ESLint over every changed root TypeScript owner/test
  passed with zero errors

direct emdash-template TypeScript check and Vite build
  passed: 179 transformed modules

EMDASH_VERIFY_PROOF_AGENT_BROWSER_BUILD=1 focused browser gate
  passed: exact initial and incremental lazy raw/gzip closures

./scripts/pnpmw run package:check
  passed: packed ESM, CommonJS, strict NodeNext, existing-entry browser,
  benchmark browser, and separate root-only browser consumers

Playwright built-page smoke
  passed: panel is inert before its explicit action; click-to-load renders
  6 tracks, 10 cases, 9 accepted baselines, and 1 abstention

git diff --check and unchanged 12A/12B1/existing-entry source audit
  passed
```

The earlier prescribed browser wrapper failure remains an environmental
non-pass; direct checked-in fixture binaries supply the successful typecheck
and Vite evidence. Root `check:ts`, root-test, `check:all`, Lambdapi/kernel,
book/print, sibling, registry, release, deployment, provider/model, and hosted
checks did not run. The user's repeated direct standing waiver applies to the
long TypeScript/repository aggregates, and the unchanged mathematical owners
make Lambdapi irrelevant to this surface-only row. These omissions are not
passes.

The next action is only a non-authorizing 12B3 package-version/release and
fresh CloserFans consumer audit after the exact 12B2 checkpoint is pinned. No
version change, package publication, GitHub release, push/merge/tag,
CloserFans/Arrowgram edit, model run, or hosted effect is authorized by this
record.

## `AGENT-EVAL-12B3` Read-Only Audit And Frozen Release/Host Contract

Date: 2026-08-11

State: non-authorizing proposal. This audit changes only the two living plans.
Its exact proposal checkpoint must be pinned by an immediate ledger-only
follow-up and then approved by a separate immutable review before any package,
workflow, Git-ref, registry, GitHub Release, Pages, or CloserFans mutation.

### Fresh Release And Host Evidence

The audit re-read every Emdash worktree, branch/index/worktree state, exact
ancestry, current release owners, public registry identity, previous hosted
run, and the current CloserFans SOP/template owners:

- every Emdash worktree is clean. The proof-assistant branch is at ledger
  checkpoint `151c518`, descends from exact 12B2 semantic checkpoint
  `93c9804`, and descends from public `main` `e35d5ae` by 134 commits with no
  commits on the other side;
- remote `main` is exact `e35d5ae`. Annotated `emdash-v0.2.0` peels to exact
  package checkpoint `ab513f7`; public npm `latest` is `0.2.0` and the only
  public versions are `0.1.0` and `0.2.0`;
- the public `0.2.0` manifest has only `.`, `./authoring`, `./workspace`, and
  `./package.json`. Exact `0.3.0` returns `E404`, so the completed
  `./benchmark` entry is not yet installable from the registry;
- `package_core.ts`, `package_authoring.ts`, and `package_workspace.ts` are
  byte-identical to `ab513f7`, with SHA-256 values
  `34e42cbb1fe6f3bf210e785bafda63b9ce9208da5dd4457e8aafd6fb6f7398a8`,
  `b4324e7ae3ad9d8db2ec737c050e1444565b265b099832ac2fe39f5f701fe9b4`,
  and `2d00f937d2484e7fc6c9d749faed53be7141556c9cf64e61b8f619d723daa33e`.
  `package_benchmark.ts` is the sole new entry owner. This is an additive
  pre-1.0 public feature, so the selected version is `0.3.0`, not a patch or
  breaking-major release;
- the token-free two-job OIDC workflow already published exact `0.2.0` in
  successful run `31414385484`. Its build and publish jobs verified the tag,
  ancestry, package, tarball handoff, and provenance. No workflow secret or
  npm token is required. The owner's separately retained bypass-2FA token
  policy remains allowed but is not the selected publication mechanism;
- the prior run log reproduces two maintenance findings rather than hiding
  them: old upload/download artifact actions were forced from Node 20 to Node
  24, and checkout cleanup traversed tracked gitlink
  `.hott-book-review-20260720` without a `.gitmodules` URL and reported Git
  exit 128 after every owning step had succeeded;
- official action releases now identify checkout `v7.0.1` at
  `3d3c42e5aac5ba805825da76410c181273ba90b1`, upload-artifact `v7.0.1` at
  `043fb46d1a93c77aae656e7c1c64a875d1fc6a0a`, download-artifact `v8.0.1` at
  `3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c`, and setup-node `v7.0.0` at the
  already pinned `820762786026740c76f36085b0efc47a31fe5020`;
- current CloserFans local `master` is exact `5c0d0c1`, has no configured Git
  remote, and retains only the unrelated untracked
  `reports/GENERAL_REPOSITORY_QUALITY_REVIEW_PLAN_2026-08-09.md`. That report
  remains uninspected by this work and must stay untracked and untouched;
- CloserFans already auto-discovers workspace templates, installs exact
  template dependencies with ordinary npm, and runs the default controller on
  Node 20. Existing `emdash_ts` remains the exact `0.1.0` complete/open proof
  starter, while `emdash_goal_graph` remains the exact `0.2.0` derived
  read-only visualization. Neither should be silently repurposed; and
- one explicit current-host measurement of the repository benchmark catalog
  completed in 3.67 seconds with maximum RSS 561,820 KiB and emitted a
  1,172-byte compact ten-case/six-track summary. This is capacity evidence for
  an explicit command, not a latency or memory service-level claim.

The audit therefore accepts one exact release followed by one new additive
ordinary-Node workspace. It rejects a package bin, embedded provider, hidden
proof server, new controller image/pool, GetPaidX API/MCP extension,
repurposing either existing Emdash template, and any Arrowgram edit.

### Frozen `0.3.0` Release Contract

The release candidate may change only the package version and its exact
version assertions, the existing token-free workflow/action pins, and living
release records. It must not change the already-qualified benchmark/evaluator
semantics or any existing package-entry source.

1. Change `packages/emdash/package.json` from `0.2.0` to exact `0.3.0` and
   update only the matching active assertions in `scripts/check-workspace.mjs`,
   `packages/emdash/scripts/release-preflight-tests.mjs`, and
   `packages/emdash/scripts/verify-packed-install.mjs`. Historical `0.1.0` and
   `0.2.0` evidence remains historical.
2. Preserve the exact five-key export order `.`, `./authoring`,
   `./workspace`, `./benchmark`, `./package.json`; no `bin`, install hook,
   runtime dependency, peer dependency, optional dependency, or package
   script may appear.
3. Keep the two-job release-only OIDC design. Update only immutable action
   pins to checkout `3d3c42e5aac5ba805825da76410c181273ba90b1`,
   upload-artifact `043fb46d1a93c77aae656e7c1c64a875d1fc6a0a`, and
   download-artifact `3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c`; retain setup-node
   `820762786026740c76f36085b0efc47a31fe5020`. Set checkout
   `persist-credentials: false`: this public read-only release needs no
   persisted GitHub token and therefore avoids leaving cleanup dependent on
   the unrelated malformed historical gitlink. Do not add a secret or
   `NODE_AUTH_TOKEN`.
4. Qualify one exact local `hotdocx-emdash-0.3.0.tgz` through workspace,
   typecheck, focused release-policy lint/tests, build, preflight, packed
   ESM/CommonJS/strict-NodeNext/browser consumers, exact inventory, and
   digest/entry/size recording. Recheck that the three predecessor entry
   sources remain byte-identical. Do not rerun `check:ts`, root-test,
   `check:all`, Lambdapi, book, or print merely for reassurance.
5. Only after a clean candidate checkpoint and exact staged/ancestry review,
   non-force-push the goal branch, fast-forward the dedicated local `main`
   worktree, and non-force-push `main`. Because the accumulated branch changes
   touch `emdash-template/**` and `src/v3_2/**`, the existing Pages workflow
   will run; its exact head, build, deployment, and public benchmark panel are
   part of this release gate rather than an incidental unverified effect.
6. Create annotated tag `emdash-v0.3.0` only on the exact candidate already in
   public `main`, push that new tag once, and publish one non-draft,
   non-prerelease GitHub Release titled `@hotdocx/emdash 0.3.0`. The frozen
   release body is:

   ```text
   Publish the isolated browser-safe proof-agent benchmark surface.

   - adds @hotdocx/emdash/benchmark with strict canonical case, run, and
     report interchange;
   - provides a fixed six-track, ten-case corpus with nine freshly accepted
     owner baselines and one honest ambiguity abstention;
   - retains the existing Core, authoring, and workspace entries and the
     package's no-bin, no-install-hook, and no-runtime-dependency policy; and
   - invokes no provider, model, network, filesystem adapter, or proof server.

   Reference attempts are reproducible baselines, not proof authority,
   committed source, model-performance measurements, or a leaderboard.
   ```

7. Require exactly one release-triggered npm workflow for that tag. Verify
   both jobs, environment approval, exact uploaded artifact/head/digest, OIDC
   publication, npm identity/dist-tag/integrity, attestations and SLSA subject,
   byte identity among local/GitHub/registry tarballs, exact fresh-installed
   exports, and successful installed consumers. Never locally publish with the
   ignored token merely to bypass a failed OIDC boundary.
8. If integration, Pages, build, approval, publication, or verification fails,
   retain the exact evidence and correct forward. Do not move/reuse a tag,
   republish an immutable version, force-push, rewrite history, or delete the
   release branch/worktree. If npm publication has completed, `0.3.0` is
   immutable even if a later host step fails.

### Frozen Additive CloserFans Workspace Contract

Only after public `@hotdocx/emdash@0.3.0` and its exact installed benchmark
entry are verified may CloserFans change. Re-read its status immediately
before editing. If tracked `master` no longer equals exact `5c0d0c1`, stop and
revise this baseline rather than absorbing concurrent work. Otherwise create
branch `goal/emdash-proof-benchmark-v1` from `5c0d0c1`, preserving the
unrelated untracked report.

Create one new workspace-project template at `templates/emdash_benchmark/`
with manifest ID `emdash_benchmark` and exact public
`@hotdocx/emdash@0.3.0`. It stays on the default Node controller and owns only:

- `benchmark-run.emdash.ts`, the compact source of authority for a complete
  ten-case run. Its initial deterministic policy explicitly abstains on every
  case. An AI agent edits ordinary TypeScript decisions, retrieved premises,
  reported usage, and proof-plan patches; no serialized artifact or mutable
  server cursor is authoritative;
- `scripts/emdash-benchmark.mts`, a stateless adapter with `catalog`, `case`,
  `run`, `evaluate`, `evaluate-file`, `reference`, and `verify` commands.
  Every command freshly reconstructs the fixed package corpus. `run` emits the
  canonical current source run; `evaluate` freshly scores it;
  `evaluate-file` reads exactly one explicit canonical run path, strictly
  parses it, and freshly scores it; `reference` presents the package-owned
  nine/one baseline. It never scans directories, writes files, invokes a
  provider/model, accesses a network, retains session state, or pretends to
  enforce provider-reported resource limits;
- exact package/TypeScript configuration, source-ownership README,
  `.gitignore`, and a lightweight static preview which explains the
  source/edit/evaluate workflow without loading or evaluating the corpus; and
- no lockfile, tracked generated run/report, dependency cache, or build output.
  Community run retention and provider execution remain 12B4 decisions.

The repository-owned focused verifier belongs at
`scripts/verify-emdash-benchmark-template-runtime.ts`, with one root script
`templates:verify:emdash-benchmark`. It must copy the template to a disposable
directory, install only from the public registry, assert exact `0.3.0`,
typecheck, exercise all commands, prove the initial ten abstentions and the
separate nine/one reference baseline, round-trip canonical run/report bytes,
reject stale/tampered or unknown-case artifacts, confirm expected exit codes,
probe the inert preview, and verify the manifest selects no special pool.
`npm run templates:validate`, targeted lint, and root typecheck are the nearest
host gates. Full Jest/Playwright/build, controller/Docker/Azure, database,
MCP/API, Arrowgram, and repository-wide checks remain omitted unless a focused
failure proves one is necessary.

The bounded CloserFans checkpoint may include only the new template/verifier,
one root script registration, and concise README/AGENTS/current-runtime
documentation. If the candidate is clean and green and local `master` remains
its exact ancestor, fast-forward local `master` only. CloserFans has no remote,
so no sibling push or deployment is possible or claimed. The existing
`emdash_ts` and `emdash_goal_graph` versions and behaviors remain unchanged.

### Review And Success Boundary

Separate immutable review must confirm all of the following before
implementation authority exists:

1. exact 12B2 checkpoint `93c9804` and ledger `151c518` remain ancestors;
2. `0.3.0` is additive and the three existing package entry owners are
   byte-identical to `ab513f7`;
3. release action upgrades and `persist-credentials: false` reduce workflow
   authority without changing exact artifact handoff or OIDC publication;
4. Pages deployment is explicit, head-pinned, and verified;
5. the new template imports public registry bytes only and starts from honest
   all-abstention rather than disguising owner baselines as agent results;
6. provider invocation, model credentials, resource enforcement, run
   retention, and measured performance remain in 12B4;
7. no Emdash semantics, Core/checker/rule, package bin/dependency, CloserFans
   API/MCP/controller, Arrowgram, Lambdapi, mathematical, book, or print owner
   changes; and
8. exact-diff, ancestry, no-secret, clean-worktree, focused validation, and
   rollback evidence are synchronized before each checkpoint or external
   mutation.

This audit itself requires only exact source/status/external-identity review,
Markdown heading/link hygiene, and `git diff --check`. It runs no TypeScript,
package, browser, kernel, book, sibling, or aggregate behavior check because
it changes no behavior. The omitted checks are not passes.

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
5. treat 12B1 as complete at exact checkpoint `d0d3764`;
6. treat exact 12B2 proposal/review/implementation checkpoints
   `ba49705`/`8c9652a`/`93c9804` as complete; advance only to a separately
   frozen 12B3 audit; and
7. synchronize both plans and exact evidence before every rollback-safe
   commit.
