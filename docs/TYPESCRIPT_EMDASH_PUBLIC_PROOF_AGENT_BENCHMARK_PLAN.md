# TypeScript/Emdash Public Proof-Agent Benchmark Plan

Status: living plan; `AGENT-EVAL-12B0` through `AGENT-EVAL-12B3` complete.
Corpus/interchange checkpoint `d0d3764`, public runner/package checkpoint
`93c9804`, immutable package source `995e497`, permanent release hardening
`3af518d`, and locally integrated CloserFans host `cbf2356` satisfy the
separately reviewed contracts and proportional gates recorded below. Exact
public `@hotdocx/emdash@0.3.0`, Pages, Release, provenance, installed
consumers, release-only OIDC workflow, and the all-abstention source workspace
are verified. The `AGENT-EVAL-12B4` read-only audit, first policy proposal,
and immutable implementation review are frozen below. The approved mock-only
Stage A runner is now implemented on an isolated CloserFans branch at
checkpoints `1d77473` and `8e270a7`, with final tree `9fc93af`; its focused
containment, replay, public-package, CLI, template, and hygiene gates are
green. No provider/model execution or real retained run occurred. The next
preflight review accepted the mock boundary but correctly denied a real call
because no authenticated one-shot driver exists. The corrective driver
proposal below is now separately reviewed for code and fake/no-model tests
only; it is not implemented. Provider execution, measurement, and graduation
remain gated.

Date: 2026-08-11

Branch: `goal/typescript-emdash-proof-assistant-v1`

Worktree: `/home/user1/emdash1-classes-v1`

Governing plan:
[`TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md`](./TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md).

Original exact predecessors:

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

The first three slices are now complete. The third published exact `0.3.0`,
restored a permanent release-only workflow, and locally integrated one
source-first CloserFans workspace; it still invoked no provider/model and made
no PathOut task conversion. The subsequent 12B4 provider/execution/retention/
reporting audit, proposal, first review, mock-only implementation, and
fail-closed second preflight, and corrective-driver review are now frozen
below. The next bounded action is only the approved local code plus fake/no-
model test implementation—not a real-agent run or performance claim.

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
| `AGENT-EVAL-12B3` | complete at Emdash hardening `3af518d` and CloserFans host `cbf2356` | Exact `0.3.0`, Pages run `31509112917`, protected OIDC recovery run `31510726533`, byte/provenance/installed-consumer verification, permanent trigger removal, and the focused-green ten-abstention source workspace are complete. Two safe pre-package failures and the reviewed one-time dispatch remain durable evidence. |
| `AGENT-EVAL-12B4` | Stage A terminal without a benchmark result; R11 correction focused-green at CloserFans `8a5c2f9`, with R12 parse-probe repair proposed | Supported `--disable view_image` replaces the stale strict key and focused typecheck/synthetic/mock gates pass. The old `exec --help` check did not load config; R12 proposes validating the full vector to an exact no-prompt boundary. Live probing and new-coordinate authority stay separate. |

The separately reviewed `AGENT-EVAL-12B1` implementation is complete. The
separately approved `AGENT-EVAL-12B2` implementation is also complete and its
exact semantic checkpoint is `93c9804`. Separately reviewed 12B3 is complete
through exact public and local-host checkpoints recorded above. No provider,
model, retained-run, or measured-graduation effect follows from these
completions.

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

State: non-authorizing proposal frozen at exact checkpoint `bb16e47`. This
audit changes only the two living plans. It must be approved by a separate
immutable review before any package, workflow, Git-ref, registry, GitHub
Release, Pages, or CloserFans mutation.

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

## `AGENT-EVAL-12B3` Immutable Contract Review

Date: 2026-08-11

State: approved at exact review checkpoint `0027c66` under the user's
delegated unattended authority, with later human supersession. This review
approves only exact proposal checkpoint `bb16e47`.

Immutable proposal evidence:

- dedicated proposal-plan SHA-256:
  `4dba6dd000d72982b797d3a594db65957990341b3bed866adf632735ff863dcc`;
- governing proposal-plan SHA-256:
  `0d8a90f3e2678d47fc8794169a92565b0ad02b3a5f648cafd8b438070790879d`;
- exact semantic predecessor: `93c9804`;
- exact completed-ledger predecessor: `151c518`; and
- proposal checkpoint: `bb16e47`.

The review independently accepts the contract for ten reasons:

1. **Dependency closure.** Both required predecessors are ancestors of the
   proposal. Public `0.2.0` is still latest, exact `0.3.0` is absent, and the
   benchmark entry has already passed its own 12B2 package/browser consumers.
2. **Semver and compatibility.** A new isolated subpath is a bounded additive
   pre-1.0 feature. The exact three predecessor entry sources match
   `ab513f7`; the review forbids using versioning as cover for an unreviewed
   source or export change.
3. **Least-authority workflow maintenance.** The three replacement action
   commits are official immutable release-tag targets, setup-node is already
   current, and `persist-credentials: false` removes unnecessary credential
   persistence. Build remains unprivileged; only the publish job retains
   `id-token: write`; no token or secret enters the workflow.
4. **Exact artifact handoff.** The tag/version/repository preflight, one packed
   tarball, SHA-256 output, named artifact, publish-time digest comparison,
   no-republish guard, OIDC provenance, and post-registry byte comparison
   preserve the successful `0.2.0` model. A release failure is corrected
   forward and never by moving a tag or republishing a version.
5. **Explicit deployment consequence.** Main integration necessarily triggers
   Pages because already-qualified benchmark browser paths changed. Requiring
   the exact main head, successful workflow/deployment, and live panel smoke
   prevents release integration from smuggling an unverified hosted effect.
6. **Host isolation.** A new `emdash_benchmark` workspace is more honest than
   changing the `0.1.0` proof starter or `0.2.0` goal-view artifact. It uses
   the existing default Node controller and auto-discovery path, so no pool,
   image, database, API, MCP, permission, or Arrowgram contract is needed.
7. **Source-first AI operation.** The direct TypeScript run source is compact,
   diffable, and starts with ten explicit abstentions. It binds attempts to
   fresh exact cases and lets an AI edit ordinary patch data without treating
   a generated JSON artifact, terminal cursor, or server session as source
   authority. Stable provider/revision/seed metadata must be explicit;
   reported usage remains optional and unverified.
8. **Fresh evaluation and negatives.** Both source and explicit-file paths
   reconstruct the public corpus and use the package's strict canonical parser
   plus unchanged fresh evaluator. Stale/tampered/unknown-case inputs fail;
   reference nine/one results remain visibly separate from the all-abstention
   starter and from later model measurements.
9. **Proportional validation.** Version/workflow edits require exact package,
   release, packed-consumer, no-secret, and external artifact gates. The later
   host edit requires registry install, focused command/negative/preview
   checks, template validation, root typecheck, and targeted lint. Long
   TypeScript/root/Lambdapi/book/sibling aggregates add no direct coverage and
   remain omitted unless a focused failure makes one progress-blocking.
10. **Rollback-safe sequencing.** Package qualification and checkpoint precede
    branch/main pushes; public main precedes tag/Release; verified npm bytes
    precede the sibling branch; and the clean CloserFans candidate precedes
    local `master --ff-only`. Every stage rechecks ancestry and dirty state and
    preserves unrelated work.

Implementation authority is therefore exact and staged:

1. Emdash may change only the four active `0.2.0` version assertions to
   `0.3.0`, the three immutable action pins, checkout credential persistence,
   the tests which own those exact policies, and the two living plans.
2. After local proportional qualification and a clean checkpoint, the goal
   may non-force-push its branch, fast-forward and non-force-push public
   `main`, verify the resulting Pages deployment, create/push the one annotated
   `emdash-v0.3.0` tag, publish the frozen GitHub Release, approve only its
   exact `npm-release` deployment, and verify the immutable OIDC package.
3. Only after that package is public and verified may CloserFans branch from
   exact clean `5c0d0c1`, add the frozen template/verifier/script/docs slice,
   checkpoint it, and fast-forward local `master` if ancestry remains exact.

The review does not authorize any semantic source, Core/checker/rule, package
entry/dependency/bin/hook, provider/model, performance claim, run-retention
policy, CloserFans API/MCP/controller, Arrowgram, Lambdapi, mathematics,
book/print, force-push, history rewrite, tag movement, branch/worktree cleanup,
or sibling deployment. Real-agent operation and community result policy remain
exclusively `AGENT-EVAL-12B4`.

Review validation is deliberately plan-only: exact proposal blob hashes,
predecessor ancestry, unchanged public-entry hashes, current clean state,
exact diff review, conflict-marker scan, and `git diff --check`. No behavior or
aggregate gate ran, and none is claimed.

## `AGENT-EVAL-12B3` Stage A Local Candidate Qualification Record

Date: 2026-08-11

State: local release candidate complete and proportionally qualified at exact
checkpoint `995e497`. No remote, registry, Release, tag, Pages, or sibling
mutation has occurred.

The implementation follows the reviewed contract exactly:

- `packages/emdash/package.json` is exact `0.3.0` with the same five ordered
  export keys, files, engine, repository, provenance, and no-bin/no-script/no-
  dependency surface;
- only the matching active version assertions changed in
  `scripts/check-workspace.mjs`, release preflight tests, and the packed-
  install verifier. Historical package evidence remains `0.1.0`/`0.2.0`;
- checkout is pinned to official `v7.0.1`
  `3d3c42e5aac5ba805825da76410c181273ba90b1` with
  `persist-credentials: false`; upload-artifact is official `v7.0.1`
  `043fb46d1a93c77aae656e7c1c64a875d1fc6a0a`; download-artifact is official
  `v8.0.1` `3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c`; setup-node retains official
  `v7.0.0` `820762786026740c76f36085b0efc47a31fe5020`;
- build remains unprivileged, only publish has `id-token: write`, and workflow
  scanning finds no secret reference, npm token, or local ignored credential;
  and
- `package_core.ts`, `package_authoring.ts`, and `package_workspace.ts` retain
  their exact `ab513f7` SHA-256 values. No semantic/public-entry owner changed.

Changing the workspace package version caused the first pnpm-wrapped
workspace and release-policy invocations to stop before their scripts with
`ERR_PNPM_VERIFY_DEPS_BEFORE_RUN`. One frozen-lockfile install refreshed only
the ignored per-worktree link metadata; pnpm reported the lockfile current and
changed no package or tracked lock. Both blocked gates then passed. They are
not misreported as initial test passes.

Exact proportional evidence:

```text
./scripts/pnpmw install --frozen-lockfile
  passed; pnpm@11.16.0; lockfile current; no dependency change

./scripts/pnpmw run workspace:check
  passed; exact four-workspace contract; Node 24.11.1

./scripts/pnpmw run package:release:check
  passed: 3/3 exact identity, manifest negatives, token-free workflow policy

./node_modules/.bin/tsc --noEmit --pretty false
  passed

focused ESLint over release-preflight-tests.mjs,
verify-packed-install.mjs, and check-workspace.mjs
  passed with no diagnostics

./scripts/pnpmw run package:build
  passed: ESM, CommonJS, declarations, and source maps

node packages/emdash/scripts/release-preflight.mjs \
  --tag emdash-v0.3.0 --repository hotdocx/emdash
  passed with exact version/tag/repository/artifact/tarball/provenance record

node packages/emdash/scripts/verify-packed-install.mjs \
  --tarball /tmp/.../hotdocx-emdash-0.3.0.tgz
  passed: exact inventory plus installed ESM, CommonJS, strict NodeNext,
  benchmark browser, existing-entry browser, and root-only browser consumers

git diff --check, no-secret scan, and unchanged-entry hash audit
  passed
```

The exact local candidate tarball has 162 entries and 2,778,964 bytes. Its
SHA-256 is
`49c4f2ca7a12f1bc0f7721044015c1df3bee17e849bc593b99a9161206178541`.
A second independent pack from unchanged source produced the identical digest
and `cmp` passed. This proves local deterministic repacking; hosted and
registry identity remain future evidence.

`actionlint` is unavailable on this host, so it is not claimed. The exact
workflow policy test and later GitHub execution own that boundary. Root
`check:ts`, root-test, `check:all`, Lambdapi/kernel, book/print, Pages,
registry, GitHub Release, environment approval, CloserFans, Arrowgram,
provider/model, and hosted-agent checks did not run. The user's standing
anti-aggregate direction applies, and the omissions are not passes.

The next admissible sequence is exact staged review and candidate checkpoint,
then clean ancestry/remote/registry re-audit before the reviewed non-force
branch/main push, Pages verification, annotated tag, frozen Release, and OIDC
publication. The CloserFans stage remains forbidden until public registry
bytes are independently verified.

## `AGENT-EVAL-12B3-R1` Checkout Failure And Forward-Recovery Proposal

Date: 2026-08-11

State: non-authorizing proposal. The failed hosted run and still-absent npm
version make a bounded workflow correction necessary, but this section must
be checkpointed and independently reviewed before workflow, `main`, Release,
environment, or registry state changes again.

The reviewed integration sequence completed safely through its Pages gate:

- remote goal branch `goal/typescript-emdash-proof-assistant-v1` is exact
  ledger checkpoint `bc80632`;
- local and remote `main` are the exact qualified package candidate
  `995e497`, reached by fast-forward;
- Pages run `31509112917` has exact head `995e497`; both build and deployment
  passed, and the live browser panel showed six tracks, ten cases, nine
  accepted references, and one abstention with no console error or warning;
- annotated tag `emdash-v0.3.0` peels to exact `995e497`;
- GitHub Release database ID `368683536` is the one public, non-draft,
  non-prerelease Release titled `@hotdocx/emdash 0.3.0` with the exact frozen
  body; and
- release-triggered workflow run `31509330799` is the only `0.3.0` npm run.
  Its build failed in `Checkout exact release tag`; publish was skipped, and
  npm still returns `E404` for exact `0.3.0` with `latest` remaining `0.2.0`.

The run log establishes the root cause rather than an application or package
failure. Official checkout v7 fetched and checked out exact tag `emdash-v0.3.0`
at `995e497`. Although `persist-credentials: false` was set, checkout first
installed a temporary include-file credential and then removed it before
returning. That removal executed `git submodule foreach --recursive` against
the tracked historical gitlink `.hott-book-review-20260720`. Because that
gitlink intentionally has no `.gitmodules` URL, Git exited 128 and the action
failed before Node setup, preflight, build, pack, upload, environment approval,
OIDC, or npm mutation. The prior assumption that non-persistence would avoid
the malformed-gitlink cleanup path is therefore falsified. Retrying the same
run cannot correct it.

The smallest forward correction is release-workflow-only:

1. Remove `actions/checkout` from `.github/workflows/npm-publish.yml`. Replace
   it with one unprivileged shell step which initializes the empty runner
   workspace, adds the public HTTPS repository URL without a token, fetches
   only exact `refs/tags/$RELEASE_TAG` and `refs/heads/main`, and checks out the
   tag detached. It must not initialize, update, inspect, or recurse through
   submodules and must not read or persist `GITHUB_TOKEN`.
2. Keep the release-only `types: [published]` trigger, two-job artifact
   handoff, unprivileged build, exact ancestry/package checks, immutable
   setup/upload/download action pins, protected `npm-release` environment,
   sole publish-job `id-token: write`, no-republish guard, and OIDC provenance
   publication unchanged. Do not add `workflow_dispatch`, another workflow,
   a secret, `NODE_AUTH_TOKEN`, or an npm token.
3. Update the focused release-policy test to require the direct exact-ref
   fetch, detached checkout, and absence of `actions/checkout`, credentials,
   submodule operations, and broader push/pull-request/manual triggers.
4. Reproduce the direct checkout in a fresh disposable directory against the
   public repository, proving exact tag peel, exact remote-main ancestry, and
   clean package source without fetching a sibling branch or submodule.
   Run the three focused release-policy tests, workspace contract, root
   typecheck, focused lint, package preflight/build, and diff/no-secret gates.
   Package semantics and the already qualified tarball are unchanged, so no
   long aggregate, kernel, book, print, browser, or packed-consumer rerun is
   required merely for this workflow correction.
5. After a separate immutable review and clean correction checkpoint,
   non-force-push the goal branch and fast-forward/push `main`. Confirm the
   public workflow bytes and that tag `emdash-v0.3.0`, Release ID `368683536`,
   and npm absence remain exact.
6. Change that same Release object to draft and immediately publish the same
   object again with its exact tag, title, body, and non-prerelease state. This
   is a one-time event recovery, not a second Release or a moved/reused tag.
   It must produce exactly one new `release: published` workflow run at exact
   package head `995e497`; the first failed run remains durable evidence.
7. Approve only the corrected run's exact pending `npm-release` deployment,
   then apply every original artifact, OIDC, registry, provenance, byte-
   identity, installed-export, and consumer verification gate. The CloserFans
   stage remains forbidden until these public bytes pass.

If the direct checkout, Release-object transition, corrected workflow, OIDC,
or registry verification fails, stop again and correct forward. Never move or
delete the tag, delete/recreate the Release, locally publish, republish an npm
version, force-push, rewrite history, or conceal the failed run. This recovery
adds no semantic, package-entry, dependency, bin, hook, provider/model,
CloserFans, API/MCP/controller, Arrowgram, Lambdapi, mathematics, book, print,
or 12B4 authority.

## `AGENT-EVAL-12B3-R1` Immutable Recovery Review

Date: 2026-08-11

State: approved under the user's delegated unattended authority, with later
human supersession. This review authorizes only exact proposal checkpoint
`de26b61` and must itself be checkpointed before implementation.

Immutable proposal evidence:

- dedicated proposal-plan SHA-256:
  `0414852f2c39e3464fe664e5a6ccb49edfb5ee60320e8fc09d032a6a3a275b85`;
- governing proposal-plan SHA-256:
  `17b8e9febc7038c76b04c006801135d6ebf78436190b12fe071d42c0edad1ad1`;
- last qualified package checkpoint and immutable tag peel: `995e497`;
- pre-failure ledger checkpoint: `bc80632`;
- exact Pages run: `31509112917`;
- exact failed npm workflow run/job: `31509330799` / `93838861316`; and
- exact retained GitHub Release database ID: `368683536`.

The review accepts the correction for eight independent reasons:

1. **Failure isolation.** The job log proves that checkout fetched and checked
   out exact `995e497`, then failed inside checkout's credential-removal path.
   Every package-owned and publish-owned step was skipped; npm independently
   reports `0.3.0` absent. No ambiguous partial publication must be repaired.
2. **Root-cause fit.** The failure is specifically the action's unconditional
   recursive submodule-config cleanup against a tracked gitlink without a
   `.gitmodules` URL. A direct Git fetch never invokes that path. Retrying,
   adding a token, changing package bytes, or changing the historical book
   gitlink would not be a proportional correction.
3. **Lower authority.** The replacement uses the public HTTPS repository with
   `GIT_TERMINAL_PROMPT=0` and an empty credential helper, fetches only the
   exact release tag and `main`, and checks out detached. It neither receives
   `GITHUB_TOKEN` nor persists an authorization header. Setup, artifact, and
   OIDC actions retain their reviewed immutable pins.
4. **Independent reproduction.** A fresh disposable repository fetched only
   public `main` and `emdash-v0.3.0`, checked out exact `995e497`, proved it an
   ancestor of exact remote `main`, remained clean, and contained no local
   credential, extra-header, or submodule configuration. The probe performed
   no submodule operation.
5. **Release-event integrity.** Keeping only `release: published` avoids a
   permanent manual publication surface. Re-drafting and publishing the same
   database object preserves one tag, one Release identity, exact title/body,
   and the event's package head. The first failed run remains visible; the
   second run is explicitly a recovery, not falsely described as the sole
   attempt.
6. **Immutable package discipline.** The annotated tag never moves, package
   source stays at the already qualified candidate, the no-republish guard
   remains, and npm is still empty for the version. If the second run reaches
   npm, `0.3.0` becomes immutable and all original byte/provenance checks are
   mandatory before the sibling stage.
7. **Proportional gates.** Workflow policy tests must now reject checkout,
   credentials, submodule recursion, and added broad triggers while requiring
   exact refspecs and detached checkout. A fresh public-fetch probe, focused
   release tests, workspace, typecheck, focused lint, preflight/build,
   no-secret scan, and diff hygiene directly cover the change. Long/kernel/
   book/browser/packed reruns would not exercise the corrected boundary.
8. **Rollback-safe sequencing.** Correction and plan evidence are checkpointed
   before goal/main pushes; public workflow bytes are verified before the
   Release transition; only the resulting exact environment deployment may be
   approved. Any further failure stops without tag movement, Release deletion,
   local publication, force, rewrite, or CloserFans mutation.

Implementation authority is limited to the release workflow, its focused
policy test, and the two living plans. It authorizes the exact non-force
branch/main integration and same-Release event recovery only after the local
correction is green. It does not authorize semantic or package-entry changes,
workflow dispatch, another workflow or Release, credentials, tokens, provider
or model execution, CloserFans before registry verification, Arrowgram,
Lambdapi, mathematics, book/print, 12B4, history rewriting, or cleanup.

Review validation is plan-only plus the fresh public Git probe: exact proposal
blob hashes and paths, ancestry, remote/tag/Release/npm identities, failed-job
log, clean worktree, conflict-marker scan, and diff hygiene. No behavior or
aggregate check is claimed for the review document itself.

## `AGENT-EVAL-12B3-R1` Local Correction Qualification Record

Date: 2026-08-11

State: implementation complete and proportionally green at exact semantic
checkpoint `f965d03`. This immediately following plan-only ledger update pins
that immutable correction. No additional remote, Release, environment,
registry, or sibling mutation occurred during the local correction.

The implementation changes exactly two behavioral owners:

- `.github/workflows/npm-publish.yml` removes `actions/checkout` and replaces
  it with one unprivileged, credential-empty direct Git initialization/fetch/
  detached-checkout step. It fetches only public `main` and exact
  `emdash-v0.3.0`, never invokes a submodule command, and leaves every later
  build/artifact/environment/OIDC step unchanged; and
- `packages/emdash/scripts/release-preflight-tests.mjs` requires those exact
  refspecs and detached checkout while rejecting checkout-action use,
  persisted credentials, submodule operations, token/secret references, and
  push, pull-request, or manual workflow triggers.

The two plans add only failure, review, and qualification evidence. Package
version, manifest, export order, source entries, evaluator/corpus semantics,
tarball policy, setup/upload/download action pins, and Release/tag bytes are
unchanged.

Exact proportional evidence:

```text
fresh credential-empty public Git probe
  passed: fetched only main and emdash-v0.3.0; detached exact 995e497;
  remote main exact 995e497; ancestry and clean status passed; no local
  credential, extra-header, or submodule configuration

./scripts/pnpmw run workspace:check
  passed: pnpm@11.16.0; exact four-workspace contract; Node 24.11.1

./scripts/pnpmw run package:release:check
  passed: 3/3 exact release identity, manifest negatives, and corrected
  token-free workflow policy

./node_modules/.bin/tsc --noEmit --pretty false
  passed

./node_modules/.bin/eslint \
  packages/emdash/scripts/release-preflight-tests.mjs
  passed with no diagnostics

./scripts/pnpmw run package:build
  passed: ESM, CommonJS, declarations, and source maps

node packages/emdash/scripts/release-preflight.mjs \
  --tag emdash-v0.3.0 --repository hotdocx/emdash
  passed with exact 0.3.0 identity

Python safe YAML parse, no-secret/static denial scan, and git diff --check
  passed
```

`actionlint` remains unavailable and is not claimed. A Ruby YAML probe could
not run because Ruby is absent; the available Python parser passed, and the
focused policy plus forthcoming hosted run own actual GitHub execution. No
`check:ts`, root-test, `check:all`, Lambdapi/kernel, book/print, browser,
packed-consumer, CloserFans, Arrowgram, provider/model, or hosted publish gate
was rerun. Those omissions are deliberate and not passes.

The next admissible operation is a clean ancestry/external-state re-audit,
then non-force goal-branch push and `main` fast-forward to exact `f965d03`.
Only after the public workflow bytes are verified may the exact same Release
object be re-published once under the reviewed recovery sequence.

## `AGENT-EVAL-12B3-R2` Tagged-Workflow Failure And One-Time Dispatch Proposal

Date: 2026-08-11

State: non-authorizing proposal. The second failed run falsifies the proposed
Release-event recovery mechanism, not the direct-checkout correction. This
section must be checkpointed and independently reviewed before adding a
manual trigger, pushing another correction, dispatching, approving an
environment, publishing, or editing CloserFans.

Exact new evidence:

- recovery implementation `f965d03` and its direct-checkout policy are public
  on `main`; the public workflow SHA-256 is
  `97ea63caafdd4efd0d17eee9d99fded2ab0acf560257349e34469c633ccf8201`;
- Release ID `368683536` was changed to draft and published again without
  changing its tag, title, body, or non-prerelease state;
- this emitted exactly one new release run, `31510177054`, at package head
  `995e497`; and
- that run nevertheless executed the old step `Checkout exact release tag`
  from tagged commit `995e497`, failed again in checkout's recursive
  credential removal, skipped every package/publish step, and left npm exact
  `0.3.0` absent.

GitHub's documented event model explains the result: each workflow run uses
the workflow version present at the event's associated commit/ref; for a
release event, `GITHUB_SHA` is the released tag commit and `GITHUB_REF` is the
tag. A corrected default-branch workflow is necessary for future release
tags, but re-publishing an immutable old tag cannot make that tag contain the
correction. Repeating the Release transition would therefore be knowingly
ineffective and is forbidden. GitHub separately documents that a
`workflow_dispatch` run uses the workflow on the selected branch/ref. npm's
trusted-publisher documentation permits manual workflows and validates the
calling workflow filename; using the same `npm-publish.yml` and protected
environment retains the configured publisher identity.

Official design evidence:

- <https://docs.github.com/en/actions/concepts/workflows-and-actions/workflows>;
- <https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#release>;
- <https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#workflow_dispatch>; and
- <https://docs.npmjs.com/trusted-publishers/>.

The bounded forward correction is a temporary exact-version recovery path:

1. On current `main`, add `workflow_dispatch` to the existing
   `.github/workflows/npm-publish.yml` with one required choice input whose
   only option is exact `emdash-v0.3.0`. Do not add another workflow or accept
   an arbitrary version, tag, ref, SHA, package, registry, or command input.
2. Resolve `RELEASE_TAG` and the concurrency key from either the ordinary
   release tag or that exact dispatch choice. Keep the ordinary release job
   condition unchanged in meaning; admit manual execution only when
   `github.event_name == 'workflow_dispatch'` and the choice equals exact
   `emdash-v0.3.0`.
3. Retain credential-empty direct checkout, exact tag/main fetch and ancestry,
   package preflight/build/pack, artifact handoff, no-republish guard,
   protected `npm-release` environment, sole publish-job `id-token: write`,
   npm 11.19.0, and OIDC provenance. The manual run's workflow-authority SHA
   will be the selected corrected `main` commit while its package-source SHA
   remains the detached immutable tag `995e497`; record both rather than
   conflating provenance of the release machinery with package source.
4. Update the focused policy test to require the one-option recovery input,
   exact event-aware tag resolution and condition, and continued denial of
   push/pull-request triggers, secrets/tokens, checkout actions, submodule
   traversal, and arbitrary manual inputs. Run the same focused workflow,
   workspace, typecheck, lint, build/preflight, YAML, no-secret, and diff gates
   as R1. Long/kernel/book/browser/packed/sibling aggregates remain omitted.
5. After separate immutable review, green checkpoint, ledger pin, clean audit,
   and non-force goal/main integration, dispatch exactly once on exact remote
   `main` with choice `emdash-v0.3.0`. Do not modify the Release again. Verify
   the run's workflow-authority head and exact checked-out package head.
6. Approve only that run's exact pending `npm-release` deployment. Apply all
   original artifact, OIDC, registry, provenance, byte-identity, installed-
   export, and consumer gates. If publication fails before npm mutation,
   retain evidence and stop; if npm succeeds, the version is immutable.
7. After successful registry verification and before CloserFans, immediately
   remove `workflow_dispatch`, its input, temporary condition, and dual tag
   resolution from `main`. Restore the permanent release-only direct-checkout
   workflow, rerun its focused policy/YAML/diff gates, checkpoint, non-force
   integrate, and verify public workflow bytes. Future version tags will then
   contain the corrected release-only workflow; exact `0.3.0` needs no further
   trigger.

This recovery is narrower than retaining a general manual publish control and
more truthful than moving the tag. It authorizes no Release re-publication,
tag change, local/token publish, second package version, semantic/package
entry change, provider/model execution, run-retention policy, CloserFans
before verified npm bytes, API/MCP/controller, Arrowgram, Lambdapi,
mathematics, book/print, history rewrite, force, or cleanup.

## `AGENT-EVAL-12B3-R2` Immutable Dispatch Recovery Review

Date: 2026-08-11

State: approved under the user's delegated unattended authority, with later
human supersession. This review authorizes only exact proposal checkpoint
`cda361e` and must itself be checkpointed before implementation.

Immutable proposal evidence:

- dedicated proposal-plan SHA-256:
  `a69ed4403b6f88231e1e5f2ec3e1742c3dcfb7ee65576f3fa4d4f350ebbd0013`;
- governing proposal-plan SHA-256:
  `6efd912cd1c61834b5e3b031e985a02b323c70e47bc84557e48f28c538716898`;
- exact corrected workflow checkpoint and public main: `f965d03`;
- exact immutable package source/tag peel: `995e497`;
- exact first and second failed runs: `31509330799` and `31510177054`; and
- exact retained Release database ID: `368683536`.

The review accepts the one-time dispatch for nine reasons:

1. **Second-failure isolation.** Run `31510177054` visibly used the old tagged
   checkout step and failed in the same internal cleanup. All Node, package,
   artifact, environment, OIDC, and npm steps were skipped; registry `0.3.0`
   is still absent. There is no partial package to supersede.
2. **Documented event semantics.** GitHub states that each run uses the
   workflow version at its associated SHA/ref; release events use the release
   tag, while `workflow_dispatch` uses the selected branch/tag and requires
   the workflow on the default branch. This exactly explains both the failed
   replay and why corrected `main` is the necessary recovery authority.
3. **Trusted-publisher fit.** npm documents manual workflows as supported and
   warns that validation follows the calling workflow's filename. Dispatching
   the same `.github/workflows/npm-publish.yml`, with the same repository,
   `npm-release` environment, GitHub-hosted runner, and sole publish-job OIDC
   permission preserves the configured identity rather than routing around it.
4. **Finite manual authority.** The input is a required choice with exactly
   one value, `emdash-v0.3.0`; the job condition admits no other manually
   supplied tag or package. Repository write access, exact source checks, and
   the protected environment remain independent gates.
5. **Source/workflow separation.** The dispatch run's `GITHUB_SHA` records the
   corrected workflow-authority commit. The build itself fetches and checks
   out immutable package source `995e497`, proves tag peel and main ancestry,
   and packs only those bytes. Recording both SHAs is more accurate than
   pretending a workflow absent from the package tag executed there.
6. **Artifact continuity.** All package checks, deterministic pack, uploaded
   artifact, digest handoff, no-republish guard, npm version/tool pin, and
   provenance publication remain unchanged. Local candidate SHA-256
   `49c4f2ca7a12f1bc0f7721044015c1df3bee17e849bc593b99a9161206178541`
   remains the independent byte target.
7. **No Release/tag workaround.** The review forbids another draft/publish
   transition, Release deletion/recreation, tag movement, alternate version,
   and local/token publication. Both failed runs remain durable evidence.
8. **Mandatory hardening.** Registry success does not complete R2 by itself.
   The temporary dispatch input and dual event resolution must be removed,
   proportionally rechecked, checkpointed, integrated, and verified on public
   `main` before CloserFans begins. Future tags then contain the corrected
   permanent release-only workflow.
9. **Proportional validation and stop rule.** Focused policy, workspace,
   typecheck, lint, package build/preflight, YAML, no-secret, exact-diff, and
   hosted-run evidence cover this boundary. Long/kernel/book/browser/packed
   aggregates remain irrelevant. Any unexpected dispatch, build, approval,
   OIDC, registry, provenance, or byte result stops the sequence forward.

Implementation authority is limited to the temporary exact-choice dispatch,
its focused policy test, and the two living plans; then to its mandatory
post-publication removal. It authorizes one non-force integration, one exact
manual dispatch, and approval of only that run's exact environment deployment
after the build passes. It does not authorize any other manual publish,
Release/tag change, secret/token, semantic/package-entry change, provider/model
execution, CloserFans before public verification and hardening, API/MCP,
controller, Arrowgram, Lambdapi, mathematics, book/print, 12B4, force, rewrite,
or cleanup.

Review validation is plan-only: exact proposal blob hashes/paths, official
primary documentation, both job logs, remote/main/tag/Release/npm identities,
clean worktree, conflict-marker scan, ancestry, and diff hygiene. No behavior
or aggregate gate is claimed for the review document.

## `AGENT-EVAL-12B3-R2` Temporary Dispatch Qualification Record

Date: 2026-08-11

State: implementation complete and proportionally green at exact semantic
checkpoint `7e275a7`. This immediately following plan-only ledger update pins
that immutable implementation. No push, dispatch, environment approval,
registry, Release, tag, or sibling mutation occurred during local work.

The temporary implementation changes exactly two behavioral owners:

- `.github/workflows/npm-publish.yml` keeps `release: published` and adds one
  `workflow_dispatch` choice input with sole value `emdash-v0.3.0`. Its
  concurrency key, build condition, and job-level `RELEASE_TAG` distinguish
  the ordinary release event from only that exact recovery event. Direct
  credential-empty tag checkout and every package/artifact/OIDC step remain
  unchanged; and
- `packages/emdash/scripts/release-preflight-tests.mjs` requires the exact
  one-option input, dual event resolution, finite condition, direct checkout,
  and two-job OIDC policy while continuing to reject push/pull-request
  triggers, checkout actions, credentials, submodule operations, and token or
  secret references.

The plans add only failure/review/qualification evidence. There is no package
manifest, export, source, evaluator, corpus, tarball, Release, tag, environment,
or registry delta.

Exact proportional evidence:

```text
./scripts/pnpmw run workspace:check
  passed: pnpm@11.16.0; exact four-workspace contract; Node 24.11.1

./scripts/pnpmw run package:release:check
  passed: 3/3 exact release identity, manifest negatives, direct checkout,
  and finite one-option dispatch policy

./node_modules/.bin/tsc --noEmit --pretty false
  passed

./node_modules/.bin/eslint \
  packages/emdash/scripts/release-preflight-tests.mjs
  passed with no diagnostics

./scripts/pnpmw run package:build
  passed: ESM, CommonJS, declarations, and source maps

node packages/emdash/scripts/release-preflight.mjs \
  --tag emdash-v0.3.0 --repository hotdocx/emdash
  passed with exact 0.3.0 identity

Python safe YAML parse and git diff --check
  passed
```

The unchanged R1 public-fetch probe remains the direct-checkout execution
evidence. `actionlint` is unavailable and not claimed. No long TypeScript/root
aggregate, Lambdapi/kernel, book/print, browser, packed-consumer, CloserFans,
Arrowgram, provider/model, or hosted dispatch gate ran. Those omissions are
not passes.

The next admissible operation is clean re-audit, non-force goal-branch push
and `main` fast-forward to exact `7e275a7`, public workflow recognition, and
one dispatch on exact integrated `main`. The Release must not be edited again.

## `AGENT-EVAL-12B3-R2` Public Release And Permanent Hardening Record

Date: 2026-08-11

State: exact public package verified; permanent release-only workflow
hardening is complete and proportionally green at exact semantic checkpoint
`3af518d`. This immediately following plan-only ledger update pins that
immutable hardening. CloserFans remains untouched until it reaches public
`main`.

### Hosted publication evidence

The sole manual recovery run is `31510726533`, event `workflow_dispatch`,
workflow-authority branch/head `main` / exact `7e275a7`. Its build job
`93843570505` passed credential-empty checkout of exact package tag
`emdash-v0.3.0` at `995e497`, tag/main ancestry, frozen install, workspace,
typecheck, 3/3 release policy, package build, deterministic pack, installed
verification, and artifact upload. No checkout action or submodule operation
ran.

The only pending deployment was exact environment ID `19605245682`, name
`npm-release`, for that run. The reviewed owner approval created deployment
`5854097178`; publish job `93843776669` then downloaded the already qualified
artifact, retained npm 11.19.0, verified its digest, and completed OIDC
publication. Both jobs and the overall run are successful, the pending list
is empty, and the complete run log has no GitHub warning or error annotation.
Failed runs `31509330799` and `31510177054` remain visible and correctly show
publish skipped before any npm mutation.

Exact artifact and registry evidence:

- GitHub artifact ID `9108950678`, name `emdash-npm-0.3.0`, belongs to run
  `31510726533` and workflow head `7e275a7`; its ZIP-container digest is
  SHA-256 `66dbc8d8f3c8344b364ff6a7692fced43defc88a9bddf0161a5ec9caca0d2e26`;
- the independently retained local candidate, extracted GitHub artifact, and
  fresh npm-registry tarball are byte-identical: 162 entries, 2,778,964 bytes,
  SHA-256
  `49c4f2ca7a12f1bc0f7721044015c1df3bee17e849bc593b99a9161206178541`;
- npm reports exact package/version `@hotdocx/emdash@0.3.0`, `latest: 0.3.0`,
  `fileCount: 162`, unpacked size 15,997,850, SHA-1
  `78ea059643204dd830f8508d0031400923d8b4e9`, and SHA-512 hex
  `7b002169bfad2cc634419ace5cb312a47d7d55890fef7891da26316118ab7982bedb54033a2f42a7f4eae2cbbe408f9bfcd9989d4a19cc6a04110a411890b1c6`;
- the registry exposes an npm publish attestation and SLSA provenance v1,
  plus an npm signature. Both attestation subjects have the exact package
  SHA-512. Provenance records GitHub-hosted builder, workflow path
  `.github/workflows/npm-publish.yml`, workflow ref `refs/heads/main`, event
  `workflow_dispatch`, resolved workflow commit `7e275a7`, and invocation run
  `31510726533`; the build log independently proves detached package source
  `995e497`. The Sigstore transparency-log index is `2423388773`; and
- the registry-downloaded tarball passed fresh installed ESM, CommonJS,
  strict NodeNext, benchmark-browser, existing-entry-browser, and root-only-
  browser consumers. It installed as exact `0.3.0` and produced the expected
  three browser bundles.

Release ID `368683536` remains the same public, non-draft, non-prerelease
GitHub Release with exact tag/title/body. Annotated tag `emdash-v0.3.0` still
peels to package source `995e497`; public `main` at publication was workflow
authority `7e275a7`. No token, ignored `.env`, local npm publish, alternate
version, package byte change, or sibling mutation participated.

### Permanent workflow hardening

Immediately after registry verification, the temporary dispatch and its sole
choice, dual concurrency/tag resolution, and manual job condition were
removed. The workflow and focused policy test now exactly match their reviewed
R1 blobs at `f965d03`: permanent `release: published` only, credential-empty
direct tag/main checkout, no manual/push/pull-request trigger, no checkout
action/submodule traversal, and unchanged protected OIDC jobs. Future release
tags will contain this corrected workflow; immutable `0.3.0` needs no trigger.

Exact hardening evidence:

```text
git diff --exit-code f965d03 --
  .github/workflows/npm-publish.yml
  packages/emdash/scripts/release-preflight-tests.mjs
  passed: exact reviewed permanent blobs

./scripts/pnpmw run package:release:check
  passed: 3/3 release identity, manifest negatives, permanent token-free
  release-only direct-checkout policy

focused ESLint over release-preflight-tests.mjs
  passed with no diagnostics

Python safe YAML parse, temporary-trigger absence scan, and git diff --check
  passed
```

No TypeScript/root aggregate, Lambdapi/kernel, book/print, browser, package
repack, CloserFans, Arrowgram, provider/model, Release, tag, environment, or
registry mutation ran for the exact hardening reversion. Those omissions are
not passes. The next admissible operation is clean non-force goal-branch push
and `main` fast-forward to exact `3af518d`, followed by public workflow-byte
verification. Only afterward may the frozen additive CloserFans stage begin.

## `AGENT-EVAL-12B3` CloserFans Candidate And Local Integration Record

Date: 2026-08-11

State: complete. Exact public package, permanent workflow hardening, and the
additive source-first host are all verified. The qualified CloserFans
checkpoint is `cbf23566fe59d03a9e5f7539a37bfdc0beb473ba` (`cbf2356`,
`feat(workspaces): add Emdash proof-agent benchmark`); the same exact commit is
now local CloserFans `master` by clean fast-forward.

### Public prerequisite closure

Immediately before the sibling edit, public Emdash `main` and the remote
tracking authority were exact permanent hardening checkpoint `3af518d`; the
remote proof-assistant branch was exact ledger checkpoint `f5206a8`.
Annotated `emdash-v0.3.0` still peeled to immutable package source `995e497`.
The permanent workflow at local/public `main` retained SHA-256
`97ea63caafdd4efd0d17eee9d99fded2ab0acf560257349e34469c633ccf8201`,
with no temporary dispatch trigger. The previously recorded npm identity,
byte equality, installed consumers, provenance, Release, and Pages evidence
therefore closed every frozen host prerequisite; none was rerun merely for
reassurance.

### Concurrent-work isolation

CloserFans initially had local `master` at exact frozen baseline `5c0d0c1`, no
remote, and one unrelated untracked quality-review plan. Branch
`goal/emdash-proof-benchmark-v1` was created from that baseline. While the new
template remained untracked, a concurrent process committed that independently
owned plan as `8980842` on the same branch. This tranche did not inspect,
absorb, reset, amend, or remove that commit. Instead it created separate
worktree `/home/user1/closerfans-emdash-benchmark-v1` and recovery branch
`goal/emdash-proof-benchmark-v1-recovery` from exact `5c0d0c1`, then reproduced
only the plan-scoped new files there. The first untracked copy remains
recoverable in the original worktree; it was neither staged nor treated as
integration evidence.

### Additive host result

The candidate changes exactly fourteen CloserFans files and 904 inserted
lines: new `templates/emdash_benchmark/**`, one focused verifier, one root
script registration, and concise `AGENTS.md`, `README.md`, and current-runtime
records. Existing `emdash_ts` over exact public Emdash `0.1.0`,
`emdash_goal_graph` over exact public Emdash `0.2.0`, the root lock, controller
pools/images, API/MCP, database, Arrowgram, and all Emdash package bytes remain
unchanged.

The auto-discovered `emdash_benchmark@1.0.0` workspace uses the ordinary Node
controller and exact public `@hotdocx/emdash@0.3.0`. Its only editable run
authority is `benchmark-run.emdash.ts`: a typed ten-entry record in canonical
case order with an explicit abstention for every initial decision. An agent
may edit one decision to a portable proof-plan patch and record exact retrieved
premises plus optional provider-reported usage. No generated report, mutable
cursor, provider state, or done flag replaces that source.

The template-local adapter implements `catalog`, `case`, `run`, `evaluate`,
`evaluate-file`, `reference`, and `verify`. Every invocation freshly
reconstructs the fixed public corpus. The source run scores as ten abstentions;
the separately labeled package-owner reference freshly retains nine accepted
complete patches and one honest ambiguity abstention. The adapter reads only
one explicitly named canonical run for `evaluate-file`; it does not scan or
write directories, invoke a provider/model, access a network, retain session
state, or claim to enforce provider-reported limits. Its preview serves only
inert HTML/README documentation and exposes neither source nor evaluator
route.

### Proportional qualification and integration

The first verifier invocation stopped before testing because the new recovery
worktree had no root `tsx`; a lockfile-based, scripts-disabled local install
bootstrapped that worktree. The first semantic run then measured a conceptual-
track versus canonical-case ordering mismatch, which was corrected by using
the package suite's exact ID order. A strengthened unknown-case negative first
hit canonical ordering; sorting that deliberately renamed attempt produced a
valid canonical run which then reached and was rejected by fresh suite
evaluation. These diagnostics are retained as corrections, not passes.

Final focused evidence is:

- `npm run templates:verify:emdash-benchmark`: passed after a disposable
  public-registry install; it asserted exact installed `0.3.0`, template
  typecheck, all seven commands, six tracks/ten cases, initial 0/0/0/10 and
  separate 9/0/0/1 outcomes, canonical run/report byte replay,
  noncanonical/stale/tampered/unknown-case rejection with exit 2, default pool,
  inert preview, and source-route 404;
- `npm run templates:validate`: passed every discovered manifest and the real
  archive exclusions;
- root `npm run typecheck`: passed after local-only `prisma generate`; the
  preceding missing-generated-client enum cascade is not a TypeScript pass;
- targeted `eslint --no-ignore` on the repository-owned verifier passed with
  no diagnostics. Template-local TypeScript/MTS is intentionally outside the
  root ESLint project and passed its own strict `tsc`; `node --check` passed
  for the static server. The default ignored-file lint observation and the
  invalid forced-project retry are not lint passes; and
- exact staged-name/stat/diff review, `git diff --cached --check`, no-secret
  scan, manifest/package assertions, unchanged predecessor-template and lock
  comparisons, and absence of generated/cache/build paths all passed.

No full Jest, Playwright, Next.js build, controller/Docker/Azure, database,
API/MCP, Arrowgram, Emdash TypeScript aggregate, Lambdapi/kernel, book/print,
provider/model, cloud workspace, push, or deployment ran. Those unchanged
boundaries are explicit omissions, not passes.

Candidate `cbf2356` has exact parent `5c0d0c1`. Immediately before integration
the candidate worktree was clean, local `master` remained exact `5c0d0c1`,
the revision count was `0 1`, the fourteen-file diff was the reviewed
candidate, and CloserFans still had no remote. `git switch master` followed by
`git merge --ff-only goal/emdash-proof-benchmark-v1-recovery` advanced only
local `master` to exact `cbf2356`; no merge commit, push, publication, or
deployment occurred. The recovery branch also retains exact `cbf2356`.

`AGENT-EVAL-12B3` is therefore complete. The next admissible benchmark work is
not an immediate model run: it is a separate read-only `AGENT-EVAL-12B4`
provider, execution, retention, privacy, reproducibility, and reporting audit,
followed by a frozen proposal and independent review before any credential,
provider, hosted action, retained run, measurement, or performance claim.

## `AGENT-EVAL-12B4` Policy Audit And Frozen First Contract

Date: 2026-08-11

State: read-only audit, behavior-free proposal, immutable first review, and
mock-only implementation checkpoint are complete. No Codex model invocation,
provider attempt, real benchmark-source edit, retained real transcript,
performance measurement, push, merge, deployment, or external mutation has
occurred. A second exact implementation/preflight review remains mandatory.

### Exact audited authorities

The audit started with all twelve Emdash worktrees clean. The active goal
branch, local `main`, `origin/main`, and the remote goal branch were exact
checkpoint `3727015c1975c346f309981b440810a309776931`, with identical tree
`7b128825c7fa5991c9a945de969c83048fb9b940`. The isolated CloserFans
benchmark worktree was clean on locally integrated `master` at exact
`cbf23566fe59d03a9e5f7539a37bfdc0beb473ba`. The unrelated concurrent
CloserFans branch at `8980842` and its untracked first template copy remain
outside this tranche.

The semantic authority remains unchanged:

- `lf_proof_agent_benchmark.ts` owns immutable cases, attempts, runs, fresh
  checker replay, outcomes, diagnostics, and integer metrics;
- `lf_proof_agent_interchange.ts` owns strict canonical interchange;
- `lf_proof_agent_public_corpus.ts` owns the six-track, ten-case corpus and
  the separate nine-success/one-abstention owner reference; and
- `lf_proof_agent_benchmark_cli.ts` owns the stateless Node adapter which
  invokes no provider and treats resource usage as unverified reported data.

The CloserFans template at `cbf2356` is a real public-package consumer, but it
is intentionally not an agent host. Its only run authority is direct
`benchmark-run.emdash.ts`; its seven commands reconstruct public corpus data
and replay attempts without a provider, session, network, controller, API,
MCP, or database. The existing CloserFans native chat path is a different
product boundary: it uses persistent sessions and broad `--search --yolo`
execution. It must not be reused or modified for the first benchmark pilot.

### Official Codex and model evidence

The audit used current official OpenAI documentation as external execution
evidence, not repository authority:

- <https://learn.chatgpt.com/docs/developer-commands> documents stable
  non-interactive `codex exec`, explicit sandbox and approval flags,
  `--ephemeral`, `--ignore-user-config`, `--ignore-rules`, JSONL,
  output-schema, model, and prompt-via-stdin controls;
- <https://learn.chatgpt.com/docs/non-interactive-mode> documents ephemeral
  runs, machine-readable events and usage, saved authentication reuse, and
  the rule that any `CODEX_API_KEY` must be scoped only to the one Codex
  process rather than a repository-controlled job environment;
- <https://learn.chatgpt.com/docs/agent-approvals-security> distinguishes
  command sandboxing from approvals and states that command network is off in
  the ordinary workspace boundary unless deliberately enabled;
- <https://learn.chatgpt.com/docs/permissions> documents beta least-privilege
  permission profiles, including root denial, minimal runtime reads,
  workspace-only writes, secret-file denies, and disabled command network;
- <https://learn.chatgpt.com/docs/config-file/config-reference> supplies the
  exact model, web-search, plugin/agent, history, environment, and network
  configuration keys used below; and
- <https://developers.openai.com/api/docs/models/gpt-5.6-sol> identifies
  `gpt-5.6-sol` as the frontier GPT-5.6 model and supports the selected high
  reasoning setting. Its snapshot table currently exposes only the same
  alias, not a separately dated immutable model identifier.

The installed local executable is exact `codex-cli 0.147.0`. Read-only login
status reports ChatGPT authentication; no account identifier, access token,
API key, or `auth.json` content was read or copied. The live local catalog
offers `gpt-5.6-sol` with catalog `comp_hash` `3000`, low through ultra CLI
reasoning settings, default low verbosity, and the ordinary Codex transport.
The requested first-pilot tuple is therefore:

```text
provider adapter: codex-cli
CLI revision:     0.147.0
model request:    gpt-5.6-sol
catalog comp_hash: 3000
reasoning effort: high
model verbosity: low
reasoning summary: none
auth category:    existing local ChatGPT login
service tier:     unset / provider default
```

The alias and catalog hash are provenance, not an immutable model snapshot.
A later rerun can reproduce the task bytes and requested configuration, but
cannot claim bitwise or time-stable model behavior unless OpenAI supplies and
the plan selects an immutable snapshot. The benchmark run's `seed` is only a
stable provenance label; it is not evidence that Codex sampling is seeded or
deterministic. API list pricing must not be applied to a ChatGPT-authenticated
run. The first receipt records token counts supplied by Codex but records
dollar cost as unknown/not applicable to this auth path.

### Credential and sandbox finding

The ordinary legacy `workspace-write` profile is insufficient for this
benchmark's credential boundary. A no-model local sandbox probe established
that a command can test the cached `~/.codex/auth.json` as readable under that
profile. The probe did not print or copy the file. Read-only protection from
modification is not protection from disclosure, so the initial idea of using
legacy `--sandbox workspace-write` is rejected.

The successful replacement no-model probe used an explicit beta permission
profile which denied `:root`, reopened only `:minimal`, reopened the exact
installed Node/Codex runtime tree read-only, made the current workspace root
writable, denied `**/*.env`, and disabled command network. Under that profile
the benchmark `package.json` remained readable while the cached auth file was
not readable. The exact runtime-tree exception was necessary on this host;
without it, the sandbox could not execute the installed Codex binary. These
probes validate feasibility only. The implementation must construct and test
the same policy for its disposable path, and must fail closed if the installed
CLI cannot enforce it.

The runner must not pass `--sandbox`, because legacy sandbox selection
overrides permission-profile configuration. It must start `codex exec` with
`--ignore-user-config` while retaining `CODEX_HOME` only for parent-process
authentication, and provide one inline strict permission profile equivalent
to:

```toml
default_permissions = "emdash-benchmark"

[permissions.emdash-benchmark]
extends = ":workspace"

[permissions.emdash-benchmark.filesystem]
":root" = "deny"
":minimal" = "read"
"<resolved-codex-and-node-runtime-root>" = "read"
":tmpdir" = "deny"
":slash_tmp" = "deny"

[permissions.emdash-benchmark.filesystem.":workspace_roots"]
"." = "write"
"**/*.env" = "deny"

[permissions.emdash-benchmark.network]
enabled = false
```

The implementation may encode this as an exact inline TOML table rather than
write into the user's Codex home. It must resolve and receipt the runtime root,
must not widen that root to the user's home, and must run no model if the
credential-denial, workspace-read/write, outside-write, `.env`-deny, or
network-deny preflight fails.

Parent-process authentication and model-command environment are separate.
The Codex parent may use the existing login, but commands proposed by the
model receive a constructed environment with inheritance `none`, a fixed
tool `PATH`, a private fake `HOME` and `TMPDIR` inside the disposable
workspace, stable locale/CI values, and no inherited token, key, secret,
cloud, npm, GitHub, proxy, or repository environment variables. The runner
sets `shell_environment_policy.ignore_default_excludes=false` as defense in
depth and `allow_login_shell=false`. No ignored Emdash/Arrowgram `.env` file
is read; its npm credential is unrelated to this run.

### Public-reference contamination

The 12B3 workspace intentionally exposes `reference`, and exact public
`@hotdocx/emdash@0.3.0` contains the owner reference patches. A model with
read access to the installed package can recover those answers. Prompt text
which merely says not to inspect them does not make the task blind.

Therefore the first runnable slice is classified exactly as an **open-book
workflow canary**. It may show that Codex can inspect one Emdash task, edit the
source attempt, invoke the stateless commands, and produce an independently
replayed result under the frozen boundary. It cannot support a theorem-proving
rate, comparison with another prover or model, leaderboard entry,
representative-corpus score, or `AGENT-EVAL-12B4` graduation. The receipt must
set `contamination = "public-owner-reference-accessible"` and
`graduationEligible = false`, even if raw command audit finds no forbidden
reference access.

A later measured stage requires a decontaminated split boundary. The agent
side may receive only the selected canonical case/task surface, authoring
instructions, one attempt file, and a narrow stateless checker interface. The
independent host side must retain the full package, owner references, and
authoritative evaluator where the agent's filesystem and tools cannot read
them. Prompt prohibitions, path hiding, post-hoc assertions, or deleting a
command name are not substitutes for this isolation. Designing that split is
later work and must not enlarge the trusted Emdash Core or introduce a hidden
mutable prover server.

### Ordered 12B4 stages

The single roadmap row is implemented through three internal stages. These
stage names do not add new rows to the 41-row master accounting.

1. **Stage A — local workflow canary.** Add a standalone, mock-tested
   CloserFans operator runner, then separately preflight and execute at most
   one real Codex attempt for `native.exact.local-premise`. It is open-book,
   non-graduating, local-only, and may legitimately abstain or fail.
2. **Stage B — decontaminated repeated suite.** Freeze and implement a split
   agent/evaluator environment in which owner answers are unavailable to the
   model, then run repeated independent trials over all ten unchanged cases.
3. **Stage C — measured graduation.** Publish only claims supported by Stage
   B's exact trial matrix, checker outcomes, contamination audit, and
   uncertainty. A composite score, cross-model ranking, hosted registry, or
   product claim requires another explicit contract rather than following
   automatically.

### Frozen Stage A implementation boundary

The first immutable review may authorize only local implementation and
mock/fake-process tests in a new isolated CloserFans branch/worktree from
exact clean `cbf2356`. It does not authorize the real Codex call. The
implementation must be additive under `templates/emdash_benchmark/**` plus
one narrowly owned verifier/script registration if required. It must not
modify Emdash semantics or package bytes, the existing native-chat runner,
controller pools/images, API/MCP, database, GetPaidX plugin contract,
Arrowgram, cloud/deployment configuration, or any other template.

The operator runner must:

1. create a fresh private disposable Git workspace for one invocation and
   copy/install only the exact existing `emdash_benchmark` fixture;
2. start from exact public `@hotdocx/emdash@0.3.0`, canonical ten-abstention
   source, corpus fingerprint, selected case ID, and a clean Git baseline;
3. allow the agent to edit only the selected attempt in
   `benchmark-run.emdash.ts`; every other file/attempt change invalidates the
   canary even when the evaluator would accept it;
4. permit ordinary inspection of the fixture README, package manifest,
   selected source entry, and exact `case` output, plus stateless `case` and
   `evaluate` commands; forbid `reference`, direct `node_modules` inspection,
   other-case acquisition, installation, Git mutation, network tools, and
   writes outside the one source file;
5. treat abstention, rejected proof, accepted-incomplete proof, process
   failure, timeout, policy violation, and accepted-complete proof as distinct
   outcomes; never repair or reinterpret a model result silently;
6. independently rerun the canonical evaluator after Codex exits and make
   that fresh report—not model prose—the proof acceptance authority; and
7. preserve the exact candidate source/diff and canonical attempt/report
   digests needed for review without making the raw conversation proof
   evidence.

The first real invocation, if a later preflight review authorizes it, must use
the equivalent of the following explicit controls. The final implementation
owns the safely quoted argument vector; this is a contract, not a shell
snippet to copy blindly:

```text
codex --strict-config
  --ask-for-approval never
  --model gpt-5.6-sol
  --disable hooks
  --disable plugins
  --disable remote_plugin
  --disable plugin_sharing
  --disable recommended_plugins
  --disable skill_search
  --disable skill_mcp_dependency_install
  --disable multi_agent
  -c agents.enabled=false
  -c web_search="disabled"
  -c model_reasoning_effort="high"
  -c model_verbosity="low"
  -c model_reasoning_summary="none"
  -c hide_agent_reasoning=true
  -c history.persistence="none"
  -c memories.generate_memories=false
  -c memories.use_memories=false
  -c allow_login_shell=false
  -c <exact least-privilege permission profile>
  -c <exact constructed command environment>
  exec --ephemeral --ignore-user-config --ignore-rules
  --json --output-schema <schema> --output-last-message <private-path> -
```

The prompt is supplied on stdin from a tracked versioned template. It names
one case, the sole editable source location, allowed commands, forbidden
reference surfaces, abstention, and the fact that fresh evaluator replay is
authoritative. The final output schema contains only case ID, declared
disposition, and a short non-sensitive completion note. It must not request or
retain chain-of-thought. Prompt, schema, case text, and initial-source bytes
are each SHA-256-bound in the receipt.

The outer runner enforces a 600,000 ms wall timeout and records any graceful
termination/kill sequence. It does not claim a token cap because installed
`codex exec` exposes no audited hard token-limit flag. JSONL is parsed
fail-closed: unknown or malformed events invalidate usage and command-audit
claims rather than being ignored. `turn.completed` usage supplies reported
input, cached-input, output, and reasoning-output counts when present. Outer
monotonic time supplies elapsed duration. Agent-visible evaluator invocations
and the final independent host replay are counted separately. None of these
operational fields changes theorem authority.

### Retention, privacy, and receipt contract

Raw JSONL, final model text, command arguments/output, and transient source
copies may contain reasoning summaries, paths, source text, or accidental
sensitive material. They are private operational evidence, never tracked
artifacts. The runner creates them with user-only permissions under one
explicit ignored/quarantined directory or private temporary directory. It
never uploads, serves, commits, publishes, or sends them to GetPaidX. It does
not print raw JSONL or credentials to the ordinary console.

For the first real canary, raw evidence remains only until an operator reviews
the forbidden-command and secret scans and derives the minimized receipt. A
later preflight review must authorize the exact bounded removal policy for the
runner-created directory; this proposal does not delete anything. The source
attempt, fresh canonical evaluator report, and minimized receipt may be
retained after human/privacy review because they contain no model reasoning or
credential values.

The canonical receipt must include at least:

- receipt schema/revision, runner commit and clean/dirty state;
- Emdash package name/version/integrity, corpus/run/case/profile fingerprints,
  selected case, and initial source digest;
- prompt/schema/case-text digests, not an unreviewed raw prompt transcript;
- CLI version, requested provider/model/effort/verbosity/summary, local model
  catalog hash, auth-method category, and explicit mutable-alias warning;
- permission-profile digest, resolved runtime read root, constructed
  environment keys, disabled network/search/plugin/MCP/hook/memory/subagent
  controls, and preflight results;
- start/end timestamps, monotonic duration, timeout/exit state, and provider-
  reported token fields without a fabricated dollar cost;
- parsed tool/command audit, evaluator-call counts, forbidden-surface result,
  exact source diff and digest, and final host replay outcome;
- canonical attempt/run/report hashes and any stable diagnostics; and
- `contamination`, `graduationEligible=false`, and a statement that neither
  receipt nor AI output is proof evidence.

Authentication is recorded only as a category such as `chatgpt`; user,
workspace, account, token, cookie, and credential-file contents are forbidden
receipt fields. Host-absolute paths are normalized or omitted. If any secret-
name/value scan, permission preflight, source-scope check, command audit, or
canonical replay cannot be completed, the receipt is invalid and no benchmark
claim may be made.

### Stage A validation and approval sequence

This proposal checkpoint is plan-only. Its proportional gates are exact diff,
Markdown/link/heading hygiene, worktree/ancestry checks, and confirmation that
no provider/model process ran. No TypeScript, CloserFans, browser, package,
kernel, book, or repository aggregate can add evidence to this behavior-free
freeze.

After a separate immutable proposal review, implementation requires:

- fake-Codex process fixtures for accepted, rejected, abstained, malformed
  JSONL, timeout, nonzero exit, forbidden command, forbidden file edit,
  unknown event, and tampered evaluator output;
- focused runner/verifier tests proving exact arguments/configuration,
  prompt/schema hashes, source confinement, fail-closed parsing, receipt
  minimization, private file modes, and no secret values;
- no-model sandbox probes proving credential denial, workspace access,
  `.env` denial, outside-write denial, and command-network denial under the
  generated exact permission profile;
- the existing template verifier, template validation, strict local
  TypeScript/Node checks, root typecheck and focused lint only as directly
  affected; and
- exact staged diff, no-secret, ignored-output, unchanged-owner, and clean
  branch ancestry review before a rollback-safe implementation checkpoint.

No long Jest/Playwright/build, root Emdash `check:ts`/`check:all`, CloserFans
cloud/controller/database/API/MCP aggregate, Lambdapi/kernel, or book/print
gate is required for this isolated runner unless an exact changed boundary
later makes omission progress-blocking. Omissions are not passes.

The implementation checkpoint still performs no real model call. A second
immutable preflight review must bind its exact code, tests, CLI/catalog/login
category, permission probe, selected case, prompt/schema/source hashes,
timeout, private output path, and expected maximum one invocation. Only then
may the goal authorize one local Stage A call under delegated unattended
authority with human supersession. Any retry requires a new receipt and
explicit reason; it is not silently part of the one-call authorization. No
push, deployment, public benchmark result, or Stage B/C work follows
automatically.

### Immutable Stage A proposal review

Review date: 2026-08-11

Reviewed proposal checkpoint:
`286a50db5f3295d4f9dbe58e046c82f53ad37e55`, exact parent
`3727015c1975c346f309981b440810a309776931`, exact tree
`6be5c72f62a31e088e8bedb01afe001b9fa52d23`.

The proposal changes only the two living plans. Its immutable complete-file
SHA-256 values are:

```text
c71bc63ffb715fdb39e0792766a565b15c033de911a0f54449b6f4b2fdcb3942
  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
48e0e9044ee59d602637ec9706e3d97a4402167d18d7be33716e093c0e80ca93
  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
```

Exact name/status review, `git diff --check`, secret-token pattern scan,
clean Emdash/CloserFans status, and remote divergence review passed. The
proposal branch was exactly one commit ahead of its unchanged remote; no push,
model run, source edit, package operation, sibling mutation, retained raw
evidence, or aggregate occurred. Official links were fetched during the
audit. Master accounting remains 35 of 41: it excludes the three completed
readiness/audit ledger rows and counts the two generic PathOut prerequisites
as their recorded single bounded checkpoint.

The review accepts the architecture and Stage A selection, but adds five
mandatory corrections before implementation:

1. **Narrow writes.** The illustrative proposal profile's workspace-wide
   write is too broad. The generated effective profile must make the
   disposable workspace read-only by default and reopen only the selected
   `benchmark-run.emdash.ts` plus exact private fake-home and temp subtrees for
   writes. `package.json`, lockfiles, scripts, README, Git metadata, and all
   `node_modules` remain read-only. Root, real home, real temp, `.env`,
   `.agents`, and `.codex` reads remain denied except the separately resolved
   read-only Node/Codex runtime needed to execute tools.
2. **Never execute unvalidated agent TypeScript as host code.** The candidate
   source is hostile until a non-executing TypeScript AST validator proves
   that the complete file is byte/AST-identical to baseline except for the
   selected `benchmarkAttemptEdits` value and that this value uses only the
   reviewed data-literal grammar. Imports, calls, accessors, identifiers,
   spreads, computed keys, templates, functions, classes, statements, and
   every other case are forbidden. The host extracts/reconstructs canonical
   patch data from that syntax; it never imports the candidate module.
3. **Separate clean replay.** Agent-visible evaluation may run inside the
   restricted disposable workspace, but final authority runs in a fresh
   host-controlled evaluator environment whose package/scripts cannot have
   been modified by the agent. It consumes only statically extracted canonical
   data and the exact selected case. A same-workspace post-run import is not
   independent evidence.
4. **Two-phase setup.** Any exact public-package installation is an outer host
   setup step before Codex starts, uses the fixture lock with lifecycle scripts
   disabled and no registry credential, and is recorded separately from the
   command-offline agent phase. The contributor workspace is never the
   installation target. The installed package identity/integrity and the
   read-only permission outcome are preflight gates.
5. **Bound untrusted bytes.** Before parsing or execution, cap the candidate
   source at 262,144 bytes, each JSONL line at 4 MiB, cumulative JSONL at
   64 MiB, and final-message output at 65,536 bytes. Overflow terminates the
   process and yields a distinct invalid operational result. Implementation
   may lower these limits after focused fixtures prove the selected task fits;
   it may not raise them without another review.

With those corrections, the review requires all of the following conditions:

1. exact baseline `cbf2356` and a new isolated CloserFans branch/worktree;
2. changes limited to the benchmark template and its narrowly owned focused
   verifier/script/docs registrations;
3. exact `codex-cli 0.147.0` argument/config construction, but only fake Codex
   processes in this implementation tranche;
4. root-denying least-privilege no-model probes and inherit-nothing command
   environment, with all failures closed before a provider process;
5. no inherited parent `AGENTS.md`, `.codex`, plugin, MCP, hook, rule, memory,
   web-search, or subagent input in the disposable agent workspace; any
   intentional instruction file becomes tracked prompt material and is
   digest-bound;
6. non-executing whole-source validation and fresh clean evaluator replay as
   corrected above;
7. distinct outcomes, exact diff/command/event audits, and canonical hashes
   without accepting model prose as proof;
8. private mode-restricted raw evidence and a receipt which excludes
   credentials, account identity, raw reasoning, and unnormalized host paths;
9. permanent open-book contamination and non-graduation labels for Stage A;
   and
10. focused fake-process, permission, source-validator, evaluator, template,
    typecheck/lint, secret, diff, and ancestry gates with every aggregate
    omission stated honestly.

Decision: approve only the corrected mock-driven Stage A runner
implementation under delegated unattended authority, with later human
supersession. Do not run Codex, use an OpenAI API key, read/copy cached auth,
retain a real transcript, remove private evidence, push/deploy, change a
package/release, modify another CloserFans surface, or begin Stage B/C. After
the implementation checkpoint, synchronize both plans and perform the second
exact preflight review required by the proposal before at most one real call.

### Stage A mock implementation checkpoint and validation record

Implementation date: 2026-08-11

The bounded implementation was made in the isolated CloserFans worktree
`/home/user1/closerfans-emdash-canary-v1` on branch
`goal/emdash-proof-agent-canary-v1`, starting from exact clean host checkpoint
`cbf23566fe59d03a9e5f7539a37bfdc0beb473ba`. It is preserved by two additive
local commits:

```text
1d77473f662c345d52c060b5af8364ab93265503
  feat(templates): add mock Emdash agent canary
8e270a78da2762148da0c93b0a8b64b74b6d14e9
  fix(templates): retain canary install lock
final tree 9fc93afd801b8db2351643249abd0063df580dc6
```

The second checkpoint is a visible correction, not rewritten history. The
first implementation placed `package-lock.json` at the template root, but the
existing CloserFans template validator rejects that generated filename and
the template uploader excludes it. The correction retains the identical lock
as `scripts/emdash-canary-package-lock.json`; host-controlled setup
materializes it as `package-lock.json` only inside each disposable clean
install before `npm ci --ignore-scripts --no-audit --no-fund`. The hosted
archive therefore retains immutable installation bytes without widening the
shared validator/uploader policy. The isolated canary worktree itself has no
root `node_modules` directory.

The implementation adds no selectable real provider. Its public
`canary:mock` command always spawns the tracked fake process through the exact
Node executable, while its separate permission probe uses only the installed
`codex sandbox` wrapper and makes no model/API request. The real `codex exec`
argument constructor is present for review, pinned to `codex-cli 0.147.0`,
`gpt-5.6-sol`, catalog hash `3000`, high reasoning, low verbosity, no
reasoning summary, ephemeral JSONL, strict output schema, ignored user config
and rules, disabled network/search/plugins/MCP/hooks/memories/skills/subagents,
and an inherit-nothing command environment. No public command can select that
constructor as a process driver in this checkpoint.

The source and replay boundary implements the first review literally where
the operating system permits it:

- the agent sees a separate Git workspace and a copy of the exact selected
  source at `candidate/benchmark-run.emdash.ts`;
- package metadata, scripts, lockfile, Git metadata, and dependencies are
  explicitly read-only, while the candidate subtree and private fake
  home/temp subtrees are the only listed writes;
- the candidate is never imported or executed by the host. TypeScript parses
  the whole file, exact prefix/suffix byte equality permits a change only to
  the selected `benchmarkAttemptEdits` initializer, and a bounded literal
  extractor rejects calls, imports, identifiers, templates, accessors,
  computed keys, spreads, omitted array entries, duplicate/prototype keys,
  functions, classes, statements, or other executable syntax;
- extracted canonical JSON-like data crosses into a separately installed,
  host-controlled evaluator which reconstructs all ten fixed public cases and
  freshly replays the unchanged Emdash evaluator; and
- source, JSONL line/total, stderr, final-message, literal-depth/node, and
  extracted-attempt bounds fail closed. Timeout termination records `SIGTERM`
  and bounded `SIGKILL` escalation rather than silently treating an
  operational failure as abstention or proof failure.

Live Linux sandbox probes required two concrete refinements which the second
review must adjudicate explicitly. First, Bubblewrap cannot reopen one file
for writes below a read-only parent mount, so the writable unit is the
`candidate/` directory. A before/after manifest and Git/diff audit rejects
any additional candidate or workspace-root creation and accepts only the
selected file change. Second, an explicit filesystem-root deny conflicts with
the writable nested workspace mounts. The effective profile instead begins
from missing-path default denial, reopens only minimal runtime paths and the
enumerated workspace entries, and explicitly denies both system temporary
aliases and command network. The synthetic workspace shell can receive a new
root name at kernel level, so the same post-run manifest rejects it; existing
unlisted host, credential, environment, evidence, and provider-state paths
remain unreadable and unwritable. The no-model probe verifies these effective
properties rather than equating the implementation with an unexecuted TOML
sketch.

Host Codex state/temp and command-visible fake home/temp are disjoint. Private
runner/probe roots live under mode-`0700` `~/.emdash-stage-a/{runs,probes}` so
they are short enough for the TypeScript runner's Unix sockets and do not use
the denied system temp roots. Raw JSONL, final text, stderr, and intermediate
artifacts remain mode-restricted private evidence. The tracked/minimized
receipt records canonical hashes, normalized configuration/outcomes,
permission/command/event audits, reported usage, contamination, and
`graduationEligible=false`; it excludes credentials, account identity, raw
reasoning, and unnormalized host paths. Copied npm `.bin` links are rebased to
relative package-local links, and the benchmark command uses
`node --import tsx` so the agent does not require a writable tsx control
socket.

Focused validation on final tree `9fc93af` is green:

```text
template registry validation
  10 templates accepted, including emdash_benchmark

--permission-probe-only
  ✔ emdash_benchmark no-model permission and command probe passed
--canary-only
  ✔ emdash_benchmark focused Stage A mock canary passed
--adapter-only
  ✔ emdash_benchmark public-package/source-run smoke passed
--cli-only
  ✔ emdash_benchmark public Stage A mock CLI passed
```

Each focused verifier creates a disposable copy, materializes the retained
lock, performs clean `npm ci`, verifies exact public
`@hotdocx/emdash@0.3.0`, and runs the template TypeScript check before its
mode-specific gate. The fake suite covers accepted, rejected, abstained,
malformed JSONL, timeout, nonzero exit, forbidden command, forbidden source/
workspace-root creation, unknown event, and evaluator-tamper paths. The root
focused verifier also proves that the shared archive rule excludes generated
`**/package-lock.json` but not the retained canary lock. Exact diff/whitespace,
tracked-path, ancestry, ignored-output, and token/private-key pattern checks
are green. CloserFans' current ESLint configuration ignores both `templates/**`
and `scripts/**`, so there is no applicable changed-file lint owner and no
lint pass is claimed.

The complete owning verifier was green before the lock-path correction; the
four current-tree focused modes and template registry check directly cover
the corrected setup, containment, replay, adapter, and CLI boundaries. No
long CloserFans aggregate, cloud/controller/database/API/MCP check, provider
or model invocation, Emdash `check:ts`/`check:all`, Lambdapi/kernel,
book/print, push, merge, deployment, package release, or cleanup ran. These
are omissions, not passes. The master roadmap remains 35 of 41 because this
mock subtranche does not complete `AGENT-EVAL-12B4`.

The next admissible action is only the second immutable preflight review below.
Until its corrective result is implemented and separately rebound, no real
Codex/provider process, credential access, retained real transcript, retry,
result claim, push, merge, deployment, or Stage B/C work is authorized.

### Second exact implementation/preflight review and corrective driver proposal

Review date: 2026-08-11

Review result: **mock implementation accepted; real call not authorized.**

The review binds Emdash plan checkpoint
`00d56a2257a48af8d53d84d5bc7ea77ad04bdd2e`, CloserFans implementation
checkpoints `1d77473f662c345d52c060b5af8364ab93265503` and
`8e270a78da2762148da0c93b0a8b64b74b6d14e9`, final CloserFans tree
`9fc93afd801b8db2351643249abd0063df580dc6`, and exact host baseline
`cbf23566fe59d03a9e5f7539a37bfdc0beb473ba`. Both goal worktrees were clean;
the canary branch was exactly `0 2` relative to that baseline and had no root
`node_modules`.

The complete relevant final-tree SHA-256 inventory is:

```text
06a5f28554079aaabe7f7bd63ff70e0542a64ac2a98a47fcf53b5b239a65f338
  templates/emdash_benchmark/package.json
e8dbd30a445c9a81f256d15b040548bfff24ffdc81d80fc613d131d07715c9d3
  templates/emdash_benchmark/getpaidx.template.json
50ea5f65a847571bf809a37d092b5de7127769c2f4f9dde8f8d02c8de37ed3d8
  templates/emdash_benchmark/README.md
0c104f3888c61ce669958c44051ea65a153d9fbaea3c9c37139e6325b310eb84
  templates/emdash_benchmark/benchmark-run.emdash.ts
d30d84d74a5f78ee967c403702d188373006b4841ddde24f742831afa930c976
  templates/emdash_benchmark/scripts/emdash-benchmark.mts
a0e7ee0431f6196353b7e993fa937d2e0981980c84188352d956fcda5be15366
  templates/emdash_benchmark/scripts/emdash-canary-contract.mts
0f6c65353062241d4677acc77bc7f6ee93a53df2400cf019b8adc677d163ac86
  templates/emdash_benchmark/scripts/emdash-canary.mts
7666a3659b487fd4633e22b31f3872fa8c262a3ebccc280112f93b40b4305cc8
  templates/emdash_benchmark/scripts/emdash-canary-evaluate.mts
117768e52381ede1b23f3bf4c43064e526daa6a25f3d8d4b0c3c879ffd7574ed
  templates/emdash_benchmark/scripts/emdash-canary-prompt.txt
f8935691d02f44d7c9b2d0ad1c96559c985c5596ecc210c3c03390a0680a8e06
  templates/emdash_benchmark/scripts/emdash-canary-output.schema.json
1f9efb7b416b9ab162ddc98f14c2c4ade0a56ddcf2df5fb519f437031f9fccf8
  templates/emdash_benchmark/scripts/emdash-canary-package-lock.json
523357c1109f62bd956d196c9a9280ea5313b5a264c0e080608e9c56b021caac
  templates/emdash_benchmark/scripts/probe-emdash-canary-permissions.mts
d2c2107eeefe1fb87a032e5d0f2eb8987c80e2c24109ee643135fc61f94ea9e9
  templates/emdash_benchmark/scripts/verify-emdash-canary.mts
0194c5dc3c8ed794eeb25f37250d9e2e6e50d3d21b11c3249ae7b5846b76e006
  templates/emdash_benchmark/scripts/fixtures/emdash-canary-fake-codex.mjs
19a859f59d53c3811ae9fb29aea91bbfe5022acf35f1dd91a967cff9f4f276db
  scripts/verify-emdash-benchmark-template-runtime.ts
```

The retained lock resolves exact `@hotdocx/emdash@0.3.0` with integrity
`sha512-ewAhab+tLMY0QZrOXLMSpH19VYkP73iR2iYxYRireYK+21QDOi9Cp/Tq4su+QI+b/NmYnUoZzGoEEQpBGJCxxg==`.
The preceding focused evidence and template-validation result remain exact.
A fresh read-only preflight reports `codex-cli 0.147.0`, login category
`ChatGPT`, and a model cache fetched 2026-08-11 which exposes
`gpt-5.6-sol`, `comp_hash` `3000`, default low verbosity, and high among its
supported reasoning levels. No account identifier or credential-file content
was read or copied, and no model was invoked.

The security and replay implementation passes review, including the two
measured Linux mount refinements. The call authorization fails for a narrower
operational reason: the current artifact is intentionally and physically
mock-only.

1. `emdash-canary.mts` always spawns the tracked fake fixture with
   `process.execPath`; its CLI requires one enumerated `--fake-scenario` and
   rejects any real-provider selection.
2. Its parent environment deliberately points `HOME` to a new empty private
   directory and passes no `CODEX_HOME`. This proves fake/no-model isolation,
   but cannot reuse the existing ChatGPT login required by the frozen pilot.
3. Its receipt correctly hardcodes `providerExecuted=false`,
   `authCategory=none-fake`, `liveNoModelProbePassed=false`, and fake cost
   semantics. Reusing or editing that receipt after the fact would be false
   provenance.
4. The real receipt contract still needs explicit runner commit/dirty state,
   current model-cache tuple, at-call probe identity, and corpus/case/profile
   fingerprints. Existing canonical artifact hashes are strong replay
   evidence but do not silently substitute for these named provenance fields.
5. There is consequently no reviewed executable which both performs exactly
   one authenticated parent call and feeds its output through the already
   qualified source/event/replay/receipt boundary. An ad hoc shell command or
   one-line replacement of the fake driver would bypass the immutable-code
   requirement.

Decision: deny the real Stage A call at this checkpoint. This is not a failed
mock implementation and does not undo either CloserFans commit. It is the
required fail-closed outcome of the second preflight.

The smallest corrective tranche is frozen as a behavior-free proposal:

1. Keep `npm run canary:mock` and its CLI physically fake-only. Add one
   separate local operator entry, not a hosted endpoint, package lifecycle
   hook, MCP/API action, or default template command.
2. Make that entry a dependency-free root Node bootstrap. It creates one
   explicit mode-`0700` run root, copies only the benchmark template,
   materializes the retained lock, performs one scripts-disabled credential-
   empty clean install, and then starts an internal TypeScript one-shot driver
   from that installed authority. The contributor worktree still receives no
   `node_modules`.
3. Refactor the shared runner around a closed fake-versus-real driver union.
   The mock public CLI can construct only the fake member. The operator entry
   can construct the real member only when passed the exact checkpointed
   authorization ID and a not-yet-existing run root; no loop, retry, fallback
   provider, or second spawn is present.
4. Before the provider spawn, require exact CLI version, exact `Logged in
   using ChatGPT` category, current cache tuple `gpt-5.6-sol`/`3000` with high
   support, strict-config parse, and a fresh successful no-model permission/
   command/network probe built from the same permission function. Failure at
   any gate leaves `providerExecuted=false` and performs no call.
5. Give only the Codex parent the existing home/`CODEX_HOME` locator needed
   for saved authentication; never read or copy `auth.json`. The model's
   commands retain inheritance `none`, fake home/temp, fixed path/locale, and
   no credential locator or value. Provider transport remains outside the
   command-network-denied sandbox.
6. Derive receipt driver/auth/probe/cost fields from the closed driver result
   rather than constants. Bind runner commit/tree/clean state, exact model
   cache fields, generated argument vector after the explicit run path exists,
   package/corpus/case/profile/source/prompt/schema data, probe/script digests,
   source/event/command/replay audits, and the permanent contamination/non-
   graduation labels. Never emit a credential path/value, account identity,
   raw reasoning, or fabricated dollar cost.
7. Preserve raw output privately and do not delete it in this tranche. A
   provider process which starts consumes the sole authorization even if it
   times out, exits nonzero, violates policy, abstains, or produces a rejected
   proof. Any retry requires a new immutable review and authorization ID.
8. Add fake-provider tests of the real-driver orchestration, including every
   pre-spawn refusal, exactly-one-spawn accounting, dynamic receipt fields,
   parent-versus-command environment separation, and post-spawn operational
   failures. These tests must never contact a provider.

The corrective implementation may touch only the benchmark template, one
dependency-free root operator script, its narrowly owned verifier/registration,
and these plans. It must not change Emdash bytes/semantics, another template,
native chat, controller/API/MCP/database, cloud/deployment, Arrowgram, package
release, or Stage B/C. Focused fake/no-model/template/typecheck/diff/secret/
ancestry gates remain sufficient; no long aggregate is justified.

This proposal authorizes no code by itself. It requires a separate immutable
review checkpoint before implementation, followed by a final exact code/
preflight review before one real call. Human direction may supersede the
delegated unattended sequence at any point.

### Immutable corrective driver proposal review

Review date: 2026-08-11

Reviewed proposal checkpoint:
`4ab09fce690be378bfec314d8d0ad67e5f0aaaa0`, exact parent
`00d56a2257a48af8d53d84d5bc7ea77ad04bdd2e`, exact tree
`7012f362174d6c2449f896461cd6fe6c3f1bb99a`.

The proposal changes only the two living plans. Its immutable complete-file
SHA-256 values are:

```text
2ea99af614f0d9585740f72e2f1b9c00aadb6d94f468ca4261666e788557e858
  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
220776b4897d6732857972cec21003a5e0e6ba7858a04eefc021ee2c4d233627
  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
```

Exact ancestry, clean Emdash/CloserFans worktree state, full implementation
hash inventory, Markdown/diff hygiene, token/private-key pattern scan, CLI
version, login category, and selected model-cache fields were reviewed. No
credential content, provider/model call, code edit, raw real transcript,
package operation, network mutation, push, merge, deployment, or aggregate
occurred. The second preflight's denial is correct: reviewing an argument
constructor does not manufacture a truthful authenticated driver.

The corrective architecture is accepted with these mandatory refinements:

1. **Consume authorization atomically.** Select one non-secret authorization
   ID in the final preflight. Immediately before the sole provider spawn, the
   operator must create a mode-`0600` lease with exclusive-create semantics
   under mode-`0700` `~/.emdash-stage-a/authorizations/`. An existing lease
   refuses the call. A spawn attempt consumes the authorization even if exec,
   transport, model, policy, or replay later fails. Neither runner nor this
   goal deletes or rewrites the lease. Tests inject a disposable state root
   and cannot consume the real authorization.
2. **Bootstrap committed bytes, not ignored state.** The dependency-free root
   operator must require a clean exact Git checkpoint and reconstruct the
   benchmark template from its tracked commit tree (for example, enumerated
   `git ls-tree` plus `git show` bytes), excluding working-tree ignored files.
   It refuses a source root with staged, unstaged, or untracked changes and
   records commit/tree/template-manifest digests. The contributor canary
   worktree keeps no root or template `node_modules`.
3. **Keep the public path physically mock-only.** No `package.json` script,
   hosted button, API/MCP action, lifecycle hook, native-chat integration, or
   fake CLI flag may select the real member. One separate root operator entry
   owns the local path. Test dependency injection is callable only from the
   focused verifier and is absent from the operator's command-line grammar.
4. **Use a closed parent environment.** The real parent environment may
   contain only fixed runtime/locale/temp fields plus the existing `HOME` and
   optional `CODEX_HOME` locator needed by saved ChatGPT authentication.
   Reject or drop `OPENAI_API_KEY`, `CODEX_API_KEY`, npm, GitHub, cloud,
   proxy, repository, and unrelated secret variables. Never read, copy, hash,
   receipt, or expose credential-file contents or paths. The command
   environment remains the existing inherit-nothing fake home/temp policy.
5. **Finish every no-model gate before the lease/spawn.** Exact Git/template/
   package/integrity, CLI version, ChatGPT login category, model-cache tuple,
   strict config parse, source/case/prompt/schema hashes, and the fresh
   permission/filesystem/command/network probe must pass first. The lease is
   then created and exactly one provider child may be spawned. No retry,
   fallback, recursion, or implicit second turn is allowed.
6. **Make provider provenance observationally true.** A child `spawn` event,
   not intent, sets `providerExecuted=true`. The receipt distinguishes
   pre-spawn refusal, spawn/exec failure, timeout/overflow, invalid stream,
   policy/source violation, evaluator failure, abstention, rejection,
   accepted-incomplete, and accepted-complete. Driver kind, ChatGPT auth
   category, current model tuple, at-call probe and lease identity, argument
   vector, exact runner commit/tree/clean state, corpus/case/profile, package,
   source/prompt/schema, and canonical artifact hashes are derived from
   observed data. Dollar cost stays null.
7. **Preserve independent authority and private evidence.** The candidate
   remains hostile data; no real-driver refactor may import it or evaluate in
   the agent tree. Raw provider output remains under the existing private
   evidence boundary, untracked and undeleted. Receipt minimization,
   open-book contamination, `graduationEligible=false`, and
   `proofEvidence=false` are unconditional.
8. **Test every new branch without a provider.** Add focused fake executable
   cases for all pre-spawn refusals, lease collision, exactly-one spawn,
   authenticated-parent/credential-free-command separation, truthful dynamic
   receipt, and post-spawn failure classes. Re-run the existing mock suite,
   live no-model probe, public adapter/CLI, clean install/typecheck, template
   registry, exact diff/secret/ancestry/ignored-output checks, and no
   in-worktree dependency-tree assertion.

Decision: approve only this corrected local one-shot-driver implementation
under delegated unattended authority, with later human supersession. Do not
invoke a provider/model, create the real authorization lease, read/copy auth
content, retain a real transcript, change Emdash, modify another CloserFans
surface, add a public/hosted invocation, push, merge, deploy, release, clean
up, or begin Stage B/C. After a focused-green correcting checkpoint,
synchronize both plans and perform a final immutable code/preflight review.
Only that later checkpoint may authorize at most one call.

### Corrective one-shot driver implementation checkpoint

Implementation date: 2026-08-11

The approved local tranche is now checkpointed on isolated CloserFans branch
`goal/emdash-proof-agent-canary-v1` at
`1abdfd8ee3711a3993fa0db573672ababee7e6d3`, exact parent
`8e270a78da2762148da0c93b0a8b64b74b6d14e9`, and exact tree
`5912793c74fa2b4a247b69f2915baa16344d8447`. The worktree is clean and the
checkpoint remains local: no push, merge, deployment, release, API/MCP,
controller, database, other template, Emdash, Arrowgram, or hosted surface
changed.

The checkpoint implements the reviewed separation rather than weakening the
mock canary. `npm run canary:mock` retains an enumerated fake-scenario grammar
and has no real selector. A separate dependency-free repository operator
requires the exact non-secret authorization ID, an absolute unused run root,
and a clean source worktree; reconstructs the template from `git ls-tree` and
`git show` bytes at the recorded commit; excludes ignored working-tree state;
materializes the retained lock; and performs a scripts-disabled,
credential-empty clean install. It then invokes an internal closed
fake-versus-real driver unavailable from `package.json`, API, MCP, controller,
or hosted UI.

The real member performs exact CLI-version, `Logged in using ChatGPT`, model-
cache tuple, selected-case, strict-config, filesystem, command, and network
preflights before the authorization boundary. Its parent environment is a
closed eight-key set—fixed runtime/locale/temp fields plus `HOME` and
`CODEX_HOME`—while model-created commands retain the existing inherit-nothing
fake-home/temp environment. The operator never reads, copies, hashes, or
receipts authentication content. Immediately before the sole provider spawn,
an exclusive mode-`0600` lease is created below a mode-`0700` authorization
directory. The lease is never removed or rewritten, no retry/fallback/loop is
present, and a child `spawn` event—not intent—sets `providerExecuted`.

Receipt revision v2 derives driver, ChatGPT-auth category, model-cache,
permission-probe, lease, argument-vector, source commit/tree/clean state,
template/operator, package, corpus/case/profile, prompt/schema, command/source
audit, replay, usage, and canonical-artifact provenance. Spawn failure,
timeout/overflow, process failure, invalid stream/final message, scope or
authority violation, replay failure, abstention, rejection, incomplete
acceptance, and complete acceptance remain distinct. Raw JSONL, stderr, final
message, candidate source/diff, selected attempt, and clean replay remain
private and untracked. Dollar cost stays null, and contamination,
`graduationEligible=false`, and `proofEvidence=false` are unconditional.

The complete changed-file SHA-256 inventory is:

```text
e6e93778a0e021bed8074d888958070465f7bae724879871c6801a3a4288e2f9  AGENTS.md
cab4764e39e69c9eee7a177da539347f5a9f4a3693be816d3900d08580849db6  README.md
42325cdedd181f36e1e221c6eb9d6fd2aadf89c005b05b55b08cc7e00b6aee01  scripts/run-emdash-stage-a-real.mjs
de000ea8a72b9c2d1f482f5801159178677a3f3501925afadf582bfaca42808e  scripts/verify-emdash-benchmark-template-runtime.ts
b6d4eb040df34eab3864e1c3fad34f49cc0fcc5c669f8f797f0ff95a0e02875a  templates/emdash_benchmark/README.md
f89f208da92ac16e6835354bee273c5a365a7035a4831bb94a10a7f4eac3e8f1  templates/emdash_benchmark/scripts/emdash-canary-contract.mts
db599cd2e5dc70f34ff0e6c5c43a910cb003dc9d741d3b49942229dec9e3af88  templates/emdash_benchmark/scripts/emdash-canary-evaluate.mts
74962e480ad3bd3b51af22ae64314d3d988338146f482b6c3dff428c3b93e23e  templates/emdash_benchmark/scripts/emdash-canary-real.mts
12c278ceadcb88f0bd1b0dbea0a24e7a955a7d766d95e63280fa26b157b784fb  templates/emdash_benchmark/scripts/emdash-canary.mts
fc9e704d5578399bd0326f39387e5b96e0f2c60d0b3d7e31c46073cf6e27c2ac  templates/emdash_benchmark/scripts/fixtures/emdash-canary-fake-codex.mjs
16b4d4494b63fecc9c32a3c8d727dfbe0d0413febc66cbcffd5aa3f955647ef0  templates/emdash_benchmark/scripts/verify-emdash-canary.mts
```

Exact-checkpoint focused evidence is green:

- `--canary-only`: clean locked install, template typecheck, existing mock
  containment/failure suite, real-driver fake orchestration, lease collision,
  exactly-one fake spawn, closed parent environment, dynamic receipt, and
  pre-/post-spawn failure tests;
- `--permission-probe-only`: live local `codex sandbox` strict-config,
  filesystem, command, and network checks, explicitly without a model/API
  request;
- `--adapter-only` and `--cli-only`: public-package/source replay and public
  physically mock-only CLI;
- dependency-free operator syntax, committed-snapshot fixture, exact ancestry,
  clean status, whitespace, credential-shape, and public-surface scans; and
- no root/template `node_modules` and no real authorization directory after
  validation. A deliberate invocation with an unreviewed ID exited `2` before
  source bootstrap, lease creation, or provider execution.

The earlier all-template registry validation remains applicable because the
subsequent changes did not alter any template manifest or registration entry;
the exact checkpoint's focused verifier nevertheless rechecks this template's
manifest and installed identity. CloserFans excludes these paths from ESLint,
so no lint pass is claimed. Long repository aggregates, cloud/controller/
database/API/MCP checks, Emdash aggregates, kernel/book checks, provider/model
execution, real lease/transcript creation, push, merge, deployment, release,
and cleanup remain omitted, not passed.

This checkpoint completes only the implementation authorized by the immutable
review. Roadmap accounting remains 35/41. It does not itself authorize the
exact ID or a provider call; a separate immutable review of these committed
bytes and current at-call no-model state remains mandatory.

### Final-review correction checkpoint

The first final code audit did not authorize a call. It found two narrow
requirements that the safe implementation had not yet made reviewable enough:
recognized pre-spawn gate failures returned only an exit diagnostic rather
than a privacy-minimized receipt, and the observed process-spawn-error branch
had no fake executable test. The existing exclusive lease and no-call behavior
were already correct; this was an evidence/diagnostic correction, not a trust-
boundary widening.

CloserFans correction
`4faef7832ae7ac2131fe1c12e50831084835f60f`, exact parent
`1abdfd8ee3711a3993fa0db573672ababee7e6d3`, and exact tree
`a5e72ddc8cc62f82087a444c7ec96edd46275d81` closes both findings. Exact updated
file hashes are:

```text
6761f9b22d0c4a41dfd08927e61ca824ddeaa740980fa52f89fce93a759968dd  templates/emdash_benchmark/scripts/emdash-canary-real.mts
0c28e98abbefd9e5160522680322c53cdb6f72d782d9af8fb7bbb6c1d542ab9f  templates/emdash_benchmark/scripts/emdash-canary.mts
47b8fa608ca98e9ec335ac8b63072a7ad20e49660eca095abf0f8f5884f8e32e  templates/emdash_benchmark/scripts/verify-emdash-canary.mts
```

Recognized CLI-version, login-category, model-cache, permission-probe, selected-
case, and authorization refusals now create a mode-`0600` minimized receipt in
an explicit mode-`0700` unused run root. It records only the normalized gate,
hashed authorization, exact non-secret source identity, expected public tuple,
`providerExecuted=false`, `spawned=false`, and unconditional contamination/
non-graduation/non-proof labels. Invalid authorization grammar and an already
existing caller path still fail before a run is accepted. Authorization
collision remains atomic and produces no second spawn.

The focused fake suite now also removes its direct fake executable after all
no-model preflights but before the leased spawn. The resulting canonical v2
receipt records `process-spawn-failure`, `spawned=false`, normalized
`spawnError`, and `providerExecuted=false`, while the lease remains consumed.
A separate real-member fake policy violation records a successful process
spawn and `providerExecuted=true`. Together with the retained nonzero,
timeout/overflow, malformed-stream, scope, replay, abstention, rejection, and
accepted paths, the receipt outcome partition is now directly covered.

The exact correction checkpoint passes the focused canary/clean-install/
typecheck suite and the live no-model permission/filesystem/command/network
probe. Formatting, whitespace, credential-shape, clean-status, no-root-or-
template-`node_modules`, and no-real-authorization-directory checks are green.
Its committed 19-entry template snapshot manifest is
`445f79b056fb29d3caee56049ae196e01acc4efc41c49bea9cca8b1501e8efce`.
Public adapter/CLI behavior and the root operator are unchanged from their
immediately preceding focused-green checkpoint. No model/provider, real lease
or transcript, push, merge, deployment, release, aggregate, or unrelated
surface occurred.

This correction remains implementation evidence only. A new immutable review
must bind exact `4faef78` bytes and current no-model state before selecting the
sole run root and authorizing the committed non-secret ID.

### Immutable corrected-driver review and sole Stage A authorization

Review date: 2026-08-11

Decision: approve exactly one local operator invocation after this behavior-
free review is checkpointed. The reviewed CloserFans source is clean commit
`4faef7832ae7ac2131fe1c12e50831084835f60f`, exact parent
`1abdfd8ee3711a3993fa0db573672ababee7e6d3`, exact tree
`a5e72ddc8cc62f82087a444c7ec96edd46275d81`, and 19-entry committed-template
manifest SHA-256
`445f79b056fb29d3caee56049ae196e01acc4efc41c49bea9cca8b1501e8efce`.
The reviewing Emdash plan parent is clean checkpoint
`6ab3aefe20382c6a9997c7fcd10a088efa1f2355`, tree
`99b5727b4dab6a80aea3ac92dfe15817fd5f1f66`.

The exact committed-file inventory is:

```text
e6e93778a0e021bed8074d888958070465f7bae724879871c6801a3a4288e2f9  AGENTS.md
cab4764e39e69c9eee7a177da539347f5a9f4a3693be816d3900d08580849db6  README.md
42325cdedd181f36e1e221c6eb9d6fd2aadf89c005b05b55b08cc7e00b6aee01  scripts/run-emdash-stage-a-real.mjs
de000ea8a72b9c2d1f482f5801159178677a3f3501925afadf582bfaca42808e  scripts/verify-emdash-benchmark-template-runtime.ts
b6d4eb040df34eab3864e1c3fad34f49cc0fcc5c669f8f797f0ff95a0e02875a  templates/emdash_benchmark/README.md
f89f208da92ac16e6835354bee273c5a365a7035a4831bb94a10a7f4eac3e8f1  templates/emdash_benchmark/scripts/emdash-canary-contract.mts
db599cd2e5dc70f34ff0e6c5c43a910cb003dc9d741d3b49942229dec9e3af88  templates/emdash_benchmark/scripts/emdash-canary-evaluate.mts
6761f9b22d0c4a41dfd08927e61ca824ddeaa740980fa52f89fce93a759968dd  templates/emdash_benchmark/scripts/emdash-canary-real.mts
0c28e98abbefd9e5160522680322c53cdb6f72d782d9af8fb7bbb6c1d542ab9f  templates/emdash_benchmark/scripts/emdash-canary.mts
fc9e704d5578399bd0326f39387e5b96e0f2c60d0b3d7e31c46073cf6e27c2ac  templates/emdash_benchmark/scripts/fixtures/emdash-canary-fake-codex.mjs
47b8fa608ca98e9ec335ac8b63072a7ad20e49660eca095abf0f8f5884f8e32e  templates/emdash_benchmark/scripts/verify-emdash-canary.mts
```

The remaining fixed source inputs are exact:

```text
0c104f3888c61ce669958c44051ea65a153d9fbaea3c9c37139e6325b310eb84  benchmark-run.emdash.ts
117768e52381ede1b23f3bf4c43064e526daa6a25f3d8d4b0c3c879ffd7574ed  emdash-canary-prompt.txt
f8935691d02f44d7c9b2d0ad1c96559c985c5596ecc210c3c03390a0680a8e06  emdash-canary-output.schema.json
523357c1109f62bd956d196c9a9280ea5313b5a264c0e080608e9c56b021caac  probe-emdash-canary-permissions.mts
1f9efb7b416b9ab162ddc98f14c2c4ade0a56ddcf2df5fb519f437031f9fccf8  emdash-canary-package-lock.json
```

The retained lock resolves exact `@hotdocx/emdash@0.3.0` with integrity
`sha512-ewAhab+tLMY0QZrOXLMSpH19VYkP73iR2iYxYRireYK+21QDOi9Cp/Tq4su+QI+b/NmYnUoZzGoEEQpBGJCxxg==`.
The package manifest has only `benchmark`, `canary:mock`,
`canary:probe-permissions`, `canary:verify`, `dev`, `start`, `typecheck`, and
`verify`; it has no real command.

Current no-model state is exact immediately before this decision:

- the CLI resolves through Node 24.11.1 and reports `codex-cli 0.147.0` in the
  same closed eight-key parent environment;
- `codex login status` in that closed environment reports exactly `Logged in
  using ChatGPT`; no account identifier or credential content/path was read,
  copied, hashed, or recorded;
- the selected local cache entry was fetched at
  `2026-08-11T19:11:24.621770496Z` and reports `gpt-5.6-sol`, `comp_hash=3000`,
  default low verbosity, and high reasoning support;
- the live no-model strict-config/filesystem/command/network probe is green;
  its script digest is recorded above and its expected result digest is
  `2ae19204681704e5dc5beca30d15b5abdfff52a920537042404d7e1d483c340c`;
- all focused fake orchestration, mock, clean-install/typecheck, public
  adapter/CLI, committed-snapshot, source/event/replay/receipt, timeout/
  overflow/refusal/policy/spawn-failure, credential-shape, whitespace,
  ancestry, and no-in-worktree-dependency-tree gates are green; and
- neither `~/.emdash-stage-a/authorizations/` nor the selected run root exists.

The exact non-secret authorization ID is
`emdash-stage-a-native-exact-local-premise-2026-08-11-v1`, SHA-256
`4c8dc99972629f7b0e0807aa9986111a5dc89bbd839129ffc060c53a1c4aba21`.
The sole run root is
`/home/user1/.emdash-stage-a/stage-a-native-exact-local-premise-2026-08-11-v1`,
SHA-256
`5690701f93e2ee10e953e3a645afdacf7d69206a6e5e208e3f2b2eb74d897361`.
Only the following command is authorized, once, from the clean reviewed
CloserFans worktree:

```bash
node scripts/run-emdash-stage-a-real.mjs \
  --authorization-id emdash-stage-a-native-exact-local-premise-2026-08-11-v1 \
  --run-root /home/user1/.emdash-stage-a/stage-a-native-exact-local-premise-2026-08-11-v1
```

This authorizes no substitute path, source, ID, case, model, provider, CLI
revision, credential form, permission profile, second process, retry,
fallback, recursion, or second turn. Invoke the operator at most once. If any
preflight refuses, stop even though no provider lease exists; do not select a
new run root or repeat the command without another immutable review. If a
provider spawn is attempted, its exclusive persistent lease consumes the ID
regardless of exec/transport failure, timeout/overflow, malformed output,
policy/source/replay failure, abstention, rejection, incompleteness, or
completion. Do not delete or rewrite the bootstrap, run root, private evidence,
or lease.

After that single invocation, inspect only the minimized receipt and canonical
artifacts needed to classify the outcome; keep raw JSONL, stderr, final model
message, candidate source/diff, and replay evidence private and untracked.
Synchronize both plans in a new rollback-safe checkpoint. The result remains
open-book and non-graduating under
`contamination=public-owner-reference-accessible`,
`graduationEligible=false`, and `proofEvidence=false`. It cannot support a
success-rate, leaderboard, representative-performance, solver-comparison, or
graduation claim. ChatGPT-authenticated dollar cost remains unknown/null.

No long aggregate is relevant or authorized. This decision uses the user's
standing unattended-approval delegation plus checkpointing/backtracking SOP;
the human may supersede it before execution. Roadmap accounting remains
35/41.

### Sole Stage A invocation outcome: terminal preflight refusal

The behavior-free authorization was checkpointed at Emdash commit
`4e3960024bad5607c139911189b1006eefa515c6`, exact tree
`e15c7e51f87999daa6ea3645f13ec21231c7bd03`. The exact reviewed operator
command was then invoked once from clean CloserFans commit `4faef78`. It
returned `preflight-refusal` and was not retried.

The only inspected run artifact is the minimized canonical receipt at the
reviewed run root. Its SHA-256 is
`cb02d5085f855e3a516f5c20f2b5593103b53c38824e5b85e99e530fda25edf3`.
It records:

```text
revision             getpaidx-emdash-stage-a-preflight-receipt-v1
operationalOutcome   preflight-refusal
preflight.failure    login-category
providerExecuted     false
process.spawned      false
benchmarkOutcome     null
valid                false
graduationEligible   false
proofEvidence        false
```

The receipt binds the expected authorization-ID hash, case, exact source
commit/tree, operator digest, and committed-template manifest. The run root,
private-evidence directory, and receipt retain modes `0700`, `0700`, and
`0600`. The real authorization directory remains absent, so no lease was
created. Nevertheless the plan-level one-operator-invocation authorization is
terminal: do not reuse the ID with another run root and do not retry this
command. The bootstrap, run root, and receipt remain preserved and unmodified.

No provider child spawned, no model ran, no real JSONL/final message/candidate
or replay transcript exists, no usage or cost was incurred or inferred, and
there is no mathematical, benchmark-performance, proof, or graduation result.
The earlier direct closed-environment status observation and this normalized
driver refusal are distinct facts; the receipt alone does not establish the
cause of the login-category mismatch. Any diagnosis must be separately no-
model, privacy-preserving, and behavior-free, followed by a new proposal,
implementation checkpoint, and immutable authorization with new coordinates
before another provider attempt.

Roadmap accounting remains 35/41. Push, merge, deployment, release, API/MCP,
controller, database, Emdash semantics, another template, Stage B/C, and long
aggregates remain untouched or omitted.

### `AGENT-EVAL-12B4-R1` No-model login-stream diagnosis and correction proposal

The terminal receipt made the next operation diagnostic rather than
provider-backed. A fresh, closed-environment, no-model process probe now
identifies the exact cause without reading credential content or preserved run
evidence:

```text
command              exit  stdout                  stderr
codex --version      0     codex-cli 0.147.0\n    empty
codex login status   0     empty                   Logged in using ChatGPT\n
```

The real driver used one stdout-only `expectText` helper for both commands and
therefore classified a valid real login as `login-category`. The tracked fake
executable wrote its login fixture to stdout, so its successful orchestration
test reproduced the driver's assumption rather than the CLI contract. The
preflight refusal was consequently correct relative to the implemented gate,
and its receipt/provenance remain valid; the mismatch is in the modeled stream
contract. No model/provider, auth-file read, lease, retry, or transcript was
involved in this diagnosis.

The smallest correction proposal is:

1. Replace the internal stdout-only helper with an exact channel-aware helper
   over the already bounded capture. Successful version, permission-probe, and
   selected-case commands require their expected text on stdout and empty
   stderr. Successful login status requires its expected category on stderr
   and empty stdout. A nonzero exit, timeout, selected-channel decoding error,
   unexpected other-channel bytes, or wrong exact text remains a normalized
   preflight refusal.
2. Make the tracked fake executable model `codex login status` on stderr,
   including wrong-category overrides. Do not add a provider selector,
   environment inheritance, credential fixture, fallback, compatibility
   acceptance of both channels, or output concatenation.
3. Extend the focused fake suite so the normal real-member path succeeds only
   with the stderr login contract and an explicitly stdout-emitting login
   fixture is rejected before authorization/spawn. Retain every existing
   refusal, lease, spawn-error, policy, receipt, environment, and replay test.
4. Rerun only formatting/diff/credential-shape checks, the focused canary/
   clean-install/typecheck suite, and the live no-model permission probe. The
   public adapter/operator/CLI behavior and package/template registry are
   unchanged; their immediately preceding focused-green evidence carries
   forward unless the exact diff reaches them.

Implementation may change only
`templates/emdash_benchmark/scripts/emdash-canary-real.mts`, the tracked fake
fixture, and `verify-emdash-canary.mts`, plus these plans. It may not edit the
operator, authorization ID, public package scripts, prompt/schema/case,
permission profile, evaluator, receipt semantics, Emdash, another template,
API/MCP/controller/cloud surfaces, or preserved Stage A evidence. The existing
ID/run root are retired and must never be reused or removed.

This proposal authorizes no code and no new call. Require a separate immutable
proposal review, focused-green implementation checkpoint, a new exact no-model
code/preflight review, and wholly new non-secret ID/run-root coordinates before
any later provider attempt. Accounting remains 35/41.

#### Immutable R1 proposal review

Review date: 2026-08-11

Reviewed proposal checkpoint:
`58ff9915252d503d215c458f73bb8ba7215b42bb`, exact parent
`208c109c5e3519cabc4218073edc06fe4e8da092`, exact tree
`bf1573e3fa4b735c6b5848a2b6b9f4ae40233451`. The proposal changes only the two
living plans. Their complete SHA-256 values are:

```text
a435395466ba4926c0c12282cb79d8c698035dee0bf64d256f291822bfc9c573  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
20ea665bea79ad123fd267226c77f12d76b1ee6a7507e08ef7a9c5f9186eac70  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
```

The diagnosis and correction are accepted with six binding conditions:

1. Use the existing bounded child capture; do not add another process,
   provider, retry, fallback, network, or credential surface.
2. Require exact version text on stdout with empty stderr, exact login category
   on stderr with empty stdout, and retain stdout-plus-empty-stderr for the
   permission and selected-case preflights. Never concatenate or accept both
   channels.
3. Decode only the selected bounded channel with fatal UTF-8 and normalize all
   other-channel/nonzero/timeout/text failures through the existing preflight-
   refusal receipt without copying raw diagnostics into it.
4. Change the fake login command to stderr and add a wrong-stream pre-spawn
   refusal fixture. Retain all existing successful, refusal, lease, spawn,
   policy, environment, replay, receipt, and public-mock tests.
5. Touch only the three proposed template script/test files plus later plan
   synchronization. The root operator, contract/authorization ID, package
   scripts, prompt/schema/source, permission profile, evaluator, other
   templates, Emdash, API/MCP/controller/cloud, and preserved run evidence
   remain byte-for-byte unchanged.
6. Run focused fake canary/clean-install/typecheck, live no-model permission,
   formatting/diff, credential-shape, exact scope, clean ancestry, no-
   dependency-tree, and no-real-lease checks. Do not run a provider or long
   aggregate.

Decision: approve only this local three-file implementation and fake/no-model
validation under the user's standing unattended delegation, with human
supersession. It authorizes no new ID/run root, operator invocation, provider/
model, lease/transcript, push, merge, deployment, release, cleanup, Stage B/C,
or performance/proof claim. After a focused-green code checkpoint,
synchronize both plans and perform a new exact code/preflight review before
even proposing new call coordinates. Accounting remains 35/41.

##### Post-review evaluator-launch amendment

The three authorized R1 edits were applied but remain uncommitted. Their first
focused canary run did not pass: the outer 120-second harness timed out. A
separate disposable clean install then isolated a faster deterministic failure
in the unchanged mock accepted case. Replaying its canonical selected attempt
under the exact private evaluator environment produced:

```text
Error: listen EINVAL: invalid argument
.../host-evaluator-tmp/tsx-1000/998122.pipe
```

The same evaluator and attempt succeed under a shorter temp path. The failure
is therefore not evaluator semantics, the login-stream correction, source
tampering, or provider behavior. `replayCandidate` launches the clean evaluator
through `node_modules/.bin/tsx`; that CLI creates an IPC Unix-domain socket
whose path can exceed the host limit when nested below the intentionally
private run root. The already qualified selected-case preflight instead uses
`process.execPath --import tsx` and needs no tsx CLI IPC socket.

The minimal amendment adds one production file to the R1 scope:

1. In `emdash-canary.mts`, launch only the clean evaluator as
   `process.execPath --import tsx <exact-evaluator-script> ...` from the same
   clean root and same closed evaluator environment. Keep all input/output
   paths, timeout/byte bounds, exit handling, clean-manifest comparison,
   canonical artifact checks, and evaluator source unchanged.
2. Do not shorten, relocate, symlink, delete, or weaken the private run/evidence
   boundary; do not widen PATH/environment or call the agent/provider.
3. Let the existing default-run-root mock suite act as the long-private-path
   regression, alongside the new login-channel tests. Re-run the focused
   canary/clean-install/typecheck and live no-model permission gates. Record
   the initial timeout and diagnostic fixture failure as failures, not passes.

The amended implementation scope is exactly four template files:
`emdash-canary-real.mts`, `emdash-canary.mts`, the tracked fake fixture, and
`verify-emdash-canary.mts`. The earlier three-file authorization does not by
itself authorize the fourth edit. This amendment changes plans only and
requires a separate immutable review before `emdash-canary.mts` is edited. It
selects no new call coordinates and authorizes no provider/model or external
effect. The disposable diagnostic tree was removed after the bounded evidence
above was recorded; preserved real Stage A evidence remains untouched.

###### Immutable evaluator-launch amendment review

Reviewed amendment checkpoint:
`3f5e428a0e7408e5919c91a1ba69596876b3b559`, exact parent
`dcfa9a76799487b44a5d2044dfffa30430e4efa9`, exact tree
`f227ed1adb7a468fee10be3066c02cd9182ddb06`. Complete plan SHA-256 values are:

```text
84c7371f1864bbed4f84d5b785081b3d5ededf318ee434ded3c478604e95291d  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
dc8265c92e77875890403e8b77bab3db05f13cc48a1beaea5aa82436135a1334  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
```

Review accepts the diagnosis and the single added production edit. Node
`--import tsx` executes the same exact evaluator module from the same clean
root, resolves the same installed dependency, and keeps the same attempt and
output arguments, cwd, inherit-nothing host evaluator environment, timeout,
byte bounds, exit classification, manifest comparison, summary parser, and
canonical-artifact digest checks. It removes only the tsx CLI's incidental IPC
server and does not weaken private path placement or evaluator authority. The
existing selected-case preflight is direct evidence that this launch form
works in the installed fixture.

Decision: expand the prior R1 implementation authority only to the exact four
template files named above. Require the default long-private-run-root suite to
pass without a special short `HOME`/`TMPDIR`; also rerun live no-model
permission, formatting/diff, scope/hash, credential-shape, no-dependency-tree,
and no-real-lease checks. Preserve and report the prior timeout and disposable
`EINVAL` run as diagnostic failures. No operator/contract/source/prompt/schema/
permission/evaluator/package/other-template/Emdash/external edit, new call
coordinate, provider/model, retry, lease, push, merge, deployment, release,
cleanup, or claim is authorized. Accounting remains 35/41.

###### Focused-verifier scheduling correction proposal

The approved four-file R1 implementation removes the evaluator IPC failure,
but the auditable default `--canary-only` run still did not pass: its outer
focused harness terminated `npm run canary:verify` at the existing 120-second
ceiling. Running that exact inner verifier from a disposable clean installed
template, without changing `HOME`, `TMPDIR`, the private default run roots, or
any code, passed every assertion in 133.41 seconds. This is positive semantic
evidence for the inner fake/no-model matrix, but it is not a pass for the
default outer gate. The old `EINVAL` no longer occurs.

The measured cost is the sequential ten-case mock matrix: each independent
case copies the same read-only preinstalled template into its own private
agent root and initializes its own audit repository. Increasing the outer
timeout would preserve a needlessly slow focused gate. Weakening clean-copy,
private-root, replay, or assertion coverage would weaken the reviewed
boundary. The narrow proposal instead changes only scheduling inside the
already scoped `verify-emdash-canary.mts`:

1. execute the same ten mock scenarios as five explicit two-case
   `Promise.all` batches;
2. preserve each scenario's existing options, hook, result binding, assertion,
   receipt checks, independently allocated run root, retained-root cleanup,
   and the sequential order between pairs;
3. leave `executeScenario`, `runStageACanary`, real-driver tests, evaluator,
   production files, limits, environment, and all source/evidence contracts
   unchanged; and
4. require both the direct inner verifier and the default outer
   `--canary-only` gate to pass, followed by the existing live no-model
   permission and static hygiene checks.

Pairwise concurrency is bounded at two and operates only on fake, isolated,
no-network cases. This proposal changes plans only. It does not authorize the
test edit until a separate immutable review, and it selects no new call
coordinate or provider/model effect. The discarded outer run and 133.41-second
direct pass remain recorded with their distinct meanings. Accounting remains
35/41.

###### Immutable focused-verifier scheduling review

Reviewed proposal checkpoint:
`2b2387734840a0429307a7573ad78f727d795187`, exact parent
`e1bae2126faf932b886caccdf18f54bc6c6cf711`, exact tree
`adc5a42b5531e02e2780e658f58da9d569ccc6dd`. Complete plan SHA-256 values are:

```text
91188bbca632a2e4b6cb8e5715527a90712e065cf7f4fc72fdeccd0c2fa5d6a3  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
e6f05a5ce8c94ff5b4238f5261065a3e97fcbd19338ebea2bb9b52a06500b923  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
```

The pre-edit verifier SHA-256 is
`aa386894e968d558c2fe5427b708025e5a9499ac2b6febcdc681b11a4b1fba50`.
Review confirms that all ten mock invocations allocate disjoint run,
workspace, fake-home/temp, evidence, and evaluator-output paths. They share
only the read-only installed template. `Promise.all` returns results in input
order, while the retained-root cleanup is already order-independent. The
tamper hook and timeout remain confined to their own roots. The real-driver
sequence, including its authorization-collision dependency, is outside the
proposed concurrency and remains sequential.

Decision: approve only replacement of the ten sequential invocations inside
`verifyMockRunner` by the five explicit pairs recorded above. Do not add a
general scheduler, exceed concurrency two, coalesce roots or cases, change any
scenario option/assertion/hook, or edit production/real-driver code. Require
the direct inner verifier and the unchanged outer `--canary-only` invocation
to pass under their existing bounds, then run the live no-model permission and
static hygiene checks. No new coordinates, operator call, provider/model,
lease/transcript, integration, publication, deployment, cleanup of preserved
evidence, or performance/proof claim is authorized. Accounting remains 35/41.

###### R1 implementation qualification checkpoint

CloserFans checkpoint `a6b5e61194551f2cf648226e7e86249eec670168`,
exact parent `4faef7832ae7ac2131fe1c12e50831084835f60f`, and exact
tree `fe50a80d4c1c8160a22050487189e5c71e03f969` contain the complete
four-file R1 correction. Committed file SHA-256 values are:

```text
6eea2a93d16a1c263ea17458969328535452490386ff6080a725eb6ad83f2e8e  templates/emdash_benchmark/scripts/emdash-canary-real.mts
2b7cb752a752faf5ed507d613982249f8253c64cb1dea75772aa146a54bb00d5  templates/emdash_benchmark/scripts/emdash-canary.mts
dcd1b53b9e95db4911e26400ba46ab9c1591a295e42def950e0bcf1087f238c7  templates/emdash_benchmark/scripts/fixtures/emdash-canary-fake-codex.mjs
37ba4d05b29ebb504b725322ee79ac90af0f3f62254f3a0f556d7841f32f8094  templates/emdash_benchmark/scripts/verify-emdash-canary.mts
```

The committed 19-entry template snapshot manifest is
`1d63cef9ed32398ecf768bdaeafc2a4668798d4ed1d83177877804e9a0c5f2e5`;
the unchanged committed operator is
`42325cdedd181f36e1e221c6eb9d6fd2aadf89c005b05b55b08cc7e00b6aee01`.
The direct fresh-installed inner verifier passes all cases in 101.43 seconds,
the unchanged outer `--canary-only` gate passes under its 120-second bound,
and the live permission/command probe passes without a model. Formatting,
exact four-file scope, full staged review, diff/whitespace hygiene, credential-
shape scan, ancestry, clean worktree, absent contributor/template dependency
trees, absent real authorization lease, and the preserved receipt hash
`cb02d5085f855e3a516f5c20f2b5593103b53c38824e5b85e99e530fda25edf3`
are green.

The evidence history remains explicit: the first R1 outer run timed out; its
disposable accepted-case diagnosis exposed the tsx CLI `EINVAL`; the amended
sequential inner matrix later passed in 133.41 seconds but its outer gate still
expired at 120 seconds; bounded pairwise scheduling then made both exact gates
green. None of those fake/no-model runs contacted a provider. One mistakenly
created generated worktree-root dependency tree during disposable setup was
removed exactly; no tracked file changed and final no-tree checks pass.

This checkpoint authorizes only a new immutable code/preflight review. It does
not revive the consumed authorization, select new coordinates, or authorize
an operator/provider/model call, lease, transcript, retry, push, merge,
deployment, release, Stage B/C, or performance/proof claim. Accounting remains
35/41.

##### `AGENT-EVAL-12B4-R2` consumed-ID rotation proposal

The first behavior-free review against clean `a6b5e61` did not authorize a
call. Its closed eight-key parent environment is otherwise exact: version is
`codex-cli 0.147.0` on stdout with empty stderr; login is exactly `Logged in
using ChatGPT` on stderr with empty stdout; the selected cache entry was
fetched at `2026-08-11T20:00:03.264061398Z` and remains
`gpt-5.6-sol`/`comp_hash=3000`/default-low/high-supported; and the freshly
repeated live no-model permission/command/network probe passes. No credential
content, model, provider, lease, or new run root was accessed or created.

The review instead found an intentional closed-world incompatibility. Both
`scripts/run-emdash-stage-a-real.mjs` and
`emdash-canary-contract.mts` still accept only the now-consumed
`emdash-stage-a-native-exact-local-premise-2026-08-11-v1`. Reusing that ID is
forbidden even though its first invocation stopped before the provider lease;
passing a new ID would correctly be rejected by both guards. Final review
cannot select new coordinates until the committed allowlist is rotated.

The minimal R2 proposal is:

1. replace the exact v1 literal by
   `emdash-stage-a-native-exact-local-premise-2026-08-11-v2` in only the
   dependency-free root operator and the internal contract;
2. extend only `scripts/verify-emdash-benchmark-template-runtime.ts` to assert
   that both committed sources contain the same exact v2 literal and no longer
   contain the retired v1 literal;
3. retain the one-value grammar, exclusive non-deletable lease, unused-absolute-
   root requirement, no-loop/no-retry behavior, fake-only public commands,
   committed-byte bootstrap, closed environments, all preflight gates, private
   evidence, and every contamination/non-graduation/non-proof label; and
4. run the focused outer canary, live no-model permission probe, snapshot/
   static/typecheck coverage, formatting/diff/credential-shape, exact scope,
   ancestry, no-dependency-tree, no-old/new-lease, and preserved-v1-receipt
   checks before checkpointing.

The old ID remains durable historical evidence and becomes unrepresentable at
both execution guards; its preserved run/receipt is not removed or rewritten.
The new ID is a candidate code allowlist value, not an authorization. This
proposal changes plans only and requires separate immutable review before the
three local files are edited. A focused-green implementation checkpoint and
another fresh behavior-free review must bind an absent absolute run root and
all at-call state before at most one invocation. No call, retry, provider/
model, push, merge, deployment, release, or claim is authorized. Accounting
remains 35/41.

###### Immutable consumed-ID rotation review

Reviewed proposal checkpoint:
`a92c16c348bce39996a735b30e7d31720ef8e0eb`, exact parent
`2fbd606c2c1cd4494307842f0856e341b037f9a2`, exact tree
`b4644f85577d5aba9a46fc27c67ac921fbdb3b82`. Complete plan SHA-256 values are:

```text
cdbe068548bec4b16a657962010c8f78043e47d4c7085114c97fbb685ec7820e  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
26087cdc14111a80d7de99c972b2610b60e4b52a4e31615a350e6480fa37c92e  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
```

Review accepts exact v2 as a code-level one-shot allowlist candidate, not a
call authorization. The root operator must retain a literal because it is a
dependency-free bootstrap over committed bytes; the internal contract must
retain the same literal because it closes the TypeScript driver. Rotating both
is narrower than accepting arbitrary CLI input, parameterizing the allowlist,
reusing v1, weakening the guard, or adding a retry registry. The root verifier
is the existing owner for static agreement between bootstrap and template
contracts.

Decision: authorize only these three local edits:

1. replace the v1 literal by exact v2 in
   `scripts/run-emdash-stage-a-real.mjs`;
2. replace the same literal in
   `templates/emdash_benchmark/scripts/emdash-canary-contract.mts`; and
3. make `scripts/verify-emdash-benchmark-template-runtime.ts` require exact v2
   in both sources and reject v1 in both sources.

Do not change argument grammar, lease naming/creation, run-root handling,
process count, environment, preflights, provider arguments, evidence,
receipts, template source/case/prompt/schema/lock, or public commands. Require
focused outer canary and permission-probe modes, their included clean install/
typecheck/snapshot/static checks, formatting, exact scope, credential-shape,
diff/ancestry, no dependency tree, no v1/v2 lease, absent candidate run root,
and preserved v1 receipt. After a focused-green checkpoint, synchronize both
plans and repeat the behavior-free at-call review. No operator invocation,
provider/model, push, merge, deployment, release, Stage B/C, or claim is
authorized. Accounting remains 35/41.

###### R2 implementation qualification checkpoint

CloserFans checkpoint `8276e962ea0d5e2f1fa4e87c79357f38cdd03321`, exact
parent `a6b5e61194551f2cf648226e7e86249eec670168`, and exact tree
`e03085a472aee51b2b934a9c71b8db7320cb9998` implement only the reviewed
three-file rotation. Committed file SHA-256 values are:

```text
e3c205ecd3b10b380710295b20471992381741d1c16cc76cc6d835c4386655c6  scripts/run-emdash-stage-a-real.mjs
b615654019cdbd6f364132dc74b72501ec6058dcabe3020cb7ccb91e14348557  scripts/verify-emdash-benchmark-template-runtime.ts
4923b93b08af3279443df640e73706a29e3a83c2bd614a16bad413bf759e1271  templates/emdash_benchmark/scripts/emdash-canary-contract.mts
```

The new committed 19-entry template snapshot manifest is
`28c06be7b4feeb8077237e82b4524b00f6f88cf5bf40f22d72c0305380dadb82`.
Exact v2 hashes to
`aff872d7aa486ab1fb21a73bb514b73218f033f3b2184137969c2000cdccab58`;
retired v1 remains
`4c8dc99972629f7b0e0807aa9986111a5dc89bbd839129ffc060c53a1c4aba21`.

The focused outer canary passes under its existing bound, including clean
install, typecheck, static v2-equality/v1-retirement checks, committed-snapshot
coverage, all fake orchestration and real-driver-without-provider tests, and
public mock CLI smoke. The live no-model permission/command/network probe also
passes. Formatting, exact three-file scope, full staged review, diff/
whitespace hygiene, credential-shape scan, ancestry, clean worktree, absent
contributor/template dependency trees, absent v1/v2 leases, absent candidate
v2 run root, and unchanged preserved v1 receipt SHA-256
`cb02d5085f855e3a516f5c20f2b5593103b53c38824e5b85e99e530fda25edf3`
are green.

No provider/model, real lease/transcript, push, merge, deployment, release, or
long aggregate occurred. This checkpoint makes v2 representable but does not
authorize its use. A new immutable at-call review must recheck exact source,
manifest/operator/input hashes, current no-model host state, absent v2 lease
and absolute run root, and then checkpoint the sole command before at most one
invocation. Accounting remains 35/41.

### Immutable v2 at-call review and sole Stage A authorization

Review date: 2026-08-11

Decision: approve exactly one local operator invocation after this behavior-
free review is checkpointed. The reviewed CloserFans source is clean commit
`8276e962ea0d5e2f1fa4e87c79357f38cdd03321`, exact parent
`a6b5e61194551f2cf648226e7e86249eec670168`, exact tree
`e03085a472aee51b2b934a9c71b8db7320cb9998`, and 19-entry committed-template
manifest SHA-256
`28c06be7b4feeb8077237e82b4524b00f6f88cf5bf40f22d72c0305380dadb82`.
The reviewing Emdash plan parent is clean checkpoint
`aa6a105634f4caaf31570cc480b9c3fd302ac78d`, tree
`2b28d606873371fa81610a26c6f2269cb00d21d8`, with dedicated/governing plan
SHA-256 values
`3513c812552c78bf2311deb05b5067838ed5a578297bd5ad1b45c06e7aac06ad` and
`5c8a0a4611333185a3478f33b84915a2beeb64cd1d5843041c3cd820b984e16f`.

The exact committed-file inventory is:

```text
e6e93778a0e021bed8074d888958070465f7bae724879871c6801a3a4288e2f9  AGENTS.md
cab4764e39e69c9eee7a177da539347f5a9f4a3693be816d3900d08580849db6  README.md
e3c205ecd3b10b380710295b20471992381741d1c16cc76cc6d835c4386655c6  scripts/run-emdash-stage-a-real.mjs
b615654019cdbd6f364132dc74b72501ec6058dcabe3020cb7ccb91e14348557  scripts/verify-emdash-benchmark-template-runtime.ts
b6d4eb040df34eab3864e1c3fad34f49cc0fcc5c669f8f797f0ff95a0e02875a  templates/emdash_benchmark/README.md
4923b93b08af3279443df640e73706a29e3a83c2bd614a16bad413bf759e1271  templates/emdash_benchmark/scripts/emdash-canary-contract.mts
db599cd2e5dc70f34ff0e6c5c43a910cb003dc9d741d3b49942229dec9e3af88  templates/emdash_benchmark/scripts/emdash-canary-evaluate.mts
6eea2a93d16a1c263ea17458969328535452490386ff6080a725eb6ad83f2e8e  templates/emdash_benchmark/scripts/emdash-canary-real.mts
2b7cb752a752faf5ed507d613982249f8253c64cb1dea75772aa146a54bb00d5  templates/emdash_benchmark/scripts/emdash-canary.mts
dcd1b53b9e95db4911e26400ba46ab9c1591a295e42def950e0bcf1087f238c7  templates/emdash_benchmark/scripts/fixtures/emdash-canary-fake-codex.mjs
37ba4d05b29ebb504b725322ee79ac90af0f3f62254f3a0f556d7841f32f8094  templates/emdash_benchmark/scripts/verify-emdash-canary.mts
```

The remaining fixed source inputs are exact:

```text
0c104f3888c61ce669958c44051ea65a153d9fbaea3c9c37139e6325b310eb84  benchmark-run.emdash.ts
117768e52381ede1b23f3bf4c43064e526daa6a25f3d8d4b0c3c879ffd7574ed  emdash-canary-prompt.txt
f8935691d02f44d7c9b2d0ad1c96559c985c5596ecc210c3c03390a0680a8e06  emdash-canary-output.schema.json
523357c1109f62bd956d196c9a9280ea5313b5a264c0e080608e9c56b021caac  probe-emdash-canary-permissions.mts
1f9efb7b416b9ab162ddc98f14c2c4ade0a56ddcf2df5fb519f437031f9fccf8  emdash-canary-package-lock.json
```

The retained lock still resolves exact `@hotdocx/emdash@0.3.0` with integrity
`sha512-ewAhab+tLMY0QZrOXLMSpH19VYkP73iR2iYxYRireYK+21QDOi9Cp/Tq4su+QI+b/NmYnUoZzGoEEQpBGJCxxg==`.
The package manifest still exposes only `benchmark`, `canary:mock`,
`canary:probe-permissions`, `canary:verify`, `dev`, `start`, `typecheck`, and
`verify`; it exposes no real command.

Current no-model state is exact immediately before this decision:

- the CLI resolves through Node 24.11.1 and reports `codex-cli 0.147.0` only on
  stdout in the same closed eight-key parent environment;
- `codex login status` reports exactly `Logged in using ChatGPT` only on
  stderr; no account identifier or credential content/path was read, copied,
  hashed, or recorded;
- the selected local cache entry was fetched at
  `2026-08-11T20:11:33.210101020Z` and reports `gpt-5.6-sol`,
  `comp_hash=3000`, default low verbosity, and high reasoning support;
- the freshly repeated live no-model strict-config/filesystem/command/network
  probe is green, with script digest recorded above and expected result digest
  `2ae19204681704e5dc5beca30d15b5abdfff52a920537042404d7e1d483c340c`;
- focused outer canary, clean-install/typecheck, committed snapshot, static v2/
  retired-v1, all fake/real-without-provider, public mock CLI, formatting,
  credential-shape, exact scope, whitespace, ancestry, clean-source, and no-
  dependency-tree gates are green; the unrelated original CloserFans untracked
  template remains preserved and outside this clean worktree; and
- neither the v2 authorization lease nor the selected absolute run root
  exists; the v1 receipt remains byte-identical at SHA-256
  `cb02d5085f855e3a516f5c20f2b5593103b53c38824e5b85e99e530fda25edf3`
  with modes `0700`/`0700`/`0600` and no v1 lease.

The exact non-secret authorization ID is
`emdash-stage-a-native-exact-local-premise-2026-08-11-v2`, SHA-256
`aff872d7aa486ab1fb21a73bb514b73218f033f3b2184137969c2000cdccab58`.
The sole run root is
`/home/user1/.emdash-stage-a/stage-a-native-exact-local-premise-2026-08-11-v2`,
SHA-256
`0359aa03bb162feccb2389e18cd6688b84b4332e257ee0e110136e05bb65ee18`.
Only the following command is authorized, once, from the clean reviewed
CloserFans worktree:

```bash
node scripts/run-emdash-stage-a-real.mjs \
  --authorization-id emdash-stage-a-native-exact-local-premise-2026-08-11-v2 \
  --run-root /home/user1/.emdash-stage-a/stage-a-native-exact-local-premise-2026-08-11-v2
```

This authorizes no substitute path, source, ID, case, model, provider, CLI
revision, credential form, permission profile, second process, retry,
fallback, recursion, or second turn. Invoke the operator at most once. Every
preflight refusal terminates the authorization even if no lease exists. Any
provider-spawn attempt consumes the exclusive persistent v2 lease regardless
of exec/transport failure, timeout/overflow, malformed output, policy/source/
replay failure, abstention, rejection, incompleteness, or completion. Do not
delete or rewrite either bootstrap, run root, private evidence, or lease.

After the single invocation, inspect only the minimized receipt and canonical
artifacts needed to classify the outcome; keep raw JSONL, stderr, final model
message, candidate source/diff, and replay evidence private and untracked.
Synchronize both plans in a new rollback-safe checkpoint. The result remains
open-book and non-graduating under
`contamination=public-owner-reference-accessible`,
`graduationEligible=false`, and `proofEvidence=false`. It cannot support a
success-rate, leaderboard, representative-performance, solver-comparison, or
graduation claim. ChatGPT-authenticated dollar cost remains unknown/null.

No long aggregate is relevant or authorized. This decision uses the user's
standing unattended-approval delegation plus checkpoint/backtracking SOP; the
human may supersede it before execution. Roadmap accounting remains 35/41.

### Terminal v2 operator result: spawned process failure

Authorization checkpoint `bf94f6b2293496244651393873a1b846eb77bdb6`, exact
parent `aa6a105634f4caaf31570cc480b9c3fd302ac78d`, exact tree
`bf115d4b307bb861737af36f5220cce630218154`, checkpointed the sole command.
The exact operator command was then invoked once from clean CloserFans
`8276e96`. It returned `process-failure` and was not retried.

The minimized canonical receipt is preserved at the reviewed run root with
SHA-256
`c97c1f87e5734e03c0fa6e69a98b4cb162cd9bff9e9951112809a54c4ba251f1`.
The persistent v2 lease has SHA-256
`6dce7e86044eddbf0602dd0a3f95ea18c49cde5d1a82c4fcada05186a3f516eb`.
Run/evidence/receipt/lease modes are `0700`/`0700`/`0600`/`0600`; both objects
bind exact ID/run-root/source/tree/template/operator/argument hashes and remain
preserved.

The receipt records:

```text
revision             getpaidx-emdash-stage-a-receipt-v2
caseId               native.exact.local-premise
operationalOutcome   process-failure
benchmarkOutcome     null
valid                false
providerExecuted     true
spawned              true
exitCode             1
durationMs           95
timedOut             false
overflow             null
signal               null
spawnError           null
stream failure       incomplete-stream
command count        0
file-change events   0
final-message valid  false
usage                 null
graduationEligible   false
proofEvidence        false
```

The source remained unchanged, its audit and clean-authority checks passed,
and no forbidden command/file surface was observed. The canonical attempt,
run, and report were independently hashed, but the benchmark outcome is null.
The receipt's `providerExecuted=true` is the conservative classification for a
successfully spawned real Codex child. The 95-millisecond process failure does
not establish whether a remote model request began or completed; it establishes
only that no valid event stream/final message, usage record, candidate change,
or benchmark result was produced. Dollar cost therefore remains unknown/null.

The v2 authorization and command are terminal. Do not reuse the ID, replace
the run root, remove/rewrite the lease or evidence, inspect raw JSONL/stderr/
model-message/candidate/replay files, or retry. A later diagnosis must be
separately planned and no-model, using committed code, CLI help/config probes,
and minimized receipt facts rather than the private raw transcript. No proof,
mathematical result, performance result, success-rate, leaderboard,
solver-comparison, or graduation claim exists. Accounting remains 35/41.

##### `AGENT-EVAL-12B4-R3` no-model process-start diagnosis proposal

Official OpenAI documentation describes `codex exec` as the non-interactive
automation surface, `--json` as newline-delimited event output,
`--ignore-user-config` as retaining `CODEX_HOME` authentication, and
`codex doctor --json` as a redacted machine-readable diagnostic report. Those
documented/local-help contracts match the intended runner architecture, but
the existing live probe validated only the complete global config stack plus
`exec --help`; it did not separately parse every post-`exec` option, load the
real schema, or audit redacted runtime/provider health.

The minimized receipt bounds the diagnostic problem without revealing raw
evidence: the host spawned Codex successfully; the process exited 1 in 95 ms;
no timeout, overflow, signal, spawn error, command, file change, valid final
message, usage, or benchmark outcome exists; and the event parser saw only an
incomplete stream. Plausible pre-turn boundaries are therefore post-`exec`
argument/schema/path validation, ignored-versus-effective config/feature
state, selected-model/provider availability, or authentication/runtime health.
No one cause is asserted yet.

The proposed R3 audit is read-only/no-model except for disposable private test
paths and may:

1. run the exact committed global arguments followed by every reviewed
   post-`exec` option and `--help`, with no prompt, to validate the complete
   parser boundary;
2. run `codex doctor --json` in a fresh closed environment and retain/output
   only redacted aggregate/check classifications needed for diagnosis;
3. inspect `codex features list`, `codex debug models --bundled`, and the
   already whitelisted current cache entry, retaining only the selected model
   and named disabled-feature facts;
4. parse and structurally audit the committed output schema, prompt/case/input
   paths, directory modes, Git status, and exact argument vector without
   opening any v2 raw evidence file; and
5. compare the results with official command/config references and local
   `--help`, then record either one measured correction proposal or an honest
   unresolved boundary.

The audit may create and remove only explicitly validated disposable `/tmp`
directories. It must not invoke `codex exec` with a prompt, use the consumed
ID/run root, remove or inspect private v1/v2 evidence, read credential content,
alter login/config, contact a model/provider, retry, edit code, or change any
external/repository state beyond plan checkpoints. This proposal changes plans
only and requires a separate immutable review before probes. Accounting
remains 35/41.

###### Immutable R3 no-model diagnosis review

Reviewed proposal checkpoint:
`de1f00ebb47585e741137fb412bd250f48a4c69e`, exact parent
`8055eb35b4db098da3d41c71ba2f453133867352`, exact tree
`f5a1772ce6cd237bcf5e074ad3949aef2f80c2f3`. Complete plan SHA-256 values are:

```text
81a25370fd9883f29bf33008948842cf70a530012c6e83e2a86669259ade2c7b  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
7f2132f108256bb7a08be1ddd5c678dfc3929f603f678baa06a0118794ce3388  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
```

Review checked the current local help against the official
[Codex developer-command reference](https://developers.openai.com/codex/cli/reference).
The selected probes are supported read-only/non-interactive surfaces:
`exec --help` parses options without a prompt; `doctor --json` is documented as
a redacted diagnostic report; `features list` is read-only; and
`debug models --bundled` explicitly avoids catalog refresh. None constitutes a
proof-agent attempt or consumes the v2 lease again.

Decision: approve only the R3 audit exactly as proposed, with these controls:

1. build arguments from committed `8276e96` bytes in one disposable clean
   template and compare their SHA-256 to receipt-bound
   `cdca618e4eed081e622b1a3e7fef17be23d5d0d04e32dce85bae6268ad3a4592`;
2. replace only the terminal stdin prompt marker with `--help`, retaining every
   preceding global and post-`exec` option, and require zero input/model access;
3. invoke redacted doctor, feature-list, and bundled-model commands only in a
   closed environment; whitelist reported fields before recording them and do
   not retain full diagnostics;
4. read only committed source/schema/prompt/case metadata and ordinary host
   path/mode/Git facts, never any private evidence file; and
5. remove only the validated disposable directory, then synchronize one
   measured diagnosis or unresolved result in both plans.

Do not invoke `codex exec` with a prompt, read raw v1/v2 evidence or credentials,
alter config/login, use a network-refreshing model command, retry, create a new
authorization coordinate, edit code, or mutate external state. A diagnosed
correction requires a later proposal and review. Accounting remains 35/41.

###### R3 measured diagnosis: parser and host health green; turn-start boundary unresolved

The approved R3 audit completed without a prompt, model turn, retry, code edit,
or access to the private v1/v2 evidence. It reconstructed one clean disposable
copy from exact committed CloserFans checkpoint `8276e96`. The installed
manifest contained 19 entries and matched expected SHA-256
`28c06be7b4feeb8077237e82b4524b00f6f88cf5bf40f22d72c0305380dadb82`.
The reconstructed 69-entry argument vector placed `exec` at index 59 and
matched receipt-bound SHA-256
`cdca618e4eed081e622b1a3e7fef17be23d5d0d04e32dce85bae6268ad3a4592`.
Replacing only the terminal stdin marker with `--help` returned zero, printed
the expected usage, and left stderr empty. The complete reviewed global and
post-`exec` parser boundary is therefore green; this does not exercise schema
submission or start a turn.

The whitelisted `codex doctor --json` projection returned zero with overall
status `ok`, Codex `0.147.0`, and `ok` classifications for installation,
configuration loading, auth credentials, runtime, system, state, Git,
sandbox, terminal, MCP, app-server, updates, network environment, provider
reachability, and WebSocket reachability. The command's documented health
checks did contact provider/WebSocket health endpoints; they did not submit a
prompt or request a model completion. No full diagnostic report is retained.
The first `features list` projection returned one only because that command
does not accept the global `--strict-config` option. Removing only that
unsupported diagnostic option returned zero and confirmed `hooks`, `plugins`,
`remote_plugin`, `plugin_sharing`, `recommended_plugins`, `skill_search`,
`skill_mcp_dependency_install`, and `multi_agent` disabled. This limitation of
the diagnostic subcommand is not evidence about `exec`. Bundled-model
inspection returned zero, parsed as JSON, selected `gpt-5.6-sol` with
composition hash `3000`, default effort `low`, and `high` effort support, and
did not refresh the model catalog.

Committed input and path checks also passed. The 421-byte output schema has
SHA-256 `f8935691d02f44d7c9b2d0ad1c96559c985c5596ecc210c3c03390a0680a8e06`;
the prompt and source hashes remain respectively
`117768e52381ede1b23f3bf4c43064e526daa6a25f3d8d4b0c3c879ffd7574ed` and
`0c104f3888c61ce669958c44051ea65a153d9fbaea3c9c37139e6325b310eb84`
as recorded by the terminal receipt audit. The private schema copy was mode
0600; the agent workspace, private evidence, and
provider temporary directory were mode 0700; and the clean agent workspace
had empty Git status. JSON parsing and structural inspection establish an
object root, exactly three required properties, and
`additionalProperties: false`.

The official
[Structured Outputs guide](https://developers.openai.com/api/docs/guides/structured-outputs)
requires an object root, every property in `required`, and
`additionalProperties: false`; it documents enums and ordinary-model string
length constraints, and the committed schema satisfies those requirements.
The guide does not explicitly specify whether a top-level `$schema` annotation
or a property expressed solely with `const` belongs to the supported subset.
The installed CLI's local contract establishes that `--output-schema` reads
and JSON-parses a file, but exposes no no-model command that validates the
remote Structured Outputs subset. An auxiliary read-only inspection of the
installed npm wrapper/native string inventory after the documentation lookup
found only local read/JSON error surfaces and did not inspect configuration,
credentials, or run evidence. It was not one of the named R3 projections, so
it is recorded as a non-authorizing observation and is not used to claim a
cause.

R3 therefore rejects several broad hypotheses but does **not** prove the root
cause. Full argument parsing, ordinary committed paths, selected bundled
model, disabled optional features, redacted auth/runtime health, and the
documented portions of the schema are green. The remaining measured boundary
is schema submission or subsequent remote turn initialization. The 95 ms
terminal receipt still cannot prove whether a remote request began, and raw
stderr/JSONL remains intentionally uninspected. The safest next experiment is
a separately proposed, fake/no-model-tested normalization of the schema to
only the guide's explicit example forms; that would be a compatibility
hardening experiment, not proof that the original schema caused v2. No code
edit, new coordinate, provider call, retry, benchmark result, or graduation
is authorized by this diagnosis. Accounting remains 35/41.

The disposable directory was under the validated prefix
`/tmp/emdash-r3-diagnosis.*`. A subsequent host shutdown cleared `/tmp`; on
recovery the exact path was absent. No bootstrap, run root, lease, or private
evidence was removed or changed.

##### `AGENT-EVAL-12B4-R4` documented-subset schema normalization proposal

R3 does not justify changing authentication, model selection, process
environment, permission policy, prompt, proof source, or stream handling. It
does justify one smaller compatibility experiment: express the existing final
message contract using only schema forms shown explicitly in the official
Structured Outputs examples. This proposal is based on clean CloserFans
checkpoint `8276e962ea0d5e2f1fa4e87c79357f38cdd03321`, tree
`e03085a472aee51b2b934a9c71b8db7320cb9998`.

The proposed implementation changes exactly three files under
`templates/emdash_benchmark/scripts/`:

1. `emdash-canary-output.schema.json` removes the top-level `$schema`
   annotation, represents `caseId` as
   `{"type":"string","enum":["native.exact.local-premise"]}`, and adds
   `"type":"string"` beside the existing `disposition` enum. The `note`
   string/240-character bound, exact three-property `required` list, object
   root, and `additionalProperties: false` remain unchanged.
2. `fixtures/emdash-canary-fake-codex.mjs` validates the exact normalized
   schema rather than looking only for the former `caseId.const` value. This
   keeps the fake process aligned with the real invocation contract and makes
   accidental reintroduction of unstated keywords fail locally.
3. `verify-emdash-canary.mts` reads the committed schema and asserts the exact
   normalized object before running the existing fake scenarios. The test
   must reject the old `$schema` and `const` shapes by exact deep equality,
   while leaving final-message validation unchanged.

This is syntax-level compatibility hardening, not a semantic relaxation:
`caseId` still has one possible value, `disposition` still has the same three
values, `note` has the same type and bound, all three fields remain mandatory,
and extra properties remain forbidden. No Core, checker, proof source,
benchmark case, evaluator, receipt, contamination label, or trust boundary
changes. The public mock command remains physically fake, and the real driver
continues to copy committed bytes without gaining authorization.

Validation is proportional and entirely fake/no-model: JSON parsing plus the
new exact schema assertion, JavaScript syntax check for the fake fixture,
TypeScript formatting/static checks for the three paths, the focused Stage A
mock canary through its existing bounded scheduler, exact diff/ancestry/status
inspection, and confirmation that neither a new run root nor authorization
lease was created. Permission, root TypeScript, package, browser, kernel,
book, repository-wide, deployment, and release aggregates are unchanged and
must not be rerun.

This proposal authorizes no edit until a separate immutable review. Even after
implementation and fake/no-model validation, it authorizes no prompt, model,
provider, raw-evidence access, retry, v1/v2 mutation, new ID/run root, lease,
performance claim, benchmark result, or graduation. A later code/preflight
review would be required before even proposing fresh coordinates. Accounting
remains 35/41.

###### Immutable R4 schema-normalization review

Reviewed proposal checkpoint:
`685ce818c15d9d582e880163ad23147a121f3781`, exact parent
`d62a375ac2637241f224304c6feb9391bef88ac9`, exact tree
`69ab5e849197fc0e8d06ed802751504322305689`. Complete plan SHA-256 values are:

```text
135ed479a231f020b6f617f0005d4e8c0ae594369e7499fa2f0ce7eeee3a346a  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
6c8a0e5d466c4ef45114beb768cb25bf590875c535fc52ddd59e363c3ca3b356  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
```

The proposal preserves the accepted JSON-instance language: a single-value
typed enum is extensionally equal to the former string `const`, adding an
explicit string type to a string-valued enum rejects no intended disposition,
and `$schema` is an annotation rather than an instance constraint. The result
matches the object, typed-enum, required-field, closed-property, and string
bound forms explicitly shown by the official
[Structured Outputs guide](https://developers.openai.com/api/docs/guides/structured-outputs).
It neither claims that v2 failed because of the old form nor broadens the
benchmark output.

Decision: approve only the three-file R4 implementation from exact CloserFans
checkpoint/tree `8276e962...`/`e03085a...`, with these controls:

1. commit the exact normalized schema described above; do not change the
   prompt, source, case, output values, note bound, required list, or closed
   object policy;
2. use structural deep equality in both the fake consumer and focused verifier
   so JSON member ordering does not become a hidden contract;
3. keep the fake fixture dependency-free except for Node built-ins, and run
   schema verification before any fake scenario executes;
4. do not edit `emdash-canary-real.mts`, `emdash-canary-contract.mts`, the root
   operator, authorization constants, environment/sandbox policy, receipt
   logic, or any v1/v2 artifact; and
5. run only syntax/format/static checks and the existing bounded fake Stage A
   canary, then inspect exact source/ancestry/status and absence of new
   authorization/run state. No permission or repository aggregate is needed
   because those boundaries are unchanged.

The implementation checkpoint remains non-authorizing. Do not invoke a
prompt/model/provider, inspect raw evidence, retry v1/v2, mint a new ID/root,
create a real lease, or make a benchmark/performance/graduation claim. A
separate exact code/preflight review remains mandatory before new coordinates
may even be proposed. Accounting remains 35/41.

###### R4 implementation checkpoint and focused validation

The exact reviewed implementation is committed on the isolated CloserFans
branch as `1307f249df784107a260fb2461719f93f2467fb5`, parent
`8276e962ea0d5e2f1fa4e87c79357f38cdd03321`, tree
`863db44af8a1d774fa1cac7839efd6babbebe4dc`. Its staged and committed diff
contains only the three authorized paths, with 41 insertions and 5 deletions.
The normalized schema is 409 bytes with SHA-256
`a33c63dccf3a687484358b326dfbf41d1d668ad0fe1c7025b6b3c6aedf8f0978`.
It has no `$schema` or `const`, uses the exact typed single-value `caseId` enum
and typed three-value `disposition` enum, and retains the note bound, required
list, and closed object.

The fake fixture and verifier independently use Node strict structural deep
equality over that complete shape. The verifier performs its schema check
before any fake scenario. The real driver, shared invocation contract, root
operator, prompt, proof source, authorization constants, permission profile,
receipt code, and terminal evidence did not change.

Focused validation is green:

1. JSON parse/static shape, `node --check` for the fake fixture, and
   `git diff --check` passed.
2. `node --experimental-strip-types
   scripts/verify-emdash-benchmark-template-runtime.ts --canary-only` exited
   zero. Its disposable clean `npm ci` preserved the retained lock, template
   typecheck passed, the complete bounded fake scenario matrix passed through
   the existing two-wide scheduler, the new schema assertions passed in both
   verifier and fake process, and the public abstaining mock CLI passed.
3. The verifier removed its disposable benchmark/CLI roots. The CloserFans
   worktree has no root or template `node_modules`; no matching temporary
   prefix remained.
4. Only the existing v2 authorization lease is present. Receipt/lease hashes
   remain v1 `cb02d508...`, v2 `c97c1f87...`, and lease `6dce7e860...` exactly
   as recorded; no new run root, ID, or lease exists.

Two preliminary launches stopped before testing: direct import of `tsx` found
the deliberately absent worktree dependency tree, and passing
`--canary-only` to the root real operator returned its usage because that flag
belongs to the template verifier. Neither launch copied credentials, invoked
Codex, created a lease/run root, or contacted a provider; neither is reported
as a test pass. Node type stripping then invoked the correct focused verifier
without installing into the worktree.

Permission, full CloserFans TypeScript/lint/test/build, root Emdash, package,
browser, kernel, book, repository-wide, deployment, and release gates were
omitted because R4 changes no such boundary. This checkpoint is fake/no-model
compatibility hardening only. It does not diagnose v2, authorize a provider
call, create coordinates, produce a benchmark result, or advance 35/41
accounting. A separate exact code/preflight review remains mandatory.

###### Immutable R4 code/preflight review

The review accepts exact CloserFans checkpoint
`1307f249df784107a260fb2461719f93f2467fb5`, parent `8276e962...`, tree
`863db44af8a1d774fa1cac7839efd6babbebe4dc`. `git diff --check` is clean and
the revision changes only the three reviewed paths. Committed content SHA-256
values are:

```text
a33c63dccf3a687484358b326dfbf41d1d668ad0fe1c7025b6b3c6aedf8f0978  templates/emdash_benchmark/scripts/emdash-canary-output.schema.json
e9935771da40b165efda8f997aff057cac47c35c0fe641ff3965848372ad1a3d  templates/emdash_benchmark/scripts/fixtures/emdash-canary-fake-codex.mjs
6d2dc52622528645aa5b207f7939dba28de420be7ebd43201b3256745955db8b  templates/emdash_benchmark/scripts/verify-emdash-canary.mts
```

The committed schema is exactly the reviewed closed typed-enum object. The
two structural assertions are independent, precede fake execution, and add no
non-Node dependency. The focused disposable validation exercises both copies
and the unchanged final-message validator. No production proof/checker,
benchmark source, invocation argument, sandbox/environment rule, stream or
receipt parser, evidence policy, or public API changes.

The root operator, `emdash-canary-real.mts`, and
`emdash-canary-contract.mts` are unchanged from `8276e96`. Both execution
guards therefore still name terminal v2 and correctly reject every unreviewed
ID. The current branch is clean, descends from the reviewed base, and retains
no dependency tree or temporary test root. v1/v2 receipt and v2 lease hashes
remain exact. The recent R3 redacted host/model/feature health and R4 focused
fake evidence are carried forward because those inputs did not change; no
permission, provider, or aggregate rerun is warranted.

Decision: accept R4 as focused-green compatibility hardening and permit only a
later plan proposal to rotate the two execution guards from consumed v2 to a
fresh candidate v3 value. That proposal must bind one exact non-secret ID,
require a static retirement assertion for v2, change no other driver behavior,
and undergo its own review before code edits. This review itself authorizes no
new ID/root, edit, prompt/model/provider call, raw-evidence access, retry,
lease, benchmark result, performance claim, or graduation. Accounting remains
35/41.

##### `AGENT-EVAL-12B4-R5` consumed-ID v3 guard-rotation proposal

R4 is accepted, but both execution guards intentionally still name terminal
v2. A fresh invocation cannot be reviewed while the committed operator and
internal contract reject its ID. The proposed non-secret candidate is exactly:

```text
authorization ID: emdash-stage-a-native-exact-local-premise-2026-08-12-v3
ID SHA-256:       e1fe31c138df2b2ea7bf33138862a579aa5064dd1d738afefaffa21602aa5250
candidate root:   /home/user1/.emdash-stage-a/emdash-stage-a-native-exact-local-premise-2026-08-12-v3
candidate lease:  /home/user1/.emdash-stage-a/authorizations/e1fe31c138df2b2ea7bf33138862a579aa5064dd1d738afefaffa21602aa5250.json
```

Both candidate filesystem paths are absent at proposal time. Naming them here
does not create or authorize them.

The proposed implementation changes exactly three literals across three
CloserFans files from clean checkpoint `1307f249df784107a260fb2461719f93f2467fb5`:

1. root `scripts/run-emdash-stage-a-real.mjs` changes its closed allowlist from
   exact v2 to exact v3;
2. `templates/emdash_benchmark/scripts/emdash-canary-contract.mts` makes the
   identical change to `STAGE_A_REAL_AUTHORIZATION_ID`; and
3. `scripts/verify-emdash-benchmark-template-runtime.ts` requires exact v3 in
   both sources and requires both terminal v1 and v2 strings to be absent.

No schema, prompt, source, model, CLI version, model-catalog hash, argument,
permission/environment rule, bootstrap, lease implementation, process/stream
handling, evaluator, receipt, or evidence behavior changes. The candidate ID
does not assert that R4 fixed v2, and v1/v2 evidence remains immutable.

Validation is syntax and fake/no-model only: `node --check` for the root
operator, exact static presence/retirement checks, `git diff --check`, and the
bounded clean-install `--canary-only` verifier. The unchanged permission probe
and every broader aggregate are omitted. The implementation must leave the
candidate root/lease absent and the terminal receipt/lease hashes unchanged.

This proposal authorizes no edit until separately reviewed. Implementation
would still be non-authorizing: a fresh redacted at-call preflight, exact code
review, absent-state recheck, immutable authorization checkpoint, and explicit
one-command boundary would remain mandatory. No prompt/model/provider call,
raw-evidence access, v1/v2 retry/mutation, new lease/run root, benchmark result,
performance claim, or graduation is authorized. Accounting remains 35/41.

###### Immutable R5 v3-rotation review

Reviewed proposal checkpoint:
`43933823ea2f3ae9580b6d05a505e6d7a1e01eb1`, exact parent
`7ccf29e9fcba2d2a636a7109a3578ee690780642`, exact tree
`d23b37d1d667b7d3b5731b65a8f6036d3f03311d`. Complete plan SHA-256 values are:

```text
fe5858eb78853a099bee4b387e92be9d0095f83c5cdece4591e14b54e7635162  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
2de46565722b6f73a8f0c1459c8bcc69c4684529a68650b6f7356d349ef12b3c  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
```

The v3 string is a non-secret monotone identifier distinct from terminal v1
and v2. Its recorded hash is the exact lease-key derivation used by the
unchanged driver, and its candidate root and lease paths are absent. The
review finds no reason to change the date/sequence or broaden the correction.

Decision: approve only the three literal/assertion edits from exact clean
CloserFans checkpoint `1307f249df784107a260fb2461719f93f2467fb5`, with
these controls:

1. both execution guards must contain exact v3 once and contain neither exact
   v1 nor exact v2;
2. the root verifier must assert v3 presence and absence of both retired IDs
   in each guard source;
3. no other source, schema, prompt, runtime, permission, lease, receipt, model,
   evaluator, or evidence behavior may change;
4. validation is limited to operator syntax, exact static checks,
   diff/ancestry/status, and one bounded clean-install fake canary; and
5. candidate root and lease must remain absent, terminal hashes unchanged,
   and no provider/model process may be spawned.

The resulting checkpoint is still only a prerequisite for a later exact
at-call review. Do not create the v3 root/lease, invoke the operator with v3,
inspect raw evidence, retry or mutate v1/v2, or claim a benchmark/performance/
graduation result. Accounting remains 35/41.

###### R5 implementation checkpoint and focused validation

The exact reviewed rotation is committed on the isolated CloserFans branch as
`0ea5b98fbdacb6f449ef78577aebb8c7277b69a6`, parent
`1307f249df784107a260fb2461719f93f2467fb5`, tree
`149de95e39270ce007b645c7d11746b0266dfa44`. Its diff contains only the
three approved files, with these committed SHA-256 values:

```text
774752d0459d405b352d859f71cd0d3c1a275a328708899f9434032019c4854a  scripts/run-emdash-stage-a-real.mjs
f0091222fd38c4a03fecf825ce12512af4748c314c3b8624742543cf0dec47b8  scripts/verify-emdash-benchmark-template-runtime.ts
4938190361d718672ef9c8b38627c685853c38fb54f5f9690652e0f72341d2b0  templates/emdash_benchmark/scripts/emdash-canary-contract.mts
```

Both guards contain exact v3 once and contain neither exact v1 nor exact v2.
The root verifier enforces those counts for both committed sources. Operator
syntax, stripped-TypeScript syntax, exact static checks, and `git diff --check`
passed. The bounded disposable clean-install `--canary-only` verifier exited
zero: lock-preserving install, template typecheck, full fake scenario matrix,
schema assertions, and public fake CLI are green. It removed its disposable
roots and left no worktree dependency tree.

Candidate v3 root and lease remain absent. Terminal v1/v2 receipt and v2 lease
hashes remain `cb02d508...`, `c97c1f87...`, and `6dce7e860...`; no provider,
model, prompt, raw evidence, lease, or real run was touched. The permission
probe and all wider gates were omitted because R5 changes only the guard
identity and its static test.

This checkpoint makes the exact v3 guard available for review but does not
authorize using it. A fresh at-call review must independently bind committed
source/tree/manifest/input hashes, current closed CLI/login/model state,
permission probe, absent candidate state, and one exact command. Any resulting
authorization must remain terminal on every outcome. Accounting remains
35/41.

##### `AGENT-EVAL-12B4-R6` v3 at-call no-model preflight proposal

The proposed preflight audits exact clean CloserFans checkpoint
`0ea5b98fbdacb6f449ef78577aebb8c7277b69a6`, tree
`149de95e39270ce007b645c7d11746b0266dfa44`, and exact proposed command:

```text
node scripts/run-emdash-stage-a-real.mjs --authorization-id emdash-stage-a-native-exact-local-premise-2026-08-12-v3 --run-root /home/user1/.emdash-stage-a/emdash-stage-a-native-exact-local-premise-2026-08-12-v3
```

The command is review data only and must not be invoked during this tranche.
The audit may:

1. reconstruct exact committed template bytes in one validated disposable
   `/tmp/emdash-r6-preflight.*` directory through the exported snapshot helper;
   record only commit, tree, entry count, manifest SHA-256, operator SHA-256,
   and prompt/schema/source byte counts and SHA-256 values; then remove only
   that validated disposable directory;
2. in the same inherit-nothing environment used by the driver, run only
   `codex --version` and `codex login status`, retaining exact CLI revision and
   the non-secret `Logged in using ChatGPT` category but no credential data;
3. parse the bounded existing model cache and retain only fetched timestamp,
   selected `gpt-5.6-sol`/`3000`, default `low`, and high-effort support;
4. run
   `node --experimental-strip-types
   scripts/verify-emdash-benchmark-template-runtime.ts
   --permission-probe-only`, which performs a disposable clean install,
   template typecheck, full config help parse, local `codex sandbox`
   filesystem/network checks, and selected-case command without a prompt or
   model turn; and
5. recheck exact clean ancestry/status, absence of candidate v3 root/lease,
   absence of worktree dependencies and temporary roots, and unchanged v1/v2
   receipt plus v2 lease hashes.

Do not run doctor/provider reachability again; R3 already recorded that
broader health and R6 needs only the execution-critical local boundary. Do not
invoke `codex exec` with stdin, the real operator, a model/provider turn, or a
network-refreshing model command. Do not read credentials or raw v1/v2
evidence, alter config/login/cache, create a lease/run root, retry v1/v2, edit
code, or run any aggregate.

This proposal changes plans only and requires separate immutable review before
the probes. Green results would still not authorize the command: a later
behavior-free checkpoint must record every exact value and explicitly
authorize at most one terminal invocation. Accounting remains 35/41.

###### Immutable R6 no-model preflight review

Reviewed proposal checkpoint:
`b5b3cd14d432148e9cde8cb5ae0b007f5e5c47f5`, exact parent
`7406a8cb083f465e5c9e8d4f1886385071be1980`, exact tree
`338b09007007e91f7aad4e60409eb0b1352cc615`. Complete plan SHA-256 values are:

```text
1c982321680bb0290e0d80ffdb40c8ba6742daafc9397288648a20d8e1931696  docs/TYPESCRIPT_EMDASH_PROOF_ASSISTANT_AND_GOAL_GRAPH_PLAN.md
0f2b20a0ceeadd08058fd00df75bb1befefa1431d8f439cb128125df3e3a0fbc  docs/TYPESCRIPT_EMDASH_PUBLIC_PROOF_AGENT_BENCHMARK_PLAN.md
```

The review traces each proposed operation to a pre-provider boundary. Git
snapshotting and hash calculation read only committed public bytes. Version
and login status disclose only revision/category. Bounded cache parsing retains
only the already reviewed model tuple. The dedicated probe uses `exec --help`
only for parsing and `codex sandbox` for local process containment; it neither
feeds stdin to `exec` nor requests a model. It removes its own probe root. The
additional snapshot target is a single newly allocated `/tmp` directory whose
real path/prefix must be validated before exact removal.

Decision: approve R6 exactly as proposed, with these controls:

1. build the snapshot only from committed `0ea5b98` and reject any commit/tree
   mismatch before recording hashes;
2. construct the inherit-nothing environment explicitly and output only the
   whitelisted version, login category, and selected cache fields;
3. invoke only the verifier's `--permission-probe-only` mode; do not rerun the
   fake matrix, doctor, bundled-model refresh, or any aggregate;
4. validate and remove only the newly created `/tmp/emdash-r6-preflight.*`
   path, while leaving every `.emdash-stage-a` bootstrap/run/evidence root
   untouched; and
5. record failures as failures, then recheck clean worktrees, absent v3
   root/lease, and unchanged terminal hashes before any authorization proposal.

Do not invoke the exact v3 command, `codex exec` with a prompt, or any model/
provider turn; read no credential or raw evidence; alter no config/cache/state;
and create no lease/run root. Even a green R6 needs a separate behavior-free
authorization checkpoint. Accounting remains 35/41.

###### R6 measured v3 preflight result

R6 is green without invoking the v3 command or a model/provider turn. The
disposable committed snapshot matched exact CloserFans commit/tree
`0ea5b98fbdacb6f449ef78577aebb8c7277b69a6`/
`149de95e39270ce007b645c7d11746b0266dfa44`, contained 19 tracked entries,
and produced manifest SHA-256
`12aedbdfe2d0891e37422c1594e4c30462ba9539ab03d946f1120d872568a821`.
Exact operator and input facts are:

```text
 9910  774752d0459d405b352d859f71cd0d3c1a275a328708899f9434032019c4854a  scripts/run-emdash-stage-a-real.mjs
  409  a33c63dccf3a687484358b326dfbf41d1d668ad0fe1c7025b6b3c6aedf8f0978  scripts/emdash-canary-output.schema.json
 1704  117768e52381ede1b23f3bf4c43064e526daa6a25f3d8d4b0c3c879ffd7574ed  scripts/emdash-canary-prompt.txt
 3593  0c104f3888c61ce669958c44051ea65a153d9fbaea3c9c37139e6325b310eb84  benchmark-run.emdash.ts
```

The inherit-nothing projection contained only `CI`, `CODEX_HOME`, `HOME`,
`LANG`, `LC_ALL`, `NO_COLOR`, `PATH`, and `TMPDIR`. It observed Codex
`0.147.0`, empty stdout plus exact stderr category `Logged in using ChatGPT`,
and selected cache tuple `gpt-5.6-sol`/`3000`, fetched at
`2026-08-12T21:08:11.363260352Z`, default verbosity `low`, with high reasoning
supported. No credential value or full cache was output or retained.

The bounded clean-install `--permission-probe-only` verifier exited zero. It
passed template typecheck, complete strict-config help parsing, local sandbox
filesystem confinement, network denial, fake-home/tmp writes, protected-state
denials, and the exact selected-case allowlisted command. It used no `exec`
stdin or model turn and removed its probe and installation roots.

Exact v3 ID SHA-256 is
`e1fe31c138df2b2ea7bf33138862a579aa5064dd1d738afefaffa21602aa5250`;
the absolute run-root SHA-256 is
`9015f1615dee96634b6d4356814d97166f30521df849f0ff0de991d739713bd7`.
Both candidate root and lease remain absent. CloserFans and Emdash plan
worktrees are clean at `0ea5b98` and the current plan checkpoint respectively;
no root/template dependency tree or matching temporary root remains. The sole
v2 lease remains the only authorization file, and terminal hashes are still
v1 receipt `cb02d508...`, v2 receipt `c97c1f87...`, and v2 lease
`6dce7e860...`.

The validated temporary root was exactly
`/tmp/emdash-r6-preflight.rAnljz`, mode 0700, containing only `host-clean` and
`status-tmp` at cleanup time. Exact realpath/prefix validation preceded its
removal; it is now absent. No pre-existing `.emdash-stage-a` bootstrap, probe,
run, lease, or evidence was removed; the dedicated permission probe removed
only the probe root it had newly allocated.

Doctor/provider reachability, the already-green fake matrix, permission-
unrelated tests, and all aggregates were omitted. R6 establishes current
preflight readiness only. It does not prove that schema normalization fixed
v2, authorize the command, create an outcome, or advance 35/41. A separate
behavior-free checkpoint must bind these facts and decide whether one terminal
v3 invocation is authorized.

###### Immutable v3 at-call review and sole authorization

Reviewed qualification checkpoint:
`926979dd9991781a48aae22b416e47721f688df0`, exact parent
`6a55c5955a459870606b136d236cd13d54e9828b`, exact tree
`57660b57a1f010646bb9d71311c960b9840e5d88`. The exact CloserFans source,
manifest, operator/input, closed host, permission, cleanup, absent-state, and
preserved-evidence values are those recorded immediately above.

The review checks all mandatory boundaries:

1. CloserFans source is clean at exact `0ea5b98`, tree `149de95`, descending
   from reviewed R4/R5 checkpoints; its 19-entry snapshot manifest is
   `12aedbdf...` and both closed guards contain only v3.
2. Exact normalized schema, prompt, source, and operator hashes are fixed;
   focused fake/type/static gates and the fresh local permission probe pass.
3. Closed CLI/login/cache state is exact and exposes no credential value.
4. Candidate ID/root hashes are exact, both root and lease are absent, no
   dependency/transient root remains, and terminal v1/v2 evidence is intact.
5. The public mock route remains fake and the local real operator remains the
   sole authority that can reconstruct committed bytes, rerun preflights,
   acquire the exclusive lease, spawn Codex, and derive the minimized receipt.

Decision under the explicitly delegated unattended checkpoint policy:
authorize exactly one invocation of exactly this command after this
behavior-free plan checkpoint is committed:

```text
node scripts/run-emdash-stage-a-real.mjs --authorization-id emdash-stage-a-native-exact-local-premise-2026-08-12-v3 --run-root /home/user1/.emdash-stage-a/emdash-stage-a-native-exact-local-premise-2026-08-12-v3
```

No equivalent shell spelling, alternate executable, changed environment,
different ID/root, second command, or manual internal-driver invocation is
authorized. The operator may create only the bootstrap/preflight/run/evidence/
lease state already governed by committed code. Every result is terminal:
preflight refusal, authorization refusal, process failure, invalid stream,
abstention, rejected/accepted candidate, timeout, or any other observed
outcome consumes this authorization. Do not retry, reuse v3, replace its root,
or mint another coordinate without a new diagnosis/proposal/review chain.

Afterward inspect only the minimized receipt, canonical lease, ordinary path/
mode/hash/source facts, and public candidate diff/outcome fields exposed by the
receipt contract. Do not inspect or publish raw JSONL, stderr, final model
message, private candidate/replay files, credentials, or hidden reasoning.
Treat usage/cost as reported only if present, and retain unconditional
open-book contamination, non-graduation, and non-proof labels. One Stage A
result cannot establish success rate, comparative performance, or measured
graduation. Accounting remains 35/41 until a later Stage B/C design and
representative repeated evidence satisfy 12B4.

###### Sole v3 invocation outcome: terminal 35 ms process failure

The exact authorized command was invoked once after checkpoint `c880c8d` and
returned:

```text
emdash Stage A real: process-failure; receipt=receipt.json
```

This consumes v3 permanently. Do not rerun the command, reuse the ID, replace
the run root, remove or rewrite its lease/evidence, or create alternate
coordinates without a new diagnosis/proposal/review chain.

The minimized receipt is 4,658 bytes, mode 0600, SHA-256
`f7c6f859ee8c2991657214ce91e2be81f7812b7c2c2ccc784f90ca928cb1129a`.
The canonical 691-byte mode-0600 lease has SHA-256
`da092debaa617891847a6b29a0e4c7fddace0726153e2679d1640e7e662e4bf4`.
Run root and private evidence are mode 0700. Preserved v3 state includes
bootstrap `bootstrap-FXLRBm`, preflight root keyed by exact ID hash, run root,
private evidence, and the lease; no cleanup is authorized.

Receipt revision is `getpaidx-emdash-stage-a-receipt-v2`. It binds exact case
`native.exact.local-premise`, clean source `0ea5b98`/tree `149de95`, manifest
`12aedbdf...`, operator `774752d...`, normalized schema `a33c63d...`, prompt
`117768e...`, initial/candidate source `0c104f3...`, argument vector
`4227e9c49130c97a7eb5fde1f7666f59c48c465e1672c253373ae02ec04f5d68`,
v3 ID hash `e1fe31c...`, and lease hash `da092de...`. The lease independently
binds the same source/operator/manifest/argument vector, run-root hash
`9015f161...`, and state `provider-spawn-authorized`.

Operational facts are exact: `providerExecuted=true` under the conservative
spawn classification; process spawned, exited 1, and ran from
`2026-08-12T21:12:54.814Z` to `21:12:54.849Z` (35 ms), without timeout,
overflow, signal, or spawn error. Stream audit is invalid with
`incomplete-stream`, zero commands, zero file-change events, no forbidden
surface, and no valid final message. Source remained clean with zero changed
paths and valid scope/Git/extraction audits. Usage is null; cost amount and
currency are null with reason `chatgpt-authenticated-provider-cost-not-priced`.
Benchmark outcome is null and receipt validity is false.

The receipt also confirms exact fresh local permission provenance, disabled
network/web search/plugins/MCP/hooks/memories/subagents, no inherited agent
configuration, lifecycle-scripts-disabled clean installation, separate clean
evaluator, and no registry credential. Contamination remains
`public-owner-reference-accessible`; `graduationEligible=false` and
`proofEvidence=false` remain unconditional.

The 35 ms result does not establish whether a remote model request began or
completed. It does establish that replacing top-level `$schema`/bare `const`
with the normalized typed-enum schema was not sufficient to cross the same
pre-turn boundary. No proof patch, proof result, benchmark score, usage/cost,
performance comparison, or graduation evidence exists. Raw JSONL, stderr,
final model message, candidate, diff, and replay evidence were not inspected.
Terminal v1/v2 receipt and v2 lease hashes remain unchanged; both worktrees
are clean.

Any next step must be separately planned and no-model. The dependency-ready
direction is an evidence-safe classifier that may read the private stderr only
inside a bounded local process and emit a fixed, non-content category plus
byte/hash facts, without exposing raw text to the reviewer. That direction is
not authorized by this result. Accounting remains 35/41.

##### `AGENT-EVAL-12B4-R7` non-content stderr classifier proposal

The repeated pre-turn failure cannot be narrowed further through public help,
redacted health, normalized schema, or minimized receipt fields. Opening raw
stderr directly would unnecessarily expose private provider diagnostics,
paths, or identifiers to the reviewer. R7 instead proposes a deterministic,
tracked, local classifier whose process reads only exact v3 stderr and emits no
raw-derived string.

The proposed implementation adds exactly two root CloserFans scripts from
clean checkpoint `0ea5b98`:

1. `scripts/classify-emdash-stage-a-stderr.mjs` exports a pure bounded byte
   classifier and a closed no-argument main program hard-bound to exact v3 run
   root, receipt SHA `f7c6f85...`, lease SHA `da092de...`, ID hash
   `e1fe31c...`, expected mode 0600, regular-file/no-symlink status, and a
   four-MiB maximum. The main program validates those facts before reading
   `private-evidence/codex-stderr.txt`.
2. `scripts/verify-emdash-stage-a-stderr-classifier.mjs` imports only the pure
   classifier and tests empty, non-UTF-8, CLI argument, configuration,
   authentication, structured-output/schema, model-selection, transport/
   provider, ambiguous, and unmatched synthetic fixtures plus maximum-size and
   non-disclosure properties.

The classifier output is a fixed JSON object containing only revision, exact
target ID hash, byte count, SHA-256, UTF-8 validity, line count, terminal-
newline boolean, fixed matched rule IDs, and one of `empty`, `classified`,
`ambiguous`, `unclassified`, or `non-utf8`. Rule IDs are constants such as
`cli-argument`, `configuration`, `authentication`, `structured-output-schema`,
`model-selection`, and `transport-provider`. Regex captures, matched text,
unmatched text, file contents, provider messages, arbitrary error strings, and
raw-derived paths must never enter output or thrown diagnostics.

The main program must use fatal UTF-8 decoding, bounded synchronous/atomic
reads of existing files only, fixed error codes/messages, and no writes,
network, child process, provider, model, config, cache, or credential access.
It must not open JSONL, final-message, candidate, diff, replay, or any v1/v2
file. Ambiguous or unmatched data is a valid non-diagnostic result, not a
reason to reveal content.

Implementation validation is limited to `node --check`, the synthetic
verifier, a source scan excluding raw-output/error interpolation and external
capabilities, exact two-file diff/ancestry/status, and unchanged receipt/lease
hashes. No real evidence is read during implementation. After a separate exact
code review, a later one-command authorization may run the classifier once and
record only its fixed output. It may never feed evidence to a model or retry
Codex.

This proposal authorizes no edit, classifier execution, raw evidence read,
provider/model access, coordinate, retry, cleanup, result, or graduation. It
requires separate immutable review. Accounting remains 35/41.

###### Immutable R7 proposal review

Exact proposal checkpoint `43a8a9f057439497f7f481832fbc3fcfc6605ce4`
has parent `0603dae490b2d2424e4e58dcd82fdad4693f6b43`, tree
`70231c703ab7c5a40035683b879747f783023fc0`, master-plan SHA-256
`f930312f407204ded15ae8545761e1609159160090033eb37dd8c0b9a6ef254d`,
and this-plan SHA-256
`f239ee4d520c14037af4d5b85385e26ebcb2861d0278f48b47b705bfd6ade27c`.
The implementation baseline is clean CloserFans
`0ea5b98fbdacb6f449ef78577aebb8c7277b69a6`, tree
`149de95e39270ce007b645c7d11746b0266dfa44`; both proposed paths are
absent. The unchanged root operator and canary owner have SHA-256
`774752d0459d405b352d859f71cd0d3c1a275a328708899f9434032019c4854a`
and `2b7cb752a752faf5ed507d613982249f8253c64cb1dea75772aa146a54bb00d5`.

Under the standing unattended-approval delegation, review approves only the
two new local scripts, subject to these corrections and conditions:

1. The pure function accepts bytes, rejects more than exactly 4,194,304 bytes
   with a constant error, and never performs I/O. Its output keys are exactly
   revision, target authorization-ID SHA-256, byte count, content SHA-256,
   UTF-8 validity, LF-delimited line count, terminal-LF boolean, matched fixed
   rule IDs, and status. Empty input has zero lines and no terminal LF; for
   non-empty input line count is LF count plus one only when the last byte is
   not LF, including for invalid UTF-8.
2. Fatal UTF-8 decoding precedes matching. Empty and invalid input select
   `empty` and `non-utf8`; zero, one, or multiple matches select
   `unclassified`, `classified`, or `ambiguous`. Matched IDs are deduplicated
   in the fixed rule-table order. Patterns must be bounded, capture-free in
   their use, and may influence only this constant vocabulary.
3. The proposal's phrase “no raw-derived string” excludes content-bearing or
   reversible text. It still permits the explicitly reviewed digest, numeric
   counts, booleans, and selection among fixed rule/status constants. No
   substring, capture, exception message, path, or arbitrary property key may
   cross the process boundary.
4. The no-argument main is hard-bound to the exact absolute v3 run, receipt,
   stderr, and lease paths plus full receipt SHA-256
   `f7c6f859ee8c2991657214ce91e2be81f7812b7c2c2ccc784f90ca928cb1129a`
   and lease SHA-256
   `da092debaa617891847a6b29a0e4c7fddace0726153e2679d1640e7e662e4bf4`.
   It validates non-symlink private directories, current-user ownership,
   exact 0700 directory/0600 file modes, regular files, bounded metadata, and
   exact metadata hashes before opening stderr.
5. Every file is opened read-only with `O_NOFOLLOW`; `fstat` and bounded read
   use that same descriptor, followed by a stability check before close. This
   is the required meaning of the proposal's “atomic reads.” Validation or I/O
   failure emits only one fixed non-content failure code and exits nonzero.
6. Imports are limited to Node filesystem/path/URL/crypto primitives. No
   filesystem write, child process, network, dynamic import, environment or
   configuration read, credential/cache access, model/provider call, or
   evidence path other than exact v3 receipt/lease/stderr is permitted.
7. The verifier imports only the pure export and uses synthetic bytes. It must
   prove every status/rule, deterministic order, exact-limit success,
   over-limit failure, fatal-decoding behavior, output-key closure, and
   non-disclosure against path/token/provider-message sentinel strings.
8. Only syntax, the synthetic verifier, static capability/output scans, exact
   two-file diff and baseline ancestry, and unchanged tracked authority hashes
   qualify implementation. No private artifact may be opened by a validation
   command. A focused-green implementation checkpoint remains non-authorizing;
   a separate exact code/evidence-access review is mandatory before one run.

This review authorizes those two additive code files and synthetic-only gates.
It authorizes no classifier execution against v3, raw evidence access,
provider/model action, Codex retry, integration, push, deployment, release,
cleanup, diagnosis, benchmark result, or graduation. Human supersession
remains available through the checkpoint history. Accounting remains 35/41.

###### R7 implementation qualification checkpoint

CloserFans checkpoint `04e58f99313a9c61132d5b13e952e7bbabc63cf0`,
parent `0ea5b98fbdacb6f449ef78577aebb8c7277b69a6`, and tree
`5b150bc38e421dad7f64871e9389e4015471a874` add exactly the two reviewed
scripts in 431 lines. Their SHA-256 values are:

```text
7b5e4d332ff9ae960f8d6d576ddcbd2aa5da1fdb3dae0514564bb8f1fbc32e24  scripts/classify-emdash-stage-a-stderr.mjs
2a881c2bed7597a92e88e46d38b508651439dd923ea95c4186fc2b3c9c9b4bf1  scripts/verify-emdash-stage-a-stderr-classifier.mjs
```

The classifier copies and bounds its byte input, uses fatal UTF-8 decoding,
emits the exact closed nine-key record, preserves fixed rule order, and
distinguishes all five statuses. Its closed main binds the full v3
receipt/lease hashes and exact paths, validates owner/mode/type/realpath,
opens with `O_NOFOLLOW`, and performs a same-descriptor `limit + 1` read plus
pre/post stability checks. All exceptions collapse to one fixed failure line.
The verifier imports only the pure export and uses no real filesystem input.

Node `v24.11.1` syntax checks for both files and the synthetic verifier pass.
The verifier covers all six rule IDs, empty, invalid UTF-8, ambiguous,
unclassified, LF/unterminated lines, deterministic order, exact four-MiB
success, over-limit/non-byte refusal, exact output-key closure, freezing, and
three sentinel non-disclosures. Static scans find no child-process, network,
dynamic-import, environment, filesystem-write, or other external capability;
the only credential-like source term is the fixed authentication regex.
Diff/whitespace/ancestry checks pass and the CloserFans branch is clean at
0/9 relative to preserved `master` `cbf2356`.

The unchanged root operator and canary owner retain SHA-256
`774752d0459d405b352d859f71cd0d3c1a275a328708899f9434032019c4854a`
and `2b7cb752a752faf5ed507d613982249f8253c64cb1dea75772aa146a54bb00d5`.
No classifier main, private artifact, Codex/provider/model, configuration,
credential, package install, aggregate, push, merge, deployment, release, or
cleanup ran. These are omissions, not passes. This checkpoint remains
non-authorizing; an exact code/evidence-access review is next. Accounting
remains 35/41.

###### R7 exact evidence-access proposal

The next operation is a read-only diagnosis of the already terminal v3
process, not a Codex retry or provider action. Freeze the sole candidate
command as:

```text
/usr/bin/env -i HOME=/home/user1 LANG=C.UTF-8 LC_ALL=C.UTF-8 NO_COLOR=1 PATH=/usr/bin:/bin /home/user1/.nvm/versions/node/v24.11.1/bin/node /home/user1/closerfans-emdash-canary-v1/scripts/classify-emdash-stage-a-stderr.mjs
```

The Node executable SHA-256 is
`5796fd9700e83170bc7ddfdf7f18858c794a9f91cb39dd6f9e95060b292f2563`.
The command has no arguments beyond the exact committed script and supplies
no inherited environment, configuration, cache, credential, network, model,
provider, or output-file authority.

Before execution, a separate behavior-free review may recheck clean exact
CloserFans `04e58f9`/tree `5b150bc`, the two implementation hashes, unchanged
operator/canary hashes, exact executable/hash, and metadata only for the four
hard-bound private directories plus exact receipt, lease, and stderr files.
Metadata output is limited to regular/directory/symlink booleans, current-user
ownership, exact permission mode, byte size, and exact-realpath equality. It
must not open or hash stderr, parse any artifact, list sibling evidence, or
inspect timestamps, names beyond the already recorded paths, content, JSONL,
final message, candidate, diff, replay, v1, or v2.

If every code and metadata fact satisfies the committed classifier, a distinct
plan checkpoint may authorize the frozen command exactly once. Successful
execution must have exit zero, empty stderr, and one newline-terminated JSON
object with exactly the reviewed nine keys and closed values. Fixed failure is
also terminal and must not be retried. Only that one output line may be
recorded; no raw content or new artifact may be displayed or written.

This proposal authorizes no metadata probe, classifier execution, evidence
read, provider/model action, Codex retry, integration, push, deployment,
release, cleanup, result, or graduation. It requires separate immutable
review. Accounting remains 35/41.

###### Immutable R7 access-proposal review

Exact proposal checkpoint `c88cb1d709293cd3c835ecaa3066f5ba6bd6ef7b`
has parent `fdd37495d48b1c68fcc039820fa9816e86138faa`, tree
`aa397b1a543292ae24aba5f3e372e86f8deaa2ba`, master-plan SHA-256
`8746dc1df09d5f584b07af8e7ee8375d5b23e79fe640ced7d4ee587c4bbb393c`,
and this-plan SHA-256
`dafec0b978dafa1bd996e00b5930e0d1552ccb9ac89e8fb15d7f7324b4693164`.
Committed CloserFans remains clean at exact `04e58f9`/tree `5b150bc`; the
classifier/verifier, operator/canary, and Node executable hashes remain the
four values recorded above.

Review confirms that importing the classifier has no main effect, while its
main can open only the three hard-coded v3 files after validating the four
hard-coded directories. The pure output cannot carry content or dynamic keys;
every filesystem or decoding exception becomes the same fixed failure line.
The closed command supplies no `NODE_OPTIONS`, Codex home, auth, proxy,
credential, plugin, MCP, hook, memory, model, or provider state.

Under the standing unattended-approval delegation, this review authorizes
exactly one behavior-free metadata probe. It may call only `lstat` and
`realpath` on the seven exact paths and emit one closed JSON array with roles
`state-root`, `authorization-root`, `run-root`, `evidence-root`, `receipt`,
`stderr`, and `lease`; each entry may contain only expected-kind validity,
symlink boolean, current-UID boolean, octal mode, file byte size or null, and
exact-realpath boolean. It may recheck Git/code/executable hashes without
opening artifacts. It may not call `open`, `read`, `hash`, directory listing,
or the classifier main.

Only a completely matching result may advance to a distinct behavior-free
authorization checkpoint for the already frozen classifier command. This
review does not itself authorize that command, stderr content access, a second
metadata probe, any Codex/provider/model action, retry, integration, push,
deployment, release, cleanup, diagnosis, result, or graduation. Accounting
remains 35/41.

###### R7 metadata outcome and shape-correction proposal

The sole authorized metadata probe ran once after review checkpoint `64d60e6`
and exited zero. Its one newline-terminated line is 983 bytes with SHA-256
`906e40fd3434dfa7f676fe26809249597e429e90c74af614e13aaf5be5409c5d`.
All seven substantive entries match the classifier preconditions:

| Role | Kind | Symlink | Current UID | Mode | Bytes | Exact realpath |
| --- | --- | --- | --- | --- | ---: | --- |
| `state-root` | directory | false | true | 700 | — | true |
| `authorization-root` | directory | false | true | 700 | — | true |
| `run-root` | directory | false | true | 700 | — | true |
| `evidence-root` | directory | false | true | 700 | — | true |
| `receipt` | file | false | true | 600 | 4,658 | true |
| `stderr` | file | false | true | 600 | 98 | true |
| `lease` | file | false | true | 600 | 691 | true |

The probe nevertheless violated the reviewed closed shape by adding an
`expectedMode` property to every entry. Each value is a fixed duplicate of the
already permitted `mode` (`700` for directories and `600` for files), not an
artifact-derived value, path, message, identifier, timestamp, or content. The
inline program imported only `lstatSync`/`realpathSync`; it did not open, read,
hash, list, parse, classify, or mutate any artifact. The probe is consumed and
must not be rerun. Its result is not reported as a strict preflight pass.

Freeze a behavior-free correction: a separate review may accept only this
exact recorded 983-byte result despite the redundant constant property, after
checking that every required fact passes and every `expectedMode` exactly
equals its permitted `mode`. It may not reinterpret any other extra field,
run another probe, or access evidence. If accepted, a later behavior-free
checkpoint may authorize the already frozen classifier command exactly once.

This correction proposal authorizes no classifier, stderr read, metadata
retry, provider/model action, Codex retry, integration, push, deployment,
release, cleanup, diagnosis, result, or graduation. It requires separate
immutable review. Accounting remains 35/41.

###### Immutable R7 metadata-shape correction review

Exact correction checkpoint `cc5db11dae570615340be34f3bad5c7726876fa4`
has parent `64d60e6be81f4f95c0c5a433d7f56269599f8cec`, tree
`476aeaa98bb3da1ddccff138f3fdedc487dfc3d4`, master-plan SHA-256
`dcd36472cbfc4f19231f45c0785845bdb2b87230d34263bab6c5f0a668801bda`,
and this-plan SHA-256
`0cb370d4dddce87d437f4bb14b26965635438a3c8760470684a21668da3a79ae`.
No new filesystem probe or artifact access was used for this review.

The hash-bound recorded array has exactly seven entries and exactly one
unreviewed key. For every directory entry, `mode` and `expectedMode` are both
the fixed string `700`; for every file entry they are both `600`. The added
property therefore contributes no information beyond the already authorized
mode and does not alter any required fact. Every kind, non-symlink,
current-owner, mode, bounded-size, and exact-realpath condition is true.

Under the standing unattended-approval delegation, review accepts only this
exact output as sufficient metadata qualification. This is a narrow
supersession of the closed-shape condition, not permission for arbitrary extra
keys or a declaration that the original probe conformed. The consumed probe
remains nonconforming and must not be rerun.

Acceptance makes a separate behavior-free authorization checkpoint
dependency-ready. This review does not itself authorize the classifier,
stderr access, metadata retry, provider/model action, Codex retry, integration,
push, deployment, release, cleanup, diagnosis, result, or graduation.
Accounting remains 35/41.

###### Sole R7 classifier authorization

The final behavior-free audit is green. CloserFans is clean at exact
`04e58f99313a9c61132d5b13e952e7bbabc63cf0`, tree
`5b150bc38e421dad7f64871e9389e4015471a874`, with exact classifier/verifier
hashes `7b5e4d3...`/`2a881c2...`; operator/canary hashes remain
`774752d...`/`2b7cb75...`. The closed Node executable remains exact SHA-256
`5796fd9...`. Accepted metadata result `906e40f...` proves the four exact
private directories and three exact files satisfy kind, non-symlink,
current-owner, 0700/0600 mode, bounded size, and realpath preconditions.

Under the standing unattended-approval delegation, authorize exactly one
invocation of the already frozen command, and only after this checkpoint:

```text
/usr/bin/env -i HOME=/home/user1 LANG=C.UTF-8 LC_ALL=C.UTF-8 NO_COLOR=1 PATH=/usr/bin:/bin /home/user1/.nvm/versions/node/v24.11.1/bin/node /home/user1/closerfans-emdash-canary-v1/scripts/classify-emdash-stage-a-stderr.mjs
```

The process may internally read only exact receipt, lease, and 98-byte stderr
through its committed stable bounded descriptors. Only its one fixed JSON
line or fixed failure line may be observed. Exit zero requires empty stderr
and the exact nine-key closed result; any failure, ambiguous result, or
unclassified result is still terminal. The command must never be retried,
renamed, parameterized, redirected to an artifact, or fed to another model.

This authorization includes no Codex/provider/model action, benchmark result,
proof or performance claim, integration, push, deployment, release, cleanup,
Stage B/C, or graduation. Post-command review is limited to the emitted line,
exit/stderr shape, clean code state, and already public/recorded provenance.
Accounting remains 35/41.

###### Sole R7 outcome and R8 fixed-stage failure proposal

The frozen classifier command was invoked exactly once after authorization
checkpoint `eb6af9a` and is terminal. It exited `1` and emitted only:

```text
emdash Stage A stderr classifier: failed
```

That newline-terminated line is 41 bytes with SHA-256
`28b52c309800dfb2f8ff65b2565ca3179626b85fc46f913a92da3aa57970a31f`.
The committed failure branch writes it to stderr; the captured combined output
contains nothing else. CloserFans remains clean at exact `04e58f9`/tree
`5b150bc`. No artifact was written or changed, and no Codex/provider/model,
configuration, credential, network, retry, or external action occurred.

The generic line proves the non-disclosure boundary but cannot distinguish a
directory check, receipt/lease integrity check, stderr check, or pure
classification failure. R7 must not be rerun. Freeze R8 as a non-authorizing
two-file correction from exact `04e58f9`:

1. The classifier may wrap each existing operation in a fixed-stage boundary
   and emit on failure only a closed record with revision, target ID hash, and
   one of `invocation`, `state-root`, `run-root`, `evidence-root`,
   `authorization-root`, `receipt-integrity`, `lease-integrity`,
   `stderr-integrity`, `classification`, or `internal`. Arbitrary error text,
   codes, paths, causes, captures, or stack data remain discarded.
2. The synthetic verifier may import a pure failure-record constructor and
   prove exact key closure, every stage, fixed ordering, freezing, and fallback
   of arbitrary input to `internal`. It still must not invoke the main or open
   any filesystem path.

All existing path/hash/mode/owner/bound/read/rule/output behavior stays exact.
Only the classifier and its synthetic verifier may change; operator, canary,
receipt/lease/stderr, authorization, provider, and every other repository
surface remain untouched. Syntax, synthetic verifier, static capability/diff,
unchanged-authority hashes, and clean ancestry are the complete implementation
gates. No long aggregate is relevant.

This proposal authorizes no code edit, classifier execution, evidence access,
metadata retry, Codex/provider/model action, integration, push, deployment,
release, cleanup, diagnosis, result, or graduation. It requires separate
immutable review. Accounting remains 35/41.

###### Immutable R8 fixed-stage proposal review

Exact proposal checkpoint `8e864e9ce3c4a171a0f1b9c5080d3b682e37331c`
has parent `eb6af9a41ac5c2ebf7b89aa8b40bdcbed48cb197`, tree
`61df718126ff40f109d5b70526d54dfc97c1cd06`, master-plan SHA-256
`988c0e1f2ff96c3a2feb07c99e57c67f5113e861391f56390f41e5e8e3491425`,
and this-plan SHA-256
`e5081b5784cfa603854e96e80a562f942499c4b599b5530ce16eba517b48f754`.
CloserFans remains clean at exact `04e58f9`/tree `5b150bc`; classifier,
verifier, operator, and canary hashes remain `7b5e4d3...`, `2a881c2...`,
`774752d...`, and `2b7cb75...`.

Under the standing unattended-approval delegation, review approves only the
two-file local correction, subject to these exact conditions:

1. Add a closed ordered stage set with exactly the ten proposal constants. A
   pure exported constructor returns a frozen record whose keys are exactly
   `revision`, `targetAuthorizationIdSha256`, and `failureStage`; its revision
   is `getpaidx-emdash-stage-a-stderr-classifier-failure-v1`. Any value outside
   the set becomes `internal` rather than entering output.
2. A private stage error stores only one validated constant. A wrapper catches
   every underlying exception without retaining `cause`, message, code, path,
   stack, object, or string and replaces it with that stage error.
3. Wrap the four directory validations, three file reads, and pure classifier
   call separately. Wrong argument count maps to `invocation`; an otherwise
   unexpected main failure maps to `internal`. Failure writes only the
   canonical three-key JSON plus LF to stderr and exits one. Successful
   nine-key stdout remains byte-for-byte unchanged.
4. The verifier imports only the two pure exports. It tests all ten stages in
   order, exact keys/revision/hash/freeze, invalid string/object/sentinel
   fallback to `internal`, and absence of each supplied sentinel from JSON,
   while retaining every existing classification assertion.
5. No path, receipt/lease hash, rule, bound, descriptor, owner/mode check,
   environment, successful output, evidence, operator, canary, authorization,
   or external surface may otherwise change. Validation is syntax, pure
   synthetic verifier, static capability/content scans, exact two-file diff,
   unchanged authority hashes, clean ancestry, and no private main execution.

This review authorizes those two code edits and synthetic-only gates. It
authorizes no classifier execution, evidence access, metadata retry,
Codex/provider/model action, integration, push, deployment, release, cleanup,
diagnosis, result, or graduation. A focused-green checkpoint still requires a
separate code/access review. Accounting remains 35/41.

###### R8 fixed-stage implementation qualification

CloserFans checkpoint `7973127ef1349d89aafbeb22756cb3aa3e08e375`,
parent `04e58f99313a9c61132d5b13e952e7bbabc63cf0`, and tree
`bbf390dc964e10782e664ee4dbaef940e5ab328d` change exactly the two approved
files. Their new SHA-256 values are:

```text
f2166f0c32fb3c2434e11ad44aa27983bf9c914b0f838b24f8edd5952db739d0  scripts/classify-emdash-stage-a-stderr.mjs
4a86abe9685cb9df042fac68f502aecf295790d3ee7d5045a975cd2ac27064ee  scripts/verify-emdash-stage-a-stderr-classifier.mjs
```

The implementation adds the exact ten-stage array, frozen three-key pure
failure record, non-`Error` stage token containing only the validated constant,
cause-discarding wrappers around each exact directory/file/classification
step, `invocation` handling, and `internal` fallback. The existing nine-key
success path, all paths/hashes/rules/bounds/descriptors/modes, and every
authority surface remain unchanged.

Node syntax checks and the synthetic verifier pass. All ten stages preserve
order and exact keys/revision/target/freeze; arbitrary string, object, null,
and undefined inputs fall back to `internal` without the sentinel. Every R7
empty/UTF-8/rule/ambiguous/unclassified/line/limit/closure/non-disclosure test
also remains green. Static capability scan has no matches; exact diff and
whitespace checks pass; operator/canary hashes remain `774752d...` and
`2b7cb75...`; the CloserFans worktree is clean.

No classifier main, private artifact, metadata probe, Codex/provider/model,
configuration, credential, network, install, aggregate, push, merge,
deployment, release, or cleanup ran. These are omissions, not passes. R8
remains non-authorizing pending an exact code/access review. Accounting remains
35/41.

###### Immutable R8 code/access review and sole authorization

Exact qualification checkpoint `54af912674b61e3316ae9e9bda1323eb7cad3f54`
has parent `547e367967df5855954ea4f43b513e25edab95a3`, tree
`c88947b48d79a8a8b3073a6f9820405aeefea1ec`, master-plan SHA-256
`72c269e545c8ff3899451524fe055a6c7e2b0e05271b270059e06caef661bf52`,
and this-plan SHA-256
`5ceece9517c03c128dbe61690986e71385127ad6b7c346fb632630d2eda7ac34`.
CloserFans is clean at exact `7973127`/tree `bbf390d`, 0/10 from preserved
`master`; classifier/verifier, operator/canary, and Node hashes are exactly the
five values recorded above.

Code review confirms that only failure projection changed. Every directory,
path, file, expected receipt/lease hash, owner/mode check, descriptor flag,
read bound, stability test, classifier rule, and success output is unchanged.
Each wrapper catches without retaining its input and throws a frozen non-Error
token with one stage constant. Main projects only that constant or `internal`.
The accepted metadata result `906e40f...` therefore still satisfies all
unchanged access preconditions; no metadata rerun is needed or authorized.

Under the standing unattended-approval delegation, authorize exactly one R8
invocation after this behavior-free checkpoint:

```text
/usr/bin/env -i HOME=/home/user1 LANG=C.UTF-8 LC_ALL=C.UTF-8 NO_COLOR=1 PATH=/usr/bin:/bin /home/user1/.nvm/versions/node/v24.11.1/bin/node /home/user1/closerfans-emdash-canary-v1/scripts/classify-emdash-stage-a-stderr.mjs
```

Only one nine-key classification line on stdout or one three-key staged
failure line on stderr may be observed. Every exit, stage, classification,
ambiguous, or unclassified outcome is terminal; the command must not be
retried, redirected, parameterized, or supplied to another model. This is a
local read of preserved terminal evidence, not a Codex/provider/model action.

No benchmark/proof/performance claim, integration, push, deployment, release,
cleanup, Stage B/C, or graduation is authorized. Post-command review remains
limited to the fixed output, exit/channel shape, clean code state, and recorded
provenance. Accounting remains 35/41.

###### Sole R8 outcome and R9 receipt-hash audit proposal

The exact R8 command was invoked once after checkpoint `e6d507b` and is
terminal. It exited `1` with one 200-byte newline-terminated fixed record,
SHA-256 `ddd0b4736a42768020433d311a6779305af3a3f5a4368193cce4824abfb85a5d`:

```json
{"revision":"getpaidx-emdash-stage-a-stderr-classifier-failure-v1","targetAuthorizationIdSha256":"e1fe31c138df2b2ea7bf33138862a579aa5064dd1d738afefaffa21602aa5250","failureStage":"receipt-integrity"}
```

No raw error or artifact content was emitted. Because directory stages pass
and `receipt-integrity` is thrown before lease, stderr, or classification, this
attempt did not open stderr. CloserFans remains clean at `7973127`/tree
`bbf390d`; no file, evidence, provider/model, network, or external state
changed. R8 must not be rerun.

The accepted metadata already proves receipt kind, non-symlink, owner, mode,
size, and realpath. The least invasive next discriminator is therefore the
expected receipt digest, not another classifier edit. Freeze R9 as a
non-authorizing proposal for exactly one command:

```text
/usr/bin/env -i LANG=C.UTF-8 LC_ALL=C.UTF-8 PATH=/usr/bin:/bin /usr/bin/sha256sum /home/user1/.emdash-stage-a/emdash-stage-a-native-exact-local-premise-2026-08-12-v3/private-evidence/receipt.json
```

`/usr/bin/sha256sum` is GNU coreutils 9.4 with executable SHA-256
`9992e1f1feb6f0f396bc8d6691ebc1adbfc269fd628bce84eda1d4ba5c3995c7`.
The command may read only the already minimized receipt and emit only its
64-hex digest plus the already recorded exact path. It may not read stderr,
lease, JSONL, final message, candidate, diff, replay, v1, or v2; write a file;
or contact any process/provider/model beyond the local hash executable.

This proposal authorizes no hash command, evidence read, classifier, metadata
retry, code edit, Codex/provider/model action, integration, push, deployment,
release, cleanup, diagnosis, result, or graduation. Separate immutable review
is mandatory. Accounting remains 35/41.

###### Immutable R9 receipt-hash review and sole authorization

Exact proposal checkpoint `c1145d7378046fdcea1b4d7d423b518bdddcb989`
has parent `e6d507b32122456754fa6ec5bef6fea54bb349ee`, tree
`4fbf0f8f97e95b6f3032117be3f81c099f322935`, master-plan SHA-256
`f010316ba57883efb239b64989e44735a2528d407d92e16433b1081d30e3c681`,
and this-plan SHA-256
`18ffa3256a8e0e694185a2fc3a95461f6d215d55fff1cb6aced3b20372cc15da`.
CloserFans remains clean at `7973127`/tree `bbf390d`; no evidence or code was
accessed during review.

Review accepts the exact command because the target is the already minimized
receipt whose size, path, type, non-symlink status, owner, and mode are
recorded; SHA-256 is one-way, non-content output already part of receipt
provenance. The closed environment and exact coreutils binary expose no
configuration, credentials, model, provider, network, sibling listing, or
write authority.

Under the standing unattended-approval delegation, authorize the frozen R9
command exactly once after this checkpoint. Exit zero and one ordinary
`sha256sum` line or any failure is terminal. The command must not be retried,
redirected, generalized, supplied another path, or fed to a model. Post-command
review may compare only the 64-hex digest with committed expected
`f7c6f859ee8c2991657214ce91e2be81f7812b7c2c2ccc784f90ca928cb1129a`.

This includes no classifier or stderr/lease/other-artifact access, code edit,
Codex/provider/model action, integration, push, deployment, release, cleanup,
benchmark/proof/performance claim, or graduation. Accounting remains 35/41.

###### Sole R9 outcome and R10 unsupported-flag correction proposal

The authorized R9 command ran once after checkpoint `c9b072b`, exited zero,
and emitted one 180-byte line with SHA-256
`778c7c806121c5585549662882cdfe20f00c90b988cb10806a45bea9799dbc16`.
Its digest is exactly the classifier's expected
`f7c6f859ee8c2991657214ce91e2be81f7812b7c2c2ccc784f90ca928cb1129a`.
R9 is terminal and must not be rerun. Receipt content/provenance is therefore
not the cause of `receipt-integrity`.

A no-evidence runtime-constant probe of the exact Node 24.11.1 executable
returns `O_RDONLY=0`, `O_NOFOLLOW=131072`, `noFollowInteger=true`, and
`cloexecInteger=false`; `O_CLOEXEC` is absent and therefore omitted from JSON.
The committed helper rejects when either `O_NOFOLLOW` or `O_CLOEXEC` is not an
integer, before it calls `openSync`. Accepted path metadata and the matching
digest eliminate every earlier receipt condition, so this unsupported constant
check is the exact R7/R8 failure cause.

Freeze R10 as a non-authorizing one-file correction from exact CloserFans
`7973127`: in `scripts/classify-emdash-stage-a-stderr.mjs`, require only the
available integer `O_NOFOLLOW` and open with `O_RDONLY | O_NOFOLLOW`. Remove
only the `O_CLOEXEC` check and flag. The classifier imports no child-process
primitive and static review prohibits every spawn/exec/fork path, so no child
exists to inherit the synchronous descriptor; `finally` still closes it and
process exit closes it on abnormal termination.

All owner/mode/type/realpath, same-descriptor identity, `limit + 1` read,
pre/post stability, expected hashes, fixed stages, classifier rules, outputs,
and external authorities remain exact. Validation is exact one-file diff,
absence of `O_CLOEXEC`, presence/integer runtime check for `O_NOFOLLOW`, syntax,
unchanged synthetic verifier, static capability scan, unchanged authority
hashes, and clean ancestry. No private main or aggregate is relevant.

This proposal authorizes no code edit, classifier/evidence access, metadata or
hash retry, Codex/provider/model action, integration, push, deployment,
release, cleanup, result, or graduation. Separate immutable review is
mandatory. Accounting remains 35/41.

###### Immutable R10 unsupported-flag proposal review

Exact proposal checkpoint `cad46d95c0738e0bb58924d0715f2ed3a9cf7fa9`
has parent `c9b072bc723b4e16b9046ed8d27f04a0d66f9857`, tree
`7ba9bce35b6aecdfd2c60423198b59d3ae476ae6`, master-plan SHA-256
`6875b60b060fc6194b8b0e273725dddf33710c976a23cd5d04414171ae301a7a`,
and this-plan SHA-256
`07671089786e45db243f63c0b4f932b70a5e64ac63690fa8177517a25da990a0`.
CloserFans is clean at exact `7973127`/tree `bbf390d`; classifier, verifier,
operator, and canary hashes remain the four recorded values.

Review confirms the diagnosis from committed control flow: all accepted
metadata checks precede a guard whose second conjunct deterministically fails
because exact Node exposes no integer `O_CLOEXEC`; `openSync` is never reached.
Receipt SHA-256 independently matches the expected constant. Removing only the
unsupported guard/flag therefore corrects a harness incompatibility rather
than weakening a successful evidence check.

Under the standing unattended-approval delegation, authorize exactly one
classifier-file edit: replace the two-constant integer guard with an
`O_NOFOLLOW`-only guard and replace the three-flag open expression with
`O_RDONLY | O_NOFOLLOW`. No fallback flag, conditional child behavior,
platform branch, descriptor export, or other edit is permitted. The absence
of all child-process capability is a mandatory static gate.

Run only syntax, the unchanged full synthetic classifier verifier, the exact
Node constant projection, static capability/`O_CLOEXEC` absence and
`O_NOFOLLOW` presence checks, exact one-file diff, unchanged verifier/operator/
canary hashes, ancestry, and clean status. Do not execute the private main or
open/hash any evidence. A focused-green checkpoint remains non-authorizing
pending a separate code/access review.

This review authorizes no classifier/evidence access, metadata/hash retry,
Codex/provider/model action, integration, push, deployment, release, cleanup,
diagnosis, result, or graduation. Accounting remains 35/41.

###### R10 unsupported-flag implementation qualification

CloserFans checkpoint `d1a270e0ad244db83979416193d03b146461b7b7`,
parent `7973127ef1349d89aafbeb22756cb3aa3e08e375`, and tree
`96e705071791fba2a290cccfaa5d42ef40ce7b8b` change only
`scripts/classify-emdash-stage-a-stderr.mjs` by two insertions and five
format-inclusive deletions. The new classifier SHA-256 is
`4105a7b5fe80b9deb046a5fb4a5a6b608b5166624aa2d069ea58d01cee7e6e0e`.
Verifier, operator, and canary hashes remain `4a86abe...`, `774752d...`, and
`2b7cb75...`.

The diff removes both `O_CLOEXEC` occurrences, retains the exact integer guard
for `O_NOFOLLOW`, and opens only `O_RDONLY | O_NOFOLLOW`. Exact Node projects
`O_NOFOLLOW=131072`. Both syntax checks and the unchanged full synthetic
verifier pass. Static capability scan has no matches; `O_CLOEXEC` absence,
`O_NOFOLLOW`/`openSync` presence, exact one-file diff, whitespace, hashes,
ancestry, and clean-tree gates pass.

No private main, receipt/lease/stderr or other evidence, metadata/hash probe,
Codex/provider/model, configuration, credential, network, install, aggregate,
push, merge, deployment, release, or cleanup ran. These are omissions, not
passes. The checkpoint remains non-authorizing pending an exact code/access
review. Accounting remains 35/41.

###### Immutable R10 code/access review and sole authorization

Exact qualification checkpoint `d51b992c1fa2aa365daba5b688ebf4762c3dfb0e`
has parent `4e3c0920f9247c81b555d8fec6a326cf7589d4dd`, tree
`1465d67c0674c922149b5b050d0bd6a820f96739`, master-plan SHA-256
`5af0be1050ee8219e96e02e4f1228f72f848898ecd4298475b10d8c4705855fc`,
and this-plan SHA-256
`bedeb4b825f4bb31b68c15df1e0023313ba721405ff4147e4c17ead56e625ef2`.
CloserFans is clean at exact `d1a270e`/tree `96e7050`; classifier, unchanged
verifier/operator/canary, and Node hashes are exact.

Code/access review confirms the corrected helper now reaches `openSync` with
the supported mandatory no-follow flags. Accepted metadata `906e40f...` and
receipt digest `f7c6f85...` remain current because every diagnostic command was
read-only and both repositories are clean. Lease/stderr paths, bounds, hashes,
descriptor identity/stability, fixed stages, rules, output closure, and the
closed environment remain unchanged.

Under the standing unattended-approval delegation, authorize exactly one R10
invocation after this checkpoint:

```text
/usr/bin/env -i HOME=/home/user1 LANG=C.UTF-8 LC_ALL=C.UTF-8 NO_COLOR=1 PATH=/usr/bin:/bin /home/user1/.nvm/versions/node/v24.11.1/bin/node /home/user1/closerfans-emdash-canary-v1/scripts/classify-emdash-stage-a-stderr.mjs
```

Observe only one closed nine-key classification or three-key fixed-stage
failure line and its exit/channel shape. Every outcome is terminal; do not
retry, redirect, parameterize, or feed it to a model. This is local read-only
classification of preserved evidence, not Codex/provider/model execution.

No benchmark/proof/performance claim, integration, push, deployment, release,
cleanup, Stage B/C, or graduation is authorized. Accounting remains 35/41.

###### Terminal R10 result and bounded continuation

The sole corrected R10 invocation is consumed and terminal. It exited zero and
emitted exactly one fixed nine-key JSON record:

```json
{"revision":"getpaidx-emdash-stage-a-stderr-classification-v1","targetAuthorizationIdSha256":"e1fe31c138df2b2ea7bf33138862a579aa5064dd1d738afefaffa21602aa5250","byteCount":98,"sha256":"74cb00300ed4a4c23ba979d30d34218cd356e4bfb55b81f10a3dc832d52c56c7","utf8Valid":true,"lineCount":1,"terminalNewline":true,"matchedRuleIds":["configuration"],"status":"classified"}
```

The emitted line is 363 bytes with SHA-256
`7d22a71b0996a5da9565d9e787675bbb3c431cdc41b6171895659ac24b28536e`.
It reveals neither the terminal line nor any arbitrary substring. The result
proves only that the preserved 98-byte, valid-UTF-8, LF-terminated single line
matches the classifier's fixed `configuration` rule and no other fixed rule.
It does not establish which configuration surface failed, whether a repair is
safe, or whether a later agent attempt would succeed.

No source/evidence mutation, Codex/provider/model invocation, credential or
network access, install, aggregate, push, merge, deployment, release, or
cleanup occurred. The classifier must not be rerun. At that checkpoint the
only dependency-ready work was a local no-evidence audit of installed Codex
0.147.0's public/configuration error contracts; its result follows below. Any
classifier edit, private artifact read, new canary coordinate, or provider
retry still requires its own immutable review. Accounting remains 35/41.

###### R11 public-source preimage diagnosis and correction proposal

The no-evidence audit used the official Codex tag `rust-v0.147.0`, exact commit
`be6e8eac029b183056b7e4402879f15d2c85f61b`. The relevant exact source hashes
are:

- `codex-rs/exec/src/lib.rs`: `52d801c747c18524b42552e9da9080aa43e8eeb04b368570bb0bbfc601f613ae`;
- `codex-rs/config/src/loader/mod.rs`: `ef4e31d094943c18a995bbb9c3fd390a145a35fc561a3f74d8cd595d733e7005`;
- `codex-rs/core/config.schema.json`: `b9105f17442d5c41ba5d4d82603259d3cc0ceb38aeb3badf9e5ca20da328ae6e`; and
- `codex-rs/features/src/lib.rs`: `8437206e83806c546f9c8cf7002384c8d9be1740c1f4c78f44ef9417d7e61344`.

Those authorities are mutually decisive. Headless config-load failure emits
`Error loading config.toml: {err}`; strict CLI validation emits ``unknown
configuration field `{path}` in -c/--config override``; `ToolsToml` permits
only `experimental_request_user_input`, `update_plan`, and `web_search`; and
the stable feature catalog owns `view_image`. The committed Stage A vector
nevertheless contains `tools.view_image=false` under `--strict-config`.

Instantiating the two official error templates with that committed key yields
exactly this public-source-derived candidate, including terminal newline:

```text
Error loading config.toml: unknown configuration field `tools.view_image` in -c/--config override
```

It is exactly 98 bytes and has SHA-256
`74cb00300ed4a4c23ba979d30d34218cd356e4bfb55b81f10a3dc832d52c56c7`,
identical to R10's independently recorded artifact byte count and digest.
This establishes the exact terminal cause by equality of immutable bytes; the
private artifact was not opened or reread, and no substring classifier is
needed.

Freeze the narrowest correction as non-authorizing:

1. in `templates/emdash_benchmark/scripts/emdash-canary-contract.mts`, remove
   only `tools.view_image=false` from the `-c` configuration list and add
   `--disable`, `view_image` beside the existing fixed feature disables;
2. in `templates/emdash_benchmark/scripts/verify-emdash-canary.mts`, add
   `view_image` to the exact disabled-feature assertion and assert that the
   stale `tools.view_image` key is absent;
3. retain `--strict-config`, every permission profile, closed environment,
   model/prompt/schema/output coordinate, capability boundary, receipt, and
   all other argument bytes unchanged; and
4. run only syntax/typecheck and the nearest fake/synthetic canary contracts.
   A separately proposed no-model config/permission probe may follow the
   implementation checkpoint; no real Codex/provider retry or new
   authorization coordinate follows from this proposal.

Separate immutable review is mandatory before either file is edited. No
private evidence, Codex/provider/model execution, credential, network,
install, aggregate, push, merge, deployment, release, or cleanup is
authorized. Accounting remains 35/41.

###### Immutable R11 correction review

Exact proposal checkpoint `9d722d4a5a9e3d95d23d5a65d554885c2683455b`
has parent `b6b15638116a428ef93fb1328a1059afd92c9f00`, tree
`c999e9995742c06a65377d5424f4eab0369e93aa`, master-plan SHA-256
`0f2bb32897332196d057a35512a0f604d574c393cc90e9b4b86d73ef44f032c3`,
and this-plan SHA-256
`e882ce7ef7d99fb074bb88f3f4ad2270992263f86f77d41fb667ac4e1d5a7c17`.
Both project worktrees are clean at the recorded checkpoints.

Review approves exactly the proposed two-file correction. Codex 0.147.0's
own catalog marks `view_image` stable and the public CLI maps `--disable NAME`
to `features.NAME=false`; the same argument surface already owns eight nearby
canary disables. Removing the rejected `tools.view_image` pair and adding the
supported feature pair therefore preserves deny-by-construction intent while
retaining strict validation. Adding `view_image` to the verifier's closed
disabled-feature list plus an explicit stale-key absence assertion proves both
sides of that move.

No permission-profile value changes, so `permissionProfileDigest` semantics
remain exact. The complete argument-vector digest will intentionally change;
therefore the consumed v3 lease/authorization/run root cannot be reused or
relabelled. This review authorizes only the two source edits and fake/synthetic
validation. It does not authorize the live permission probe, private evidence,
a new authorization ID/run root, or any Codex/provider/model invocation.
Accounting remains 35/41.

###### R11 implementation qualification and R12 parse-probe proposal

CloserFans checkpoint `8a5c2f93080d828e73a1547ead8f5a6c870e0325`, parent
`d1a270e0ad244db83979416193d03b146461b7b7`, and tree
`d3e9aa900b5ac7a1efc014f33064769b316b0e40` implement exactly the approved
two-file diff: eight insertions and one deletion. The contract SHA-256 is
`1973d6a761adb56d752c99dd1c5f321ecc290a72d1d7785565bc87ff93fe867b`;
the verifier SHA-256 is
`4b3d76e72c330a6710b599e5247b21eb93ba443e0b952ff9a1d8944438d39d58`.
The stale config key is absent, supported `--disable view_image` is present,
and the exact synthetic assertions cover both facts.

The owning focused `--canary-only` gate passed from a disposable clean
installation. It includes template typecheck, Stage A synthetic containment,
replay and failure paths, and the public mock CLI. It invoked no model. Both
worktrees are clean, and no dependency tree was created in the isolated
CloserFans worktree. Repository-wide checks remain omitted by design.

That qualification does not yet justify the live permission probe. Source
review found that its current `configParse` check executes the full root option
prefix followed by `exec --help`. Clap satisfies help while parsing arguments,
before `codex_exec::run_main` loads strict configuration. The historical green
check therefore was not evidence that the full strict stack deserialized; the
consumed v3 failure is concrete counterevidence.

Freeze R12 as a non-authorizing one-file correction to
`templates/emdash_benchmark/scripts/probe-emdash-canary-permissions.mts`:

1. pass the complete `buildCodexArguments(...)` vector to the existing closed
   `capture` helper instead of replacing its execution tail with `exec --help`;
2. keep stdin attached to the helper's existing ignored/EOF channel and
   require exact exit 1, empty stdout, and exact fixed stderr `No prompt
   provided via stdin.\n`;
3. retain the disposable empty host home, closed environment, 30-second bound,
   all later permission/network/allowlisted-command probes, and cleanup; and
4. validate the source edit only with typecheck and the focused synthetic/mock
   canary gate. The actual `--permission-probe-only` invocation remains a
   separate review after checkpoint.

Codex 0.147.0 source establishes the ordering: strict configuration loads
before prompt resolution, while schema loading and agent/session/provider work
follow a nonempty prompt. With empty fake state and no inherited credentials
or API environment, the exact no-prompt outcome is a local no-model boundary,
not a benchmark attempt. Separate immutable review is mandatory before the
one-file edit. No live probe, private evidence, new coordinate, provider/model,
network, aggregate, integration, release, or cleanup is authorized. Accounting
remains 35/41.

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
3. preserve the concurrent CloserFans branch at `8980842` and its original-
   worktree untracked template copy; do not absorb, reset, or clean either;
4. keep only one semantic row active;
5. treat 12B1 as complete at exact checkpoint `d0d3764`;
6. treat exact 12B2 proposal/review/implementation checkpoints
   `ba49705`/`8c9652a`/`93c9804` as complete; treat 12B3 proposal/review,
   package source, permanent hardening, and locally integrated host checkpoints
   `bb16e47`/`0027c66`/`995e497`/`3af518d`/`cbf2356` as complete; treat the
   12B4 audit, exact proposal `286a50d`, immutable corrected review, and local
   mock implementation checkpoints `1d77473`/`8e270a7` with final tree
   `9fc93af` as non-graduating Stage A preparation only; treat the second
   preflight above as a deliberate no-call result and its corrective one-shot
   driver design as approved only for local code and fake/no-model tests under
   the immutable review above; treat corrective CloserFans checkpoint
   `1abdfd8`, tree `5912793`, and final-review correction `4faef78`, tree
   `a5e72dd`, as the focused-green implementation of that approval; treat the
   immutable corrected-driver review above and authorization checkpoint
   `4e39600` as historical authority for the now-consumed operator invocation;
   treat receipt `cb02d50` as a terminal no-call `login-category` refusal; and
   treat R1 proposal `58ff991` and its immutable review as authority only for
   the exact three-file local correction and fake/no-model tests; treat the
   evaluator-launch amendment `3f5e428` and its review as authority for only
   the fourth clean-evaluator launch edit and default-long-path regression;
   treat scheduling proposal/review `2b23877`/`5a31712` and CloserFans
   checkpoint `a6b5e61`, tree `fe50a80`, as the focused-green four-file R1
   implementation; treat R2 proposal/review `a92c16c`/`8f0cf31` and
   CloserFans checkpoint `8276e96`, tree `e03085a`, as only the focused-green
   v2 allowlist rotation; treat authorization checkpoint `bf94f6b`, receipt
   `c97c1f8`, and lease `6dce7e8` as a terminal one-shot spawned
   `process-failure` with no benchmark result and no retry authority; treat
   R7/R8/R9/R10 proposal, review, implementation, qualification, and consumed
   diagnostic checkpoints through Emdash `5b8e4ba`, CloserFans `d1a270e`,
   and tree `96e7050` as local privacy-preserving diagnosis only; treat R10's
   sole 363-byte record `7d22a71...` as terminal proof that the preserved
   98-byte line matches only fixed category `configuration`; never rerun any
   consumed command or inspect the private line directly; treat the official
   Codex 0.147.0 source-preimage equality above as exact diagnosis of stale
   strict key `tools.view_image` without another evidence read; treat exact
   proposal/review checkpoint `9d722d4` and the immutable review above as
   authority only for the two-file local correction and synthetic tests;
   treat CloserFans `8a5c2f9`, tree `d3e9aa9`, as the focused-green R11
   implementation and the R12 text above as non-authorizing until separately
   reviewed; and
   forbid any retry or alternate coordinate without the amended implementation
   checkpoint, new code/preflight review, and new coordinates; and
7. synchronize both plans and exact evidence before every rollback-safe
   commit.
