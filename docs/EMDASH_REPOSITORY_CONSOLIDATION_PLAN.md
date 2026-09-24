# Repository and Context Consolidation

Date: 2026-09-24
Status: post-completion validation repair and main integration in progress
Baseline: `2248ae2ebc3a3ac33920f8607497db26198c331c`
Branch: `goal/repository-context-consolidation`
Worktree: `/home/user1/emdash1-repository-consolidation-v1`

## Objective and authority

Make current instructions, mathematical qualifications, source owners,
validation commands and relevant prior decisions easy to find, while preserving
the existing mathematical and book architecture. Implement the bounded
recommendations in the
[accepted reassessment](EMDASH_DEVOPS_CONSOLIDATION_REVIEW_2026-09-23.md#broader-repository-and-ecosystem-reassessment).
This plan owns execution and current task status; the review owns rationale.

Follow [root guidance](../AGENTS.md), the [formal SOP](../emdash2/AGENTS.md)
and the [persistent-goal workflow](PERSISTENT_GOAL_GIT_EXPERIMENTATION.md).
The user's 2026-09-24 instruction authorizes this dedicated local branch/worktree,
implementation and validated checkpoint commits. Transfer the six accepted
review documents from main without absorbing unrelated work. Preserve the
originals until their contents are verified in a checkpoint, then remove only
those verified duplicate working changes from main.

The initial maintenance pass ran no full aggregate, at the user's direction.
The user subsequently ran `npm run check:all`, supplied its five TypeScript
failures and authorized corrections, local checkpoints and fast-forwarding
main. This integration follow-up first reproduces/fixes the affected suites,
then runs one complete TypeScript gate after focused checks are green. Reuse
evidence for unchanged boundaries; do not launch unrelated formal/print
aggregates. The later profile/laxness integration and Op/variance repairs remain
explicitly separate future work.

This goal does not select mathematical changes, diagnostic/nucleus splitting,
book regeneration, toolchain/package upgrades, hosted operations, benchmark
canary retries or a general orchestration/search system. Local checkpoints
do not authorize pushing, publishing, PR creation, history
rewriting, branch deletion or worktree removal. Inspect siblings read-only;
their integrations remain separately scoped. The latest user request separately
authorizes only a fast-forward of main after the correction/integration checks.

## Bounded work and acceptance

| Row | State | Deliverable and acceptance |
| --- | --- | --- |
| 0. Preserve the accepted review | Complete | Isolated worktree, bootstrapped dependencies, resource locator and reconciled original-stage status; exact staged docs/links pass; source worktree preserved |
| 1. Current guidance | Complete | Short elaborator handoff and report index, preserved historical receipts and lifecycle registration, concise AGENTS routing with mandatory mathematical/resource rules intact; exact links, anchors and report checks pass |
| 2. References and template lifecycle | Complete | Repair the undeclared HoTT Git link without losing source/provenance; clarify local checker-source mismatch and classify the three templates/canary with exact integration boundaries; no sibling merge or unique-evidence deletion |
| 3. Minimal test observability | Complete within focused qualification | Execution-order progress, durations and a parent heartbeat using existing runner/log infrastructure; controlled pass/fail/slow/cancellation cases pass; unchanged test selection and exit semantics; no full run |
| 4. Final review and handoff | Complete | Current task routes resolve, retained history is recoverable, focused gates pass, final qualification limits and checkpoints are recorded; final documentation checkpoint leaves the worktree clean |
| 5. User-run failure repair | Focused qualification complete | Reproduce five failures, restore required concise release guidance, align SCALE provenance with reviewed canonical commands and test frozen PathInd positions at their exact historical source; focused checks and checkpoint |
| 6. TypeScript integration and main | In progress | One complete corrected TypeScript gate, relevant bounded conformance/tooling checks, synchronized evidence, clean exact staged diff and authorized fast-forward main; no push |

Keep one bounded row in progress. Split a row only if a concrete dependency
requires it; do not grow this table into an additional project-status database.
Reference/template work is classification and local repository repair, not a
requirement to upgrade or integrate every older example.

## Document ownership and retrieval

- Root/nested AGENTS retain mandatory rules and task-specific entry points.
  Their essential contract includes whole internal operations, generic
  computation owners, explicit strict/lax/pseudo profiles and assumptions,
  runtime versus proof-time rules, owner-position controls, warning analysis,
  negative consumers and bounded diagnostic/resource policy.
- The elaborator handoff owns concise current TypeScript orientation and
  routes to its active/deferred plans. Historical qualification receipts stay
  dated and explicitly separate from today's transferred profile.
- The current architecture report owns detailed implementation status and
  owners; Foundations explains the mathematics. The report index routes to
  them and preserves its machine-checked lifecycle sections.
- Preserve unique decisions, counterexamples and replay recipes in tracked
  history or a compact summary with exact Git provenance. Do not put their
  only copy in ignored `.scratchpad`. Search history explicitly; do not hide
  active authorities with broad ignore rules.
- The existing book manifests, evidence, bibliography and third-party ledger
  retain their responsibilities. The local resource locator is optional host
  inventory, not another bibliography or build prerequisite.

For history extraction, retain exact dated content and fix relative links.
Inspect inbound heading references before replacement; preserve useful anchors
or retarget their consumers. Verify that current routing can answer: which
theory/profile applies, where is its owner, which command checks it, what
counterexample/deferral matters, and where is the relevant prior decision?

## Validation and checkpoints

Documentation rows use exact staged/unstaged diff review,
`./scripts/emdash dev docs`, changed heading/fence checks and
`python3 emdash2/scripts/lint_report_headers.py` when the index changes.
No new test suite is needed for prose. Check lifecycle membership preservation
directly when shortening the index.

The Git-link repair first inventories consumers and verifies the retained
external source revision and clean state; then inspect clone/index semantics
and book provenance references without rendering the book. Generated outputs
are not hand-edited.

For observability, inspect the actual runner and Node version, select a small
baseline, and exercise controlled workloads under explicit short deadlines.
Run owning lint/type checks as appropriate to changed implementation. Preserve
test registration, failure exit status and cancellation cleanup. A live event
is progress evidence; a heartbeat alone is only process liveness. Calibrating
the full suite's deadline remains deferred at user direction.

At each coherent checkpoint synchronize this ledger, stage only owned paths,
inspect the exact staged diff and run its proportional checks. Prefer correcting
commits over rewriting history. Carry forward validation for unchanged rows.

## Decisions and receipts

- Start: no active persistent goal existed. Main contains only the six accepted
  review-document changes; all other 62 registered worktrees are clean. The
  milestone `f76e8ac9` is an ancestor of baseline `2248ae2e`.
- Recovery: the existing hook archive verifies 1,260 responses. The user's
  linked latest response is recovery evidence for the accepted review, not a
  replacement for this plan or active authorities. No hook change is needed.
- Scope: improve navigation before adding tooling. Leave mathematical repair
  readiness explicit without making it a completion requirement for this goal.
- Row 0: the six review documents were copied byte-for-byte to the isolated
  worktree. `./scripts/bootstrap-worktree.sh` passed using pnpm 11.16.0 and
  Node 24.11.1; all 373 packages came from the shared store. The optional pnpm
  update-notice request failed, but install and workspace verification succeeded.
  Document hygiene and exact staged review qualify this documentation checkpoint.
  Checkpoint `8ec1a8e9` preserves the accepted review and this plan. Main's
  six duplicate changes were compared with that commit before clearing them;
  main is clean at the unchanged baseline.
- Row 1: checkpoint `7bb3277f`; the handoff is 116 lines (was 3,015); the report index is 127 (was
  1,351); nested AGENTS is 547 (was 749). History snapshots retain the original
  handoff/index content exactly after reversible relative-link rebasing.
  Mandatory editing/rule/resource/validation/recovery sections from
  `Starting A v3.2 Task` onward are byte-identical. Removed owner/status
  narration is retained separately; consumer safeguards remain in the SOP.
  Lifecycle membership is unchanged (8 active, 19 completed, 1 deferred,
  1 superseded). Document checks pass 257 local links and 8 heading links.
  A narrow `.rgignore` excludes only extracted history and assembled book
  Markdown; default source discovery and explicit history retrieval both pass.
- Row 2: checkpoint `4fc302a4`; no executable consumer needs the hidden HoTT checkout. A clean,
  independently stored `/home/user1/hott-book` now preserves the exact book
  pin and upstream origin. The original main checkout is untouched. Removing
  the malformed Git link changes `git submodule status` from a missing-mapping
  error to success; the book tree and attribution are unchanged. The resource
  locator includes optional acquisition and the checker-source mismatch.
  Template dispositions are accepted in the existing review: primary starter,
  optional graph view, parked developer benchmark/canary with a concrete reopen
  condition. Sibling trees remain unchanged, including unrelated CloserFans
  work. All 98 local document links pass. No runtime, render or aggregate was run.

- Row 3 design: use Node's existing multiple-reporter support. Keep the normal
  spec result report and add a compact reporter in the separate test-runner parent: periodic current
  activity plus durations for slow completions. Its heartbeat must remain
  responsive while a test worker is CPU-bound. Preserve the existing Python
  gate deadline/process-group cancellation, test entry point and concurrency.
  No monitoring service, sidecar database or custom runner is needed.
- Row 3 results: checkpoint `ef8d374d`; the 54-line reporter emits a 30-second parent heartbeat,
  last execution event/age, and slow or unsuccessful completion durations.
  Test membership, concurrency, gate deadlines and exit authority are unchanged.
  `node --test scripts/test-progress.test.mjs` passes three controlled cases
  covering pass/skip/todo, execution-order failure and heartbeat during a
  synchronous 5.1-second worker computation. The 12 Python DevOps tests pass,
  including actual process-group deadline cancellation of a busy Node worker
  with a timeout receipt and no running worker afterward. The existing Node
  registration regression passes; all 453 TypeScript suites remain reachable.
  The three signature-reference TypeScript tests pass through the real loader
  and both reporters under a 45-second outer bound (4.08 seconds observed).
  Root typecheck, changed-script ESLint, workspace and document checks pass.
  Reporter regression tests are wired into existing `ci-tooling`. No aggregate
  or mathematical source check is claimed; full-runtime calibration remains open.
- Row 4: final baseline-to-branch document audit passes 299 local links across
  14 changed Markdown files, 18 heading links, fence/whitespace checks and
  active-reference lint. Lifecycle membership and mandatory formal SOP sections
  remain intact; scoped current search and explicit history recovery work.
  Mathematical/TypeScript source, root TypeScript tests, book/renderer source,
  lockfile and toolchain are unchanged. All 64 registered worktrees were
  inspected; only this final goal-owned documentation slice was dirty. Main is
  clean at baseline; the sibling CloserFans change remains untouched.

## Completion boundary

The selected maintenance rows are complete and locally checkpointed. The final
documentation checkpoint synchronizes their status; preceding implementation
checkpoints are `8ec1a8e9`, `7bb3277f`, `4fc302a4` and `ef8d374d`.
The dedicated branch/worktree remain for review. No push, main integration,
publication or worktree removal was performed.

The full TypeScript aggregate, runtime calibration and hosted CI qualification
remain incomplete/deferred under the user's instruction. This is focused
maintenance qualification, not a full integration or release claim. Future
mathematical profile/variance work and any sibling integration require their
own scope and acceptance criteria. The accepted future-design reference and
template reopening conditions remain in the linked review; they are not an
automatic continuation queue for this completed goal.

## User-run validation follow-up

The user's run at `58451168` completed the TypeScript test phase in
2,407.575 seconds (about 40 minutes): 2,923 tests, 474 suites, 2,833 passes,
five failures, 85 skips and no cancellations. The five failures are two
handoff/release contract assertions, two SCALE representation/proposal ordinal
assertions and one historical PathInd proposal position assertion. Since
`check:all` chains its stages with `&&`, this was not a completed conformance or
formal CI run. It is one full-duration observation, not a general timing SLA.

A bounded serial reproduction of the five owning test files reports the same
five failures (34 tests: 28 pass, five fail, one skip; 63.03 seconds). Source
and all worktrees were clean before this follow-up; main remains an ancestor.
The two handoff omissions were introduced by the navigation cleanup. SCALE's
acquisition contracts already contain the reviewed new ordinals, but the
corresponding IR provenance still used the old ones. PathInd's immutable
proposal must retain its historical source identity instead of relabeling it
as a current-source proposal.

Corrections restore the exact MVP profile, completion status and retained
Lambdapi/metatheory boundaries in a concise handoff. All five owning suites
then pass (34 tests: 33 passes, one opt-in skip; 51.14 seconds). A further
focused acquisition/SCALE/audit run enables the live oracle controls and passes
all 31 tests with no skips in 40.67 seconds, including the new constructor
provenance checks. Its bounded positive and negative Lambdapi consumers pass.
A fresh serial 2 GiB/60s canonical export exactly matches the previously
reviewed source/export hashes `f7206b8e…` / `594bbfa4…`; none is changed to
silence a failure. Historical PathInd source is explicitly SHA-256 checked.
Root typecheck, changed-owner lint, workspace and document hygiene pass.
The correction logs are under ignored `emdash2/tmp/probes/consolidation-repair-*`.

## Original persistent goal prompt

This prompt records the completed maintenance scope. The later user-run
validation/integration authorization above supersedes its no-aggregate and
no-main-integration boundary for rows 5–6 only.

Complete the bounded repository/context consolidation governed by
`docs/EMDASH_REPOSITORY_CONSOLIDATION_PLAN.md` in
`/home/user1/emdash1-repository-consolidation-v1`, on
`goal/repository-context-consolidation`. Let that living plan own specifics,
ordering, acceptance, decisions and recovery. Follow the repository authorities
and persistent-goal Git workflow, preserve unrelated work, and make validated
local checkpoints as coherent rows finish. Do not run full aggregates or timing
calibration; keep the remaining aggregate evidence explicitly incomplete.
Profile/laxness integration, variance/Op repairs, sibling integrations, pushes,
publication and worktree cleanup remain outside this goal. Continue until the
selected rows are completed or resolved with concrete evidence and the final
handoff is synchronized.
