# Repository DevOps

The implementation and validation ledger is the
[consolidation plan](EMDASH_DEVOPS_CONSOLIDATION_IMPLEMENTATION_PLAN.md).
The [review](EMDASH_DEVOPS_CONSOLIDATION_REVIEW_2026-09-23.md) records the design
and outside comparisons. Root and nested AGENTS instructions continue to govern
mathematical scope and proportional validation.

## Daily commands

From any directory in this checkout, the existing `scripts/emdash` entry point
now provides an inexpensive Python DevOps branch:

```bash
./scripts/emdash dev doctor
./scripts/emdash dev doctor --formal
./scripts/emdash dev doctor --print
./scripts/emdash dev targets
./scripts/emdash dev check --explain
./scripts/emdash dev plan --base main
./scripts/emdash dev check --gate tooling
./scripts/emdash dev status
./scripts/emdash dev status --claim TT-EQUALITY-INDUCTION
```

Use the appropriate relative or absolute path to `scripts/emdash` when outside
the Git root. `doctor` reads prerequisites; it does not install packages.
`--formal` compares the installed checker/compiler and dependency versions with
the verification manifest. Exploratory environments can still run explicit
checks, but their evidence keeps its actual tool identity.

Root contributor tests verify the completed PathOut audit against its local Git
snapshot `a05493b49a1ef49c18ffe921725dd1ce56f21647`, then compare the selected
owners with current source. Keep that commit available in shallow checkouts;
CI uses `fetch-depth: 0`. These historical tests are outside the distributed
package's runtime and its external-install smoke test.

`pnpmw test` keeps Node's normal result report and adds compact progress on
stderr through [test-progress.mjs](../scripts/test-progress.mjs). Every 30 seconds
the separate test-runner parent reports elapsed time, the last execution event
and its age. Slow completions (at least five seconds) and unsuccessful
completions report their duration immediately. The reporter uses Node's
[execution-order events](https://nodejs.org/download/release/v24.11.1/docs/api/test.html#class-testsstream);
the ordinary result report can wait for an earlier-declared test to finish.
The event counter includes suites and is not the final test total. A heartbeat
establishes parent liveness, not worker progress or a detected hang.

Gate execution retains both streams in the printed `emdash2/logs/devops/` log;
inspect that file during a long run. `EMDASH_TEST_PROGRESS_INTERVAL_MS` optionally
sets the reporting interval (50–3,600,000 ms); it does not change a test or gate
deadline. To use the same reporter on one focused file, run:

```bash
node --require ts-node/register --test \
  --test-reporter=spec --test-reporter-destination=stdout \
  --test-reporter=./scripts/test-progress.mjs --test-reporter-destination=stderr \
  tests/v3_2_algebra_formal_signature_reference_tests.ts
```

The existing one-hour TypeScript gate limit is provisional. Full-suite runtime
calibration and the incomplete aggregate remain deferred at the user's request;
focused reporter/fixture results do not close that qualification boundary.

`plan`/`check --explain` show selection without executing gates. Without `--base`,
selection covers staged, unstaged and untracked nonignored work. With `--base`,
it also covers the commit comparison. Rename detection is disabled for this
inventory so both the removed and added paths participate. `check` executes
the selected gates serially; `--gate NAME` deliberately runs one focused gate.
`--full` selects every integration/release gate and is reserved for a boundary
that actually requires it.

## Operational ownership

| Owner | Contract |
| --- | --- |
| [devops/gates.json](../devops/gates.json) | Gate commands, input scopes, deadlines, prerequisite tools and conservative change selection |
| [emdash2/checks.json](../emdash2/checks.json) | Formal source/reviewer membership, ordinary check order, health priorities, staged groups and named resource profiles |
| [check_registry.py](../emdash2/scripts/check_registry.py) | Validate registration and resolve exact local LP import closures, including package configuration |
| [run_lambdapi.py](../emdash2/scripts/run_lambdapi.py) | Guarded source checks, exact input retention and execution receipts |
| [check_metrics.py](../emdash2/scripts/check_metrics.py) | Health inventories, execution summaries and conservative successful-result reuse |
| [test registration](../scripts/check-test-registration.mjs) | Require every root `*_tests.ts` suite to be reachable through runtime imports from the aggregate |
| [verification.json](../toolchains/verification.json) | Reviewed Lambdapi commit, OCaml version, opam repository and installed dependency-version capture |

The ordinary `make check` suite and full health suite retain distinct scopes.
`make examples` runs registered reviewers. `make ci` is the full formal and
document-contract gate. `make ci-tooling` runs infrastructure tests without
running the mathematical library. Root `check:ts` includes test registration.
Root `check:all` keeps its existing TypeScript/MVP-conformance/formal meaning;
it is not an alias for every package, renderer and publication check.

Registration is explicit. A new active LP owner or reviewer must be added to
the registry, even when another source imports it. Temporary probes and
non-library audits do not become positive library targets through discovery.
The dependency resolver handles the repository's local `require` forms and
fails closed on unresolved/external or unsupported import syntax.

## Resources and receipts

Source checks and probes share the default 2 GiB/90-second guard. Registered
native profiles retain their reviewed GC/deadline/memory settings; an unrelated
temporary file with the same basename does not acquire those exceptions.
Existing explicitly bounded environment overrides remain visible in receipts.
Subject reduction cannot be disabled through the guarded entry points.
The OS-guard integration tests target Linux; the published/browser-safe checker
keeps its existing runtime boundary and does not acquire Python or Lambdapi.

Staged compiled-parent recipes retain their source-copy and invocation order.
The guard applies to each checker, without nesting a serial lock around a
whole group. Group timings cover prerequisites and must not be read as individual
target measurements. TypeScript export helpers also use the guard. Opt-in
conformance test files execute serially, with their existing individual checker
deadlines and a separate 600-second outer suite deadline.

New source/group receipts and raw logs are in ignored
`emdash2/logs/check-runs/`. Content-addressed input blobs are in
`emdash2/logs/check-inputs/`; they retain generated probes even after their
temporary directory is removed. Gate-level logs and receipts are in
`emdash2/logs/devops/`. Archive receipts with the blobs and tool identities they
reference. These stores are not automatically pruned during checks.

Receipts distinguish fresh success, failure, timeout, allocation failure,
unknown-cause termination, contention and input changes as applicable. A killed
process is not automatically classified as an allocation failure. Unchanged
source contents alone do not establish an identical execution environment.
Health reuse also fingerprints imported sources, package resolution, compiled
objects when present, checker bytes and relevant runner/profile files. The
earlier incomplete resume schema is rejected.

The generated health table explicitly labels inventory-only rows `not-run`.
Refreshing that source inventory is:

```bash
python3 emdash2/scripts/check_metrics.py --no-check --write-report --brief
```

That command does not establish a successful formal pass. `make health` remains
the explicit checked/resumable route. Receipts are operational evidence relative
to the recorded theory and profile, with the existing foundational qualifications.

## CI and reproducibility

[Validate repository](../.github/workflows/validate.yml) runs on PRs and pushes
to main. It selects from a prior successful main validation, so cancelled or
failed intervening pushes do not disappear from the comparison. Without a
qualified available baseline, it selects the full gate set. Changes to validation
policy also require full qualification. It calls the gate selector and retains receipts/logs/inputs for
14 days. The final `Repository validation` job fails if planning or any selected
gate failed, was cancelled or was missing. Maintainers can make this named check
required through repository rulesets; no remote ruleset change is made by this
implementation.

Documentation-only changes select document hygiene. Formal source/toolchain
changes select the full formal and relevant conformance gates. Changes to shared
TypeScript semantic code widen conformance. Unknown paths select all gates.
Selection is intentionally conservative; it is not a proof of minimal change
impact. The validation workflow makes no checkpoint, merge or npm publication.
A successful main push validation can trigger the existing Pages publication
route described below; no push or deployment is performed by local checks.

CI uses a pinned OCaml setup action and the
[verification installer](../scripts/verification-toolchain.py). To reproduce
the formal environment locally, create a separate opam switch for OCaml 5.4.0,
activate it, then explicitly opt into installation:

```bash
EMDASH_INSTALL_VERIFICATION_TOOLCHAIN=1 python3 scripts/verification-toolchain.py install
python3 scripts/verification-toolchain.py verify
```

The installer changes the selected switch/repository configuration. Do not use
it to replace an exploratory switch unintentionally. To update dependency pins
after a separately qualified upgrade, use `capture`, review its exact diff, and
review the source commit/repository pins separately. Source/version pins are
not a claim of identical operating-system images or binary bytes; actual checker
bytes are recorded with each execution.

## Book and publication boundaries

The emdash book already owns its architecture in `book.json` and
`expansion.json`, its prose and style in chapter sources and `STYLE.md`, and
its claims in `evidence.json`. Its Markdown/KaTeX/Arrowgram/Paged.js renderer
and existing source, typography, browser and PDF gates remain in use.

`dev status --claim ID` projects the existing evidence entry and locates recorded
executions for its reviewers. It neither creates a second claim registry nor
upgrades the book's status categories. A displayed historical execution must be
revalidated against current inputs and the requested profile before reuse.

Package, reviewer, render and publication gates are separately named. Existing
book/article promotion scripts remain their artifact owners. The reviewer gate
builds once and produces `validation.json` with source/run identity and every
bundle file's digest. Pages downloads that exact successful workflow attempt's
artifact, verifies its identity and bytes, then deploys without rebuilding.
Only the deploy job receives Pages write and OIDC permissions.

Automatic publication accepts successful pushes from this repository's main
branch. It skips an older artifact when newer main changes affect the reviewer;
unrelated documentation changes do not cause an unnecessary rebuild. PR/fork
artifacts cannot enter this route. A manual Pages dispatch now takes a successful
main validation run ID; it fails if its reviewer artifact has expired or is absent.
An explicitly selected older valid run can be used for a deliberate rollback.

These workflow changes need their first hosted run after an authorized push
before any hosted-success claim can be made. Existing remote rulesets and
environment approvals were not changed.
