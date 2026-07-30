# TypeScript Test Parallelism Qualification Plan

Status: deferred, measured side plan; no optimization row is selected for
implementation.

## Purpose

Reduce the wall time of the root TypeScript integration gate without changing
test semantics, losing shared expensive-compilation coverage, hiding failures,
or making the default unsafe on a developer laptop.

This plan was opened after the 2026-07-29 `check:ts` gate took 720.76 seconds
for 1,071 tests: 1,023 active passes, 48 intentional skips, and zero failures
on a 20-core host.

## Current Execution Model

`package.json` invokes:

```text
node --require ts-node/register --test tests/main_tests.ts
```

As measured on 2026-07-30, `tests/main_tests.ts` statically imports 182 test
files. The tree contains 183 `*_tests.ts` files in total; the aggregator itself
is the sole file not imported by the aggregator. Node therefore sees one test
file and executes all registered tests on one application thread. The
repository benefits from one process-wide TypeScript module cache, but several
older categorical profile compilers reconstruct the same immutable prerequisite
graphs on every call.

Node 24 can execute separate test files concurrently only under process
isolation. `--test-concurrency` controls the number of child-process files;
its default is available parallelism minus one. With
`--test-isolation=none`, all files share one process and file concurrency is
forced to one. Therefore merely replacing `main_tests.ts` with 182 file
arguments would trade shared caches for up to nineteen concurrent
TypeScript/kernel-loading processes on this host.

## Bounded Audit

Static inspection found:

- no test file imports another `*_tests.ts` file; `main_tests.ts` is the only
  aggregator;
- test files read opt-in environment flags but do not mutate them;
- temporary Lambdapi probes use isolated temporary directories; and
- process isolation is structurally plausible, but it duplicates ts-node
  transpilation and expensive imported transfer-fragment construction.

The first representative benchmark on 2026-07-29 deliberately used only two
independently green but expensive files:

```text
node --require ts-node/register --test --test-concurrency=2 \
  tests/v3_2_categorical_displayed_nd_higher_foundation_transfer_tests.ts \
  tests/v3_2_categorical_displayed_nd_higher_target_tests.ts
```

Observed result:

```text
14/14 tests passed
wall time: 167.61 seconds
reported maximum resident set: 728,956 KiB
```

The same suites had recently taken approximately 41 and 72 seconds in their
individual focused runs, about 113 seconds combined. Even two isolated
workers were therefore roughly 48% slower in this cache-heavy sample, and
the foundation suite alone slowed to 63 seconds under contention. Naively
using Node's nineteen-worker default is not a safe quick optimization.

### Follow-up attribution

The 2026-07-30 follow-up used a fairer shared-process control and
`ts-node/register/transpile-only` so the comparison did not sum two isolated
runs that each rebuilt their common prerequisite:

| Probe | Wall time | Observed maximum resident set |
| --- | ---: | ---: |
| Foundation and target suites in one shared process | 99.75s | approximately 491 MiB |
| The same suites in two isolated workers | 119.76s | approximately 450 MiB reported maximum; aggregate child RSS unavailable |
| Full aggregator with every test body skipped, ordinary ts-node | 86.23s | approximately 848 MiB |
| Full aggregator with every test body skipped, transpile-only | 82.41s | approximately 516 MiB |

The two-worker run was therefore about 20% slower than the fair serial
control. Transpile-only execution materially reduced memory but only modestly
reduced full discovery wall time.

Instrumentation of the 182 direct imports attributed approximately 66.86
seconds to module acquisition. Three eager top-level fixtures accounted for
approximately 59 seconds:

| Test module | Top-level cost |
| --- | ---: |
| `v3_2_categorical_text_internal_action_audit_tests.ts` | 34.18s |
| `v3_2_categorical_text_displayed_constructor_audit_tests.ts` | 18.78s |
| `v3_2_categorical_text_parity_tests.ts` | 6.48s |

Each constructs a `CoreCategoricalProgram` before any test callback runs.
Consequently even a name-filtered aggregate pays for expensive profiles whose
test bodies are all skipped. Loading all 170 exports of the public `src/v3_2`
barrel directly took approximately 4.96 seconds; the barrel is not the primary
serial bottleneck.

The non-test portions of `check:ts` are also not the long phase:

| Command | Serial wall time |
| --- | ---: |
| `workspace:check` | 0.72s |
| `typecheck` | 12.18s |
| `lint` | 10.88s |

Running typecheck and lint concurrently took 20.40 seconds rather than about
23.06 seconds serially. That small saving does not justify making orchestration
parallelism the first implementation.

### Repeated semantic compilation

The strongest bounded attribution is an identical repeated call to
`compileCoreCategoricalFibredTransfdTransfer()` in one process:

```text
first call:  6.380s
second call: 5.657s
```

The second result has the same six declarations and seven runtime rules, yet
the current function recompiles its binder prerequisite, declarations,
runtime fragment, and proof program. Static inspection found the same pattern
in the older zero-argument dependent, structural, comprehension, fibred
product, fibred structure, binder, transfd, and weaken/reindex profile
compilers.

Caching is compatible with the existing architecture:

- newer displayed-evaluation, displayed-chain, dependent-target, chain-2A,
  and higher-ND compilers already keep a module-local successful compilation;
- compiled declaration modules, declaration environments, mixed contexts,
  runtime fragments, runtime programs, and proof programs are immutable;
- declaration-environment extension is persistent and returns a new
  environment;
- categorical program construction still creates fresh program/builder state;
  and
- no test was found that mutates a compiled profile or requires fresh
  compilation-result identity.

This identifies the primary problem as duplicate immutable semantic
compilation, followed by eager fixture construction. It is not primarily a
shortage of Node test workers.

## Deferred Recommended Optimization

All work below remains deferred. This plan records the dependency order but
does not authorize a source, test-runner, package-script, dependency, or
command change.

### 1. Complete process-local compilation caching

Extend the existing local `cachedCompilation` pattern to the older pure
zero-argument profile compilation functions. Keep the implementation
mechanical and local; do not introduce a general cache framework merely for
this tranche.

The qualification must establish that:

1. only a completely successful compilation is cached;
2. failures are never cached;
3. returned declarations, environments, runtime fragments, and proof programs
   remain frozen/persistent;
4. fresh categorical programs and checker-facing state remain isolated;
5. order-independent focused suites retain the same results; and
6. no test contains a wall-clock timing assertion.

### 2. Defer expensive test fixtures until their suites execute

Replace the largest top-level `const data = fixture()` constructions with one
lazy or suite-setup fixture per test module. A complete aggregate may still
need each fixture, but filtered and focused runs should not compile profiles
whose test bodies are skipped.

### 3. Separate type checking from runtime test transpilation

After the complete root `tsc` gate succeeds, qualify a serial runtime-test
command using `ts-node/register/transpile-only`. Retain the current
typechecking serial command as an explicit diagnostic fallback. The measured
benefit is primarily lower memory; this row must not be represented as the
main wall-time solution.

Native Node TypeScript execution is not presently a quick substitute: the
bounded Node 24 probe did not resolve the repository's extensionless NodeNext
imports without a broader module/import migration.

### 4. Measure the optimized serial boundary once

After the preceding rows are otherwise green, run one complete serial
aggregate and compare test inventory, wall time, CPU, and peak memory with the
recorded baseline. Do not rerun the multi-minute aggregate after every
individual cache or fixture edit.

If the cached serial runner meets the accepted performance threshold, stop.
Parallel sharding is conditional rather than an end in itself.

### 5. Qualify only coarse dependency-aware parallelism if still needed

If the optimized serial aggregate remains disproportionate, compare
precompiled JavaScript and transpile-only execution using two to four coarse
shards. Keep related LF/categorical transfer lineages together so each worker
preserves useful prerequisite caches. Use an explicit conservative default
worker cap—likely three—not Node's host-dependent nineteen-worker default.

Twenty hardware cores do not imply that nineteen copies of this
dependency-heavy, memory-intensive compilation graph will improve throughput.
Worker count must be selected by repeated wall-time and memory evidence.

## Deferred Rows

| Row | Status | Deliverable |
| --- | --- | --- |
| DEVEX-TEST-PARALLEL-0A | measured complete; documentation only | Current inventory, fair serial/two-worker comparison, eager-import attribution, repeated-compilation attribution, TypeScript-loading measurements, and safety audit |
| DEVEX-TEST-CACHE-1A | deferred; not selected | Process-local successful-result caching for the older pure zero-argument profile compilers, with immutability and isolation tests |
| DEVEX-TEST-FIXTURE-1B | deferred; not selected | Lazy construction of the measured expensive top-level test fixtures |
| DEVEX-TEST-RUNTIME-1C | deferred; not selected | Typechecked-then-transpile-only serial runtime command with the existing checked serial fallback |
| DEVEX-TEST-PARALLEL-2A | deferred after 1A/1B/1C | One optimized serial aggregate measurement with exact inventory, wall, CPU, and memory evidence |
| DEVEX-TEST-PARALLEL-2B | conditional and deferred after 2A | Compare precompiled-JavaScript and transpile-only execution over two to four dependency-aware shards |
| DEVEX-TEST-PARALLEL-2C | conditional and deferred after a successful candidate | Repeated equivalence/stability qualification, serial fallback, explicit worker cap, documentation, and default-script proposal |

## Acceptance Criteria

A candidate can replace the default only if it:

1. returns the identical discovered/pass/fail/skip inventory as the serial
   runner;
2. passes at least three consecutive runs without order, port, path,
   temporary-directory, or environment interference;
3. retains a simple serial fallback for diagnosis;
4. uses an explicit conservative worker cap rather than the host-dependent
   default;
5. records peak memory and does not create swap pressure;
6. improves representative full-gate wall time by at least 25%;
7. leaves semantic code, checker behavior, Lambdapi authority, and validation
   requirements unchanged; and
8. uses semantic/identity/isolation assertions rather than flaky wall-clock
   assertions in the permanent test suite.

Compilation caching may be accepted independently of sharding when it
preserves every semantic result and makes the serial boundary proportionate.

## Proportional Validation And SOP Relationship

The root `AGENTS.md` now treats the complete aggregate as a tranche-boundary
gate rather than a routine pre-edit baseline:

- plan/documentation-only changes use exact diff and Markdown/link hygiene;
- TypeScript implementation uses affected focused tests and typecheck/lint
  while it is changing;
- a shared compiler/runtime/test-runner change receives one complete
  `check:ts` after its bounded tranche is otherwise green;
- `check:all` remains for an affected cross-layer/integration or release
  boundary; and
- unchanged aggregate evidence is carried forward rather than recomputed for
  reassurance.

These rules change validation timing and frequency, not semantic coverage.
The nested Lambdapi SOP, warning comparisons, audits, catalogs, and health
ownership remain unchanged. Lambdapi and print parallelization are separate,
lower-priority qualifications because their artifact ordering and ownership
constraints differ from the TypeScript test bottleneck measured here.

## Verdict

Do not change the default root test command merely by expanding all files or
adding `--test-concurrency`. The quick/mechanical candidate is rejected by
measurement. When this maintenance work is eventually selected, first remove
duplicate immutable compilation, then defer eager fixtures, then qualify the
lighter serial runtime. Measure that serial result before deciding whether
two-to-four-worker sharding is necessary.

Until those rows are selected, use focused tests during implementation and
one serial aggregate root gate per bounded semantic tranche. This plan does
not select an implementation successor and does not delay product,
mathematical, or transfer work.
