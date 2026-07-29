# TypeScript Test Parallelism Qualification Plan

Status: deferred, measured side plan; not on the elaborator semantic critical
path.

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

`tests/main_tests.ts` statically imports 154 test files. Node therefore sees
one test file and executes all registered tests on one application thread.
The repository benefits from one process-wide module cache, including cached
generic LF declaration/runtime compilations reused by later suites.

Node 24 can execute separate test files concurrently only under process
isolation. `--test-concurrency` controls the number of child-process files;
its default is available parallelism minus one. With
`--test-isolation=none`, all files share one process and file concurrency is
forced to one. Therefore merely replacing `main_tests.ts` with 154 file
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

The first representative benchmark deliberately used only two independently
green but expensive files:

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

## Verdict

Do not change the default root test command merely by expanding all files or
adding `--test-concurrency`. The quick/mechanical candidate is rejected by
measurement. Parallel qualification is worthwhile but requires a dedicated
performance tranche rather than an unreviewed DevOps edit during semantic
kernel work.

## Deferred Rows

| Row | Status | Deliverable |
| --- | --- | --- |
| DEVEX-TEST-PARALLEL-0A | pending | Capture per-file wall time, CPU, memory, import/cache overlap, temporary-resource use, and deterministic test-count inventory without changing the default |
| DEVEX-TEST-PARALLEL-1A | pending 0A | Compare precompiled-JavaScript workers against ts-node workers so TypeScript compilation is not duplicated per shard |
| DEVEX-TEST-PARALLEL-1B | pending 0A/1A | Compare two to four coarse dependency-aware aggregators that keep related LF/categorical transfer suites in one process and preserve useful caches |
| DEVEX-TEST-PARALLEL-1C | pending successful candidate | Repeated equivalence/stability qualification, serial fallback, explicit worker cap, documentation, and default-script proposal |

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
6. improves representative full-gate wall time by at least 25%; and
7. leaves semantic code, checker behavior, Lambdapi authority, and validation
   requirements unchanged.

Until those rows are selected, use focused tests during implementation and
one serial aggregate root gate per bounded semantic tranche. This plan does
not delay SCALE-KIND-PI-1, SCALE-INDUCTIVE-1B, or the remaining systematic
transfer qualification.
