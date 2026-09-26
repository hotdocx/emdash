# Action-Profile Integration: Fatal Checker Output Repair

Date: 2026-09-25 (America/Toronto; 2026-09-26 UTC)

Status: implemented and focused-tested validation repair; mathematical
integration remains active in the dedicated worktree

This bounded repair supports the [action-profile integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md).
It changes execution-result interpretation, not Lambdapi computation or the
resource guard. The ordinary classifier implementation is a separate tranche.

## Observed Failure

The first bounded `make check` run passed 86 targets, then exhausted memory
in `emdash3_2_commutative_algebra_affine_cover_charts.lp`. Its 31-file LP
closure is byte-identical to baseline main `37ce19d5` and does not contain
the changed classifier owner.

Compiling its direct parent, `emdash3_2_commutative_algebra_affine_basis.lp`,
exposed a false success: Lambdapi printed `Uncaught [Out of memory].` from
`Core__Sign.write`, left a zero-byte `.lpo`, and returned exit code zero.
The old runner classified that as `passed-fresh` and reusable. This receipt
is **not valid compiled-parent qualification**:

`20260926T025724Z-8c409741ae774d2a8ae71a4da944b8d5`.

The next load failed with `Uncaught [End_of_file].`, receipt
`20260926T025933Z-210de653f91648b38886aefbe3f45d0c`.
Both original receipts/logs remain unchanged in `emdash2/logs/check-runs/`;
this report records the correction rather than rewriting historical evidence.

The empty object was created by this goal. It was moved intact to
`emdash2/tmp/probes/api_invalid_objects/affine_basis-20260926T025724Z.lpo`
(SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`).
No source or user-owned artifact was discarded. With the already-checked
dependency objects present, recompilation passed in 2.326 seconds at the
same 2 GiB/90-second limit and `OCAMLRUNPARAM=o=20,v=1024`, receipt
`20260926T031133Z-5cce8a963b314757a3d0da2aeebff699`.
Artifact nonemptiness and a subsequent actual load are separate checks;
process exit zero alone is insufficient.

The regenerated object is 999,858 bytes, SHA-256
`bd257019d9cadc7f7a12c36dae87b448bbfaf899cbecaaf23674d8f3e5286c9c`.
Its load passes in 2.041 seconds, receipt
`20260926T031442Z-75f1405a95a04223b3a9640c23ae9ab9`.
The original affine-cover consumer now passes in 4.746 seconds, receipt
`20260926T031445Z-00ba6de20d934e3bad0b629b50d655b4`, with the same limits
and explicit GC setting. No mathematical change was needed for that failure.

## Repair Contract

The [runner](../emdash2/scripts/run_lambdapi.py) now recognizes fatal/uncaught
diagnostic prefixes, including colored output, before accepting a zero exit.
Out-of-memory, cannot-allocate and allocation-failure diagnostics receive
the existing `allocation-failed` outcome. Other uncaught failures remain
`failed`. Successful ordinary output retains its existing behavior.

Receipts preserve the actual process/recipe exit code. A fatal zero-exit run
is not reusable, the CLI returns nonzero, and quiet mode displays its failure
tail. An input-change observation does not overwrite a known fatal cause.
Staged recipes apply the same zero-exit rejection without treating their
total elapsed duration as a per-child deadline.

The repair neither changes checker flags nor increases memory, time or file
limits. It does not certify arbitrary object files. Compilation still needs
the actual downstream load/consumer and matching source/object dependencies.
The new runner hash prevents automatic reuse of receipts from the old runner
as if they were produced by the corrected validation boundary.

## Validation

The focused [runner tests](../emdash2/tests/test_check_runner.py) reproduce
zero-exit serialization failure using a real guarded child that emits the
observed diagnostic and leaves an empty object. They check receipt status,
non-reusability, CLI exit/tail, colored allocation failure, competing input
changes, and staged-recipe rejection. Existing success, hard-timeout,
explicit-limit and group-scope checks remain green.

```bash
python3 -m unittest tests.test_check_runner tests.test_check_metrics tests.test_check_registry
python3 -m py_compile scripts/run_lambdapi.py
```

All 43 tests pass from `emdash2`. Root `workspace:check` passes with
`pnpm@11.16.0` and Node `24.11.1`; exact diff hygiene passes. This tooling
checkpoint does not claim completion of the mathematical integration or its
remaining formal/health gates.

The [TypeScript probe-bridge regression](../tests/v3_2_probe_runner_tests.ts)
also passes under `node --require ts-node/register --test`. It verifies that
the existing bridge rejects a zero-exit fatal checker result, reports wrapper
status 1, and retains the actual checker exit zero with non-reusable
`allocation-failed` evidence. Its ordinary-success and hard-timeout controls
remain green. No TypeScript implementation or source pin changed.
