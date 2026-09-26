# Action-Profile Integration Resource Qualification

Date: 2026-09-26

Status: qualified target and first consumer; full integration validation continues

Plan: [living integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), `API-02M`.

The user supplied standing authorization for any needed measured memory or
timeout increases for this goal, without further approval requests. The root
and Lambdapi guidance now record it. Default checks remain at 2 GiB/90s.

## Target And Controls

`emdash2/emdash3_2_homology_map_kernel_covers.lp` and its 38-file LP closure
are byte-identical to main `37ce19d5`. They do not import the changed action
profile owner. At 2 GiB, the source exhausted allocation both before and
after compiling its three direct parents; more aggressive GC did not resolve
the failure. The plan records those immutable receipts.

All following runs use `OCAMLRUNPARAM=o=20,v=1024`, the normal guarded runner,
subject reduction, the serial lock, 64 MiB file limits, no core dumps and the
systemd no-swap scope. No mathematical source, runner or guard was changed.

| Check | Limit | Outcome | Seconds | Maximum child RSS (KiB) |
| --- | --- | --- | ---: | ---: |
| Target compilation | 3 GiB/90s | Allocation failure; no object | 66.388 | 2,868,776 |
| Target compilation | 6 GiB/180s | Passed | 96.259 | 3,668,804 |
| Compiled target import | 2 GiB/90s | Passed | 3.283 | 432,740 |
| Direct `homology_map_corrections` consumer | 2 GiB/90s | Passed | 3.637 | 453,656 |

The corresponding receipt IDs, under `emdash2/logs/check-runs/`, are:

- `20260926T051024Z-225df07de9044af18a7fdcdcc54ab880`
- `20260926T051232Z-b5c4d0aebcc9416782704c74f4dba35c`
- `20260926T051409Z-76be9a74b67b40d4afbcb79e3f7ba17a`
- `20260926T051413Z-cbb6b7323bb942edb6b81c88f288a94e`

The successful object has 2,890,429 bytes and SHA-256
`6c03b37e10719e15315819e82682a6e37bbf9274bebf9565392741a7f6c623b9`.
Its nonzero length, checked load and actual consumer distinguish this result
from the earlier invalid affine object described in the
[runner repair](EMDASH_ACTION_PROFILE_RUNNER_REPAIR.md).

## Replay And Remaining Scope

With the recorded direct parents compiled at their exact source versions:

```bash
cd emdash2
EMDASH_LP_MEMORY_MIB=6144 OCAMLRUNPARAM=o=20,v=1024 \
  python3 scripts/run_lambdapi.py --quiet --no-colors --timeout-ms 180000 --compile \
  emdash3_2_homology_map_kernel_covers.lp
OCAMLRUNPARAM=o=20,v=1024 \
  python3 scripts/run_lambdapi.py --quiet --no-colors \
  emdash3_2_homology_map_corrections.lp
```

The 6 GiB/180s setting is explicit for this target; it is not a claim of a
minimal resource requirement. Registry defaults remain unchanged. A durable
clean-checkout recipe and its profile belong to final gate integration after
the remaining resource-dependent targets are measured.

During these runs only the owned batch launcher was suspended. Its active
guarded child finished normally before another checker acquired the serial
lock; the launcher resumed in a `finally` handler. Individual receipt timing
is authoritative. Outer batch timings spanning those waits include the pause
and must not be used as performance measurements.

At that checkpoint the independent 567-target validation partition was still
running. Its 22 excluded targets remained required. The subsequent replay
below rejoins the full 589-target gate. This resource evidence does not certify
the ordinary classifier tranche or the completed migration.

## Subsequent Homology Replay

The independent partition then reached allocation failure in
`homology_epic_covers` at 2 GiB/90s, despite both direct parents already
having compiled objects. Its 36-file LP closure is unchanged from main and
excludes the new profile. A target-only compilation at 6 GiB/180s passed in
93.302s, with maximum child RSS 3,614,700 KiB:
`20260926T053322Z-aa96479d010149798a7ad4c28a64a80e`.
The object has 1,825,830 bytes and SHA-256
`57f1004da4f5d572162743d72ecf9225c9eab6ecccfcca8ef9724ad6d9673139`.

The resource partition separately failed while replaying imports of
`homology_first_exactness`; its 131-file LP closure is also unchanged from
main. Compiling its four direct parents at 2 GiB/90s resolved that import
overhead. The target then compiled in 18.333s at those same default limits,
receipt `20260926T053556Z-6402ed9a23954421bce3bc3a063c81be`. Its object has
4,643,427 bytes, SHA-256
`a95f3a502052e59c736d509fbadb52bb054754df22bda676b3df872b375d0eb9`.
The actual `homology_second_exactness` consumer, importing both recovered
bodies, passed at defaults in 26.495s:
`20260926T053615Z-5bbccbe8e0084841b885a7e0bf47ff5a`.

The exact receipt sequence is retained at
`emdash2/logs/api-resource-followup-receipts.json`. This follow-up used
sequential `run_check` calls in one Python process. Its child-RSS field is
the process-lifetime maximum and therefore includes earlier children; only
the first call's RSS above is a target-specific measurement. Later calls'
time, enforced limits, return classification, exact inputs and object checks
remain applicable. Do not report their repeated RSS value as individual
memory consumption. Subsequent measurements use separate CLI processes.

Full-suite continuation now selects explicit 6 GiB/180s settings for the two
measured cover owners and atomic staged recipes that compile those owners.
Other targets retain their default or existing registered settings. Successful
receipts are reusable only when exact source/object, checker, runner, recipe
and effective settings still match. The full suite remains in progress.
