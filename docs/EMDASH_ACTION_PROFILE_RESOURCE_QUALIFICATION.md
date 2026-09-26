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

The independent 567-target validation partition continues. Its 22 excluded
targets remain required and will be reconciled with the full 589-target gate.
This report qualifies one unchanged target and its first consumer; it does
not certify the ordinary classifier tranche or the completed migration.
