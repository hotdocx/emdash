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
and effective settings still match. The complete check-suite result is
recorded below.

## Normalization Recipe Follow-Up

The full continuation reached 462 successful targets before the atomic
`check_short_exact_normalization.sh` recipe failed in
`monic_image_comparison` at 2 GiB/90s. Its 21-file LP closure is unchanged
from main and excludes the action-profile owner. The failed group receipt is
`20260926T065106Z-62898140375e4ec38f418e47f4311450`.

A 6 GiB/180s retry with `o=20,v=1024` passed that target and subsequent owners,
then exhausted allocation in `short_exact_normalization_projections`:
`20260926T065724Z-720076f7b87543e793eabf2abdb2917d` (253.433s total recipe
time, not a per-child timeout). No source or guard was changed.

The retry at 6 GiB/600s per child with more aggressive GC (`o=5,v=1024`) also
exhausted allocation in `short_exact_normalization_projections`, receipt
`20260926T070928Z-2171939ce5724a1a8ffe7c244519d54e` (484.368s total recipe
time). That target therefore has separate measured failures under two GC
settings with its preceding dependency objects compiled in the fresh recipe.

Under the standing authorization, the guard, runner and registry now support
an explicit ceiling of 8192 MiB. The default remains 2048 MiB; existing native
profiles remain 6144 MiB. The deadline ceiling remains 600s, and serial,
subject-reduction, file/core and no-swap protections are unchanged. The host
reported about 12.6 GiB available before selecting the single-checker 8 GiB
experiment. No 8 GiB default or unrelated target profile is introduced.

Validation passed: 29 guard/runner/registry tests, 12 DevOps tests and 10
native-profile tests. These include inherited hard limits, unchanged defaults,
explicit 8 GiB acceptance without allocating a large heap, rejection above
the new ceiling, serialization, deadline behavior and subject-reduction
bypass rejection. The runner-code change invalidates exact tooling-identity
reuse of older receipts; retain them as historical evidence.

The registered normalization recipe passes at 8 GiB/600s per child with
`o=20,v=1024`, including the previously failing projection owner and all its
reviewers. Receipt `20260926T073103Z-666ff1d96c2146519a3b393114d25ac4`
records 388.071s total recipe time. That single recipe did not establish
full-suite success; the subsequent complete check continuation does so below.
Checkpoint `f4a3aac1` records the bounded guard extension and its tests.

## Complete Registered Check-Suite Result

Continuation 33024 completed with exit 0 and all 589 distinct targets in
`checks.json`'s `check` list passed. There are no excluded resource targets.
The registry and result sets were compared exactly, not inferred from log
line counts (staged groups repeat some member status lines).

The log is `emdash2/logs/api-ordinary-check-eight-gib-resume.log` and the result
is `emdash2/logs/api-ordinary-check-results.json`, SHA-256
`2c893c3a7d1bc3ecf30f6503c3627b03e9e2c95bc9f2b1e25399c43f48613756`.
The final source receipt is
`20260926T085607Z-947024def2eb4dc7a63011022b2c1684` for projective line.
An additional read-only audit matched all 589 targets to successful current
source/group receipts, preserving exact source/object, checker, runner and
effective settings identity. The ID map is
`emdash2/logs/api-ordinary-check-final-evidence.json`; no typecheck was rerun
by that audit.

The recipe retains explicit per-target/group settings: normal 2 GiB/90s,
the reviewed cover settings, the normalization setting above, existing native
profiles, and GC `o=20,v=1024`. Source/object/checker/runner/settings identity
governs reuse. This qualifies the registered check suite for the ordinary
classifier checkpoint. It does not certify the whole migration or replace
complete final formal CI (currently 1,293 registered targets, plus any new
owners/reviewers) and clean-checkout resource routing.

## Combined Native And Inherited Cubical Prototype

The [Gray/path-cubical candidate](EMDASH_ACTION_PROFILE_GRAY_AND_PATH_CUBICAL_FEASIBILITY.md)
checks the two separate closures at the normal profile: the Gray/native
review takes 20.895s and the inherited path/address review takes 84.745s.
Their combined test preloads all 159 selected semantic owners before running
both reviewer closures. It uses a scoped 180-second deadline because the
path closure alone nearly fills the default 90 seconds.

| Combined check | Limit | Outcome | Seconds | Maximum child RSS (KiB) |
| --- | --- | --- | ---: | ---: |
| First combined import/reviewer check | 2 GiB/180s | Allocation failure during face naturality | 72.424 | 1,818,092 |
| Identical mathematical inputs | 3 GiB/180s | Passed; 470 positive/80 negative assertions | 113.562 | 1,896,180 |

Receipts are `20260926T135258Z-0ca2ca715e144c3fb4759608d8eca7fa` and
`20260926T135535Z-1b8f72b9a7f94b078ec29b7255fb4b53`. Their mathematical
input maps agree exactly. Both use `o=20,v=1024`, subject reduction, serial
execution, the 64 MiB file limit, disabled core dumps and the systemd no-swap
scope. The runner correctly records the first result as `allocation-failed`.
The address-space limit is distinct from the reported maximum child RSS.

The successful command from `emdash2` is:

```bash
EMDASH_LP_MEMORY_MIB=3072 OCAMLRUNPARAM=o=20,v=1024 \
  python3 scripts/run_lambdapi.py --timeout-ms 180000 --quiet --no-colors \
  --package-root tmp/probes/api_ordinary_profile_minimal \
  api_profiles_cubical_native_joint_review.lp
```

This is a measured profile for one temporary combined target, not a change
to the default guard or evidence that every inherited owner needs 3 GiB.
It does not discharge the displayed assembly prerequisite, production
promotion or final integration gates.

## Native Snake Six-Term Candidate

The original six-term reviewer now checks the main-based lax/profile
candidate. After adapting its actual ordinary support proofs, the default
run passes the affected biproduct/coproduct injection owners but exhausts
allocation while checking the second exactness closure. Identical source
passes with a target-specific memory increase:

| Check | Limit | Outcome | Seconds | Maximum child RSS (KiB) |
| --- | --- | --- | ---: | ---: |
| Original six-term reviewer | 2 GiB/90s | Allocation failure | 39.301 | 1,818,040 |
| Identical mathematical inputs | 3 GiB/90s | Passed, six original assertions | 64.754 | 2,735,912 |

Receipts are `20260926T151510Z-36afbd72f3064e27a3f8b0c1958cacfa` and
`20260926T151626Z-b04ca809f99c4e24978100df4faaad90`. Their input maps
are identical. Both retain `o=20,v=1024`, subject reduction, the serial lock,
file/core limits and systemd no-swap scopes.

The expanded joint review additionally preloads the selected Gray/path,
native and retained-data owners. It selects 4 GiB/240s because the separate
six-term replay approaches 3 GiB and the earlier cubical/native union
required 3 GiB/180s. Its first run at 118.250s exposed a remaining use of the
retired unrestricted mapper in arrow-evidence evaluation, rather than a
resource failure (`20260926T152027Z-9d50257c548a47c78a8dfb0fe3cfed4c`).
That owner now uses direct evaluation of retained inverse data. The final
joint replay passes in 143.610s with maximum child RSS 3,518,656 KiB, receipt
`20260926T152718Z-905556c99d9c4b3f94e8eb666f59d462`: 513 positive/89 negative
assertions and twenty retained-data consumers. The separate retained-data
reviewer passes at 3 GiB/90s in 66.811s, RSS 2,748,612 KiB, receipt
`20260926T152535Z-e6fbecfec9d64a6ba04c3a6e322b5f62`. The
[native feasibility review](EMDASH_ACTION_PROFILE_NATIVE_SNAKE_FEASIBILITY.md)
records exact current source and control manifests.

These are explicit temporary-target profiles under the user's standing
authorization. Defaults remain 2 GiB/90s; no new production resource profile
or permission question is introduced.

## Freyd And Proof–CAS Import Qualification

The [Freyd/proof–CAS review](EMDASH_ACTION_PROFILE_FREYD_CAS_FEASIBILITY.md)
records all 94 original assertions passing across eight unchanged emitted
artifacts. Six source-only replays use 6 GiB/180s. The final two certificate
artifacts use byte-identical sources and verified compiled parents at
8 GiB/300s. Every run retains subject reduction, serial execution, file/core
limits and no swap.

The raw LES import order exhausts 6 GiB with `o=20` in 81.156s, and with
`o=5` in 169.747s, without a generated assertion body. Checking the existing
action/profile parents first resolves that boundary. After two existing-C1
caller repairs, the same seven-parent closure passes in 27.468s, RSS
2,074,824 KiB, and the unchanged 48-assertion diagram in 29.816s, RSS
2,310,088 KiB. This is an explicit preparation-order qualification, not a
claim that arbitrary orders have equal resource cost.

The original snake pair comparison fails at both 6 and 8 GiB. The adapted
component-proof construction preserves its statement and data. It proves
each complete-arrow comparison, assembles the pair path, and reuses shared
adjacent-arrow proofs. The full adapted diagnostic passes at 8 GiB/300s;
its actual owner also compiles independently. These are changed proof bodies,
not a relabelling of the original failed source as a larger-limit success.

| Qualified check | Profile | Seconds | Maximum child RSS (KiB) | Receipt |
| --- | --- | ---: | ---: | --- |
| Actual adapted pair owner, compile with subject reduction and warnings | 8 GiB/300s | 124.441 | 7,676,472 | `20260926T171234Z-a1232561282d4ce4b34cbeb4331ebf69` |
| Original snake certificate signatures, checked compiled parents | 8 GiB/300s | 37.284 | 4,236,956 | `20260926T171511Z-81bba6a6223c41b5af3db379db3e90f1` |
| Original concrete snake certificate, same parents | 8 GiB/300s | 46.762 | 4,253,456 | `20260926T171550Z-2d92755250494c15be49fe5e38c70a75` |
| Expanded profile/native/Gray/path review after actual CAS parents | 8 GiB/300s | 193.833 | 7,533,472 | `20260926T171726Z-8d163441774942c6a94ea4c29c465b81` |

The larger source-only certificate environment still exceeds 8 GiB while
rechecking the pair owner. The separate resource package prepares that owner
first; all 231 produced objects are nonempty and their hashes are bound by
the successful consumer receipts. Every copied LP source matches the
preferred candidate. The final qualification manifest in the CAS review
binds the 94 original assertions and expanded 513-positive/89-negative
review, plus twenty retained-data consumers.

Normal defaults remain 2 GiB/90s. These exact temporary resource profiles and
source/object snapshots do not replace final clean-checkout routing or full
integration gates. The prepared group must be made reproducible through the
owning registry/tools at that boundary; no mathematical source pin is changed
merely to pass a resource check.

## Whole Matching-Action Candidate

The [matching-action feasibility review](EMDASH_ACTION_PROFILE_MATCHING_ACTION_FEASIBILITY.md)
combines the new whole matching-parameter proof with the existing profile,
residual-precomposition, Γ/H and Hom-introduction reviewers. Its separate
source-only candidate contains one generalized proof-time precomposition
comparison; it is not the earlier compiled-parent CAS environment.

| Same 157-input snapshot | Profile | Outcome | Seconds | Maximum child RSS (KiB) | Receipt |
| --- | --- | --- | ---: | ---: | --- |
| Complete interaction review | 2 GiB/90s | Allocation failure during a dependent-owner import | 33.385 | 1,819,548 | `20260926T191725Z-96e00f43e1254fb9812934bf31c2f75f` |
| Identical source retry | 3 GiB/180s | 269 positive/77 negative assertions pass | 33.849 | 1,884,016 | `20260926T191910Z-dc94abf95bc6464db84edd5d64dfe7e5` |

Both receipts bind input snapshot
`ebd5ac484e3291245ef65fb122097113681da7f0854f93db9ab6a67f90d67f10`.
Subject reduction, warnings, `o=20,v=1024`, serial/file/core/no-swap guards
are unchanged. The larger profile is explicitly scoped under the standing
authorization; defaults remain 2 GiB/90s. This measures a successful profile,
not the minimum memory or time requirement. Maximum child RSS is distinct
from address-space and aggregate memory limits.

## Production Routing And Cold Normalization

The complete 791-library sweep and subsequent 307-object comment-exact
rebuild pass. Production now has 64 measured exact-target overrides; normal
limits remain 2 GiB/90s. The [production continuation](EMDASH_ACTION_PROFILE_PRODUCTION_CONTINUATION.md)
owns the complete measurement manifests and final acceptance queue.

The candidate cold normalization recipe prepares missing parents in local
import order and selects each exact registered target's profile. Its source,
package and dependency identities are checked before granting that profile.
The first cold projection check exceeded 180 seconds at 8 GiB; the same
source passed a second cold run at an 8 GiB/300s ceiling in 93.323s. This is
observed timing variability, not a minimum-bound claim. That run subsequently
exhausted 2 GiB in an original reviewer, so the whole recipe was not green.

Both affected original reviewers now pass individually at 3 GiB/90s:
monic selected-row comparison in 43.745s and normalization structure in
26.466s. The remaining normalization/comparison reviewers pass at defaults.
Those measured settings and the 300-second projection deadline are registered;
the subsequent complete cold replay passes all 48 child checks, including
the seventeen original explicit targets. The twelve-file adapter patch is
installed, with exact receipts in `api_staged_profile_installation.json`.
The remaining recipes still require full CI qualification. No formal
source change or generic strictness restoration was needed for these retries.

## Adjacent-Window Reviewer Follow-Up

The full formal gate stopped at the adjacent-window reviewer after 475
successful registered targets. Merely raising limits did not qualify it:
3 GiB/90s, 3 GiB/180s and 4 GiB/300s timed out; the 6 GiB/600s control with
default GC overhead exhausted memory after 532.842s. A source-only control
and typed-view experiments locate expensive pair/type reconstruction in the
manual tail assembly, rather than an object-generation-only cost.

The qualified reviewer uses main's existing transparent whole-window tail
constructor for the same two windows and supplies literal endpoint arguments
to its original first-step comparison. All five mathematical observations
remain, with no library, rule, opacity or assumption change. The complete
candidate passes in 25.397s and the installed reviewer in 22.784s, both at
3 GiB/90s and GC `o=20,v=1024`. Its exact target profile is registered, bringing
the override count to 65 while retaining 2 GiB/90s defaults. The
[production continuation](EMDASH_ACTION_PROFILE_PRODUCTION_CONTINUATION.md#adjacent-window-diagnosis-and-qualified-adaptation)
records the failed controls, receipts, installation and the subsequent full
reviewer sweep. Complete cold-recipe/full-CI qualification remains required.

## Complete Reviewer Sweep And Measured Production Profiles

All 596 registered reviewers pass in the complete production-source sweep,
including compilation of the 24 cold-recipe reviewers. Seven exact-input
continuations preserve the preceding successes and failures; final state:
`api_all_production_reviewer_resume7_results.json`. Every production source
hash still matches its final staged counterpart. This sweep uses qualified
compiled library parents and does not replace the complete cold recipes.

The sweep measures 33 further target-specific memory increases: 22 reviewers
at 3 GiB/90s, seven at 4 GiB/90s and four at 6 GiB/90s. These are observed
passing bounds after allocation failures, not minimum requirements. All use
`o=20,v=1024`, warnings, subject reduction and the existing serial/file/core/
no-swap guards. The registry now has 98 exact-target overrides; its normal
2 GiB/90s profile and all target sets remain unchanged. The exact registry
delta is only these 33 mappings. Installation manifest:
`api_reviewer_profile_installation.json`.

| Reviewer (`examples/`) | Memory (GiB) | Seconds | Successful receipt |
| --- | ---: | ---: | --- |
| `homology_bounded_generator.lp` | 3 | 11.652 | `20260927T151125Z-91385c3ad5b649e595b07e7e8306abe9` |
| `homology_bounded_generator_arrows.lp` | 3 | 14.021 | `20260927T151151Z-39b6ed998d3a4e64aae8e69079769b0e` |
| `homology_window_extension.lp` | 3 | 12.012 | `20260927T151315Z-642cd64745df4929a66a0779454eeace` |
| `freyd_adjunction_model_connecting_observation.lp` | 3 | 17.845 | `20260927T153443Z-21d58bea74554c7a9d7a49ad7cccf737` |
| `freyd_adjunction_model_whole_exactness.lp` | 4 | 22.708 | `20260927T153548Z-73811665e6b241dcaca991d22414093c` |
| `freyd_adjunction_model_window.lp` | 4 | 19.918 | `20260927T153647Z-5e0f7f5108cb4980b7bc1036287eece7` |
| `freyd_native_column_comparisons.lp` | 3 | 12.965 | `20260927T153731Z-e976109f74894c308baa79df45d0fe61` |
| `freyd_native_column_homology_paths.lp` | 3 | 14.202 | `20260927T153758Z-df9af6dcb4f942f687f699612f2c5110` |
| `freyd_native_connecting_endpoints.lp` | 3 | 16.732 | `20260927T153826Z-67a2213158444511ba03a2aa5ef9f5bb` |
| `freyd_native_diagram_exactness.lp` | 3 | 12.534 | `20260927T153857Z-3fc76c20ecce428397e8c79749cfecb2` |
| `freyd_native_middle_column_comparisons.lp` | 3 | 12.378 | `20260927T153937Z-b00b8c77db1b4132a6a5efff53ee67c9` |
| `freyd_native_middle_pair_exactness.lp` | 4 | 22.710 | `20260927T154026Z-e83ada19fd31465a91fda24f179569f0` |
| `freyd_native_middle_public_exactness.lp` | 4 | 18.733 | `20260927T154125Z-54bcd6e13d3c44439e394ef7c9ba334d` |
| `freyd_native_snake_exactness.lp` | 4 | 19.407 | `20260927T154226Z-a9133f3b76634897af0a5097b225ba26` |
| `freyd_native_snake_observations.lp` | 3 | 14.542 | `20260927T154307Z-d0a0f7935f6242b5a1f1ea68c25e33dd` |
| `freyd_native_source_pair_exactness.lp` | 6 | 32.177 | `20260927T154446Z-61102a36b86d456aa0fde5e797e0ee0d` |
| `freyd_native_source_public_exactness.lp` | 6 | 24.101 | `20260927T154624Z-326cbbabf8a644e09f6f8d52d4659795` |
| `freyd_native_target_pair_exactness.lp` | 6 | 31.393 | `20260927T154752Z-99d1761f18d64324bde43c71742ff49b` |
| `freyd_native_target_public_exactness.lp` | 6 | 24.090 | `20260927T154929Z-d5a75e1ee4004459818769596d02f25d` |
| `freyd_native_whole_exactness.lp` | 4 | 20.554 | `20260927T155030Z-e301ef95a9594aa880a1e95bb3c7ea1e` |
| `freyd_raw_native_window.lp` | 4 | 19.991 | `20260927T155130Z-14ee04e5e99946d78c6e57cab5f96822` |
| `one_cat_connecting_source_exactness.lp` | 3 | 13.629 | `20260927T161208Z-d62454472e574b58b288c961203d2201` |
| `one_cat_connecting_target_exactness.lp` | 3 | 13.626 | `20260927T161236Z-f2586e8c0cc64a2ca704cc540aba10fa` |
| `one_cat_middle_homology_exactness.lp` | 3 | 13.646 | `20260927T162029Z-0d6029a1d7e642b1bcf4242bf2627d1a` |
| `one_cat_native_exact_comparison_kernels.lp` | 3 | 11.657 | `20260927T162137Z-19092844c55f4cf99c90061253adfaae` |
| `one_cat_native_homology_window_exactness.lp` | 3 | 16.107 | `20260927T162257Z-b6901f0f52db41e1870ced869e9c0263` |
| `one_cat_native_snake_six_term_data.lp` | 3 | 14.369 | `20260927T162625Z-a401ebd674d244549f4bfeb84e61920b` |
| `one_cat_native_snake_six_term_inputs.lp` | 3 | 15.532 | `20260927T162654Z-b50c8760a69c43cc9439b1926b1f6245` |
| `one_cat_native_snake_six_term_result.lp` | 3 | 13.431 | `20260927T162734Z-d20aaf15a278493f9806cb1874636df7` |
| `one_cat_native_window_point_exactness.lp` | 3 | 16.314 | `20260927T162851Z-904f3ffc60a54f45b805fdb153f430a0` |
| `one_cat_native_window_snake_connecting_comparison.lp` | 3 | 17.078 | `20260927T162923Z-443df5c3f0e44e199ce6b1050e72da66` |
| `one_cat_native_window_snake_right_homology.lp` | 3 | 14.292 | `20260927T163031Z-ec03ab150a6544329adcc5c6ce97946b` |
| `one_cat_native_window_snake_surrounding_maps.lp` | 3 | 18.021 | `20260927T163124Z-88de414ac99947b48d988ebcb68a2987` |

The focused registry/metrics/staged-adapter/native-profile tests pass all
58 cases (`logs/api-reviewer-profile-tooling-qualified.log`). Their original
attempt correctly caught a hard-coded GC expectation for the three newly
profiled six-term reviewers; the expectation now names those exact measured
overrides. No checker-runner behavior or formal source changed in this step.
The preceding immutable receipts retain their original configuration snapshot;
the next complete formal CI run qualifies the registered configuration.


## Final Cold-Recipe Qualification

The completed formal gate
`formal-20260927T164506Z-d45cf3135aaa42c8a51b128f5e319355` passes all nine
isolated recipes under the registered profiles, with 80 successful registered
group members. All 1,388 formal targets pass in the same invocation. Exact
recipe receipts, member counts and whole-group durations are indexed in
`api_final_cold_group_evidence.json`; group shares are not individual checker
measurements. No additional resource/profile changes were required after
the complete reviewer sweep. Defaults remain 2 GiB/90s and the registry
retains 98 exact-target overrides. The original production CAS artifacts
also pass at the separately recorded explicit 6 GiB/180s and 8 GiB/300s bounds.

## September 29 public CI follow-up

The first public cold-checkout run exposed an ordinary-profile allocation
failure in `emdash3_2_commutative_algebra_affine_glue.lp`. The
[release ledger](EMDASH_LOCAL_CLOUD_RELEASE_PLAN.md#cold-formal-ci-resource-follow-up)
records a source-identical cold replay: 2 GiB/90s with `o=20,v=1024` fails in
48.230s; the existing `action-profile-3g-90s` profile passes the owner in
46.310s at 1,933,456 KiB maximum child RSS and its concrete
`examples/commutative_ring_affine_glue.lp` consumer in 53.275s at 2,341,096 KiB.
Those two exact targets now select that existing profile, bringing the
override count to 100. This uses the standing action-profile resource
authorization. No mathematical declaration, proof, source pin, checker,
global default, subject-reduction setting or resource ceiling changes.
It is repository-validation maintenance, not a requirement for the independent
GetPaidX Node/TypeScript scientific runtime.

## September 30 cold homology consumer follow-up

Public CI `36526254196` stopped at the ordinary-profile
`one_cat_homology_covers` owner. A source-identical temporary package with no
compiled objects reproduces the allocation failure. Its 16 ordinary-profile
owner/consumer targets were then checked serially at the existing 2 GiB/90s
bound. Every default-GC control fails allocation. Scoped `o=20,v=1024` passes
13; the projection-zero and inclusion-zero owners and the exact-input reviewer
still fail at 2 GiB, then pass at the already authorized 3 GiB/90s bound.

Only those 16 exact targets receive overrides: 13 select the new GC-only
`action-profile-2g-90s`, three select existing `action-profile-3g-90s`.
The registry now has 116 exact overrides. Normal defaults, subject reduction,
checker/source pins, all mathematical files, serial/file/core/no-swap guards
and the resource ceiling remain unchanged. These are observed passing bounds,
not minimum requirements. No new mathematical qualification is asserted.

| Target (library prefix `emdash3_2_` omitted) | GiB | Seconds | Successful receipt |
| --- | ---: | ---: | --- |
| `one_cat_homology_covers.lp` | 2 | 36.062 | `20260930T054039Z-ddbf0b7acfd547bda3764607673097a3` |
| `one_cat_native_homology_window_covers.lp` | 2 | 32.835 | `20260930T054301Z-365a6c0859434a7e832d18a94761712d` |
| `one_cat_native_connecting_kernel_paths.lp` | 2 | 44.352 | `20260930T054753Z-1ff01e021f914ab183cb7cdbca16d984` |
| `one_cat_native_cycles_connecting.lp` | 2 | 32.457 | `20260930T054907Z-17e383bfe8f94a139657cce2af31ea3a` |
| `one_cat_native_connecting_upper_lifts.lp` | 2 | 32.453 | `20260930T055007Z-e73afe227f734cf2b42565453d5ef2ca` |
| `one_cat_native_connecting.lp` | 2 | 37.272 | `20260930T055106Z-8c7ba4ecd425462e8b4391400b3d8498` |
| `one_cat_native_homology_window_connecting.lp` | 2 | 33.170 | `20260930T055209Z-922831ab49d5427e8b287ed3a2ed3c68` |
| `one_cat_covered_middle_cycles.lp` | 2 | 33.171 | `20260930T055309Z-d33821f6e4a24e6696a1aa22eec53d02` |
| `one_cat_native_connecting_projection_zero.lp` | 3 | 24.422 | `20260930T085358Z-356d8ba024294f868a49fcd1d70949b8` |
| `one_cat_native_connecting_inclusion_zero.lp` | 3 | 26.461 | `20260930T085650Z-1966d6e756d44674b7c06036023a3957` |
| `one_cat_connecting_source_representatives.lp` | 2 | 25.060 | `20260930T085735Z-adb8a7f41b73421581b672f4f93ed9d2` |
| `examples/one_cat_native_connecting.lp` | 2 | 24.714 | `20260930T085820Z-84cfca10f2244c8f95a8ad15ba75da87` |
| `examples/one_cat_native_connecting_lifts.lp` | 2 | 22.733 | `20260930T085905Z-cbc452279e0f4c9793e20b76b610dce3` |
| `examples/one_cat_native_homology_window_connecting.lp` | 2 | 27.311 | `20260930T085946Z-ed8e443ee9d04482b58abd3af39a3c3a` |
| `examples/one_cat_native_homology_window_covers.lp` | 2 | 30.938 | `20260930T054423Z-880a2877b5f24e648535fd2179d07c71` |
| `examples/one_cat_native_homology_window_exact_inputs.lp` | 3 | 29.057 | `20260930T090131Z-996568ca9f5443b5835eb222070a1f39` |

Full controls are indexed in `/tmp/emdash-homology-cold-followup-complete.json`;
immutable source snapshots and execution receipts remain under
`emdash2/logs/check-runs/`. The first batch reused a launcher, so its child RSS
field is a cumulative high-water measurement, not per-target RSS. Later
controls use fresh runner processes. All memory bounds above are explicit
guard limits; the per-target wall times exclude unrelated work.

The registry/tooling checks and next public formal run qualify this routing;
earlier full formal evidence does not substitute for that cold hosted run.
This maintenance remains independent of the cloud Node/TypeScript runtime.

## September 30 cold native snake follow-up

Public CI `36693986974` passes all non-formal jobs, including the complete
TypeScript gate, then stops at `one_cat_native_snake_inner_zeros` with an
allocation failure. The cold, source-identical import group contains 25
ordinary-profile owners/reviewers. Serial default controls reproduce allocation
failures for each. Scoped `o=20,v=1024` passes 23 at the unchanged 2 GiB/90s
bound. Only the second- and third-exactness reviewers still fail there; both
pass at the existing authorized 3 GiB/90s bound. No compiled objects are used.

Only these 25 exact target bindings change: 23 reuse `action-profile-2g-90s`,
two reuse `action-profile-3g-90s`. There are now 141 exact overrides. Normal
defaults, mathematical/checker/source pins, target membership, subject reduction
and serial/file/core/no-swap guards remain unchanged. These are passing
observations, not minimum-bound claims or broader mathematical qualification.

| Target (library prefix `emdash3_2_` omitted) | GiB | Seconds | Successful receipt |
| --- | ---: | ---: | --- |
| `one_cat_native_snake_inner_zeros.lp` | 2 | 38.464 | `20260930T102429Z-97bb95aae170469092a7ef43e5043046` |
| `one_cat_native_snake_exact_inputs.lp` | 2 | 37.565 | `20260930T110055Z-a4e6b5b6112d402685417dd1154f3f95` |
| `one_cat_native_snake_comparison_kernels.lp` | 2 | 37.557 | `20260930T110203Z-15c78e15fabf48cfb2f96b0434893938` |
| `one_cat_native_snake_first_kernel_comparison.lp` | 2 | 31.887 | `20260930T110309Z-dc417bba1d184477bda4e7ffe915c6f1` |
| `one_cat_native_snake_first_cover.lp` | 2 | 29.601 | `20260930T110412Z-0b93fe26f04348118569795475035be4` |
| `one_cat_native_snake_second_covers.lp` | 2 | 41.512 | `20260930T110510Z-fa93d9f1b0594241b2483c30aea8b6ab` |
| `one_cat_native_snake_third_covers.lp` | 2 | 37.798 | `20260930T110622Z-e2b8fc77253644fd91dfa2bdab5f05ae` |
| `one_cat_native_snake_third_representatives.lp` | 2 | 38.083 | `20260930T110727Z-8940cfecf49a4be9a0bfc29adc28866e` |
| `one_cat_native_snake_fourth_covers.lp` | 2 | 38.774 | `20260930T110833Z-261b7a7719d44957a4792516b146b5f1` |
| `one_cat_native_snake_first_pair_path.lp` | 2 | 30.349 | `20260930T110937Z-587924f9cc3a401cb6c49f9c86855698` |
| `one_cat_native_snake_other_pair_paths.lp` | 2 | 29.832 | `20260930T111031Z-c8a712d3a20640a5b20680d8fc329865` |
| `examples/one_cat_native_snake_comparison_kernels.lp` | 2 | 31.713 | `20260930T111129Z-2ff1eee69c824abd9e4166c271564e30` |
| `examples/one_cat_native_snake_first_cover.lp` | 2 | 34.537 | `20260930T111230Z-e677fb92137a48f5b2197d0b03edd709` |
| `examples/one_cat_native_snake_first_exactness.lp` | 2 | 35.355 | `20260930T111329Z-edddfff43cf7423ca132511088e669cc` |
| `examples/one_cat_native_snake_first_kernel_comparison.lp` | 2 | 36.880 | `20260930T111429Z-c7da1451cde5400786931a375ef89cbf` |
| `examples/one_cat_native_snake_fourth_covers.lp` | 2 | 35.227 | `20260930T111529Z-ba0aa53a0a534817bb93c75891ec6c01` |
| `examples/one_cat_native_snake_fourth_exactness.lp` | 2 | 35.878 | `20260930T111628Z-02e9b52d295a4cc9b34818a024ed1d89` |
| `examples/one_cat_native_snake_fourth_representatives.lp` | 2 | 31.321 | `20260930T111725Z-c82ca21e4a644a94b2ee804f378102fb` |
| `examples/one_cat_native_snake_second_covers.lp` | 2 | 32.534 | `20260930T111824Z-cc6fb0e9ee9c43919a076661b3a7f64a` |
| `examples/one_cat_native_snake_second_exactness.lp` | 3 | 39.123 | `20260930T111957Z-fdeee57d922846b5a9601229144d4109` |
| `examples/one_cat_native_snake_second_representatives.lp` | 2 | 33.102 | `20260930T112104Z-e638654d99b0408ca1c85cbf068ed5fd` |
| `examples/one_cat_native_snake_six_term_zeros.lp` | 2 | 30.942 | `20260930T112202Z-9b277046f11643d5bcb2ffb727892018` |
| `examples/one_cat_native_snake_third_covers.lp` | 2 | 36.940 | `20260930T112258Z-d2403344becd4413b825f00179f31ec9` |
| `examples/one_cat_native_snake_third_exactness.lp` | 3 | 31.271 | `20260930T112433Z-994b17595c284ce4af3de1605096ff0c` |
| `examples/one_cat_native_snake_third_representatives.lp` | 2 | 26.611 | `20260930T112526Z-c5dc51723c9e4bcda6bd75b9faa63358` |

Complete controls are indexed in
`/tmp/emdash-snake-zeros-cold-controls-20260930.json`; immutable inputs and
receipts remain in `emdash2/logs/check-runs/`. Each control uses a fresh runner
process. Registry/tooling checks and the subsequent public formal run are
required for the recorded routing. This is repository validation and does
not add a Lambdapi runtime dependency to cloud scientific programs.

## September 30 cold native window-left follow-up

Public run `36712188754` passes every other gate, then formal stops after 211
checks at `emdash3_2_one_cat_native_window_snake_left_homology.lp` (allocation
failure/exit 134, 29.006s). Both default-profile targets importing this owner
were replayed source-identically without any `.lpo` inputs. The default-GC
controls fail allocation. The owner passes scoped GC at 2 GiB/90s; its reviewer
still fails GC at 2 GiB and passes the existing 3 GiB/90s profile. The real
whole connecting-comparison consumer passes cold at its existing 3 GiB/90s.
Only these two exact bindings are added, bringing the override count to 143.
Formal source, checker, subject reduction, normal defaults, file/deadline/serial
and no-swap guards are unchanged.

| Target | GiB | Seconds | Passed receipt |
| --- | --- | --- | --- |
| `emdash3_2_one_cat_native_window_snake_left_homology.lp` | 2 | 36.079 | `20260930T130305Z-e495f3a571624e389c2662cf591aec17` |
| `examples/one_cat_native_window_snake_left_homology.lp` | 3 | 43.799 | `20260930T130449Z-b887506a61114b7fa27ed0b9237e19db` |
| `emdash3_2_one_cat_native_window_snake_connecting_comparison.lp` (existing profile) | 3 | 54.159 | `20260930T130857Z-a143946a513446a7b2be92ea6a0a54bf` |

Controls: `/tmp/emdash-window-left-cold-controls-20260930.json` and
`/tmp/emdash-window-left-consumer-3g-20260930.json`; immutable input/settings
snapshots remain in the referenced receipt files. An initial consumer control
without an explicit memory override used 2 GiB and failed; the cold scratch
package does not carry registry metadata, so its subsequent 3 GiB control is
explicit. Do not report that initial control as a 3 GiB failure. Full public
formal validation remains required after this bounded metadata correction.

## September 30 cold native window-right follow-up

Public run `36720083359` passes every other job and the previous left-window
correction, then stops after 215 formal checks at right kernel quotients
(exit 134, 28.213s). Eleven source-identical cold owners/consumers are replayed
with no object inputs. Four previous defaults require 4 GiB with scoped GC;
seven existing 3 GiB/90s targets pass unchanged, including whole right homology,
connecting comparison and surrounding-map owners/reviewers. Only four exact
bindings are added, bringing the count to 147. Defaults, formal source,
checker, subject reduction and serial/file/no-swap guards remain unchanged.

The pair/reviewer pass 4 GiB/90s in 82.481/85.574s, close to the deadline.
Reviewed repetitions at the existing 4 GiB/180s profile pass in 91.939/94.318s,
confirming runtime variability that can exceed 90 seconds. Only those two
receive 180 seconds; the other two select the existing 4 GiB/90s profile.
This operational qualification does not certify CAS algorithm implementations
or change any mathematical qualification. It makes clean-checkout checking
of the published formal reference reproducible within explicit bounds.

| Target | GiB / seconds ceiling | Measured seconds | Passed receipt |
| --- | --- | --- | --- |
| `emdash3_2_one_cat_native_window_snake_right_kernel_quotients.lp` | 4 / 90 | 72.376 | `20260930T141608Z-18a17d6272da41a785c619c87df90f0b` |
| `emdash3_2_one_cat_native_window_snake_right_kernel_pair.lp` | 4 / 180 | 91.939 | `20260930T144119Z-f77b89dbac8f411da14e07215684c898` |
| `emdash3_2_one_cat_native_window_snake_right_kernels.lp` | 4 / 90 | 73.049 | `20260930T142643Z-ffbebd1628674adba435a64b4d5e443d` |
| `emdash3_2_one_cat_native_window_snake_right_homology.lp` | 3 / 90 | 41.378 | `20260930T142757Z-220c88b766db4a0286da5c5bc75902af` |
| `emdash3_2_one_cat_native_window_snake_connecting_covers.lp` | 3 / 90 | 44.085 | `20260930T142840Z-cb91fbb52ea1403bb29e95ffe29437b4` |
| `emdash3_2_one_cat_native_window_snake_connecting_comparison.lp` | 3 / 90 | 59.786 | `20260930T142925Z-3de7ea8a4c314816b9313916fb9b1776` |
| `emdash3_2_one_cat_native_window_snake_surrounding_maps.lp` | 3 / 90 | 51.142 | `20260930T143026Z-bca9e1f4919c49c2a67df8908241d67d` |
| `examples/one_cat_native_window_snake_connecting_comparison.lp` | 3 / 90 | 49.295 | `20260930T143118Z-38d3443090c54eada88f2633069c4dd5` |
| `examples/one_cat_native_window_snake_right_homology.lp` | 3 / 90 | 46.848 | `20260930T143209Z-f2ac1bf5e66f4ef29cac621d7bc0da9d` |
| `examples/one_cat_native_window_snake_right_kernels.lp` | 4 / 180 | 94.318 | `20260930T144252Z-2e5163de5d4a4b1e82127839cc6f6187` |
| `examples/one_cat_native_window_snake_surrounding_maps.lp` | 3 / 90 | 53.224 | `20260930T143624Z-2bed83590b6340de94d1de252b8c0ce7` |

Allocation controls: `/tmp/emdash-window-right-cold-controls-20260930.json`;
complete import group `/tmp/emdash-window-right-import-controls-20260930.json`;
reviewed deadline controls `/tmp/emdash-window-right-time-headroom-20260930.json`.
All successful receipt input hashes are checked against the current checkout
and contain no compiled objects. The scratch package uses explicit runtime
settings rather than its own registry metadata. Required public full formal
validation still follows this bounded metadata correction.

## September 30 cold boundary/middle homology follow-up

Formal job `109943660587` at source `86ae3a78` passes the preceding right-window
fixes, reaches 246 checks, then fails allocation in boundary representatives
(exit 134, 30.559s). Six default-profile targets in its import cone are replayed
source-identically without compiled objects. Every default-GC control fails
allocation. Five pass scoped GC at 2 GiB/90s; middle homology exactness still
fails 2 GiB/GC and passes the existing 3 GiB/90s profile. Native whole middle
exactness and its reviewer pass their unchanged 3 GiB/90s profile. Six exact
bindings are added (153 total); ordinary defaults, formal source, checker,
subject reduction and serial/file/no-swap guards remain unchanged.

| Target | GiB / seconds ceiling | Measured seconds | Passed receipt |
| --- | --- | --- | --- |
| `emdash3_2_one_cat_boundary_representatives.lp` | 2 / 90 | 30.919 | `20260930T160758Z-0a1b080ced1c4578a7492f4c370ba74a` |
| `emdash3_2_one_cat_middle_homology_representatives.lp` | 2 / 90 | 33.704 | `20260930T160852Z-0e5a7abf217443129c218a9aa3dcc982` |
| `emdash3_2_one_cat_middle_homology_cycles.lp` | 2 / 90 | 34.192 | `20260930T160949Z-0bd9232e974a4450a00023fca23aa143` |
| `emdash3_2_one_cat_middle_homology_exactness.lp` | 3 / 90 | 33.149 | `20260930T161123Z-87af221ede434d639ab2fc6a3d6124ba` |
| `examples/one_cat_homology_representatives.lp` | 2 / 90 | 30.149 | `20260930T161221Z-a66bc0241c4c4608b183d791538d20ca` |
| `examples/one_cat_middle_homology_cycles.lp` | 2 / 90 | 32.258 | `20260930T161316Z-841d92062dd8422fbe5b30ec227ac3e2` |
| `emdash3_2_one_cat_native_middle_homology_exactness.lp` | 3 / 90 | 37.051 | `20260930T161550Z-05a83686957e4c1aad981c30de818b6d` |
| `examples/one_cat_middle_homology_exactness.lp` | 3 / 90 | 36.868 | `20260930T162021Z-3a826080f77a44b583705adbbe604e4c` |

Controls: `/tmp/emdash-boundary-cold-controls-20260930.json`;
consumer receipts `/tmp/emdash-boundary-consumers-20260930.json` and
`/tmp/emdash-boundary-reviewer-consumer-20260930.json`. All successful input
hashes match the current checkout. The initial reviewer setup attempt lacked
its file in the scratch package; copying its exact source closure resolves
that setup failure. It is not a typechecking/allocation failure. Required full
public formal validation still follows this metadata correction.
