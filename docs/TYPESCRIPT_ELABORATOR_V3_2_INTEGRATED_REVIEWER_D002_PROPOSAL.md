# H-DTTLF-PRODUCT-REVIEWER-CORRECTION-01 — Active Export-Pin Correction

Date: 2026-07-30
Gate: H-DTTLF-PRODUCT-REVIEWER-CORRECTION-01
Proposed-Decision: D-DTTLF-PRODUCT-REVIEWER-002
Status: frozen, bounded, non-self-authorizing correction proposal
Depends-On:
[`TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_D001_REVIEW.md`](./TYPESCRIPT_ELABORATOR_V3_2_INTEGRATED_REVIEWER_D001_REVIEW.md)
and the active kernel checkpoint `89afe5f64710b99a262ff92cb193e2742a11827f`

## Measured Problem

Final validation of the integrated reviewer reached the existing live
`check:scale-inventory` gate and exposed stale current-authority evidence. The
active source was already pinned at:

```text
sha256:ccda94c638af8d4fa7ce122967dcc30159c713846eedd53cee0df83123b48a11
```

but several older current-core contracts still recorded the preceding
canonical export digest:

```text
sha256:18500d46d4ff3583fef1f25a3c28eff7b849a61d528a6f9e20e89b32db13f1b2
```

Two consecutive exports with Lambdapi `3.0.0-90-gdb4f780` reproduce:

```text
sha256:91f0deb710b93acc55aa3a6f947505de973b9deaa94d68e1a213037dfcc9c3d3
```

The active export has 1,472 commands. Relative to the stale inventory it has
one additional runtime-rule command:

| field | stale current pin | measured active value |
| --- | ---: | ---: |
| `rule` commands | 620 | 621 |
| runtime clauses | 656 | 657 |

All other command-kind and shape counts are unchanged.

## Exact Selection Audit

A fresh canonical inventory found all 73 commands selected by the eight
current core acquisition contracts. Every selected command retains its exact
kind, metadata, and text SHA-256. No selected command is missing or
textually changed. Twenty-five selections retain their prior ordinal; the
following 48 selections were deterministically reordered:

| contract | exact old-to-active ordinal changes |
| --- | --- |
| `SCALE-STRESS-2-UNCURRYING` | `section-category 961→977`; `sigma-category 981→997`; `sigma-projection-pullback 991→1008`; `sigma-section-comparison 995→1013` |
| `SCALE-STRESS-2-INTERNAL-PI` | `pullback-family 926→928`; `pullback-fibre 927→929`; `pullback-family-functor 930→932`; `pullback-functor-object 931→933`; `constant-family 936→938`; `constant-fibre 939→941`; `constant-pullback 941→943`; `section-functor 969→985`; `section-functor-object 970→986`; `package 972→988`; `package-component 973→989`; `pullback-package 974→990`; `pullback-fold 975→991`; `pullback-component 976→992` |
| `SCALE-STRESS-2-PI-BASE-ACTION` | `fibre-category 925→927`; `transport-left 1074→1098`; `transport-right 1075→1099`; `internal-cell 1095→1119`; `section-pullback 1189→1218`; `internal 1195→1226`; `pullback 1196→1227` |
| `SCALE-STRESS-2-SIGMA-TRANSFOR` | `telescope-family 1006→1028`; `telescope-fibre 1007→1029`; `uncurrying-owner 1009→1031`; `fibre-functor 1056→1080`; `displayed-component 1058→1082`; `object-component 1068→1092` |
| `SCALE-STRESS-3-PROFUNCTOR-BOUNDARY` | `definitional-isomorphism 577→578`; `category 1198→1229`; `classifier 1202→1233`; `comparison 1232→1263`; `tensor 1262→1293` |
| `SCALE-STRESS-3-PROFUNCTOR-COMPARISON` | `forward-arrow 578→579`; `inverse-arrow 579→580`; `vertical-map 1204→1235`; `push 1233→1264`; `pull 1234→1265` |
| `SCALE-STRESS-3-PROFUNCTOR-TENSOR-ACTION` | `product-category 661→662`; `product-object 663→664`; `product-hom-category 680→681`; `map 1264→1295`; `functor 1265→1296`; `object-action 1266→1297`; `arrow-action 1267→1298` |

The seven `SCALE-STRESS-1` core selections and all three declarations in its
separate Nat-module contract retain their exact ordinals and text.

## Proposed Exact Correction

The correction may change only these nine active evidence files:

```text
src/v3_2/directed_continuation_transfer.ts
src/v3_2/directed_continuation_runtime_transfer.ts
src/v3_2/scale_stress_1_acquisition.ts
src/v3_2/scale_stress_2_acquisition.ts
src/v3_2/scale_stress_3_acquisition.ts
tests/v3_2_lambdapi_export_inventory_tests.ts
tests/v3_2_lf_transfer_tests.ts
tests/v3_2_lf_transfer_compiler_tests.ts
tests/v3_2_lf_transfer_runtime_tests.ts
```

Within that boundary it may:

1. replace only current-authority core export pins with the measured
   `91f0…d3` digest;
2. update the 48 exact ordinals listed above;
3. advance the eight affected core acquisition-contract revisions from
   suffix `-1` to suffix `-2`;
4. update the live core inventory from 620 to 621 rule commands and from 656
   to 657 runtime clauses; and
5. update matching current-provenance test expectations.

The old `18500…1b2` digest must remain unchanged where it is deliberately
named `historicalScaleContractSha256` or described as historical audit
evidence in:

```text
src/v3_2/categorical_displayed_nd_higher_audit.ts
docs/TYPESCRIPT_ELABORATOR_V3_2_DISPLAYED_BRACKET_PLAN.md
```

Git history remains the authority for the superseded `-1` contract values.
No compatibility alias or second acquisition path is required.

## Required Validation

Before joining the reviewer implementation checkpoint, the correction must
pass:

1. a fresh all-contract acquisition selection against the active export;
2. `./scripts/pnpmw run check:scale-inventory`;
3. the affected transfer/compiler/runtime focused tests;
4. `EMDASH_TYPECHECK_TIMEOUT=60s make -C emdash2 check`;
5. `./scripts/pnpmw run check:conformance`;
6. the integrated reviewer/browser gate and final root aggregate;
7. `git diff --check`; and
8. exact path-scoped staged review plus `git diff --cached --check`.

## Explicit Non-Effects

This proposal authorizes no Lambdapi source, mathematical owner, declaration,
runtime/proof/unification rule, TypeScript semantic rule, Core node,
checker/evaluator behavior, parser behavior, browser behavior, dependency,
lockfile, deployment, publication, or bulk-scale implementation change. It
does not weaken a hash, ordinal, metadata, or text-digest check. It corrects
those fail-closed checks to the already-active deterministic authority.

It also authorizes no push, merge, PR, release, amend, rebase, reset, history
rewrite, cleanup, branch/worktree deletion, or publication.

Implementation requires a separate exact review. Any human decision may
supersede the proposed delegated review.
