# Endpoint Investigation: User-Directed Deferral

Date: 2026-09-11
Checkpoint baseline: `d6be8db530f6b3174de991a4efcc6c31996b6102`
Active mathematical baseline: `ff139362be71dfec03142d05dda2dc123b3624a5`

The user explicitly requested deferring the endpoint-proof issue and
stopping the Lambdapi debugging detour. Continue with the checked bounded
iterator, formal/proof–CAS boundary audit, book and consolidation. This
archive is recovery evidence, not an active continuation queue or a set of
promoted library changes. The
[living plan](../../../docs/TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md#current-user-direction-finish-the-remainder-defer-endpoint-debugging)
records the authoritative deferral and remaining work.

Structure/record types with primitive projections, instead of nested Sigma,
remain an explicitly requested option for a later review. The narrow failed
probes do not establish that this broader design is infeasible.

## What Was Established Before Stopping

- The evidence classifiers themselves can reproduce the resource failure;
  comparing proof inhabitants is not necessary.
- Both arrows of a native row compare quickly. Its whole transformation and
  naturality proof also compare quickly. The additive terminal-to-zero and
  zero-composition proofs fail at the indexed native endpoints, even with
  an independent flat preadditive parameter.
- `homology_zero_minimal_native.lp` reduces the failure to an additive law
  at native zero-cone projections: it needs no H, short-exact rows, windows
  or Abelian package. Plain indexed endpoints pass. Abstract views over the
  same native source category pass; concrete source/abstract target passes,
  whereas abstract source/concrete target fails.
- The concrete target normalizes to application of the second product-
  functor projection of a totalized displayed Sigma projection. The direct
  nested-pair target is not its runtime normal form, because the generic
  arbitrary Sigma-map object view is proof-time. Using that direct target
  also fails the additive-law comparison.

These are computational-cost distinctions, not counterexamples to the
mathematics. No equality eliminator guard, universal selection, whole H or
delta operation was changed.

## Mathematical-Owner Probes Not Promoted

Two direct strict-naturality unifiers permit the same generic theorem to
have a single reflexivity proof. Their owner and five positive/four negative
controls pass in the private owning-module copy. The real row-zero comparison
still fails. The owning replacement is exactly the content of the archived
`homology_naturality_direct_usability.lp`, placed at the original
`emdash3_2_strict_transfor_component_paths.lp` owner.

A proposed stable nested-Sigma target observation passes source/SR and
strict LHS audit. Normal-form queries confirm that its fold really fires in
both import orders. The small law, row-zero, source-pair and canonical-delta
consumers still fail under the guard. No owning-library promotion or general
higher-action qualification is claimed.

All these tests use normal subject reduction. Warnings were not used as a
veto; the decisive consumers failed under the 2 GiB/90-second resource guard.

## Private Checker Experiments Not Adopted

Both private variants start from Lambdapi revision
`db4f7809961b8c107247613067fb567491fb0b84`. They attempt sufficient same-head
argument congruence before expensive unfolding, with a shared comparison/
weak-head fuel counter. Failure or fuel exhaustion rolls back speculative
reference changes and falls back to the original evaluator. Fuel zero disables
the attempt. This introduces no intended new conversion equation or
injectivity assumption; implementation qualification remains unfinished.

| Experiment | Result |
| --- | --- |
| Left-first, fuel 0, reduced native law | Allocation failure in 8 seconds |
| Left-first, fuel 512, same source | Completes in under 1 second |
| Right-first, fuel 512, same source | Completes in about 1 second |
| Erasing/nonlinear rewrite controls | Pass; seven assertions, including fuel-one fallback |
| Left-first, fuel 512, existing target-cycles proof | 90-second timeout |
| Right-first, fuel 512, same prerequisite | 90-second timeout |
| Disabled-mode control on that prerequisite | Completes in under 1 second |

The left-lift prerequisite also slows to roughly 54–56 seconds in the enabled
variants. The subsequent source-boundary-zero and actual indexed H/delta
roots were not reached in these stopped dependency runs. Do not claim those
comparisons were fixed. The installed checker was never replaced, and no
mathematical source was promoted using only private-checker success.

`variants/checker/left-first.patch` and `right-first.patch` recover the exact
changes to `src/core/eval.ml`. Their private executable hashes are recorded
in the manifest; binaries and compilation objects are not archived. Builds
used `dune build -j 1 --profile release --only-packages lambdapi
src/cli/lambdapi.exe` through the resource guard. Each binary has a separate
source-checked environment; the driver rejects a changed binary or source
rather than mixing marshalled objects.

No checker or build process remained running at deferral. Do not restart
these experiments without a separately requested follow-up.

## Recovery

[prototypes.patch](prototypes.patch) recovers forty source/patch snapshots
into an EMPTY directory. [manifest.json](manifest.json) records statuses,
byte counts, hashes and the private executable identities.
[verification.json](verification.json) records successful exact recovery.
The prior indexing, canonical-degree and proof-projection archives supply
reused probe dependencies; active dependencies remain at the recorded
mathematical baseline. The local whitespace exemption preserves raw patch
contents only.

Representative retained logs under `emdash2/logs/probes/`:

- `homology_zero_minimal_native-leaf-20260911-011536.log`
- `homology_zero_minimal_source_only-leaf-20260911-011814.log`
- `homology_zero_minimal_target_only-leaf-20260911-011822.log`
- `homology_nested_target_normal_form_first-leaf-20260911-013443.log`
- `naturality-owner-20260911-010616.log`
- `bounded-congruence-fuel0-20260911-015046.log`
- `bounded-congruence-fuel1-20260911-015138.log`
- `bounded-congruence-fuel512-20260911-015139.log`
- `bounded-congruence-fuel512-20260911-015344.log`
- `bounded-congruence-fuel0-20260911-015824.log`
- `bounded-congruence-fuel512-20260911-020015.log`.

The unresolved op/Sigma variance notices remain separate inherited boundaries.
This investigation neither repaired them nor used an invalid reversal as a
mathematical construction.
