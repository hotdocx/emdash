# Action-Profile Integration: TypeScript Source Alignment

Date: 2026-09-27 UTC

Status: metadata alignment, complete TypeScript aggregate and all selected live conformance qualified; exact follow-up scope below

Owner: [integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), API-08.
This retains the existing bounded transfer scope, including the recorded
Op/Sigma/Homd qualifications. It introduces no new transfer or metatheory claim.

## Source Identity

The exact pinned predecessor was recovered from Git `f9ae8d6a`. A guarded
canonical export reproduces its existing hashes exactly. The current core is
the selected action-profile integration source; its named extension owners
have separate production validation.

| Evidence | Predecessor | Current |
| --- | --- | --- |
| Source SHA-256 | `f7206b8eed56897ee8483934cd5f9b31348c22865cea20a1257c409eab025e61` | `6a980df34be718a23a6be121d170153650830a49f54b7e0eca415705ffb2068a` |
| Canonical export SHA-256 | `594bbfa447bb383e979d3b082d3ed063d5023d9c0a300f729c34b376cfb229d6` | `7200f0614757bccf2e309703771003511ecd239a4e99433a2890d2049c40b89d` |
| Canonical commands | 1,708 | 1,674 |

Both exports use the pinned `3.0.0-90-gdb4f780` exporter under the serial
2 GiB/90s guard. Export identity is not itself source typechecking or profile
qualification. Exact inputs, commands and settings are in
`emdash2/tmp/probes/api_production_core_export_manifest.json` and the retained
predecessor/current canonical LP files.

## Reviewed Transfer Boundary

All 95 distinct commands selected by the ten current-core acquisition
contracts have unique byte-identical current matches. The existing acquisition
validator first rejects the old source pins with `SOURCE_HASH_MISMATCH`, then
accepts each candidate contract after changing only source/export identities
and the verified command positions. Exact command digests, kind/shape facts,
imports and exporter version are preserved.

The complete referenced-name inventory contains 155 ordinary declarations
whose full canonical signatures and bodies are byte-identical. The three
constructor names `Struct_sigma`, `zero`, and `succ` retain byte-identical
complete `τΣ_`/`nat` parent commands. The existing synthetic
`Obj_func__displayed_chain_mirror` remains a checked transparent mirror of the
unchanged `Obj_func`; it is not relabelled as a source declaration.

The rule inventory contains 184 distinct transferred runtime/proof rule IDs.
Thirty-three predecessor rule/unification commands changed or disappeared in
the larger core. Seventy-eight transferred rules share a head with that change
set; head overlap alone is not evidence of changed behavior. Of these, 67 have
unchanged matching literal source commands. Ten further cases use reviewed
unchanged named-constructor/normal-identity clauses. The remaining uncurry
case specializes the unchanged `uncurry_func_func` definition through the
existing object-composition, postcomposition and fixed-product observations.
Its conformance replay remains part of validation. The generic strict
composition/naturality rules being retired are not silently installed in the
TypeScript profile.

## Provenance Corrections And Application

A separate audit found 107 declaration-provenance ordinal mismatches against
the already pinned predecessor. These are pre-existing metadata defects,
including the `Prof_cat` entry pointing at a displayed-transport theorem.
They are not changes to the named declaration bodies. Binding relocation uses
the actual semantic owner and its complete unchanged canonical text, rather
than moving the erroneous old ordinal blindly.

The reviewed mapping contains 96 distinct provenance bindings, with 81
relocations and no unresolved binding. The pullback object-action reference
is distinguished from the separate component-action clause; Pi decoding's
binder parentheses are canonical formatting. Generated constructor evidence
continues to identify its complete parent command.

The initial patch changed 28 source files: 24 source-hash occurrences, eleven
export-hash occurrences, 71 acquisition positions and 84 provenance positions.
An isolated candidate loader exercised all 28 files. Semantic snapshots of
134 module records, including directly loaded records outside the root barrel,
are identical after removing only provenance metadata: declaration terms,
inductives, runtime/proof rules, ordering, dependencies and external symbols
are unchanged. No additional mathematical owner or rule is transferred.

Six test files that bind current source/export identity or provenance positions
are updated.
The live core inventory now records 814 symbols, 743 rule commands and 91
unification commands, with 504 definitions, 310 assumptions and 777 runtime
clauses. The other counts are unchanged. These vocabulary totals are source
inventory, not transfer or consistency claims. Fresh guarded exports also update the two changed non-core live inventories.
The hom-action owner adds three derived public path helpers and imports the
strict-action owner (81 symbols, no rules). WalkingEnd adds the already
qualified protected recursor boundary and named composition theorem (82
symbols, eleven rule commands/thirteen clauses and one opacity command). These
are source inventories, not added TypeScript transfers; their mathematical
qualification is in the integration owner reviews.

Workspace checks, typechecking, lint and all 37 focused transfer/compiler/runtime
tests pass. The live `check:scale-inventory` gate also passes all fourteen tests
with no skips (22.949s), including the current source/export acquisition contracts
and the reviewed extension inventories. Its log is
`emdash2/logs/api-ts-scale-inventory.log`. One complete
`check:ts`, affected Lambdapi conformance, and final cross-layer gates remain
pending. Historical release decisions and frozen source-world audit evidence
are preserved.

## Recovery

The following files are under `emdash2/tmp/probes/`:

- `api_typescript_canonical_command_audit.json`
- `api_typescript_all_symbol_evidence_audit.json`
- `api_typescript_generated_parent_audit.json`
- `api_typescript_rule_head_audit.json`
- `api_typescript_rule_overlap_classification.json`
- `api_typescript_remaining_rule_bindings.json`
- `api_typescript_provenance_mapping.json`
- `api_typescript_requalified_acquisition_trial.json`
- `api_typescript_pin_patch_manifest.json`
- `api_typescript_before_semantic_ir.json`
- `api_typescript_candidate_semantic_ir.json`
- `api_typescript_alignment_application.json`

The rule-head audit initially used an inadequate head extractor. Its result
was corrected before classification or pin changes; the retained final audit
reports the 78 overlaps above. A candidate-loader check also caught one file
not reached through the root barrel; direct loading covered it before the
patch was applied. Neither preliminary result was treated as qualification.

## Aggregate Follow-Up

The first full aggregate stopped after 34.7 minutes with two failed assertions
and a V8 allocation failure at the explicitly selected 2 GiB heap ceiling.
Its partial result is 1,784 passes, two failures and 43 skips across 1,829
reported tests; it is not a completed aggregate. Log:
`emdash2/logs/api-check-ts-3600.log`.

The failures exposed three active source pins written as concatenated literals,
which the first AST patch missed, and two target-projection expectations still
using their old incorrect ordinals. The pins are now current in the foundation
and target transfer/runtime modules. The reviewed canonical mapping identifies
the projection commands at 1141 and 1143 (unchanged text digests, formerly
misrecorded as 1075/1077). Historical D-020 decision evidence is preserved;
its active policy explanation no longer calls the old ordinal current.

The strengthened tests verify both transfer and runtime source pins. All
fourteen focused tests pass without skips, followed by typecheck and lint.
A fresh active audit verifies all 134 semantic module records against the
preserved pre-migration snapshot and checks every collected source pin against
the actual core. All match, and semantic IR remains identical. Artifacts:
`api_typescript_concatenated_pin_fix.json` and
`api_typescript_active_semantic_ir.json` under `emdash2/tmp/probes/`.
The total source-hash updates are now 27; the changed source-file count stays 28.

The full aggregate is rerunning with a 4 GiB V8 heap and the existing
3,600-second ceiling (`emdash2/logs/api-check-ts-4g.log`). An actual Node test
worker verifies the effective heap limit (`logs/api-node-heap-check.log`).
This rerun includes the reviewed metadata/test corrections, so it is not
labelled an identical-input resource retry. Final aggregate and conformance
qualification remain pending.

The distributable `package:check` gate also passes at the corrected source
snapshot, including packed external consumers, ESM/CJS and browser/algebra
checks (`emdash2/logs/api-package-check.log`). No new transfer scope or
publication is inferred from this packaging evidence.

## Complete Aggregate And Selection-Ordinal Expectations

The 4 GiB aggregate completed without a heap failure in 2,805.112s. It reported
2,948 tests across 478 suites: 2,853 passes, seven failures and 88 opt-in skips.
All seven failures were literal canonical-selection ordinal arrays in the
existing scale-representation tests. The command identities, text digests,
source-phase order, policies and runtime behavior were unchanged.

An AST-scoped test patch matches each entire old ordinal array to exactly one
reviewed acquisition contract in `api_typescript_canonical_command_audit.json`
and uses that contract's unique unchanged-command matches. It changes seven
test files and no implementation. Exact edits and command identities are in
`api_typescript_selection_test_alignment.json`; local declaration/runtime
phase indices are untouched. The focused replay passes 27 tests, with seven
explicit opt-in conformance skips, in 73.363s
(`emdash2/logs/api-ts-selection-ordinal-tests.log`).

The subsequent full 4 GiB/3,600s aggregate rerun is recorded in
`emdash2/logs/api-check-ts-final-ordinals.log`; its green result is below. The preceding complete run is
retained as failure evidence, not relabelled green. Required live conformance
still remains separate from the opt-out aggregate.

## Complete TypeScript Gate Passed

The final 4 GiB aggregate exits zero. Workspace contract, test registration,
typecheck, lint and the complete contributor suite pass. The test process
reports 2,948 tests across 478 suites: 2,860 passed, zero failed/cancelled,
88 opt-in skips, and 3,323.092s duration. Log:
`emdash2/logs/api-check-ts-final-ordinals.log`. The post-run evidence index is
`api_typescript_complete_gate_evidence.json`; it identifies the actual command
and log hash without pretending to be an immutable runner-generated receipt.

This closes the aggregate gate at the corrected source/test snapshot. The
skipped opt-in Lambdapi conformance checks remain required under their own
commands. No later TypeScript implementation change is currently planned;
carry this green aggregate forward for that unchanged boundary.

## Module Acquisition Follow-Up

The final `check:scale-module-stress` run correctly rejected the additional
Eq1 hom-action acquisition contract's stale source digest. This is separate
from the earlier core-only acquisition audit. A read-only canonical comparison
finds all 58 selected protected/public hom-action commands and all 25 selected
evidence-property commands byte-identical to their recorded command hashes.
The hom-action owner adds one import and three unselected public wrappers;
its selected ordinals move to `2..33,37..60,62,63`. Its late fibre-transport
change is outside this acquisition selection. The evidence-property source,
export and ordinals are unchanged. Selected byte totals remain 63,945 and
14,614. Audit: `api_scale3b_alignment_audit.json` under the production probes.

The hom-action acquisition metadata now pins source `c707cf7c` and canonical
export `ba709099`, includes the actual strict-action import, and uses those
exact relocated ordinals. No selected command text, proof body, transfer or
runtime term changes. The focused test also checks both source digests without
an opt-in flag, so an ordinary test run now detects this source drift.
Historical completed audit reports retain their old snapshots.

The live module retry passes all eight tests, including local dependency
closure and the unchanged root prerequisite audit. Typecheck and lint pass;
all 134 transferred semantic module records remain unchanged. Logs:
`api-final-check-scale-module-stress-aligned.log`, `api-scale3b-typecheck.log`
and `api-scale3b-lint.log` under `emdash2/logs/`. Across the nine selected live
conformance commands, 102 tests pass with no failures or skips; the exact
combined index is `api_final_conformance_qualification.json`.

The preceding full `check:ts` result remains evidence at its recorded snapshot.
This subsequent acquisition-metadata and focused-test update is qualified by
its exact command audit, live eight-test module suite, typecheck and lint.
No shared engine, public barrel or package setup changed, so the proportional
validation policy carries the full aggregate forward without another complete
run. Do not claim that the preceding aggregate itself ran on this later edit.
