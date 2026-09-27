# Action-Profile Integration: TypeScript Source Alignment

Date: 2026-09-27 UTC

Status: metadata alignment, focused tests and live inventory qualified; aggregate and conformance validation pending

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

The applied patch changes 28 source files: 24 source-hash occurrences, eleven
export-hash occurrences, 71 acquisition positions and 84 provenance positions.
An isolated candidate loader exercised all 28 files. Semantic snapshots of
134 module records, including directly loaded records outside the root barrel,
are identical after removing only provenance metadata: declaration terms,
inductives, runtime/proof rules, ordering, dependencies and external symbols
are unchanged. No additional mathematical owner or rule is transferred.

Four tests that explicitly bind current source/export identity are updated.
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
