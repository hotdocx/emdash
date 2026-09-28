# Action-Profile Integration Acceptance Audit

Date: 2026-09-27

Status: complete; all acceptance gates and semantic checkpoint `8ea6c86b`
verified, with a clean local handoff.

Plan: [living integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md).
Detailed execution evidence: [production continuation](EMDASH_ACTION_PROFILE_PRODUCTION_CONTINUATION.md).

Subsequent user-requested book review and local main integration are recorded
in the [main integration review](EMDASH_ACTION_PROFILE_MAIN_INTEGRATION_REVIEW.md).
The main/branch statements below describe this completed goal's handoff
snapshot, before that separately requested follow-up.

## Scope And Revision Identity

The goal reimplements donor `114dc19fdee4b952f1c75be4e2000d6ff7195741`
against main `37ce19d5c727f8d1c5579445981a8f4f6d3f32d4` in
`/home/user1/emdash1-action-profile-integration-v1`, branch
`goal/action-profile-integration-v3.2`. Main remains an ancestor of the goal
branch. Main and donor worktrees remain unchanged.

Implementation checkpoint: `8ea6c86bda894b32a33db13b52ba51b92fd701f5`. All 332 committed
file blobs match the reviewed qualification/staging manifest, and clean Git
status is verified. The final documentation checkpoint only closes the plan
and handoff records. No push, main merge, PR, publication, history rewrite or
cleanup belongs to this acceptance boundary.

Passing checks qualify the recorded interfaces and observations. They do not
prove unrestricted consistency, confluence, normalization or model adequacy.

## Requirement Evidence

| Requirement | Inspected evidence and present result |
| --- | --- |
| Account for the donor solution by owner | The [inventory](EMDASH_ACTION_PROFILE_INTEGRATION_INVENTORY.md) records all 114 donor paths, sixteen declaration seeds, thirteen composition-theorem consumers and twelve semantic owner groups. Its source audit accounts for all 81 LP paths: 68 exact donor files, ten adaptations and three retained-main files. Every donor-added library symbol has a current owner. Presence alone is not semantic qualification. |
| Replace generic strictness with the selected action profiles | Production owners and the complete library sweep are qualified. The registered precomposition, postcomposition, vertical-fold and telescope controls cover the demonstrated leaks and their profiled alternatives. Constructor-specific computation, normal identities and projection-order controls remain. See `API-04`, `API-04R/V/P/T` in the plan and inventory. |
| Retain the accepted assembly baseline | The [assembly review](EMDASH_ACTION_PROFILE_ASSEMBLY_BASELINE_REVIEW.md) records inherited ordinary/displayed inverse constructors, both inverse slots, component betas and cancellation assumptions. The derived retained-member proof remains. `examples/action_profile_inherited_assembly_controls.lp` passes in the production reviewer sweep. This remains an assumption boundary, not an adequacy proof. |
| Preserve current main's whole native consumers | `api_final_acceptance_identity_audit.json` rechecks byte identity of six selected primary owners with main: kernel/cokernel adjunctions, whole homology families, native snake inputs, native connecting, the six-term result and Freyd adjunction models. Adapted downstream observations retain their existing profiles, original K/Q/H and supplied inverse choices. All registered native reviewers and the original 94-assertion production CAS corpus pass. |
| Preserve the guarded paired-family reindexing path | The scoped product/diagonal owner retains the literal composite argument and every factor. The original native consumers and `examples/product_diagonal_reindex_views.lp` pass; recorded different-factor/runtime controls remain. The production continuation identifies the owning proof and comparison. |
| Integrate the bounded Gray/path-cubical source work | The [consolidated review](EMDASH_ACTION_PROFILE_CONSOLIDATED_NATIVE_CAS_REVIEW.md), source dispositions and complete reviewer sweep qualify the 22 owners and seventeen path-cubical reviewers, with the classified Gray graph. Native dimensions 0–2 and conditional dimension 3 retain the recorded readback/groupoidality boundary. |
| Preserve the other affected main consumers | The complete 791-library sweep and 596-reviewer sweep cover the current registered adjunction, Hom-comparison, represented-comma, Gamma/H, monad, product, pullback, slice, presheaf/sheaf, simplex and groupoidification consumers. Earlier combined owner reviews remain scoped interaction evidence; complete formal CI now passes on the actual production sources. |
| Align TypeScript without expanding its trusted/transfer scope | The [source-alignment review](EMDASH_ACTION_PROFILE_TYPESCRIPT_SOURCE_ALIGNMENT.md) records unchanged semantic IR for 134 module records, corrected provenance and inspected source pins. The complete TypeScript aggregate passed 2,948 tests: 2,860 passes, 88 opt-in skips and zero failures. All nine selected live conformance suites passed 102 tests without skips. The later Eq1 metadata adjustment retained all 83 selected command texts and passed its focused suite, typecheck and lint; the earlier aggregate is not represented as having run on that later edit. |
| Register reproducible resource limits | The [resource record](EMDASH_ACTION_PROFILE_RESOURCE_QUALIFICATION.md) records 98 exact-target overrides, including 33 measured reviewer increases. Defaults remain 2 GiB/90s. Registry membership is unchanged; 58 focused registry/metrics/staged-adapter/native-profile tests pass. All nine cold recipes pass in the completed formal gate. |
| Complete source and rule hygiene | The current catalog has 2,432 central diagnostic assertions and zero unclassified entries. `api_complete_reviewer_lhs_audit.json` covers 244 changed/new registered LP files, with zero unreviewed slots and 64 annotated slots. This is an advisory slot audit; the owner reviews carry the warning/overlap qualifications. No library source changed during the final reviewer repairs. |
| Keep authority and published-source descriptions aligned | The current SOP, Foundations, canonical syntax, README, book and authored overview describe opaque profiles, retained normal identities, lax composition and the explicit inherited assembly assumption. Owning package/template/local artifact gates passed. The latest local artifact receipt is `publication-20260927T122134Z-459c3851610a4a649585b9300b82cf9f`, covering the 416-page book and 19-page article. No distribution publication occurred. That artifact receipt still matches every current input. The refreshed template gate `reviewer-20260927T170021Z-6acac73f3d1a46718100c25e0946ca7e` passes on current inputs. |
| Complete formal CI | **Passed.** `formal-20260927T164506Z-d45cf3135aaa42c8a51b128f5e319355` records actual `make -C emdash2 ci` exit zero in 9,430.511s. All 1,388 targets pass: 1,308 individual checks and 80 targets across nine isolated groups. The remaining tooling, registry, book, source-reference, LHS and catalog gates also pass. |
| Replay the retained production CAS corpus | **Passed.** Eight original, byte-identical artifacts pass all 94 assertions on the final production closure. All eight final fresh receipts, source/object inputs and log hashes are verified in `api_final_clean_source_acceptance.json`; individual results are listed below. Earlier prototype receipts are not substituted for this result. |
| Generate checked health | **Passed on current source.** The owning formatter generated the refreshed report from 370 fresh affected checks and 1,018 verified exact-input reused successes. All 1,388 zero exits, current source/content hashes and report data were checked. `api_whitespace_health_evidence.json` records the current report and payload hashes. Original CI and group timings retain their original scope; group shares are not individual execution times. |
| Finish a clean, reviewable local branch | **Passed.** Semantic checkpoint `8ea6c86b` contains the exact 332 reviewed files. Every committed blob matches `api_final_implementation_staging_manifest_v2.json`; `api_semantic_checkpoint_evidence.json` records clean status. The goal branch retains pinned main ancestry, and main/donor references are unchanged. |

## Final Gate Evidence And Identity

`emdash2/tmp/probes/api_all_production_reviewer_resume7_results.json` records
the completed 596-target sweep. The original failed states remain preserved;
each continuation verified every predecessor input before reusing its result.
All 24 cold-recipe reviewers also produced nonempty compiled outputs in that
sweep. Compiled-parent reviewer checks do not replace cold recipe checks.

`api_final_acceptance_identity_audit.json` rehashes all 1,389 registered
source/package inputs against that completed sweep, verifies the 596 success
receipts, and checks the retained TypeScript log/core hashes and six primary
native owners. These are source/evidence identity checks. The separate
`api_final_success_receipt_audit.json` now verifies the completed formal and
CAS receipts against the current source/object inputs and raw log hashes.

The serial CI → production CAS → checked-health sequence completed with exit
zero while the conversation was paused. Both process handles are terminal.
The only formal-gate input changed by that sequence is the health report
rendered from its actual metrics; its recorded before/after hashes are
verified. Subsequent source edits only close status documentation. Staging subsequently identified trailing whitespace/extra final blank lines
in ten newly added LP files. The cleanup preserves every token, and compiling
the three affected library files produces byte-identical objects. No
TypeScript, runner, resource-registry, declaration or rule behavior changes.
The raw LP hashes do change, so their 370 dependent targets have been checked afresh;
1,018 successes with exact unchanged receipt inputs are reused. None of
the nine cold groups is affected. The subsequent eight-artifact CAS replay
passes all 94 assertions and checked health matches the final source.

The formatting follow-up is recorded in `api_final_whitespace_cleanup_manifest.json`,
`api_whitespace_resume_preparation.json`, `api_whitespace_health_evidence.json`
and `api_final_clean_source_acceptance.json`.
It uses the owning `check_metrics.py --resume` workflow after verifying every
cached result against actual prior source/object, runner and checker inputs.
The first follow-up wrapper stopped only on a report-order comparison after
all checks passed: JSON sorts source-metric keys, while the owning report
preserves source order. Restoring the original order reproduces the report
exactly, without changing its data or rerunning the checks. That wrapper
failure remains preserved; the subsequent CAS run is separately successful.
No previous failed or successful receipt is rewritten. The qualified semantic
checkpoint and clean-worktree verification are complete.


| Production CAS artifact (final cleaned source) | Assertions | Seconds | Fresh receipt |
| --- | ---: | ---: | --- |
| `api_cas_les_diagram.lp` | 48 | 18.369 | `20260927T212920Z-1f617a0c505147b8b9ea1eb07149439a` |
| `api_cas_les_displayed_exactness.lp` | 7 | 30.672 | `20260927T212941Z-9025702e3b704559ac6626a95317d48f` |
| `api_cas_les_exactness_0.lp` | 3 | 20.102 | `20260927T213015Z-e3bebfd9694b4b3283b40a8116b1c161` |
| `api_cas_les_exactness_1.lp` | 3 | 20.527 | `20260927T213037Z-e48b6a1cecc44c668898f7f57271a34d` |
| `api_cas_les_exactness_2.lp` | 3 | 21.109 | `20260927T213100Z-15a625626e1943739f1d2ed9286a9577` |
| `api_cas_snake.lp` | 15 | 13.790 | `20260927T213123Z-257f1087291e4c2cb6955753980e69cc` |
| `api_cas_snake_certificate_signatures.lp` | 10 | 19.415 | `20260927T213140Z-bab46395906a482b958407cc3c9b81b3` |
| `api_cas_snake_certificate.lp` | 5 | 19.862 | `20260927T213202Z-8cc0e1f55bdc42c2b1d507ff0c97a16d` |

All nine cold-recipe receipts and their exact member counts are recorded in
`api_final_cold_group_evidence.json`. The original failed aggregate and
reviewer attempts remain preserved as failure evidence.

## Retained Exclusions

The explicit-profile assembly redesign remains deferred as `API-05R`, with
its investigation and unfinished obligations preserved. No counterexample
to the exact inherited assembly primitive has been established here.

Op/duality repair, unrestricted Sigma-Hom/Homd repair, further Empty audits,
fully lax units, general oplax/pseudo redesign, the large six-term package
comparison, new Groupoidify adjunctions, closed model construction and
spectral/stabilization work remain separate goals. This integration does not
claim unconditional higher cubical readback, general Cartesian substitution
or full Kan structure. Those exclusions do not waive a regression in the
selected baseline's existing consumers.

## Local Handoff

The implementation is ready for review on `goal/action-profile-integration-v3.2`
in `/home/user1/emdash1-action-profile-integration-v1`. Main remains pinned at
`37ce19d5`; donor remains `114dc19f`. Their sources and histories are unchanged.
All background validation processes are terminal. Main merge/publication is
outside this completed local goal and needs separate user authorization.

The living inventory accounts for every donor path, while the production
continuation retains failed attempts, exact successful receipts, formatting
follow-up and resource measurements. The accepted inherited assembly baseline
and every explicitly deferred research boundary remain as recorded above.
