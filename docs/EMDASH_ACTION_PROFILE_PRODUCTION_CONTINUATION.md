# Action-Profile Production Continuation

Date: 2026-09-27 UTC

Status: active, uncheckpointed semantic integration; full qualification remains pending

Owner: [integration plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), API-04/05/09/10.

The previous goal turn made progress: checkpoints `388a3e71` and `6bb2fc07`
qualified native/CAS/cubical consumers and complete central diagnostics. This
turn applies their permanent names and resumes production validation. The
current source tree, not the earlier prototypes, is the active authority.

## Applied State

- Base checkpoint: `6bb2fc07`; branch `goal/action-profile-integration-v3.2`.
- The 190-file preparation is applied, with 21 named helper owners and 94
  symbol renames. Active code round-trips through the naming map.
- Registry: 792 core and 596 reviewer targets, 634 in the check suite.
- The old generated objects are retained at
  `emdash2/tmp/probes/api_pre_promotion_objects_20260927T045154Z/`.
  Only 128 current-core objects with exact transitive source matches were reused.
- The promoted mathematical/TypeScript source is still uncommitted; the
  production semantic tranche is not claimed green. Main/source-reference
  worktrees are unchanged. Tooling and progress-document checkpoints are
  separate from that pending semantic checkpoint.

Exact preparation/application files are
`emdash2/tmp/probes/api_production_preparation_manifest.json`,
`api_production_application_manifest.json`, and
`api_production_reused_objects_manifest.json` in the same directory.
The renamed central source passes at 6 GiB/180s, receipt
`20260927T044822Z-78265a8d177e4b1494f56b0c5ed2830d` (65.473s).

## Selected Kernel/Cokernel Map Interpretation

The initial production sweep stops at target 126/790, receipt
`20260927T050104Z-5794dc52737d4005947e6d8cd223f652`.
Preadditive Hom sethood alone does not supply OneCat. A raw diagram
transformation no longer supplies strict component naturality automatically.

The repaired presentation owners preserve the existing whole K/Q, adjunction,
selected object and inclusion/projection interfaces. Their generic
`profiled_*_presentation_map_semantic` and `profiled_*_presentation_map_path`
operations require profiles of the actual diagram transformation and
inclusion/projection. They derive the comparison through existing kernel/
cokernel uniqueness. The ordinary public wrappers take OneCat and derive those
profiles; they do not choose replacement kernels, cokernels or maps.

The old generic selected-map unifiers are retired. A kernel-source and a
cokernel-target comparison address the observed implicit object-frame
mismatch inside composition. Both sides must contain the same two arrows;
all remaining category/object arguments are compared through the existing
presentation observations. These are proof-time comparisons, not new runtime
rules or generic strict-functor laws.

The joint review passes in 6.703s at 2 GiB/90s:
`20260927T053310Z-d0ca5d1121f949af981e2ad5c3b9981d`.
It includes both actual reviewers, generic-profile cases without OneCat,
positive metadata comparisons, runtime distinction, rejection of a different
arrow, and ambient composition/naturality noncollapse. Both strict LHS audits
have zero candidates. Source-identical controls with the respective metadata
comparison removed fail as expected:
`20260927T053421Z-265791a144f544ffa6bb91e0a79b4b01` and
`20260927T053423Z-2d3ae27d95e7458c9ed761f4f403fc28`.

The repair is installed in both presentation owners and their reviewers, with
new `kernel_presentation_metadata_comparisons` and
`cokernel_presentation_metadata_comparisons` reviewers. The exact installation
is `emdash2/tmp/probes/api_selected_presentation_installation.json`; trailing
whitespace was subsequently removed without changing active code.

## Running Work And Next Action

Production compilation is serial with warnings and subject reduction. It uses
registered per-target limits and explicit GC `o=20,v=1024`; the known renamed
Freyd pair body has its previously qualified 8 GiB/300s compilation profile.
No defaults were raised.

The production compilation passed selected H views, zero-cone consumers and
both generic kernel/cokernel record owners. It then stopped at the ordinary
factor-space adapter, target 468/791, receipt
`20260927T075747Z-8d32cbf9d7bd4e51954cbad1dee26e30`. The driver session is
closed; its state is
`emdash2/tmp/probes/api_production_compile_record_resume_results.json`.
The adapter/record and map-factor/chain-map repairs below are installed.
The serial sweep has resumed with state
`api_production_compile_homology_observers_resume_results.json` and driver
`api_compile_production_homology_observers_resume.py` in the probe directory.
Successful prefixes are reused only when source and dependency-object hashes
still match. Prior failures and receipts remain preserved.

The first-exactness and second-representatives targets passed source/object-
identical 3 GiB/90s retries after 2 GiB allocation failures. The latter failed
while serializing and left an empty object despite process exit zero; the
runner correctly rejected it and the empty output is preserved under
`api_failed_second_representatives_object/`.
Receipts: `20260927T060129Z-7986849370614683abcb891993a0779a` and
`20260927T060704Z-98774124033a4989875faf6da47eaa41`.

The temporary sweep now retries only measured resource failures with identical
source/dependency-object inputs. The bounded memory ladder is 2/3/4/6/8 GiB;
deadlines are 90/180/300/600s. It preserves failed outputs and every attempt,
keeps all guards and GC settings, and stops on semantic failures or exhaustion
of the supported ceilings. This implements the standing authorization without
changing repository defaults. Durable clean-checkout profile routing remains
part of the final DevOps gate.

The selected mate interpretation is installed. `terminal_arrow_kernel_test`
and its cokernel mirror already require OneCat; the selected helpers now
forward that guard. Whole transpose/untranspose functors stay generic.
Companion comparisons retain the same chosen operation/test arrow through
both raw and stable evaluated-inverse projections. The joint actual mate
reviewers pass in 14.900s at 2 GiB/90s, receipt
`20260927T055950Z-08d470bea126432fa8e081fe1dd8868e`. Installation is recorded
in `api_selected_mates_installation.json`; both production owners also pass.

The selected H observations and zero-cone consumers are installed and pass.
Their actual joint reviewers pass in 24.557s at 2 GiB/90s, receipt
`20260927T074112Z-b8888fbce59747d4bbe4d7eef882b65e`. Selected point/object
observations forward the existing OneCat guard; the generic profiled map path
requires the actual diagram/projection profiles, with an ordinary wrapper.
The whole H-family owner remains unchanged. Two obsolete raw H-composition
assertions are now negative controls paired with existing OneCat composition
paths on the same original H. Identity, map, unrelated-arrow and next-Hom
observations are retained. Exact installation is
`api_selected_homology_installation.json`.

The kernel/cokernel record adapter needs no new OneCat premise. Its selected
computational kernel/cokernel already supplies annihilation. The new body
transports this law along the existing complete object-and-structural-arrow
frame agreement, as the owner already does for universality. Both original
reviewers pass in 12.377s at 2 GiB/90s, receipt
`20260927T075050Z-7141744d00c64b6585406f5e34422d84`. Public signatures, whole
K/Q objects, structural arrows, operational lift/colift and reconstruction
paths are preserved. There is no new assumption, rule or operational data
transport. Only the two law bodies and their header explanation changed;
installation is `api_record_annihilation_installation.json`.

The ordinary factor-space adapter and homology-family record now forward the
OneCat evidence already required by their annihilator/chain-pair input.
Existing OneCat family and raw-chain-pair callers pass it through. Their four
actual reviewers pass jointly in 53.998s at 3 GiB/90s, receipt
`20260927T080021Z-5573a13a9a424e19aea2a98a3281dd27`. The source/object-identical
retry follows a 2 GiB allocation failure while importing the fourth,
image/coimage reviewer (`20260927T075927Z-053d962078c04c3c8a9b8a4bc6c88ce4`).
Whole K/Q/H, semantic boundary arrows and reconstruction are unchanged.
Installation is `api_homology_record_guards_installation.json` (four owners,
two reviewer updates).

The map-factor and raw-chain-map repair is installed after its joint actual
reviewers pass in 49.525s at 3 GiB/90s, receipt
`20260927T080523Z-fd2b1cad3b874846b492041f6be84c1e`. The source/object-identical
retry follows a 2 GiB allocation failure in later record dependencies
(`20260927T080430Z-94663bb305ec47b0a67ea4dfcab3328c`). Three old unqualified
naturality calls and the untranspose-square call now use existing OneCat paths.
The actual raw-chain-map caller already supplies OneCat; its witness is
forwarded through boundary naturality and native cone-map introduction.
Whole inclusion/projection transformations and the next-Hom reviewer remain
generic. Original maps, lift choices, reconstruction, both constructor
projections and unrelated-arrow negative controls are retained. No rewrite,
unification rule or axiom is added.

The first two attempts exposed the obsolete boundary-naturality and
untranspose-square calls, respectively:
`20260927T080156Z-3d20616fbfd34d8c8a68b3b2f666385a` and
`20260927T080301Z-fb03f590a90646f68c1f1ba21a8bccb5`.
Installation is `api_homology_map_factor_guards_installation.json` (five
owners, two reviewer updates); `api_homology_observers_installation.json`
combines the exact identities with the preceding record repairs for resumption.

Further work: complete all remaining production owners/reviewers; refresh
source comments, authority claims, catalog/health/book; align affected
TypeScript profiles and run required formal/cross-layer gates. The active
authority prose is being synchronized, but several historical transitional
paragraphs and the inherited assembler's original header still need review.
The goal remains active, with no push, main merge, publication or cleanup.

## TypeScript Review Started

The reviewed TypeScript metadata alignment is now applied; transferred semantic
IR is unchanged. Its exact evidence and pending gates are recorded in
[the source-alignment review](EMDASH_ACTION_PROFILE_TYPESCRIPT_SOURCE_ALIGNMENT.md).
A fresh canonical core export is
`emdash2/tmp/probes/api_production_core_canonical.lp`, source SHA-256
`6a980df34be718a23a6be121d170153650830a49f54b7e0eca415705ffb2068a`.
The exact source hash is authoritative in `api_production_core_export_manifest.json`;
the export hash is
`7200f0614757bccf2e309703771003511ecd239a4e99433a2890d2049c40b89d`.
The predecessor was recovered from Git `f9ae8d6a`; its source/export hashes
match the currently pinned `f7206b8e` / `594bbfa4` pair exactly.

The read-only acquisition audit finds unique unchanged canonical text for all
95 distinct commands selected by the ten contracts. The broader declaration
inventory finds 155 byte-identical ordinary declarations, three generated
constructor names (`Struct_sigma`, `zero`, `succ`), and the documented synthetic
`Obj_func__displayed_chain_mirror` alias. The complete generated-parent commands and the existing alias owner are
byte-identical and have been reviewed. The traversal includes cloned records; its raw
record count is not a distinct-profile count.

The audit also finds 107 declaration-provenance ordinal mismatches against the
already pinned predecessor, including `Prof_cat`; they are pre-existing
metadata defects, not evidence that those declaration bodies changed. Match
bindings by their actual semantic owner and full canonical text, not by blindly
relocating the erroneous old ordinal. The pins and verified command/provenance positions are now aligned by an
AST-scoped patch. All 134 loaded module records retain identical semantic IR;
all ten applied acquisition contracts, typecheck, lint and 37 focused tests
pass. The live scale-inventory gate also passes all fourteen tests without
skips. Aggregate and conformance qualification remain pending. No pin-only
success is claimed.

Audit files: `api_typescript_canonical_command_audit.json`,
`api_typescript_transfer_evidence_audit.json`, and
`api_typescript_affected_source_inventory.json` under `emdash2/tmp/probes/`.

## Native Window Diagonal View

The next semantic stop was
`emdash3_2_one_cat_native_window_snake_right_kernel_quotients.lp`, receipt
`20260927T062114Z-2e08b4fbad334ad787c7236629fdfd90`. Its reverse-triangle proof
compared two bracketings of the same Prod/diagonal/Q/H functor chain. A direct
typed-reflexivity control failed (`20260927T062732Z-6039698e2e114dbc912f37008dfaccd8`),
while the whole-functor path follows from existing category associativity and
identity-family postcomposition (`20260927T063247Z-9ce2e585d47b465daf3a8e47ded06e93`).

The new one-way owner `emdash3_2_product_diagonal_reindex_views.lp` preserves
that derived path and supplies its scoped proof-time comparison. Both forms
retain the literal diagonal and composite Q∘H argument, and every category and
factor is checked. There is no new runtime rule or functor strictness premise.
The existing product-family owner remains unchanged. The native consumer adds
one import; all its theorem bodies and selected maps remain unchanged.

Qualification:

- Full native owner: `20260927T063830Z-f9a0738a61d041a7897133cfedf06f1f`,
  19.917s at 2 GiB/90s.
- Existing right-kernels reviewer: `20260927T064116Z-903885e964a34e02b3bdb85ad092ff50`,
  21.884s at 2 GiB/90s.
- Final whole-view, unit, dependent next-Hom, different-factor, runtime and
  ambient-noncollapse controls: `20260927T064351Z-29e1e53098574bb0a81f4c0a1af9c64c`,
  5.316s at 2 GiB/90s.
- Same control without the comparison fails:
  `20260927T064306Z-e3febac9c8cf412793005a87702bc870`.
- Strict LHS audit: zero candidates.

Installation and exact source identities are in
`emdash2/tmp/probes/api_window_diagonal_installation.json`; the focused
production reviewer is `examples/product_diagonal_reindex_views.lp`.

## Book Claim Synchronization

Chapters 9, 11 and 14 now distinguish generic normal identities and retained
laxity from stable strict-profile computation. Chapter 28 describes the
current opaque lax-arrow Gray hom, its retained post/left cell and ambient
higher modifications; the obsolete pending-global-cut narrative is removed.
Chapter 27 records the completed cut retirement, and Chapter 31 separates
this integration from deferred higher duality. Chapter 20 names inherited
ordinary/displayed assembly as an assumption, retaining both inverse choices
and whole cancellation, rather than deriving it from generic strictness.

The evidence map corrects eight moved-owner references and the affected
strictness/Gray/locality claims. No book edition, publication date or release
artifact is promoted. `book:check` passes: 187 claims, 46 source files and
3,124 math spans, including evidence, assembly, source, typography, KaTeX and
paper validation. Log: `emdash2/logs/api-book-check.log`.
The bounded browser rendering check passes at 416 pages, with no console,
page, request or render errors (`emdash2/logs/api-book-render.log`). Its preview
process has stopped. Generated book Markdown is produced only by the owning
assembly tool.

Repository registry, report lifecycle/header and active-reference lints pass.
The documentation gate passes at receipt
`docs-20260927T080623Z-1ef07d1e47c24c068e18f854c33bd273`; later book/doc edits
retain an exact-diff check and receive the book checks above. The Infinity
archive is verified from the launch worktree `/home/user1/emdash1` (1,307
responses); this isolated worktree has no separate session archive.

## Document-Link Checker Repair And Checkpoint Scope

The expanded documentation check exposed a pre-existing scanner bug: inline
and display mathematics such as `D[p](u)` was treated as a local Markdown
link. `scripts/devops.py` now masks math before extracting links, as it already
does for code. Placeholders preserve real links with mathematical labels.
A regression test also retains normal links, escaped dollar prices, ordinary
prices and an unmatched-dollar case. All thirteen DevOps tests pass; the
changed-document gate passes at
`docs-20260927T081738Z-1c659629eea84d04aba8834bb663053e`.

This small Python fix and the synchronized progress/TypeScript evidence
records form a validated tooling/document checkpoint. It does not claim the
larger uncommitted mathematical, TypeScript or book tranche has completed its
integration gates. The production driver continues serially from the exact
state file above; 517/791 library targets have been traversed successfully at
this observation, with target 518 retrying its unchanged inputs after measured
allocation failures. Remaining reviewers, durable resource routing, source
header cleanup, catalog/health, final TypeScript/conformance and formal CI
still gate the semantic checkpoint.
