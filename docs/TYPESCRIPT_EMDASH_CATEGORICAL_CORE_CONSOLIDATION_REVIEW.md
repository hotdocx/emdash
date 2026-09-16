# Categorical Core And Homology Consolidation: Living Plan And Review

Date: 2026-09-16

Status: active — CC-0 published and CC-1a qualified; CC-1b next

Plan-ID: TS-EMDASH-CATEGORICAL-CORE-CONSOLIDATION

Decision record: user acceptance and launch, 2026-09-16; response 0110 in
Infinity Codex session `2026-09-12_01a096616c4a`.

Implementation branch: `goal/categorical-core-consolidation-v3.2`

Implementation worktree: `/home/user1/emdash1-categorical-core-v1`

Checkpoint/decision ledger: the execution ledger in this file; split out a
linked ledger only if the implementation history outgrows this plan.

Reviewed checkpoint: `2b1066c6e7b7489e954581f6473bb0ba75da8975`

Comparison baseline: `cbef77e76fc292453c8814b5ecc6d62e84132f01`

## Decision And Scope

The native universality/homology goal is complete under its revised scope.
Its [final audit](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md) remains
the evidence authority for that completion. The user has now accepted this
review and authorized its implementation as a new persistent goal, without
reopening the preceding goal's completed proof obligations.
Op/duality, integration of the separate action-profile branch, spectral research,
and the large six-term comparison remain deferred. The initial documentation
checkpoint has no semantic changes. Subsequent implementation follows the
bounded tranches below.

The user explicitly authorizes local green checkpoint commits, followed first
by fast-forwarding main to this documentation/completed-homology checkpoint,
pushing main to GitHub and deploying through the existing GitHub Pages workflow.
Do not create a release or publish a package. Later consolidation checkpoints
remain local unless a subsequent instruction authorizes their integration.
Use a dedicated branch/worktree from that published checkpoint; preserve the
completed native-homology branch and all deferred experiment bundles.

The main recommendation is to separate reusable categorical structure, native
homological constructions, ordinary observations, and CAS input vocabulary by
their actual dependencies. Several of these boundaries already exist. Moving
everything into the nucleus, renaming every path helper, or inventing a second
universality interface would obscure them.

There is a real remaining architectural issue: some shared input/observation
vocabulary still lives in, or imports, the former homology implementation.
Eliminating those dependency edges is a more concrete first implementation
tranche than another broad normalization experiment.

## Reusable Interface Inventory

The following groups distinguish structural declarations from derived operations.
The ten new body-free structural symbols are enumerated individually in the
[final audit](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md#declared-structural-boundary).
They are not ten derived theorems and are not assumptions asserting output
exactness. This inventory also includes supporting definitions and rule owners.

| Family and current owners | What was added or reused | Ownership recommendation |
| --- | --- | --- |
| [Whole adjunction families](../emdash2/emdash3_2_one_cat_adjunction_families.lp), [formula views](../emdash2/emdash3_2_one_cat_adjunction_family_views.lp), evaluation and reindex companions | The declared ordinary postcomposition lift F⊣G ⇒ (F∘−)⊣(G∘−), ordinary functor-category closure, whole unit/counit projections, and derived mate functors. The formula-view owner has seven proof-time unifiers. | Keep as generic ordinary adjunction extensions, upstream of K/Q. Retain existing postcomposition heads and inverse cuts. Do not describe the lift as derived from the older β interface. |
| [Diagram reconstruction](../emdash2/emdash3_2_one_cat_diagram_reconstruction.lp), [diagram transpose](../emdash2/emdash3_2_one_cat_diagram_transpose.lp), diagram-map paths/equivalences | Declared DefIso D∘E≅id with identity endpoint components; derived faithfulness, actual diagram maps and inverse data; transposition is a whole internal term. | Keep with walking-arrow/diagram structure. Do not upgrade the one-sided reconstruction to an unrestricted higher equivalence with LaxArrow(C). |
| [Terminal/initial family universality](../emdash2/emdash3_2_one_cat_terminal_family_universality.lp), [family uniqueness](../emdash2/emdash3_2_one_cat_terminal_family_paths.lp) | Two declared ordinary DefIso instances Arr(h)≅J∘F and Arr(h)≅I∘F, with sixteen endpoint/whole-projection rules; derived whole-family uniqueness. | Keep the current guarded extension. The primary higher terminality redesign below is separate work, not already implemented. |
| [Product adjunction](../emdash2/emdash3_2_one_cat_product_adjunction.lp), [whole pairing](../emdash2/emdash3_2_one_cat_product_families.lp), projection/inverse-component companions | Declared ordinary product-category closure and Δ⊣P for the existing BinaryProducts choice; derived family pairing/unpairing and their observations. | Keep under Cartesian structure, not homology. Document the structural declaration and inherited whole mate computation in Chapter 30. |
| [Biproduct adjunction](../emdash2/emdash3_2_one_cat_biproduct_adjunction.lp), [injections](../emdash2/emdash3_2_one_cat_biproduct_injections.lp), [copairing](../emdash2/emdash3_2_one_cat_copair_families.lp) | Derived whole injections, declared P⊣Δ for the same selected biproduct, derived whole copairing. Additive-family, bilinearity, negative, difference, shear and reindex modules build on these. | Keep as additive categorical structure upstream of the LES/snake. Do not duplicate pairing or create new product choices. |
| `product_family_*`, [product-composition paths](../emdash2/emdash3_2_product_composition_paths.lp), [unit views](../emdash2/emdash3_2_functor_category_unit_views.lp), [factorization views](../emdash2/emdash3_2_hom_action_factorization_views.lp), whiskering/reindex helpers | Derived projection/evaluation equations and narrowly typed proof-time presentation comparisons. Some helpers are generic despite living beside their first consumer. | Audit rule placement separately from file moves. Preserve the distinction between runtime rules and unification; do not install all these comparisons globally merely for convenience. |
| [Ordinary slice paths](../emdash2/emdash3_2_one_cat_slice_paths.lp), [discrete functor paths](../emdash2/emdash3_2_discrete_functor_paths.lp), [groupoidal object maps](../emdash2/emdash3_2_groupoidal_object_maps.lp) | Declared ordinary slice/discrete functor-category closure; derived automatic coherence and equality reflection at genuinely discrete Homs. | Keep truncation guards explicit. These constructors are not a way to recover directed higher action from arbitrary object functions. |
| [Kernel pullback comparison](../emdash2/emdash3_2_one_cat_kernel_pullback_comparison.lp), [lifts](../emdash2/emdash3_2_one_cat_kernel_pullback_lifts.lp), [universality](../emdash2/emdash3_2_one_cat_kernel_pullback_universality.lp) | Derived inverse to the actual slice-Hom comparison, using whole kernel mates. The inverse functor uses discrete-Hom coherence in the ordinary profile. No new generic pullback axiom or manual cone record was added. | Keep downstream of both the existing pullback interface and K. This is a kernel/pullback theorem, not a reason to move all homology into the generic pullback owner. |
| `omega_equiv_*`, [equivalence conjugation](../emdash2/emdash3_2_equivalence_conjugation_paths.lp), [natural equivalence transport](../emdash2/emdash3_2_one_cat_natural_equivalence_transport.lp) | Derived composition, cancellation, inverse-square/right-factor operations and transport of a component equivalence along an actual input equivalence. | Keep as reusable equivalence calculus. The last operation uses ordinary-target naturality; its name “transport” does not mean a cast of F or G along equality. |
| [Proposition-fibre constructor paths](../emdash2/emdash3_2_prop_fibre_constructor_paths.lp), [finite-family paths](../emdash2/emdash3_2_finite_family_paths.lp), fibre cancellation and [Sigma fibre inclusion](../emdash2/emdash3_2_sigma_fibre_inclusion.lp) | Derived groupoidal congruence/evidence bookkeeping and native structural inclusions. `two_prop_fibre_image_path` is already factored out of native-square proofs. The one-variable `prop_fibre_image_path` remains inside the slice owner. | Move the remaining one-variable lemma only as a small ownership cleanup with an actual reuse/dependency benefit. Keep proof irrelevance restricted to proved proposition-valued fields. |
| [Whole K/Q structures](../emdash2/emdash3_2_kernel_cokernel_adjunctions.lp), mates, transposes, zero-column and normality modules | Primary J⊣K and Q⊣I packages; derived structural arrows, whole universal operations, Coim⇒Im and ordinary record views. | These are homological/additive owners, not generic adjunction axioms. Ordinary views must remain downstream and retain the same selected data. |

The nucleus also gained two whole-transformation exchange cancellation rules;
the final audit records their exact boundary. They belong to generic exchange,
not to a homology-specific normalization package. The original hom_int/homd_int
owners remain foundational.

Existing reviewer entry points include `one_cat_adjunction_families.lp`,
`one_cat_product_families.lp`, `one_cat_terminal_family_universality.lp`,
`one_cat_diagram_reconstruction.lp` and `one_cat_kernel_pullback_universality.lp`
under `emdash2/examples/`. Their existing checked evidence should be reused;
this documentation review did not rerun their semantic checks.

## Terminality: Implemented Extension And Proposed Primary Interface

The current [TerminalObject](../emdash2/emdash3_2_terminal_objects.lp) already
has a whole canonical transformation !:id_C⇒const_t and a computing terminal
cut. Its additional `terminal_hom_contr` field has type IsContr(Hom C x t),
where the contracted groupoid is Obj(Hom_cat(C,x,t)). The homology goal added
whole ordinary-family comparisons to this interface; it did not replace it
by general categorical terminality.

A coherent categorical formulation should control the entire varying Hom
family. The intended mathematical target is the appropriate internal
adjunction !:C→1 ⊣ t:1→C, with the dual adjunction for initiality, or its
whole represented-Hom comparison. The selected ! and its action should remain
computational projections, with ordinary uniqueness derived when applicable.

For an individual Hom category D, equivalence D≃1 is the relevant categorical
contraction. `OmegaEquivAlong Cat_cat D Terminal_cat (Terminal_func D)` is a
candidate expression using an existing interface, not a new implemented
definition. A family of separately chosen witnesses is insufficient as the
primary varying-endpoint owner: its whole action must be specified. Also,
today's OmegaEquivAlong has equality-valued inverse laws; its adequacy for the
intended higher comparison and functor-category profile must be reviewed.

Object/core contractibility alone does not control noninvertible arrows.
Even a category with a single object can have nontrivial endomorphisms.
Object-univalence relates paths to equivalences; it does not turn every
directed cell into an invertible one. Consequently neither deleting OneCat(C)
from the current DefIso declarations nor wrapping the old pointwise field in
a new name is the proposed redesign.

First specify the native owner, its whole Hom comparison, inverse/coherence
data and observable cuts. Then derive the ordinary family normalizers and
record views from it where justified. Do not require users to supply separate
naturality squares. Do not treat this review as a completed general
ω-categorical semantics or as authorization to reopen Op/profile migration.

## Paths: What Remains And What Needs Work

The criterion is what a path is used to compute, not whether `=` appears.

1. **Categorical presentation changes.** The current
   [H point comparison](../emdash2/emdash3_2_homology_family_point_comparisons.lp)
   applies Q to an actual boundary-diagram map with retained inverse data.
   The introduced-input and native-pair comparisons likewise use actual
   maps. This removes the identified operational H cast. Their earlier
   equality observations remain available as observations. Where parameters
   vary, a future public comparison should be a whole transformation; the
   checked point/column interface does not by itself establish that upgrade.
2. **Ordinary equations as internal cells.** Native raw-input, diagram-map and
   kernel/cokernel-family constructors still use `path_to_hom` on a proved
   arrow equation. The endpoints and underlying maps remain fixed. This is
   appropriate at the ordinary/truncated input boundary, where a matrix
   equation supplies an internal cell. It is not a cast selecting a new
   functor. The primary whole operations do not ask their callers to assemble
   a family of naturality-square proofs.
3. **Inverse and reconstruction laws.** Mate formula agreement, cancellation
   and equivalence laws remain equations between the original arrows or
   transformations. Keep them. “Use categorical universality” does not mean
   removing the laws that express an adjunction or an inverse.
4. **Finite CAS observation matching.**
   [Freyd diagram observations](../emdash2/emdash3_2_commutative_algebra_freyd_diagram_observations.lp)
   use `ind_eq` to move proposition-valued endpoint-matching evidence and to
   establish equality of finite observations. This is a derived display
   interface, not the definition of H or δ. The
   [observed exactness transporter](../emdash2/emdash3_2_one_cat_native_observed_exactness.lp)
   retains `sigma_Fst E` literally and only extends its observation path:
   canonical Ω evidence and its inverse data are not transported by induction.
5. **Discrete/groupoidal assembly.** Slice congruence and discrete functor
   constructors use paths under explicit truncation hypotheses. They are
   valid ordinary-profile techniques. Generalizing these owners to directed
   higher categories would require actual higher action; deleting the guards
   would not provide it.

Thus the review identifies further consolidation and a whole-parameter
comparison design opportunity, but no evidence that every remaining path use
must be replaced or that categorical terminality would cure the six-term
allocation failure. That deferred check compares retained package expressions;
its cause must not be inferred from this general design preference.

Review method: a textual import-graph scan of the root library at the reviewed
checkpoint used `commutative_algebra_freyd_native_les_certificate_views`,
`commutative_algebra_freyd_native_snake_exactness` and
`one_cat_native_snake_six_term_result` as roots (all with the `emdash3_2_`
prefix). Their union has 382 modules. Of the 272 changed root owners in that
closure, 20 contain `@ind_eq`, `@path_to_hom` or `@eq_transport`, including the
inherited nucleus. These are discovery counts, not counts of defects or of new
transport sites. Inspected owners are classified above. This is not an
exhaustive semantic audit of every inherited equality eliminator.

## Concrete Dependency Cleanup Before Retirement

The native route no longer requires an old `FreydHomologyModel` or a
KernelPresentation/CokernelPresentation argument. However, mathematical API
independence is not yet complete source-import independence. In particular:

| Current dependency | Why it remains | Proposed extraction |
| --- | --- | --- |
| `freyd_chain_pair_data` → `freyd_homology` → `freyd_selected_homology` | `CommRingFreydChainPair`, the raw zero-composite agreement, is declared beside the former homology operations. | Move the unchanged raw chain-pair classifier to a presentation-input owner. Both implementations may consume it during removal. |
| `freyd_chain_map_data` → `freyd_functorial_homology` | Raw chain-map agreement vocabulary and its projections live with the former induced-H construction. | Extract unchanged raw chain-map data, with no selected-H dependency. |
| `homology_adjunction_record_data` → `computational_homology` → `kernels_cokernels` | Native semantic boundary observations share an owner with ordinary pair/record views. | Separate native boundary observations, generic raw pair data and optional record views. Keep the whole native comparison route independent of record-only imports where possible. |
| `one_cat_slice_paths` contains both ordinary slice closure and a generic proposition-fibre lemma | These were introduced for one pullback consumer. | Consider a small split along existing generic congruence/truncation owners; do not create a new omnibus module. |

Names in this table abbreviate the corresponding `emdash3_2_*.lp` files.
These edges describe the reviewed baseline. CC-1a below now removes the
first two; the boundary/record separation remains CC-1b. Their former presence
did not imply that the old operations were executed or that the native model
contracts required the old model.

The older `kernel_adjunction_presentations`, `cokernel_adjunction_presentations`,
`homology_families`, `zero_arrow_cone_homology`, `homology_record_connecting`,
`freyd_homology_models` and `freyd_adjunction_model_adapter` are outside those
three selected native import closures. They still have other library,
TypeScript or reviewer consumers. The older `homology_bounded_generator` also
remains a separate ordinary-interface reference; book 0.9.0-dev explicitly
labels it. No old/new comparison obligation is reinstated by this inventory.

Before removing a family, inspect symbol users as well as direct imports,
formal signature mirrors, public exports, tests, Makefile/catalog registration,
book evidence and documentation links. A textual absence from these three
closures is useful evidence, not a complete deletion proof.

## What “Retire” Should Mean

| State | Repository action |
| --- | --- |
| Current whole construction | Keep in the active library and current reading route. |
| Useful derived ordinary view or shared CAS input data | Keep at a clearly named downstream observation/input boundary. Records are not automatically legacy algorithms. |
| Superseded implementation with no retained consumer | Delete its active source, exports, checks and registrations in one checked tranche. Git history preserves the implementation; do not leave dead copies in active owners. |
| Former implementation with a still-useful consumer | Migrate that consumer or explicitly retain it as a limited reference first. Do not claim retirement is complete while the active graph still depends on it. |
| Unfinished experiment worth resuming | Preserve a small tracked audit bundle with exact source identity, replay instructions and outcome, outside the positive library/check graph. Existing Op and six-term bundles are examples. |
| Disposable generated logs/probes | Keep ignored if useful locally; never make untracked files the only archive of a decision or required result. |

There is no benefit in maintaining a parallel archive of every deleted source
file. A concise retirement note with replacement owner and commit is enough
when Git contains the old implementation. Mandatory SOP text should route to
current decisions; chronological probes belong in dated ledgers. Temporary
disable-and-comment guidance is distinct from deliberate final retirement.

## Documentation And Book Disposition

This review updates the root and emdash2 READMEs to the native final audit,
documents both displayed certificates and current contracts, updates both
versions of the local `tmp/EMAIL.md` appendix, adds reviewer/owner routing, and
replaces the duplicated native-goal chronology and older homology owner
narrative in AGENTS.md with current scope, a compact owner map and recovery
links. The email draft is not sent or published.

Book 0.9.0-dev already explains primary whole K/Q/H, direct δ, categorical
presentation comparisons, native snake/LES certificates and the ordinary
structural declarations in Chapters 12 and 31. It need not be regenerated for
entry-point maintenance. A subsequent substantive consolidation should place
general adjunction-family lifting with Chapter 12 and product/terminal
structural material with Chapter 30, leaving the homological application in
Chapter 31. Mark general categorical terminality as a proposal until its owner
and consumers qualify. Update source prose/evidence first, then regenerate
book artifacts through their tools.

The current-status report, Foundations and report index still contain long
historical milestone prose. Their current routing is clarified here; a full
history extraction should preserve owner links and decisions while leaving a
short current mathematical account. It is separate from moving formal rules.

## Accepted Implementation Order

1. Extract the unchanged shared raw pair/map vocabulary and separate native
   boundary data from optional record views. Prove the new import direction
   with dependency and symbol inventories. This is a file-ownership tranche,
   without mathematical redesign or new rewrite rules.
2. Decide and execute retirement of superseded model/presentation/connecting
   wrappers and their dependent legacy reviewers. Preserve useful CAS
   algorithms and any explicitly retained ordinary iterator. Compatibility
   with the retired formulation is not a new acceptance condition.
3. Review the primary categorical terminal/initial and structural adjunction
   interfaces as one bounded design task. Preserve hom_int/homd_int, whole
   action, selected inverses and existing computational owners. Implement
   only the portion justified independently of deferred profile/duality work.
4. Where an actual consumer needs it, upgrade remaining point presentation
   comparisons to whole transformations. Keep ordinary display equations
   downstream. Revisit source/exposition placement and the book together.
5. Reassess whether these changes provide a concrete hypothesis for the
   deferred six-term comparison. Do not resume it automatically or promise a
   performance fix. Op/duality still has its own later scope.

For documentation only, use exact diff and local-link/Markdown hygiene.
For source moves, run localized owner/consumer checks and warning comparisons,
refresh affected catalog/health evidence under the SOP, and inspect signature
mirrors. TypeScript changes use affected dependency compilation and focused
tests. Avoid long repository-wide typechecks. Retain the documented compiled-
parent and resource/GC workflow; it is independent of the mathematical choice
between equations and categorical maps.

Documentation validation: `git diff --check`, introduced local-link/anchor
checks, Markdown fence/encoding checks and compact-map owner existence pass.
The mandatory workflow from “Starting A v3.2 Task” onward in AGENTS.md is
unchanged. No Lambdapi/TypeScript source, signature mirror, book chapter or
generated book artifact changes in this review. Existing semantic and book
validation from the completed audit is carried forward; no repository-wide
typecheck or renewed normalization probe was run.

## Execution Ledger And Completion Gates

| Tranche | Required result | State |
| --- | --- | --- |
| CC-0 | Checkpoint the accepted review and documentation; fast-forward main, push and verify the existing Pages deployment. Record the exact commit/run. Bootstrap an isolated continuation worktree. | Complete |
| CC-1a | Extract unchanged raw chain-pair/map vocabulary into shared input owners. Native raw adapters cease importing former homology algorithms merely for those classifiers/projections. Record declaration identity, import closures, focused checks and warnings. | Qualified |
| CC-1b | Separate native boundary observations from optional ordinary record views; factor remaining generic support only where an actual ownership/dependency benefit is established. Preserve original whole operations and data. | Pending CC-1a |
| CC-2 | Inventory remaining legacy consumers and retire superseded wrapper families in bounded groups. Delete unused source/exports/check registrations; preserve shared CAS algorithms and explicitly retained ordinary references. No old/new compatibility proof requirement. | Pending dependency separation |
| CC-3 | Review the primary whole terminal/initial and structural-adjunction interfaces, specify native owners/action/inverses/cuts, and implement the independently justified portion. Retain explicit qualifications for anything needing deferred profiles/duality; do not merely delete guards. | Pending ownership cleanup |
| CC-4 | Inventory actual consumers of point presentation comparisons; construct needed whole transformations with their endpoint/Hom observations. Record a reason for each retained point-only view. Ordinary equations remain downstream. | Pending CC-1 and relevant CC-3 decisions |
| CC-5 | Consolidate current status/Foundations routing and expose reusable mathematics at the proper book chapters. Update book source/evidence and regenerate artifacts only when substantive book content changes. | Pending implementation decisions |
| CC-6 | Final source/API/trust audit, focused regression and documentation gates; reassess whether a concrete six-term hypothesis emerged, without resuming that deferred experiment. Preserve an exact later-work list. | Pending |

For each implementation slice, record the hypothesis, actual affected owners,
baseline, validation command/resource profile, warning comparison and outcome
before a green checkpoint. Code moves preserve symbol bodies/signatures unless
an explicitly reviewed later design slice says otherwise. Shorten import
closures without moving rewrite rules indiscriminately or changing implicit
normalization environments without checking consumers.

Completion requires qualified outcomes for all scoped rows, with any smaller
unimplemented portion explicitly justified by a concrete prerequisite or user
deferral. Documentation alone does not count as completing an implementation
row. General higher terminality must not be claimed implemented merely because
an ordinary adapter passes. The complete native nonsplit LES/snake capability,
selected CAS data, explicit contracts and retained inverse computations must
survive the affected changes.

Persistent goal launch objective: execute this evolving plan in the dedicated
consolidation worktree, under the repository authority/SOP order. Delegate
specifics, decisions, scope refinements, validation and completion to this file
and any explicitly linked ledger. Work autonomously in bounded green tranches
with local checkpoint commits. Preserve hom_int/homd_int, categorical whole
action, selected computational data and proof–CAS behavior. Respect the listed
deferrals and localized-check policy. The initial main push/Pages deployment
is authorized; future integration/release/history rewriting/cleanup is not
implicitly authorized by the persistent goal.

2026-09-16 startup: recovered the accepted uncommitted documentation tranche
on `goal/native-universality-homology-v3.2`; main is clean at cbef77e7 and is
an ancestor. Fetch reports origin/main has no independent commits. The Pages
workflow builds the existing reviewer and deploys on relevant main changes;
no package release is triggered. The existing semantic/book audit is reused
for unchanged code. Infinity Codex recovery verifies 1210 responses at the
session's main-worktree archive; isolated worktrees have no separate archive.


CC-0 completed (2026-09-16): documentation checkpoint `df9b4778` includes
this accepted living plan. Main fast-forwarded cleanly and origin/main now
contains that exact commit. [Pages run 35131972244](https://github.com/hotdocx/emdash/actions/runs/35131972244)
completed successfully for it (build and deployment). The separate
`goal/categorical-core-consolidation-v3.2` worktree was created from that
checkpoint and bootstrapped with the pinned pnpm wrapper; workspace contract
passes. The persistent goal is active and delegates its details to this plan.

CC-1a hypothesis: the existing raw `CommRingFreydChainPair`,
`CommRingFreydHomologyChainMap`, and its upper/lower projections can move
unchanged into `emdash3_2_commutative_algebra_presentation_chain_inputs.lp`,
importing only raw presentation composition/zero operations. Requiring that
owner directly from the shared pair/map adapters should remove their imports
of the former Freyd homology algorithms. Preserve all four declaration texts
and unqualified API names; module ownership changes explicitly, and qualified
old-owner references were searched for (none found). No rule, classifier
meaning, CAS choice or inverse data changes in this slice.

Baseline: warning-enabled `freyd_native_maps.lp` and
`commutative_ring_freyd_functorial_homology.lp` reviewers pass at
90s/2048MiB with `OCAMLRUNPARAM=o=20`, under the serial resource guard.
Post-change checks will include the new owner, both raw adapters, native
input/map consumers and retained former-owner reviewers. Compare full warning
inventories, declaration bodies/signatures, imports and signature mirrors;
refresh source health/catalog metadata proportionally. This is an owner move,
not new mathematical behavior requiring another handcrafted theorem test.


CC-0 deployment verification: the public homepage responds successfully.
The actual Vite-emitted [book asset](https://hotdocx.github.io/emdash/assets/emdash-book-DRPtWe8T.pdf)
has SHA-256 `3064cdf8bffc6ba5eb2b63815e96903d4bc0b2c10f52efa76eb71c2278f48c7e`,
byte-identical to the qualified local 0.9.0-dev PDF. The asset is fingerprinted;
there is no unversioned `/emdash/emdash-book.pdf` route.

CC-1a qualified (2026-09-16): the new
[raw presentation input owner](../emdash2/emdash3_2_commutative_algebra_presentation_chain_inputs.lp)
contains the four unchanged declarations. Both shared adapters import it
directly; the former owners import it for their retained consumers. There
are no new primitives, rewrites, unifiers, opaque bodies or changed signature
mirrors. The preserved declaration-block SHA-256 values are
`7deb31680afe0d0dfb988769ec51addbdb0859a4c160986eeaaf601ae01113c0`
(pair) and `90a947c6ee8fea41cf06b2e7a6ecdd46ed31531d1b100800d26e1ed7ed18f14e`
(map/projections). Each declaration occurs exactly once in the root library.

Textual root-module import closures, including each root:

| Consumer | Before | After |
| --- | ---: | ---: |
| Shared raw pair adapter | 74 | 40 |
| Shared raw map adapter | 79 | 44 |
| Native raw input | 91 | 67 |
| Native raw map | 119 | 94 |
| Native LES certificate views | 351 | 330 |

The former Freyd homology/induced-homology algorithms are absent from these
new closures. This does not claim removal of every ordinary record owner;
that remaining direction is CC-1b.

Validation: nine focused warning-enabled LP checks pass (new owner, both
adapters, native input/map, whole H map, native model-arrow observer and the
two retained former-owner reviewers). The six reviewers contain 25 existing
assertions. The seven serial measured checks take 8.53–15.95s each, within
90s/2048MiB with `OCAMLRUNPARAM=o=20`; no subject-reduction bypass or broader
typecheck was used. Native-map before/after inventories match exactly at
1460 warnings/1291 critical-pair heads and families; the retained induced-map
reviewer matches at 1421/1252. Locations and parser inventories also match,
with zero parser issues. Counts alone are not the comparison criterion.

Source-health registration now includes the new owner; its 1412-file source
snapshot is `772fdb432793456cd74ab4f40fc7350db015f5a36b022ed17c1bf51ad92c5b0e`.
The no-check metadata refresh is explicit, not a claim of 1412 fresh checks.
Catalog and TOC checks pass; all 178 book evidence claims still resolve.
The TS mirrors retain the same names/telescopes; there is no TS source change.
Exact local receipts are `emdash2/tmp/probes/cc1a_checks.json`,
`cc1a_baseline.json` and `cc1a_warning_comparison.json`; the published baseline,
unchanged blocks and target names above suffice to reconstruct the check.

Next: CC-1b should separate the five raw generic chain-pair declarations from
`computational_homology` and move the native semantic-boundary observations
out of the mixed record owner, preserving their declaration bodies and
checking the actual native consumers. Do not combine that move with a
terminality rewrite or legacy API deletion.
