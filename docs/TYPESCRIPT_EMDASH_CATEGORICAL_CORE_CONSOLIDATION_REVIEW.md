# Categorical Core And Homology Consolidation: Living Plan And Review

Date: 2026-09-16

Status: active — CC-3a checkpoint 5c575800; CC-4 comparison-consumer review in progress

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
contraction. [CatContraction](../emdash2/emdash3_2_categorical_contractions.lp)
now transparently specializes `OmegaEquivAlong Cat_cat D Terminal_cat
(Terminal_func D)`. The companion CatdContraction specializes the same
interface at the whole canonical family map `Terminal_funcd`; its selected
inverse is one whole Functord. Object/core contractibility is derived from
that data, not conversely. These definitions retain today's equality-valued
whole inverse laws; they are not a proof that an arbitrary higher terminality
notion has this presentation. A product of separately chosen fibre witnesses
does not supply the whole family contract.

Object/core contractibility alone does not control noninvertible arrows.
Even a category with a single object can have nontrivial endomorphisms.
Object-univalence relates paths to equivalences; it does not turn every
directed cell into an invertible one. Consequently neither deleting OneCat(C)
from the current DefIso declarations nor wrapping the old pointwise field in
a new name is the proposed redesign.

The independently implemented ordinary portion is
[terminal/initial adjunction presentations](../emdash2/emdash3_2_one_cat_terminal_adjunctions.lp):
!:C→1 ⊣ t:1→C and t:1→C ⊣ !:C→1, guarded by OneCat(C). These are two
explicit structural primitives, not derivations from the old β rules. Their
whole units/counits and represented-Hom comparisons belong to the existing
Adjunction interface. Derived Hom DefIso/Ω observations keep the actual mate
and inverse; they do not cast its forward map to Terminal_func. Existing
ordinary family normalizers compare the unit/counit diagram families with
the original selected terminal/initial families. Those normalizers remain
structural declarations, not retroactively derived theorems.

A primary general terminality upgrade must still specify its native owner,
whole Hom comparison, inverse/coherence data and observable cuts, then derive
ordinary normalizers where justified. In particular current Adjunction owns
a computational DefIso comparison, which is stronger than merely supplying
higher equivalence data. Do not require users to supply separate
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
These edges describe the reviewed baseline. CC-1a below removes the first
two; CC-1b separates the third. Their former presence
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
| CC-1b | Separate native boundary observations from optional ordinary record views; factor remaining generic support only where an actual ownership/dependency benefit is established. Preserve original whole operations and data. | Qualified |
| CC-2 | Inventory remaining legacy consumers and retire superseded wrapper families in bounded groups. Delete unused source/exports/check registrations; preserve shared CAS algorithms and explicitly retained ordinary references. No old/new compatibility proof requirement. | Qualified with explicit retained references |
| CC-3 | Review the primary whole terminal/initial and structural-adjunction interfaces, specify native owners/action/inverses/cuts, and implement the independently justified portion. Retain explicit qualifications for anything needing deferred profiles/duality; do not merely delete guards. | Qualified independent portion; general higher replacement has recorded prerequisites |
| CC-4 | Inventory actual consumers of point presentation comparisons; construct needed whole transformations with their endpoint/Hom observations. Record a reason for each retained point-only view. Ordinary equations remain downstream. | In progress |
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


CC-1a checkpoint: `3778c1c9` (local consolidation branch; main remains the
published `df9b4778`). Worktree clean at that checkpoint.

CC-1b hypothesis: move five unchanged generic raw pair declarations to
`emdash3_2_chain_pair_data.lp` (preadditive dependency only). Move the two
native semantic-boundary observations and raw pair observation to
`emdash3_2_homology_adjunction_input_data.lp`, using the already independent
zero-arrow diagram observations and original adjunction observations.
The old mixed owner will retain only its optional factor-space view and
import the native data one-way. Switch direct raw/diagram/map consumers and
native H point comparisons to the appropriate shared owners. Retain the
ordinary annihilator view and record algorithms in their existing downstream
owners for now. All eight moved declarations keep their bodies and names.
No rule or semantic redesign is included.

Baseline controls will be the actual H point-comparison and ordinary H-record
reviewers at 90s/2048MiB/o20. Existing CC-1a native maps are an additional
control. Rejection conditions: changed declaration bodies, missing original
input/inverse/record observations, new unexplained diagnostics, or importing
optional record algorithms back into a supposedly independent shared owner.


CC-1b diagnostic review: all twelve initial focused checks pass. Removing
unused modules changes import order: H point comparison loses 28 inherited
truncation-reflector overlaps; native raw maps expose two additional existing
Kᵢᵃ/id overlaps at NType_cat, with other overlap locations redistributed.
The ordinary H-record inventory is identical. No implicated rule owner changed.
Before qualification, run the existing product and terminal assertions in two
otherwise identical native-map contexts, loading the unchanged product and
Freyd-preadditive modules in opposite orders. This tests the load-order
explanation and relevant computation without changing any rule or resuming
deferred variance/profile work. Do not report these warning inventories as
identical merely because all consumers typecheck.


CC-1b qualified (2026-09-16): the five raw pair declarations now live in
[chain-pair data](../emdash2/emdash3_2_chain_pair_data.lp); three native boundary
and input observations live in
[adjunction input data](../emdash2/emdash3_2_homology_adjunction_input_data.lp).
The former mixed owner retains only its unchanged factor-space observation.
Two optional ordinary record consumers now state their record dependency
explicitly. No new primitive, rule, opaque term or assumption is introduced.
The eight moved declarations and the retained factor declaration are each
unique and byte-identical through their declaration-ending semicolon.
Original block hashes: raw pair
`bbbbf16ac04fdd6f0e86eaa45edb7ccaf36db2975b04b63bc8d361c5addbd67a`,
native data `991c9f94f5da8e0a770a8a23c464a5ebb293d3781ad19603e7df37632e8cafa9`,
retained factor `b2fa7af327b6dfa65149be7029107078a7514e7561eea42fbbfac7d13bfb8e66`.

Import closures no longer contain `computational_homology` or
`homology_adjunction_record_data` for either native LES certificate views or
native snake exactness. Their total sizes are unchanged at 330 and 220
respectively because the smaller owners replace mixed owners. Generic
chain-pair maps shrink 13→6 modules, native raw maps 94→92, and the H point
comparison 55→51. Ordinary record consumers remain explicitly downstream;
CC-2 must separate still-useful HomologyRecord views before retiring their
former selected-homology owner. Moving that record vocabulary is not a new
compatibility-proof requirement.

Validation: twelve initial focused LP checks pass, including both new owners
and ten existing reviewers (50 assertions). The eleven measured checks take
4.06–8.97s, with the unchanged 90s/2048MiB/o20 profile. Book evidence (178
claims), catalog, TOC, declaration identity and source metadata checks pass.
The 1414-file no-check source snapshot is
`f892b19893b5a341379737df3c90711b8efd7afae4db3703a934492ff951878e`.

Warning disposition is explicit rather than an equality claim:

- H point comparison drops exactly 28 `comp_fapp0` overlaps at
  `truncation_reflector.lp:41`; that module is no longer in its closure.
- Ordinary H-record warnings match all five inventory fields exactly
  (1459 warnings, 1290 critical-pair heads/families, no parser issues).
- Native raw maps change 1460→1462 warnings and 1291→1293 critical pairs.
  The two added families are K₁ᵃ/id and K₂ᵃ/id at NType_cat; unchanged
  product/terminal/truncation rules also report some overlaps at different
  owning positions. No source rule changes.
- Initial opposite-order controls reproduce the categories/heads/families;
  explicitly placing the terminal import as in each actual dependency graph
  reproduces **all five inventory fields, including locations, exactly**.
  Baseline order: products, terminal, Freyd preadditive, native maps. New
  order: Freyd preadditive, terminal, products, native maps. Append the
  existing `triangular_binary_products.lp` and `terminal_objects.lp` reviewer
  bodies in both contexts. Both exact controls pass all 18 assertions at
  6.88s and 7.00s. The implicated rule owners are byte-identical to 3778c1c9.

These controls explain the diagnostic delta and qualify the affected typed
computations. They do not establish global confluence or repair the inherited
profile/duality system. No unnecessary import was restored merely to suppress
warnings, and none of the deferred experiments was resumed. Local receipts
are `cc1b_checks.json`, `cc1b_baseline_checks.json`, `cc1b_warning_comparison.json`,
`cc1b_order_controls.json`, `cc1b_exact_order_controls.json` and
`cc1b_exact_order_warning_comparison.json` under `emdash2/tmp/probes/`.

Next dependency-ready work is CC-2: construct the actual legacy-consumer and
registration inventory, extract useful ordinary record vocabulary as needed,
and remove superseded wrapper groups only when their retained consumers have
been handled. The secondary generic proposition-fibre helper split has no
additional consumer benefit established here and is not required for CC-1b.


CC-1b checkpoint: `d35cc98e`; CC-2 begins from a clean descendant of the
published baseline. The previous goal turn made implementation progress.

CC-2 inventory (2026-09-16): protected native roots have a 361-module union;
the separately retained ordinary iterator has 147 modules, 99 outside that
native union. KernelPresentation/CokernelPresentation, legacy H-family,
record-connecting and computational-homology owners still serve that explicit
reference. The former Freyd model has ten downstream root owners, none in
either protected closure. The old `abelian_snake_lemma` has 106 downstream
owners, likewise outside both. Registration and non-LP consumer checks are
still required before removing those larger groups.

CC-2a decision: retire only the closed leaf
`emdash3_2_commutative_algebra_freyd_retained_column_homology_comparisons.lp`
and `examples/freyd_retained_column_comparisons.lp`. All four comparison
symbols have no other root-library, reviewer, src or tests users. They belong
to the withdrawn old-model/new-native compatibility route, not the current
native LES/CAS comparison or the new snake–LES comparison.

The initial wider two-owner proposal failed the symbol-consumer gate before
any edit: `freyd_homology_model_native_connecting` still uses the old-model
input comparison, and the legacy TS emission tests import that owner. Keep
that required dependency until the whole legacy model workflow is retired.
This is sequencing, not a decision to retain it as a permanent compatibility
API. Remove the closed leaf's health registration; redirect dated source links
to the exact published df9b4778 snapshot rather than leaving dead links or
copying obsolete source into an untracked archive. Validate import/symbol
closure, the surviving native column consumer and current book evidence.


CC-2a qualified (2026-09-16): removed the obsolete retained-column comparison
owner (four definitions) and its dedicated reviewer. The old-model input
comparison remains for the still-active legacy connecting workflow. All 460
modules in the protected native/reference union are byte-identical to
`d35cc98e`, no remaining library/reviewer import dangles, and the surviving
`freyd_native_column_comparisons.lp` reviewer passes at 90s/2048MiB/o20.
The three dated source links now point to the exact published df9b4778 source.
Catalog and all 178 book evidence claims pass; source-health registration is
updated (1412 files; no aggregate LP rerun), snapshot `ca5d9fbe24ea8a4bda43552c48eefd1019f45586db0a280d3cae3a608b1f6996`.
No TS source or current native comparison was removed.

CC-2b inventory result: the old snake's 106-owner downstream closure contains
324 declared symbols and has 37 reviewer consumers. A lexical symbol audit
finds no TS source/test consumer. None of its owners intersects the protected
native or ordinary-iterator closures. Six dedicated shell gates and the
shared check/examples/metrics registries refer to this old route. Before
retirement, verify the shared-gate dispatch blocks, all remaining formal symbol
users and book/report links; delete the closed obsolete route and its own
reviewers/gates without touching the new native snake or snake–LES comparison.
The exact local inventory is `emdash2/tmp/probes/cc2_inventory.json`.


CC-2a checkpoint: `5829e76c` (local). CC-2b retirement is now authorized by
the accepted plan's consumer gate: all 324 symbols in the 106-owner old-snake
closure have no remaining root-library or TS source/test consumer outside
that closure; its 37 reviewers are specific to that route. Current native and
retained-reference closures and all 178 book evidence entries are disjoint.

The check-script audit adds one thin alias (`check_abelian_snake_inner_zero.sh`)
to the six directly referenced old gates. Three gates have useful dispatch
coverage independent of the old snake: ordinary exactness support, row
comparisons and cycle factors. Preserve their surviving owners/reviewers in
renamed gates, with the same fresh-parent compilation strategy and the current
per-process resource guard. Remove retired targets and dispatch flags from
check.sh/check_examples.sh/check_metrics.py; leave the other generic helper
owners registered. The remaining old-only gates/alias can be deleted. This is
check-coverage maintenance, not deletion of shared mathematical lemmas.

Validation for this tranche: protected closure source hashes unchanged; zero
dangling LP imports or live uses of retired symbols; surviving registration
coverage and shell/Python syntax; focused real checks of retained ordinary
support plus existing native snake/LES consumers, using the documented
resource profiles where applicable; catalog, source-health and book evidence.
Redirect dated Markdown source/gate links to published df9b4778. Do not copy
the entire retired theory to another active or untracked source directory.
No rewrite rule or native mathematical construction is to change.


CC-2b qualified (2026-09-16): retired the entire obsolete snake/snake-derived
connecting closure: 106 root owners, 324 declarations, and 37 dedicated
reviewers. No current native snake, native snake–LES comparison or ordinary
iterator owner was removed. All 460 modules in the protected union remain
byte-identical to d35cc98e. Root and nested-example imports have no dangling
references; no surviving formal or TS source/test uses a retired symbol.

Preserved generic coverage in three renamed/trimmed gates:
`check_ordinary_exactness_support.sh`, `check_ordinary_row_comparisons.sh`,
and `check_ordinary_cycle_factors.sh`. They retain fresh compiled parents and
now use the serial resource guard for every LP invocation. The four old-only
gates/alias are removed. Shared source/example/health dispatch tables and
explicit default-list appends no longer reference the retired route. A logic-
only before/after dispatcher audit preserves 692 explicit-source events,
515 reviewer events and the 530-event default-source multiset after excluding
retired targets and normalizing the three gate names. No mathematical checker
is invoked by that dispatch audit.

Real validation: the ordinary exactness, row and cycle gates pass in 80.10s,
11.43s and 24.37s total, with every individual LP check guarded at 90s/2048MiB
and `OCAMLRUNPARAM=o=20`. Current native six-term map and displayed LES
certificate reviewers pass in 11.15s and 12.54s under the same profile.
Shell/Python syntax, live registration targets, catalog and all 178 book
claims pass. The source-health refresh explicitly skips an aggregate check;
1269 files remain, snapshot
`284be39df40abc241a31863d803d645e4bc0b40bc373d48527bcda7fdf7d38af`.

The first registration audit caught default-list `files+=` entries in addition
to the initial array; all 106 retired appended entries were then removed and
the default dispatch was checked separately. An import scanner was also
corrected to recognize `emdash.examples.*` namespaces rather than treating
“examples” as a root module. Both stronger audits pass. These corrections are
validation-tool findings, not changes to mathematical declarations.

Git preserves the removed source at the published df9b4778 snapshot. The
single dated Markdown source link in the native snake plan now points to that
snapshot. Generated book artifacts and TS sources are unchanged. Exact local
receipts: `cc2b_gate_checks.json`, `cc2b_native_checks.json`,
`cc2b_dispatch_audit.json`, `cc2b_default_dispatch_audit.json` and the updated
`cc2_inventory.json` under `emdash2/tmp/probes/`.

Next CC-2 work: retire the remaining legacy model workflow together with its
TS consumers, extracting shared helpers where needed; separate useful ordinary
HomologyRecord observations from the former selected-homology implementation.
The retained ordinary iterator still explains the remaining selected-
presentation/record-connecting dependency and remains explicitly scoped.
CC-3–CC-6 are not complete. Op/profile integration and all deferred comparison
experiments remain untouched.


CC-2b checkpoint: `af24ef60`; current continuation starts clean. The previous
turn made checked retirement progress. CC-2c now addresses the coupled legacy
model/TS workflow, not the retained native CAS algorithms.

CC-2c1 prerequisite: separate raw matrix/chain-map signature builders and
raw window-telescope helpers from legacy model signature modules. The native
signature factory currently constructs a legacy environment and copies four
raw declarations from it. Replace that dependency with shared raw builders;
move the generic window template without changing its declarations or emitted
calls. Also isolate the legacy bounded-model environment factory from the
shared selected-result inventory. Native point/map/δ/LES signature telescopes,
input plicity, contracts and selected-result inventory must remain identical.
These are TypeScript ownership changes, not new mathematical owners or an
old/new comparison requirement. The production legacy facades are still
scheduled for actual removal after these shared dependencies are separated.

Validation: workspace check; scoped dependency compilation/lint; canonical
before/after signature inventories for native observation/δ/exactness/LES
factories; focused signature and existing native consumer tests; emitted LP
conformance where affected. Preserve the user prohibition on long repository-
wide typechecks; no generic checker, runtime or workspace setup is redesigned.


CC-2c1 validation update: scoped dependency compilation and affected-file lint
pass. Six complete signature inventories (512 entries across native and
remaining legacy environments) match canonical type/body/mode hashes exactly.
Native context (9 tests, 85.40s) and native map (4 tests, 46.90s) suites pass.
The full native connecting suite reaches the 90s runtime limit (exit 137 at
90.06s, before a completed test report). Review authorizes a 180s retry of this
specific existing suite, preserving the 2GiB OS bound and 512MiB worker heap.
This is a workflow-time qualification attempt, not a renewed deferred proof
normalization experiment or a declaration that the timeout proves a defect.


CC-2c1 qualified (2026-09-16): raw chain-map/arrow signatures now have the
shared `algebra_formal_freyd_raw_map_signatures.ts` owner; window telescopes
and generic observation construction live in
`algebra_formal_freyd_window_signatures.ts`. Native observation, connecting,
exactness, diagram and LES factories use these directly. Their transitive
signature-module closures no longer contain the three legacy model-signature
modules. Previously those old declarations were already excluded from the
resulting native environment; this change removes their implementation-level
construction/import dependency. It does not change the model contracts.

The legacy bounded-model environment factory moved out of the shared selected-
result inventory into the remaining legacy signatures. Its two production
consumers were redirected. Shared inventory, CAS selections and native public
function signatures remain. Legacy observation facades still have users and
are not claimed retired by this prerequisite tranche.

Validation: workspace contract; scoped dependency compilation with 18 roots
(16 affected TS source roots and two nearest test roots); affected-file lint;
canonical declaration inventory equality across six factories (512 entries,
including type, body and binder mode), SHA-256
`ac71054c7a22d59247da2cb216975ee9d059133a08d919744546d05d0884b73d`.
All 17 existing native context/map/connecting tests pass. The connecting
retry completes in 102.63s at the reviewed 180s deadline, still 2GiB/512MiB;
its prior 90s termination is recorded above. Native-map LF emission passes
Lambdapi with its original one typed assertion at 90s/2GiB/o20. No LP source,
checker/runtime, public barrel, book artifact or model assumption changes.
No repository-wide typecheck/aggregate was run.

Local receipts: `cc2c1_typecheck_final.log`, `cc2c1_lint_final.log`,
`cc2c1_signatures_before.json`, `cc2c1_signatures_after.json`,
`cc2c1_consumer_checks.json`, `cc2c1_connecting_180s.log` and
`cc2c1_native_h_map.lp` under `emdash2/tmp/probes/`; the LP warning-enabled
log is under `emdash2/logs/probes/`. The source factory inventory and issued
rational-context tests cover the relocated legacy assembly during the transition.

Next CC-2c2: remove the legacy model observation/connecting/long-exact/rational
facades and their model signatures, preserve their native implementations and
shared raw preparation, and retire the corresponding obsolete LP model owners
and dedicated tests. Replace negative tests' dependence on production legacy
factories with local wrong-model fixtures or retained active rejection cases;
do not weaken native contract/mixed-model/reselection checks. Retain generic
CAS computation and ordinary provider data that current consumers still use.


CC-2c1 checkpoint: `739c045d`; this continuation begins clean and classifies
the previous turn as implementation progress. CC-2c2 retires the coupled
legacy-model facades, while preserving current native function bodies/profile
values and shared preparation. The LP former-model downstream closure has
nine owners after CC-2a; it is disjoint from protected native/reference roots.
Full symbol and reviewer inventories are in `cc2c2_retirement_inventory.json`.

Remove the six legacy-only TS model signature/workflow/rational-context files
and the old point/map/row/connecting wrappers in mixed observation files.
Flatten native profiles without changing their values; narrow internal point
unions to the surviving native type. Retire tests specifically exercising the
removed API. Keep ordinary provider/raw-spine tests by giving their fixtures a
model-independent raw environment, and preserve native wrong-model, foreign-
profile, mixed-model, normality/row, forgery and no-reselection rejection tests.
Only local test fixtures may reproduce an old nominal classifier if useful;
they must not retain a production compatibility API. Qualify native signature
identity, profile identity, scoped compilation/lint and the affected workflows.


CC-2c2 validation update: scoped compilation/lint, import audit and book
evidence pass after correcting the raw fixture's `baseEnvironment` argument.
The nine old-model LP owners and eight reviewers, six legacy-only TS files,
legacy observation wrappers and their unused old workflow gate are removed.
All 460 protected mathematical sources are unchanged. Native profile values
are identical, and all twelve surviving observation functions retain their
original computation (two obsolete diagnostic mentions of legacy support are
being corrected). Production source has no old-model symbol use; the remaining
strings in native tests assert its absence.

Native context/map/connecting and retained ordinary provider/spine suites pass
at their scoped limits. Two native wrong-profile tests are now strengthened
in the surviving direction (foreign source-point profile passed to the native
map/δ factory), replacing tests that called the removed legacy factory. Rerun
those cases after the diagnostic correction. Then replay the complete native
nonsplit LES and snake consumers to qualify the retirement end to end. Use the
existing 600s/2GiB/512MiB+4MiB-semispace profile for the three-test LES assembly,
and a 300s/2GiB/512MiB bounded snake suite; all LP consumers retain their owning
resource profiles. These are localized workflow checks, not repo-wide checks
or the deferred six-term direct-comparison experiment.


CC-2d inventory prepared while CC-2c2 integration runs: ordinary HomologyRecord
and its projections share `computational_homology` with the former selected
recipe. Extract the record/classifier/intro/projections without the
`homology_record_selected` selection helper; keep that helper downstream with
the explicit ordinary iterator. Move the unchanged raw-pair annihilator view
to its own shared test-data owner. Then redirect the native-derived ordinary
record consumers to those owners. This removes their accidental dependence
on the selected algorithm without inventing a new record or comparison.
Do not modify those LP owners until the current retirement checkpoint is
qualified. The retained iterator still explains the separate selected-
presentation and old ordinary exactness route; its migration remains outside
the deferred endpoint/normalization experiments.


CC-2c2 integration boundary: the strengthened map/connecting rejection cases
pass (23.36s and 55.78s). The full LES with ts-node reaches assembly (190.26s)
and begins reuse, then its worker exhausts the 512MiB V8 heap at 251.40s.
The established NUH qualification used compiled JS, not a resident TS loader.
Repeat using a scoped emitted dependency tree and the original Node 512MiB /
4MiB semispace / 2GiB OS / 600s envelope before considering any limit increase.
Do not change declarations, proof data or contracts to work around this loader
resource failure. The terminated process is confirmed complete; no live job
is restarted speculatively. The native snake integration has not yet run.


CC-3 source-review note (no implementation yet): `ProfComparison` is explicitly
`DefIso(Prof_cat,−,−)`, and the nucleus documents DefIso as judgmental inverse
cancellation, stronger than ordinary inverse evidence. The existing
`Adjunction_hom_prof_comparison` uses that computational interface. Therefore
a primary terminality redesign must distinguish the chosen computational
adjunction presentation from mere higher categorical contraction D≃1. Do not
silently identify those contracts or delete OneCat guards on the strength of
object-univalence. Read the actual whole comparison and its data/actions before
choosing the independently justified implementation boundary.


The compiled integration runner (session `46957`) completed successfully.
Its exact receipt is `cc2c2_compiled_integration_receipt.json`; the prior live
handoff is superseded by the results below.


CC-2c2 compiled integration succeeds: all three full LES tests pass in 392.22s
at the unchanged 600s/2GiB/512MiB+4MiB-semispace profile. Assembly, reuse and
emission complete. The result retains 12 degree points, 8 maps, 3 windows,
8 displayed points/7 arrows, 9 original whole exactness terms, 20 computed
equations and 13 interpretation claims; homology/connecting replays and
universal reselections are all zero. The manifest contains the expected 64
assertions. The compiled native snake passes all 9 tests in 47.77s, including
four pair certificates and the displayed diagram, without new interpretations.
Thus the loader-free replay resolves the observed V8 heap failure without
changing source, proof data, model contracts or memory limits.

The serial LP qualification runner (session `11204`) completed successfully;
its full result is recorded below and in `cc2c2_formal_checks.json`.


CC-2c2 qualified: the remaining legacy model layer is retired: nine LP owners,
thirty formal symbols, eight reviewers, six legacy-only TS files, five legacy
observation/context wrappers and the old workflow gate. The three native
profiles retain exactly the same values. Twelve surviving observation function
bodies retain their computation; only two diagnostics now correctly say native
profiles. Native signature inventories retain all 365 entries byte-for-byte
in canonical type/body/mode form. All 460 protected mathematical source files
remain byte-identical to d35cc98e, and live imports/registrations are valid.

The native context/map/connecting suites pass (9+4+4 tests). Foreign nominal
model/normality fixtures replace production legacy factories in rejection tests;
wrong model parameters, foreign source profiles, mixed models, raw-zero/row
misuse, forged data and reselection rejection remain covered. The two newly
strengthened source-profile cases also pass independently. Ordinary provider
and raw-spine suites remain (5+6 cases, with their two existing optional LP
cases skipped in the Node run); their fixtures no longer declare any model.
The full nonsplit LES (3 tests, 392.22s) and snake (9 tests, 47.77s) pass from
compiled JS at the documented original memory limits. The prior ts-node heap
failure is retained as runner evidence, not hidden as a mathematical failure.

All eight emitted LP artifacts pass: 64 LES assertions, 15 snake observations,
10 snake certificate signature assertions and 5 snake certificate assertions
(94 total). Their category/location/head/rule-family/parser warning inventories
match exact import-only controls, with controls reused only for identical
ordered imports. The existing 6GiB/180s/o20 profile is retained; the slowest
artifact takes 115.79s. No opacity, computation, model contract or output
assumption was changed for these checks. Compiler/loader guidance is now in
the repository-wide Lambdapi SOP's resource section.

Final scoped typecheck/lint, catalog, source metadata and book evidence pass.
The source-health report explicitly skips an aggregate run: 1252 files,
snapshot `161dc84ad6131b4699b694a69150e08afa8a4b0dc1eb5915271739a7b7f537b2`.
Twenty-one historical links in six documents point to the published df9b4778
sources. No release, push or further main integration occurred. Exact receipts
and emitted proof sources are in `emdash2/tmp/probes/cc2c2_*`, especially
`cc2c2_retirement_inventory.json`, `cc2c2_compiled_integration_receipt.json`
and `cc2c2_formal_checks.json`; source/log hashes bind the actual LP checks.

Next: complete CC-2d's useful-record separation, then undertake CC-3's
categorical terminal/initial and structural-interface review. Do not resume
Op/profile integration, spectral work, endpoint experiments or the deferred
six-term package comparison as an implicit prerequisite.


CC-2c2 checkpoint: `38e2e7c0` (local; worktree clean). CC-2d now extracts the
unchanged HomologyRecord classifier/intro/projections into
`emdash3_2_homology_records.lp`, excluding `homology_record_selected`, which
continues to belong to the retained selected algorithm. The raw pair's existing
annihilator view moves to `emdash3_2_chain_pair_kernel_tests.lp`. Redirect the
five record/cone-only consumers; keep genuine selected-homology consumers and
the ordinary iterator in their explicit reference layer. No symbol rename,
new proof body, primitive, rewrite or equivalence claim is introduced. The
remaining generic preadditive observation alias in the selected file can be
reviewed independently; it is not required by these native-derived record views.

Baseline and qualification: actual whole-adjunction and original-pair record
reviewers, retained selected-homology consumer, unchanged-declaration/unique-
owner audit, dependency graph and warning comparison under 90s/2GiB/o20. Update
source registration/health and book evidence; do not repeat the completed
full CAS replay for an unrelated optional-view owner move.


CC-2d qualified (2026-09-16): twelve unchanged HomologyRecord declarations
now have an independent observation owner; the unchanged annihilator view has
its own raw-test owner. `homology_record_selected` remains with the actual
selected algorithm. All moved/retained declarations are unique and their
bodies are unchanged. Original block hashes: record data
`89f96a6ad912899953fb4bd7b9d1525221035a5ee3302b76958b08eed5953152`,
raw test `f5913714527962d6b32a57cd05e16526df26f53828d997ebd08a411237fba20b`,
selection helper `1eceb528d1e32ef52b3da09602802c81179ab96b0a7afa67fca4faab8afd64ff`.
The two native-derived ordinary record consumers, boundary-factor helpers and
raw cone input no longer import `computational_homology`. The reference
iterator still does, intentionally. This adds no primitive, rule, opacity,
new universal selection or compatibility theorem.

Eight focused checks pass, including the actual adjunction/pair record views,
the retained selected computation and affected factor/cone consumers. The
whole-adjunction record warning inventory matches exactly in all five fields
(1459 warnings, no parser issue). The seven serial measured checks take
4.91–14.93s at 90s/2GiB/o20. Catalog and all 178 book evidence claims pass;
the source-only health refresh records 1254 files, snapshot `a16b8021473b6d887a00698bdcd5b0267c91fbe39e3f3c31765467832331f077`.
Local receipts are `cc2d_baseline.json`, `cc2d_checks.json` and the warning logs.

Retirement disposition at the end of CC-2: removed the superseded snake route,
old-model wrappers and compatibility consumers; kept the model-independent
CAS algorithms/provider proofs and useful ordinary observations. The earlier
selected-presentation/H-family/record-connecting/window route remains only as
the explicitly retained ordinary iterator/reference interface, whose dependency
was inventoried before deletion decisions. Its endpoint experiments remain
deferred, and no native→legacy comparison requirement is reinstated. This is
not a claim that every historically named helper has been deleted. Current
native constructions and their direct proof–CAS route are independent of the
retired model/algorithm interfaces. Proceed to CC-3's mathematical/interface
review; later source or book review may identify further genuinely unused leaves.


CC-2d checkpoint: `8a73f84c`; CC-3 starts clean. The previous turn made checked
implementation progress. First implement generic whole categorical contraction
along the existing canonical terminal functor, and its coherent family version
along `Terminal_funcd`. Both are transparent uses of OmegaEquivAlong, with its
retained inverse functors and whole inverse laws; no second equivalence type
or pointwise-only contraction dictionary is introduced. Derive object/core
contractibility as an observation of that data, not conversely. This is the
native interface needed to assess a primary terminality upgrade.

Keep computational DefIso presentation separate: the current adjunction Hom
comparison is explicitly DefIso-valued. The ordinary terminal/initial family
normalizers cannot simply lose their guards because objects of a Hom are
contractible. The generic contraction layer has no Op dependency of its own;
applying it to the represented Hom family must preserve that family's native
owner and the existing higher-variance/profile qualification. No general
univalence bridge, higher duality repair or weak-adjunction theorem is assumed.


### CC-3a — Categorical Contraction And Ordinary Terminal Adjunctions

Hypothesis: expose whole contraction using the existing Ω interface, and
make terminal/initial adjunction mates available in the independently valid
ordinary profile, without altering existing terminal normal forms or
reconstructing naturality by hand.

Implemented owners:

- `emdash3_2_categorical_contractions.lp`: nine transparent definitions,
  including whole category/family contraction, selected inverse and centre,
  evaluation, and derived object-contractibility observations. No primitive
  or rewrite/unification rule is added. The observation along an arbitrary
  supplied forward map keeps the actual adjunction mate instead of casting it
  to the canonical terminal functor.
- `emdash3_2_one_cat_terminal_adjunctions.lp`: two declared structural
  adjunctions plus ten derived whole unit/counit, diagram-comparison, Hom
  DefIso/Ω and ordinary contraction views. OneCat(C) is required. The whole
  profunctor comparison supplies varying-endpoint action before evaluation;
  selected inverses and both whole inverse cuts remain at generic owners.

The ordinary semantics justifies the extension: a terminal t gives the unique
map x→t, and an initial t gives t→x, naturally in x. This is the ordinary
adjunction with the singleton category. The implementation explicitly declares
its computational presentation rather than claiming it follows from today's
pointwise terminal β rules. It introduces no output-exactness or model axiom.

Normal-form decision: do not rewrite the terminal unit directly to the old
canonical-arrow transfor. The old terminal cut plus adjunction triangle would
then identify the intentionally separate !ₜ and idₜ normal forms. Instead,
compare the whole arrow diagram families using the existing ordinary DefIso
normalizers with identity endpoint components. Both directions keep the
original choices; users supply no extra naturality squares. No old symbol is
redefined and no old rule is changed.

Qualification: this implements the independent contraction/ordinary-adjunction
portion of CC-3. General higher TerminalObject replacement is not implemented.
Its prerequisite is a reviewed whole Hom comparison compatible with the
intended higher profiles/variance and a decision between the current
computational DefIso adjunction contract and weaker Ω equivalence. Those are
concrete interface distinctions, not a reason to weaken current checks or
resume the deferred Op/profile migration. Ordinary contractions remain valid
downstream observations; no proof irrelevance is imposed on inverse data.

Reviewer checks cover family inverse evaluation in both slots, retained base
and iterated-Hom action, whole mate cancellation, point round trips, selected
centres, categorical diagram endpoints, whole profunctor cancellation, and
preservation of !ₜ≢idₜ and the distinct unit normal form. Final focused receipts
and warning comparisons are recorded below before checkpointing.


CC-3a validation (2026-09-16): the two new reviewers pass 22 positive and two
negative assertions. Three unchanged reviewers also pass after importing the
new ordinary extension: terminal objects, whole terminal/initial family
normalizers, and the concrete Freyd terminal zero. They exercise the stable
terminal cut, old contraction projection and all original diagram endpoints.
Every check uses the serial resource guard, 90s/2GiB, subject reduction enabled,
`OCAMLRUNPARAM=o=20` and warnings enabled; no limit increase or opacity is used.

Exact import controls preserve every warning-inventory field after ANSI colour
normalization, with zero parser issues: contraction has 157 replaceable-slot
warnings and 1146 inherited critical pairs; the combined ordinary extension
has 159 and 1178 respectively. No new rule is installed. Receipts are
`tmp/probes/cc3a_validation_receipt.json`; logs are under `logs/probes/`, with
reviewers at `categorical_contractions-20260916-165745.log` and
`one_cat_terminal_adjunctions-20260916-165657.log`, controls at
`cc3_categorical_contractions_imports-20260916-165731.log` and
`cc3_one_cat_terminal_adjunctions_imports-20260916-165737.log`, and existing
consumer logs at `cc3_terminal_objects_consumer-20260916-165751.log`,
`cc3_commutative_ring_freyd_terminal_zero_consumer-20260916-165759.log`, and
`cc3_terminal_family_consumer-20260916-170110.log`.

Check/health registrations include both source owners and both reviewers.
Shell/Python syntax, strict catalogue, source TOC, all 178 existing book
evidence entries and diff hygiene pass. Source-only health refresh covers
1258 files, snapshot
`e5e08efb46ed91536af1ffa68502ea506fac2985dd6663251324bd0363ba0a42`;
it is not a fresh repository-wide typecheck. The native model/LES/snake owners
and contracts are byte unchanged; their recent 94-assertion end-to-end receipt
is retained. The source audit confirms exactly two new structural declarations,
19 definitions and no new rewrite/unification rule. Documentation states that
boundary explicitly. Proceed to CC-4's actual comparison-consumer inventory.


### CC-4 — Comparison Consumer Review In Progress

CC-3a checkpoint: `5c575800`. Native H/maps/δ and the qualified proof–CAS
consumers are unchanged. The following inventory separates actual supplied
point data from a coherent varying-parameter input; a free x binder by itself
does not construct the latter.

| Comparison | Actual consumers and present reason for point scope |
| --- | --- |
| `homology_family_global_point_map/equiv` | Native left/right/middle column comparisons, projection/quotient observations, and native-map comparison paths. The family H is whole; the target is H of `zero_arrow_family_point_input(A,D,h,x)`. That helper currently constructs an object, not a whole K→ZeroArrowCone functor. A whole upgrade must first supply that native whole introduction and its observations. It must not manufacture coherence from an arbitrary object function. |
| `image_family_global_point_map/equiv` and the Coim counterparts | Evaluation of canonical exactness and Im→K comparison observations at the same input. Both apply the existing whole Im/Coim functor to actual diagram equivalences. Their target-family introduction has the same prerequisite. Selected Ω inverses are retained, not transported by equality induction. |
| `introduced_input_diagram_map/equiv` and `one_cat_introduced_terminal_input_comparison_map/equiv` | Native column input comparisons. The complete comparison also receives A, b, a zero equation and an incoming observation at a chosen x. Those are genuine ordinary/CAS point inputs; no whole family for them is supplied. The diagram-reconstruction subcomparison, independently, has a whole owner. |
| `one_cat_terminal_input_comparison_path/map/equiv` | The symbol audit finds no external consumer of these three definitions. The introduced-input owner imports their module only for its dependencies. CC-4a retires the unused definitions and imports those dependencies directly. |
| `chain_pair_retained_*` | This former KernelPresentation/direct-input comparison has no remaining symbol or import consumer. CC-4a retires all four definitions. The independently useful ordinary iterator/reference constructions stay; they do not need this comparison. |

The existing diagram reconstruction r:R⇒id is already whole, with R=D∘E.
A bounded prototype tests reindexing it by an actual family V:K→Diag(C), then
applying an actual whole output functor F:Diag(C)→L. The proposed terms use
only existing `defiso_fmap`, native precomposition and postcomposition. No
manual square data or new primitive is proposed.

Prototype observations at checkpoint 5c575800:

- With the readable raw-composite endpoints, both reindexed forward/inverse
  component comparisons typecheck and compute to the corresponding components
  of the original r. The combined prototype then fails its whole automatic
  cancellation assertion; it is not a qualified new whole normalization API.
- For postcomposition, the constructor requires the native F∘− endpoint
  presentation rather than an unrestricted raw associative-composite reading.
- Repeating the first construction with literal native precomposition endpoints
  exposes a separate point-type comparison failure. Current source has the
  Cat-valued point projection for stable postcomposition; the corresponding
  precomposition point presentation does not compute through the same route.
  This is an identified projection/presentation boundary, not a demonstrated
  mathematical obstruction or evidence about the deferred six-term experiment.

No production source or rewrite/unification rule was changed for this
experiment. The candidate is `tmp/probes/cc4_diagram_family_reconstruction.lp`;
logs `cc4_diagram_family_reconstruction-20260916-170726.log`,
`...-170829.log`, `...-170948.log` and `...-171038.log` record the bounded
90s/2GiB checks with `OCAMLRUNPARAM=o=20` and subject reduction enabled.
The first candidate is mathematically `defiso_fmap((−)∘V,r)`; the second is
`defiso_fmap(F∘−,defiso_fmap((−)∘V,r))`. These formulas, source checkpoint and
failure distinctions are the durable recovery record; ignored files are only
local probe material. Do not describe either failed assertion as a proved cut.

Next decision: distinguish an ordinary whole isomorphism with retained checked
inverse laws from an additional judgmental-cancellation promise. If the former
is enough for the actual comparison consumer, use existing IsoEvidence/Ω data;
if a runtime projection/cut is needed, isolate that actual consumer at its
proper owner before proposing any narrowly scoped rule. Do not install broad
composition folds or restart the deferred duality/profile migration. Complete
the comparison inventory and independently useful whole interface before
marking CC-4 qualified; book/entry-point consolidation remains available as
independent work.


CC-4a retirement qualification (2026-09-16): the complete tracked symbol/import
scan, including TypeScript, check registrations and book evidence, finds no
consumer for the seven definitions in `one_cat_terminal_input_comparisons`
and `one_cat_chain_pair_input_comparisons`. The former's sole importer uses
none of its symbols. Replace that import with the same three dependencies in
the same order; preserve every declaration/body in the introduced-input owner.
Delete the two leaves and their health registrations. No positive reviewer or
public signature needs removal. Deferred audit JSON source inventories remain
unchanged historical evidence. Four dated documentation links now point to
the exact published df9b4778 sources, verified byte-identical before deletion.

Validation: the introduced-input reviewer passes both before and after;
all warning fields match exactly (169 replaceable-slot warnings, 1292 inherited
critical pairs, zero parser issues after ANSI normalization). The native column
comparison reviewer also passes. Both use the unchanged guarded 90s/2GiB,
`OCAMLRUNPARAM=o=20` profile. Logs are
`introduced_terminal_input_comparisons-20260916-171417.log`,
`introduced_terminal_input_comparisons-20260916-171509.log`, and
`freyd_native_column_comparisons-20260916-171529.log`; the local source/warning
receipt is `tmp/probes/cc4a_retirement_receipt.json`. Catalog, source TOC, all
178 book evidence links and diff hygiene pass. The source-only health snapshot
for 1256 files is
`5181b7e7fc3b9c8f599f2bb796b268b4553a1c9447f108ab4db458c13331e5d4`.

This retirement is a qualified implementation result of the consumer audit.
CC-4's whole comparison question remains in progress; do not count the ignored
failed prototype as a promoted interface. CC-5 book/entry-point consolidation
and CC-6 final audit remain required. Op/duality, action-profile integration
and the six-term experiment are still outside scope.


CC-4b continuation from 07e3f5d6: the preceding turn was progress (two checked
source checkpoints). No checker remained live. The existing diagram
reconstruction reviewer passes again. Replacing DefIso with IsoEvidence in
the reindexing prototype does not fix the endpoint-presentation mismatch;
no replacement interface has been promoted.

The consumer-driven prerequisite now has a concrete derivation: retain A
while reusing the protected internal transformation-graph section for
h:J∘A⇒D, apply Σ base change along Op(A), then take the outer opposite.
Because the graph helpers are protected, the experiment is a full-file copy
at that owner, not an external call to its protected symbols. Staging the
base-family comparison as an identity Functord makes all six helper
constructions typecheck without a new primitive or any manual naturality
square. This preserves the existing represented comma and hom_int/homd_int.
The final object assertion still fails; therefore the constructor is not yet
qualified for promotion.

The computed point is exactly (A(x), id_component(D(x),hₓ)). The residual
id_component has two proof-time-equal family presentations in the inferred
source/target slots. The current displayed identity-component rule repeats
`$E $E` in those slots, so it does not fire. Next bounded hypothesis: omit
only these two redundant inferred family guards in the existing
`tapp0_fapp0 … (id (Catd_cat K) E)` rule. This is an identity projection
cleanup, not an Op signature change, a strict-functor axiom, a new inverse
choice or a broad composition fold. Qualify it with a full-core owner-position
probe, the actual comma point and arrow consumers, inherited identity checks
and exact warning comparison before any source promotion.


CC-4b identity-projection qualification (2026-09-16): two existing nucleus
clauses now infer the source/target family presentations from the actual
identity head: `tapp0_fapp0` at a displayed identity, and the capped
`fdapp1_int_hom_fapp0` identity action. The measured nested Catd identity-category
guard remains. The unused family pattern in the latter is `_`. No primitive,
unification rule, general composition fold or Op/profile declaration changes.

The new `examples/displayed_identity_presentations.lp` uses ordinary pullback
versus raw-composition presentations, without Op. Its three positive checks
cover the component functor, its object action and the next displayed-Hom
cell; its negative check preserves an arbitrary displayed functor. The exact
pre-edit nucleus fails the first new assertion at line 22960 of
`cc4_identity_old_control.lp`. Both owner-position full-core candidates pass
subject reduction. The final source's regression passes. This is a runtime
projection correction for existing proof-time presentation equality, not
transport of a functor along a groupoidal path.

Actual comma experiment: the whole constructor, its object action
x↦(A(x),D(x),hₓ), and the source-arrow action A[g] pass. The target-arrow
assertion does not yet pass. After both identity corrections its computed
normal form contains three remaining nonidentity displayed-Hom actions:
fibrewise Σ of the internal action, total base change, and varying Σ projection.
Those actions cannot simply be erased. Preserve the precise fragment and
replay recipe in
[the active audit bundle](../emdash2/audits/categorical-family-introduction-boundary/README.md).
It is not a positive library module or a qualification of higher variance.
Do not add a primitive merely to conceal this observation boundary.

Validation of the identity correction:

- Whole nucleus source, final regression, ordinary terminal/initial adjunction
  reviewer and native column comparison reviewer pass. The source TOC,
  strict inferred-slot audit (zero unreviewed clauses), strict catalog and all
  178 current book evidence entries pass.
- The combined nucleus diagnostic file first exhausts the guarded 2GiB
  address-space limit with `o=20`; this is not a type error or an attribution
  of a performance regression. Its complete final-source run passes at the
  explicitly scoped, user-authorized 6GiB limit, with the same 90s deadline,
  `OCAMLRUNPARAM=o=20,v=1024`, subject reduction and warnings enabled. Measured
  wall time is 89.38s and maximum RSS is 3,568,160KiB (about 3.40GiB), with no
  swaps. This is one affected nucleus target, not a repository-wide aggregate
  or a changed global limit. Its near-deadline measurement should be retained
  rather than routinely repeated for reassurance.
- Exact warning inventories on the old and final whole nucleus, after ANSI
  and temporary-source-path normalization, have zero parser issues and no
  additions. Replaceable-variable warnings remain 157; critical pairs change
  from 1146 to 1144. The removed diagnostics are the displayed-identity /
  constant-section component overlap at line 14888 and the capped displayed
  identity/input-identity overlap at line 17898. This diagnostic change is not a general
  confluence claim and does not resolve the deferred section/profile issues.

Key logs: `cc4_core_identity_final-20260916-174829.log` checks a byte-identical
full copy of the final nucleus; `displayed_identity_presentations-20260916-174921.log`,
`one_cat_terminal_adjunctions-20260916-174448.log`,
`freyd_native_column_comparisons-20260916-174456.log`, and the measured final
`cc4b_final_diagnostics-20260916.log`. Source/warning/resource receipts are
`tmp/probes/cc4b_identity_validation.json`; the active mathematical boundary
is tracked in the audit bundle rather than existing only in ignored logs.
The source-only health report covers 1257 files with metrics snapshot
`0aaa980207f23307ea2f65558b68ae1744bbbdecfe256cfe4489d35ed1383e03`.
It does not claim that all registered files were rechecked.

Next: finish the actual comma target/whole-input observations and their H
comparison consumer; retain supplied finite CAS point data at its explicit
boundary. CC-4 is still in progress. CC-5 book/current-document consolidation
can proceed independently; CC-6 final audit remains required. The previously
qualified native model contracts and selected CAS data remain unchanged.
