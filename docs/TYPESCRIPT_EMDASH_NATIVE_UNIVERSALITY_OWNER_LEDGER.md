# Native Universality: Owner, Variance And Dependency Ledger

Date: 2026-09-12

Status: complete — revised native universality/homology scope, displayed CAS certificates, final audit and local book 0.9.0-dev qualified; explicit deferrals retained

Parent: [living implementation plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

Deferred user refinement (2026-09-13): C2b's ordinary-target presentation
is accepted for now. Later review should consider upgrading TerminalObject
itself to whole categorical terminality, without an intrinsic OneCat
restriction. The categorical subplan records the precise univalence/core
distinction and the native Hom-family/adjunction formulation. Do not merely
replace equality by OmegaEquiv inside the old objectwise groupoidal
quantifiers or remove C1 on the strength of univalence alone. The existing
whole terminal transformation's strict/lax profile is part of that later
review. This is not a new prerequisite for the active C2c construction.

Latest correction (2026-09-13): the primary connecting/exactness construction
must continue through whole categorical universal operations. The proposed
ordinary category-view bridge is optional compatibility work. The new
[categorical subplan](TYPESCRIPT_EMDASH_CATEGORICAL_EXACTNESS_AND_CONNECTING_PLAN.md)
records whole image/coimage comparisons, exactness and universal descent
for δ, with explicit implementation obligations. No whole exactness or
connecting theorem is claimed merely from this formulation.

Consolidated user review (2026-09-13): retain the present
r_C:DefIso(End(Diag(C)),D_C∘E_C,id) for the ordinary-target use, provided
everything remains computational/internal and the program does not manually
carry naturality/functoriality squares. The implementation meets that scoped
criterion: r_C is one whole internal witness; defiso_to/from select its two
transformations, generic DefIso cuts cancel them, and tapp/fapp expose their
components and higher action. Four endpoint rules compute identities. No
per-diagram naturality premise or specialized naturality rule is introduced.
The checked computations cover endpoint projections, inverse cuts and the
ordinary consumers; typed further action is not a claim of complete higher
normalization. The shape-law instance is still primitive rather than
derived from the beta-only Join interface.

There are actual equality proofs in functor_reconstruction_paths and the
ordinary square/cancellation/record modules. They apply generic naturality,
congruence and inverse computation to derive ordinary observations. They
do not provide a second functor/transfor structure or ask callers to supply
coherence squares. In particular, the reconstruction helper currently uses
strict_component_naturality_path. Its application here is OneCat-restricted;
do not generalize that equality argument to arbitrary lax transformations
without its needed profile. Prototype strictness migration stays deferred.

The dependency audit confirms that independent K/Q structures, their mates,
the H-family and native global H have 9/11/10/16-module source graphs with
no reconstruction, ordinary square-path or ordinary record dependency.
Thus this comparison is in the derived ordinary-view lane, not a truncation
of the generic primary K/Q/H program.

NativeArr(C) is prose for LaxArrow_cat C, not a new declaration. E_C and D_C
are already defined functors. The projected inverse of the current DefIso
is r_C⁻¹; it does not designate D_C as an inverse of E_C. The ordinary proof
uses only E_C's faithfulness, derived from this one-sided reconstruction.
The earlier proposal to replace it immediately by a full fixed-forward
equivalence was too strong and is withdrawn as an implementation gate.
Preserve the existing evidence; C4 is checkpointed at 1ea98f63 and NUH-4 is active.
The user explicitly retains the right to revisit this design against the
computational/internal criterion, including avoiding manually carried
naturality/functoriality square proofs or equations. Apply that criterion
at each new consumer; do not use checkpoint status to freeze the design.

The lax question has two different levels. In the standard strict
2-categorical model, strict interval functors with lax transformations and
modifications describe the usual lax-arrow category, with matching filler
orientation. Strict transformations instead describe commuting squares;
arbitrary unnormalised lax interval functors can carry additional unit data.
Thus a full interval/arrow comparison depends on the selected profiles, not
just on replacing an equality by a lax cell. One-sided lax naturality alone
does not supply either missing inverse laws or ordinary equality reflection.
The distinction between strict functors with lax transformations and lax
functors themselves is explicit in
[Nikolić's primary reference](https://tac.mta.ca/tac/volumes/34/22/34-22abs.html).
This semantic clarification is not a new higher/profile implementation row.
If a full comparison is later consumed, use the existing fixed-forward
machinery at the strength actually established. OmegaEquivAlong currently
has equality-valued inverse laws; DefIso has judgmental inverse cuts and
no existing DefIsoAlong classifier. Neither follows just from an arbitrary
lax reconstruction cell.

An additional reconstruction-action review probe at 062809 did not establish
the proposed raw mixed-action conversions. It is exploratory evidence only,
not a current consumer prerequisite. Do not expand the projection bridge
without a concrete required observation. All checked code and checkpoint
323e71fc are preserved; the present clarification changes documents only.

Semantic clarification: in the standard ordinary-category interpretation,
Diag(C)=Fun([1],C), while NativeArr(C) has arrows as objects and commuting
squares as maps. E extracts d(0→1); D builds the [1]-diagram of that arrow.
For every d, r_d:D(E(d))⇒d has identity components at 0 and 1. Its inverse
has the same endpoint components, and naturality for h:d⇒e reads
r_e∘D(E(h))=h∘r_d; both sides have h's two components. Thus the whole
natural isomorphism is mathematically valid in that ordinary interpretation.
The existing DefIso in End(Diag(C)) records this particular comparison.
This validates its intended semantics, not derivability from the current
β-only Join interface or its architectural placement as a new primitive.
No unrestricted higher/lax extension is being claimed. The usual arrow-
category interpretation is also explicit in the
[mathlib arrow-category reference](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Arrow.html).

Latest user direction (2026-09-13): park the Op/duality migration because
of its possible strict/lax interaction, preserve its partial results, and
start whole kernel/cokernel universality now. The earlier duality next-action
language below is resumption evidence only. No Op experiment is part of the
current completion gate or a prerequisite for NUH-3–7.

Earlier user direction (2026-09-12): use the
[native duality owner design](TYPESCRIPT_EMDASH_DUALITY_SEMANTIC_THEORY.md)
to continue native operations. Prototype strictness migration and Empty
audits are deferred; their earlier acceptance/next-action language below
is historical and does not govern this continuation. Integration of
`goal/opaque-action-profile-classifiers-v3.2` comes after this goal.

## Source Identity And Recovery

The worktree starts at `cbef77e76fc292453c8814b5ecc6d62e84132f01`.
Its active nucleus Git blob is
`91f1974ece225e399604dce24710bf1437ad3ef5`. At launch the active LP sources
and reviewers matched the final mathematical checkpoint `ff139362`.
NUH-3A/B now add independent whole-adjunction and H-family extensions;
legacy structural maps and H operations delegate into them. NUH-3C1 adds
native input construction from raw zero-composite data; NUH-3C2 derives
reconstruction and annihilation from the whole mates and unit/counit.
NUH-3C3 adds the explicit ordinary diagram-reconstruction law, derives
faithfulness from it, and constructs raw tests at original arbitrary diagrams.
The nucleus itself remains unchanged.

The preserved total-op patch is anchored to nucleus blob
`5387c65ab75ddcfff4b5ffca9fb6f9d082084774`. The current nucleus adds 328 lines
in four hunks after that anchor: a transformation observation, composition
and weakened-section observations, and displayed evaluation/pairing/identity
action. No old lines were deleted. These additions are part of the current
homology baseline and must survive a repair with their corrected variances.

An initial ordinary `git apply --check` rejected the preserved patch at its
first hunk. That is not source-conflict evidence: this is a zero-context
patch. `git apply --check --unidiff-zero` succeeds against the current source.
This establishes mechanical applicability only, not correct placement of
every zero-context insertion or qualification of the later added owners.
The old runner rejects the changed source hash and independently uses raw
timeout calls without the current memory/serialization guard. Do not run it
unchanged or bypass its anchor by resetting a worktree.

The complete original patch, its original baseline, and the four current
addition hunks must be audited together before producing a new staged copy.
There is no installed patched checker and no promoted repaired kernel.

## Native Foundations And Variance Inventory

The defining sources in the following table refer to the current nucleus
[emdash3_2.lp](../emdash2/emdash3_2.lp), unless another file is linked.
Symbols and consumer families were relocated with `rg`; line numbers are
observations of this source identity, not enduring authority.

| Owner | Current source observation | Design disposition and discriminating consumer |
| --- | --- | --- |
| `Op_cat`, `Op_func` | Lines 3282/7046; dimension-1 Hom transpose, object/arrow and whole Hom observations | Audit total-dual reinterpretation jointly with recursive Hom action; retain objects and test genuine dimension-2/3 directions |
| whole `op` | Line 7153; covariant Cat→Cat | Correct universe variance; direct Empty reproducer must fail at the repaired type, not at a missing declaration |
| `Op_catd_func`, `Op_catd`, `Op_funcd` | Lines 7221/12658/12720; unrestricted same-base formation/action | Base change and displayed-transformation variance are part of the repair; family-only reconstruction of bad op must fail |
| `hom_con`, `hom_int` | Lines 7900/8455; fixed-target and whole internal Hom owners | Preserve their ownership, cuts and distinct pre/postcomposition; classify each opposite slot by actual dimension/profile |
| `Pi_func` and negative-section observations | Line 13054 and mixed-section consumers | Preserve internal section calculus; test constant families and actual section components at the corrected bases |
| generic family/section profiles and strict naturality | Ordinary §6d, constant-section comparisons/evaluation and displayed §16a | NUH-1B2g derives Empty from their combined endpoint collapse; preserve generic directed section action and qualify strict equality at the actual profile |
| `homd_` | Line 13205; endpoint-observation family over opposite base Hom | Preserve relation to `homd_int`; audit variance of the base-Hom argument separately from total fibre duality |
| `Sigma_cat`, `Sigma_func` | Line 13258; totalization and constant-family product rule | Preserve existing owner; correct Hom totalization coherently rather than cancel only its visible base reversal |
| Sigma Hom | Line 13315; outer Op of a total of the dependent-Hom family | Terminal-base constant family must retain full fibre Hom direction; independent Sigma Empty derivation must fail |
| `Sigma_proj1_func` and second-coordinate observations | Line 13492 and associated generic action | Whole projection and further Hom action must remain typed; object pairs alone do not test fibre-cell orientation |
| `Functor_catd`, constructor package | Lines 14184/14255; negative source family and positive target family | Specify joint base/whole-action variance; no arbitrary higher regrading or duplicate composition owner |
| `Hom_catd`, `Transf_catd` | Lines 14505/14527; positive/negative section inputs | Correct the actual bases of negative sections and test the constant-Cat specialization at higher action |
| `Rep_catd_func`, `Edge_catd_func` | Lines 14565/14596; internal represented family followed by fibre opposite | Rep stays a view of hom_int; Edge must distinguish total opposite from variance-only transposition |
| `Presheaf_catd_func`, `HomPresheaf_catd_func` | Lines 14606/14618; composed mixed-functor-family target | Trace both argument variances and the external parameter through the complete composition |
| `Homd_target_section_catd`, `Homd_target_catd` | Lines 14645/14658; old mixed-family/Pi composition | First unresolved coupled semantic gate; keep original E over Z and native constructor, with no replacement-family premise |
| `homd_int` | Line 14688; fundamental syntactic package with displayed-functor argument | Preserve fundamental ownership, recoverability and canonical projection ladder; no replacement by total-category extraction |
| `homd_src_func`, `homd_src_sec`, `homd_tgt_func` | Lines 14806/14830/14852; whole-to-component-to-endpoint ladder | All levels must land in the same repaired target; test whole next action as well as endpoint equations |
| internal displayed hom action and extracted laxity | After the native homd ladder; Sigma consumes this action | Preserve the noncircular dependency: native homd action → extracted laxity → Sigma action |
| current displayed Eval/pairing/identity additions | Four post-anchor source hunks | Retain their legitimate computations while migrating every affected opposite/base annotation; historical prefix cannot validate them |

The source types are not a semantic consistency certificate. The known
inherited defects are still present, and the prospective repair must interpret the
whole collection together.

## First Coupled Target Question

The old pipeline has the schematic shape

```text
Rep → opposite Edge → HomPresheaf
                    → mixed Functor_catd with original E
                    → Pi → Homd_target.
```

The preserved total-op candidate moves HomPresheaf's outer base to the
shifted category and its inner base to a total opposite. The unchanged
mixed-family input then demands a regraded E. That is the documented
R(Z) versus Z type mismatch. It is a failure of that composition, not a
license to replace `homd_int` or assume R(Z)=Z.

The next design subrow must jointly derive the external x base, the inner y
base, the variance of HomZ(x,y), the family argument E and the resulting
whole homd source/target. In particular, verify that variance-only
transposition at a base Hom and total duality of a fibre are not conflated
in Edge/HomPresheaf. The preserved candidate's shifted-dual action on entire
functor categories also needs its actual strict/lax interpretation.

Possible changes to a supporting target classifier are not ruled out, but
they must have a coherent native internal interpretation and working whole
action. Do not add an opaque target solely because its point projection
can be made to resemble the desired Hom. A total-Hom observation is a
derived check, never the new defining source of native homd action.

**Acceptance gate:** a complete variance table for this composite, preserving
the original input family and native homd ladder, plus the matching
nonidentity base-arrow, base-2-cell, further-Hom and wrong-base controls.
This gate is still open; NUH-2 source mutation has not begun.

### First explicit dimension-2 constraint

The current mixed-functor action supplies a useful paper-level discriminator.
Let p,q:x→y and α:p⇒q be a genuine directed base 2-cell. For source family
A and target family B the object action at p is

```text
F ↦ B(p) ∘ F ∘ A(p).
```

An action from this p-image to its q-image needs components with directions

```text
A(p) ⇒ A(q),       B(p) ⇒ B(q).
```

With dimension-1 transposition of the base, A(p):Aᵧ→Aₓ and A(α) still has
the first required direction. With total base duality, α reverses and the
available comparison is A(q)⇒A(p). That does not supply the required action
for arbitrary noninvertible cells in the same ordinary functor category.

Therefore changing `Functor_catd`'s negative-family base from Transpose(K)
to total Op(K) merely to make the old E input fit is not a valid repair of
this interface. A changed transformation profile would require an explicit
new semantic account of the whole action, not just the same fibre formula.
This is a derivation from the displayed composition action, not a claim
that a new LP negative fixture has already been run.

Likewise, restricting Z to an ordinary category could hide R(Z) versus Z,
but would not repair native homd for arbitrary directed bases. Both the
unrestricted-base and noninvertible-2-cell controls belong in NUH-1B.
The next target design must resolve these constraints jointly with the
presheaf argument's variance while preserving the native homd owners.

## Whole Universality And Homology Dependency Inventory

| Owner | Current dependency | Intended next boundary |
| --- | --- | --- |
| [generic adjunction mates](../emdash2/emdash3_2_adjunction_mates.lp) | Defined whole Hom views of the existing adjunction comparison, with whole and point cancellation | Reuse as primary operation owners; preserve cut discriminators |
| [whole K/Q structures](../emdash2/emdash3_2_kernel_cokernel_adjunctions.lp) and [their mates](../emdash2/emdash3_2_kernel_cokernel_adjunction_mates.lp) | Whole functors and native adjunction evidence; no W/V or selected-factor dependency | NUH-3A implemented; H-family migrated in NUH-3B; ordinary views derived in NUH-3C4 |
| [kernel presentation](../emdash2/emdash3_2_kernel_adjunction_presentations.lp) and [cokernel presentation](../emdash2/emdash3_2_cokernel_adjunction_presentations.lp) | Legacy W/V-indexed choices, with adapters into the independent structures; structural maps now delegate there | Keep selected realization one-way; no mandatory old factor dictionary for new formal operations |
| [kernel record](../emdash2/emdash3_2_kernel_adjunction_records.lp) and [cokernel record](../emdash2/emdash3_2_cokernel_adjunction_records.lp) | Whole endpoints; old selected universal evidence is transferred/recentered | Derive ordinary factor/uniqueness observations from the whole comparison at the stated profile |
| [independent mate observations](../emdash2/emdash3_2_kernel_cokernel_adjunction_observations.lp) | Inverse-mate component formulas, reconstruction by cancellation, and annihilation from counit/unit, without W/V | NUH-3C2 implemented; diagram faithfulness and full ordinary uniqueness derived in NUH-3C3/C4 |
| [ordinary diagram reconstruction](../emdash2/emdash3_2_one_cat_diagram_reconstruction.lp) | New whole natural DefIso D∘E≅id at OneCat, with four endpoint rules; faithfulness is derived | NUH-3C3 retained after review; keep the primitive shape law and ordinary/strict-component scope in the trust audit |
| [native zero cone](../emdash2/emdash3_2_zero_arrow_cones.lp) | Represented comma built from native homdc/Sigma | Reuse current native ownership at the stated profile; the coupled Op migration is separately deferred; no independent cone grammar |
| [ordinary-target universal transformation](../emdash2/emdash3_2_one_cat_zero_cones.lp) | Existing OneCat profile exposes a whole family | Keep the ordinary specialization explicit; do not impose it on generic higher categories |
| [chain input](../emdash2/emdash3_2_chain_pair_zero_cones.lp) and [raw Freyd input](../emdash2/emdash3_2_commutative_algebra_freyd_zero_cone_inputs.lp) | Original selected boundary lift is unmated to introduce the native input | Input formation should use its native differential/zero structure before any kernel selection |
| [direct original-pair input](../emdash2/emdash3_2_one_cat_chain_pair_inputs.lp) and [its H record](../emdash2/emdash3_2_one_cat_chain_pair_homology_records.lp) | Original fields enter the existing native source without K/Q; the record then observes whole P/Q at the same pair | NUH-4A2 implemented; specialize to raw Freyd agreements and migrate actual map consumers next |
| [direct Freyd input](../emdash2/emdash3_2_commutative_algebra_freyd_native_inputs.lp) and [its whole H/record](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_homology.lp) | Original raw morphisms/agreement form input without W/P; H then uses whole P/Q with the existing local categorical data | NUH-4A3 implemented; raw classes, agreement and H endpoint check; migrate native maps and model binding next |
| [direct native maps](../emdash2/emdash3_2_one_cat_chain_pair_native_maps.lp) and [whole H action](../emdash2/emdash3_2_one_cat_chain_pair_homology_maps.lp) | Original raw-map factors and a derived ordinary comparison produce the native map without K/P; whole action feeds H | NUH-4B1/2 implemented; original components and record/H endpoints check; specialize to Freyd raw maps next |
| [direct Freyd maps](../emdash2/emdash3_2_commutative_algebra_freyd_native_maps.lp) and [whole H action](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_homology_maps.lp) | Existing raw-agreement conversion feeds the generic whole native/H map functors | NUH-4B3 implemented; all raw classes and actual H/record endpoints check; model and connecting integration remain |
| [direct raw input](../emdash2/emdash3_2_one_cat_zero_arrow_inputs.lp) | Raw b,d,d∘b=0 enter the existing native source via whole square action, with explicit OneCat and no K/Q | NUH-3C1 implemented; migrate the packaged chain-pair/Freyd adapters and derive their comparisons separately |
| [raw tests at original diagrams](../emdash2/emdash3_2_one_cat_zero_diagram_inputs.lp) | Actual reconstruction maps compose canonical raw tests into J(X)⇒d or d⇒I(X), retaining the original arbitrary d and raw b | NUH-3C3 implemented; use these inputs for ordinary records at K(d)/Q(d), without new selection or object casts |
| [whole H](../emdash2/emdash3_2_homology_adjunction_families.lp) and [native global H](../emdash2/emdash3_2_zero_arrow_cone_adjunction_homology.lp) | β=K(h)∘η; H=Q∘Arr(β), with independent K/Q structures; the global application retains explicit OneCat | NUH-3B implemented; old selected APIs delegate here, with the original comparison views |
| [independent homology record data](../emdash2/emdash3_2_homology_adjunction_record_data.lp) and [ordinary homology record](../emdash2/emdash3_2_one_cat_homology_adjunction_records.lp) | Actual β, original h/pair and derived K/Q records; no W/V inputs or new H | NUH-4A1 implemented; whole object, boundary, quotient, arrow and Hom-action endpoints check; package original raw inputs next |
| [direct connecting](../emdash2/emdash3_2_homology_record_connecting.lp) | Retained homology records and universal factors | Reuse mathematics and nonzero consumers while moving primary construction to whole universality |
| [whole connecting](../emdash2/emdash3_2_homology_window_connecting_transformation.lp) | Declared whole transfor whose component is the direct construction | Preserve actual endpoints and generic action; audit the declaration/interpretation contract |
| [finite iterator](../emdash2/emdash3_2_homology_bounded_generator.lp) | Retained row/map fields and whole H/δ with interior evidence | Reference consumer; symbolic endpoint debugging remains deferred |
| [formal model](../emdash2/emdash3_2_commutative_algebra_freyd_homology_models.lp) | Explicit W/V plus coherent K/Q presentations | Reusable model construction/registration and accurately classified realization contracts |
| [native connecting](../src/v3_2/algebra_polynomial_freyd_homology_connecting.ts) | Snake method with retained endpoint comparisons/descent | Preserve as computational method; compare against the whole formal characterization |
| [bounded model workflow](../src/v3_2/algebra_formal_freyd_long_exact_model.ts) | Supplied model and optional normality, prepared observations and explicit adoption | Automate repetitive model/reifier plumbing for the supported backend without upgrading trust claims silently |

NUH-3A/B supply whole K/Q, mates and H without W/V inputs. The full vertical
consumer now has a direct raw-input constructor; packaged input migration,
derived ordinary records and a retained nonzero result with its realization
contract remain. Adjunction triangles
alone do not establish all interacting exactness laws.

## Fresh Baseline Evidence

All four targets were checked serially by `scripts/probe.sh`, which uses the
current resource guard and ordinary subject-reduction checking. The copied
source and installed checker were not modified.

| Target | Result | Log under emdash2/logs/probes |
| --- | --- | --- |
| `emdash3_2.lp` | accepted; bounded positive baseline | `emdash3_2-20260912-151741.log` |
| `audits/internal_op_empty_reproducer.lp` | accepted; inherited defect reproduced | `internal_op_empty_reproducer-20260912-151820.log` |
| `audits/sigma_hom_empty_reproducer.lp` | accepted; independent inherited defect reproduced | `sigma_hom_empty_reproducer-20260912-151953.log` |
| `audits/internal_op_family_empty_reproducer.lp` | accepted; family reconstruction defect reproduced | `internal_op_family_empty_reproducer-20260912-152032.log` |

The last three successes reproduce failures of the encoding; they are not
positive mathematical-library tests. Eventual repair must reject their
invalid terms for the correct variance reason while keeping valid native
Hom/diagram action available.

Bootstrap/workspace validation passed, and Infinity Codex verified 1,103
archived responses in the original worktree. The latest verified recovery
response is the accepted 0003 of this session. No hook changed, no global
aggregate was rerun, and no mathematical source was edited for this initial
design tranche.

## Subrow State And Next Experiment

### NUH-7 / NUH-7B: Final Audit And Book Qualified

The [final audit](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_FINAL_AUDIT.md) records
every required outcome, the ten new declared structural instances, two nucleus
exchange rules, direct native proof–CAS evidence and the explicit deferrals.
No hom_int/homd_int owner was replaced. The public displayed LES flag is true;
the large six-term comparison remains deferred under D-NUH-080.

Book edition 0.9.0-dev updates Chapter 31, Chapter 12 and related appendices
around whole K/Q/H/δ/exactness, the general native snake and its LES comparison.
The original iterator remains identified in its own interface, without a
required old/new comparison. All 178 evidence claims/46 sources, typography,
links and source gates pass. The browser and tagged-PDF gates pass at 405
pages with 18 embedded fonts; 23 selected pages were visually inspected.
The owning promotion tool updates the repository PDF/Markdown with identical
checked hashes. The artifact receipt is `emdash2/tmp/probes/nuh7b_qualification.json`.
No external publication occurred. The PDF skill operation marker was run
successfully once before book authoring; do not repeat it on continuation.

The revised goal scope is complete. Op/duality, the deferred comparison and
other recorded research boundaries require their own later scope. The closing
checkpoint retains this ledger and the exact final audit rather than treating
any deferred computation as proved.

### NUH-6C3b2: Bounded Review Completed; Observation Comparison Deferred

H1 isolates the stored first step and proves its original canonical whole-map
comparison in 22.685s at 6GiB/180s/o20. H2 compiles exact current parents in an
isolated package (37.353s, 179 objects), then observes the first package and
both inverses before allocation failure at complete-package comparison
(48.739s, exit 134). The active mathematical owners, guard, proof data and
inverse choices remain unchanged. The [snake plan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records the source finding: no functor equality-cast in the reviewed observer.

Under the user's D-NUH-080 authorization, defer the still-unqualified large
comparison and proceed to final audit and book update. Preserve the bounded
snapshot/measurement/replay bundle alongside earlier attempts. This is not a
claim that the comparison is proved, and does not invalidate the separately
qualified six-term construction, typed data consumers or displayed CAS results.
No further C3b2, Op, or endpoint-debugging experiment is scheduled in this goal.

### NUH-5N2G3B2c4b: Displayed Native CAS LES — Qualified

The finite certificate retains one actual native input for each displayed
adjacent pair and the original canonical Ω data. The frontend constructs all
six pairs and one proof over the same coherent diagram. The nonsplit complete
workflow passes assembly, negative coverage checks, reuse and emission in
524.23s, with zero new certificate assumptions or decisions and no CAS
reselection. The native model context is v8; diagram profile v3 exposes checked
displayed exactness. Metadata was enabled only after the actual proof checks.

All 64 emitted assertions, six assembly assertions and 13 exact signature
assertions pass. Seven final consumer checks and their import-warning
comparisons pass; identical import blocks reuse verified controls. The last
emitter import repair preserves every proof-body byte and avoids repeating
CAS/adoption work. Sixteen transparent definitions add no primitive, rule or
opacity. The [model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records source/log hashes, focused TypeScript checks and the 1411-file source
snapshot. The cross-layer checkpoint is `5df9292c`.

Latest user direction D-NUH-080: conduct one bounded categorical review of
C3b2 with at most two focused implementation hypotheses. If no clear route
emerges, preserve the evidence and defer that comparison gap, then finish
NUH-7 and the newly required book update NUH-7B. Op/duality remains outside
this goal and will have its own later goal. Do not reinterpret a deferred
comparison as solved or drop the original data-retention/trust qualifications.

### NUH-5N2G3B2c4a: Complete-Arrow Certificates — Qualified

The generic certificate retains the already-transported native input X,
its canonical Ω evidence and the complete-arrow pair observation. Its
observation transport keeps the whole witness judgmentally unchanged and
rejects substituting a different native input Y. The three model constructors
apply the original public-pair proofs, with only the original complete-arrow
interpretation paths as additional arguments. All eight final owner/reviewer
checks and eight exact import-warning inventories pass; actual-result reviewers
retain the canonical witnesses unchanged.

Nine definitions and ten assertions add no primitive, rule, opacity or
output-exactness premise. The [model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records the unchanged generic and model-facing resource profiles. The body/LHS
audit, catalog/TOC, documentation hygiene and 1406-file source-health snapshot
pass. Exact evidence is bound in
`emdash2/tmp/probes/nuh5g3b2c4a_qualification.json`. Next assemble
the finite displayed diagram and frontend replay; the displayed LES exactness
flag remains false. NUH-6C3b2 and NUH-7 remain required.

### NUH-5N2G3B2c3: Canonical Public-Pair Exactness — Qualified

The generic comparison forms a genuine map/equivalence of actual native
inputs. It derives target zero composition and transports the original
canonical Im→Ker evidence. Whole-family staging supplies original incoming
recovery before concrete model expansion. All three concrete LES applications
and their explicit canonical-result reviewers pass at 6GiB/180s/o20; their
original row/normality proofs are applied, not replaced by assumptions.
Generic target/inverse observations pass at default 90s/2GiB.

Twenty-four definitions and fifteen assertions add no primitive, rule,
opacity or model contract. The positive δ comparison supplies both adjacent
input compatibilities with the existing H-map equations. The source/target
helper telescopes retain an unused opposite-column witness from the original
bounded-complex inventory through the existing H-comparison interface.
All thirteen final owner/reviewer checks and exact warning controls pass;
source/body, LHS, catalog/TOC, documentation and the 1398-file source-health
snapshot pass. The [model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records the seven 180s/6GiB/o20 model-facing checks and unchanged generic
90s/2GiB defaults. Exact evidence is bound in
`emdash2/tmp/probes/nuh5g3b2c3_qualification.json`.

Next construct the observed-pair/displayed-diagram certificate and frontend
nonsplit replay under the unchanged model/interpretation contracts. The
canonical pair proofs alone do not set the displayed CAS exactness flag.
NUH-6C3b2 and NUH-7 remain required; old/new homology comparisons remain removed.

### NUH-5N2G3B2c2b2: CAS-Facing Native H Map Agreement — Qualified

Both original whole row-triple H maps now commute with c_L,c_M,c_R and the
original public `freyd_adjunction_model_map`. The raw prefix identifies
matrix/presentation input; this is integration of two new native entry points,
not compatibility with the former homology design. All actual diagram/cycle
comparison premises are derived from original row data and native actions.
A raw column-map builder also reuses the original two row agreements.

The existing introduced-input comparison required a scoped body repair:
keep an actual D[x]→Arr(u[x]) map with identity endpoint action, then construct
the native input map and inverse through existing owners. Both public
signatures and endpoints remain. Eighteen new definitions and two revised
bodies add no primitive, rule, unifier or opacity. Sixteen added assertions,
two updated diagram-component expectations and six
actual supplied/derived-map consumers are qualified. All seventeen focused
checks and warning inventories pass; source/signature, LHS, catalog/TOC,
documentation and the 1385-file source-health snapshot pass. Exact evidence
is bound in `emdash2/tmp/probes/nuh5g3b2c2b2_qualification.json`.
The new H theorem/consumer uses the previously documented o=20 GC setting
at unchanged 90s/2GiB limits; other targets use default GC.

The [model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md) records exact
qualification and the corrected architectural boundary. Next use these
agreements and existing δ conjugation to form actual adjacent input
equivalences and transport canonical exactness to the CAS LES. NUH-6C3b2
and NUH-7 remain open; no old/new snake or LES compatibility gate is restored.

### NUH-5N2G3B2c2b1: Middle Column Comparison — Qualified

The original middle chain now constructs its whole input, incoming recovery,
native input comparison/equivalence, H comparison/equivalence and actual-target
quotient equation. The comparison itself needs no new short-exact-row premise.
Both H inverse slots retain the original selected factors. Ten assertions and
three original-data consumers cover quotient reconstruction and composition
with the existing incoming/outgoing whole H maps. These typed compositions
are not yet commuting equations with the raw public H maps.

Seven definitions add no primitive, rule, opacity or model contract. The
[model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md) records the focused
qualification and next direct comparison through actual native diagram actions.
The extra family-map constructor is unpromoted; its two residual native-parent
comparisons are not a prerequisite. Separate point quotient-reflection and
H-map reconstruction observations have checked in ignored probes. Keep whole
parameter comparison and general terminality claims outside this point slice.
Three owner checks, the final original-data reviewer and all four warning
controls pass at default 90s/2GiB. LHS, catalog/TOC, links/lifecycle and the
1374-file source-health snapshot pass; exact evidence is bound in
`emdash2/tmp/probes/nuh5g3b2c2b1_qualification.json`.
Next prove the surrounding H-map comparison, transport the original exact
pairs and qualify displayed LES exactness; NUH-6C3b2 and NUH-7 remain open.

### NUH-5N2G3B2c2a: Categorical H Comparison And Actual Column Quotients — Qualified

The H point comparison now applies the original Q to an actual categorical
map of the original boundary diagrams, with identity endpoint components.
Both original public signatures and all H objects remain. Its inverse data
comes from existing whole reconstruction and endpoint equivalence; no new
primitive, rule or equality cast is introduced. The old path-generated arrow
is not asserted definitionally equal to this computational presentation.

The actual whole quotient is compatible with this comparison. For a further
native map n to an actual target Y, the equation retains K(diagram(n)).
Both named Freyd column maps consume it under the ordinary model scope.
Their four map/equivalence bodies remain unchanged. An attempted target
normalization and its shared-owner variant are rejected: the latter exposed
an endpoint mismatch after earlier expanded checks allocated out at 2/6GiB.
The corrected actual-target theorem passes at default 90s/2GiB.

Thirteen new definitions, two revised bodies, thirteen added assertions and
two actual column consumers are qualified. All eleven focused checks and
warning-control comparisons pass at default 90s/2GiB, including public δ and
model-facing observation. Signature/body, LHS, catalog/TOC, documentation and
1370-file source-health checks pass. Exact evidence is bound in
`emdash2/tmp/probes/nuh5g3b2c2_qualification.json`.
The [model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md) records
source-bound evidence and the remaining surrounding-map/zero-pair integration.
The user clarified that categorical maps and whole universality should be
primary; equality belongs in justified derived observations, not operational
casts of categorical presentations. General terminality/profile refinement
remains a separate foundational review. Displayed LES exactness, NUH-6C3b2
and NUH-7 remain open.

### NUH-5N2G3B2c1: Native Input Equivalence Criterion — Qualified

The existing source and diagram projections jointly reflect equality of
native zero-cone maps under OneCat(C). Native Hom reconstruction uses the
existing whole universal transfor, with ordinary filler uniqueness; no
caller supplies a naturality square. The selected component inverses then
form an actual inverse native map, and generic projection functoriality
proves both inverse laws. Both inverse slots keep that computed map.

Eleven new definitions and one shared moved proof add no primitive, rule,
unifier, opacity or model contract. Eight new assertions test component
computation and inverse laws; a typed consumer transfers canonical native
exactness without a full-input-equivalence or target-exactness premise.
The [model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md) records
qualification and the rejected naive native-identity filler experiment.
Ten focused checks and all ten warning-control comparisons pass at the
default 90s/2GiB profile. The shared proof body is unchanged; strict LHS,
catalog/TOC, documentation and 1364-file source-health checks pass. Evidence
is bound in `emdash2/tmp/probes/nuh5g3b2c_qualification.json`.
Public H/maps/δ specialization is NUH-5N2G3B2c2; displayed LES exactness,
NUH-6C3b2 and NUH-7 remain required.

### NUH-5N2G3B2b: Canonical Point Exactness And Categorical Transport — Qualified

The native comparison of the same incoming diagrams has identity endpoint
components and a derived fixed-forward Ω equivalence. The original Coim
projection's naturality and native cokernel cancellation prove Coim→Ker
compatibility; whole Coim⇒Im naturality and its original normality evidence
then prove the canonical Im→Ker equation. The existing image-comparison
signatures are unchanged; their bodies now use this categorical diagram
comparison, whose endpoint action is checked directly.

`OneCatNativeExactAt` is ΩAlong on the original canonical Im→Ker at an
object of the existing native zero-cone category. Whole-family evaluation
and transport along an actual native-input equivalence are derived.
All three original LES proof constructors produce this predicate, without
an output-exactness premise. Ten assertions, three actual window consumers
and all eight changed owners pass with the default 90s/2GiB settings.
Both inverse slots of the transport compute to the retained composite.

The tranche adds 26 transparent definitions and revises two existing
image-comparison bodies; it adds no primitive, rule, unifier or opacity.
Next carry these certificates through the retained column H comparisons
to the public pairs and actual CAS diagram, then qualify the frontend.
Displayed LES exactness, NUH-6C3b2 and NUH-7 remain open. The
[model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md) owns that queue.

### NUH-5N2G3B2a: Native Point Comparisons And Mate Evaluation — Qualified

Eight transparent definitions identify the original family/global incoming
diagrams, apply the existing image functor to obtain the fixed-forward
image equivalence, evaluate both whole adjunction mates, and specialize
that evaluation to the original native cokernel descent. Six focused
assertions cover the image inverse laws, use after arbitrary composition,
and formation of the original Im→Ker compatibility statement.

No primitive, rule, opacity, model contract or output-exactness premise is
added. The [model plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records the remaining theorem: prove the canonical comparison compatibility,
then transport through the retained column H equivalences and the actual
CAS diagram. Statement formation is not a proof of commutativity or
displayed exactness. NUH-6C3b2 also remains open; the temporary constructor
projection/collector experiments are not promoted.

### NUH-6C3b1: Whole-Result Data And Inverse Access — Qualified

The [observer](../emdash2/emdash3_2_one_cat_native_exact_tail_observations.lp)
packages the original comparison and Ω evidence before specializing a
generic tail. Five generic constructor/field assertions preserve the
original witness and inverse choices. Twenty typed consumers access all
four actual packages, complete arrows, witnesses and eight inverse maps
from the assembled snake result at 90s/2GiB with `o=20`. Two transparent
definitions add no primitive, rule, opacity or supplied assumption.

Source/control warning inventories match. The scoped runner includes the
three new targets; its five routing/provenance tests pass. The
[subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records the checked boundary and measurements. NUH-6C3b2 still concerns
direct reconciliation with the original canonical maps/witnesses: whole
package comparison fails at 2GiB and 6GiB. Compare computational fields
separately before concluding that full proof-law normalization is needed.
Displayed LES transport and NUH-7 remain required after the six-term gap.

### NUH-6C3b: Resource Controls And Reuse Of Prior Techniques — In Progress

The unchanged retained reviewer still fails at 6GiB/180s with `o=20`.
The user-authorized 8GiB control also fails with allocation failure after
122.564s, before its 180s deadline, at about 7.73GiB peak RSS. The active
guard and all mathematical sources remain unchanged. The six-term input
reviewer passes; these failures concern the larger comparison/evidence
consumer and do not revoke the completed displayed nonsplit snake result.

The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
maps the earlier GC, exact-endpoint, transparent-name, compiled-parent,
record and law-opacity experiments to the remaining boundaries. A traced
named-step variant fails during conversion to reconstructed endpoint
indices, before its comparison assertion; actual projected indices also
reach that failure. An isolated record annotation passes its five generic
field checks and six-term parent, but its full reviewer still fails at
2GiB. The isolated eight original witness-typing/recovery assertions also
fail there. Next distinguish specialized type formation, projection
application typing and conversion at the first position before another
interface change. Keep the original canonical comparisons and inverse
choices; no output-exactness premise or opacity is introduced. The separate
displayed LES alignment/transport remains required after this observation.

### NUH-6E2b2: Exactness Indexed By The Displayed CAS Snake — Qualified

The [pair links](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_pairs.lp)
retain each original exactness input. The
[certificates](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_pair_exactness.lp)
keep its original Ω witness and compose only the observed-pair path with
the existing arrow interpretations. A
[single diagram predicate](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_diagram_exactness.lp)
indexes all four at the adjacent pairs of the actual five-arrow diagram.
Matching and the whole diagram path are derived through the existing
presentation-setness/finite-family owners. No new interpretation is supplied.

The frontend now checks that certificate on (x,id_R,0) with the original
six CAS presentations, including ∂=[1] on R/(x). The displayed-exactness
result is true; the source remains the same fourteen-claim arrow realization.
Nine workflow tests and 46 formal assertions pass. Thirty-two transparent
definitions introduce no primitive or rewrite/unification rule. The heavy
pair/certificate checks use their measured 6GiB/180s profile; the default
remains 2GiB/90s. Guard/profile tests and nineteen unchanged existing
signature comparisons qualify the tooling changes. Details and evidence
are in the [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

NUH-6E is complete at its stated model boundary. Next is the retained
NUH-6C3b full-result observation gap, then NUH-5N2G3B2 displayed LES
transport and the final NUH-7 audit. This is not goal completion.

### NUH-6E2b1: Original Whole Exactness And Point Evidence — Qualified

The [four proof families](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_exactness.lp)
and [point observations](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_point_exactness.lp)
retain the original comparisons, model and raw input. Direct ΩAlong
predicate heads avoid the expanded general-family inference cost. Sixteen
transparent definitions add no primitive, rule or assumption. Four existing
carrier definitions moved unchanged; the old LES owner still checks, and
fourteen existing frontend declaration types remain identical.

The frontend constructs all four proofs and their point data without
changing the fourteen-claim realization source. Seven workflow tests pass
in 42.484s. Twelve generic comparison/evidence/inverse checks, sixteen
signature checks and sixteen actual nonsplit proof/point checks pass under
90s/2GiB. Focused imports resolve the conformance header's earlier timeout;
no proof or inverse is opaque. Evidence and the local resource diagnoses
are in the [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

Next is 6E2b2: the certified native input's pair must be related to the
public arrow pair, then to the CAS pair with shared endpoint/diagram
coherence. These are required native links, not old-formulation comparisons.
The displayed-exactness flag and the separate 6C3b obligation are unchanged.

### NUH-6E2a: Standalone Nonsplit Native Snake Realization — Qualified

The [context](../src/v3_2/algebra_formal_freyd_native_snake_context.ts),
[preparation](../src/v3_2/algebra_formal_freyd_native_snake_preparation.ts) and
[workflow](../src/v3_2/algebra_formal_freyd_native_snake_workflow.ts) reuse
the original native backend, coefficient preparation and adoption session.
They retain all six CAS terms and five maps of (x,id_R,0), with ∂=[1]
on R/(x). Nine computed equations and five model interpretations qualify
the five native arrows; all fourteen requests reuse without source change.
One transparent matrix-zero constructor and seven exact private mirrors
provide the signature-only frontend's input without new rules or axioms.

Five workflow tests pass in 47.387s. Four affected original preparation
regressions plus the final signature exporter pass in 12.179s. Focused
types/lint and seven-signature/fifteen-concrete-assertion Lambdapi checks
qualify this boundary. The source contracts remain supplied and the exactness
flag remains false. The next row is 6E2b: connect the four derived native
exactness witnesses to this same concrete output, retaining shared endpoints.
The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records raw matrices, qualifications and remaining obligations.

### NUH-6E1: Native Freyd Snake Input And Five-Arrow Observations — Qualified

The [input](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_inputs.lp)
maps the original raw c∘(b∘a)=0 agreement to a whole constant-family
native input, before P/Q selection. The
[five whole transformations](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_maps.lp)
specialize the existing native snake using only the supplied model and,
for ∂, its normality. Their
[observations](../emdash2/emdash3_2_commutative_algebra_freyd_native_snake_observations.lp)
evaluate the same maps in the existing complete-arrow carrier.

Sixteen transparent definitions add no primitive, rule, unifier, opacity,
ordinary universal record or old-snake comparison. The 24-assertion reviewer
checks all five maps' projections and reconstruction, original input
recovery and its two endpoint actions, and off-diagonal connecting Hom
action. Its promoted form passes in 15.772s with default GC, under 90s/2GiB.
The warning inventory matches the existing-dependency control exactly.
Retaining the original generic additive/terminal projections in dependent
∂ annotations resolves the earlier local comparison allocation failure.
The separate 6C3b obligation is unchanged. Source/control logs and manifests
are recorded in the [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

Next is 6E2: actual nonsplit CAS adoption using these observations, then the
four derived exactness consumers. No TypeScript source or model contract
changed in 6E1, so the concrete acceptance case is not yet fully qualified.

### Scope Correction: Replace The Former Snake Without A Compatibility Gate

User direction on 2026-09-15, D-NUH-078, removes NUH-6D4 from the goal.
The former raw snake is a superseded formal interface, not a required
comparison target. Stop the unpromoted `nuh6r_universals` probe; its syntax
failure and source are recorded in the
[snake/LES subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md#nuh-6d4-former-raw-snake-comparison--withdrawn-2026-09-15).
No semantic comparison owner was promoted. There is no new requirement to
keep old APIs or prove old/new equivalence. Retire obsolete dependencies
after migrating any affected consumers to the native interface.

The new-native-snake/new-native-LES comparison remains qualified at
`0ddb6386`. Next is direct native concrete qualification (6E), followed by
the retained native 6C3b evidence observations, displayed CAS transport and
final audit. Historical milestone queues below are superseded by this
direction; their recorded results remain evidence.

The user's nonsplit acceptance case is retained explicitly by D-NUH-079:
R=ℚ[x], S=R/(x), `0 → R ─x→ R → S → 0`. Existing native LES
H/map/δ realization evidence remains valid at its declared contract
boundary. Direct native snake input (x,id_R,0) and displayed exactness
remain concrete qualification work, detailed in the same subplan.

This scope-only tranche changes seven guidance/plan files and no formal or
TypeScript source. All 62 worktrees were inspected; only this goal's prior
plan edit was present, and `cbef77e7` remains an ancestor of `0ddb6386`.
Validation uses exact diff/whitespace review, changed Markdown links and
anchors, fence balance, active-reference lint and report-lifecycle lint.
The existing semantic check evidence is carried forward; no typecheck or
repository aggregate is needed for this documentation correction.

### Priority Correction: Native Contracts Before Legacy Comparison

The user requests direct interaction between the new whole K/Q/H/δ/exactness
development and declared native model contracts. `FreydAdjunctionModel`
already provides the mathematical model surface. Preserve CAS-selected
matrices, witnesses, results and provenance; do not conflate that retention
with a requirement to reproduce the older formal H/map/δ objects and syntax.
The qualified retained workflow stays available as compatibility evidence.

NUH-5N1 native context/signature preparation, complete native H/map/δ
observation assembly, finite-diagram coherence and the native whole exactness
interface are qualified. Next is categorical exactness transport to the
displayed diagram. Native snake/LES work and
final qualification follow. The older formal-diagram comparisons and recent
auxiliary projection-normalization experiments are deferred, with snapshots
in the [resumption bundle](../emdash2/audits/deferred-native-exactness-observations/README.md).
The latter also affect native expressions, so the direct route is not a
claim that all projection normalization is fixed. Required native consumer
checks remain mandatory; report a demonstrated dependency if one arises.
Do not replace a missing output theorem by a stronger model assumption.

### NUH-6D3b: Original surrounding-map factorizations — qualified 2026-09-15

The [surrounding-map owner](../emdash2/emdash3_2_one_cat_native_window_snake_surrounding_maps.lp)
proves R∘k₂=H(p₀)∘q_B and q₁∘L⁻¹=j_B∘H(i₁) through original
row homology and kernel/cokernel reconstruction. The native diagram maps
retain q_B/R and L⁻¹/j_B endpoint actions, including their whole Hom
action. Eight definitions and ten consumers add no primitive, rule,
unifier, opacity or caller naturality field. Actual cycles and cokernels
remain distinct from middle H objects.

The native LES endpoint, connecting/sign and incident-map comparisons
are now qualified. Next qualify direct native concrete consumers at all
six terms/maps, preserving arbitrary a/c. The former raw-snake comparison
has been withdrawn by D-NUH-078. Native six-term evidence observations,
displayed CAS and final qualification
remain required under the [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

### NUH-6D3a: Original whole connecting/sign comparison — qualified 2026-09-15

The [connecting comparison](../emdash2/emdash3_2_one_cat_native_window_snake_connecting_comparison.lp)
proves L∘∂∘R⁻¹=δ and L∘∂=δ∘R using the original LES cover,
original snake cover, whole left-cycle reconstruction and existing native
δ uniqueness. Its actual whole arrow-diagram map retains R/L as endpoint
actions. Ten definitions and eight whole consumers add no primitive, rule,
unifier, opacity or caller square; no connecting map is reselected.

Next compare the surrounding maps through the original K(b₀) cycle and
Q(b₀) quotient factors. Do not identify those objects with middle H objects.
General reference-snake, concrete, six-term observations, displayed CAS
and final qualification remain required in the
[subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

### NUH-6D2c3: Original right H identification — qualified 2026-09-15

The [generic equivalence](../emdash2/emdash3_2_one_cat_native_homology_quotient_equivalence.lp)
derives H=Q(β)≃K(ḡ) through original whole P/Q operations. Kernel-
precomposition and image-source covers supply the required cancellations
under original normality; cover and annihilation evidence are proved.
The [window comparison](../emdash2/emdash3_2_one_cat_native_window_snake_right_homology.lp)
then identifies the original K(γ) with the existing native right H, retaining
its quotient and selected inverse data. Thirty-five definitions and sixteen
actual whole consumers add no primitive, rule, unifier or opacity.

Next prove the positive L∘∂∘R⁻¹=δ relation using the original LES cover,
then the surrounding-map factorizations. K(b₀)/Q(b₀) must not be called
literal H(B₀)/H(B₁); their cycle/quotient factors are part of the comparison.
General reference-snake, concrete, six-term observations, displayed CAS
and final qualification remain required in the
[subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

### NUH-6D2c2: Original right kernel comparison — qualified 2026-09-15

The [kernel comparison](../emdash2/emdash3_2_one_cat_native_window_snake_right_kernels.lp)
composes K(γ)≃K(χ) and K(χ)≃K(d̄₀ᴰ). Original whole K action maps
native diagram transformations; original inclusion cancellation proves
the inverse laws. The paired-zero diagram maps need not be inverse on
their targets. The composed w and its selected inverse reconstruct through
the original φ/ψ and kernel inclusions.

Twenty-three definitions and ten actual whole consumers add no primitive,
rule, unifier, opacity or normality premise. Both selected inverses and
their Hom action are retained. The original γ-diagram owner is the source
of K(γ). Next construct the original H(D₀)≃K(d̄₀ᴰ) comparison using
native normality/covers; right H, sign, general reference, concrete,
six-term observations, displayed CAS and final qualification remain required.
The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records the planned original-quotient/cover descent proof.

### NUH-6D2c1: Original right quotient and γ diagram — qualified 2026-09-15

The [quotient owner](../emdash2/emdash3_2_one_cat_native_window_snake_right_quotients.lp)
derives Q(a)≃Q(dₘᴰ) by original whole row/quotient descents. The new
row colift uses the existing row cokernel inverse into Q(i), with no
section into the middle object. Original row/Q cancellation proves both
inverse laws. The [γ owner](../emdash2/emdash3_2_one_cat_native_window_snake_right_gamma.lp)
constructs d̄₀ᴰ and χ=⟨0,d̄₀ᴰ⟩, proves χ∘φ=γ, and supplies its native
whole arrow-diagram map with endpoint actions φ and id.

Twenty-four new definitions and twelve actual whole consumers retain the
original P/Q and Em/E₀. No primitive, rule, unifier, opacity or normality
premise is added. The recovered a keeps its original diagram and Q choice.
Next compare K(γ), K(χ) and K(d̄₀ᴰ), then construct the original right-H
comparison with the required native normality/cover assumptions. Sign,
general reference, concrete, six-term observation, displayed CAS and final
qualification remain required in the
[subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

### NUH-6D2b: Original left H comparison — qualified 2026-09-15

The [homology comparison owner](../emdash2/emdash3_2_one_cat_native_window_snake_left_homology.lp)
constructs f:Q(α)⇒H(A₁) and its inverse by original whole Q descents.
Its [boundary comparison](../emdash2/emdash3_2_one_cat_native_window_snake_left_boundary.lp)
proves v∘α=[0,β_A]. Whole uncopairing and Q-unit annihilation give the
two descent inputs; quotient cancellation and the original u/v laws prove
both inverse identities. Fixed-forward ΩAlong(f) retains the same derived
inverse. Fourteen definitions and nine whole consumers add no primitive,
rule, unifier, opacity or new normality premise. The actual native LES
target H is a checked consumer, not a replacement homology choice.

Next: Q(a) versus the original upper-right differential quotient, then
K(γ) versus original right H and positive ∂/δ agreement. Preserve the
normality/cover boundary of the latter homology construction. The general
reference comparison, six-term observation gap, concrete qualification,
displayed CAS integration and final audit remain required under the
[subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

### NUH-6D2a: Original cycle comparison — qualified 2026-09-15

The [cycle owner](../emdash2/emdash3_2_one_cat_native_window_snake_cycles.lp)
constructs u:Z(A₁)⇒K(c) and v:K(c)⇒Z(A₁) through original whole row
and kernel mates. Original inclusion cancellation proves both inverse laws.
Fixed-forward ΩAlong(u) retains the same v in both inverse slots; their
projections and inverse Hom action check. Thirteen transparent definitions
and eight consumer assertions add no primitive, rule, opacity or normality premise.
The original P/Q and short-exact row capabilities remain explicit, and
an arbitrary replacement inverse is rejected by the reviewer.

Next: v∘α=[0,β_A], the whole Q(α)≃H(A₁) comparison, the right endpoint,
then the positive ∂/δ and general reference comparisons. The original
quotients and boundary choices must remain; this cycle equivalence alone
does not prove a homology endpoint comparison. The six-term observation
gap, displayed CAS integration and final qualification remain required.
Details and evidence are in the
[snake/LES subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md).

### NUH-6D1: Whole LES-to-snake input — qualified 2026-09-15

The [window input owner](../emdash2/emdash3_2_one_cat_native_window_snake_inputs.lp)
forms a=[bₘ,i₀], b=b₀, c=⟨b₁,p₁⟩ from the original four-row window.
The two original column zeros and derived native row-map reconstruction
prove c∘b∘a=0. The native input recovers the same a; it requires no P/Q,
short-exact row evidence or normality. Four supporting whole mate-zero laws
and five window definitions introduce no primitive, rule or opacity.
Eighteen assertions check whole formation, recovery, projections, retained
Hom action and the first actual α/γ consumers. The negative retains the
need for an annihilation premise.

Next: K(c) versus the original left cycles, then Q(α) versus left H and
K(γ) versus right H, preserving original P/Q choices. Compare the positive
covered formulas only after those maps are qualified. The
[subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md) records
this 6D2 design; the endpoint/sign comparisons are not implemented by 6D1.
Six-term comparison/witness observations, the general reference comparison,
concrete qualification, displayed CAS integration and NUH-7 remain required.

### NUH-6C3a: Whole result construction and input observations — qualified 2026-09-15

The previous turn made progress at `c7d190c2`, completing all four individual
exactness proofs. The native result now uses `FiniteArrowTail` in
`Functor_cat K C`, with the five original whole maps and four annotations
containing the original native input, its incoming-map reconstruction and
its original exactness witness. Thirteen definitions add no primitive or
rule. Nineteen assertions qualify construction, maps, generic annotation
computation and all four native input/zero observations.

The original constructor allocation failure is resolved at 2GiB by
`OCAMLRUNPARAM=o=20`. The same source passes a temporary 4GiB/default-GC
comparison. Threading actual projected endpoints fixes the input reviewer.
The broader comparison/witness reviewer remains unqualified after bounded
GC, 4/6GiB, fresh checked-object and post-proof-opacity experiments. The
[resumption bundle](../emdash2/audits/native-six-term-observation-boundary/README.md)
preserves that required 6C3b gap; it is excluded from positive examples.
No map/inverse data, proof law or checker logic is made opaque or changed
to force qualification. The user permits advancing independent LES work
before returning to this gap.

The earlier NUH-5 modular pair/certificate artifact passes unchanged at
2GiB with the same GC setting. This clears that specific resource failure,
not its still-required public pair alignment/displayed transport. The GC
procedure is documented in root guidance and the existing Lambdapi SOP.
The scoped runner and five profile/routing/provenance tests keep this
technique reproducible without changing global GC or memory defaults.

Next: review and construct the whole LES specialization triple in NUH-6D.
NUH-6C3b, LES/reference/sign comparison, concrete checks, NUH-5 displayed
integration and NUH-7 all remain required. The full goal stays active.

### NUH-6C2b2b: Fourth interior exactness at Q(b) — qualified 2026-09-15

The preceding turn made progress at `a44393cb`; third exactness remains
qualified. This tranche covers the original K(q₂) along π_b, then covers
the resulting image lift successively along the source-image map of γ and
π_a. All three cover conditions are derived from the same P/Q/normality.
The original γπ_a=cb reconstruction makes psu−by a c-cycle. Its native
K(c) lift followed by π_α gives z with q₁z=μrsu wholly.

The actual ε₄:Im(q₁)⇒K(q₂) and its original source-image map then
factor rsu. The Q-unit and all three derived cover cancellations give its
cokernel projection zero. Combined with the existing kernel-zero proof,
this gives fixed-forward ΩAlong on the actual fourth comparison. No Op
transport, new universal choice or caller naturality/factor record enters.

The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records 33 transparent definitions and 12 passing assertions. All six
owner/reviewer checks pass in 14–17 seconds each at 90s/2GiB; their diagnostic
inventories match exact import controls. Scoped LHS, dependency, catalog,
TOC, health and document checks pass, with no primitive or rule added.

All four individual interior exactness proofs now qualify. NUH-6C3 must
assemble and check the whole six-term result on the same maps/comparisons;
LES/reference sign comparison, concrete qualification, NUH-5 displayed
integration and NUH-7 remain required. This is progress, not goal completion.

### NUH-6C2b2a: Third interior exactness at Q(α) — qualified 2026-09-15

The preceding turn made progress at `ff71ab1a`; its second exactness
remains qualified. This tranche covers the original K(q₁) along π_α,
then uses q₁π_α=π_bκ_c to lift into the original Im(b). A second
derived cover along the source-image map of b supplies x with bx=κ_cps.
The original γπ_a=cb reconstruction lifts x into the same E used by ∂.
Kernel cancellation gives ℓw=ps, so ∂ρw=μrs wholly.

The actual ε₃:Im(∂)⇒K(q₁), with its original input/source-image
factor, then factors rs. Its Q-unit and the two original cover cancellations
give π_ε₃=0; the already derived kernel-zero proof gives fixed-forward
ΩAlong. All universal constructions use the original P/Q. No Op migration,
output assumption, new selection or caller naturality/factor record enters.

The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records 26 transparent definitions and 11 passing assertions, including both
whole cover cancellations and a consumer built from the arbitrary triple.
The six owner/reviewer checks pass in 13–19 seconds each at 90s/2GiB;
diagnostic inventories match exact import controls. Scoped LHS, dependency,
catalog/TOC/health and document checks pass, with no primitive or rule added.
The fourth exactness proof at Q(b), whole six-term assembly, LES/reference
sign comparison, concrete qualification, NUH-5 displayed integration and
NUH-7 remain required.

The user's later resource/opacity suggestions are recorded as tentative
options in the model/reifier plan. They do not change this tranche's
90s/2GiB guard or authorize opaque output assumptions; continue the remaining
mathematics before reconsidering that separate issue.

### NUH-6C2b1: Second interior exactness at K(γ) — qualified 2026-09-15

The previous turn made progress at `42c72f49`; its first exactness remains
qualified. This tranche uses the existing whole cospan-kernel cover theorem
twice: first over K(∂) along ρ, then along the source-image cover of α.
Both cover hypotheses are derived from the original P/Q and normality.
Whole reconstruction identifies the corrected difference jes−ax as a
b-cycle, giving w:V⇒K(b) and k₂w=μrs.

The source-image factor on the original second exact input makes the
canonical ε₂:Im(k₂)⇒K(∂) factor rs. Its Q unit and both cover
cancellations prove its actual cokernel projection zero. Combining this
with its original kernel-zero proof gives ΩAlong on that same comparison.
No arbitrary endpoint equivalence, new selection, output assumption or
caller naturality/factor record is introduced.

The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records 28 transparent definitions and 11 passing assertions, including
both whole cover cancellations and the composed arbitrary-triple consumer.
The six owner/reviewer checks pass in 14–18 seconds each at 90s/2GiB.
Their diagnostic inventories match exact import controls, and the scoped
LHS/catalog/TOC/health/dependency/document checks pass. No primitive,
rewrite or unifier is added. The third and fourth exactness proofs remain
next; LES/reference sign comparison, concrete qualification, NUH-5 displayed
integration and NUH-7 are still required.

### NUH-6C2a: First interior exactness at K(b) — qualified 2026-09-15

Original kernel lifts compare K(k₂) with K(v), where v:Im(a)⇒K(c).
Their reconstruction derives a section χ of η:K(v)⇒K(k₂), rather
than requiring one as an input. The existing image-source cover s_a
gives a derived kernel-precomposition cover with source K(v∘s_a),
which maps into K(α). Native inclusion reconstruction identifies the
resulting representatives with maps through the actual first comparison.

The comparison's original Q-unit annihilation, cover cancellation and
η∘χ=id derive its cokernel projection zero. Its previously derived
kernel-zero proof then gives ΩAlong on that same canonical comparison.
This completes the first interior position without a monic-a/epic-c
restriction, ordinary universal records or added exactness/cover premise.
The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records the 28 definitions, 11 passing assertions and validation evidence.
The six owner/reviewer checks take 13–17 seconds each under the existing
90s/2GiB guard. Their diagnostic inventories match exact import controls;
the scoped LHS/catalog/TOC/health and document checks pass. No primitive,
rule, unifier or TypeScript change is introduced.

This is **progress**. The second, third and fourth exactness proofs remain
required, followed by LES/reference sign comparison, concrete qualification,
NUH-5 displayed integration and NUH-7. First exactness is not the complete
six-term theorem.

### NUH-6C1: Whole six-term maps, zeros and comparison kernels — qualified 2026-09-15

The original α/γ reconstructions form two whole diagram maps α→b→γ;
native K/Q action supplies the four surrounding transformations and their
original source/target reconstructions. Alongside the same whole ∂ this
retains all six terms K(α), K(b), K(γ), Q(α), Q(b), Q(γ).

Native quotient/kernel cancellation proves both outer zeros. The original
K(b) lift into E reconstructs k₂ under ρ and vanishes under θ; ∂∘ρ=θ
then proves the first inner zero. The dual inner zero follows by the same
cover cancellation. No caller naturality/square or zero-composite field is
added. All four native exact inputs and actual Im→Ker comparisons are now
defined, and the existing generic theorem gives zero kernel inclusion for
each. This does not supply their still-required cokernel-zero proofs.

Thirty-six definitions and 22 assertions qualify under 90s/2GiB, without
new primitives/rules/unifiers, TypeScript changes or repository aggregates.
The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records exact validation and the original-input scope.

This is **progress**. NUH-6C2 must prove all four comparison cokernel
projections zero and derive their fixed-forward ΩAlong evidence. The
LES/reference sign comparison, concrete qualification, NUH-5 displayed
integration and NUH-7 remain required.

### NUH-6B: Derived annihilation and whole connecting ∂ — qualified 2026-09-15

Original coimage quotient cancellation and fixed-comparison normality make
s_a:A⇒Im(a) a whole cover. The image remains K on the original Q-arrow
family; no identification with a separately reconstructed kernel is assumed.
Native lifting gives v:Im(a)⇒K(c), and reconstruction yields v∘s_a=α.
Cancellation derives π_α∘v=0. The original ρ square lifts j∘κ_ρ into
this same image, and native kernel cancellation then proves θ∘κ_ρ=0.

Existing whole coimage-cover descent now constructs ∂:K(γ)⇒Q(α).
Its actual reconstruction is ∂∘ρ=θ, with uniqueness from the same
cover. The general a,b,c scope, all original P/Q selections and the
positive covered formula are retained. Twenty-two definitions and eleven
reviewer assertions add no primitive, rule, unifier or output assumption.
The [subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
records owner/consumer checks, diagnostics and the unsuccessful direct
kernel-reindex presentation separately.

This is **progress**. NUH-6C must construct all surrounding whole maps,
four adjacent zeros and four interior exactness comparisons. NUH-6D/6E,
NUH-5 displayed integration and NUH-7 remain required; the sign comparison
is not yet supplied merely by the positive ∂ construction.

### NUH-6A / 6B first part: General native snake factors and cover — qualified 2026-09-15

The [snake/LES subplan](TYPESCRIPT_EMDASH_NATIVE_SNAKE_AND_LES_COMPARISON_PLAN.md)
preserves the general a,b,c triple: neither monicity of a nor epicity of c
is assumed. The native input is the existing whole h:J∘A⇒Arr(c∘b),
with an input constructor/recovery for a supplied whole triple-zero path.
Original P/Q mating constructs α:A⇒K(c) and γ:Q(a)⇒D and both
whole reconstruction laws. No ordinary W/V factor record drives them.

The original E=K(γ∘π_a) supplies ρ:E⇒K(γ). The existing quotient-zero
and kernel-precomposition cover theorems derive ΩAlong on Coim(ρ)⇒K(γ);
native cancellation consumes that same proof. There is no inverse of ρ.
Original kernel lifting then gives ℓ:E⇒K(c), and θ=π_α∘ℓ is a whole
map E⇒Q(α) with computing point composition. Twenty-three definitions
add no primitive/rule/unifier; 20 focused assertions qualify the interfaces.
Expanded/global cover-review variants hit 2GiB and are recorded separately;
the final parameter-scope cancellation and pre-Abelian covered-map reviewers
pass. No TypeScript profile or model contract changed.

This is **progress**. The next proof is θ∘κ_ρ=0; the current
`covered_zero` proves only c∘b∘j=0. Whole ∂, the full six-term exactness,
LES/sign comparison, NUH-5 displayed integration and NUH-7 remain required.

### NUH-5N2G3B1: Original input-pair observations — qualified 2026-09-15

The original A,D,h of each whole canonical Im→Ker comparison now supplies a
paired observation of its incoming and outgoing arrows. This uses existing
whole transformations and adds only result data/projections, with no new
category, universal structure, rule or primitive. Seven definitions qualify
all nine pairs across the original zero/nonzero/zero windows. Thirty-six
concrete assertions and six generic checks pass under 90s/2GiB.

The combined pair/exactness certificate remains unqualified: both larger
input packages and direct/modular certificate variants exhaust 2GiB. These
experiments are not promoted. Existing whole proofs, point Ω observations
and the finite native→CAS path remain intact; neither the pair data nor
that path alone proves displayed exactness. Exact artifacts, rejected
alternatives and validation are in the
[model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md).

This turn is **progress**. NUH-6 is next from the completed general NUH-4
construction, preserving six-term scope/signs. G3B2's pair alignment,
exactness transport and combined consumer remain required before NUH-7.
No TypeScript profile or displayed-exactness flag changes in this tranche.

### NUH-5N2G3A: Original exactness point observations — qualified 2026-09-15

The required point consumer exposed the existing 2GiB boundary again. A
compact Sigma containing the original LaxArrow and its `OmegaEquivAlong`
witness, checked generic/native evaluation constructors, and typed projections
qualify all three comparisons/evidence at each concrete window. This is a
data wrapper around the existing equivalence, not another notion or choice.
Twenty-one definitions add no primitive, rule or unifier.

Native context v7 adds seven exact mirrors. The frontend passes the original
whole theorem term explicitly and names each evaluated result with a checked
transparent definition. Inline emission failed; named definitions retain
their bodies and complete dependency closure. The returned proof environment
extends the unchanged assumption source, with no additional assumption or
decision. Whole-only conformance still rejects body-bearing source entries;
point conformance rechecks the needed transparent bodies in source order.

Three exactness tests and nine native-context regressions are qualified;
the concrete test takes 97.90s under 120s and retains 69 assumptions plus
three derived definitions. Thirty-nine formal assertions pass under 90s,
including a 301,489-byte concrete artifact. Owner diagnostic inventories
match their controls. The [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records exact evidence and the failed expanded/inline alternatives.

This is **progress**. NUH-5N2G3B must relate the observed comparisons to the
displayed arrow pairs and finish categorical exactness transport. The
displayed-exactness flag remains false. No broader projection/inverse
normalization repair or combined-import memory repair is claimed.

### NUH-5N2G2: Whole finite diagram path — qualified 2026-09-15

A nonempty finite family of complete LaxArrow observations with adjacent
matching is a derived result-data view of the existing finite arrow tails.
Matching is proved proposition-valued. The ordinary Sigma path constructor
therefore lifts the existing arrow agreements to a path of the whole diagram,
including that evidence. The existing tail observer is retained literally;
no tail eta, category of complexes, primitive, rule or output assumption is
added. Nineteen definitions include six existing-observer endpoint β views.

Native context v6 contains the exact opaque mirrors. A pure frontend
constructor validates their signatures and the original arrows/endpoints,
constructs matching and the whole path, and adds no assumption or decision.
The native driver invokes it automatically. Its coherence flag is specific
to this finite observation representation; displayed exactness stays false.

Two focused constructor tests, nine native-context regressions and all three
integration cases are qualified. The combined run's reuse/emission passed;
its negative fixture accidentally chose identical H terms. The corrected
assembly case passes separately in 268.60s, with production code and emitted
terms unchanged. Full reuse takes 216.24s and reuses all 215 requests and the
identical path. All 89 final LP assertions and diagnostic comparisons pass.
The [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md) records
the exact runs, artifact hashes, source-health checks and temporary failures.

This is **progress**. NUH-5N2G3 must connect and transport the actual whole
Im→Ker exactness evidence to this diagram; the whole diagram equality alone
does not do that. NUH-6/7 and the existing deferrals remain required.

### NUH-5N2G1: Shared endpoint coherence — qualified 2026-09-15

Finite presentation objects are now proved set-valued by the existing
truncation owners. The original LaxArrow object's decoded endpoint views map
the supplied complete-arrow paths to presentation paths; setness proves that
two adjacent arrows induce the same path at their shared H object. Six
definitions add no primitive, rewrite, unifier, naturality square or new
semantic assumption. Both generic endpoint/path computations and a rejection
of unrelated endpoints check. All six junctions of the actual native/CAS
diagram check from their original interpretation references.

Nine generic assertions and 51 concrete assertions pass under 90s. The
small module/reviewer match the baseline's 1,166 critical-pair/157 pattern
reports; the concrete consumer preserves the original import order and
matches all inventory fields at 1,488/169. The older NUH-5N2F "no warnings"
report was a literal-word counter error and is corrected. Its successful
checks are unaffected. Failed whole-target and Grpd-level arrow-Sigma
comparisons remain candidate evidence; no foundation repair was added.

This is **progress** on realization coherence. The whole-diagram exactness
consumer and automated frontend proof construction remain NUH-5N2G2; no
full-coherence flag or output-exactness assumption is added. Details and
evidence are in the [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md).

### NUH-5N2F: Complete native observation assembly — qualified 2026-09-15

The native diagram driver retains the original whole CAS adoption, M/N and
source. Twelve degree H observations, eight maps and three δ windows cover
the eight displayed points/seven arrows. Repeated native/formal endpoints
and actual CAS selections agree; both endpoint δ maps remain zero and the
middle remains nonzero. Nine whole exactness theorem applications add no
output assumption. First construction reuses 182 requests and adds twenty
computed equations plus thirteen explicit row/arrow interpretations. Full
reuse reuses all 215 requests with the identical source and no new decision.

Three focused tests pass in 429.00s. The first 300s guard expired without
allocation failure; its reviewed extension to 600s retains the 90s default,
2GiB memory cap and all file/serial restrictions. Ten guard tests and focused
types/lint pass. Four modular proof artifacts pass all 54 LP assertions at
90s each with warnings enabled. No active LP mathematical source changed.

This is **progress**. Literal endpoint consistency and attached whole proofs
do not yet establish displayed-diagram exactness transport/coherence. That is
NUH-5N2G, followed by the general snake/LES sign comparison and NUH-7.
The separate combined-import memory boundary and auxiliary normalization
deferrals remain. See the [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
for exact evidence and the next consumer requirements.

### NUH-5N2E: Native whole exactness evidence — qualified 2026-09-15

The twelve whole API definitions name the original model/raw comparison
functors, their Ω predicates and the original derived evidence. Six Terminal
aliases serve the frontend. The terminal row contract was extracted unchanged
to a small shared owner. There is no primitive, rule, independent inverse or
output-exactness assumption. Native context v5 includes the six exact mirrors;
the pure constructor applies all three theorem owners to the actual window.

The concrete consumer retains its 69 source assumptions. Its checked
dependency closure contains 59 declarations and excludes the unused δ
interpretation reference. All original model/row/matrix dependencies remain
and are rechecked. General/Terminal reviewers, symbolic/concrete emitted
proofs and the native δ regression total 17 passing LP assertions. Three
exactness tests pass (77.57s, reviewed 120s guard), three legacy regressions
pass (3.26s), and focused types/lint plus static metadata checks pass.

The combined δ-point-observer/exactness import exhausts 2GiB in either order,
before new consumer terms are checked. Narrow shared-row ownership and exact
proof dependency closures qualify the actual proofs; they do not fix that
loader boundary. No failed point/inverse-projection probe was resumed.

This turn is **progress**. Full H/map assembly, transport from the original
whole exactness families to the displayed diagram, its coherence and the
later snake/LES sign comparison remain. See the
[model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md) for evidence.

### NUH-5N2D: All native connecting windows — qualified 2026-09-15

The bounded driver checks the current original CAS adoption, source membership
and prepared equation/result inventory, then interprets every window with
one M/N and one source. Degrees 0/1/2 retain displayed positions 6/3/0 and
zero/nonzero/zero CAS arrows. The first pass reuses 91 claims and adds fifteen
matrix equations plus five model interpretations (two row contracts, three
δ agreements). Reuse covers all 111 requests without further decisions.
Foreign/stale preparations, unrelated replay, missing original adoption and
wrong normality are rejected before any additional interpretation.

Four tests pass in 157.71s with a reviewed 240s limit. The measured first
pass takes 91.26s and reuse 54.63s; compiler and all three LP checks retain
90s limits. Nine emitted assertions, focused types and lint pass. No active
LP source/registry changed, no aggregate ran, and the deferred auxiliary
endpoint/projection experiments were not resumed. Full evidence and artifact
paths are in the [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md).

This turn is **progress**. Native categorical exactness, complete H/map
assembly, whole-diagram coherence, and the later snake/LES sign comparison
remain. Sharing M/N and the source across windows is not itself that proof
of coherence.

### NUH-5N2C: Direct native middle-window δ realization — qualified 2026-09-15

Two definitions expose the existing whole P/Q row predicate at Terminal and
the complete arrow of the original native raw-window δ. The H endpoints stay
native; no legacy H comparison is inserted. Native context v4 and exact
47-argument mirrors use that interface. The row/δ adapters share unchanged
lossless transport and current-data validation, with distinct native model,
row/observer and operation choices. No primitive or rule was added.

The automatic native workflow prepares source/target raw H inputs, rows,
row maps and matrix facts; it records native row interpretations and one δ
agreement. The middle nonzero two-term nonsplit window reuses 23 claims,
adds eleven computed equations and three interpretations (two row predicates
covering four rows, plus δ). There are no standalone point interpretations
or output-exactness assumptions. Reuse needs no new source or decision and
covers all 37 requests. Wrong normality, legacy/mixed models, forged data and
raw chain-zero proofs used as row shortness are rejected.

Four native δ tests pass (81.69s), nine native context/H regressions pass
(55.25s), four complete-arrow regressions pass (30.74s) and four legacy δ
regressions pass (39.54s), each in its own 90s guarded process. Focused types/
lint and 30 affected LP assertions pass. Static catalog/health/TOC are current;
no aggregate or deferred normalization experiment ran. Full evidence is in
the [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md).

This turn is **progress**. The zero endpoint windows, native exactness,
complete bounded diagram/coherence and later snake/LES sign comparison remain.
The explicit δ interpretation is not a derivation of that comparison.

### NUH-5N2B: Complete native H-arrow realization — qualified 2026-09-15

The existing FreydArrowObservation/raw introduction now have a shared
model-independent owner; names and bodies remain available to the legacy
workflow. One new native definition constructs the existing lax edge from
the original H endpoints and H map. No primitive or rule was added. Native
context v3 mirrors that observer and shared carrier. Native and legacy map
adapters share transport with distinct profile/model/owner/operation choices.

The native realization session separates raw-point preparation from point
interpretation. The complete-arrow workflow derives its matrix inputs and
adopts one agreement including both endpoints, requiring no independent
point claims or formal selected-provider proof. The nonzero/nonidentity x
map in the degree-0 nonsplit sequence reuses nine claims and adds three
computed matrix equations plus one model interpretation. Repeat use reuses
all thirteen requests. The earlier two-term fixture remains unchanged.

Four arrow tests pass (33.62s), nine native context/H regressions pass
(53.47s), and four legacy H/map regressions pass (6.63s). Focused types/lint
and 27 affected Lambdapi assertions pass in separately bounded processes.
This includes the legacy native-connecting reviewer after the carrier move.
No aggregate or deferred normalization probe ran. Full evidence is in the
[model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md).

This turn is **progress**. Native δ/exactness realization and coherence of
the complete bounded diagram remain; one complete-arrow agreement does not
prove that whole-diagram coherence or supply output exactness.

### NUH-5N2A: Native H observations and first CAS realization — qualified 2026-09-15

Three definitions expose application of the original whole H, its raw-map
functor specialized to M's P/Q, and that functor's application. Their five
reviewer assertions preserve original native inputs, endpoints and Hom
action; no primitive or rule was added. Exact frontend object/map mirrors
extend the native context to profile v2. Legacy observation transport is
shared with distinct native owners, model type, profile and operation IDs.

The new native H workflow automates reuse/computation of the three matrix
prerequisites and the explicit selected-presentation realization. The
nonsplit degree-1 C consumer needs one additional computed chain equation
beyond its original 55; it adds one separately classified model-interpretation
claim, requiring no old model or formal selected-provider proof. Reuse adds
nothing and requests no further decision. Nine native tests pass in 53.85s;
four legacy H/map regression tests pass in 7.68s. Focused types/lint and ten
emitted LP assertions pass, in addition to the five owner checks. Catalog,
static health and source TOC are current; no aggregate or deferred probe ran.

This turn is **progress**. The remaining NUH-5N2 boundary is complete-arrow
CAS realization, native whole δ and categorical exactness under coherent
realization/row contracts. The point agreement is a selection-specific
interpretation condition, not whole coherence or output exactness. Full
evidence is in the [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md).

### NUH-5N1: Direct native model/context — qualified 2026-09-15

Implemented exact private mirrors of `FreydAdjunctionModel(R)` and
`FreydAdjunctionModelNormality(M)`, plus a separately issued native rational
backend/context. It declares M/N directly without the legacy model or adapter.
Coefficient collection and selected CAS inventories are factored into one
model-independent preparation shared with the compatible old context.

Five native tests pass (29.91s), including negative legacy/model/ring checks
and the original nonsplit replay: 55 computed-equation assumptions cover 422
labels, whose typed raw witnesses require no extra assumptions. Four legacy
preparation/replay tests pass (9.51s). Focused types, lint, workspace checks
and six warning-enabled Lambdapi input assertions pass. No active Lambdapi
owner/rule changed and no repository aggregate ran. Evidence is recorded in
the [model/reifier plan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md#nuh-5n1-direct-native-context--qualified).

This turn is **progress**, not blocked: native context preparation and CAS
equations now work directly. M/N remain supplied inputs, and model-specific
H/maps/δ realization, row contracts and native exactness consumers remain
NUH-5N2. No output exactness is assumed. Do not describe the successful CAS
equation run as the completed native model realization.

### NUH-5B2d2b: Complete retained model workflow qualification

**Qualified after 3871827c.** The original combined fixture is retained,
including all six older selected H constructions, raw witnesses, 18 model
points, eight maps, all three connecting windows, and later reuse/rejection
tests. The user authorizes reviewed extensions of the former 90-second limit;
the selected complete five-test gate now has a measured 300-second deadline.
Its OS memory/file/serial bounds remain unchanged.

A worker probe found that this Node build does not forward V8 CLI heap flags
to isolated tests. The gate supplies them through `NODE_OPTIONS` and checks
the actual worker heap limit before adoption. Connecting/row adapter profile
v3 uses the existing lossless table codec for request payloads. Original
realizations, values, formal terms and current checks remain intact. Adapter
closures retain the exact checked private declarations they compare instead
of copies of their entire prerequisite environments. No proof-validity cache,
Core/checker rule or mathematical primitive is added.

The single-window regression passes four tests, exact payload round trips and
nine LP assertions, with byte-identical emitted source. All five full-workflow
tests pass in 267 seconds: complete adoption, both endpoint windows, the
nonzero middle δ, shared row proofs, reuse and rejection checks. The resulting
source has 143 entries, including 38 explicitly trusted semantic claims;
model/normality inputs remain separately supplied. The three emitted LP
files pass all 18 assertions. A wrapper count typo (four instead of six)
was corrected, and the exact emitted files checked without repeating the
passed adoption stage. The receipt records their hashes and stage evidence.
Ten resource-guard tests, the worker preflight, focused compilation, lint and
document hygiene pass. The [subplan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records the controls and qualification.

Next NUH-5B2e: native categorical exactness observations, using the existing
whole Im⇒K evidence and the original retained-H comparisons. NUH-6
snake/native comparison and NUH-7 final qualification remain open.

### NUH-5B2d2a: Fresh batched declaration replay

**Qualified after cc8a4dc0 (2026-09-14).** The measured bottleneck is repeated
typechecking of declaration prefixes during assumption-source validation.
The additive LF `extendOpaqueBatch` operation checks ordered scopes and the
complete declaration types afresh once. It preserves the original prefix,
transparent definitions and reviewed checker factory; new bodies/transparent
declarations are rejected. Source replay keeps every adoption-current check
and the original final environment comparison. No cached validity, new
conversion rule, mathematical primitive or LP source change is introduced.

Eighteen focused LF/source tests and the existing three-test six-H/raw-witness
consumer pass. The latter completes in about 66 seconds. The native δ gate
passes its four adoption/emission tests and nine LP assertions; its emitted
source is byte-identical to cc8a4dc0. Focused compilation and affected-file
ESLint pass. The [subplan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records commands, logs, exact artifact identity and measured phase costs.

The full model run is still unqualified: all 18 point and eight map observation
builders return, then allocation fails near 89.5 seconds before the model
workflow returns. Next NUH-5B2d2b audits the test's model prerequisites:
it currently first runs the separate older six-H/raw-witness consumers, while
the model API accepts the retained whole adoption directly. Keep the larger
combined-source case and all required checks/windows/contracts. Do not claim
model completion from the successful observation builders alone. Native
exactness observations, snake/native comparison and final qualification remain.

### NUH-5B2d1: Native TypeScript connecting observation at retained H

**Qualified after 96ddecaa (2026-09-14), through one retained nonsplit window.**
The new context aliases native whole normality/row shortness at the original
model's P/Q adapter. A raw point observer applies the existing whole δ and
selected column comparisons; a general-K retained-model stage uses the
existing input equivalences, and the outer complete-arrow observer fixes
Terminal_obj. Five definitions add no primitive, rewrite or unifier.

The earlier input comparison now directly uses the same incoming-source
law instead of importing unused whole-H recipe comparison proofs. Its
proof is unchanged after the old alias unfolds. This dependency narrowing
and the staged observation make the source join fit the existing guard.
The failed combined-import/object experiments are not qualified alternatives.

TypeScript preserves the 47-field layout and original raw/H selections but
uses three distinct native mirror names. Old normality/row terms are rejected.
Registration requires `nativeNormalityContract`; profile revisions record
native whole δ and selected categorical comparisons, with no endpoint casts.
The existing Core/checker/evaluator and public barrel are unchanged.

Eight focused tests cover contracts, automatic preparation/replay and
nonzero nonsplit adoption/reuse without reselection. The new focused gate
checks compilation, adoption/emission and the actual emitted LP in separate
bounded processes. Model, normality, row and arrow semantics remain supplied
or trusted, not closed constructions. The subplan records validation details.
Six registered LP assertions, four generic emitted assertions and nine
concrete emitted assertions pass. Complete owner/reviewer warning blocks
match controls at 1,490/169; the narrowed input owner stays at 1,290/169.
Two existing comparison reviewers, affected audits/catalog/TOC/report checks,
localized TypeScript compilation and ESLint pass. Source-only health covers
1,207 files. Complete bounded adoption still terminates under the guard;
its current costly phase remains to be isolated.

Next NUH-5B2d2: complete automatic bounded-model adoption and native exactness
observations. Then NUH-6 snake/native comparison and NUH-7 final qualification.
The single-window result does not close the parent goal.

### NUH-5B2c2: Derived columns compare with original raw and retained H

**Qualified after 5925c5b1 (2026-09-14), through both column comparisons.**
The raw specializations retain the existing whole column inputs and derive
their incoming point observations from whole source recovery. Ordinary
diagram reflection and terminal-tip uniqueness compare the two original
transformations at the actual outgoing diagram. Existing fibre inclusion
and canonical point introduction give fixed-map input equivalences.
The original raw column chain witness remains the comparison target; it
is not a new input to δ or a supplied naturality square.

Original whole H maps those comparisons and selected inverses. Composition
with the inverse of the earlier retained/native comparison lands in the
older model's exact H objects, using existing IsoEvidence and OmegaEquivAlong
owners. The native core still needs no W/V dictionaries. The actual whole
δ/component/Hom-action reviewer checks these column H endpoints and the
resulting raw-H arrow. No new natural comparison in x is asserted.

Twenty-three definitions in seven new owners add no primitive, runtime
rule, unifier or earlier LP edit. Three reviewers contain 25 passing assertions.
The subplan records localized validation and the larger all-exactness
import experiment's allocation boundary. Use the actual column/H/connecting
dependencies for these observations; keep every resource guard unchanged.
Complete warning inventories and raw blocks match controls at 1,489/169
(native/retained H) and 1,490/169 (connecting) critical-pair/pattern reports.
Affected strict audits, catalog, source TOC and report headers pass;
source-only health metrics cover 1,203 files. No TypeScript source changed.

Next NUH-5B2d migrates TypeScript model observations to the native whole
owners. Native normality and raw-row shortness remain explicit supplied
contracts. Retained nonsplit replay/adoption, exactness observations, snake
comparison and final qualification remain required.

### NUH-5B2c1: H-family point and global H at the observed input

**Qualified after ae266507 (2026-09-14), through the point comparison.**
The point-input observer retains the original A[x], D[x] and h[x] before
any P/Q choice. Under the existing global-H ordinary profile, the two
actual boundary diagrams compare through their existing canonical
point-introduction paths. Original Q maps that categorical comparison
once, preserving both actual H objects and the selected inverse via
OmegaEquivAlong action. No intermediate quotient, object cast, reselection
or caller coherence proof is introduced. This is a point observation with
the full Q Hom functor, not a new whole natural comparison in x.

Five definitions in two new owners add no primitive, rule, unifier or edit
to earlier LP owners. Two reviewers contain seven passing assertions;
an existing H-family consumer also passes with the new owner imported.
Complete warning inventories and raw blocks match import-only controls
at 1,157/159 and 1,255/169 critical-pair/pattern reports. The
[model/reifier subplan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
records exact logs and the outgoing-column typed-introduction diagnostic.
Strict affected-owner audits, catalog and source TOC pass; source-only
health metrics cover 1,193 files. No TypeScript implementation changed.

Next NUH-5B2c2 derives the column incoming-arrow observation, compares
the actual column input with the original raw input, and composes these
comparisons with the retained/direct input equivalence. Retained TypeScript
observations, nonsplit adoption, snake comparison and final qualification
remain required. NUH-5B2 is not complete.

### NUH-5B2b: Four raw rows instantiate whole δ and native exactness

**Qualified after 1f89653b (2026-09-14), through the raw whole-window assembly.**
Whole constant chain-zero laws use existing weakening, its composition law
and whole initial/terminal uniqueness. The original three raw row-map
projections have whole comparisons with the same raw morphisms. Together
these derive both native-window middle-column zero inputs from the original
raw agreements. The result retains the literal generic additive projections.

The new raw-row shortness alias is the existing whole P/Q predicate at the
actual constant row. The four-row constructor applies the existing whole δ;
three further definitions apply the same native exactness theorems at the
same assembled inputs. Row shortness and normality remain supplied model
contracts. No output exactness, representative, cover, splitting or additional
coherence proof is supplied. Twelve definitions add no primitive.

An initial proof-time constant-evaluation view solved the immediate row
projection but failed under the nested zero-family parents. Its replacement
is two runtime folds at the existing evaluation owner: whole constant
evaluation and its preprojected Hom companion. A full source overlay checks
their owning position and both reduction orders. The remaining guarded
postcomposition view is proof-time only and retains the same functor and
identity second component. Its canonical-head and actual raw-row consumers
pass; removing the view rejects the positive query. Unchanged generic
represented-parent facade typing is not claimed as a new qualified boundary.

The changed evaluation owner, seven new owners and four reviewers pass.
Sixteen new assertions include 13 positives and three rejection controls;
five affected existing consumers also pass. Complete owner/reviewer warning
inventories match (1,150/157; 1,150/157; 1,280/169; 1,490/169 critical-pair/
pattern reports). The original evaluation owner has no warning-body, head
or rule-family delta. The subplan records the full logs and warning JSON.
Affected strict LHS audits, catalog and source TOC pass; source-only health
metrics cover 1,189 files. No TypeScript implementation changed.

Next NUH-5B2c compares the derived column inputs with the original raw
homology inputs, then retains the original H through the proved categorical
input equivalences. Native raw-window H endpoints are already retained;
the final retained-CAS observation interface, TypeScript migration, nonsplit
end-to-end consumer, later adoption and snake comparison remain required.

### NUH-5B2a: Retained/direct input equivalence and native raw-row families

**Qualified after c10b82d3 (2026-09-14), through input comparison and raw rows.**
Existing reconstruction and ordinary diagram reflection derive the whole
J(A)⇒d comparison between the retained inverse-mate input and direct raw
input. A whole fibre inclusion into the original zero-cone category maps
that fibre path to a categorical equivalence, using existing
`OmegaEquivAlong`. Both base components are identities and the fibre cell
is retained. The zero-cone inclusion's scope is ordinary C; no general
higher-duality repair or foundational replacement is introduced.

The Freyd adapter applies original whole H to the same input comparison;
its inverse is the image of the selected input inverse. Neither endpoint
is cast or reselected. The legacy W/presentation data is confined to that
comparison adapter. Independent raw-row families and maps use the existing
native raw constructors and constant-family action, with no K/Q or extra
coherence premise. All three original raw map components and both parameter
actions are retained. Thirteen definitions in five owners add no primitive,
rewrite, unifier or earlier LP edit. Three focused reviewers contain 19
assertions.

All five owners and three reviewers pass. Complete warning inventories and
raw warning blocks equal their import-only controls: 1,157/159 for the fibre
inclusion, 1,296/169 for the retained-model comparison, and 1,291/169 for raw
rows (critical pairs/pattern reports). The subplan records exact logs and
the comparison JSON. Catalog and source TOC pass; source-only health metrics
cover 1,178 registered files. No TypeScript implementation changed.

Next NUH-5B2b assembles four original rows/maps, derives whole chain-zero
inputs from raw agreements and compares the window's derived column inputs
at the retained H. The present input equivalence covers the same outgoing
diagram, not that whole column assembly. Native row shortness remains an
explicit model contract. TypeScript observations, the nonsplit end-to-end
consumer, later adoption, snake comparison and final qualification remain.

### NUH-5B1: Native model and whole connecting/exactness observations

**Qualified after 4c5e55ab (2026-09-14), at the native whole-model interface.**
The [model/reifier subplan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md)
owns the next consumer boundary. `FreydAdjunctionModel` contains the
initial-zero capability and whole P/Q, with H delegated directly to the
native owner. Separate `FreydAdjunctionModelNormality` refers to the actual
whole Coim⇒Im. The old model adapts into these same P/Q with identical
whole H and original input/point/Hom observations.

The whole connecting and three exactness operations specialize their
existing owners. Their remaining dependent telescope is inferred from the
original whole interface, preserving every row, H endpoint, comparison and
selected inverse. No pointwise coherence proof is added. Twelve definitions
in five owners introduce no primitive, rewrite, unifier or earlier LP edit.
Two reviewers contain 15 assertions, including retained whole Hom action
and a changed-kernel rejection control.

All five owners and both reviewers pass under the unchanged guard. Complete
warning inventories and raw warning blocks equal their import-only controls:
1,263 critical pairs / 169 pattern reports for the model adapter and
1,490 / 169 for the whole window. The subplan records exact logs. Catalog
and source TOC checks pass; source-only health metrics cover 1,170 files.

The first redundant combined-package wrapper exhausted the memory guard.
The native normality type alone checked. Keeping its literal generic
additive projections makes the whole δ specialization check without new
comparison rules. Removing an unnecessary ordinary-record import from the
model core also brings the combined exactness consumer within the original
guard. The native model needs no new combined Abelian package wrapper.

Next NUH-5B2 must assemble the original concrete raw window and migrate
TypeScript observations to these actual whole owners. Native normality
remains explicitly supplied; its derivation from old pointwise normality
is not asserted. Retained nonsplit observations, later assumption adoption,
snake/native comparison and final goal qualification remain required.

### NUH-5A: Supported model/reifier preparation

**Qualified after 69bf3577 (2026-09-14), at preparation/replay only.**
Follow the [model/reifier subplan](TYPESCRIPT_EMDASH_NATIVE_MODEL_REIFIER_PLAN.md).
The new [rational context preparation](../src/v3_2/algebra_formal_freyd_rational_model_context.ts)
automates coefficient names, generator/model/normality references, all
existing inventories and the immutable environment for one retained result.
An issued immutable registration records explicitly supplied coefficient,
coherent-model and normality contracts. The coefficient inventory seals
before the environment is built. Preparation does not adopt any claim,
construct a closed model, or reselect a universal object.

The existing nonsplit consumer now uses the helper. Four focused tests pass:
no reselection/adoption during preparation, agreement with the independent
manual preparation interfaces, deterministic and scoped names, typed model
inputs, unsupported/forged/sealed-input rejection, and actual retained
nonsplit replay without adoption. The test and shared fixture use their exact
defining imports instead of the whole workbench barrel. No public barrel,
Core checker or mathematical signature is changed.

Localized TypeScript compilation and ESLint pass, together with all four
focused runtime tests and six generated Lambdapi input-reference checks.
The subplan records exact local evidence. The generated probe checks typed
inputs; it does not discharge the supplied semantic contracts.

The original full observation baseline hits the resource guard. A compiled
instrumented copy locates the delay after whole adoption and before
selected-homology adoption finishes; preparation itself is about one second.
Explicit Node heaps, localized compilation and runtime separation keep the
new checks within the unchanged bounds. The complete later adoption case
remains open and must not be described as green. The existing concrete
connecting observation still uses the older component interface; NUH-5B
must connect it to the new whole δ and exactness owners before NUH-5 is
complete. The subplan records these distinct remaining obligations.

Terminology clarification (2026-09-14): δ is the whole internal connecting
transformation H_C⇒H_A in Functor_cat(B,C). Its components are observations
of that single term. “Direct” describes its construction by the original
K/Q universal descents without a snake-lemma input; it does not mean a
componentwise reconstruction. Prefer “whole connecting transformation δ”
in progress reports.

### NUH-4C6e2c: Both positions adjacent to the whole connecting transformation

**Qualified after 8403cfa0 (2026-09-14).**
The actual Im(H(p))⇒K(δ) and Im(δ)⇒K(H(i)) comparisons have derived
inverses. Together with the middle result, all three recurring native-window
positions are exact in the stated ordinary setting. Sixty-one definitions
in six new owners add no primitive, runtime rewrite, unifier or change to
an earlier LP owner. Original H, δ, K/Q, normality and cover choices remain
the actual terms.

**Source of δ.**

- [Representatives](../emdash2/emdash3_2_one_cat_connecting_source_representatives.lp)
  cover the actual K(δ) through the original ρ:L⇒H_C. Its proved zero
  cokernel supplies the cospan cover. Original δρ=θ makes the induced
  left cycle have zero H_A class; the original boundary representative
  program supplies a second cover and a left boundary representative.
- [Corrected middle cycles](../emdash2/emdash3_2_one_cat_connecting_source_cycles.lp)
  subtract that representative's incoming-row image from the original
  middle lift. Native row/kernel reconstruction proves equality of their
  differentials, so whole difference gives a cycle. Original K lifts it
  into the original upper middle cycle object. The difference unit law
  preserves its outgoing projection.
- [Source exactness](../emdash2/emdash3_2_one_cat_connecting_source_exactness.lp)
  uses original cycle and quotient naturality to reconstruct the covered
  class through H(p). Original kernel cancellation gives β_source(pre)=R
  for the composite of the two covers. The original quotient kills that
  boundary; cover cancellation forces the actual quotient zero. The
  existing criterion certifies the original Im(H(p))⇒K(δ) comparison.

**Target of δ.**

- [Representatives](../emdash2/emdash3_2_one_cat_connecting_target_representatives.lp)
  cover the actual K(H(i)) through the original q_A. The induced middle
  cycle has zero class by the original H(i) quotient law and kernel
  condition. Its original boundary quotient gives the second cover and
  a middle boundary representative.
- [Lift into the original L](../emdash2/emdash3_2_one_cat_connecting_target_lifts.lp)
  derives annihilation by the original precomposed differential, then
  applies the original K mate. Incoming-row and kernel cancellation
  identify its covered left cycle with the first representative. The
  original ρ supplies the right class, and δρ=θ reconstructs the covered
  original left class.
- [Target exactness](../emdash2/emdash3_2_one_cat_connecting_target_exactness.lp)
  identifies the actual boundary on that preimage with the two-cover
  composite. Original Q annihilation and cover cancellation prove the
  actual target boundary quotient zero. The same inverse criterion gives
  OmegaEquivAlong on the original Im(δ)⇒K(H(i)) comparison.

No pointwise representative selection or caller naturality/functoriality
square is introduced. All constructions and reconstruction equations are
whole internal maps over B. The existing structural/profile assumptions and
ordinary OneCat boundary remain explicit.

**Experiments.** The resumed whole-δ baseline passes at `134151`. Source
representatives pass at `142144`. The first source-cycle probe found the
missing owning import for `zero_cone_middle_column_outgoing_func`; adding
the existing row-homology-map dependency makes it pass at `142640`.
Source exactness passes at `143033`. Target representatives, original-L
lifting and target exactness pass at `143548`, `143929` and `144305`.
No new rule, checker patch or enlarged resource limit was needed.

**Qualification.** All six owners and three reviewers pass warning-enabled
resource-guarded `scripts/probe.sh` checks. Nineteen assertions (17 positive,
2 negative) cover whole and component preimage reconstruction, the actual
boundary-quotient zeros, retained forward maps, both inverse laws, and
rejection of unrelated comparison maps. The combined reviewer checks the
whole δ type and δρ=θ, then all three original comparison witnesses on
one and the same native window.

- `emdash3_2_one_cat_connecting_source_representatives.lp`: `emdash3_2_one_cat_connecting_source_representatives-20260914-145058.log`.
- `emdash3_2_one_cat_connecting_source_cycles.lp`: `emdash3_2_one_cat_connecting_source_cycles-20260914-145115.log`.
- `emdash3_2_one_cat_connecting_source_exactness.lp`: `emdash3_2_one_cat_connecting_source_exactness-20260914-145131.log`.
- `emdash3_2_one_cat_connecting_target_representatives.lp`: `emdash3_2_one_cat_connecting_target_representatives-20260914-145148.log`.
- `emdash3_2_one_cat_connecting_target_lifts.lp`: `emdash3_2_one_cat_connecting_target_lifts-20260914-145207.log`.
- `emdash3_2_one_cat_connecting_target_exactness.lp`: `emdash3_2_one_cat_connecting_target_exactness-20260914-145224.log`.
- `one_cat_connecting_source_exactness.lp`: `one_cat_connecting_source_exactness-20260914-145241.log`.
- `one_cat_connecting_target_exactness.lp`: `one_cat_connecting_target_exactness-20260914-145300.log`.
- `one_cat_native_homology_window_exactness.lp`: `one_cat_native_homology_window_exactness-20260914-145319.log`.

The retained join with the existing middle-exactness and whole-connecting
reviewers passes at `145727`. Seven exact original dependency-load-order
baselines pass at `145747`–`145928`. All ten complete warning inventories
match: 1,484 critical-pair and 169 pattern warnings, including locations,
heads, rule families and parser issues. No new warning is introduced.

The nine checked library/reviewer hashes match the final files; all 61
new definition names and six registry entries are unique. Source-only
health covers 1,163 files, with snapshot
`f9c26037656458a8a91068649efe93b9abbf5dbbeae9ee842a4fea0823dc059d`.
Strict catalog, report-header, active-reference and shell checks pass;
the central diagnostic catalog is unchanged. Only localized serial
Lambdapi checks ran under the existing 90-second/2-GiB guard. No repository
aggregate, TypeScript execution, model/CAS replay or Op/profile migration
was run. The TypeScript work this turn was read-only recovery/inventory.

**Next NUH-5: retained supported model/reifier preparation.** Inventory the
current nonsplit proof–CAS consumer and its actual model contracts. Remove
repeated manual coefficient-name, environment, model-reference and
observation-inventory construction for supported backends. Preserve original
whole H/δ and exactness selections; distinguish computed equations from
supplied universal-provider, normality and whole-model semantics. A reusable
explicitly trusted backend contract is allowed by the master plan; do not
relabel it as a closed derived correctness theorem. The snake/direct/native
comparison, sign/endpoint checks and final qualification remain required.

Initial read-only inventory locates
[prepareAlgebraFormalFreydLongExactHomology](../src/v3_2/algebra_formal_freyd_long_exact_homology.ts),
[retained model observations](../src/v3_2/algebra_formal_freyd_model_observation.ts),
and [model connecting observations](../src/v3_2/algebra_formal_freyd_model_connecting_observation.ts).
The latter two explicitly classify adopted agreement as trusted presentation
semantics; the homology preparation reuses the selected provider and
reconstruction bundles. Start from these active consumers and their focused
tests, under the TypeScript handoff, before selecting a supported model
registration/preparation change. No TypeScript implementation or execution
has occurred in this tranche.

### NUH-4C6e2b2: Whole additive units and middle exactness

**Qualified after 1a64449f (2026-09-14).**
The actual Im(H(i))⇒K(H(p)) comparison has a derived inverse, including
the original native-window middle instance. Twenty-eight definitions in
five new owners and six proof-time comparisons in the existing product
reindexing owner add no primitive or runtime rewrite. Original K/Q, H,
diagrams, normality inverse and cover projections remain fixed.

**Native computation and ownership.**

- [Product-family reindexing](../emdash2/emdash3_2_product_family_reindex.lp)
  adds raw/native β views for each projection of a literal paired functor,
  plus whole Hom-action comparisons over a literal paired base functor
  when either endpoint is the actual identity on C×C and the other is a
  diagonal composite. Both component
  reindexing functors retain the original family, projection and base map.
  No product η or global naturality/functoriality rule is installed.
- [Biproduct injection restriction](../emdash2/emdash3_2_one_cat_biproduct_injection_reindex.lp)
  stages the original whole mate input and preserves its identity target.
  Whole identity/zero preservation and original terminal/initial uniqueness
  compare its native and local presentations. Its restriction is the
  existing product pairing ⟨id,0⟩.
- [Coproduct injection paths](../emdash2/emdash3_2_one_cat_copair_injection_paths.lp)
  keep the original whole unit and diagonal Hom action as finite pairs of
  whole maps. The native mate formula and inverse cut give [f,g]∘ι₁=f.
  This uses whole categorical structure, not componentwise equality assembly.
- [Whole additive units](../emdash2/emdash3_2_one_cat_additive_family_units.lp)
  derive f+0=f from that injection law and existing pairing/copairing
  composition. Whole negation gives −0=0, then f−0=f. If h∘g=0,
  whole bilinearity gives h∘(f−g)=h∘f.
- [Middle exactness](../emdash2/emdash3_2_one_cat_middle_homology_exactness.lp)
  applies that law to the actual correction: q_Mw=q_Mb. Original kernel
  reconstruction, H(i)'s quotient law and K(i)a=w identify
  β_H(q_Aa)=r₁r₂r₃. The original quotient kills β_H. Three original cover
  cancellations therefore prove q_β_H=0; the existing inverse criterion
  yields OmegaEquivAlong on the actual Im(H(i))⇒K(H(p)) map.
- [Native middle instance](../emdash2/emdash3_2_one_cat_native_middle_homology_exactness.lp)
  retains the literal original upper row-triple diagram, avoiding the
  previously diagnosed expensive endpoint-alias expansion.

**Experiments.** The initial restriction probe at `124039` exposed native
projection/action comparisons at an identity endpoint. Keeping literal
restricted endpoint annotations and staging whole input comparisons
resolved the intermediate typing failures; original terminal/initial
uniqueness resolved the zero presentation. The complete injection probe
passes at `125144`. Whole unit/diagonal pairs and an explicit intermediate
composition presentation make the coproduct law pass at `125754`.
The additive unit laws pass at `125958`, middle exactness at `130325`,
and the native-window instance at `130600`.

A first ablation generator incorrectly stopped at semicolons inside the
constraint list; those parser failures are not necessity evidence. The
corrected parser preserves complete rule clauses and its unchanged-copy
control passes at `130910`. Valid deletion probes retain the four raw/
native projection views and two identity-endpoint Hom views, with actual
typing failures. Removing the extra diagonal-associativity view passes
at `130949`; it is not promoted. The full native-window probe with the
six retained views passes at `131054`.

The first broader reviewer used an opaque U:A⇒C×C. Its Hom-comparison
type could not align the opaque functor's projections with composition
by the two product projections; the four literal-pair projection checks
pass separately at `132046`. Rather than introducing general product η,
the two new Hom views are scoped to the literal paired base maps used by
the program. The reviewer still varies the original family F arbitrarily
and retains both whole Hom actions; it passes at `132407`. This is an
explicit computational presentation boundary, not a mathematical
counterexample or a restriction on the original LES inputs. No checker
patch, resource-limit increase or new mathematical assumption was used.

The first complete warning comparison isolates eight replaceable-pattern
warnings in the four projection views: their captured C/D parameters are
unused on the right. A full-owner probe replaces those inferred slots by
`_` and its focused reviewer passes at `133024`. The same cleanup is
installed in the existing owner; the two guarded Hom rules retain their
actual category, paired-base and identity discriminators. The warning
comparison found no new critical-pair warnings.

**Qualification.** The changed reindexing owner, five new owners, three
reviewers and retained-consumer join pass warning-enabled resource-guarded
`scripts/probe.sh` checks. Eighteen assertions (15 positive, 3 negative)
cover raw/native product projections, both identity-endpoint Hom actions
for an arbitrary original family over paired bases, whole additive units,
annihilated-correction preservation, the derived actual boundary quotient
zero, the original comparison's forward projection and both inverse laws,
and the native-window specialization. Rejection checks retain the original
coordinate, result and comparison map.

- `emdash3_2_product_family_reindex.lp`: `emdash3_2_product_family_reindex-20260914-133151.log`.
- `emdash3_2_one_cat_biproduct_injection_reindex.lp`: `emdash3_2_one_cat_biproduct_injection_reindex-20260914-133155.log`.
- `emdash3_2_one_cat_copair_injection_paths.lp`: `emdash3_2_one_cat_copair_injection_paths-20260914-133201.log`.
- `emdash3_2_one_cat_additive_family_units.lp`: `emdash3_2_one_cat_additive_family_units-20260914-133209.log`.
- `emdash3_2_one_cat_middle_homology_exactness.lp`: `emdash3_2_one_cat_middle_homology_exactness-20260914-133220.log`.
- `emdash3_2_one_cat_native_middle_homology_exactness.lp`: `emdash3_2_one_cat_native_middle_homology_exactness-20260914-133233.log`.
- `product_identity_family_reindex.lp`: `product_identity_family_reindex-20260914-133248.log`.
- `one_cat_additive_family_units.lp`: `one_cat_additive_family_units-20260914-133253.log`.
- `one_cat_middle_homology_exactness.lp`: `one_cat_middle_homology_exactness-20260914-133304.log`.
- `nuh4c6e4_retained_homology.lp`: `nuh4c6e4_retained_homology-20260914-133321.log`.

Seven exact original import-order baselines were checked before changing
`product_family_reindex`; its original bytes and hash are retained in the
ignored experiment evidence. The final ten complete inventories match those
original baselines, including categories, locations, heads, rule families
and parser issues. The owner/reindex reviewer preserve 1,151 critical-pair /
157 pattern warnings; injection/copair preserve 1,278 / 169; addition and
its reviewer preserve 1,482 / 169; middle/window and retained consumers
preserve 1,484 / 169. The temporary eight pattern warnings are eliminated.

All ten checked source hashes match, the 28 new definition names and five
new registry entries are unique, and source-only health covers 1,154 files
with snapshot
`a3c48688715e9a78639cd737225f1f12d10d1781aaaa61b4f5631dc355881b82`.
Strict catalog, LHS, report-header, active-reference and shell checks pass.
The central diagnostic catalog is unchanged. Only localized serial Lambdapi
checks ran, each under the existing 90-second/2-GiB guard. No repository
aggregate, TypeScript check, model/CAS run or Op/profile migration was run.

**Next C6e2c: the two positions adjacent to δ.** Derive zero of the actual
boundary quotient for H(p) followed by δ, and for δ followed by H(i),
using the original window, whole representative programs, original
δ∘ρ=θ reconstruction and native universal operations. Apply the same
inverse criterion to their original comparison maps. Model/reifier
automation, snake/direct comparison and final qualification remain later;
middle exactness does not complete the long exact sequence or the goal.


### NUH-4C6e2b1: Whole representative covers for the LES boundary proofs

**Qualified after 6bf3785d (2026-09-14).**
Six one-way owners contain 56 definitions, with no new primitive, runtime
rewrite, unifier or change to an earlier LP owner. They derive representative
covers and lift the corrected middle cycle into the original left cycle
object. They do not yet prove the middle boundary quotient is zero or
certify any of the three LES output comparisons as invertible.

**Whole construction and retained choices.**

- [Cospan kernel covers](../emdash2/emdash3_2_one_cat_cospan_kernel_covers.lp)
  use the original K of Δ=fπ₁−gπ₂ for f:X⇒Z and g:Y⇒Z. Its original
  projections r,s satisfy fr=gs. A proved zero actual cokernel of g gives
  the cover of r by auxiliary difference descent and original injections.
  The equivalence is on the original Coim(r)⇒X factor; r is not asserted
  invertible. Whole cancellation uses that factor's selected inverse.
- [Quotient cokernel zero](../emdash2/emdash3_2_one_cat_quotient_cokernel_zero.lp)
  derives the required premise for an original quotient q_D: its actual
  cokernel projection is zero by original Q annihilation and cancellation.
  This does not say q_D itself is zero.
- [Homology representatives](../emdash2/emdash3_2_one_cat_homology_representatives.lp)
  apply that cospan program to v:X⇒H and the original homology quotient.
  The derived cover r:R⇒X and whole cycle representative b retain
  v∘r=q_H∘b. The caller supplies v, not a representative or cover.
- [Boundary representatives](../emdash2/emdash3_2_one_cat_boundary_representatives.lp)
  lift a cycle v with q_H∘v=0 into the original image. The original
  normality inverse gives its coimage lift; the original coimage quotient
  gives a derived cover r and boundary representative b with β∘b=v∘r.
- [Middle representatives](../emdash2/emdash3_2_one_cat_middle_homology_representatives.lp)
  apply those constructions to the actual K(H(p)), then lift the right
  boundary through the original previous short-exact row. Three retained
  projections give a covered middle cycle b and original boundary β_M∘b₀.
  Their induced right cycles agree. Whole difference produces
  w=b−β_M∘b₀ with K(p)∘w=0.
- [Middle cycle lift](../emdash2/emdash3_2_one_cat_middle_homology_cycles.lp)
  uses the original middle-row inverse mate to lift κ_M∘w into A₁.
  Original lower-row cancellation proves it is a left cycle. The original
  K mate then gives a:R₃⇒K_A, and original kernel cancellation proves
  K(i)∘a=w. All three cover-cancellation instances are derived from the
  original row and quotient data, with no extra cover assumption.

The successful full representative probe is `121550`; the resumed baseline
is `122414`. The added left-cycle lift and all three cover-cancellation
instances pass the full probe at `122833`. A reviewer-generator variable
name was corrected before any reviewer check; this was not an LP or theory
failure. No resource limit was raised and no checker patch was used.

**Qualification.** Six owners and three reviewers pass the resource-guarded,
warning-enabled `scripts/probe.sh` checks, with 15 assertions (13 positive,
2 negative). The observations cover original projection computation,
component cospan compatibility, fixed-forward cover evidence, retained
normality inverse, whole representative reconstruction, the actual
K(i)∘a=w comparison and component observation, typed generic Hom action,
and all three derived cover cancellations. Negative assertions reject
substituting an unrelated forward map or representative equation.

- `emdash3_2_one_cat_cospan_kernel_covers.lp`: `emdash3_2_one_cat_cospan_kernel_covers-20260914-123139.log`.
- `emdash3_2_one_cat_quotient_cokernel_zero.lp`: `emdash3_2_one_cat_quotient_cokernel_zero-20260914-123147.log`.
- `emdash3_2_one_cat_homology_representatives.lp`: `emdash3_2_one_cat_homology_representatives-20260914-123153.log`.
- `emdash3_2_one_cat_boundary_representatives.lp`: `emdash3_2_one_cat_boundary_representatives-20260914-123207.log`.
- `emdash3_2_one_cat_middle_homology_representatives.lp`: `emdash3_2_one_cat_middle_homology_representatives-20260914-123220.log`.
- `emdash3_2_one_cat_middle_homology_cycles.lp`: `emdash3_2_one_cat_middle_homology_cycles-20260914-123232.log`.
- `one_cat_cospan_kernel_covers.lp`: `one_cat_cospan_kernel_covers-20260914-123245.log`.
- `one_cat_homology_representatives.lp`: `one_cat_homology_representatives-20260914-123255.log`.
- `one_cat_middle_homology_cycles.lp`: `one_cat_middle_homology_cycles-20260914-123309.log`.

The retained join with the existing native-window exactness-input and
comparison-inverse reviewers passes at `123335`. Six exact original
dependency-load-order baselines pass at `123348`–`123448`. Every complete
warning inventory matches, including categories, locations, term heads,
rule families and parser issues: 1,484 critical-pair / 169 pattern warnings
throughout, except the smaller quotient-zero owner at 1,381 / 159. These
are inherited inventories, not new warnings.

All nine checked source hashes match the final files; the 56 definition
names and six registry entries are unique. Source-only health covers 1,146
files, with snapshot
`a25a6041e852cf8cf26e050d2843b6e03325104d9d174a0e1876d3261f088ee0`.
Strict catalog, report-header and active-reference checks pass; the central
diagnostic catalog is unchanged. Only affected serial Lambdapi targets were
checked under the existing 90-second/2-GiB guard. No repository aggregate,
TypeScript check, Op/profile experiment or model/CAS run was performed.

**Next C6e2b2: preserve the homology class and finish the middle proof.**
Derive the whole additive unit/difference law needed for
q_M∘(b−β_M∘b₀)=q_M∘b from the original native product/coproduct mates.
The library does not yet provide this whole unit law or a complete
PreadditiveCategory(Functor_cat(B,C)); neither may be silently assumed.
Do not assemble a transformation equality from component equations.
Then compare the original boundary into K(H(p)) on q_A∘a with the
composite of the three original covers. Original Q annihilation and those
cover cancellations must prove the actual boundary quotient zero. Apply
the existing inverse criterion only to that derived proof.

Specialization to the original native window, the other two output positions,
model/reifier automation, snake comparison and final qualification remain
required. No splitting, representative, cover or output exactness witness
has become a new caller assumption.

### NUH-4C6e2a: Comparison kernels and inverses from the original boundary quotient

**Qualified after 02d39d88 (2026-09-14).**
The original comparison e:Im(f)⇒K(g) satisfies κ_g∘e=ι_f and has zero
kernel inclusion. All three actual native-window comparisons now have this
zero-kernel result. An inverse of e is constructed once the original
quotient of β:A⇒K(g) is proved zero. The original short-exact row provides
a derived instance, using its existing fixed-forward β equivalence.

Seventeen definitions across five one-way owners introduce no primitive,
runtime rewrite, unifier or edit to earlier LP sources. Original universal
objects, maps, diagrams and inverse choices remain fixed. The three LES
boundary-quotient zero proofs are still outstanding; this conditional
criterion is not an output exactness assumption or completion claim.

**Construction and ownership.**

- [Original cokernel of zero](../emdash2/emdash3_2_one_cat_zero_cokernel_families.lp)
  descends id through the original Q. Its reconstruction and original
  quotient cancellation give both inverse laws for the same retraction.
- [Inverse from universal zeros](../emdash2/emdash3_2_one_cat_inverse_from_universal_zeros.lp)
  keeps the original kernel-arrow diagram. Whole terminal/initial uniqueness
  presents κ=0 at that same diagram; its original Q projection is invertible.
  The existing zero-cokernel cover and original normality make φ invertible.
  Their composite reconstructs the actual differential, giving its inverse.
- [Comparison inclusion paths](../emdash2/emdash3_2_one_cat_image_kernel_inclusion_paths.lp)
  use original native mate projection to obtain β̄q_κ=β. Original quotient
  cancellation identifies κ_gβ̄ with φ_f. Original normality then gives
  κ_g e=ι_f. Applying the original image-kernel cancellation to K(e) proves
  that the actual κ_e is zero.
- [Comparison inverse criterion](../emdash2/emdash3_2_one_cat_image_kernel_exactness.lp)
  uses a proved zero original boundary quotient to cancel β. Since q_e e=0,
  the existing factorization through e gives q_eβ=0, hence q_e=0. The two
  original universal zeros now construct fixed-forward OmegaEquivAlong(e).
  The original short-exact row derives the boundary-zero premise from its
  β equivalence; it does not supply a separate exactness witness.
- [Native comparison kernels](../emdash2/emdash3_2_one_cat_native_exact_comparison_kernels.lp)
  instantiate the zero-kernel theorem at the original source, middle and
  target comparison maps of the existing native window.

**Experiments and resource boundary.** Missing owning imports were added
before the complete criterion checked. A generator wrapped a long line
comment without continuing `//`; a guarded parser-only check isolated that
syntax error, and comment preservation fixed it. This was not a theory
change. The combined window probe then reached the 2 GiB guard. Isolating
positions showed that source and target passed, while the middle failed.
The middle specialization had rebuilt the row-triple outgoing diagram with
a native-window endpoint alias. Retaining the literal original row-triple
diagram makes the middle check pass (`113259`) and the combined file pass
(`113455`). No object cast, new comparison rule or raised resource limit
was used. The earlier guarded failure logs at `112802` and `113044` remain
recovery evidence.

**Qualification.** All five owners and three reviewer files pass serial,
warning-enabled, resource-guarded checks within the 90-second per-target
ceiling. The 12 assertions comprise ten positive observations and two
unrelated-map rejection controls. They retain the original Q retraction,
both inverse laws, the actual comparison forward map, an original
short-exact-row instance and the component observations of all three
native-window zero-kernel results.

Final owner logs span `113953`–`114028`. Reviewer logs are
`one_cat_zero_cokernel_families-20260914-114042.log`,
`one_cat_image_kernel_exactness-20260914-114048.log` and
`one_cat_native_exact_comparison_kernels-20260914-114059.log`.
The existing native-window zero-input and connecting reviewers still pass
after the new comparison-kernel owner, at
`nuh4c6e2_retained_homology-20260914-114312.log`.
Six original dependency-load-order baselines pass at `114329`–`114422`.
All nine final warning inventories exactly match their corresponding
baselines in categories, locations, term heads, rule families and parser
issues. Exact logs and checked source hashes are retained in
`tmp/probes/nuh4c6e2_warning_comparison.json`.

Strict catalog, report-header/reference lint, shell syntax, unique
symbols, exact owner registration, added local links and diff hygiene pass.
All 17 symbols are definitions; no new primitive or rule requires a new
LHS audit. The generated source-only health report records 1,137 files and
snapshot `a7e65c5a64709499bb7ca1070fe5aee4ca36f3a29d1cd8d2bb287a91b56ffadb`.
No repository-wide, TypeScript or aggregate typecheck was run. These checks
qualify the stated zero-kernel results and conditional inverse criterion;
they do not prove the remaining LES boundary-quotient zeros or infer
concrete model closure or deferred Op/profile qualification.

**Next C6e2b: derive the LES boundary-quotient zeros.** At each output
position, prove that the original quotient of the actual boundary into the
original kernel is zero, using the original short-exact window, native K/Q,
whole reconstruction and derived covers. Feed these derived zeros to the
new inverse criterion at the original comparison. Do not supply those
zeros as new input assumptions or rename the conditional theorem as a
completed LES exactness theorem. Model/reifier automation, snake/direct/
native comparison and final qualification remain required; all agreed
Op/profile and endpoint-debugging deferrals remain in force.

### NUH-4C6e1: Adjacent whole homology maps and all three zero pairs

**Qualified after ff37f33d (2026-09-14).**
The native window now has whole H(i) and H(p), their original quotient
characterizations, and the three zero composites

```text
H(p)∘H(i)=0,       δ∘H(p)=0,       H(i)∘δ=0.
```

The existing actual Im⇒K comparisons are formed for the middle, source-of-δ
and target-of-δ positions. These are maps, not exactness inhabitants; their
invertibility remains unproved. Original H choices, δ, row data and K/Q
structures are retained. The tranche adds 52 definitions and two guarded
proof-time unit views, with no new primitive, runtime rewrite or earlier
LP edit.

**Construction and ownership.**

- [Arrow-family maps](../emdash2/emdash3_2_one_cat_arrow_family_maps.lp)
  realize a whole square through the existing native arrow category in
  Functor_cat(B,C), then exchange the parameter and shape axes. Both whole
  endpoint maps compute. This introduces no new square carrier.
- [K/Q family maps](../emdash2/emdash3_2_one_cat_kernel_cokernel_family_maps.lp)
  retain the original functor actions. Their inclusion/projection laws are
  derived through native mate naturality, inverse cuts and shape evaluation.
- [Whole H family maps](../emdash2/emdash3_2_one_cat_homology_family_maps.lp)
  use original kernel cancellation and boundary reconstruction to obtain
  the boundary-diagram map, then apply the original Q action. Whole quotient
  naturality characterizes the induced cycle map. No ordinary universal
  provider dictionary or caller pointwise naturality field is used.
- [Middle-column input](../emdash2/emdash3_2_one_cat_middle_column_inputs.lp)
  forms its actual diagram and native input from the original whole middle
  chain law before selecting any K/Q. Its H then uses the original program.
- [Row homology maps](../emdash2/emdash3_2_one_cat_row_homology_maps.lp)
  derive both required commuting relations from the existing whole row
  transformations and generic naturality. Their cycle and quotient
  observations retain the original inclusions/projections.
- [Middle zero pair](../emdash2/emdash3_2_one_cat_row_homology_zero_pairs.lp)
  uses the original zero row, kernel cancellation and quotient cancellation
  to prove H(p)H(i)=0 and form its native input and actual comparison.
- [Covered middle cycles](../emdash2/emdash3_2_one_cat_covered_middle_cycles.lp)
  prove θs=0 whenever the original covered middle differential is zero.
  Original incoming/kernel cancellation supplies the argument.
- [δ after H(p)](../emdash2/emdash3_2_one_cat_native_connecting_projection_zero.lp)
  lifts the original middle kernel inclusion into the existing L. Its
  r-image is the actual induced right cycle map, and θ kills it. The
  existing γ/δ reconstruction and original quotient cancellation yield
  δH(p)=0.
- [H(i) after δ](../emdash2/emdash3_2_one_cat_native_connecting_inclusion_zero.lp)
  identifies the induced covered left cycle with the original middle
  boundary. The original quotient kills that boundary; δρ=θ and the
  existing categorical cover cancellation yield H(i)δ=0.
- [Native-window exactness inputs](../emdash2/emdash3_2_one_cat_native_homology_window_exact_inputs.lp)
  expose the two middle H functors and adjacent maps at the original native
  H_C/H_A endpoints. The proved zeros form the native inputs, and the
  original comparison owner supplies all three actual Im⇒K maps. No output
  exactness or inverse is assumed.

**Action observations and unit views.** The first direct K/Q naturality
observation stopped at native shape evaluation versus postcomposition by
evaluation. A broad equality of those evaluation functors did not check
(`nuh4c6e1_eval_views-20260914-100403.log`) and is not introduced. Instead,
existing native untranspose/transpose naturality supplies the required
whole action laws, followed by the existing shape evaluator.

Mixed native/raw presentations of the same intermediate functor prevented
the old runtime unit patterns from matching. The
[unit views](../emdash2/emdash3_2_functor_category_unit_views.lp) apply those
same unit laws proof-time in the existing functor category, comparing the
identity classifier, both relevant endpoints and the original arrow.
They do not remove or reorient the runtime rules at core lines 5659/5662.
The unit comparison must be staged as an equality before applying the mate
functor: burying it inside fapp0 does not make unification transitive.
Removing both views fails the K consumer
(`nuh4c6e1_kq_no_units-20260914-103518.log`); retaining only the right view
fails the Q consumer (`nuh4c6e1_kq_right_unit_only-20260914-104542.log`).
Both views therefore have concrete consumers. The direct evaluation
comparison remains an unpromoted experiment, not a new categorical premise.

The initial wrong-endpoint/classifier negative fixtures put an ill-typed
composition inside the expected equality type, so the checker rejected that
type before evaluating the negative assertion. The corrected fixtures check
the bad term against a well-formed Hom type. All six arrow/endpoint/classifier
rejection controls pass; no theory change was made for that fixture repair.

**Qualification.** All eleven owners and three reviewer files pass serial,
warning-enabled, resource-guarded checks within the 90-second per-target
ceiling. The 14 assertions comprise eight positive component/Hom-action
observations and six negative arrow/identity-endpoint/classifier controls.
Actual non-definitional unit presentations exercise both new comparisons;
changed data are rejected. H-map quotient equations and both zero composites
involving δ have their original component and whole next-Hom observations.

Final owner logs span `105020`–`105200`. Reviewer logs are
`functor_category_unit_views-20260914-105401.log`,
`one_cat_homology_family_maps-20260914-105409.log` and
`one_cat_native_homology_window_exact_inputs-20260914-105419.log`.
The existing native-window connecting and cover reviewers still pass after
the new exactness-input owner, at
`nuh4c6e1_retained_homology-20260914-105600.log`.
Eleven original dependency-load-order baselines pass at `105617`–`105755`.
All fifteen final warning inventories exactly match their corresponding
baselines in categories, locations, term heads, rule families and parser
issues. Exact logs and checked source hashes are retained in
`tmp/probes/nuh4c6e1_warning_comparison.json`.

Strict LHS audit, strict catalog, report-header/reference lint, shell syntax,
unique declarations, exact registration, added local links and diff hygiene
pass. The source-only health report records 1,129 files and snapshot
`ea0178f42c8560ea6956e98b06e9e13cadc2492fff44dea2da06a91ad619d09b`.
No repository-wide, TypeScript or aggregate typecheck was run. This qualifies
the stated whole maps, zero laws and comparison constructions; it does not
supply the still-required comparison inverses, concrete model closure or
deferred Op/profile qualification.

**Next C6e2: prove output exactness.** Construct inverses of the three actual
comparison maps from the original short-exact data and normality, preserving
their original H, image and kernel objects. The zero composites and formed
comparisons alone do not imply exactness. Continue through native K/Q,
whole reconstruction and derived covers; do not add an exactness capability
as an assumption or switch to ordinary universal-provider dictionaries.
Model/reifier automation, snake/direct/native comparison and final
qualification remain required. Existing Op/profile and endpoint-debugging
deferrals remain in force.

### NUH-4C6d1: Two native descents construct the connecting map

**Qualified after e1182a38 (2026-09-14).**
The direct native δ:H_C⇒H_A now exists at the original native-window
homology functors. Its whole laws are

```text
γr=θ,       δq_C=γ,       δρ=θ,       θκ_ρ=0,
vρ=θ ⇒ v=δ.
```

The previously planned single descent along ρ is proved equal to this
construction as a whole transformation. No judgmental identity between the
two programs is claimed. Twenty-eight definitions in six one-way owners
add no primitive, runtime rewrite, unifier or earlier LP edit. Original
P/Q, L, r, ρ, θ, H_C, H_A and selected inverse choices are retained.

**Construction and owners.**

- [Kernel input boundaries](../emdash2/emdash3_2_one_cat_kernel_input_boundaries.lp)
  compose existing native input recovery and whole boundary reconstruction
  to identify the original kernel boundary with its original input arrow.
- [Kernel-side connecting paths](../emdash2/emdash3_2_one_cat_native_connecting_kernel_paths.lp)
  prove θs=0 whenever rs=0. The original square gives p₀a_Ls=0; the
  original row E0 lifts a_Ls to A0. Whole row naturality and original
  incoming cancellation identify the covered left lift with d_A times that
  row lift. Original kernel cancellation identifies the entire left cycle
  with β_A times the lift, and the original target quotient kills it.
  All equations concern whole maps; no caller naturality square is supplied.
- [Cycles connecting](../emdash2/emdash3_2_one_cat_native_cycles_connecting.lp)
  specializes this to the original K(r), then applies the proved coimage
  cover descent to obtain γ:K(d_C)⇒H_A with γr=θ. Full AdditiveCategory
  and original normality enter here through the existing cover of r; the
  preceding annihilation proof requires only the stated original row/K/Q
  data and ordinary profile.
- [Upper lifts](../emdash2/emdash3_2_one_cat_native_connecting_upper_lifts.lp)
  lift the original upper middle differential into the existing L. The
  original first projection reconstructs it; original kernel cancellation
  proves its r-image is β_Cp_m. The upper middle chain-zero law, original
  incoming cancellation and original kernel cancellation make its θ-image
  zero. No new cover, representative choice or splitting is introduced.
- [Native connecting](../emdash2/emdash3_2_one_cat_native_connecting.lp)
  uses these facts and the original upper-row outgoing cancellation to
  prove γβ_C=0. The original Q at the original boundary diagram then
  constructs δ. Its two reconstruction laws yield δρ=θ and θκ_ρ=0.
  The already derived cover of ρ makes that whole reconstruction determine
  δ uniquely.
- [Native-window connecting](../emdash2/emdash3_2_one_cat_native_homology_window_connecting.lp)
  exposes δ at the existing window and its original source/target homology
  functors. Its whole reconstruction, annihilation and uniqueness use the
  same original ρ and θ. Applying uniqueness to the original single-descent
  program proves agreement between the two native constructions.

**Plan refinement.** Two successive descents use the already available r
cover and q_C quotient directly. This refines the earlier schedule that
first sought θκ_ρ=0 using an additional cover. The required annihilation
and the original single-descent specification are both recovered as
proved consequences. It does not make the snake lemma a prerequisite,
change any H choice, or assume output exactness.

**Observed checker boundary.** All theory-owner probes pass. The initial
combined connecting reviewer hit the 2 GiB guard while checking its final
unconstrained δ=0 rejection query, with exit 134 (minor-GC allocation
failure). Isolating its six queries showed that the first five—including
the original component equation, reconstruction and uniqueness—all pass.
Only the δ=0 query reproduces the guarded failure:
`nuh4c6d1_delta_review_6-20260914-092806.log` (combined failure at `092525`).
That query remains ignored recovery evidence and is not promoted as a
successful negative test. The retained suite checks reconstruction,
components, Hom action and unrelated-map retention. No memory limit was
raised and no additional rewrite or unifier was introduced to force this
optional comparison. Concrete nonzero model tests remain in the model
qualification work; this resource failure is not a mathematical zero claim.

**Qualification.** Six owners and three reviewer files pass serial,
warning-enabled, resource-guarded checks within the 90-second per-target
ceiling. The promoted suite has 16 assertions: 14 positive observations and
two unrelated-map rejection controls. These include the original lift and
boundary comparisons, δq_C=γ, δρ=θ, θκ_ρ=0, whole uniqueness, the component
equation δ_x∘ρ_x=θ_x and whole next-Hom action of the single-descent
comparison. The separate δ=0 resource failure above is excluded from this
passing count.

Final owner logs span `092353`–`092456`. Reviewer logs are
`one_cat_native_connecting_lifts-20260914-092512.log`,
`one_cat_native_connecting-20260914-093008.log` and
`one_cat_native_homology_window_connecting-20260914-093022.log`.
The existing native-window cover and map reviewers still pass when imported
after the new connecting owner, at
`nuh4c6d1_retained_homology-20260914-093743.log`.
Three original dependency-load-order baselines pass at `093758`–`093819`.
All ten final warning inventories exactly match their corresponding
baselines in categories, locations, term heads, rule families and parser
issues. Exact logs and final checked source hashes are retained in
`tmp/probes/nuh4c6d1_warning_comparison.json`.

Strict catalog, report-header/reference lint, shell syntax, exact owner
registration, unique declarations, added local links and diff hygiene pass.
All 28 owner symbols are definitions; no new primitive or rule requires a
new LHS audit. The generated source-only health report records 1,115 files
and snapshot
`2718d87d09096a558493833c42757d4c41e5b911c05bb12cbb606a4e83517351`.
No repository-wide, TypeScript or aggregate typecheck was run. Qualification
is scoped to the stated ordinary whole construction and its original
structural/normality assumptions; model closure and deferred Op/profile
qualification are not inferred from these checks.

**Next C6e: output exactness.** Construct the actual adjacent whole homology
maps and their zero-pair inputs, then prove fixed-forward invertibility of
the existing Im⇒K comparisons at the LES positions. The δ construction
and its uniqueness alone do not provide these exactness inhabitants.
Retain the original H choices and use native K/Q and derived covers;
ordinary per-position records remain derived observations. Model/reifier
automation, snake/direct/native comparison and final qualification remain
required. Op/duality, later strictness-profile integration and the separate
endpoint-debugging experiments remain deferred.

### NUH-4C6c3e2: Original kernel-square and native homology covers

**Qualified after e1a9a07f (2026-09-14).**
The original r:L⇒K(d), L=K(d∘p), and ρ=q_H∘r now have derived
categorical covers. The fixed-forward evidence concerns the existing
Coim(r)⇒K(d) and Coim(ρ)⇒H factors; it does not assert that r or ρ
is itself invertible. Their actual cokernel projections are proved zero.
The existing native window supplies the necessary p evidence from E0.

Thirty-five definitions in seven one-way owners preserve the earlier LP
sources, original diagrams, L, r, ρ, H and selected inverse choices. No
primitive, runtime rewrite, unifier, ordinary universal dictionary or
caller naturality/functoriality square is introduced.

**Construction and ownership.**

- [Coimage cover descent](../emdash2/emdash3_2_one_cat_coimage_cover_descent.lp)
  restricts the original quotient of the original kernel diagram and proves
  φ_D∘q_κ=∂D. Given a whole u with uκ_D=0, it descends through that same
  Q and composes with the selected inverse of the proved φ_D. Whole
  reconstruction gives desc(u)∘∂D=u. The inverse factorization and
  original quotient cancellation also derive cancellation of ∂D. These
  are the generic internal operations later needed for δ.
- [Difference cover closure](../emdash2/emdash3_2_one_cat_difference_cover_closure.lp)
  derives the auxiliary difference cover when the actual second leg p has
  zero cokernel. Its proof uses the preceding categorical cancellation,
  without an IsEpic dictionary. A separate definition derives this premise
  from the original whole OneCatShortExactFamily.
- [Auxiliary kernel lifts](../emdash2/emdash3_2_one_cat_kernel_difference_lifts.lp)
  introduce D′=κ_d∘π₁−p∘π₂. Its original K(D′) projects to K(d) and M;
  whole difference-zero reflection supplies their compatibility. Native
  kernel lifting sends the second projection into the existing L=K(d∘p).
  Its original first projection reconstructs that input; original kernel
  cancellation proves r∘lift equals the first auxiliary projection. No
  replacement pullback object, ordinary cone record or slice dictionary
  enters this construction.
- [Difference factor paths](../emdash2/emdash3_2_one_cat_difference_factor_paths.lp)
  prove ψ∘D′=a∘π₁ ⇒ ψ∘p=0 by the original second injection and whole
  difference reflection. The original first injection proves a∘π₁=0 ⇒ a=0.
- [Kernel precomposition covers](../emdash2/emdash3_2_one_cat_kernel_precomposition_covers.lp)
  form w=coker(r)∘π₁. Its annihilation of K(D′) follows through the proved
  lift and the original cokernel annihilation. Whole cover descent gives
  ψ∘D′=w. The second injection and cancellation of p force ψ=0, and
  the first injection gives coker(r)=0. Original normality yields the
  actual cover factor and cancellation of the existing r.
- [Homology covers](../emdash2/emdash3_2_one_cat_homology_covers.lp)
  use the just-derived r cancellation and original q_H cancellation to
  prove coker(ρ)=0. Original normality yields its categorical cover with
  the actual original homology endpoint.
- [Native window covers](../emdash2/emdash3_2_one_cat_native_homology_window_covers.lp)
  connect these programs to the existing Rm/R0/R1/R2 window and its
  original whole maps and input chain-zero laws. E0 derives the outgoing
  p premise; the previous right-column input supplies the original H
  family. The public window operation accepts no separate cover, inverse
  or epicity evidence. Full AdditiveCategory and the original normality
  are explicit, as required by the Abelian proof.

**Experiment notes.** The first coimage-input generator had a parenthesis
error, corrected before checking. All semantic owner probes then checked
without new proof-time comparisons or computation rules. Original graph
source presentations of zero are aligned by existing whole terminal-family
uniqueness. The selected inverse remains fixed throughout descent and
reflection; no object transport or universal-choice replacement is used.

**Qualification.** All seven owners and three reviewer files pass serial,
warning-enabled, resource-guarded checks within the 90-second per-target
ceiling. The 19 assertions contain 15 positive observations and four
rejection controls. They check original descent reconstruction, retained
kernel-square projections, actual cover forwards, both laws at the same
selected inverse, whole Hom action and the original native-window endpoint.
The cover evidence cannot certify that r itself is invertible or replace
the indexed factor by an unrelated map.

Final owner logs span `072912`–`073025`. Reviewer logs are
`one_cat_coimage_cover_descent-20260914-073040.log`,
`one_cat_kernel_precomposition_covers-20260914-073048.log` and
`one_cat_native_homology_window_covers-20260914-073101.log`.
The original kernel-pullback and native-window-map reviewers still pass
when imported after the new window-cover owner, at
`nuh4c6c3f_retained_homology-20260914-073240.log`.
Seven original dependency-load-order baselines pass at `073254`–`073408`.
All eleven final warning inventories exactly match their corresponding
baselines in categories, locations, term heads, rule families and parser
issues; exact logs and checked source hashes are retained in
`tmp/probes/nuh4c6c3f_warning_comparison.json`.

Strict catalog, report-header/reference lint, shell syntax, exact owner
registration, unique declarations, added local links and diff hygiene pass.
All 35 symbols are definitions; no new primitive or rule requires a new
LHS audit. The generated source-only health report records 1,106 files and
snapshot `4c6479344102e23bcc365a5a3d1ad0612bfd51bc2d2c6b7677d360db4adfeb21`.
No repository-wide, TypeScript or aggregate typecheck was run. Qualification
is scoped to these ordinary whole constructions and their stated original
structural/normality assumptions; deferred Op/profile work remains separate.

**Next C6d: annihilation and connecting descent.** Prove the original whole
θ∘κ_ρ=0 from the input window, preserving the already constructed θ and
ρ. Then apply the new coimage-cover descent at Arr(ρ) to construct δ
and prove its reconstruction and output exactness. Additional cover
constructions needed to establish that annihilation must likewise be
derived through native K/Q; do not assume the output zero law or exactness.
Concrete model/reifier automation, snake/direct/native comparison and
final qualification remain required. Op/duality and the later strictness-
profile integration remain deferred.

### NUH-4C6c3e1: Derived categorical cover of the whole difference map

**Qualified after 612ab396 (2026-09-14).**
For the original whole short-exact row's p:M⇒Z and any f:X⇒Z, form

```text
D = f∘π₁ − p∘π₂ : Prod(X,M) ⇒ Z.
q_D = 0;
φ_D : Coim(D) ⇒ Z is invertible under the original supplied normality.
```

The first conclusion uses no normality. The second is fixed-forward
OmegaEquivAlong on the existing coimage-to-target factor, not an arbitrary
equivalence between its endpoints. All data remain whole internal terms.
Twenty-six definitions across eight one-way owners introduce no primitive,
runtime rewrite, unifier or change to earlier LP sources.

**Construction and semantic boundary.**

- [Kernel of zero](../emdash2/emdash3_2_one_cat_zero_kernel_families.lp)
  lifts id through the original K(D). Native mate reconstruction gives one
  inverse law; original kernel cancellation gives the other for the same
  section. No replacement zero diagram or kernel selection is used.
- [Fixed-forward composition](../emdash2/emdash3_2_omega_equiv_composition.lp)
  uses the existing IsoEvidence constructor/composition and the original
  selected left inverse in both inverse slots. For an equal whole forward
  map, it retains that inverse and proves the two required laws by
  congruence. It introduces neither a new equivalence type nor an object cast.
- [Whole coimage factor paths](../emdash2/emdash3_2_one_cat_coimage_factor_paths.lp)
  give a∘q_κ=u, κ_q∘u=∂ and φ∘q_κ=∂. Native inverse mating and the
  existing native/raw mate comparison prove these equations. Original
  quotient cancellation then proves ι∘a=φ for the earlier φ program.
- [Whole difference cospans](../emdash2/emdash3_2_one_cat_difference_cospans.lp)
  form D from the original two projections. Native product β and whole
  bilinearity prove D∘⟨a,b⟩=f∘a−p∘b and its postcomposition law. Applying
  this at ⟨0,id⟩ and using zero-difference reflection gives hD=0 ⇒ hp=0.
  No unproved additive unit law or full additive functor-category structure
  is assumed.
- [Cokernel annihilation](../emdash2/emdash3_2_one_cat_cokernel_family_annihilation.lp)
  restricts the original whole unit annihilation to the actual D. Existing
  whole terminal uniqueness aligns its source presentation; no new square
  or annihilation primitive is supplied.
- [Difference cokernels](../emdash2/emdash3_2_one_cat_difference_cokernels.lp)
  apply that result to the original q_D, so q_Dp=0. The original whole
  short-exact row's outgoing cancellation forces q_D=0.
- [Zero-cokernel covers](../emdash2/emdash3_2_one_cat_zero_cokernel_covers.lp)
  keep the original image diagram Arr(q)∘D. Whole terminal/initial
  uniqueness presents q_D=0 at precisely that diagram; the kernel-of-zero
  construction makes its original inclusion invertible. Restriction,
  original normality and ι∘a=φ give invertibility of the original φ_D.
- [Difference covers](../emdash2/emdash3_2_one_cat_difference_covers.lp)
  combine those constructions for the original row. Their arguments contain
  no cover/epicity flag or independently supplied inverse.

**Refinements.** The first factor reconstruction attempt mixed the native
image endpoint with its raw composition presentation. Keeping the actual
native intermediate and reusing the existing same-composite endpoint view
resolved it. The older φ is a unit/counit formula, so its reconstruction
must first use the existing native/raw mate comparison. A proposed import
of mate-reindex comparisons proved unnecessary and was removed after
`nuh4c6c3e_factor_import_ablation-20260914-065408.log` passed. The image
inverse first stopped at the two zero-family endpoint presentations;
existing whole terminal/initial uniqueness supplied the needed equations.
No new proof-time comparison or runtime rule was required.

**Qualification.** Eight owners and three reviewer files pass serial,
warning-enabled, resource-guarded checks with a 90-second ceiling per
Lambdapi invocation. The 22 assertions comprise 17 positive observations
and five rejection controls. They retain original forwards and selected
inverses, both inverse laws at the same inverse, independent paired
inputs, the actual row's cokernel-zero result and whole Hom action. An
unrelated map cannot replace the indexed forward arrow, and changing a
cospan leg is not silently erased.

Final owner logs span `065448`–`065548`. Reviewer logs are
`omega_equiv_composition-20260914-065600.log`,
`one_cat_zero_cokernel_covers-20260914-065607.log` and
`one_cat_difference_covers-20260914-065615.log`.
The retained original kernel-pullback and native homology-window reviewers
pass together with the new cover at
`nuh4c6c3e_retained_homology-20260914-065803.log`.
Nine original dependency-load-order baseline files pass at `065817`–`065929`.
All twelve final warning inventories match their corresponding baselines
exactly in categories, locations, term heads, rule families and parser
issues; logs and exact source hashes are recorded in
`tmp/probes/nuh4c6c3e_warning_comparison.json`.

Strict catalog, report-header/reference lint, shell syntax, added local
links and diff hygiene pass. All 26 owner symbols are unique definitions;
there is no new primitive or rule requiring a new LHS audit. The refreshed
source-only health report records 1,096 files and source snapshot
`8ff201ab8ab9080711df22aaf6f5649c19f8616c55e6de2eb468e1977d1347a0`.
No repository-wide, TypeScript or aggregate typecheck was run. These are
scoped ordinary whole constructions under the stated original structural
and normality assumptions; deferred Op/profile work remains separate.

**C6c3e2 design, implemented above.** Specialize f to the original κ_d. The kernel of D gives a
compatible pair; lift its second projection into the original L=K(d∘p)
and use kernel cancellation to identify its first projection with r after
that lift. Then descend coker(r)∘π₁ through this proved auxiliary cover.
The second injection and original p cancellation force the descended map
to zero, and the first injection gives coker(r)=0. Apply the same original
zero-cokernel cover construction to r, then to ρ=q_H∘r. Retain the actual
L, r, ρ and H endpoints. These r/ρ results, θκ_ρ=0, δ and output exactness
are not established by the present auxiliary cover alone. Model/reifier
and snake comparison work, and the agreed deferrals, remain unchanged.

### NUH-4C6c3c2: Whole inverses, restriction and zero-difference cancellation

**Qualified after 4db39ec6 (2026-09-14).** This tranche proves

```text
id+N_X=0,       f+(−f)=0,       f−f=0,
a+b=a+c ⇒ b=c,       −f=−g ⇒ f=g,       f−g=0 ⇒ f=g.
```

It also derives zero composed differences from equality of either pair of
pre/postcomposites and proves the direct shear negative equal to the
original universal restriction. All inputs and conclusions are whole
transformations. The development adds 38 definitions and eight unifiers
across seven LP owners, with no primitive, runtime rule, new operation
selection or edit to earlier LP owners.

**Construction and owners.**

- [Shear inverse paths](../emdash2/emdash3_2_one_cat_shear_additive_inverse_paths.lp)
  form u=S⁻¹∘ι₁. Whole inverse cancellation gives Su=ι₁; native projection
  β then yields π₁u=id and (π₁+π₂)u=0. Whole bilinearity turns the latter
  into id+N=0. Specialization at B=C, X=id_C gives the original universal
  negative identity's law.
- [Restriction composition](../emdash2/emdash3_2_reindex_composition_paths.lp)
  first stages generic Hom action before specializing the precomposition
  functors. The full Hom comparison and its point recover successive
  restriction. A single native-precomposition/raw-associativity view
  retains the original three functors; identity and composition
  observations use existing generic functoriality.
- [Native mate restriction](../emdash2/emdash3_2_one_cat_adjunction_family_reindex.lp)
  transports the original unit/action formula. Restriction composition
  and existing whole whiskering prove the forward law; native inverse
  cuts derive the backward law. Two endpoint-presentation comparisons
  retain the same R/L/F/G/J and the exact same input h. They neither select
  a different adjunction nor erase an input.
- [Paired restriction](../emdash2/emdash3_2_product_family_reindex.lp)
  keeps literal paired functors and original diagonal source/target
  presentations. Five sufficient views cover the full paired restriction,
  its two postcomposed object presentations, and the two complete Hom
  actions. The four Hom/point observations preserve both input arrows.
- [Whole biproduct restriction](../emdash2/emdash3_2_one_cat_biproduct_family_reindex.lp)
  applies those laws to the same product/coproduct mates, then the original
  diagonal and addition. The reindexed product families compare directly
  with the original selected products of the restricted families; no
  object cast or replacement product is used.
- [Whole inverse laws](../emdash2/emdash3_2_one_cat_additive_family_inverse.lp)
  restrict the universal id+N law, retain the existing N_X, and use original
  zero restriction and whole bilinearity to derive f+(−f)=0 and f−f=0.
- [Cancellation](../emdash2/emdash3_2_one_cat_additive_family_cancellation.lp)
  computes S∘pair(a,b)=pair(a,a+b), then cancels the original invertible
  shear to cancel a common left summand. Original scalar −id is invertible;
  the existing fixed-forward pointwise-to-whole operation gives ΩAlong on
  the already constructed universal N, and generic restriction retains
  that evidence for N_X. Its whole inverse gives negation reflection.
  Left-summand cancellation and negation reflection prove f−g=0 ⇒ f=g.
  The same uniqueness proves direct-shear N equals restricted N. No
  additional inverse transformation or naturality square is supplied by
  callers.

**Selected comparison boundary.** Direct raw prewhiskering associativity
first stopped at endpoint presentations. Staging the complete generic Hom
action supplies its native proof, and the original Cat associativity view
supplies the raw consumer. Paired restrictions similarly retain the whole
Hom owner and the same mate input. The mixed-native-point and unrestricted
literal paired-Hom candidate views were unnecessary: the entire inverse/
cancellation consequence probe passes with both removed
(`nuh4c6c3d_inverse_consequences-20260914-055839.log`). Their unused
observation probes are not promoted. No runtime opposite, diagonal or
Sigma normalization change is installed.

**Qualification.** All seven owners, three reviewers and two retained
consumer probes pass serial warning-enabled resource-guarded checks, each
within the 90-second ceiling. The reviewers contain 31 assertions: 22
positive and nine negative, including controls for changed restriction,
product, functor, adjunction and mate input. Owner logs span
`060622`–`060709`, with the restriction-composition owner rechecked at
`063043` after removing its trailing blank line; reviewer logs are
`one_cat_biproduct_family_reindex-20260914-061424.log`,
`one_cat_additive_family_inverse-20260914-061432.log` and
`one_cat_additive_family_cancellation-20260914-061444.log`.
Retained arithmetic and homology consumers pass at `061637` and `061651`.
Their twelve warning inventories exactly match the eight corresponding
dependency-load-order baselines (`061924`–`062026`) in categories,
locations, term heads, rule families and parser issues. The final checked
source hashes are retained in
`tmp/probes/nuh4c6c3d_warning_comparison.json`.

All three affected rule-owner LHS audits, strict catalog check, report and
active-reference lint, shell syntax and diff hygiene pass. The generated
source-only health report records 1,085 registered files and snapshot
`7f1de06f0281f6545ab07bf408e2746ffe30a35ca4206d0d291ac10265e9f8c2`.
No repository-wide, TypeScript or aggregate check was run. This is focused
qualification of the stated ordinary whole constructions, not completion
of the cover theorem or qualification of the deferred profile migration.

**C6c3e design, partly implemented by C6c3e1 above.** The proof route
uses the zero-difference criterion rather than assuming unproved additive
unit laws. For the original p:M⇒Z and κ:K(d)⇒Z, form

```text
D = κ∘π₁ − p∘π₂ : Prod(K(d),M) ⇒ Z.
```

The original K(D) gives a compatible pair by the proved difference-zero
reflection. Lift its second projection through the original L=K(d∘p);
original kernel cancellation identifies the first projection with r after
that lift. Keep the original L and r.

To make the auxiliary cover categorical, show the original cokernel
projection of D is zero: compose its annihilation with the second product
injection, use bilinearity/projection β to obtain a zero difference, then
use zero-difference reflection and the original row's outgoing
cancellation. The kernel inclusion defining Im(D) is consequently an
isomorphism by whole kernel lifting at that same zero arrow. Original
Coim⇒Im normality then gives ΩAlong on the canonical Coim(D)⇒Z.

Apply its whole descent to coker(r)∘π₁, whose kernel annihilation follows
from the preceding lift and coker(r)∘r=0. The second injection and original
p cancellation force the descended map to zero; the first injection then
forces coker(r)=0. Original image/kernel lifting and normality should give
the actual Coim(r)⇒K(d) equivalence. Derive the corresponding cover for
ρ=q_H∘r through the original quotient cancellation. This is the next
construction/qualification plan, not an already proved cover theorem.
General kernel-of-difference pullbacks may share these operations when
later exactness covers require arbitrary legs.

Whole θκ_ρ=0, δ descent and output exactness remain required. Do not
postulate r/ρ epicity, switch to ordinary W/V provider inputs, infer a
complete additive capability on Functor_cat, or silently use unproved
zero-unit/associativity laws. Concrete model/reifier and snake comparison
work remain open; Op/profile integration remains deferred.

### NUH-4C6c3c1: Whole bilinearity through native mate distribution

**Implemented after e2fb6740 (2026-09-14).** Both composition laws for
whole addition and subtraction are proved at the original functors:

```text
h∘(f+g) = h∘f + h∘g,       (f+g)∘h = f∘h + g∘h,
h∘(f−g) = h∘f − h∘g,       (f−g)∘h = f∘h − g∘h.
```

These proofs use whole mates and existing whole naturality. No caller
component square, pointwise equality assembly, new selected product or
whole PreadditiveCategory capability is introduced. The tranche adds 31
definitions and five unifiers across nine owners, with no primitive,
runtime rule or edit to an earlier LP owner.

**Owners and construction.**

- [Product composition paths](../emdash2/emdash3_2_product_composition_paths.lp)
  derive coordinate composition from existing generic projection-functor
  action, including opaque product objects.
- [Product-family action views](../emdash2/emdash3_2_product_family_action_views.lp)
  compare native diagonal Hom action with the duplicating Hom functor;
  identity application checks the original source/target Transf classifiers
  and input. Two native projected-composition comparisons retain both
  original factors and all category parameters. The final view compares
  endpoint presentations of the same whole composite, with both arrow
  operands repeated literally. It cannot select different factors in
  place of the existing associativity computation. Three derived paths
  expose complete diagonal Hom action and its two native coordinates.
- [Ordinary transpose paths](../emdash2/emdash3_2_one_cat_adjunction_transpose_paths.lp)
  give the forward-mate counterparts of existing inverse-mate naturality.
  The original unit and whole action supply the laws; ordinary R1/L1
  profiles remain explicit.
- [Native tuple paths](../emdash2/emdash3_2_product_family_tuple_paths.lp)
  preserve complete tuples and their original arrows under diagonal and
  paired composition. Literal native Sigma parameters are retained before
  specializing components to identities.
- [Whole product projections](../emdash2/emdash3_2_one_cat_product_family_projection_paths.lp)
  use the original native unpair(id). Inverse-mate naturality proves
  unpair(h)ᵢ=πᵢ∘h, then native inverse cuts prove πᵢ∘pair(f,g)=f/g as whole
  equations.
- [Product-family maps](../emdash2/emdash3_2_product_family_maps.lp)
  are the original postcomposition Hom action and its native point. No
  C1 or BinaryProducts argument is required merely to construct this map.
- [Whole biproduct distribution](../emdash2/emdash3_2_one_cat_biproduct_family_distribution.lp)
  derives pair precomposition, pair target action, copair postcomposition
  and copair source action. Two input-presentation paths keep the original
  f/g while naming their literal native Hom inside the mate application.
- [Whole addition bilinearity](../emdash2/emdash3_2_one_cat_additive_family_bilinearity.lp)
  combines those laws with the original diagonal pairing. Its naturality
  is proved at the original P(W,W)/P(X,X), rather than replacing the
  selected product-family endpoints by a new object presentation.
  [Subtraction bilinearity](../emdash2/emdash3_2_one_cat_difference_family_bilinearity.lp)
  then follows from existing whole negation composition laws and the same
  addition operation.

**Resolved comparison boundary.** The initial proofs stopped at native
versus public inferred parameters inside Sigma projections and whole
composites. The selected solution keeps literal native Sigma annotations
and uses sufficient proof-time comparisons at the complete Hom-action and
composition owners. The unchanged-composite comparison repeats both
operands; it is not an injectivity assertion for composition. Independent
Sigma β-view and Sigma η-representation experiments were unnecessary:
the complete product projection and tuple consumers pass with those views
removed (`nuh4c6c3c_beta_ablation-20260914-034607.log`). They remain ignored
historical probes and are not imported by any promoted owner. No runtime
diagonal fold or broad Sigma rewrite is introduced.

**Qualification (2026-09-14).** All nine final owners and three reviewers
pass serial warning-enabled guarded checks, each bounded to 90s. The
reviewers contain 28 assertions: 22 positive and six negative. They cover
complete diagonal Hom action and native coordinates, arbitrary base-arrow
and next Hom observations, both native projection factors, identity input
preservation, unchanged-composite endpoint comparison, retained generic
associativity, product projection β, all four mate distribution directions,
product-map Hom action, and all four bilinearity laws. Changed factors,
inputs and unrelated endofunctors are rejected. The retained arithmetic
and kernel-pullback/native-window joins both pass.

Final owner log timestamps under `emdash2/logs/probes/` are
`040733`, `040737`, `040742`, `040747`, `040753`, `040759`, `040806`,
`040815`, `040823`. Final reviewer logs are
`product_family_action_views-20260914-041157.log`,
`one_cat_biproduct_family_distribution-20260914-041435.log` and
`one_cat_additive_family_bilinearity-20260914-041214.log`.
Retained joins are `nuh4c6c3c_retained_arithmetic-20260914-041443.log`
and `nuh4c6c3c_retained_homology-20260914-041452.log`.

Every warning inventory matches the unchanged dependency load order in
categories, locations, term heads, rule families and parser diagnostics.
Counts (critical pairs / replaceable patterns) are 1,146/157 for the
generic product/action/tuple/map owners, 1,151/157 for transpose paths,
1,214/167 for whole product projection paths, 1,278/169 for distribution
and addition bilinearity, 1,307/169 for subtraction and retained arithmetic,
and 1,482/169 for the retained homology join. Exact comparisons and checked
source hashes are in ignored `tmp/probes/nuh4c6c3c_warning_comparison.json`;
the dependency map is `tmp/probes/nuh4c6c3c_baseline_mapping.json`.

The strict LHS audit passes. The central catalog is current; source-only
health covers 1,075 registered files. Report/reference lint, shell syntax,
exact diff hygiene and added local links are checked. No aggregate,
repository-wide or TypeScript typecheck was run.

**Then-next C6c3c2, now implemented above at the stated boundary.** Prove the whole zero/additive-inverse laws needed for
cancellation, then use them in cover stability. At B=C, X=id_C, let
u=S⁻¹∘ι₁. The existing S∘S⁻¹=id and new projection β laws give
π₁u=id and (π₁+π₂)u=0. Whole precomposition bilinearity identifies the
latter with id+N. Retain the original universal N and prove any required
reindexing comparisons before using the corresponding restricted-family
law. Then prove r/ρ epicity, θκ_ρ=0, original coimage/cokernel descent for δ
and output exactness. Concrete model/reifier and snake comparison work
remain required; Op/profile integration stays deferred.

### NUH-4C6c3b: Whole shear inverse, negation and subtraction

**Implemented after e3e9fdea (2026-09-14).** Negation and subtraction are
now actual internal Hom functors. The construction adds 41 definitions,
seven LP owners and three reviewers, with no primitive, runtime rule,
unifier, new product/zero choice or edit to an earlier LP source.

**Whole construction and its semantic boundary.**

1. [Native product inverse components](../emdash2/emdash3_2_one_cat_product_family_inverse_components.lp)
   are derived by Sigma elimination on the input of the existing whole
   pairing functor. Instantiate at unpair(h); its native forward/inverse
   cut recovers the same arbitrary h. Original projection β then reads
   both components. No new Sigma η or projection-composition fold is needed.
2. [Scalar shear arithmetic](../emdash2/emdash3_2_additive_shears.lp)
   proves both inverses for S(x,y)=(x,x+y) and S⁻¹(x,y)=(x,−x+y) from the
   original additive/product laws. These are component inverse proofs,
   not an assembly of pointwise naturality squares.
3. [The whole shear](../emdash2/emdash3_2_one_cat_shear_families.lp)
   is constructed first, using projections selected by native unpair(id)
   and the existing whole pairing/addition. Its actual component agrees
   with the original scalar S. Fixed-forward ΩAlong evidence keeps the
   literal scalar inverse in both inverse slots and compares the forward
   arrow in the two law proofs. This preserves component computation;
   transporting an opaque evidence package is unnecessary.
4. The existing `strict_transf_pointwise_omega_along` operation constructs
   the whole inverse of that already formed S. The ordinary C1 scope is
   explicit. Both whole inverse laws hold for the same selected left
   inverse, using the existing inverse-candidate comparison for the right
   law. This consumes an existing generic assembly interface and adds no
   new primitive or caller naturality field.
5. [The original zero component](../emdash2/emdash3_2_preadditive_zero_family_components.lp)
   is read through the existing terminal/initial factorization. Together
   with product pairing it gives the whole ι₁=(id,0).
   [Whole negative identity](../emdash2/emdash3_2_one_cat_negative_identity.lp)
   is (π₂∘S⁻¹)∘ι₁. Its component is proved to be the original −id. Fix this
   once on id_C; later restrictions use generic prewhiskering.
6. [Whole negation](../emdash2/emdash3_2_one_cat_negative_families.lp)
   restricts that one transfor and applies the native Hom-postcomposition
   functor. Existing whole naturality proves centrality and both
   −(g∘f)=(−g)∘f and −(g∘f)=g∘(−f). Component proofs observe original
   Hom negation and are not input to the whole program.
7. [Whole subtraction](../emdash2/emdash3_2_one_cat_difference_families.lp)
   composes the existing Product_map_func(id,Neg) with native addition.
   Its point is f+(−g), and its component is the original scalar
   difference. The source product and addition's literal native
   intermediate Hom are both retained; all higher action comes from
   existing internal functor composition.

**Resolved experiments.** Raw π∘(X,X) and projected raw counit routes
stopped at source-family comparisons. Native unpair(id) supplies the
projection without those comparisons. Reading it through the forward
mate cut avoids premature counit expansion. A manually written pair of
projection composites for the signed input similarly obscured the native
middle; existing Product_map_func and the correct native middle recover
its computation. None of these failures requires a new rewrite/unifier,
object cast or alternate product. Failed probes remain ignored recovery
evidence, not active theory.

**Qualification (2026-09-14).** All seven final owners and three reviewers
pass serial warning-enabled checks under the 90s/2GiB guard. The reviewers
contain 25 assertions: 20 positive and five negative. They cover scalar and
whole shear inverse laws at the same selected inverse, its computational
component, arbitrary base-arrow and next Hom action, native inverse-pair
component recovery, whole centrality and both signed composition laws,
negation/subtraction higher action, original component subtraction and
unrelated-input rejection. The combined retained addition/copairing/native
homology-window reviewer also passes.

Final owner log timestamps under `emdash2/logs/probes/` are
`022445`, `022450`, `022456`, `022506`, `022513`, `022521`, `022530`.
Reviewer logs are `one_cat_shear_families-20260914-022538.log`,
`one_cat_product_family_inverse_components-20260914-022546.log` and
`one_cat_negative_families-20260914-022552.log`. Retained consumers are
`nuh4c6c3b_retained_consumers-20260914-022603.log`.

Exact warning inventories match in categories, locations, term heads,
rule families and parser diagnostics. Counts (critical pairs / replaceable
patterns) are 1,246/169 for scalar shear, 1,214/167 for product inverse
components, 1,280/169 for zero components, 1,307/169 for whole shear and
signed owners/reviewers, and 1,482/169 for the retained join. Baselines must
preserve the source's first dependency-load order: an initially sorted
import list changed inherited diagnostic locations and two counts despite
containing the same dependencies. Matching ordered baselines resolve that
control issue without editing any LP source or suppressing warnings.
Source hashes, log paths and exact comparisons are in ignored
`tmp/probes/nuh4c6c3b_warning_comparison.json`; the ordered dependency map
is `tmp/probes/nuh4c6c3b_baseline_mapping.json`.

The rule/unification surface is unchanged. The central catalog is current,
source-only health now covers 1,063 registered files, report/reference
lint passes, and the exact diff/added local links are checked. No aggregate,
repository-wide or TypeScript typecheck was run.

**Then-next C6c3c, bilinearity now implemented above.** Derive whole additive cancellation/bilinearity and the
specific identities needed by cover stability. The whole shear inverse
laws provide a concrete start: at B=C and X=id_C, restrict S∘S⁻¹=id
along ι₁ and observe its two native product coordinates to derive the
additive inverse law for the universal negative identity. Prove the needed
reindexing/operation comparisons before using that law for the restricted
N_X; do not identify it silently with a newly assembled inverse shear over X.
Qualify those operations through whole mates, not by assuming
pointwise equality implies a whole law. Then prove r/ρ epicity and
θκ_ρ=0, perform original coimage/cokernel descent for δ, and prove output
exactness. No whole PreadditiveCategory(Functor_cat(B,C)), general
PullbackStructure or cover property is inferred merely from component
readbacks. The existing structural/model obligations, model/reifier and
snake work remain open; Op/profile integration stays deferred.

### NUH-4C6c3a: Whole copairing and addition at the original product

**Implemented after aa67d2e1 (2026-09-14).** This is the arithmetic
prerequisite identified while preparing the proof that the native cover is
epic. No epicity, θ-on-kernel annihilation or connecting map is postulated.

**Semantic and model boundary.** For ordinary C, the original additive
product is also a coproduct. Bilinearity makes the old copairing natural,
and its original injection/reconstruction laws give Prod⊣Δ. The current
opaque Adjunction interface does not assemble that whole evidence from
point laws. Therefore `one_cat_biproduct_adjunction` is explicitly one new
structural/model primitive, dependent on C1, the original Prod/t/A and the
supplied original T0. A concrete model must interpret this presentation;
green checking does not discharge that obligation.

**Owners.**

- [Whole injections](../emdash2/emdash3_2_one_cat_biproduct_injections.lp)
  are derived by the existing product-family mate from (id,0) and (0,id).
  The target diagram is literally id_(C×C), avoiding a new product η fold.
  Zero is the original terminal/initial-family composite; T0 is retained.
- [The biproduct presentation](../emdash2/emdash3_2_one_cat_biproduct_adjunction.lp)
  supplies Prod⊣Δ at that same Prod. Its two runtime clauses expose the
  whole pair of those injections and the original codiagonal component.
  They do not install generic naturality or composition rules.
- [Whole copairing and its inverse](../emdash2/emdash3_2_one_cat_copair_families.lp)
  are the native untranspose/transpose functors. Both inverse composites
  reduce to identity, including arrow and next Hom action. Literal native
  Hom parents are retained inside applications and compositions.
- [Generic component observations](../emdash2/emdash3_2_whiskering_component_paths.lp)
  stage existing whiskering computation while the functors/transfor are
  variable. Two reflexivity paths suffice; no metadata rewrite is added.
- [Copairing readback](../emdash2/emdash3_2_one_cat_copair_family_paths.lp)
  derives the whole counit/action formula and component agreement with the
  original additive copairing. Projection naturality comes from the
  existing whole projection transfors, not a caller-supplied square.
- [Whole addition](../emdash2/emdash3_2_one_cat_additive_families.lp)
  precomposes native copairing with the existing whole product diagonal.
  [Its readback](../emdash2/emdash3_2_one_cat_additive_family_paths.lp)
  proves the whole formula and original componentwise sum through the
  original bilinearity and product β laws. The program accepts only whole
  f/g; point equalities are downstream observations of that program.

The tranche has 16 definitions, one primitive, two runtime coupling rules
and no new unifier. It adds seven LP owners and three reviewer examples,
with no edit to earlier LP sources. The ordinary-target scope and explicit
model obligation are deliberate; there is no claimed higher additive
closure or automatic model construction.

**Prototype findings.** The unit's constant Sigma family must be explicitly
typed in both its rule RHS and reviewer RHS. Generic whiskering component
paths avoid premature expansion of the concrete counit/product metadata.
Scalar [f,g]∘Δ=f+g needs the existing propositional associativity witness
before projection β; no new associativity fold is introduced.

**Qualification (2026-09-14).** All seven final owner files and the three
reviewers pass serial warning-enabled guarded checks, each bounded to 90s.
The reviewers contain 26 assertions: 22 positive and four negative. They
cover the original unit/counit, both whole mate inverse cuts, input
recovery, nonidentity base action, next Hom action, component copair/sum
readbacks and rejection of unrelated input/capability substitution. The
combined retained product-family/native-window reviewer also passes.

Final owner logs under `emdash2/logs/probes/` have timestamps
`015110`, `015120`, `015130`, `015141`, `015147`, `015156`, `015205`;
reviewer logs are `one_cat_biproduct_adjunction-20260914-015213.log`,
`one_cat_copair_families-20260914-015221.log` and
`one_cat_additive_families-20260914-015229.log`. Retained consumers are
`nuh4c6c3a_retained_consumers-20260914-015237.log`.

Every warning inventory matches its unchanged dependency join exactly in
categories, locations, term heads, rule families and parser diagnostics.
The ordinary owners/reviewers retain 1,278 critical-pair and 169 replaceable-
pattern warnings; generic component observations retain 1,151/157; the
retained-consumer join retains 1,451/169. No new warning family is introduced.
The comparison and checked-source hashes are retained in ignored
`tmp/probes/nuh4c6c3a_warning_comparison.json`. The strict LHS audit passes.
The central check catalog remains current; source-only health now lists
1,053 registered files. Report/reference lint and exact diff hygiene pass.
No aggregate, repository-wide or TypeScript typecheck was run.

**Then-next C6c3b, now implemented above.** Construct the signed operations and whole laws actually
needed for cover stability from these native operations and the original
additive data. Then prove r/ρ epicity and θκ_ρ=0 and use original Q/coimage
descent for δ. Do not infer a whole PreadditiveCategory(Functor_cat(B,C)),
a general PullbackStructure or the cover theorem from these component
readbacks alone. Output exactness, model/reifier construction and snake
comparison remain subsequent obligations. Op and profile integration stay
deferred.

### NUH-4C6c2: Native row/window assembly and the covered map θ

**Implemented after 2e3300c7 (2026-09-14).** The original native row
functors, transformations and whole short-exact evidence now construct
ρ and θ on a common literal kernel pullback. Only the two whole middle-
column chain-zero laws are mathematical input. All other column zeros,
row squares, lifts and prequotient reconstructions are derived.

**Owners and construction.**

- [Family naturality/whiskering](../emdash2/emdash3_2_one_cat_family_naturality_paths.lp)
  restricts the existing whole transformations. The ordinary C1 scope is
  explicit; no pointwise naturality field is added.
- [Native row families](../emdash2/emdash3_2_one_cat_zero_cone_row_families.lp)
  retain the original ZeroArrowCone_cat row functor and expose whole
  vertices, row maps and both commuting squares. The short-exact condition
  is the existing OneCatShortExactFamily at those actual observations.
- [Whole zero postcomposition](../emdash2/emdash3_2_one_cat_zero_family_postcomposition_paths.lp)
  follows from original initial-family uniqueness; the existing whole
  zero-precomposition path is reused.
- [Column inputs](../emdash2/emdash3_2_one_cat_zero_cone_column_inputs.lp)
  derive left/right chain zero by original row cancellation, then call the
  existing whole input constructor. Outgoing diagrams precede K/Q choices.
- [Native input observation](../emdash2/emdash3_2_one_cat_kernel_input_observation_paths.lp)
  recovers the original whole differential with the native composed parent.
- [Whole row lifts](../emdash2/emdash3_2_one_cat_short_exact_family_lifts.lp)
  are actual Hom functors from the original K mate and β inverse. The
  original incoming map reconstructs the complete input k.
- [Covered maps](../emdash2/emdash3_2_one_cat_homology_covered_maps.lp)
  derive λ:L⇒A₁, i₁λ=d_B a_L, d_Aλ=0 and the original left-cycle lift v,
  with κ_A v=λ. Then θ=q_A v, using the original H quotient.
- [Four-row assembly](../emdash2/emdash3_2_one_cat_native_homology_window_maps.lp)
  constructs both native column inputs, the original H_C/H_A and ρ/θ.
  Their source is the same literal K(d_C p₀). E₀ is retained for the later
  cover-epicity proof. No new window category/opaque constructor is added.

**Measured presentation boundaries.**

The two new [proof-time views](../emdash2/emdash3_2_diagram_reindex_views.lp)
retain existing runtime owners. The first compares (ev_i∘F)∘D with
F(−)[i]∘D; the prior evaluator comparison did not automatically extend
through that accumulated composition. The second observes the same h
under its native postcomposition parent and raw composed parent. It
retains the original F, X, target G, h, shape I/C and point i. Neither
comparison changes an object or installs runtime cancellation.

A direct specialization of generic whiskering failed at the nested
whole-evaluation endpoints. Staging the shape-specific statement at
variable F/G and using the first view resolves it. The column reviewer
then exposed native/raw input recovery at compound right-column functors.
A direct recovery-wrapper body still failed; compare parent observations
while h is a variable using the second view, then instantiate the existing
recovery path. The resulting native incoming observer recovers both actual
column differentials.

The row Hom functor retains the native intermediate Hom of K∗D inside
its composition, while its postcomposition operator names the original
K(D), which is β⁻¹'s source. This lets its object projection expose the
original raw β⁻¹∘lift_K comparison through existing proof-time rules.
The unsuccessful route through explicit identity-functor actions is not
promoted, and no new identity or inverse runtime rule is installed.

**Qualification.** Forty-two definitions and two proof-time unifiers in
nine new owners, with no primitive, runtime rule or earlier LP edit.
All 41 reviewer assertions pass: 29 positive and 12 negative. They check
retained evaluator operands and runtime distinction, both native row
squares and actual vertex-map components, both column-zero laws and
native incoming recovery, row-lift point/reconstruction/further-Hom
observations, original H endpoints, the common source and ρ/θ components
and Hom action. Changed diagram/reindexing/shape/whole-cell, k, Q and p
inputs are rejected; no arbitrary equality is reflected by a runtime rule.

The source checks, reviewers and controls run serially under the resource
guard with warning output and ≤90 seconds per target. Exact categories,
locations, term heads, rule families and parser diagnostics match unchanged
dependencies: 1150 critical pairs / 157 pattern warnings for the view owner
and reviewer; 1155 / 157 for family naturality; 1208 / 159 for rows, input
observation and row lifts; 1381 / 159 for zero postcomposition, columns,
covered/window maps and their consumers. These counts describe the
respective import joins; no warning is added or removed by this stage.

| Target | Passing log under emdash2/logs/probes | Unchanged dependency join |
| --- | --- | --- |
| emdash3_2_diagram_reindex_views | emdash3_2_diagram_reindex_views-20260914-003947.log | nuh4c6c2_deps_view-20260914-004058.log |
| diagram_reindex_views | diagram_reindex_views-20260914-004207.log | nuh4c6c2_deps_view-20260914-004058.log |
| emdash3_2_one_cat_family_naturality_paths | emdash3_2_one_cat_family_naturality_paths-20260914-003952.log | nuh4c6c2_deps_family-20260914-004104.log |
| emdash3_2_one_cat_zero_cone_row_families | emdash3_2_one_cat_zero_cone_row_families-20260914-003958.log | nuh4c6c2_deps_row-20260914-004110.log |
| emdash3_2_one_cat_kernel_input_observation_paths | emdash3_2_one_cat_kernel_input_observation_paths-20260914-004009.log | nuh4c6c2_deps_input-20260914-004117.log |
| emdash3_2_one_cat_zero_family_postcomposition_paths | emdash3_2_one_cat_zero_family_postcomposition_paths-20260914-004015.log | nuh4c6c2_deps_zero-20260914-004123.log |
| emdash3_2_one_cat_zero_cone_column_inputs | emdash3_2_one_cat_zero_cone_column_inputs-20260914-004023.log | nuh4c6c2_deps_columns-20260914-004130.log |
| one_cat_zero_cone_column_inputs | one_cat_zero_cone_column_inputs-20260914-003634.log | nuh4c6c2_deps_columns-20260914-004130.log |
| emdash3_2_one_cat_short_exact_family_lifts | emdash3_2_one_cat_short_exact_family_lifts-20260914-004031.log | nuh4c6c2_deps_lift-20260914-004138.log |
| one_cat_short_exact_family_lifts | one_cat_short_exact_family_lifts-20260914-003642.log | nuh4c6c2_deps_lift-20260914-004138.log |
| emdash3_2_one_cat_homology_covered_maps | emdash3_2_one_cat_homology_covered_maps-20260914-004038.log | nuh4c6c2_deps_covered-20260914-004145.log |
| emdash3_2_one_cat_native_homology_window_maps | emdash3_2_one_cat_native_homology_window_maps-20260914-004048.log | nuh4c6c2_deps_covered-20260914-004145.log |
| one_cat_native_homology_window_maps | one_cat_native_homology_window_maps-20260914-003649.log | nuh4c6c2_deps_covered-20260914-004145.log |

The affected earlier ρ-map, kernel-pullback and row-cancellation reviewers
pass with the new window imported in
nuh4c6c2_retained_consumers-20260914-004155.log.
The start baseline is one_cat_short_exact_family_cancellation-20260913-233937.log.
Owner-position view probes and all nine strict LHS audits pass. Catalog,
shell/Python syntax and source-only health pass (1043 registered files). Exact staged
scope and Markdown/link hygiene apply before checkpointing; no aggregate
is run. All original LP owners remain byte-identical to 2e3300c7.

**Next C6c3:** prove r/ρ epicity and θκ_ρ=0 at the actual new window.
Resolve required whole additive/normality/further-cover operations before
using them; no old per-arrow W/V dictionary or unconstructed general
PullbackStructure is a shortcut. Apply original coimage/cokernel descent
to obtain δ, then prove its reconstruction and output exactness. Concrete
model/reifier synthesis, the snake comparison and final qualification stay
required. The user-deferred Op/profile and spectral work remains deferred.

### NUH-4C6c1: Whole quotient/row cancellation and the canonical ρ map

**Implemented after 017a861d.** The cover route first needs whole quotient
cancellation and actual row reconstruction. This stage derives them from
the original native mates, then constructs the canonical map to the
original H. No ordinary IsEpic/kernel/cokernel factor dictionary is a
primary input and no cover property is assumed.

**Original cokernel observation.**

- The existing [image/coimage graph owner](../emdash2/emdash3_2_image_coimage_adjunction_families.lp)
  now also names q_D through the original quotient graph restriction.
  It requires only the original Q and D; no kernel selection is involved.
- The [native target observer](../emdash2/emdash3_2_one_cat_cokernel_family_projection_paths.lp)
  composes E₁ Hom action with the original family transpose. Literal native
  source/middle/target indices preserve its application beta. Unit
  restriction, the existing whole whiskering comparison, initial-family
  action and generic evaluation-composition give Λ_D(v)=v∘q_D.
- [Ambient reconstruction](../emdash2/emdash3_2_one_cat_cokernel_family_reconstruction.lp)
  gives descent(u,z)∘q_D=u and equality reflection through q_D. Distinct
  annihilation witnesses for the same u yield equal whole descents.

**Actual row and H consumers.**

The [row cancellation owner](../emdash2/emdash3_2_one_cat_short_exact_family_cancellation.lp)
derives κ_D∘β=i and γ∘q_F=g. Kernel/quotient reflection and the
[existing fixed-forward equivalence laws](../emdash2/emdash3_2_omega_equiv_cancellation_paths.lp)
then give incoming/outgoing cancellation for entire transformations.
The two inverse directions use their respective supplied left/right laws;
no extra inverse is selected. The original row evidence remains unchanged.

The [H quotient and cover-map owner](../emdash2/emdash3_2_one_cat_homology_cover_maps.lp)
restricts the same q to the original whole H boundary, derives q_H
cancellation and defines ρ=q_H∘r. This retains the original K(d∘p), r and
H. Its current parameters are the original coherent right-column h and p.
Producing those from the native window, proving r/ρ epicity, constructing θ
and deriving the required annihilation still remain. No splitting or
normality/epicity witness is added to the map constructor.

**Qualification.** Nineteen definitions across five new owners and one
existing-owner alias; no primitive, rewrite, unifier or nucleus edit.
All 23 assertions pass: 17 positive and six negative. They check the
original q component, native observer beta and Hom action, ambient
reconstruction, arbitrary quotient cancellation, independence from the
annihilation witness, the two original β/γ factorizations, both whole row
cancellation directions, q_H cancellation, actual ρ component and further
Hom action. They reject arbitrary equality and changed Q/p inputs.

All Lambdapi targets use the serial resource guard, warnings and ≤90-second
limits. Exact categories, locations, term heads, rule families and parser
diagnostics match unchanged dependencies. Counts are 1208 critical pairs /
159 pattern warnings for quotient/row owners and their reviewers, 1146 /
157 for generic equivalence cancellation, and 1381 / 159 for the ρ owner
and reviewer. The changed existing graph owner also exactly matches its
pre-edit warning inventory. No warning family is added or removed.

| Target | Passing log under emdash2/logs/probes | Unchanged dependency / pre-edit control |
| --- | --- | --- |
| emdash3_2_one_cat_cokernel_family_projection_paths | emdash3_2_one_cat_cokernel_family_projection_paths-20260913-233041.log | nuh4c6c1_deps_cokernel-20260913-233131.log |
| emdash3_2_one_cat_cokernel_family_reconstruction | emdash3_2_one_cat_cokernel_family_reconstruction-20260913-233048.log | nuh4c6c1_deps_cokernel-20260913-233131.log |
| one_cat_cokernel_family_reconstruction | one_cat_cokernel_family_reconstruction-20260913-232937.log | nuh4c6c1_deps_cokernel-20260913-233131.log |
| emdash3_2_omega_equiv_cancellation_paths | emdash3_2_omega_equiv_cancellation_paths-20260913-233054.log | nuh4c6c1_deps_equiv-20260913-233138.log |
| emdash3_2_one_cat_short_exact_family_cancellation | emdash3_2_one_cat_short_exact_family_cancellation-20260913-232629.log | nuh4c6c1_deps_row-20260913-233143.log |
| one_cat_short_exact_family_cancellation | one_cat_short_exact_family_cancellation-20260913-233115.log | nuh4c6c1_deps_row-20260913-233143.log |
| emdash3_2_one_cat_homology_cover_maps | emdash3_2_one_cat_homology_cover_maps-20260913-233059.log | nuh4c6c1_deps_cover-20260913-233149.log |
| one_cat_homology_cover_maps | one_cat_homology_cover_maps-20260913-233122.log | nuh4c6c1_deps_cover-20260913-233149.log |
| emdash3_2_image_coimage_adjunction_families | emdash3_2_image_coimage_adjunction_families-20260913-233110.log | emdash3_2_image_coimage_adjunction_families-20260913-214332.log |

Retained H-family, kernel-pullback and short-exact reviewers pass with both
new consumer owners imported in nuh4c6c1_retained_consumers-20260913-233159.log.
The start-of-tranche baseline is
one_cat_kernel_pullback_universality-20260913-230958.log.
All six source LHS audits, catalog, shell/Python syntax and source-only
health pass (1030 registered files). Exact source/staged-scope and
Markdown/link checks apply before checkpointing. No aggregate is run.

**Then-next C6c2, now qualified above:** native row action, column inputs
and ρ/θ assembly are constructed. Cover epicity/annihilation, δ and output
exactness remain, along with concrete model/reifier synthesis and snake
comparison. User deferrals stay in force.

### NUH-4C6b2b: Native cartesian comparison of the original kernel square

**Implemented after f388ed78.** For 𝒞=Functor_cat(B,C), retain the original
K, D, p:X⇒Y, L=K(d∘p), a₀=κ_(d∘p), κ_d and r:L⇒K(d). The existing
square κ_d∘r=p∘a₀ defines a slice arrow Σ_p(a₀)→κ_d. Its native Hom
comparison at an arbitrary original a:𝒞/X is now constructed and proved
invertible with the existing fixed-forward OmegaEquivAlong.

**Owners and trust boundary.**

- [Comparison](../emdash2/emdash3_2_one_cat_kernel_pullback_comparison.lp):
  original inclusion objects, native square arrow and the actual forward
  functor Φₐ, using Σ_p Hom action then postcomposition.
- [Lifts](../emdash2/emdash3_2_one_cat_kernel_pullback_lifts.lp): a native
  cone object gives one whole annihilation path; the original K mate gives
  its lift and reconstructs both original ambient legs.
- [Universality](../emdash2/emdash3_2_one_cat_kernel_pullback_universality.lp):
  actual inverse functor, object agreement, both recovered ambient legs,
  both whole inverse paths and constructed OmegaEquivAlong on Φₐ. No comparison inverse is postulated.
- [Native slice paths](../emdash2/emdash3_2_one_cat_slice_paths.lp): equality
  reflection is derived by Sigma elimination at the actual native Hom,
  using proposition-valued triangle fibres. The OneCat slice closure is
  an explicit structural/model primitive extending the opaque profile.
- [Core object maps](../emdash2/emdash3_2_groupoidal_object_maps.lp) and
  [discrete functor paths](../emdash2/emdash3_2_discrete_functor_paths.lp):
  existing core inversion/Path_map supplies automatic higher action, and
  the existing set-target transformation assembly supplies whole paths.
  Discrete-target functor closure is the second explicit profile primitive.
- [Slice action paths](../emdash2/emdash3_2_slice_sigma_arrow_paths.lp) and
  [ordinary postcomposition observation](../emdash2/emdash3_2_one_cat_functor_postcomposition_paths.lp):
  derive the actual underlying-arrow observation without new runtime rules.

The two profile closures are ordinary/discrete structural facts, not new
kernel, cartesian or inverse axioms. Their closed model implementations
remain NUH-5 obligations. The inverse functor's object action agrees with
the existing lift by a derived core-reflection path; it is not an extra
judgmental beta. Both full functor inverse laws are paths. General coherent
SliceBaseChange_catd/PullbackStructure over all base arrows is separate.
The original parameter category B, original K and diagrams are retained.

**Rejected shortcuts and computation findings.** A raw reflexivity check
for arbitrary Σ_p input does not expose its constructor action. Eliminating
the two native endpoint objects and arrow with sigma_ind derives the same
observation; no Sigma eta or projection rewrite is needed. Likewise a raw
postcomposition equation at an already normalized opposite source misses
the generic comparison. Stage the existing comparison before specialization,
then use fapp1_comp_path in the ordinary target. The earlier proposed
higher-Sigma filler route for slice equality was unnecessary:
constructor congruence and native-classifier motives suffice.

**Qualification.** Thirty-four definitions, two profile primitives, zero
runtime rules, zero unifiers, no nucleus edit. All 38 reviewer assertions
pass: 29 positive and nine negative. They cover arbitrary native slice
inputs, both original legs, fixed-forward evidence, selected inverse
projections, whole inverse laws and next Hom action; they reject changed
inputs, arbitrary equality, over-truncation and judgmental inverse/object
beta. The wrong-p negative is a typing rejection at its actual changed
source, not an ill-typed conversion comparison.

All checks use the serial resource guard, warning output and ≤90 seconds
per target. Exact warning inventories match categories, locations, term
heads, rule families and parser diagnostics against unchanged dependencies.
Counts are 1146 critical pairs / 157 pattern warnings for the core,
discrete, ordinary slice and functor-observation owners; 1317 / 157 for
slice postcomposition and its combined reviewer; and 1381 / 159 for the
kernel comparison/lifts/universality and its reviewer. The additional
baseline warnings in the latter joins come from the existing pullbacks
imports. No warning is introduced or removed by this tranche.

| Target | Passing log under emdash2/logs/probes | Unchanged dependency join |
| --- | --- | --- |
| emdash3_2_groupoidal_object_maps | emdash3_2_groupoidal_object_maps-20260913-225556.log | nuh4c6b2b_deps_core-20260913-225651.log |
| emdash3_2_discrete_functor_paths | emdash3_2_discrete_functor_paths-20260913-225603.log | nuh4c6b2b_deps_discrete-20260913-225656.log |
| discrete_functor_paths | discrete_functor_paths-20260913-225646.log | nuh4c6b2b_deps_discrete-20260913-225656.log |
| emdash3_2_one_cat_slice_paths | emdash3_2_one_cat_slice_paths-20260913-225609.log | nuh4c6b2b_deps_slice-20260913-225702.log |
| emdash3_2_slice_sigma_arrow_paths | emdash3_2_slice_sigma_arrow_paths-20260913-225614.log | nuh4c6b2b_deps_sigma-20260913-225709.log |
| emdash3_2_one_cat_functor_postcomposition_paths | emdash3_2_one_cat_functor_postcomposition_paths-20260913-225620.log | nuh4c6b2b_deps_functor-20260913-225714.log |
| emdash3_2_one_cat_kernel_pullback_comparison | emdash3_2_one_cat_kernel_pullback_comparison-20260913-225624.log | nuh4c6b2b_deps_kernel-20260913-225719.log |
| emdash3_2_one_cat_kernel_pullback_lifts | emdash3_2_one_cat_kernel_pullback_lifts-20260913-225632.log | nuh4c6b2b_deps_kernel-20260913-225719.log |
| emdash3_2_one_cat_kernel_pullback_universality | emdash3_2_one_cat_kernel_pullback_universality-20260913-230522.log | nuh4c6b2b_deps_whole-20260913-225727.log |
| one_cat_kernel_pullback_universality | one_cat_kernel_pullback_universality-20260913-230531.log | nuh4c6b2b_deps_whole-20260913-225727.log |
| one_cat_slice_paths | one_cat_slice_paths-20260913-225640.log | nuh4c6b2b_deps_slice_join-20260913-225919.log |

The retained original reconstruction and short-exact reviewers also pass
with the new modules imported: nuh4c6b2b_retained_consumers-20260913-225735.log. The recovery baseline was
nuh4c6b2b_discrete_functors-20260913-224009.log; the preceding committed
reconstruction baseline was one_cat_kernel_family_reconstruction-20260913-215639.log.
Strict LHS audits report zero candidates in the eight new owners. Catalog,
source-only health (1022 registered files), syntax/document/link hygiene and
exact staged-scope checks pass; no aggregate is run.

**Then-next C6c:** C6c1 above now supplies quotient/row cancellation and
the canonical ρ map. Native window assembly, r/ρ epicity, θ/δ, output
exactness, concrete model/reifier synthesis and snake comparison remain
required. All user deferrals stay in force.

### NUH-4C6b2a: Whole source projection and original kernel reconstruction

**Implemented after 8db57db1.** The
[Hom-action views](../emdash2/emdash3_2_hom_action_factorization_views.lp)
add four proof-time comparisons: the next-Hom functors of the two existing
Hom_func factorizations, the raw Cat triple-composition point view, and
its identity-middle projection-order companion. Every relevant endpoint
arrow, input object and intermediate image is retained. These complete
comparison of existing owners; they install no runtime distribution.

The [ordinary whiskering owner](../emdash2/emdash3_2_one_cat_whiskering_paths.lp)
has four derived paths. The two next-Hom composites use the common native
Hom endpoints explicitly, so applying their functor equality computes.
Applying them to the original transformation gives whole pre/postwhiskering
agreement. A Cat-specialized raw-parent view then applies at the actual
counit. This publishes the ordinary-target qualification and asserts no
general lax/oplax interchange theorem.

The [kernel projection owner](../emdash2/emdash3_2_one_cat_kernel_family_projection_paths.lp)
has seven definitions. Γ_D is an actual functor: source-evaluation Hom
action after the original native inverse mate. Its native source, middle
and target categories are retained literally in the composition and
applications. Its beta returns the complete source observation. Whiskering
agreement identifies the counit source with the original restricted κ;
generic evaluation of composition and the original J action then prove
Γ_D(v)=κ_D∘v for a whole transformation v.

The [reconstruction owner](../emdash2/emdash3_2_one_cat_kernel_family_reconstruction.lp)
has three derived paths. It reconstructs k after the original lift, reflects
equality through κ_D using existing inverse-mate faithfulness, and proves
κ(d)∘r=p∘κ(d∘p) for the existing kernel-precomposition family. The
generic restricted inclusion is one new definition in the
[image/coimage family owner](../emdash2/emdash3_2_image_coimage_adjunction_families.lp).
The old first projection delegates to this alias with unchanged computation.
No K/D choice, diagram object or H selection changes.

Fifteen definitions and four unifiers add no primitive, runtime rule,
nucleus edit, caller naturality premise or ordinary universal dictionary.
The Γ equation concerns whole v; it is not a separately asserted equality
of the complete Γ functor with a postcomposition functor.

The earlier direct-reflexivity counit comparison and the path-to-identity
component route are retained in ignored C6b2 probes. They were not promoted.
The working route uses the existing rigid Hom owner as the common functor.
Applying equal functors with foreign, merely proof-time-compatible
codomain annotations hid generic composition beta. Choosing literal native
Hom indices resolves that measured failure without modifying generic
application/composition rules. The middle-identity test separately required
the fourth view because raw composition had erased one factor.

Final serial, resource-guarded checks (each ≤90 seconds), under
emdash2/logs/probes/:

| Target | Final log |
| --- | --- |
| Hom-action views | emdash3_2_hom_action_factorization_views-20260913-214309.log |
| Whole whiskering paths | emdash3_2_one_cat_whiskering_paths-20260913-214314.log |
| Native Γ and projection paths | emdash3_2_one_cat_kernel_family_projection_paths-20260913-214319.log |
| Ambient reconstruction and square | emdash3_2_one_cat_kernel_family_reconstruction-20260913-214325.log |
| Shared inclusion owner | emdash3_2_image_coimage_adjunction_families-20260913-214332.log |
| Retained first projection | emdash3_2_one_cat_kernel_precomposition-20260913-214337.log |
| Hom/whiskering reviewer | one_cat_whiskering_paths-20260913-214344.log |
| Kernel reconstruction reviewer | one_cat_kernel_family_reconstruction-20260913-214349.log |
| Retained lift, precomposition, product, image-kernel and short-exact reviewers | nuh4c6b2a_retained_consumers-20260913-214414.log |

There are 22 assertions: 16 positive and six negative. They check both
next-Hom views, all three identity corners of the Cat point view, retained
raw/runtime distinction, rejection of changed D/V/F/alpha, native Γ beta
and Hom action, lift reconstruction, equality reflection at two supplied
annihilation witnesses, the original first projection, the actual whole
square and its component, and rejection of an unrelated p.

Exact dependency warning inventories match in categories, locations,
term heads, participant-rule families and parser diagnostics:
1146 / 157 for Hom views, 1151 / 157 for whiskering and its reviewer, and
1208 / 159 for kernel projection/reconstruction and its reviewer. The
matching joins are nuh4c6b2a_deps_views-20260913-214356.log,
nuh4c6b2a_deps_whiskering-20260913-214402.log and
nuh4c6b2a_deps_kernel-20260913-214408.log. No warning is added or removed.
The pre-edit baseline was
one_cat_kernel_precomposition-20260913-202330.log.

Strict source audits, catalog freshness, shell syntax and source-only
health pass; registration contains 1011 files. Exact source/prototype,
Markdown/link and staged-scope checks apply before checkpointing. Only
localized checks are run; the nucleus remains unchanged.

**Then-next C6b2b, now qualified above:** construct the native cartesian
universal comparison for the original square, with complete inverse/action and both
legs retained. That native comparison is now constructed above. The epic
cover/δ, output exactness, concrete model/reifier synthesis and snake
comparison remain required.

### NUH-4C6b1: Whole kernel lifting and precomposition maps

**Implemented after 32518b25.** The actual connecting pullback has the
kernel inclusion of d as one leg. Its semantic carrier can be K(d∘p), by
the kernel-as-zero-pullback description and pullback associativity. The
categorical subplan records the source and distinguishes this argument
from the pending native cartesian proof.

The [kernel-family input owner](../emdash2/emdash3_2_one_cat_kernel_family_inputs.lp)
has six definitions. It forms Arr(d∘p) before a kernel is selected, adds the
forward whole reconstruction at the original D, constructs J(X)⇒D from
one whole annihilation cell, and derives source recovery. Existing native
square action in Functor_cat(B,C), exchange and the accepted terminal/shape
presentations do the assembly. No per-object naturality field is supplied.

The [kernel lift owner](../emdash2/emdash3_2_one_cat_kernel_family_lift.lp)
has three definitions. The original native mate gives X⇒K(D); its inverse
returns the complete input. Source evaluation recovers k, and the existing
whole inverse-mate faithfulness proves uniqueness. The reviewer specializes
this uniqueness to two annihilation witnesses, proving the same whole lift.
The same actual D and K remain in all operations.

The [precomposition owner](../emdash2/emdash3_2_one_cat_kernel_precomposition.lp)
has five definitions. It applies K to the introduced composite diagram,
retains the original restricted kernel inclusion a:L⇒X, derives
d∘p∘a=0 from the existing whole annihilation, and lifts p∘a into K(D).
The output r:L⇒K(D) is a constructed whole transformation. Its native
inverse-mate source recovers p∘a. The code does not yet state the ambient
κ_D∘r equation or a cartesian universal comparison.

Fourteen definitions add no primitive, rewrite, unification rule, ordinary
universal dictionary, model capability or kernel choice. Both existing
OneCat shape/terminal qualifications and all user deferrals remain.

Final serial, resource-guarded checks (each ≤90 seconds), under
emdash2/logs/probes/:

| Target | Final log |
| --- | --- |
| Input/precomposed diagram owner | emdash3_2_one_cat_kernel_family_inputs-20260913-200952.log |
| Whole lift and paths | emdash3_2_one_cat_kernel_family_lift-20260913-201051.log |
| Kernel-precomposition maps | emdash3_2_one_cat_kernel_precomposition-20260913-201057.log |
| Lift reviewer | one_cat_kernel_family_lift-20260913-201106.log |
| Precomposition reviewer | one_cat_kernel_precomposition-20260913-201112.log |
| Product views loaded before new kernel, retained cokernel and short-exact reviewers | nuh4c6b_retained_consumers-20260913-201137.log |

The reviewers have 22 assertions: 20 positive and two negative. They cover
complete native input recovery, original K(D) observations, forward
reconstruction endpoints, independence of the annihilation witness,
whole/point/next-Hom action, original composite endpoints/differential,
the derived annihilation and rejection of unrelated k/p data.

All three sources and both reviewers exactly match their unchanged
dependency joins at 1208 critical pairs / 159 replaceable-pattern warnings.
The baseline joins are nuh4c6b_dependencies_inputs-20260913-201118.log,
nuh4c6b_dependencies_lift-20260913-201124.log and
nuh4c6b_dependencies_precomposition-20260913-201131.log. Categories,
locations, term heads, participant-rule families and parser diagnostics
all match, with no added or removed warning. The fresh pre-edit product
reviewer passed in one_cat_product_families-20260913-195307.log.

Strict source LHS audits, catalog freshness, shell syntax and source-only
health pass; 1005 files are registered. Final exact staging and changed
Markdown/link checks apply before checkpointing. The nucleus is unchanged;
no TypeScript or repository-wide typecheck is run.

**Next C6b2:** derive the whole comparison Γ_D(v)=κ_D∘v for source
evaluation Γ after the native inverse mate. Then construct the cartesian
universal comparison using existing native slice-Hom/cone interfaces,
with whole inverse/action and both original legs retained. The carrier
L and r are currently kernel-precomposition data; their formal pullback
universality, epic cover/δ, output exactness, model/reifier synthesis and
snake comparison remain required.

### NUH-4C6a: Whole product pairing and native inverse action

**Implemented after 720807ee.** Three new one-way owners provide the
product prerequisite for the connecting cover:

- [product-family views](../emdash2/emdash3_2_product_family_views.lp):
  the defined diagonal, a derived product-component path and nine sufficient
  proof-time comparisons;
- [ordinary product presentation](../emdash2/emdash3_2_one_cat_product_adjunction.lp):
  two explicit structural primitives and two unit/counit coupling rules;
- [whole family pairing](../emdash2/emdash3_2_one_cat_product_families.lp):
  four defined pair/unpair operations and two derived whole/component paths.

The ordinary product-category profile and Δ⊣P at the original P/BP are
structural/model obligations, not theorems derived from today's opaque
classifier β interface. The whole counit retains the original π₁/π₂;
the unit components retain the original diagonal pairing. Native family
mates construct the pair/unpair functors, and their original inverse cuts
recover whole inputs and further Hom action. No replacement P is selected.

The component agreement follows from the existing whole mate formula,
a paired-component view and the original product-action comparison/cuts.
The two original selected projections consequently recover the original
f/g components. The runtime counit constructor retains native projected
endpoint annotations; its two whole projections return the original
projection transformations. Native indices inside mate applications and
the original explicit input-pair annotations are likewise retained.

The nine unifiers comprise four projected raw/native diagonal comparisons,
two sufficient projected-composition comparisons, two constant-coordinate
views and one whole paired-component view. They compare all relevant
functors, cells, endpoints and parameters. Composite and constant input
tests preserve the existing runtime forms; unrelated factors, coordinates
and cells are rejected. The generic product-component path supplies the
underlying projection/path semantics without new naturality input.

The earlier raw/native diagonal runtime-fold experiment and its eight
overlaps are not installed. Its evidence and the rejected first proof-time
variant are preserved in checkpoint 720807ee and the ignored C6a probes.
The successful refinement omits unnecessary inferred arguments in projected
unifiers and emits an explicit equality obligation for the retained functor.
A direct view at the paired-component owner avoids rebuilding caller
naturality data or adding runtime distribution/eta rules.

Final serial, resource-guarded checks (each ≤90 seconds), all under
emdash2/logs/probes/:

| Target | Final log |
| --- | --- |
| Product-family views | emdash3_2_product_family_views-20260913-194128.log |
| Product adjunction | emdash3_2_one_cat_product_adjunction-20260913-194947.log |
| Whole pairing and paths | emdash3_2_one_cat_product_families-20260913-194208.log |
| Generic view reviewer | product_family_views-20260913-194214.log |
| Whole product reviewer | one_cat_product_families-20260913-194219.log |
| Retained product, family-adjunction and short-exact reviewers with new owners loaded | nuh4c6_retained_consumers-20260913-194238.log |

The two reviewers have 37 assertions: 28 positive and nine negative.
Views/source and its reviewer exactly match the dependency-only join
nuh4c6_final_dependency_views-20260913-194225.log at 1146 critical pairs /
157 replaceable-pattern warnings. Both product sources and their reviewer
match nuh4c6_final_dependency_family-20260913-194230.log at 1214 / 167.
Categories, locations, term heads, participant-rule families and parser
diagnostics all match, with no added or removed warning. The fresh pre-edit
dependency baseline passed in
nuh4c6_product_dependencies-20260913-191824.log.

Strict rule-LHS audits, catalog freshness, shell syntax and source-only
health pass; registration now contains 1000 files. The nucleus is unchanged.
Final document/link hygiene and exact staging are required before the
checkpoint. No TypeScript or repository-wide typecheck is run.

**Next C6b:** construct the whole fibre-product family and its projections
through the original categorical product and K/Q owners. Whole addition
and a derived PullbackStructure are not silently supplied by C6a. The
cover/covered map, δ descent, output exactness, model/reifier synthesis and
snake comparison remain required. All user deferrals remain in force.

### NUH-4C5: Whole short-exact row comparisons and inverses

**Implemented after bb83a8b0.** The existing
[whole zero-family path owner](../emdash2/emdash3_2_one_cat_zero_family_paths.lp)
adds one derived g∘f=0 path for the original h:J∘A⇒D. Exchange puts h in
WalkingArrow→Functor_cat(B,C); the existing ordinary naturality theorem
and initial-family uniqueness prove the equation. The incoming native parent
view is compared through the existing sufficient whole-evaluation congruence.
No additional zero/naturality input is requested, and no rule is added.

The eight-definition
[short-exact-family owner](../emdash2/emdash3_2_one_cat_short_exact_families.lp)
constructs γ:Q(f)⇒E₁D by the original whole descent. Its native inverse mate
recovers the complete coherent input, and whole target reconstruction
returns the original outgoing g. The original kernel mate β is the existing
H boundary, with no replacement program or selection.

OneCatShortExactFamily is the product of existing OmegaEquivAlong evidence
on these actual β and γ. Its constructor/projections retain both supplied
witnesses. Whole inverse operations select their existing left inverse
candidates. The already proved inverse-candidate law supplies each other
inverse equation. In particular γ⁻¹:E₁D⇒Q(f) does not select a section into
E₀D; non-split rows are not excluded by this interface. No global normality
input is needed merely to define the kernel-cokernel pair.

There are 22 new assertions: constructor/evidence retention, both whole
inverse equations for both maps, their component and Hom/next-Hom actions,
rejection of evidence on unrelated maps, rejection of the incorrect middle-
term target for γ⁻¹, native whole input cancellation, reconstruction of g,
and the original Q(f) point plus whole/next-Hom reconstruction observations.
No primitive, rewrite, unifier, object cast or ordinary universal dictionary
is introduced. This package supplies the short-exact input condition; it
is not a proof of LES exactness or a construction of concrete row evidence.

Final warning-enabled, serial resource-guarded checks use ≤90 seconds per
target. Source logs are `emdash3_2_one_cat_zero_family_paths-20260913-183247.log`
and `emdash3_2_one_cat_short_exact_families-20260913-183251.log`; the complete
reviewer passes in `one_cat_short_exact_families-20260913-183124.log`, all under
`emdash2/logs/probes/`. Retained exactness and comparison consumers pass in
`one_cat_categorical_exactness-20260913-183303.log` and
`one_cat_image_kernel_comparison-20260913-183308.log`. The pre-edit exactness
baseline passed in `one_cat_categorical_exactness-20260913-181946.log`.

The new source and reviewer match their same-order dependency-only joins
`nuh4c5_dependencies-20260913-183255.log` and
`nuh4c5_reviewer_dependencies-20260913-183259.log` exactly at 1208 critical
pairs / 159 replaceable-pattern warnings. Categories, source locations,
term heads, participant-rule families and parser diagnostics all match.
Both edited/new sources pass strict rule-LHS audits (no clauses added).
Strict catalog freshness, shell syntax, active-reference/header lint and
source-only health pass (995 registered files, with no aggregate checker
run). Changed Markdown links, source/prototype agreement and the exact
staged scope are checked before checkpointing. No TypeScript or repository-
wide typecheck is run.

C6 next forms the whole fibre-product family and its projections for the
connecting cover. The cover/covered map, its universal descent, derived
output exactness, retained-model comparisons, model/reifier automation and
the snake comparison remain required. The goal stays active and all user
deferrals remain unchanged.

### NUH-4C4b: Canonical whole image-to-kernel comparison and exactness

**Implemented after 917a2981.** Nineteen new definitions across five new
one-way modules and the existing evaluator owner construct the actual
whole comparison. Four proof-time comparisons add no runtime rewrite,
primitive, nucleus edit, caller coherence field or replacement selection.

- [Incoming observations](../emdash2/emdash3_2_zero_arrow_family_observations.lp)
  define f=E₀(h) and F=Arr(f) before K/Q selection. Native parent annotations
  are retained inside the projection; point observations recover the same h.
- [Whole zero paths](../emdash2/emdash3_2_one_cat_zero_family_paths.lp) transport
  canonical zero and annihilation by prewhiskering, using whole initial/
  terminal uniqueness and generic action. They require no new additive
  structure on the functor category.
- [Kernel-family restriction paths](../emdash2/emdash3_2_one_cat_kernel_family_restriction_paths.lp)
  align the whole zero view, restrict original counit annihilation, reconstruct
  the actual H boundary under inverse mating, reflect projected annihilation,
  and prove β∘κ_F=0. The existing raw H boundary is retained literally.
- [Image-to-kernel comparison](../emdash2/emdash3_2_one_cat_image_kernel_comparison.lp)
  descends β at the original Arr(κ)∘F and composes with the same selected
  a_F inverse. The six definitions include e∘a_F=β̄, native inverse-mate
  reconstruction of both sides to the original β, and uniqueness from whole
  reconstruction. Components and higher action are observations of these
  whole terms, not rebuilt pointwise maps.
- [Categorical exactness](../emdash2/emdash3_2_one_cat_categorical_exactness.lp)
  is existing OmegaEquivAlong at this actual e. The native zero-cone
  specialization is a whole transformation on its existing category and
  tautological input. No exactness inhabitant is declared; the whole map on
  all zero-cones is not asserted invertible.

The evaluator gains a proof-time shape-arrow/prewhiskering comparison and
two defined paths with OneCat(C) explicit. The comparison retains both
family factors, endpoint evaluations and the original shape arrow. The
family-view owner gains constant precomposition, guarded congruence for a
composite of two shape-arrow observations, and represented outer associativity
Q∗(G∘F) ≐ (Q∘G)∘F. The first legitimately forgets the precomposing map while
retaining the constant's value; the others compare all corresponding data.
Guarding both shape-map operands preserves generic associativity when an
operand is itself a composite. These are sufficient comparisons, not
mathematical injectivity or new constructor-specific naturality laws.
The qualification is the ordinary target; general lax/oplax interchange and
profile migration are not settled by these consumers.

Important failed/refined probes:

- `nuh4c4_whiskered_zero-20260913-170006.log` exposed native precomposition of
  a constant versus the literal constant-family view; the narrow comparison
  resolved it (`170139`).
- `nuh4c4_kernel_family_annihilation-20260913-170336.log` used generic action
  with native evaluation parents. Cat-specific prewhiskering removed those
  failures (`170746`) without adding a native evaluation rewrite. The
  remaining zero view was derived by initial-family uniqueness; guarded
  composition comparison handled its endpoint annotations (`171252`).
- The actual boundary annihilation passed in `171845`, and the complete
  comparison in `172314`. Native indices must remain inside IsoEvidence
  projections: using raw endpoints before elimination failed in
  `nuh4c4_image_kernel_paths-20260913-172740.log`; preserving the original
  indices passed in `172931`.
- Native coimage reconstruction exposed the represented outer associativity
  comparison (`nuh4c4_image_kernel_characterization-20260913-173322.log`);
  its qualified companion passed the complete characterization in `173744`.
- The first direct incoming point conversion used raw parent annotations;
  the maintained reviewer uses the actual native parent and recovers the
  same original h. This was a view correction, not a changed incoming map
  or a proof of a new raw judgmental equality.

There are 34 new assertions: twelve typed comparison/identity/noncollapse
controls in the existing owner reviewers, six incoming-observation controls,
ten complete comparison/reconstruction/action controls and six exactness/
zero-cone controls. The latter reject evidence about an unrelated map and
obtain point evidence only by evaluating supplied whole evidence. Exactness
is not inferred from K/Q or from normality alone.

All checks are warning-enabled, serial and resource-guarded, with ≤90
seconds per target. Final source logs under `emdash2/logs/probes/` are:

| Owner | Log |
| --- | --- |
| Evaluator and new shape views | `emdash3_2_diagram_evaluation-20260913-180712.log` |
| Family proof-time views | `emdash3_2_one_cat_adjunction_family_views-20260913-180718.log` |
| Incoming observations | `emdash3_2_zero_arrow_family_observations-20260913-180721.log` |
| Whole zero prewhiskering | `emdash3_2_one_cat_zero_family_paths-20260913-180724.log` |
| Whole kernel restriction/annihilation | `emdash3_2_one_cat_kernel_family_restriction_paths-20260913-180728.log` |
| Complete comparison | `emdash3_2_one_cat_image_kernel_comparison-20260913-180732.log` |
| Exactness interface/zero-cone specialization | `emdash3_2_one_cat_categorical_exactness-20260913-180737.log` |

Final reviewers are `zero_arrow_family_observations-20260913-180356.log`,
`one_cat_image_kernel_comparison-20260913-180251.log` and
`one_cat_categorical_exactness-20260913-180439.log`. The extended existing
owner reviewers pass in `diagram_evaluation-20260913-180932.log` and
`one_cat_adjunction_family_views-20260913-180935.log`. Retained descent and
canonical Coim⇒Im consumers pass in `one_cat_cokernel_family_descent-20260913-180938.log`
and `one_cat_image_coimage_comparison-20260913-180942.log`.

The evaluator matches its exact HEAD owner copy
`nuh4c4b_eval_baseline-20260913-180709.log` at 1150 critical pairs / 157
replaceable-pattern warnings. The family views match
`nuh4c4b_family_views_baseline-20260913-180715.log` at 1151/157. Only the
temporary source path is normalized for these comparisons; no warning
family or source-local diagnostic is omitted. Complete comparison and
exactness source/reviewers match their same-order dependency joins
`nuh4c4b_comparison_dependencies-20260913-180946.log` and
`nuh4c4b_exactness_dependencies-20260913-180950.log` exactly at 1208/159.
Every comparison covers categories, locations, term heads, participant
families and parser diagnostics.

All seven changed/new source owners pass strict LHS audits. Strict catalog
freshness, shell syntax, active-reference/header lint and generated source-
only health pass (993 registered files; no aggregate checker run). The
staged diff, source scope and changed links are checked before checkpointing.
No TypeScript or repository-wide typecheck is run. The proof-time rule
controls also passed at both full temporary owners before promotion in
`nuh4c4_rule_controls-20260913-174729.log`.

**Historical C4b boundary, advanced by C5 above:** construct the actual whole cokernel row comparison γ alongside the
existing kernel mate β, then packages their fixed-map invertibility as the
short-exact-family interface. Whole cover/covered-map/δ, its derived exactness,
concrete model/reifier automation and the snake comparison remain required.
The corresponding formal comparisons with the retained H-zero/ordinary
exactness views are still obligations for their actual consumers. The goal
stays active, with all user deferrals unchanged.

### NUH-4C4a: Whole cokernel descent at the original diagram family

**Implemented after 65faa183.** The two new owners contain nine definitions.
The [input owner](../emdash2/emdash3_2_one_cat_cokernel_family_inputs.lp)
defines canonical whole zero, introduced input, family reconstruction,
original-family input and both whole target observations (six definitions).
Its imports require no kernel/cokernel structure. The three-definition
[descent owner](../emdash2/emdash3_2_one_cat_cokernel_family_descent.lp)
then introduces the cokernel adjunction, applies the native mate, and proves
reconstruction and uniqueness. No primitive, runtime rule,
unifier, ordinary universal record or replacement selection is introduced.

The introduced case reuses the native square in Functor_cat(B,C), exchange
and the accepted initial-family normalizer. A single whole z:u∘k=0 supplies
its internal cell. The arbitrary-family case uses the existing reconstruction
inverse at Sym(D) in Functor_cat(B,C), with its existing OneCat profile.
Exchanging back gives ρ_D:D⇒Arr(∂D) with identity whole endpoints.
The resulting h:D⇒I∘Y therefore retains u as its entire target. The
cokernel mate is evaluated at D itself, not at Arr(∂D). This is the
retained-selection boundary needed by later exactness and δ.

Native inverse cancellation returns the full h, including its reconstruction
data. Whole target reconstruction gives E₁(transpose_Q(desc))=u. Existing
projected cokernel-mate faithfulness proves uniqueness against a competing
whole map with that same reconstruction. The zero cell and comparison
proofs are whole internal data; no per-object naturality/functoriality
premise is added to the formal program.

The canonical Coim⇒Im input and its whole target proof now delegate to the
introduced constructor and its view. Exact comparison with the original
source bodies confirms unchanged computation for both. Canonical a and its
inverse/normality interfaces continue to pass; this is sharing an existing
program, not substituting an isomorphic selected input.

There are 16 new assertions: seven for both reconstruction endpoints, their
parameter Hom action, whole u recovery and noncollapse; nine for whole native
cancellation, original Q(D(b)) endpoints, reconstruction/uniqueness, wrong-
input rejection, raw whole-formula agreement, components, arbitrary base
arrows and the next Hom functor with its retained endpoints. One reviewer
helper derives raw-formula agreement through the existing family mate view.
All operations remain internal transformations with the B-action retained.

Final warning-enabled, serial resource-guarded checks (≤90 seconds each)
are recorded under `emdash2/logs/probes/`:

| Target | Log |
| --- | --- |
| Input source | `emdash3_2_one_cat_cokernel_family_inputs-20260913-165316.log` |
| Descent source | `emdash3_2_one_cat_cokernel_family_descent-20260913-165320.log` |
| Input reviewer | `one_cat_cokernel_family_inputs-20260913-165324.log` |
| Descent reviewer | `one_cat_cokernel_family_descent-20260913-165327.log` |
| Exact old/new input and proof conversion | `nuh4c4_old_input_conversion-20260913-165331.log` |
| Initial introduced-input specialization | `nuh4c4_input_specialization-20260913-164116.log` |
| Retained full comparison/characterization | `one_cat_image_coimage_comparison-20260913-165336.log` |
| Retained fixed-a normality/inverse | `one_cat_adjunction_normality-20260913-165344.log` |
| Input dependency-only join | `nuh4c4_inputs_dependencies-20260913-165210.log` |
| Descent dependency-only join | `nuh4c4_descent_dependencies-20260913-165214.log` |
| Descent reviewer dependency-only join | `nuh4c4_descent_reviewer_dependencies-20260913-165218.log` |

Sources and reviewers match the appropriate dependency-only joins exactly
at 1208 critical pairs / 159 replaceable-pattern warnings. Retained comparison
and normality match the pre-edit normality baseline `162714` exactly too.
The comparisons include categories, locations, term heads, participant-rule
families and parser diagnostics. No new warning or source-local warning is
hidden by counts. The old/new conversion probe retains the literal prior
source bodies and checks both the shared input and its target proof by
conversion; all public types and the original canonical a body are unchanged.

The input owner's 35-module import closure contains no kernel/cokernel
module; the whole structure first enters at descent. All three edited/new
sources pass the strict LHS audit (no clauses added).
Strict catalog freshness, shell syntax, active-reference/header lint and
source-only health pass (985 registered files; no aggregate typecheck).
Changed Markdown links, exact staged scope and whitespace are checked before
the local checkpoint. No TypeScript or repository-wide checker is run.

**Historical C4a boundary, resolved by C4b above:** derive the whole kernel mate's annihilation at the incoming
arrow family. The preserved experiment
`nuh4c4_family_differential_reindex_candidate.lp` passes two whole evaluation/
prewhiskering views against the full temporary owner
`nuh4c4_differential_reindex_owner.lp`; the earlier direct view failed in
`nuh4c4_family_differential_view-20260913-163105.log`. At C4a this proposed proof-time
comparison was not installed; C4b above qualifies its refined form. It compares original family factors, endpoint
evaluations and the shape arrow; an actual restricted-κ consumer and full
SOP qualification remain required before promotion. Keep all active
runtime and unification owners unchanged for this C4a checkpoint.

At C4a the canonical Im(f)→K(g), categorical exactness and δ were unfinished;
concrete model/reifier work and the snake comparison are still required.
The active goal and all user deferrals are unchanged.

### NUH-4C3: Fixed-comparison normality and native Abelian structure

**Implemented after 61b3158d.** The four-definition
[normality owner](../emdash2/emdash3_2_one_cat_adjunction_normality.lp)
uses the existing OmegaEquivAlong at the actual whole a:Coim⇒Im. It defines
the selected whole inverse, an ordinary whole IsoEvidence view with forward
arrow literally a, and restriction to an arbitrary whole diagram family.
Existing generic functor action owns the latter and its inverse projections.
No new operation-specific naturality or functoriality rule is introduced.

OmegaEquivAlong stores supplied left/right inverse candidates. The inverse
operation selects its existing left candidate. The equality-evidence
extension already has `omega_equiv_left_as_right_law`, which derives its
second law through the comparison of those candidates. The initial probe
reproved that lemma; it remains ignored and is not promoted. Both equations
are proved paths, not new judgmental cuts or a stronger DefIso assumption.

The five-definition
[Abelian owner](../emdash2/emdash3_2_one_cat_abelian_adjunctions.lp)
is additional structure on the original AdditiveCategory A, OneCat(C) and
initial presentation at t. A retains the whole binary-product functor,
preadditivity and terminal structure. The dependent Sigma stores whole P/Q
and normality of their actual comparison. Its constructor and projections
retain those structures literally; it introduces no W/V dictionaries.
This meets the usual additive + kernels/cokernels + canonical-comparison
criterion in [Stacks 12.5.1](https://stacks.math.columbia.edu/tag/00ZX).
Normality is supplied structure, not a theorem from K/Q existence or a
closed concrete provider. No comparison with old normality families or
concrete model synthesis is claimed by this package.

There are 18 reviewer assertions. Twelve cover retained forward/inverse,
both whole inverse equations, rejection of unrelated forward/inverse maps,
actual component evidence, and family restriction through whole and next
Hom action. Six cover package projections, unchanged H application and
rejection of a different selected kernel or evidence about a different map.
All nine definitions are transparent. No primitive, rewrite, unifier,
nucleus edit, object cast or new caller coherence field is added.

All checks used serial warning-enabled resource-guarded invocations, each
bounded to 90 seconds. Source logs are
`emdash3_2_one_cat_adjunction_normality-20260913-162013.log` and
`emdash3_2_one_cat_abelian_adjunctions-20260913-162017.log`; final reviewers
are `one_cat_adjunction_normality-20260913-162601.log` and
`one_cat_abelian_adjunctions-20260913-162339.log`, under
`emdash2/logs/probes/`. The C2c4 baseline reviewer also passes in
`one_cat_image_coimage_comparison-20260913-161233.log`.

Normality source/reviewer match their exact ordered dependency join
`nuh4c3_normality_dependencies-20260913-162030.log` at 1208 critical pairs /
159 replaceable-pattern warnings. The additive package source/reviewer
match `nuh4c3_abelian_dependencies-20260913-162034.log` at 1280/169.
Categories, locations, term heads, participant families and parser diagnostics
all agree; the larger package inventory is inherited from the additive
join, with no source-local or new warning. Rule audits find no clauses to
review. Strict catalog freshness, shell syntax, active-reference/header lint
and generated source-only health pass (981 registered files, no aggregate
checker run). Changed links and the exact staged diff are checked before
checkpointing. No TypeScript or repository-wide typecheck is run.

C4a above supplies general descent; C4b next constructs e:Im(f)⇒K(g) on whole native zero-family inputs by
cokernel descent of the actual kernel mate and the restricted a⁻¹. The
subplan fixes that route. C4 reconstruction/action, exactness, whole δ,
concrete model/reifier work and the snake comparison remain required.
The goal is active; deferred Op/profile/terminality work is unchanged.

### NUH-4C2c4: Canonical whole comparison and its characterization

**Implemented after c1a79176.** The canonical a:Coim⇒Im is a defined whole
transformation using the original K/Q structures. There are no new
primitives, ordinary-factor program inputs, object casts or changed H
selections. Five new one-way owners supply 24 definitions:

- [zero-arrow action paths](../emdash2/emdash3_2_zero_arrow_family_action_paths.lp):
  three composition/embedding observations, with one protected generic helper;
- [terminal-family paths](../emdash2/emdash3_2_one_cat_terminal_family_paths.lp):
  two whole initial/terminal uniqueness consequences of the existing normalizers;
- [diagram-family paths](../emdash2/emdash3_2_one_cat_diagram_family_paths.lp):
  whole endpoint reflection and the two one-endpoint universal test cases;
- [kernel/cokernel-family paths](../emdash2/emdash3_2_one_cat_kernel_cokernel_family_paths.lp):
  eight native projection-faithfulness, structural, annihilation,
  precomposition and zero observations;
- [image/coimage comparison](../emdash2/emdash3_2_one_cat_image_coimage_comparison.lp):
  eight definitions for u reconstruction/annihilation, its coherent mate
  input, a, input-target recovery and whole factorization/uniqueness.

Whole diagram reflection exchanges into WalkingArrow→Functor_cat(B,C),
applies the original OneCat diagram reflection, and exchanges back. Its
premises compare entire endpoint transformations. Whole initial/terminal
uniqueness removes the unused endpoint premise for J∘A⇒D and D⇒I∘A.
Original native inverse cuts then give faithfulness of the projected mates.
The original counit and generic naturality derive ∂∘κ=0, and the dual unit
proves q∘∂=0. Projected kernel mating respects whole precomposition and
zero. Together with E₀(unmate_P(u))=∂, faithfulness derives u∘κ=0.

The resulting cell forms one existing native square **in Functor_cat(D,C)**.
Its realization, exchange and the original initial-family normalizer
construct h_a:Arr(κ)⇒I∘Im. Cokernel untransposition defines a. Native
transposition computes back to the whole h_a, and E₁(h_a)=u is proved as a
whole path. No componentwise naturality/functoriality proof is supplied as
program data. The accepted ordinary shape/family presentations and the
lifted adjunction remain explicit primitives/model obligations; no arbitrary
higher lax interchange is claimed.

The transparent function fact(b)=E₀(unmate_P(E₁(transpose_Q(b)))) satisfies
fact(a)=∂, and projected mate faithfulness proves fact(b)=∂ ⇒ b=a. This is
whole factorization/uniqueness; it is not a separately packaged internal
functor in b or a new runtime factorization cut. The actual a is a whole
internal transformation with original parameter and Hom action.

Four runtime clauses are added at the
[introduced-arrow owner](../emdash2/emdash3_2_arrow_diagram_families.lp):
E₀/E₁ after postcomposition by Arr(η) compute to postcomposition by F/G.
Two functor clauses retain the iterable owner; two object-first clauses
complete the competing route after that composite head has been erased.
Every inferred slot is a wildcard except the required Cat/id, shape and
retained data discriminators. Typed whole/object-first, identity-endpoint,
generic identity-postcomposition and noncollapse controls pass.

Two sufficient proof-time comparisons preserve runtime heads. Same-head
`sym_transf_tapp0_transf` congruence compares every index, parent family and
whole transformation, aligning native/raw parent annotations without erasing
data. The existing family-view owner gains the companion mixed associativity
view `(G∘F)∗X ≐ G∘(F∗X)` at the same G,F,X. Typed eq_refl controls exercise
both helpers; unrelated transformations, shape observations and retained
input families are rejected.

Rejected experiments are kept as ignored probes:
`nuh4c4_evaluation_owner.lp` proposed a generic Eᵢ/postcomposition fold;
its generic identity-postcomposition corner failed in
`nuh4c4_eval_identity_corner-20260913-145518.log`. Only constructor-scoped
clauses are promoted. Raw parent annotations *inside* mate composites also
failed; native postcomposition endpoints are kept there, with raw views
only at the qualified observation interface. Separate internal-functor
packaging of fact failed on nested native/raw annotations and is not
promoted or claimed. The explicit whole-transformation function is checked.
An early negative index-control used an unqualified constant-exchange fold;
its expected type was ill formed. The maintained control instead uses
Arr(η:F⇒F), whose two endpoint families compute to the same F, and verifies
that the two observations of an arbitrary h still do not collapse.

All checks are warning-enabled, serial, resource-guarded and ≤90 seconds.
The [comparison reviewer](../emdash2/examples/one_cat_image_coimage_comparison.lp)
checks actual Coim/Im endpoints, whole input cancellation, original u,
factorization and uniqueness, wrong-input rejection, raw whole-formula
agreement, components, arbitrary diagram maps and the next Hom functor
packaged with its original endpoints in the existing native arrow carrier.
The projection helpers are not substituted by per-object proof hypotheses.

There are 27 added assertions: 13 comparison/characterization/action checks,
three whole-evaluation comparison controls, nine constructor/identity/noncollapse
checks and two mixed-associativity controls. Final focused logs are:

| Target | Warning-enabled log under `emdash2/logs/probes/` |
| --- | --- |
| Introduced-arrow owner | `emdash3_2_arrow_diagram_families-20260913-160314.log` |
| Existing family-view owner | `emdash3_2_one_cat_adjunction_family_views-20260913-160317.log` |
| New zero-arrow action paths | `emdash3_2_zero_arrow_family_action_paths-20260913-160321.log` |
| New whole terminal-family paths | `emdash3_2_one_cat_terminal_family_paths-20260913-160324.log` |
| New whole diagram-family paths | `emdash3_2_one_cat_diagram_family_paths-20260913-160328.log` |
| New whole kernel/cokernel-family paths | `emdash3_2_one_cat_kernel_cokernel_family_paths-20260913-160332.log` |
| New whole comparison source | `emdash3_2_one_cat_image_coimage_comparison-20260913-155706.log` |
| Complete comparison reviewer | `one_cat_image_coimage_comparison-20260913-160255.log` |
| Constructor evaluation reviewer | `arrow_diagram_families-20260913-160010.log` |
| Whole-evaluation view controls | `zero_arrow_family_action_paths-20260913-160219.log` |
| Existing/new family-view controls | `one_cat_adjunction_family_views-20260913-160344.log` |
| Retained whole zero-input mate consumer | `one_cat_adjunction_family_zero_inputs-20260913-160352.log` |
| Retained K/Q and ordinary observations | `kernel_cokernel_adjunctions-20260913-160358.log`, `kernel_cokernel_adjunction_observations-20260913-160402.log` |
| Dependency-only join in the same import order | `nuh4c4_retained_dependencies_ordered-20260913-160747.log` |

The arrow owner matches its pre-edit `154727` baseline exactly at 1150
critical pairs / 157 replaceable-pattern warnings; the family-view owner
matches its `155448` baseline at 1151/157. Full comparison source and reviewer
match the dependency-only join exactly at 1208/159. Comparisons include
categories, source locations, term heads, participant-rule families and
parser diagnostics; no new warning family or source-local warning is hidden
by equal counts. An earlier dependency-only join used a different import
order and moved one pre-existing overlap's reported location from the Gray
profile to the terminal owner. Preserving the actual traversal resolves that
reporting difference; the same-order inventory is identical.

The three changed/new rule owners pass strict LHS audits. Catalog generation
and strict freshness pass; the generated source-only health snapshot covers
977 files and deliberately runs no aggregate typecheck. Shell syntax,
active-reference/header lint, changed Markdown links and exact staged diff
are checked before the local checkpoint. Source metrics are bookkeeping,
not extra formal qualification or resumable aggregate evidence.

**Historical C2c4 boundary, advanced by C3 above:** Abelian invertibility of this actual a, then canonical exactness and
whole universal descent for δ. Concrete model/reifier automation and the
snake comparison remain in the active goal; general terminality, old LES
endpoint debugging, duality and strictness migration remain deferred.

### NUH-4C2c3: Whole evaluation of the original normalized inputs

**Implemented after 2a419dde.** The original h_Q and h_P now satisfy
E₀(h_Q)=∂ and E₁(h_P)=∂ as equalities of whole transformations D→C,
where D=Functor_cat(WalkingArrow_cat,C). The actual
[zero-column views](../emdash2/emdash3_2_one_cat_adjunction_zero_column_views.lp)
contain two defined proof terms, with the original Q or P and original
initial/terminal structures. They import the operational zero-column owner;
there is no ordinary-record or optional mate-formula-view dependency.

The [evaluator owner](../emdash2/emdash3_2_diagram_evaluation.lp) defines
`diagram_family_evaluation_func` as value evaluation after exchange and
routes the old component alias through it with unchanged computation.
`one_cat_diagram_family_evaluation_comp_path` is defined by the existing
generic `fapp1_comp_path`, with the ordinary C1 scope explicit. It adds no
new composition-preservation rule or manually supplied naturality square.

Two nucleus rules complete the existing double-exchange ladder for the
whole transformation and its preprojected component. Whole cancellation,
three-exchange overlap orders, the projected route, original Hom action
and its next projection check. The ordinary flipping interpretation is
linked in the subplan. This is not a qualification of arbitrary lax/oplax
interchange, nor an integration of the deferred profile branch.

Eight [whole normalizer endpoint rules](../emdash2/emdash3_2_one_cat_terminal_family_universality.lp)
return the identity transformation of F or const_t. The original primitive,
OneCat guard and terminal/initial inputs remain unchanged. These complete
its intended ordinary identity-endpoint presentation; they are not a new
terminality interface or a derivation of whole extensionality from the old
point β rules. Removing the original direct point clauses fails their
retained consumer (`nuh4c3_terminal_old_points_without-20260913-134315.log`),
so both routes are kept and explicitly checked to agree. Further action
returns the original endpoint functor's Hom action, including the constant
endpoint case; it does not collapse nontrivial base arrows to identities.

The original whole-endpoint baseline failed
(`nuh4c3_whole_terminal_endpoint_baseline-20260913-130813.log`). The normalizer
projection alone passed but did not finish the composed input observation.
The existing generic evaluator composition path and the double-exchange
rungs then completed both input equations. The minimal-import experiment
`nuh4c3_full_evaluation_minimal-20260913-134530.log` confirms that the previous
optional family-view comparisons are unnecessary here.

There are 38 added reviewer assertions: seven for exchange, two for the
whole evaluator, 21 for normalizer endpoints/routes/action and eight for
the actual input observations. The latter cover whole equality, components,
whole off-diagonal Hom functors and arbitrary original diagram maps. The
retained evaluator, adjunction/family and factor-reconstruction consumers
also pass. No new primitive, unifier, H selection or factor implementation
is introduced. There are ten runtime projection rules and four defined
operations/proof views across the four owners.

**Historical boundary, resolved by C2c4 above:** coherent factorization/annihilation and a:Coim⇒Im,
using the actual whole inverse-mate reconstruction and evaluation evidence.
Neither these observations nor the two existing factors constitute a.
Keep their complete source data and avoid a pointwise cone rebuild or an
opaque comparison/exactness witness. General terminality, the old LES
endpoint-checker investigation, strictness migration and Op repair remain
deferred.

Final warning-enabled, serial resource-guarded ≤90-second checks:

- nucleus baseline: `emdash3_2-20260913-132913.log`;
- normalizer baseline: `emdash3_2_one_cat_terminal_family_universality-20260913-133258.log`;
- promoted nucleus: `emdash3_2-20260913-141123.log`;
- promoted normalizer: `emdash3_2_one_cat_terminal_family_universality-20260913-141232.log`;
- whole input-view source: `emdash3_2_one_cat_adjunction_zero_column_views-20260913-141703.log`;
- whole input-view reviewer: `one_cat_adjunction_zero_column_views-20260913-141433.log`;
- final evaluator reviewer, checking its original native normal form: `diagram_evaluation-20260913-142431.log`;
- retained exchange/evaluation/normalizer/family/factor-reconstruction reviewers: `nuh4c3_retained-20260913-140410.log`.

The nucleus inventory changes from 1,144 / 157 to 1,146 / 157 critical
pairs / replaceable-pattern warnings. Its two new overlap families are
three successive exchanges (`sym_func_func_transf` with itself) and
preprojected cancellation (`sym_transf_tapp0_transf` with
`sym_func_func_transf`), at owner lines 17268 and 17273. The reviewer checks
both typed orders with the actual swapped arguments. The raw critical-pair
warnings remain recorded; this is not a global confluence certificate.

The eight whole normalizer endpoint clauses add no further reported
overlap: its inventory changes from 1,171 / 159 to 1,173 / 159 solely through
those two nucleus families. The new source/reviewer have 1,173 / 159.
The retained join has 1,271 / 169, exactly the earlier reconstruction
dependency inventory plus those same two families. Categories, locations
(accounting for inserted source lines), term heads, participant families
and parser issues were compared; there are no removals or new parser issues.
The final nucleus blob is e465551f2e115f303cc28676d1021440544036ca.

All three affected LHS audits pass. Catalog freshness, shell syntax,
Markdown/diff hygiene and source-only health freshness pass; health now
inventories 970 files. Validation is localized; no repository-wide or
TypeScript aggregate ran.

### NUH-4C2c2: Whole formula agreement and inverse reconstruction

**Implemented after e8dda02f.** The optional
[family-view owner](../emdash2/emdash3_2_one_cat_adjunction_family_views.lp)
resolves C2c1's native/raw formula boundary with three proof-time helpers:
congruence of a pair of Cat horizontal actions under whole-transformation
composition; congruence of the horizontal actions; and associativity with
an inner represented postcomposition. Every corresponding operand and
endpoint must compare. This is a sufficient elaboration procedure, not a
claim that mathematical composition is injective.

The whole-composition helper is guarded by both horizontal-action heads.
An initially unguarded version proved the desired family comparisons but
shadowed the existing generic associativity rule. The regression at
`nuh4c2_views_review-20260913-124327.log` rejected it. The guarded version
preserves associativity and passes the actual family/factor consumers.
A fourth, broader represented/raw-operand comparison proved unnecessary
and was dropped. Removing either required congruence helper failed the
actual comparison (`nuh4c2_compare_without_0-20260913-123350.log` and
`nuh4c2_compare_without_1-20260913-123456.log`); removal of the broader
helper passed (`nuh4c2_compare_without_2-20260913-123553.log`).

Four defined paths expose native/raw whole mate agreement in both
directions and whole inverse-mate reconstruction of the raw formulas.
They use the original Hom comparison, equality action and its same
selected inverse. The actual input h is retained throughout. There is no
ordinary universal-factor dictionary, additional naturality-square field,
new primitive or runtime rewrite. The original H and two factor programs
are unchanged. Reconstruction for a raw formula is proved equality;
judgmental cancellation remains at the native mate pair.

The [reviewer](../emdash2/examples/one_cat_adjunction_family_views.lp)
contains two defined generic K/Q comparison witnesses, twelve positive
assertions and four negative assertions. It covers whole inverse recovery,
components and whole off-diagonal Hom action in the family parameter B, the original published
Coim/Im factors at their actual normalized inputs, retained ordinary
associativity, and the mixed comparison. Unrelated input transformations
and changed operands are rejected; mixed associativity remains proof-time,
not a runtime conversion. The retained family/adjunction/H/factor reviewers
also pass with the new comparison extension loaded.

**Historical C2c3 boundary, resolved above:** whole evaluation of the normalized input, then coherent
annihilation and a. The focused
`nuh4c2_whole_zero_endpoints-20260913-125108.log` stops at
`sym_transf_tapp0_transf` of the normalized cokernel-unit input when the
expected whole observation is `diagram_evaluation_transf`. Only its first
assertion was reached. The existing pointwise endpoint observations remain
green, but do not prove this whole equation. Start with the existing whole
evaluation/postwhiskering comparison and original terminal-family
normalizer, preserving the same input. Qualify any required whole
projection at its actual owner. This is part of the current internal
construction, not a reopening of the old LES endpoint-checker work,
general terminality, strictness profiles or duality repair.

Final warning-enabled, serial resource-guarded ≤90-second checks:

- promoted source: `emdash3_2_one_cat_adjunction_family_views-20260913-124844.log`;
- promoted reviewer: `one_cat_adjunction_family_views-20260913-124948.log`;
- exact reviewer dependency join: `nuh4c2_views_dependencies-20260913-125153.log`;
- retained family/adjunction/H/factor reviewers: `nuh4c2_view_retained-20260913-125314.log`.

The source exactly matches the unchanged family-adjunction dependency
inventory at 1,149 critical pairs / 157 replaceable-pattern warnings. The
reviewer matches its exact join at 1,176 / 159. The retained join matches
the C2c1 retained inventory at 1,176 / 159. Categories, locations, term
heads, participant families and parser issues match exactly; no additional
warning family is reported. Strict LHS audit, catalog freshness, shell
syntax and source-only health freshness pass. Health inventories 968 files.
No aggregate or TypeScript typecheck ran, and the nucleus is unchanged.

### NUH-4C2c1: Native adjunctions on whole functor families

**Structural substep implemented after c475bfe7; canonical a remains open.**
The [family-adjunction owner](../emdash2/emdash3_2_one_cat_adjunction_families.lp)
adds two explicit structural primitives. `one_cat_postcomp_adjunction`
takes the original F⊣G and the ordinary profiles of its two categories,
and retains `comp_cat_cov_func(F)` and `comp_cat_cov_func(G)` as the
adjoint functors. `one_cat_functor_category` supplies the ordinary profile
of Functor_cat(B,C) from OneCat(C), used for the actual K/Q specializations.
It is one-way evidence, not a classifier-equality rewrite.

**Primitive/model boundary:** these are native structural presentation
operations extending opaque Adjunction/profile interfaces. They are not
formal derivations from their current β rules. The categorical subplan
links the ordinary whiskering theorem. Qualification here uses ordinary
targets; it supplies no general lax/oplax adjunction interchange theorem.
The eventual model audit must interpret these structural operations along
with the retained reconstruction and terminal-family presentation laws.

Two whole unit/counit rules expose existing tele-postcomposition of the
original unit/counit. The first component-only candidate was superseded by
this whole-owner version: its components and further action follow from
the inherited owner. Two transparent family mate functors then project the
existing Hom comparison and its selected inverse. Native postcomposition
endpoints remain in their types so the original inverse cuts are visible.
No new unifier or constructor-specific naturality/functoriality rule is
installed, and no ordinary factor dictionary is imported.

The [generic reviewer](../emdash2/examples/one_cat_adjunction_families.lp)
has 16 positive and four negative assertions: whole input cancellation in
both directions, whole functor cancellation, next Hom projections, original
unit/counit components and action on an arbitrary family transformation,
and the existing whole semantic comparison at native endpoints. The
negative cases reject unrelated transformations and mate functors.
The [actual zero-input reviewer](../emdash2/examples/one_cat_adjunction_family_zero_inputs.lp)
has six positive assertions: the two original normalized C2b families
yield the original Coim/Im endpoint types; inverse mating recovers each
entire input and its component at any original diagram. The latter test
needed explicit existing projection endpoints; no rule was added for it.

**Historical presentation boundary, resolved by C2c2 above:** generic and specialized attempts to
identify the native result with the older raw K(h)∘η / ε∘Q(h) whole formulas
did not qualify. Initial failures involved raw endpoint annotations hiding
the native composition cuts. Keeping native endpoints resolves generic
whole cancellation, but the raw whole-formula and component comparisons
still encounter composition/product annotations. The generic printed
normal forms agree with implicits hidden, which is diagnostic evidence,
not a typed proof. The proposed extra formula unifiers also failed and
remain ignored experiments. They are not promoted or used by the goal.

Relevant unsuccessful logs: `nuh4c_kernel_cokernel_family_mates_paths-20260913-120208.log`,
`nuh4c_kernel_cokernel_family_formula_review-20260913-120535.log`,
`nuh4c_kernel_cokernel_family_components_native-20260913-121025.log`, and
`nuh4c_kernel_cokernel_family_mates_paths_native-20260913-121039.log`.
The native generic normal-form inspection is
`nuh4c_family_mate_normal_forms-20260913-120251.log`.
These are local annotation/comparison experiments, not the deferred old
LES endpoint-checker investigation or evidence of a mathematical failure.

The comparison obligation from this checkpoint is now discharged by C2c2;
the original H and raw factor programs remain unchanged. C2c must still assemble the coherent annihilation
input and define the canonical a, with factorization and higher action
from that whole program. This structural lifting does not construct a,
postulate its Abelian invertibility, or prove categorical exactness/δ.

Final warning-enabled, serial resource-guarded ≤90-second checks:

- adjunction dependency baseline: `emdash3_2_adjunction_mates-20260913-115105.log`;
- promoted source: `emdash3_2_one_cat_adjunction_families-20260913-121639.log`;
- final generic reviewer: `one_cat_adjunction_families-20260913-122014.log`;
- exact zero-input dependency join: `nuh4c_family_zero_dependencies-20260913-121334.log`;
- final zero-input reviewer: `one_cat_adjunction_family_zero_inputs-20260913-122032.log`;
- retained adjunction/H/whole-factor reviewers: `nuh4c_whole_mate_retained-20260913-121522.log`.

Source and generic reviewer exactly match the dependency baseline at
1,149 critical pairs / 157 replaceable-pattern warnings. The zero-input
reviewer matches its exact join at 1,176 / 159. The retained reviewer join
matches the earlier C2b retained inventory at 1,176 / 159. Categories,
locations, term heads, participant families and parser issues match
exactly in each comparison; the new whole rules add no reported overlap.
Strict LHS audit, catalog freshness, shell syntax and source-only health
freshness pass. Health now inventories 966 files; no aggregate or TypeScript
check ran. The nucleus blob remains 91f1974ece225e399604dce24710bf1437ad3ef5.

### NUH-4C2b: Native whole terminal/initial family universality

**Implemented and locally qualified after c38f6c0f.** The
[terminal/initial family-universality owner](../emdash2/emdash3_2_one_cat_terminal_family_universality.lp)
adds two explicit primitive operations:
`one_cat_terminal_arrow_family_iso` and
`one_cat_initial_arrow_family_iso`. They have the existing DefIso type and
require OneCat(C), the original terminal/initial capability, F:B→C and the
actual whole h with the appropriate constant endpoint. Eight shape-guarded
rules make both endpoint components of both directions identities. The
inverse is selected through the existing DefIso operation, with its generic
inverse cuts; there is no independently chosen inverse or new equivalence
grammar.

**Primitive/model boundary:** this is an additional native computational
presentation of ordinary terminal/initial family universality. It is not
claimed as a formal theorem derived from the old pointwise IsContr/β
interface. The categorical subplan records the ordinary mathematical
justification and the explicit strength of this extension. Keep it visible
in the later trust/model audit and revisitable under the user's
computational/internal criterion. It does not assert a general directed
higher-category result from groupoidal pointwise contractibility, and it
does not postulate a, normality, δ or exactness.

The [zero-column owner](../emdash2/emdash3_2_one_cat_adjunction_zero_columns.lp)
defines the two actual-column instances and the normalized whole mate
inputs. The original ZP/ZQ, κ/q and nonzero endpoints are retained, with
no object cast or caller square equation. The
[whole cokernel-family owner](../emdash2/emdash3_2_cokernel_adjunction_families.lp)
defines Q∘D, the whiskered counit, Q(h), and the colift ε∘Q(h).
Together with the existing kernel-family mate, this gives the
[two canonical whole factors](../emdash2/emdash3_2_one_cat_image_coimage_factors.lp)
v:Coim⇒ev₁ and u:ev₀⇒Im. These ten defined operations introduce no further
primitive, rewrite, unifier or ordinary factor dictionary. The primary
import graph includes no ordinary record-conversion owner.

The three new reviewers contain 28 assertions: 26 positive and two negative.
They cover all endpoint identities, both whole inverse cuts, retained next
Hom action, rejection of nonzero endpoint families, actual-column
specialization, the original horizontal components of the mate inputs, and
the whole factors' action. The reconstruction reviewer proves
v_d∘π_d=f_d and ι_d∘u_d=f_d through the existing native mate reconstruction
laws and their semantic comparison. Its ordinary reference import and one
dual semantic-reconstruction helper are reviewer-only, not prerequisites
of the operational programs.

The direct conversion assertion for reconstruction did not pass
(`nuh4c_canonical_factor_reconstruction-20260913-103052.log`). The equation
witnesses pass (`nuh4c_factor_reconstruction_views-20260913-103358.log`)
and are not advertised as judgmental reconstruction cuts. No extra runtime
rule is installed to force those equations. Whole coherent factorization
data for a remain separate work.

Final warning-enabled, serial resource-guarded ≤90-second checks:

- source: `emdash3_2_one_cat_image_coimage_factors-20260913-104217.log`;
- universal-family reviewer: `one_cat_terminal_family_universality-20260913-104220.log`;
- whole-factor reviewer: `one_cat_image_coimage_factors-20260913-104224.log`;
- reconstruction reviewer: `one_cat_image_coimage_factor_reconstruction-20260913-104227.log`;
- source dependency baseline: `nuh4c_factor_dependencies-20260913-104347.log`;
- exact reconstruction join: `nuh4c_factor_reconstruction_dependencies-20260913-104350.log`;
- reference reconstruction join without new primitives: `nuh4c_reference_reconstruction_dependencies-20260913-104355.log`;
- combined retained transposition, H-family and adjunction-mate reviewers: `nuh4c_family_retained_consumers-20260913-104359.log`.

Every old warning inventory entry is preserved. The eight new component
rules add exactly 16 overlaps with the inherited constant-family tapp0
projection, once at the outer component and once at the inner component
for each rule. The head and both participant heads are tapp0_fapp0, at
the normalizer owner lines 19, 27, 35, 43, 60, 68, 76 and 84. No generic
naturality rule is added or changed. The source/first two reviewers have
1,171 critical pairs / 159 replaceable-pattern warnings; the reconstruction
reviewer matches its exact dependency join at 1,269 / 169, and the retained
consumer join has 1,176 / 159. Exact categories, locations, heads and
participant-family deltas are checked, with no removals or parser issues.
Four LHS audits, catalog freshness and shell syntax checks pass; source-only
health is refreshed to 963 files. No aggregate or TypeScript check ran.

**Historical C2b boundary, resolved by C2c4 above:** construct the canonical whole a:Coim⇒Im and its coherent
factorization data from the original whole universal operations. The two
proved pointwise reconstruction observations do not themselves give the
required coherent annihilation/mate input. Do not rebuild pointwise cones,
make ordinary dictionaries operational prerequisites, or postulate a or
its Abelian invertibility to complete the construction.

### NUH-4C2a: Whole ordinary-target diagram transposition

**Implemented and locally qualified after 49ef915e.** The selected route
exchanges the original whole h:F⇒G first, introduces its arrow family in
Functor_cat(B,C), then exchanges the remaining walking-arrow/B arguments.
Columns are observations of that one whole family; do not reconstruct
them independently. This retains the original κ/q endpoints of the
transposed kernel counit and cokernel unit. The new transpose interface
has an explicit OneCat(C) parameter, so this is not a general lax/oplax
interchange claim.

The [diagram-evaluation owner](../emdash2/emdash3_2_diagram_evaluation.lp)
adds whole evaluation-after-precomposition computation at its functor and
preprojected Hom owners, plus two proof-time evaluation/postwhiskering
comparisons. The [arrow-family owner](../emdash2/emdash3_2_arrow_diagram_families.lp)
adds the existing introduced-arrow comparison observed through exchange.
Thus the source change has two runtime projection folds and three
unifiers, with no primitive declaration change. These are structural
computation/comparison, not new naturality premises or selected kernel
operations. The nucleus blob remains 91f1974ece225e399604dce24710bf1437ad3ef5.

The [ordinary transpose owner](../emdash2/emdash3_2_one_cat_diagram_transpose.lp)
defines one whole family and its column/shape-arrow observations. The
[adjunction instances](../emdash2/emdash3_2_one_cat_kernel_cokernel_transposes.lp)
define the two retained zero-end columns ZP/ZQ and the transposed cells
Arr(κ)⇒ZP and ZQ⇒Arr(q). Their source/target zero and evaluation functors
compute as whole functors. Horizontal components recover the original
differential and canonical terminal/initial arrow. The original κ/q are
literal endpoints of the typed whole transformations.

The three new reviewers contain 31 assertions: 26 positive and five
negative. They exercise typed proof-time comparisons, retained whole
columns, nonidentity shape arrows, next shape Hom and parameter Hom action,
the actual unit/counit components, and independent input retention. Further
action remains at the existing generic fapp/tapp owners; these checks do
not assert a complete higher normalization theorem.

**Projection-order correction:** the whole-functor fold alone did not join
the already projected `sym_fapp0_fapp1_func` route
(`nuh4c_evaluation_projection_order-20260913-095523.log`). The second fold
repairs that measured case. Whole Hom, capped arrow and next Hom comparisons
all pass in `nuh4c_evaluation_projection_owner-20260913-095644.log` and the
promoted evaluation reviewer. The source contains no duplicate point rule.

Final warning-enabled, serial resource-guarded ≤90-second checks:

- source: `emdash3_2_one_cat_kernel_cokernel_transposes-20260913-095803.log`;
- final source comment hygiene: `emdash3_2_one_cat_kernel_cokernel_transposes-20260913-100109.log`;
- evaluation reviewer: `diagram_evaluation_usability-20260913-095806.log`;
- transpose reviewer: `one_cat_diagram_transpose-20260913-095809.log`;
- adjunction reviewer: `one_cat_kernel_cokernel_transposes-20260913-095812.log`;
- retained evaluation/arrow-family reviewers: `diagram_evaluation-20260913-095815.log`, `arrow_diagram_families-20260913-095818.log`;
- retained adjunction/H/Coim reviewers: `kernel_cokernel_adjunctions-20260913-095821.log`, `homology_adjunction_families-20260913-095825.log`, `image_coimage_adjunction_families-20260913-095828.log`.

Exact warning comparisons preserve every old entry and add four classified
critical pairs: each projection fold overlaps the product-swap cancellation
and product-map composition schemas. The raw schemas have Product_cat
codomains where evaluation requires Functor_cat(I,C); focused typed
negative consumers reject both mismatches. No suppression rule or extra
compound inferred-slot guard is installed. The two heads are
`sym_fapp0_func` and `sym_fapp0_fapp1_func`, each paired twice with
`comp_fapp0`, at diagram_evaluation:50 and :56. The final adjunction-transpose
source and retained H/Coim reviewers have 1,155 critical pairs / 159
replaceable-pattern warnings; the retained adjunction-mate reviewer has
1,160 / 159. Locations, heads, participant families and parser issues are
audited against the recorded predecessors, with no removals or parser issues.

Four source LHS audits, catalog freshness and shell syntax checks pass.
Source-only health is refreshed to 956 files. No aggregate or TypeScript
check ran. Earlier failed transpose orders, the unneeded extra congruence
prototype and all qualification logs remain in ignored probes; only the
selected original-family route is promoted.

**Original C2b continuation, now implemented above:** whole terminal/initial comparisons of ZP with
I∘ev₁ and ZQ with J∘ev₀, retaining the identity component at the respective
nonzero endpoint. The later C2b implementation supplies those comparisons
through its explicitly recorded native presentation extension and derives
the two factor maps. Canonical a:Coim⇒Im and its whole factorization data
remain required; no pointwise cone rebuilding or caller square proofs are
introduced as a replacement.

### NUH-4C: Direct categorical exactness and connecting

**Current primary continuation.** Follow the categorical subplan linked
above. Coim=Q∘Arr(κ) and Im=K∘Arr(q) are now whole native functors (C1
below). Next construct the canonical whole comparison and correctly indexed
invertibility evidence. Exactness concerns the canonical Im(f)→K(g)
comparison; connecting is a whole cokernel/mate descent through its
canonical cover. All required cells and inverse data must be constructed
or identified as genuine input structure, not hidden in new axioms.

The existing whole connecting declaration remains backed by its ordinary
record component; it is a reference to compare against, not the desired
final definition. Coherent row/window data and native Hom owners remain
the input language. No new naturality-square premises or primary IsContr
factor dictionaries are introduced.

**Preserved optional prototype:** `tmp/probes/nuh4c_category_views.lp`
defines ordinary all-arrow K/Q views and pre-Abelian/Abelian packaging.
It passes `nuh4c_category_views-20260913-085741.log`; its dependency join
passes `nuh4c_category_view_dependencies-20260913-085825.log`. It adds no
primitive/rule/unifier and keeps normality explicit. It was not promoted
to active source before the user's correction and is not a prerequisite
for the direct categorical continuation. Reuse only for an actual later
compatibility or CAS observation.

### NUH-4C1: Whole Coim/Im and their structural transformations

**Implemented after ae2719d7.** The
[image/coimage adjunction owner](../emdash2/emdash3_2_image_coimage_adjunction_families.lp)
contains six transparent definitions:

- `kernel_adjunction_arrow_func` = Arr(κ);
- `cokernel_adjunction_arrow_func` = Arr(q);
- `adjunction_coimage_func` = Q∘Arr(κ);
- `adjunction_image_func` = K∘Arr(q);
- `adjunction_coimage_projection` = q whiskered by Arr(κ);
- `adjunction_image_inclusion` = κ whiskered by Arr(q).

The inputs are the original whole P/Q. The definitions use only existing
arrow introduction, composition and prewhiskering. There are no new
primitive, rewrite, unification or equality-proof declarations, and no
W/V, ordinary record or selected factor prerequisites. The canonical
comparison, its invertibility and exactness/connecting are not postulated.

The [reviewer](../emdash2/examples/image_coimage_adjunction_families.lp)
checks 14 positive and two negative assertions. Whole diagram observations
recover κ/q; an arbitrary diagram map retains K[u], u₀, u₁ and Q[u] in
the appropriate components. Coim/Im retain their original whole Hom
composites; structural components recover the original q/κ, and a further
Hom of their transfor action remains typed. Independently supplied P/Q
selections do not collapse.

Warning-enabled, serial resource-guarded ≤90-second evidence:

- dependency baseline: `emdash3_2_kernel_cokernel_adjunctions-20260913-091647.log`;
- prototype owner: `nuh4c_image_coimage_families-20260913-091802.log`;
- prototype reviewer: `nuh4c_image_coimage_review-20260913-091958.log`;
- promoted owner: `emdash3_2_image_coimage_adjunction_families-20260913-092113.log`;
- promoted reviewer, also checking the final source comment: `image_coimage_adjunction_families-20260913-092200.log`.

All inventories match the single direct dependency exactly: 1,151 critical
pairs and 159 replaceable-pattern warnings, with matching locations, term
heads and participant families and zero parser issues. Focused LHS audit,
catalog freshness and shell syntax checks pass. Source-only health is
refreshed to 951 registered files; no aggregate or TypeScript check ran.

**Initial NUH-4C2 probe, superseded by C2a above:** whole zero-triangle rotation and mate assembly for
the canonical comparison. The temporary `nuh4c_square_transpose.lp` uses
only arrow introduction and internal argument exchange. Its first whole
column-observation assertion fails because the resulting whole endpoint
functors do not unify with evaluation postwhiskering
(`nuh4c_square_transpose-20260913-092243.log`). The companion
`nuh4c_square_transpose_points.lp` passes all four corner and two column
component computations (`nuh4c_square_transpose_points-20260913-092445.log`).
This isolates an unqualified whole computational comparison; it is not a
mathematical counterexample or an implementation of the canonical comparison.
The original ordering was not promoted. C2a now supplies a better ordered
whole assembly with qualified projection/comparison support. The zero-end
columns still need the appropriate terminal/initial universal comparisons;
mere pointwise agreement cannot stand in for those whole constructions.

### NUH-4B3: Raw Freyd maps use the direct native input path

**Implemented after 0a313a2a.** The
[shared raw-map data](../emdash2/emdash3_2_commutative_algebra_freyd_chain_map_data.lp)
owns the unchanged `freyd_raw_composite_agreement_path` and
`freyd_raw_chain_map_generic`. The old selected map definition is unchanged;
all three original bodies/signatures were compared explicitly. No TypeScript
source refers to the moved helpers. The data module adds
`freyd_raw_chain_map_path_func` through the existing PathMap owner.

The [native wrappers](../emdash2/emdash3_2_commutative_algebra_freyd_native_maps.lp)
compose this with the generic direct native-map functor and project its
point view. They take no W/P/Q. The
[H-map wrappers](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_homology_maps.lp)
compose it with the generic whole H-map functor, using whole P/Q and the
existing Freyd local categorical data. Their point operation is the same
functor's application. The raw morphisms and endpoint pairs are fixed
parameters of the agreement action; this is not a new raw-complex category
or a claimed joint directed action in raw representatives. The underlying
generic native/H map functors retain their full action.

The [native reviewer](../emdash2/examples/freyd_native_maps.lp) has four
checks for the original f₂/f₁/f₀ classes and point/whole agreement. The
[H reviewer](../emdash2/examples/freyd_adjunction_homology_maps.lp) has four
checks for actual H application, original record endpoints, the whole map
functor at those endpoints and its next Hom action. No new primitive,
rewrite, unifier, equation proof or caller coherence field is added.
Raw matrix/model interpretation remains a separate obligation.

Serial guarded, warning-enabled logs in `emdash2/logs/probes/`:

- baseline `freyd_zero_cone_maps-20260913-084100.log`;
- prototype `nuh4b3_freyd_native_maps-20260913-084325.log`;
- H-map source `emdash3_2_commutative_algebra_freyd_adjunction_homology_maps-20260913-084539.log`;
- native reviewer `freyd_native_maps-20260913-084719.log`;
- H reviewer `freyd_adjunction_homology_maps-20260913-084947.log`;
- legacy reviewer `freyd_zero_cone_maps-20260913-085033.log`;
- exact joins `nuh4b3_freyd_native_dependencies-20260913-085102.log`,
  `nuh4b3_freyd_homology_dependencies-20260913-085111.log` and
  `nuh4b3_freyd_homology_record_dependencies-20260913-085119.log`.

Native/H checks match their exact dependency inventories at 1,285/169;
the H-record reviewer matches its extended join at 1,290/169. The legacy
reviewer preserves 1,255/169. Locations, heads and participant families
agree, with zero parser issues. Three focused LHS audits and the catalog
pass; source-only health is refreshed to 949 files. No aggregate ran.

**Next NUH-4C:** the subsequent user correction selects the direct categorical
subplan above. The ordinary category-view experiment is retained as optional
compatibility evidence, not the primary connecting/exactness implementation.
Whole-model/reifier construction and snake comparison remain later.

### NUH-4B1/2: Native maps before kernel selection and whole H action

**Checkpoint 0a313a2a, after b012be50.** The existing whole outgoing-diagram map
functor now imports the independent outgoing-diagram owner. Both of its
definitions are unchanged. The
[direct native-map module](../emdash2/emdash3_2_one_cat_chain_pair_native_maps.lp)
derives b∘h₀ ⇒ h₁∘J(a) at OneCat: the original upper factor supplies the
source-component equality, and terminal-zero structure supplies equality
of the target components. The existing whole-reconstruction/diagram-map
comparison produces the private ordinary comparison. The public map uses
the existing nested-Sigma Hom constructor and takes no K/P, extra equality,
naturality or functoriality premise. Its whole action in the existing raw-map
path category is obtained through PathLift.

The first full prototype failed only when installing that comparison in
the native Hom: the raw composite of two images under D had already reduced
to a single D-action, whereas the native fibre retained represented
postcomposition. The separate composites and ordinary comparison checked.
The accepted construction keeps that native postcomposition endpoint and
uses a private typed reflexivity view of the existing identity-family
postcomposition/raw-composition unifier. It adds no computation rule or
unifier, does not change native Hom, and does not reopen the Op/profile work.
This is a representation comparison for composition, not a new naturality law.

The [H-map module](../emdash2/emdash3_2_one_cat_chain_pair_homology_maps.lp)
composes the whole native-map realization with H's existing whole Hom
functor. Its point view is the same functor's application. It does not import
the ordinary H-record module; those records are optional endpoint views in
the reviewer. No H operation or per-map coherence structure is redefined.

The [native-map reviewer](../emdash2/examples/one_cat_chain_pair_native_maps.lp)
checks the original next component, outgoing diagram map, middle and previous
components, and whole/point agreement; its retained negative distinguishes
an unrelated map. The next Hom action is available. The
[H-map reviewer](../emdash2/examples/one_cat_chain_pair_homology_maps.lp)
has four checks: actual H application, both original-pair record endpoints,
the whole map functor at those endpoints, and its next Hom action.

Serial guarded, warning-enabled evidence in `emdash2/logs/probes/`:

- baselines `chain_pair_zero_cone_maps-20260913-075743.log` and
  `emdash3_2_chain_pair_diagram_maps-20260913-080025.log`;
- raw native-fibre mismatch `nuh4b_native_maps-20260913-080227.log`;
- prefixes `nuh4b_native_composites-20260913-080552.log` and
  `nuh4b_native_comparison-20260913-080720.log` (the latter's completed log
  was recovered after its tool handle expired; no checker remained running);
- corrected native prototype `nuh4b_native_maps_postcomp-20260913-081249.log`;
- H prototype `nuh4b_homology_maps-20260913-081713.log`;
- H-map source `emdash3_2_one_cat_chain_pair_homology_maps-20260913-081940.log`;
- native reviewer `one_cat_chain_pair_native_maps-20260913-082221.log`;
- H-record reviewer `one_cat_chain_pair_homology_maps-20260913-082602.log`;
- narrowed owner `emdash3_2_chain_pair_diagram_maps-20260913-082852.log`;
- legacy reviewer `chain_pair_zero_cone_maps-20260913-083119.log`;
- exact joins `nuh4b_diagram_map_dependencies-20260913-083209.log`,
  `nuh4b_native_map_dependencies-20260913-083215.log`,
  `nuh4b_homology_map_dependencies-20260913-083221.log` and
  `nuh4b_homology_map_record_dependencies-20260913-083228.log`.

The narrowed diagram owner matches its exact join at 1,244/169. Relative to
the former 1,249/169 source, five adjunction-mate overlaps are no longer
loaded; two existing composition overlaps between terminal_arrow_fapp0 and
binary_products_K1a_fapp0/K2a_fapp0 are attributed at terminal_objects:96
instead of triangular_binary_products:256/266 due to import order. Their
actual participant rules were inspected. No new term head or participant
family appears. Native map and H-map checks match their exact joins at
1,279/169; the H-record
reviewer matches its extended join at 1,284/169. The selected legacy reviewer
retains its complete 1,249/169 inventory. All comparisons include locations,
heads and participant families with zero parser issues. LHS audits and
catalog pass; source-only health is refreshed to 944 files. Validation is local.

**Next NUH-4B3:** move the existing raw Freyd composite-agreement and generic
chain-map observations into a data owner without selected map adapters.
Specialize the new native map and H action to that original raw data,
filling the known local categorical observations. Preserve raw f₂/f₁/f₀
and source/target H endpoints. Whole model binding, connecting/exactness,
reifier automation and snake comparison remain later consumers.

### NUH-4A3: Direct Freyd raw inputs and whole-adjunction records

**Implemented after 515b7187.** The
[shared raw data](../emdash2/emdash3_2_commutative_algebra_freyd_chain_pair_data.lp)
owns the unchanged `freyd_raw_chain_zero_path` and
`freyd_raw_chain_pair_generic`. All four original definitions across that
module and the legacy selected input/H source are unchanged after stripping
comments/imports/whitespace. No TypeScript source refers to the moved names.

The [native input](../emdash2/emdash3_2_commutative_algebra_freyd_native_inputs.lp)
defines `freyd_raw_chain_native_cone` from the original raw e, d and chain
agreement, without W/P/Q arguments. It fills the existing Freyd OneCat,
preadditive and terminal-zero observations. The
[whole H/record module](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_homology.lp)
defines `freyd_zero_cone_adjunction_homology_func` and
`freyd_raw_chain_adjunction_homology_record` from explicit whole P/Q. It
retains the original generic pair and actual H at the direct native input.
P/Q still express whole model structure; these wrappers do not construct
that structure from raw agreements or complete model/reifier automation.

All three new operations are definitions through existing generic owners,
with no new primitive, rule, unifier, equality proof or coherence field.
The data imports retain existing classifier vocabulary; no hidden selected
factor operation occurs in the new input or H/record bodies.
The [input reviewer](../emdash2/examples/freyd_native_inputs.lp) checks the
original first presentation, incoming/outgoing raw morphism classes and
existing agreement observation, with no kernel/cokernel parameters.
The [record reviewer](../emdash2/examples/freyd_adjunction_homology.lp)
checks the actual H object and boundary reconstruction to the original
incoming class. These six checks and the existing selected consumer pass.

Serial guarded, warning-enabled logs in `emdash2/logs/probes/`:

- baseline `freyd_zero_cone_inputs-20260913-072822.log`;
- prototype `nuh4a3_freyd_native_homology-20260913-073443.log`;
- input source `emdash3_2_commutative_algebra_freyd_native_inputs-20260913-073716.log`;
- H/record source `emdash3_2_commutative_algebra_freyd_adjunction_homology-20260913-073903.log`;
- input reviewer `freyd_native_inputs-20260913-074036.log`;
- record reviewer `freyd_adjunction_homology-20260913-074201.log`;
- legacy reviewer `freyd_zero_cone_inputs-20260913-074351.log`;
- record join `nuh4a3_freyd_record_dependencies-20260913-074518.log`;
- input join `nuh4a3_freyd_input_dependencies-20260913-074558.log`.

The input source/reviewer match their exact source dependency inventory at
1,250 critical pairs / 169 pattern warnings; the H/record pair match their
join at 1,290/169. The legacy reviewer preserves 1,255/169. All compared
locations, heads and participant families agree; parser issues are zero.
Three focused LHS audits and the catalog pass; source-only health is
refreshed to 940 files. No repository aggregate or TypeScript check ran.

**Next NUH-4B:** the old `chain_pair_zero_cone_map` still introduces maps
through selected lifts and inverse mates. Reuse the existing whole
`chain_pair_outgoing_diagram_map_func`, narrowing its unnecessary selected
input import to the shared outgoing-diagram owner. Construct the map
between the new direct native inputs from the original chain-map fields;
any required comparison cell must be derived internally, with no extra
caller naturality/functoriality-square premise and no kernel selection.
Use existing native Hom constructors and whole action; retain the stated
OneCat profile and the revisitable owner criterion. Then specialize to the
raw Freyd map and apply the original H functor at actual record endpoints.
Connecting/exactness and whole-model/reifier construction remain later.

### NUH-4A2: Original chain pairs enter H before kernel selection

**Checkpoint 515b7187, after b9e5e0e5.** The unchanged outgoing-diagram observation
now lives in [chain-pair diagrams](../emdash2/emdash3_2_chain_pair_diagrams.lp).
All three original definitions across the split are unchanged after comments
and whitespace are removed. No TypeScript source refers to the moved name.

The [ordinary native inputs](../emdash2/emdash3_2_one_cat_chain_pair_inputs.lp)
package the existing raw zero-composite transformation and native cone from
the pair's original dNext, d and zero witness. Neither definition takes a
kernel/cokernel structure or selected capability. The zero witness is input
chain data; callers supply no new naturality law or square proof.

The [original-pair record](../emdash2/emdash3_2_one_cat_chain_pair_homology_records.lp)
takes whole P/Q after input formation. Its type is literally
HomologyRecord(C,S,A,B,D,pair). The existing semantic boundary-factor
observation at `chain_pair_native_transf` already has the required endpoints,
so the record adds no equality proof, reconstructed-pair transport, or chosen
test lift. It observes the original whole β and Q boundary-diagram family.
This tranche adds no primitive, rewrite, unifier or coherence field.

The [input reviewer](../emdash2/examples/one_cat_chain_pair_inputs.lp)
checks the first vertex, outgoing diagram, whole universal observation,
incoming differential and outgoing generator, all without K/Q in context.
The [record reviewer](../emdash2/examples/one_cat_chain_pair_homology_records.lp)
checks cycles, actual β/H, reconstruction of the original dNext and the
original H action on a native map between two raw inputs at record endpoints.
Thus all ten checks preserve the required staging and actual outputs.

Serial guarded, warning-enabled logs in `emdash2/logs/probes/`:

- original baseline `chain_pair_homology_records-20260913-071600.log`;
- prototype `nuh4a2_chain_pair_records-20260913-071834.log`;
- source `emdash3_2_one_cat_chain_pair_homology_records-20260913-072038.log`;
- input reviewer `one_cat_chain_pair_inputs-20260913-072206.log`;
- record reviewer `one_cat_chain_pair_homology_records-20260913-072304.log`;
- legacy reviewer `chain_pair_homology_records-20260913-072416.log`;
- exact join `nuh4a2_record_dependency_baseline-20260913-072508.log`.

The new source/reviewer match the complete exact-join inventory at
1,284 critical pairs / 169 pattern warnings; the legacy reviewer retains
1,249/169. Locations, heads and participant families agree, with no parser
issues. Three focused LHS audits and the catalog pass. Source-only health
is refreshed to 935 files. No repository aggregate was run.

**Next NUH-4A3:** move the existing raw Freyd chain-zero/pair observations
into a data owner without selected input adapters, then specialize this
direct native input path and whole-adjunction record. Fill the existing
Freyd OneCat, preadditive and terminal-zero observations in the wrappers.
Whole P/Q interpretation remains an explicit later model-construction
boundary; raw agreement data do not create it. Afterwards migrate the
actual raw chain-map-to-native-map consumer before connecting/exactness.

### NUH-4A1: Homology records observe independent whole adjunctions

**Implemented after checkpoint 1ea98f63.** The
[independent data owner](../emdash2/emdash3_2_homology_adjunction_record_data.lp)
extracts the existing actual boundary β=K(h)∘η, its reconstruction and factor
view, plus the unchanged `homology_family_pair` observation of h. The three
legacy boundary names delegate through the presentation-to-structure
adapter. All four remaining legacy signatures and the old complete record
body are unchanged; no OneCat argument is added to those generic names.
No TypeScript source refers to the moved pair or boundary names.

The [ordinary record](../emdash2/emdash3_2_one_cat_homology_adjunction_records.lp)
defines `homology_adjunction_family_record` from whole P/Q and OneCat(C),
without W/V. It retains the actual semantic β field and uses Q on the
original whole boundary-diagram family. The primary K/Q/mates/H graphs
remain independent of all these derived record modules (9/11/10/16 files).
The new sources contain no selected capability/presentation arguments,
new primitive, rewrite, unifier or coherence field. Their imports include
the established record vocabulary, not supplied selections hidden in bodies.

The [reviewer](../emdash2/examples/one_cat_homology_adjunction_records.lp)
has six successful checks: literal cycle, actual whole β, H and quotient
projections, plus the original H's arbitrary-arrow and whole Hom actions at
the record H endpoints. It adds no naturality or functoriality proof to the
consumer. The record never substitutes the canonical lift of an extracted
raw test for β, and does not cast to another H object.

Prototype observations are retained. The first pass lacked the existing
`zero_arrow_universal_tests` import. A proposed one-line replacement of the
semantic reconstruction proof did not compare the native mate application
with its unit formula under composition. The accepted proof shares the
existing whole mate/semantic comparison in the derived reconstruction; no
unifier or new naturality equation was added to force the shorter term.
Those probes are `nuh4a_homology_adjunction_records-20260913-070226.log`,
`...-070342.log` and the corrected passing `...-070407.log`.

Serial guarded, warning-enabled qualification in `emdash2/logs/probes/`:

- baseline `emdash3_2_homology_family_records-20260913-065912.log`;
- new source `emdash3_2_one_cat_homology_adjunction_records-20260913-070548.log`;
- six-check reviewer `one_cat_homology_adjunction_records-20260913-070706.log`;
- legacy source `emdash3_2_homology_family_records-20260913-070741.log`;
- legacy reviewer `homology_family_records-20260913-070833.log`;
- exact join `nuh4a_record_dependency_baseline-20260913-070920.log`.

Legacy source/reviewer preserve the complete baseline inventory at
1,249 critical pairs / 169 pattern warnings. The new source/reviewer match
their exact dependency join at 1,284/169, including locations, heads and
participant families; parser issues are zero. Rule audits and catalog pass.
Source-only health is refreshed to 930 files; no aggregate typecheck ran.

**Next NUH-4A2:** package the existing `zero_composite_native_cone` directly
from a ComputationalChainPair's dNext, d and original zero witness, before
any kernel selection. Give its outgoing-diagram observation an independent
owner if needed. Construct the whole-H record over the original pair,
retaining actual β and H, rather than transporting a reconstructed pair
record. Keep old input interpretations as explicit comparisons where an
actual consumer requires them; do not assume equality with another H input.
Then migrate the packaged Freyd input and induced-map consumers. Connecting,
exactness, concrete-model and snake-comparison work remain later subrows.

### NUH-3C4: Ordinary uniqueness from native square paths

**Implemented (2026-09-13), following 323e71fc.** The
[native square paths](../emdash2/emdash3_2_one_cat_native_square_paths.lp)
use OneCat(C) to derive proposition-valued filler Homs. Path induction on the
two side-arrow paths and congruence of the existing square constructor then
prove equality at the actual native Hom classifier. The first flattened-Σ
attempt did not compare with that classifier; the accepted proof preserves
the native codomain rather than adding a classifier equality or rewrite.

The [diagram-map paths](../emdash2/emdash3_2_one_cat_diagram_map_paths.lp)
reflect this native square equality through the NUH-3C3 reconstruction law.
The [adjunction cancellation proofs](../emdash2/emdash3_2_one_cat_adjunction_cancellation.lp)
apply it to inverse mates. Equality after the kernel inclusion gives their
source-side path, and preadditive terminality identifies their zero tips.
Whole map equality and mate cancellation then give f=g. The cokernel proof
uses the dual endpoint observations and the original initial structure.
There is no W/V lookup or selected uniqueness proof in either derivation.

The [ordinary records](../emdash2/emdash3_2_one_cat_adjunction_records.lp)
now expose `kernel_adjunction_record` and `cokernel_adjunction_record` from
S, OneCat(C), the terminal/initial structures, whole adjunction structure and
the original diagram d. Their objects and structural maps are literally
K(d), Q(d) and the counit/unit observations. Every factor centre is the actual
mate of the original-diagram test introduced from its raw annihilator data.
The native reconstruction theorem proves the factor equation, and the newly
derived cancellation plus Hom sethood supplies its IsContr evidence.
The factor's local λh retains h's own endpoint until its concrete test is
substituted, so no additional equality premise is smuggled into the proof.

The two existing generic HFiber proofs were moved unchanged into
[hfiber_cancellation](../emdash2/emdash3_2_hfiber_cancellation.lp).
The old hom_factor_universality module imports them; all six original
signatures and bodies across that split are verified unchanged. The new
record source imports the legacy record classifiers/constructors as output
vocabulary, but has no W/V capability, presentation, or selected-contraction
reference. Its ordinary interpretation retains the explicit C1; the generic
whole H interface has not been truncated.

The [selected views](../emdash2/emdash3_2_one_cat_adjunction_selected_views.lp)
prove that the new lift/colift agrees with the retained presentation-record
operation at the same endpoints. They use new cancellation and both
reconstruction equations; they do not transfer the old uniqueness evidence
into the new records or claim equality of complete record packages.

The [record reviewer](../emdash2/examples/one_cat_adjunction_records.lp)
checks literal object/structural projections, computed mate centres, original
raw-arrow reconstruction, and public uniqueness for both records. The
[square reviewer](../emdash2/examples/one_cat_native_square_paths.lp)
checks ordinary filler independence and preserves the nontruncated boundary.
The old factor-universality consumer remains green. This tranche introduces
no primitive, runtime rule or unifier; it uses the explicit ordinary shape
law added in NUH-3C3.

Serial guarded, warning-enabled logs in `emdash2/logs/probes/`:

- `one_cat_adjunction_records-20260913-055613.log`;
- `one_cat_native_square_paths-20260913-060423.log`;
- `emdash3_2_hom_factor_universality-20260913-060428.log`;
- `hom_factor_universality-20260913-060433.log`;
- `nuh3c_record_dependency_baseline-20260913-060439.log`;
- `emdash3_2_one_cat_adjunction_selected_views-20260913-060446.log`;
- `nuh3c_selected_record_dependency_baseline-20260913-060453.log`.

After the reconstruction review, the unchanged record and native-square
reviewers passed again in `one_cat_adjunction_records-20260913-065713.log`
and `one_cat_native_square_paths-20260913-065741.log`. The clarification
itself changes documents only; no broader typecheck was run.

The old factor source and consumer preserve the complete 1,244 critical-pair
/ 169 pattern inventory against the 054703 source baseline. Both new record
and selected-view consumers match their exact dependency joins at 1,286/169,
including locations, heads and participant families. ANSI-stripped parsing
has no issues. Nine focused LHS audits and the catalog check pass; source
health is refreshed with `--no-check`. All validation remains localized.

**NUH-3 implementation checks pass at its stated ordinary-view boundary;
the subsequent review retains the whole reconstruction under the explicit
computational/internal criterion above. Checkpoint: 1ea98f63.**
Whole K/Q/mates and H have independent entry points, and the ordinary records
are now derived without W/V inputs. Whole structure existence is still
supplied; this does not construct a concrete model or finish the whole goal.

**Next NUH-4A:** migrate the homology-family record consumer to independent
U/Q and C1. The existing HomologyRecord already stores its actual boundary
factor separately, so retain β=K(h)∘η rather than substitute the ordinary
record's canonical test lift. Keep the actual Q observation on the whole
introduced boundary diagram. Also introduce packaged chain-pair inputs
through the direct raw constructor before any kernel selection. Preserve
legacy realization comparisons and the later connecting/exactness, model and
snake-comparison obligations. Op, spectral research and old symbolic endpoint
experiments remain deferred.

### NUH-3C3: Whole observation of walking-arrow diagrams

**Second gate implemented (2026-09-13), following 7b33dbc2.** The active
Join interface is a primitive nondependent recursor stress test. It does not
currently supply the whole reconstruction principle needed here. The new
[ordinary reconstruction owner](../emdash2/emdash3_2_one_cat_diagram_reconstruction.lp)
therefore adds the standard shape-universality assembly explicitly:

```text
one_cat_diagram_reconstruction_iso(C1)
  : DefIso(End(Arr(C)), D_C∘E_C, id_Arr(C)).
```

This is one new declaration-backed primitive law, not a theorem derived from
the old join β rules. It is a whole natural computational isomorphism, with
an explicit OneCat parameter, coherent existing DefIso inverse cuts, and
identity components at both walking-arrow endpoints in both directions.
Four endpoint projection rules implement those observations. The law does
not identify arbitrary diagram objects or demand that D_C and E_C be
judgmentally inverse functors. Its ordinary interpretation is the canonical
natural comparison with the diagram reconstructed from the actual generator.
This added shape law must remain explicit in the final trust/primitive audit.

The [generic reconstruction paths](../emdash2/emdash3_2_functor_reconstruction_paths.lp)
derive map reflection from a whole natural isomorphism G∘F≅id by its
component inverse and the existing strict naturality theorem. Applied to
E_C, D_C and the new shape comparison, they derive
`one_cat_diagram_observation_reflect_path`. No per-test injectivity premise
is added. The generic proof's strict-transfor profile is documented; the
actual shape consumer has the explicit ordinary target profile.

Defined component views of the natural isomorphism supply actual maps
Arr(d[generator])⇒d and d⇒Arr(d[generator]). The
[original-diagram inputs](../emdash2/emdash3_2_one_cat_zero_diagram_inputs.lp)
compose these with the existing raw zero tests. They produce J(X)⇒d and
d⇒I(X) at the original arbitrary d, recovering the original incoming or
outgoing b. No kernel is selected and no diagram object is replaced by an
equality cast. The reconstruction and input source graphs have twenty-three
and thirty-two modules respectively, with no selected universal owners.

The [reconstruction reviewer](../emdash2/examples/one_cat_diagram_reconstruction.lp)
checks all four endpoint computations, both whole inverse cuts, reflection
for arbitrary diagram maps, rejection of an unrelated image, and retained
mixed/next-Hom action. The
[input reviewer](../emdash2/examples/one_cat_zero_diagram_inputs.lp) checks
both original-diagram raw-arrow recoveries. Both legacy record modules also
check in the same import join with the new law.

The first candidate used the reducible walking_arrow_src/tgt aliases on its
rule LHSs. Subject reduction passed, but endpoint evaluation unfolded those
aliases before the new rules matched. A bounded computed-term inspection
identified that mismatch. The accepted patterns use the actual join
inclusions with the two Terminal shape arguments and inferred fapp0 slots
left anonymous. Explicit argument additions and extra aliases were not the
repair; no new unifier or compound inferred-type guard was needed.

Final serial, warning-enabled, resource-guarded logs in `emdash2/logs/probes/`:

- `one_cat_diagram_reconstruction-20260913-050720.log`;
- `one_cat_zero_diagram_inputs-20260913-050725.log`;
- `nuh3c_reconstruction_dependency_baseline-20260913-050302.log`;
- `emdash3_2_one_cat_diagram_reconstruction-20260913-050308.log`;
- `nuh3c_zero_diagram_dependency_baseline-20260913-050730.log`;
- `nuh3c_reconstruction_legacy_baseline-20260913-050950.log`;
- `nuh3c_reconstruction_legacy_join-20260913-050957.log`;
- `nuh3c_zero_diagram_rules_baseline-20260913-051231.log`.

There are exactly eight added critical pairs: each new endpoint rule overlaps
at its two tapp0 levels with the inherited Cat-valued constant-family
component rule. All have tapp0_fapp0 heads; no pattern warning is added.
The complete delta, including locations and participant families, is the
same in the direct source, raw-input and legacy-record joins. Their counts
are respectively 1,165→1,173 / 157, 1,245→1,253 / 169, and
1,278→1,286 / 169. All inherited inventories are preserved, with no parser
issues after ANSI stripping. These are classified component-profile overlaps;
the accepted ordinary-owner computation does not install new generic
naturality or inverse-laxity rules. The user-deferred profile migration and
Empty audits are not resumed. Ordinary subject reduction, the actual
consumers and all five focused LHS audits pass. Catalog and source-only
health are synchronized; no aggregate typecheck was run.

**First gate implemented (2026-09-13), following 4d3c88da.** The defined
[observation functor](../emdash2/emdash3_2_walking_arrow_native_observation.lp)
E_C:Arr(C)→LaxArrow(C) is the existing native graph of the whole evaluation
transformation at the walking-arrow generator. It adds one definition and
no primitive, rewrite or unifier. Its seventeen-module source graph contains
no selected universal owner.

The [reviewer](../emdash2/examples/walking_arrow_native_observation.lp)
checks the actual generating arrow, both components of arbitrary diagram
maps and the whole next Hom action. At the explicit ordinary profile,
D_C=`one_cat_arrow_diagram_func(C1)` is the existing return functor, and
E_C(D_C(edge)) computes to the original constructor-visible edge.

The separate diagnostic `tmp/probes/nuh3c_diagram_native_observation.lp`
also checks that reflexivity does not currently prove D_C(E_C(d))=d for an
arbitrary d. This is a computation boundary, not evidence against the
mathematical representation theorem. That negative diagnostic is not
registered as a permanent library requirement against a future inverse law.

The required direction for ordinary uniqueness is faithfulness of E_C.
The observed object round trip proves no whole faithfulness statement.
Even a whole inverse law for E_C∘D_C would establish faithfulness of D_C;
the required E_C direction instead needs the comparison involving D_C∘E_C
on arbitrary diagrams and maps. Preserve this distinction in the next gate.

Guarded, warning-enabled logs under `emdash2/logs/probes/`:

- `gray_transformation_graph-20260913-043120.log` (existing owner baseline);
- `nuh3c_diagram_native_observation-20260913-043248.log` (diagnostic);
- `walking_arrow_native_observation-20260913-043430.log`;
- `nuh3c_native_observation_dependency_baseline-20260913-043435.log`.

The registered reviewer and exact dependency join have identical complete
1,165 critical-pair / 157 pattern inventories, with no parser issues after
stripping ANSI codes. Both focused LHS audits and the catalog check pass;
source health is refreshed without aggregate typechecking.

**Then scheduled NUH-3C4 (implemented above):** derive equality of native squares from equality of their
two side arrows at OneCat, using proposition-valued filler Homs. Apply the
new faithfulness theorem to inverse mates, deriving monicity/epicity of the
whole structural maps. Reconstruction supplies the chosen factors; Hom
sethood and cancellation then supply their IsContr evidence and the full
ordinary kernel/cokernel records. Preserve the actual d, K(d) and Q(d), and
do not transfer old W/V uniqueness or substitute component equality for a
whole map comparison. Concrete model construction, packaged input migration
and later homology consumers remain open.

### NUH-3C2: Reconstruction from whole mates and structural maps

**Implemented (2026-09-13), following 6b4500e2.** The ten existing ordinary
diagram observations/zero paths now live in
[zero_arrow_diagram_observations](../emdash2/emdash3_2_zero_arrow_diagram_observations.lp),
separate from the two old annihilator-package adapters. All twelve original
symbol signatures and semantic bodies are preserved, verified against the
pre-edit source after removing comments/whitespace. The independent owner
imports additive structure, zero-arrow diagrams and the existing strict
component theorem, without selected universal definitions.

The new [whole-mate observations](../emdash2/emdash3_2_kernel_cokernel_adjunction_observations.lp)
derive six equations at the actual whole K/Q. Applying the existing whole
unit/counit formula gives the inverse mate's source/target component.
Mate cancellation then proves k∘lift(h)=h₀ and colift(h)∘q=h₁.
The actual counit/unit supplies d∘k=0 and q∘d=0. There is no W/V lookup,
factor-space transport, new primitive, rewrite or unifier. The raw consumer
retains OneCat; the general zero-observation source documents its use of the
current strict component theorem.

The two independent source graphs have thirteen and seventeen modules, with
no selected kernel/cokernel or presentation owners. Three legacy proof
bodies now delegate through the existing one-way presentation adapters:
the inverse-kernel-mate source path and both annihilation proofs. Their old
record uniqueness still transfers selected W/V evidence; it is not claimed
to be derived yet.

The [reviewer](../emdash2/examples/kernel_cokernel_adjunction_observations.lp)
applies both reconstruction theorems to the original raw inputs, recovering
the supplied b, and checks both structural zero equations at the original
d. Negative cases reject replacing either b by an unrelated arrow.
All definitions also check at arbitrary diagram maps in the owning source.

Serial guarded, warning-enabled logs under `emdash2/logs/probes/`:

- `kernel_cokernel_adjunction_observations-20260913-042444.log`;
- `emdash3_2_zero_arrow_universal_tests-20260913-042542.log`;
- `kernel_adjunction_records-20260913-042547.log`;
- `cokernel_adjunction_records-20260913-042553.log`;
- `nuh3c_observation_dependency_baseline-20260913-042600.log`.

The relocated legacy source retains its complete 1,244 critical-pair / 169
pattern inventory against 041938; both record reviewers retain 1,249/169
against 042224/042230. The new reviewer matches its dependency-only join at
1,221/169, including locations, heads and rule families. There are no parser
issues after stripping ANSI codes. Seven focused LHS audits and the catalog
check pass. Health is refreshed with `--no-check`; validation stays local.

**Then scheduled NUH-3C3 (first gate implemented above):** establish the missing ordinary diagram-faithfulness or
whole representation comparison before deriving full ordinary uniqueness.
An exact existing candidate for observation is the native graph
`gray_transf_graph_func(diagram_evaluation_transf(generator))`, from Arr(C)
to LaxArrow(C). The return functor is `one_cat_arrow_diagram_func(C1)`.
Review their actual whole actions and the needed inverse comparison at
OneCat. The current join/walking-arrow sources provide introductions and
computing observations but no demonstrated whole inverse/faithfulness law;
equal endpoint components do not by themselves supply equality of arbitrary
transformations in the active syntax. Prefer the native whole categorical
comparison over a per-test injectivity premise, broad object cast, bare
variable eta rule or a return to selected W/V proofs. Op/profile migration
remains deferred.

### NUH-3C1: Native introduction of ordinary zero-composite inputs

**Implemented (2026-09-13), following bc6bf2bd.** The existing whole
`one_cat_arrow_diagram_func` now has a defined view of its native square
action at canonical walking-arrow endpoints. The new
[input module](../emdash2/emdash3_2_one_cat_zero_arrow_inputs.lp) uses this
action to introduce J(X)⇒Arr(d) from b,d,d∘b=0 and, dually, Arr(d)⇒I(X)
from d,b,b∘d=0. `path_to_hom` turns the given equation into the existing
native square filler, retaining its required direction. The kernel-side
input also forms an object of the existing ZeroArrowCone_cat directly.
OneCat remains explicit. No kernel is selected merely to form an input.

These are realization-facing raw-data adapters. They do not replace native
diagram/Hom ownership or make manual factor operations the formal program.
Universality remains the whole adjunction mate; H remains Q∘Arr(K(h)∘η).
All four new implementation symbols are definitions, with no new primitive,
rewrite, unifier or object cast. The input module's eighteen-module transitive
source graph has no selected universal owner. Existing packaged chain-pair
and Freyd adapters are not yet migrated to this direct constructor.

The [input reviewer](../emdash2/examples/one_cat_zero_arrow_inputs.lp)
checks the actual source/target components in both directions, the original
native first/diagram data, and rejection of an arbitrary pair with no
zero-composite evidence. The
[H consumer](../emdash2/examples/zero_composite_adjunction_homology.lp)
checks retained whole h, the boundary's mate characterization and global H
formation using only the independent K/Q structures.

A direct reflexivity assertion for the last mate characterization failed to
compose two established diagram-point unifiers (040929 log). The reviewer
instead specializes a generic proof obtained by applying the existing whole
`adjunction_transpose_semantic_path`. That proof passes at the actual raw
input. It is test evidence, not an installed equality rule or an object cast.
No failed comparison was hidden by changing the native input or its result.

Final guarded, warning-enabled logs under `emdash2/logs/probes/`:

- `one_cat_zero_arrow_inputs-20260913-040913.log`;
- `zero_composite_adjunction_homology-20260913-041519.log`;
- `one_cat_arrow_diagrams-20260913-041154.log` (legacy regression);
- `nuh3c_input_dependency_baseline-20260913-041158.log`;
- `nuh3c_homology_input_baseline-20260913-041254.log`.

The legacy reviewer retains its complete 1,144 critical-pair / 157 pattern
inventory. The input reviewer matches its dependency-only join at 1,216/169;
the H consumer matches its join at 1,221/169. Categories, locations, heads
and rule families agree, with zero parser issues after stripping ANSI codes.
The H baseline follows the consumer's dependency import order: a different
order moved two existing terminal/product critical-pair report locations,
without changing the pairs themselves.

Strict LHS audits pass for all four affected source/reviewer files. Catalog
and source-only health are synchronized; no aggregate typecheck was run.

**Then scheduled NUH-3C2 (implemented above):** derive reconstruction at the actual kernel/cokernel mate
and structural maps, then the ordinary universal records. The remaining
diagram reconstruction/faithfulness evidence must be proved at the stated
ordinary profile. Do not infer arbitrary diagram eta or equality of
diagrams merely from their observed generator, and do not transfer the old
W/V uniqueness evidence into a renamed interface. The new constructors
currently concern introduced diagrams; extend their scope only with the
required native comparison. Packaged input and concrete model migration,
connecting and exactness remain subsequent work.

### NUH-3B: Independent whole H-family and native input-category consumer

**Implemented (2026-09-13), following c897aa0c.** The semantic chain
K∘D, β=K(h)∘η_A and H=Q∘Arr(β) now lives in
[homology_adjunction_families](../emdash2/emdash3_2_homology_adjunction_families.lp),
whose inputs are KernelAdjunctionStructure/CokernelAdjunctionStructure.
The six old W/V-indexed names delegate through the presentation adapters;
there is one semantic implementation. The
[native global application](../emdash2/emdash3_2_zero_arrow_cone_adjunction_homology.lp)
uses the existing zero-arrow-cone category and its explicit OneCat profile.
This adds seven definitions and no primitives, rewrites or unifiers.

The independent family and global H have ten- and sixteen-module transitive
source dependency graphs respectively. Neither contains selected W/V,
ComputationalKernel/Cokernel or KernelPresentation/CokernelPresentation
owners. The native input constructor retains (A,d,h:J(A)⇒d) without any K/Q
selection. This does not yet convert raw chain-pair zero evidence into h;
the older chain-pair adapter still uses its selected boundary lift.

The [family reviewer](../emdash2/examples/homology_adjunction_families.lp)
checks the whole boundary source/target and generator, nonidentity boundary
and H action, further-Hom identity, and rejection of an unrelated arrow.
The [native reviewer](../emdash2/examples/zero_arrow_cone_adjunction_homology.lp)
checks input formation, retained h, the actual mate boundary, and H at the
actual introduced diagram. The
[legacy comparison](../emdash2/examples/homology_adjunction_legacy_views.lp)
checks whole β, family H and global H conversion through the adapters.

The pre-edit native selected-point regression exceeded the 2 GiB guard,
including alone in a fresh compiled-dependency stage. Its assertion is now
checked compositionally: the unchanged retained path with its named target,
the generic selected-object recipe, and the three native input projections.
All of these pass against both the pre-edit c897aa0c sources and the current
sources under the same guard. No implementation theorem, selected value or
premise was weakened; no resource limit was raised. The old expanded
assertion's resource failure is not mathematical counterevidence.

Final serial, warning-enabled guarded probe logs in `emdash2/logs/probes/`:

- `emdash3_2_zero_arrow_cone_adjunction_homology-20260913-031404.log`;
- `homology_adjunction_families-20260913-032749.log`;
- `zero_arrow_cone_adjunction_homology-20260913-033250.log`;
- `homology_families-20260913-034631.log`;
- `one_cat_zero_cone_homology-20260913-034639.log`;
- `homology_adjunction_legacy_views-20260913-035044.log`;
- `homology_adjunction_dependency_baseline-20260913-035052.log`.

New consumers and their dependency-only join retain the complete 1,151
critical-pair / 159 pattern-warning inventory. Both legacy regressions retain
their complete pre-edit 1,249/169 inventory, including heads, rule families
and locations; the whole legacy comparison has that same inventory. ANSI
codes were stripped before parsing, with zero parser issues. The baseline
global reviewer failed only after all imports had finished, so its import
warning comparison does not misrepresent it as a passing regression.
Strict LHS audits pass for all nine affected source/reviewer files. The
catalog check passes and health source metrics are refreshed with
`--no-check`; no aggregate typecheck was run.

**Then scheduled NUH-3C (started above):** derive the ordinary universal records from the whole
adjunction comparison without W/V. The current kernel/cokernel record
modules still mate/unmate an old selected lift and transfer its IsContr
evidence, so renaming their inputs is insufficient. Establish the needed
native diagram introduction/observation at the explicit ordinary profile,
then derive the factor and uniqueness views. Raw chain-pair conversion,
concrete models, connecting and exactness remain subsequent work. Op,
strict/lax migration and symbolic endpoint debugging stay deferred.

### NUH-3A: Whole K/Q structures without selected W/V inputs

**Implemented first slice (2026-09-13).** The active nucleus remains at blob
91f1974ece225e399604dce24710bf1437ad3ef5. New registered extensions provide:

```text
KernelAdjunctionStructure ≔ Σ K : Functor(Arr(C),C), Adjunction(J,K)
CokernelAdjunctionStructure ≔ Σ Q : Functor(Arr(C),C), Adjunction(Q,I)

J(X) = (X→0),       I(X) = (0→X).
```

The preadditive context and selected terminal/initial structures remain
explicit. Constructors take only the whole functor and its native adjunction
evidence. K/Q action is the existing fapp calculus. Domain of the counit
gives the whole kernel inclusion; codomain of the unit gives the whole
cokernel projection. Forward/backward universal maps reuse the native
adjunction Hom comparison and its whole/point cancellation. No new primitive,
rewrite, unifier or per-test factor dictionary is introduced.

The [structure module](../emdash2/emdash3_2_kernel_cokernel_adjunctions.lp)
and [mate module](../emdash2/emdash3_2_kernel_cokernel_adjunction_mates.lp)
have an eleven-module transitive source dependency graph containing no
HasComputationalKernels/Cokernels, ComputationalKernel/Cokernel or old
KernelPresentation/CokernelPresentation dependency. This is an independent
entry point, not a wrapper requiring the old selections.

The two old presentation modules now expose explicit one-way adapters into
these structures. Their inclusion/projection bodies delegate to the new
implementation, retaining the original K/Q, adjunction evidence and selected
comparisons. The old selected data do not disappear from those legacy
interfaces or become automatically derivable from a raw algorithm. Concrete
whole-model construction and reifier automation remain NUH-5 work.

The [new reviewer](../emdash2/examples/kernel_cokernel_adjunctions.lp)
checks direct introduction, arbitrary diagram-map action, whole and point
mate cancellation, rejection of unrelated arrows, and actual unit/counit
components. Both old selected-presentation reviewers remain green.

Validation used serial guarded probes with warnings enabled. Logs under
`emdash2/logs/probes/`:

- `emdash3_2_zero_arrow_diagrams-20260913-021825.log` — dependency baseline;
- `emdash3_2_kernel_cokernel_adjunction_mates-20260913-022044.log` — both new sources;
- `kernel_cokernel_adjunctions-20260913-022706.log` — new reviewer;
- `kernel_adjunction_presentations-20260913-023015.log` and
  `cokernel_adjunction_presentations-20260913-023020.log` — legacy regressions;
- `whole_adjunction_dependency_baseline-20260913-023656.log` — exact dependency join.

New reviewer/dependency inventories agree at 1,156 critical-pair and 159
replaceable-pattern warnings. Each legacy reviewer retains its complete
1,244/169 inventory, with locations mapped through unchanged source lines
against the respective pre-edit 022458/022506 logs. Strict LHS audits pass.
The central catalog is unchanged and checked; health source metrics were
refreshed with `--no-check`, explicitly without a repository-wide typecheck.

**Then scheduled NUH-3B (now implemented above):** move the whole H-family semantic implementation to these
independent structures, leaving selected presentations as realization
adapters. Derive the needed ordinary universal views and preserve actual H
selections in subsequent consumers. Do not resume Op work as a prerequisite.

### NUH-1D6: Whole local y/v projection — user-deferred

This experiment is parked without promotion. Its source variants, helper
terms and logs have been copied from /tmp into
`emdash2/tmp/deferred-native-duality/2026-09-13-nuh1d6/`, with a manifest
hashing all 30 preserved files. The latest candidate and review sources are
also tracked under
[deferred_native_homd_y](../emdash2/audits/deferred_native_homd_y/README.md).
The last complete qualified checkpoint is 29f847f7. The latest candidate
still fails subject reduction at its whole y-projection fold; earlier
object/restriction checks passed, and arrow retyping exposed a represented
unit comparison. Do not resume these experiments until the deferred work
is explicitly reactivated. NUH-3 is the current task.

The preceding `29f847f7` turn is progress: the direct target now preserves
the native primitive/Op source and reaches a specific downstream y-view.
At resumption the worktrees are clean and the baseline/source anchors agree.

First route the existing defined homd_id_tgt_func/homd_ff_tgt_func views
through the preserved primitive homd_tgt_func, with its Transpose(Hom)
codomain. This alone does not establish their projection from the whole
shared-index value or repair the following displayed-action fold.

Test the whole local inclusion D[y]×Transpose(Hom_Z(x,y))→S_D(x), using
native Sigma base change and dual functors. The earlier attempt stopped
at a pulled-back opposite family whose total should be a constant-family
product. Check existing comparisons first. If proof-time normalized-head
comparisons are necessary, isolate them at their Op/reindexing and Sigma
owners; preserve the original runtime histories. This is now a direct
native y-projection consumer, not auxiliary G-family work. Qualify its
whole restriction and the actual following displayed-action projection
before describing the local y/v relationship as repaired.

User clarification during this continuation: strict structural functor/
transfor comparison cells may be rewritten to identity at their actual
coincident endpoints. Such a computation can remove a displayed-laxity
dependency in a structural Sigma-map route; it is not forbidden by the
deferred profile migration. Use it for a concrete strict owner when useful.
Integration of the other profile branch still belongs after this goal.

### NUH-1D5: Original-family input and direct native projections

The previous `f5954098` turn is progress: it preserved a checked
definition-only HomPresheaf correction and changed the next action to the
surrounding target. At resumption all worktrees are clean, the comparison
baseline is an ancestor and the active nucleus is unchanged.

The remaining input distinction is now checked: the corrected HomPresheaf
y-base is Reverse12(Z), so Functor_catd requires its negative input over
Transpose(Reverse12(Z))=CoOnly2(Z). Original D is over Z. Pointwise
transpose has the required base but changes the v-fibre to Transpose(D[y]);
the positive/negative controls reject treating it as the original input.

**Selected continuation (2026-09-13):** retain the shared native index as
the current target candidate, but homwise-dualize its whole value category
so that the original primitive source and displayed-map interface survive:

```text
P_D(x) ≔ Functor_cat(native_index_cat(D,x),Cat)
P_D : CoOnly2_cat(Z) → Cat
Homd_target_catd(D) ≔ native_homwise_dual ∘ CoAbove3_func(P_D)
Homd_target_catd(D) : CoAbove2_cat(Z) → Cat
Homd_target_catd(D)[x] ↪ CoAbove2_cat(P_D(x))

homd_int(FF) : Functord(Op_catd(E), Homd_target_catd(D))
homd_src_func(FF,x) : Op(E[x]) → CoAbove2_cat(P_D(x))
homd_src_sec(FF,x,u) : Functor(native_index_cat(D,x),Cat).
```

The declaration of homd_int is literally unchanged from the preceding
duality prototype, including its original Op_catd(E) source. hom_int,
homd_, Op_catd and Op_funcd also retain their declarations. No new
primitive or unifier is introduced. Applying CoAbove2_func to the source
functor gives the ordinary Transpose(E[x])→P_D(x) view; this is an actual
derived functor, not a primitive redefinition or a category-equality cast.

The first candidate used that unshifted target and changed the source to a
pointwise transpose family. Its initial projections typed, but the full
candidate stopped at tdapp1_int_func_transfd's existing Op_funcd(FF)
composition. Simultaneously dualizing source and target is a smaller
correction: it preserves that composition and checks the existing whole
internal displayed-Hom action declarations. The first source-component
fold then needs only its inferred tdapp0 base changed from $K to `_`.
The first homd_int component fold likewise infers its corrected base.

For fixed y,v, the local inclusion I(y,v):Transpose(Hom_Z(x,y))→S_D(x)
is CoAbove2_func of the existing sigma_intro_tapp0_func at (y,v).
Its point is ((y,v),a). A whole local restriction fold gives
homd_src_sec(FF,x,u)∘I(y,v) ↪ homd_(FF,x,u,y,v). Its constructor-visible
point counterpart covers evaluation after I(y,v)[a] has already reduced.
Both point orders, the restricted whole Hom action and a genuine base
2-cell observation pass. These two native projection rules replace the
old y-only section projection in the copied candidate; that old rule is
commented with its restoration/qualification boundary. Generic runtime
owners and the existing rewrite/unification roles are preserved.

The earlier product/base-change attempt retained a pulled-back opposite
family instead of identifying its total with the expected product. No
reindexing unifier, category cast or Sigma rule was added to force it.
The selected fixed-y,v inclusion reuses the existing Sigma introduction.
General G-family action remains parked.

**Remaining projection boundary:** the explicitly expanded alternative
Hom order retains
`comp(fapp1_func(homd_src_sec), Op_func(fapp1_func(sigma_intro_tapp0_func)))`.
It is well typed, but its comparison with the folded restricted Hom action
is not qualified. More importantly, whole variation of the local restriction
in v is still pending. The retained full-source attempt reaches
homd_id_tgt_func, whose old body piapp0(homd_id_src_sec(...),y) supplies
y where the new shared index requires ((y,v),a). That is the next actual
native consumer to repair; it is not a timeout or an Empty diagnostic.

Durable evidence:

- [copied native-owner patch](../emdash2/audits/native_homd_direct_owner.patch);
- [original-family input controls](../emdash2/audits/native_homd_direct_input_controls.lp);
- [primitive, projection and displayed-action controls](../emdash2/audits/native_homd_direct_owner_controls.lp);
- [expanded Hom-order observation](../emdash2/audits/native_homd_direct_expanded_hom_review.lp);
- [guarded reproducer](../emdash2/scripts/check_native_homd_direct_owner.sh).

The reproducer passed in `/tmp/emdash-homd-direct-owner.y67JN6`: five
positive source/reviewer checks, strict LHS audits, and one bounded full
owner attempt confirming the precise unmigrated y-projection boundary.
The focused prefix extends through the first displayed-Hom source-component
fold and includes only its independent later dependencies in source order.
The copied full candidate keeps those later owners at their original
positions. There are 1,101 critical-pair and 139 replaceable-pattern warnings;
the complete reviewer inventories agree. Comparing the same migrated
declarations with/without the two local folds gives zero warning delta,
including locations mapped through unchanged source lines. This is not
a comparison against the old ill-typed full target or a confluence claim.

The manifest records all hashes and open boundaries. Candidate full source:
`401221ac2b5039341e65c184b3061645a978af209fc5d052036b6c22a9e61ee9`;
accepted focused slice:
`6ec6f50b45b831d54f8f36bb59c74afc4d9d9ee1860a6dd5e99bd080c6f3e073`.
Earlier attempts, including the unselected transpose-source variant, are
retained in `/tmp/emdash-native-homd-direct.ap7vqgzr`.

**Next:** use the preserved native homd_tgt_func to repair the y/v views
and their whole projection/action relationship to the shared-index value.
Address the measured expanded-Hom comparison at its native owner; do not
start a generic whiskering/profile or auxiliary G-map project. The active
nucleus, registered catalog and health evidence remain unchanged. NUH-1
and native integration are still open; no full kernel repair is claimed.

### NUH-1D4: Correct the existing HomPresheaf composition

The preceding `8321a9d3` turn is progress: the direct source/fibre review
isolated the mismatch between total Op(Hom_Z(x,y)) in HomPresheaf and
Transpose(Hom_Z(x,y)) in the corrected native homd_ endpoint. Worktrees,
baseline ancestry and the unchanged active source were checked at resumption.

**Result (2026-09-13):** the isolated definition-only correction computes
the required presheaf fibre and both nonidentity argument actions. The
existing native homd_ endpoint inhabits that computed fibre. Retain this
candidate for the direct target repair; it does not yet complete Homd.

The existing defined HomPresheaf owner now has candidate type and point:

```text
HomPresheaf_catd_func : CoOnly2_cat(Z) → Catd(Reverse12_cat(Z))
HomPresheaf(x)[y] ↪ Functor(Transpose(Hom_Z(x,y)),Cat).
```

Its body uncurries hom_int(id_Z), applies the selected internal presheaf
operation and curries by postcomposition after Product_pair_tele_func.
Four defined helpers provide the existing transpose-universe composition,
an actual product-coordinate functor, the presheaf-universe composition and
the uncurried bifunctor. The product map uses CoAbove3_func and ordinary
projections/pairing. No category equality, cast or product-distribution rule
is introduced. Existing primitive heads and all rewrite/unification rules
retain their roles and full-file positions.

The literal curry_func presentation typed but its point evaluation retained
hom_precomp_along_fapp0. Changing only the observation's Catd/Functor façade
did not resolve it. The accepted fixed-functor curry presentation uses
existing postcomposition and pairing computation; no evaluator change was
made to force the earlier body.

For r:x→x′, the source action sends H to its precomposition along
Transpose_func(Hom_func(r,id_y)); for s:y→y′, the contravariant y-action
uses Transpose_func(Hom_func(id_x,s)). Both whole-function conversion checks
pass at these existing rigid Hom owners. The source action's readable
unary-precomposition comparison uses the existing head-local unifier via
typed eq_refl, followed by eq_ap congruence in a TEST ONLY assertion.
A larger direct eq_refl comparison did not propagate through the nested
context. No extra unifier was added.

The source 2-cell α:r⇒s gives a well-typed transformation from the s-action
to the r-action, as required by CoOnly2_cat(Z). Its point component is also
well typed. The observed normal form still contains generic higher
postcomposition/action projections; the final expected component formula
is **not qualified**. The focused slice excludes later Homd-dependent
component specializations, so this observation is not a claim that the
complete kernel fails to normalize it. Further generic whiskering/profile
work is not selected by this result.

Durable sources and gate:

- [definition-only owner patch](../emdash2/audits/hom_presheaf_transpose.patch);
- [point and actual homd_ endpoint controls](../emdash2/audits/hom_presheaf_transpose_controls.lp);
- [source/target arrow controls](../emdash2/audits/hom_presheaf_transpose_action_controls.lp);
- [typed source-2-cell observation](../emdash2/audits/hom_presheaf_transpose_two_cell_review.lp);
- [guarded focused driver](../emdash2/scripts/check_hom_presheaf_transpose.sh).

The driver passed in `/tmp/emdash-hom-presheaf-transpose.b0DD7D`. It checks
baseline/candidate slices and all three reviewers serially with ordinary
SR and the resource guard. Every stream has 1,055 critical-pair and 137
replaceable-pattern warnings; complete inventories agree after mapping
unchanged source lines. Strict LHS audits pass with zero unreviewed slots.

The baseline includes the earlier total-op/further-shift patches. Relative
to it this tranche adds zero primitives, rewrite rules or unification
rules and relocates no existing rule. The copied full candidate is retained
but not checked as a complete kernel. Its SHA-256 is
`95c8898dd8b87f4122c2860acd1c089e0810f8e6ccb7f8ca4d896ce7d25284ea`;
the checked candidate slice is
`910b2c9cf0609b14be233cb5275e87058bbe14066ffcc680815480f5aac4fcf3`.
The manifest pins baseline/reviewer hashes and records the unqualified
higher-component and full-kernel boundaries explicitly.

The focused view retains independent later constant-section/pairing and
full fapp1 identity/composition dependencies in their original relative
source order. These are not moved in the full candidate. The driver checks
that all code outside the defined HomPresheaf region remains identical.
The reviewers are non-library evidence; registered checks, catalog and
health source metrics remain unchanged, so no aggregate was run.

**Next:** repair the surrounding target's original D-family slot and the
native projection ladder using this corrected presheaf variance. Evaluate
the smallest existing-owner composition before selecting additional target
packaging. Keep the primary homd_int(FF), its native meaning, primitive
pointwise Op_catd and existing rule architecture. Auxiliary G-family action
remains parked. NUH-1 stays active and NUH-2 source promotion is pending.

### NUH-1D3: Direct homd_int adjustment before auxiliary expansion

The current task is to compare the existing homd_int declaration, target
constructor and projection ladder with the smallest internally coherent
duality correction. Preserve the fixed-endpoint homd_ meaning and the
primary homd_int(FF) constructor. Identify exactly which old target
factorization fails and whether it can be repaired with the existing
owners before committing to a replacement target classifier.
Preserve the existing rewrite/unif split, normal forms and owner placement.
Do not import auxiliary comparison/relocation experiments merely because
they made a copied prefix easier to check.

The first direct review now checks the old recipe against two small
substitutions, using only assertions on the unchanged preferred Op prefix.
The reviewer is
`emdash2/tmp/probes/native_homd_target_minimal_variance_review.lp`; its
guarded log is
`/tmp/emdash-pointwise-op-review.m_iorhfg/minimal-target-review.log`.
The check passes with the expected type rejections and positive fibre
observations; it introduces no declaration, rule or unifier.

| Existing recipe or substitution | Checked result |
| --- | --- |
| Functor_catd(Op Z,D,HomPresheaf(x)) | D is over Z but its slot requires Catd(Transpose(Op Z))=Catd(R Z) |
| Change only that outer base to Transpose Z | D's slot fits, but HomPresheaf(x) remains over Op Z |
| Supply Op_catd(D) at the original Op Z base | This application types, but its fibre has source Op(D[y]); it changes the intended covariant v-input |
| HomPresheaf(x)[y] in the preferred prefix | Computes to Functor(Op(Hom_Z(x,y)),Cat) |
| Corrected native homd_(FF,x,u,y,v) | Has source Transpose(Hom_Z(x,y)), rather than total Op of that Hom |

Thus neither simple substitution is an accepted repair. There is also a
separate variance-only-versus-total-dual issue inside the existing
presheaf-classifier pipeline. Address that pipeline's actual source/fibre
types next, preserving the primitive pointwise Op_catd meaning and existing
rule architecture. These checks do not prove that every repair using the
existing target architecture fails, or that the shared-index replacement
is minimal. The active nucleus remains unchanged.

The shared index bundles existing y,v,a arguments; it is a candidate
target-packaging change, not a new foundation. Its minimality has not
been established. General G:D→D′ index action is auxiliary and does not
precede this direct review. Do not use the auxiliary action to reconstruct
homd_int(FF) from an identity case as its primary definition.

Keep candidate construction files separate from reviewer assertions.
Typed eq_refl tests of a unifier are checks, not equality-based family
constructions. The quoted native_op_pullback_agrees temporary test was
rewritten as an explicit typed assert; the focused check still passes.
No such symbol is part of the active library.

The subsequent Op_catd clarification is settled: it remains primitive
pointwise opposite. Op_func(E):O(K)→O(Cat) and Op_func(π):O(ΣE)→O(K)
are separate operations. No total-projection reinterpretation of Op_catd
is being pursued. The focused assert-only reviewer
`emdash2/tmp/probes/native_op_catd_pointwise_review.lp` passes on the
unchanged preferred prefix in `/tmp/emdash-pointwise-op-review.m_iorhfg`.
It checks the primitive/composite fold, unchanged object values under
CoAbove2_func(E), total opposite at the fibre and its next Hom, and the
reversed base-2-cell action. No rule or theory declaration is added by
that reviewer, and the active nucleus remains unchanged.

### NUH-1D2: Auxiliary family-map action — parked

The previous `5b2714c0` turn supplied semantic explanation, but the user
clarified that the implementation is the selected finite native syntax,
not a general D_S API. The current design now records that distinction.
The existing native source-arrow reviewer passed at resumption on the
unchanged copied prefix; all worktrees and baseline ancestry were checked.

For G:D→D′, set g=Sigma(G). The existing whole projection rule gives
π′∘g=π. Thus the represented family hom_(π′,x), reindexed along g,
recovers hom_(π,x). Apply the native opposite-family reindexing interface,
then sigma_pullback_total_func(CoAbove2_func(g),...), then CoAbove2_func.
This should define S_x(G):S_x(D)→S_x(D′) with point action
(y,v,a)↦(y,G_y(v),a). It uses existing internal functor constructors.

The whole functor and its point projection check, as does the target's
contravariant precomposition. The arrow application normalizes to a pair
of Sigma(G)[m] and the original theta. A separately reintroduced raw pair
did not elaborate at opaque Sigma endpoint/projection comparisons; that
observation remains unqualified. No new comparison was added to force it.

The complete retained stage is
`/tmp/emdash-native-index-family-map._ytjursm`, with a parked source patch,
manifest and logs. This experiment introduced one proof-time reindexing
comparison in copied sources, moved existing pullback/base-change rules
earlier and added the stable-constructor beta instance. It changes no
active LP source and is not promoted. The source and tests are outside
the active queue until a direct native action consumer needs this work.

The original opposite/reindexing compatibility was already a unif_rule,
matching Op_catd of a literal composite. The preserved total-op patch
first adapted that same rule to CoAbove2_func(F), with the outer Pullback
base slots wildcarded. The v1 consumer failed after its represented family
had reduced beyond that literal-composite pattern. The additional copied
comparison handled that shape, but its necessity versus a better consumer
presentation has not been established. It is not selected for promotion.
Explicit CoAbove2_cat(A/B) arguments in typed test expressions are not
rule-LHS guards; both candidate unif patterns used `_` in those outer slots.

### NUH-1D: Selected native duality owners and internal application

The current [native owner design](TYPESCRIPT_EMDASH_DUALITY_SEMANTIC_THEORY.md)
records actual code status and the selected Op_cat/CoAbove2_cat constructors,
the supporting CoAbove3_cat prototype, derived transpose operations and
their internal functor/projection ladders. The general D_S and transported
tensor exposition in `5b2714c0` was not an implementation; the user's
clarification rejects treating it as the architecture. Native Homd target
and action integration remain unfinished.

The next work is NUH-1D3's direct homd_int owner review and adjustment,
then NUH-2 through the whole-universality and homology rows. Use the actual
native owner types and existing positive computations. Do not reopen
prototype strictness or Empty experiments to select that next action.

### NUH-1B2h: Prototype strictness/profile continuation deferred

The preceding `66e5f87c` checkpoint recorded the profile diagnostic.
The user subsequently directed us to set that investigation aside and
focus on the mathematical Op/duality theory. The independent migration in
`goal/opaque-action-profile-classifiers-v3.2` will be integrated only after
this goal; it is not a current prerequisite and no merge is scheduled here.

A finite comparison-leg experiment begun before the clarification is
retained only as ignored recovery material in
`emdash2/tmp/probes/native_transformation_profile_model_deferred.py`.
It is outside the active queue. No profile source patch was made.
The earlier directive below to continue this row before native integration
is superseded by the user's clarification and NUH-1D above.

### NUH-1B2g: Family/section profile inconsistency isolated

The preceding `0b419ddb` turn is progress: structural source arrows and
source-2-cell components now compute in the isolated native-index
prototype. The active worktree is clean at resumption and baseline ancestry
is preserved. Validation remains localized under the user's instruction.

The hypothesis is confirmed. A rule-free consumer of
functord_transport_strict_naturality, with FF an arbitrary ordinary F:K→A
viewed as const(1)→const(A), derives F(x)=F(y) for every p:x→y. The
specialization K=A=Grpd, F=id and p:Empty→Unit then yields τ Empty_grpd
by ordinary equality elimination. No homology/exactness or earlier Empty
witness is used.

The [profile diagnostic](TYPESCRIPT_EMDASH_FAMILY_SECTION_PROFILE_DIAGNOSTIC.md)
preserves three rule-free routes. Earlier ordinary object-level cuts also
derive Empty. In a preferred-total-op slice before Sigma, Op_catd and
homd_int, subtracting those two cuts rejects that route but leaves an
Empty derivation through two stable-head ordinary naturality comparisons.
Subtracting those comparisons too rejects both recorded earlier routes.
Constant-section views, evaluation and ordinary forward action still
check. Remaining strict whole/capped cuts are not yet qualified.

The reproducible guarded gate is
`emdash2/scripts/check_family_section_profile.sh`; its complete retained
stage is `/tmp/emdash-family-section-profile.GGJG5j`. The active source
consumer retains 1,144 critical-pair / 157 pattern warnings. All three
prefix variants retain 856 / 134, with complete inventories agreeing after
unchanged-line mapping; rule-free positive inventories agree exactly.
All three source LHS audits and four fixture audits pass. No active LP
source changed, and no repository-wide typecheck ran.

This rejects the blanket strict reading of Functord while retaining the
native-index prototype's conditional strict-reference meaning. The result
is a scoped native-family prerequisite, not a reason to replace native
Hom foundations or to investigate the deferred endpoint checker. Continue
with NUH-1B2h's connected profile design before generic native integration.

### NUH-1B2f: Structural Sigma action before native Homd

The preceding `39f5669e` turn is progress: the whole x-family and its
source-point/target-precomposition computations were qualified as a strict
reference experiment. At resumption the worktree is clean, baseline
ancestry and active nucleus identity are preserved.

Hypothesis: Sigma of the actual opposite represented precomposition map
acts on a constructed arrow (m,θ) by retaining m and applying the existing
whole opposite fibre precomposition functor to θ. The required endpoint
comparison is the ordinary pre/postcomposition interchange already owned
by the Hom calculus. Probe this structural constructor beta at the Sigma
map owner before homd_int; do not use the later generic displayed-laxity
extraction or supply an inverse laxity cell. Then test the original triangle,
source-arrow action and base-2-cell components, with warning comparisons.

The active source's later strict-Functord comparison comment is not blanket
authority to reinterpret every family/section interface as strict. In
particular, the constant-section comparison with ordinary Functor(K,A)
retains arbitrary base-arrow action. This experiment uses the specific
represented precomposition map's mathematical strictness; the general
profile boundary remains an explicit obligation.

The [structural patch](../emdash2/audits/native_sigma_precomp.patch) now
provides one defined arrow-map body shared by stable and raw Sigma
constructors. It retains m and maps θ by the existing whole opposite fibre
precomposition functor. One consumed-point unifier compares the two
associative pre/postcomposition presentations. Its side conditions retain
identity, image endpoints and the actual middle composite; it does not
infer an arbitrary factorization.

The first rule failed subject reduction at that interchange. An initial
literal-endpoint comparison passed the rule but failed after the concrete
Sigma projection's image endpoint reduced. The complete-arrow test then
exposed a raw-composition presentation of the middle arrow. The final
comparison abstracts those reducible slots and checks their exact values
as side conditions. Typed controls reject changed r, changed m and an
arbitrary g without the required factorization. No endpoint/object cast is
added. These stages remain in `/tmp/emdash-native-sigma-precomp.wdnpzaph`,
including `rejected_structural_without_interchange.lp`,
`rejected_interchange_literal_endpoints.lp`,
`rejected_interchange_literal_middle.lp` and their corresponding logs.

Source-2-cell computation needed ordinary owners placed later in the full
source. The copied candidate moves the existing full Hom-action rules for
ordinary identity/composition into section 3e. It moves the existing Sigma
transfor component to its Sigma owner, expressing late Fibre/tdapp views
through earlier ordinary tapp owners. Two component projections, for
opposite families and represented Hom action, return the existing whole
ordinary transformations. Their base/Cat slots are measured SR guards;
all-inferred variants failed. The represented component uses the actual
precomposition telescope action, whose result is its whole transfor.
This tranche adds no primitive: it has four new runtime clauses, one
unifier, one defined helper and three relocated rules.

The [arrow reviewer](../emdash2/audits/native_sigma_precomp_controls.lp)
checks complete beta for both Sigma presentations, with the same m and
θ⋆r. The [2-cell reviewer](../emdash2/audits/native_sigma_source_two_cell_controls.lp)
checks the complete component of S(s)⇒S(r) as (id_d,a⋆α), through generic
horizontal composition, and rejects its reversed direction. Its
[observation](../emdash2/audits/native_index_source_two_cell_observation.lp)
now normalizes to that pair; the former opaque Sigma/component heads are
gone from this selected computation.

The [guarded gate](../emdash2/scripts/check_native_sigma_precomp.sh) passes
at `/tmp/emdash-native-sigma-precomp.3oqxJs`. Its manifest records exact
source identities and explicitly false full-kernel/generic-profile flags.
The prefix ends before homd_int and its extracted-action owners. Baseline,
candidate, both reviewers and strict LHS audits pass. Candidate/reviewers
have identical complete warning inventories: 1,023 critical pairs / 137
pattern reports. The +9 prefix delta is classified in the design document;
interactions with the later generic Sigma action remain to qualify on the
full candidate. No repository-wide typecheck was used for this tranche.

**Disposition:** selected source-arrow and source-2-cell computations
qualified before homd_int, with both Sigma presentations and negative
controls. Next audit the actual Catd/Functord/Pi and native-Homd classifier
profiles, then the general D-map/module and evaluation interfaces. Do not
promote this strict-reference prototype by assuming every family map
strict. Further higher-action and affected full-source interactions remain
explicit obligations, under the user's localized-validation policy.

### NUH-1B2e: Whole source-family internalization

The preceding `6ed30b7d` turn is progress: it constructed the native index
carrier/arrow/projection before homd_int and qualified the negative source
direction. The worktree is clean at resumption and its baseline ancestry is
preserved. Continue with the strict reference whole source family, retaining
the separate generic-profile obligation.

Hypothesis: one further shifted dual, D≥₃, permits the existing homwise
duality R to be internalized with its correct universe source. The native
index then varies over D₁₂(Z); its functor-category target and fibre
transpose vary over D₂(Z). Add the prototype operators at their actual
owning positions in a copied candidate, and check the source prefix plus
whole/point and dimension-2/3 controls before any promotion. A checked
strict-reference expression does not authorize arbitrary lax-profile action.

Sigma_func and the object action of Sigma maps are already available before
homd_int. Their capped arrow computation is later, at the native displayed
action owners. Test the whole x-family and selected source-arrow point
action first, then identify the exact remaining arrow/higher-action head.
Do not postulate a generic inverse laxity cell to fill that computation.

The [shift patch](../emdash2/audits/native_index_family_shift.patch) now adds
the three experimental owners CoAbove3_cat, CoAbove3_func and
native_homwise_dual at their intended positions in the copied preferred
candidate, with 14 projection/duality rules. CoOnly2_cat, Reverse12_cat and
CoOnly2_func are derived views. This is a strict-reference prototype;
unrestricted lax/Gray semantics of these operators are not qualified.

The [whole-family reviewer](../emdash2/audits/native_index_family_prototype.lp)
constructs J, S, P_D and the fibre-transpose family at the actual shifted
bases. Whole source action along r:x→x′ computes on points to
((y,v),a)↦((y,v),a∘r). The target computes H↦H∘S(r), and a source
2-cell has the correct reversed transformation type. Dimension-2/3,
identity/composition, involution and whole/capped projection controls check;
the wrong R(Z) target base and total-O fibre view reject.

The first P_D body used Functor_cat_func's fixed-codomain presentation;
its source-action point comparison did not compute. Replacing that body by
the existing hom_con(Cat,Cat,id) owner gives the same object family and the
computing whole precomposition action, without another rule or unifier.
The initial raw identity/composition conversion queries compared distinct
unreduced lambda result classifiers; explicit typed 1-arrow views pass.
Those failed variants/logs remain in
`/tmp/emdash-native-index-family.gvye214p` as
`family_rejected_constructor_action.lp` / `logs/family-source-point.log`
and `family_rejected_raw_dual_id.lp` / `logs/family-qualified-warnings.log`.

The [arrow observation](../emdash2/audits/native_index_source_arrow_observation.lp)
types, but normalization stops at fapp1_fapp0 of
sigma_map_func(Op_funcd(hom_int_precomp_func(…))). This is the exact
remaining source-arrow computation boundary, not a failed direction or
object cast. The next required construction is its structural represented
precomposition action, with retained triangle and base-2-cell observations,
before claiming a computing whole index action.

The [guarded gate](../emdash2/scripts/check_native_index_family.sh) passes at
`/tmp/emdash-native-index-family.Q2l6wf`. It checks the preferred baseline,
owning-position shifted prefix, both reviewers and strict LHS audits. The
candidate/reviewer warning inventories agree exactly at 1,014 critical pairs
/ 137 pattern reports. Relative to the baseline, 79 reported pairs are new;
each contains CoAbove3 or native_homwise_dual. Their family classification
and unresolved scope are recorded in the design document. The gate guards
the complete family-count delta and explicitly records that source action
on index arrows does not yet compute. Exact source identities and all
incomplete qualification flags are in its manifest.

**Disposition:** whole x-family formation and source-point/target
precomposition computations checked in the strict reference prototype.
This is not full native Homd, generic lax-profile, or full-kernel
qualification. The shifted source rules are not promoted to the active
nucleus. Next derive the structural Sigma source-arrow and 2-cell action
without calling the dependent-Hom action being defined; retain the separate
general D-map/module and profile obligations.

### NUH-1B2d: Native shared-index carrier and source duality

The continuation from `7565d935` is progress: the preceding tranche refuted
the y-local target with independent finite models and selected a shared
index to investigate. The worktree is clean at resumption, the comparison
baseline remains an ancestor and the active nucleus blob is unchanged.

Current source inventory distinguishes the Sigma carrier/first projection
from its later displayed-map action. Sigma Hom uses homd_, which is already
defined through ordinary hom_con and fibre evaluation before homd_int.
The whole first projection also precedes homd_int. By contrast, homdc_int
explicitly calls homd_int, and the later total-map action extracts its
displayed laxity. Do not classify every use of the Sigma carrier as the
same circular dependency.

Tested hypothesis: for C=ΣD and π:C→Z, the shared index has the
native expression R(Σ_(R C)(Hₓᴼ)), where Hₓ=HomZ(x,π(−)). Its target
projection is π∘R(π_inner). Probe its actual object/arrow formation and
whole projection on the preferred source prefix BEFORE homd_int, preserving
D over Z. This is an ingredient test, not a repaired full nucleus; no
arbitrary lax-map action of R is assumed.

The finite model had ordinary fibres and therefore did not distinguish O
from T in the negative u-slot. With a genuine fibre 2-cell, the representable
HomC(−,z) requires T(C), not O(C). The strict higher-reference dimension
bookkeeping consequently needs the source shift for dimension-1
transposition (dimension 2 only). Audit that shift and the whole index's
external x variance before extrapolating the earlier finite R(Z) signature.

The [native prototype](../emdash2/audits/native_homd_index_prototype.lp)
checks this carrier and its nested point/arrow constructors, whole target
projection, original point/arrow projection comparisons, retained triangle
and the projection's next Hom action. It rejects a reversed triangle.
No new category primitive, runtime rule or unifier is introduced. The
initial raw arrow introduction and triangle observation failed during
elaboration of compound opposite Homs. Explicit typed opposite-arrow views
with bodies equal to the original supplied arrow resolve those boundaries;
they add no endpoint equality. Rejected variants and logs remain in
`/tmp/emdash-native-homd-index.kxse0r0n` as
`native_index_rejected_arrow_raw.lp` / `logs/prototype-first.log` and
`native_index_rejected_triangle_raw.lp` / `logs/prototype-triangle.log`.

The same prototype checks the original represented source 2-cell direction
over T(C) and rejects total O(C) and the reversed 2-cell. The independent
finite audit now includes the walking-fibre-2-cell obstruction. The
[refined design](TYPESCRIPT_EMDASH_NATIVE_HOMD_INDEX_TARGET_DESIGN.md#native-carrier-and-higher-source-shifts)
records the strict reference calculation:
J:O(Z)→Cat, S:D₁₂(Z)→Cat, P_D:D₂(Z)→Cat, with negative source T_*(E).
The additional shift D≥₃ is needed when internalizing R itself. These are
semantic mask calculations, not newly installed operators or automatic
generic lax-profile qualifications. The earlier finite R(Z) shorthand did
not distinguish D₂ from R; it is not the proposed full higher signature.

Final gate: the [guarded driver](../emdash2/scripts/check_native_homd_index.sh)
passes at `/tmp/emdash-native-homd-index.XrDjky`. Its source-prefix SHA-256
is the unchanged `c120edf0…`; the complete identities are in the manifest.
The driver verifies that homd_int and its extracted-action owners are absent
from this prefix and that the reviewer does not call the later Sigma map
action. Prefix and reviewer have identical complete warning inventories:
935 critical pairs / 137 pattern reports. Strict LHS audits pass for both.
The copied full kernel remains explicitly untested by this ingredient gate.

**Disposition:** native shared-index carrier/projection ingredient checked.
The next step is whole varying-x internalization at the correct shifted
bases and actual transformation profiles, then the D-map/module action and
complete native Homd target. The carrier's independent construction removes
one circularity concern; it does not automatically qualify those later
actions or the whole repaired nucleus. Active kernel and TypeScript sources
are unchanged.

### NUH-1B2c: Shared target index and genuine base 2-cells

The continuation from `4c6d19af` is progress: the preceding tranche preserved
a qualified full-source polarity isolation. At resumption the dedicated
worktree was clean, its baseline ancestor and active source blob unchanged;
all 62 worktrees were inspected, with no unrelated changes made.

The [shared-index target design](TYPESCRIPT_EMDASH_NATIVE_HOMD_INDEX_TARGET_DESIGN.md)
now strengthens the base-2-cell obstruction. On a strict walking α:p⇒q,
the old local target requires comparison between H(D(p)*,p) and
H(D(q)*,q). The two coordinates have opposite variance. Two finite strict
coefficient models realize diagonal values (1,0) and (0,1), where 0 is Empty
and 1 is Terminal. Either orientation of a putative whole base action would
therefore require a functor 1→0. The examples come from the original native
endpoint formula with actual E/D and strict F; they are not excluded by
restricting to native Hom values. This is a semantic counterexample,
independent of the inherited LP inconsistencies and of normalization.

Consequently, stop trying to repair this y-local family by changing only its
base annotation, its fibre-op spelling or its section polarity. The negative
section experiments remain legitimate scoped constraints/computations, but
do not by themselves supply the general target architecture.

The proposed supporting index Sₓ(D) retains objects (y,v,a:x→y), arrows
(s,β:D(s)v→w,θ:b⇒s∘a), and their actual triangular compatibility at
2-cells. It keeps D over Z. The native source-fixed Hom formula is a whole
functor on this shared index in the strict 2-dimensional reference profile.
Source change is S(r):Sₓ′→Sₓ; a source 2-cell r⇒r′ gives S(r′)⇒S(r).
Thus the candidate P_D(x)=Fun(Sₓ(D),Cat) has the expected reversal of the
source 2-cell without regrading the original D. The finite R(Z) shorthand
is refined to D₂(Z) by the higher-slot audit in NUH-1B2d.

The independent [finite model audit](../emdash2/audits/homd_target_mixed_variance_model.py)
passes both countermodels and all index axioms, strict source functors and
their comparison, native Hom observations and source/fibre action checks.
The x-index has 5 objects, 14 arrows and one nonidentity noninvertible
2-cell. Some source-2-cell observations are actual Empty→Terminal functors,
so the model does not identify them with invertible cells. This is finite
strict 2-dimensional evidence; it is not a Lambdapi or ω-level qualification.

The design records the general family-map direction and the remaining
mixed-profile tdapp1_int/fdapp1_int obligation. It also explicitly forbids
defining the target via a Sigma/comma operation that already depends on the
same native Hom action. Next qualify the supporting native context/index
and its full higher action, including laxity profiles and this noncircular
dependency, before proposing another full LP candidate. No new primitive,
active rule, registry or TypeScript behavior is installed by this tranche.

### NUH-1B2a: Derived negative-section operator

Hypothesis: in the preferred total-duality basis, the native negative-section
category can be defined as NΠ_K(E)=O(Π_R(K)(Eᴼ)). Its whole constructor is
obtained by dualizing the existing Pi/Op-family composite with the correctly
shifted domain. For constant E it should recover the ordinary functor
direction T(K)→C. This supplies an internal candidate ingredient for the
target-polarity repair; it does not complete the general Homd target.

Test it on the preserved preferred source prefix, which contains Pi and the
correctly based dual-family operators. Retain the prefix limitation and
ordinary installed checker, stage copies only, and use the current resource
guard. Qualify whole construction, constant-family introduction/elimination,
nonidentity arrow action and wrong-direction controls without adding a new
rewrite or unifier. Full source migration and rejection of the Homd Empty
diagnostic remain separate requirements.

The first prefix prototype checks the category expression and constant-family
whole readback, including a nonidentity arrow and a further Hom action.
However, its tentative unrestricted constructor on Catd(K) is not selected:
for a lax displayed F:E→D, the available comparison is
D(p)∘Fₓ⇒Fᵧ∘E(p). Mapping a negative section needs the opposite direction.
Typechecking the old shifted-duality prototype does not justify that inverse.

Refine the map interface to accept an actual whole map G:Eᴼ→Dᴼ over R(K).
Its section action comes from Π(G), followed by total duality. The whole
map operator has source O(Functord(Eᴼ,Dᴼ)) and target
Functor(NΠ(E),NΠ(D)); this uses existing whole actions and requires no
manufactured inverse to F's laxity. Check point action against the existing
section_postcomp_sec(G,s) and reject an ordinary F:E→D as the wrong input.
The initial unrestricted source is retained as an unselected experiment,
not promoted as a general negative-section functor.

The refined [prototype](../emdash2/audits/native_negative_pi_prototype.lp)
checks in the preferred prefix. NΠ is a defined category expression. Its
whole map functor accepts O(Functord(Eᴼ,Dᴼ)); the point action agrees by a
typed reflexivity path with the existing Π section_postcomp_sec(G,s).
An ordinary lax F:E→D is rejected as that input. Constant-family
introduction/readback returns the original functor, its nonidentity arrow
action checks and a further whole Hom action remains available. No rule,
unifier, new primitive section operation or inverse-laxity witness is added.

The [guarded driver](../emdash2/scripts/check_native_negative_pi.sh) stages
both the exact current and historical patched prefixes and checks their
byte identity before the prototype. It retains the untested complete
candidate separately and explicitly records `fullKernelChecked: false`.
The gate at `/tmp/emdash-native-negative-pi.kVNMc2` passes baseline and
prototype with ordinary subject reduction; complete warning inventories
agree at 935 critical pairs / 137 pattern reports. The prototype's strict
LHS audit reports no rule clauses. Source- and patch-anchor checks prevent
silent replay on drifted owners. The initial unrestricted variant remains
in `tmp/probes/nuh_negative_pi_unrestricted_v1.lp` and the earlier temporary
stage, not as the selected interface.

This qualifies a native direction-correct ingredient on the retained
preferred prefix, not the complete Homd target or a repair of the active
nucleus. The next design must supply the appropriate negative-family maps
from the actual target construction; it cannot pass arbitrary old lax maps
through a covariant NΠ wrapper. The original target, all Empty controls and
the 328 current post-prefix source additions remain to be migrated.

### NUH-1B2b: Full-file polarity isolation

Hypothesis: replacing the old positive target section by the negative
section expression, and updating its actual native projection types, can
remove the polarity route while preserving the foundational homd/action
ladder. First test this in a copied full source with the old variance
conventions deliberately retained. This isolates section polarity from
the separately required total-duality migration; it is not a candidate
replacement for that migration and cannot establish a repaired kernel.

Use only derived negative-section expressions and the existing Π/Op/action
owners. Keep homd_int and its named whole/endpoint projections. Correct the
section-arrow projection by the negative-section interpretation rather than
an equality cast. Check the full source at its owning positions, then the
new Empty diagnostic and native forward/component consumers. A source/SR
failure identifies a coupled owner to examine; no failed check is hidden
behind opacity, an unreviewed unifier or a larger deadline.

The first copied full source checks after seven named polarity/projection
changes. The old Empty diagnostic rejects the positive-section type.
Native component/endpoint projections and their next action check, and a
transparent generic opposite-arrow view exposes the intended forward Hom
functor. At that stage a direct proof that its point action is F(p)∘h did
not check: normalization stopped at fdapp1_int_cell applied to homd_src_sec.

The next tested hypothesis supplies that constructor's semantic action in
the terminal-D/constant-E case as whole constant transformations built from
the existing represented Hom postcomposition. This is a beta observation
of the Homd constructor, not a rule for preservation of identity or
composition. Its first subject-reduction check failed at three comparisons:
the constant-family and constant-functor presentations, rigid Hom action on
a constant functor, and constant-presheaf reindexing. That failed version is
retained as `polarity_rejected_beta_v1.lp` with `logs/source-beta.log` in
`/tmp/emdash-homd-polarity-full._k66kvz6`; the earlier seven-change source is
`polarity_before_beta.lp`. Neither failure nor initial source success was
treated as the final consumer result.

Three narrowly typed proof-time comparisons now expose those same strict
constant constructions. They preserve K/A and the image of the supplied
object; no runtime constant-family fold is installed. The final source adds
one constructor beta whose result remains a whole transformation, alongside
the two transparent negative-section/evaluation expressions. Original
homd_int and its named projection/action owners remain in place.

The [preserved patch](../emdash2/audits/homd_target_negative_polarity.patch)
is applied only in an isolated full copy by the
[guarded driver](../emdash2/scripts/check_homd_target_negative_polarity.sh).
The [native reviewer](../emdash2/audits/homd_target_negative_polarity_controls.lp)
checks whole equality with the existing represented Hom action, the actual
formula h ↦ F(p)∘h for arbitrary p, retention of p at an identity source
arrow, and the next whole Hom action in h. Original component/endpoint
observations also check for arbitrary supplied D/E, as do their further Hom
types. These generic component checks do not establish the missing general
base action. Wrong forward endpoints and the old positive section type are
rejected. The unchanged Empty reproducer fails at precisely the recorded
positive-family versus opposite-family goal.

The [constant comparison reviewer](../emdash2/audits/homd_target_constant_comparison_controls.lp)
uses typed reflexivity for all three proof-time comparisons and rejects
changed category/object parameters. Separate conversion negatives confirm
that their runtime heads remain distinct. The inferred unused reindexing
map slot is `_`; its identity is irrelevant to a constant-family value.

Final gate: `/tmp/emdash-homd-negative-polarity.QV3mOi`, with exact source
and reviewer SHA-256 identities in `manifest.json`. The guarded baseline,
full candidate, both reviewers, intended Empty rejection and strict LHS
audits all pass. Both cores report 1,144 critical pairs / 157 pattern reports;
categories, heads, rule families and locations agree after mapping unchanged
source lines. Each reviewer has the exact candidate warning inventory.
The new beta introduces no reported critical pair. This is scoped check
evidence, not a confluence or consistency theorem.

The patch is serialized with zero context, avoiding trailing spaces from
blank context lines. A fresh replay from the recorded source anchor and
`git apply --check --unidiff-zero` both succeed; the replayed full source is
byte-identical to the checked candidate, SHA-256
`8512aaf1c86afdba01e0a34d8bab03ca2c0a64d52b83a2dfd1b7db27c447e26e`.

**Disposition:** NUH-1B2b is complete as an unpromoted polarity isolation.
The old op/Sigma defects remain explicitly present. No active LP source,
positive diagnostic registry, catalog or health snapshot was changed; the
private patch/reviewers do not establish library compatibility. For example,
the active diagnostic still contains positive-Π target observations, which
must migrate with the final design. The preferred shifted-duality full
target, arbitrary-family base action, noninvertible base-2-cell behavior and
the coupled soundness controls remain NUH-1B2/NUH-2 obligations. Do not extend
the inherited old-op target into a second proposed final architecture.

### NUH-1B1: Terminal-family section polarity probe

Hypothesis under test: the old positive section over the opposite y-base
has the wrong direction even before the full higher-base mismatch is
considered. For a covariant F:Z→C, terminal D, constant E=C, and fixed x,u,
the endpoint observation is p↦HomC(u,F(y)). Section action along p:x→y
would send its y-value (restricted along p) to its x-value. Evaluating at
idₓ would therefore appear to give HomC(u,F(y))→HomC(u,F(x)), which is not
available for arbitrary F and p.

Test this in a non-library file using only existing definitions and actions.
No primitive witness, rewrite or unifier is to be added. If the term checks,
retain it as a diagnostic of the current coupled package, not as a valid
feature; independence from the already known defects requires separate
controls. If it fails, inspect the exact action/endpoint that rejects it
before selecting a replacement target. The intended native homd constructor
remains foundational throughout.

Result: the [tracked diagnostic](TYPESCRIPT_EMDASH_HOMD_TARGET_POLARITY_DIAGNOSTIC.md)
accepts the complete reverse functor and a closed Empty witness. Its
walking-arrow specialization also accepts. The separate forward-action
companion checks typed reconstruction/identity paths, retains the next Hom
action and rejects the reverse function type. Warning-enabled runs have
identical complete 1,144/157 inventories and all three audit files contain
zero new rule clauses. Exact source/log/status details are in the diagnostic.

This changes the next action: correcting only the R(Z) versus Z type
mismatch is insufficient. The target's section polarity must also be
corrected. The result belongs to the existing coupled package; independence
from the earlier op/Sigma faults is not established. Retain the three
earlier negative controls and add this route to full-repair qualification.

### NUH-1B2: Direction-correct native target

The required y-action in the strict working transport case is

```text
Mᵧ(q,v) → M_z(p∘q, D(p)(v)),
Mᵧ(q,v)=HomEᵧ(E(q)(u),Fᵧ(v)).
```

The old positive section over the opposite y-base supplies the converse.
First qualify a native negative/mixed-section target in the terminal and
constant case, with preserved whole projection/action. Then combine it with
varying D/E and noninvertible base-2-cell controls. A lax-comma interpretation
is a candidate semantic comparison for the target, not a new definition of
homd_int. Its complete higher variance remains to be established.

A limited primary-source review of comma polarity and dependent two-sided
fibrations is recorded in the diagnostic. It does not start a general
external calculus or a spectral research task. The new target's type,
projections and computation must be specified together before promotion.

| Subrow | State |
| --- | --- |
| NUH-1A source/dependency inventory and baseline | established; launch checkpoint records the exact anchors and controls |
| NUH-1B1 terminal-family polarity control | complete diagnostic tranche; reverse Hom and Empty reproduced, lawful forward companion checked |
| NUH-1B2 complete native Homd target variance/polarity design | active; resolve the corrected section direction and all bases/profiles together |
| NUH-1B2a negative-section ingredient | refined object/whole-map and constant-family prototype checked on preferred prefix; unrestricted lax covariance rejected |
| NUH-1B2b full-source polarity isolation | complete as an unpromoted experiment; terminal/constant whole and point beta, further Hom and rejection controls pass under explicitly retained old variance |
| NUH-1B2c shared-index target design | old y-local architecture refuted by strict finite coefficient models; candidate shared index/source variance checked at dimension 2, full native higher target pending |
| NUH-1B2d native shared-index ingredient | carrier/arrow/whole projection and source-Hom direction check before homd_int; whole x-family and D-map/profile qualification pending |
| NUH-1B2e whole x-family | strict-reference S/P_D and fibre transpose typecheck; source points and H-precomposition compute; source action on index arrows and generic profiles remain unqualified |
| NUH-1B2f structural source action | stable/raw arrow beta and source-2-cell components compute before homd_int; classifier/profile and native-Homd integration remain pending |
| NUH-1B2g family/section profile diagnostic | complete diagnostic tranche; three Empty routes and discriminating subtraction variants preserved, no profile repair promoted |
| NUH-1B2h connected naturality profiles | deferred by subsequent user direction; not a prerequisite for this goal |
| NUH-1C whole-universality/realization separation design | initial dependency inventory established; exact native interface remains to qualify |
| NUH-1D native duality owners | finite signatures/prototypes specified; no generic external D_S API; complete the actual internal target/module |
| NUH-1D2 auxiliary family-map action | parked; whole/point and target action checked in copies, raw opaque-arrow reintroduction unqualified; no active source change |
| NUH-1D3 direct homd_int owner adjustment | current next task; justify the required target change against existing declarations and preserve the native projection ladder |
| NUH-2A repaired full-owner candidate | not started; requires NUH-1B |

Continue with NUH-1D3's direct homd_int declaration/target/projection
review. Keep the shared index as a candidate and the D-map expansion
parked. Complete the required native adjustment and integration, keeping
whole higher action and actual mathematical context explicit. Use localized
checks of affected owners/features/files and reuse unchanged evidence. Empty audits and the
prototype strictness migration are deferred, as is integration of the other
profile branch until after this goal. The full native target implementation
remains unfinished. Spectral/stabilization work stays out of scope.
