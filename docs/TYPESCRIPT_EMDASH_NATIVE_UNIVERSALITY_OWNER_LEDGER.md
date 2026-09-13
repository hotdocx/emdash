# Native Universality: Owner, Variance And Dependency Ledger

Date: 2026-09-12

Status: NUH-3 checkpointed at 1ea98f63; NUH-4A1 independent homology records checked; packaged input migration next; NUH-1/2 duality work user-deferred

Parent: [living implementation plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

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
