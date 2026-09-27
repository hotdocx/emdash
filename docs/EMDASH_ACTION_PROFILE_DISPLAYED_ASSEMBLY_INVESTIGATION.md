# Action-Profile Integration: Displayed Assembly Investigation

Date: 2026-09-26

Status: preserved research; explicit-profile sufficiency and rho-producer
redesign deferred under `API-05R`; successful derived results retain their scope

Owner: [living plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), row `API-05R`.
The user-confirmed [inherited assembly baseline](EMDASH_ACTION_PROFILE_ASSEMBLY_BASELINE_REVIEW.md)
supersedes this report's earlier integration prerequisites. "Next" and
"required" steps below describe the preserved research route; they are not
gates for the first integration baseline. No findings or receipts are erased.
Production mathematics remains at checkpoint `f0f327d6`. This investigation
began in `emdash2/tmp/probes/api_ordinary_profile_minimal/`; the later
member continuations below use separate corrected cores. None restores the
commented displayed half of the pointwise-equivalence owner.

## Decision And Actual Consumer

The user initially selected an explicit action-based premise for displayed
assembly. That choice has since been superseded for this integration milestone
by the inherited-contract baseline linked above.
The actual consumer, `emdash3_2_direct_cover_completion_locality.lp`, has
three assembly stages: an ordinary fibre transformation, a displayed
transformation between matching maps, and an ordinary outer transformation
between matching endofunctors. Each needs its actual profile. `Psh_cat` is
Cat-valued; none of these profiles follows from a blanket ordinary-category
assumption.

An earlier proof dependency also needed migration. The retained-member theorem
is an opaque constant in the active source, with a historical derivation
using strict naturality of a represented section. Its archival derivation is
recorded in the
[computational-schemes plan](../emdash2/reports/REPORT_EMDASH_V3_2_COMPUTATIONAL_SCHEMES_CONTINUATION_PLAN_2026-08-03.md)
and the `psss12zzx/zza` probes in the presheaves/sites worktree. That
derivation cannot be carried forward as evidence that the missing profile
has already been proved in the lax candidate.

`api_profiled_represented_section_path` derives
`E[p](H[x](id_x)) = H[y](p)` from the existing whole
`IsStrictFunctord(H)` premise. It evaluates the existing strict-cell evidence;
it adds no axiom, rule or admission. Its reviewer has two positive and two
negative checks, including rejection of raw judgmental reflection even when
the profile is present.

The same step now checks at the actual section returned by
`direct_cover_completion_glue`. A first application through covariant
`hom_` over `Op K` fails because main retains contravariant `hom_con` and
its precomposition action separately. The corrected
`api_profiled_contravariant_section_path` derives the path directly at that
existing owner. `api_direct_cover_glue_section_value_path` then checks at the
literal glue output with an explicit profile of that output section.
No whole-representation fold or operational cast is added.

Three actual-consumer negative controls pass: omitting that section profile,
substituting the existing question-substitution profile of the whole glue
constructor, and treating the resulting path as runtime conversion. The
source's `direct_cover_completion_glue_is_strict` concerns a different
displayed map. These controls qualify the conditional historical route.
The alternative below now removes this extra premise from the retained-member
proof. Producing strictness for arbitrary glue-output sections is therefore
no longer a prerequisite for that statement. Complete locality/rho action
and inverse assembly remain unqualified.

## Decision Review: Three Distinct Boundaries

The user first requested a review of the earlier choice on 2026-09-27 UTC.
That first review did not reverse the requirement; the subsequent accepted
baseline reassessment linked above does supersede it for this milestone.
The choice concerned the unqualified displayed assembly assumption, not a
blanket prohibition on computations for a particular strict constructor.

At source tip `114dc19f`, `StrictTransfdPointwiseOmegaAlong` quantifies
pointwise `OmegaEquivAlong` evidence for the fibre transformations. Despite
its name, its definition contains no strictness or other action-profile
field. The two `strict_transfd_pointwise_*_inverse` constructors accept an
arbitrary displayed transformation with that evidence, and the two whole
cancellation laws are declared constants. Their component beta rules select
the supplied inverse arrows. This is a generic primitive assembly interface;
it is not itself a rewrite equating arbitrary `F[g] o F[f]` with `F[g o f]`,
nor is it a strictness rule confined to one particular functor.

Separately, the [vertical-fold audit](EMDASH_ACTION_PROFILE_VERTICAL_FOLD_AUDIT.md)
found genuinely generic leakage in rules retained from the source branch.
Staging a generic transfor-composition proof and specializing both transfors
to `id_F` yielded a composition-preservation equality for arbitrary raw `F`.
The [postcomposition audit](EMDASH_ACTION_PROFILE_INVERSE_ACTION_FEASIBILITY.md#further-staged-strictness-route-api-04p)
found another such route. Those corrections belong to the requested lax
boundary regardless of which displayed-assembly option is selected. They
must not be described as rejecting only a legitimate fixed-constructor
strictness instance.

Justified constructor-specific computation and supplied structural contracts
remain possible under the owner/subject-reduction/overlap SOP. There is no
new requirement to mechanically wrap every structural constructor. For
example, the source's named `direct_cover_completion_glue_is_strict` contract
is retained in the candidate. It constrains the whole glue constructor's
question-substitution action; it does not automatically give the different
rho/locality action profile. A constructor name parameterized by arbitrary
functors must still be checked for indirect generic consequences.

| Earlier option | What it commits to | Consequence for integration |
| --- | --- | --- |
| Explicit action profile | Select a sufficient condition on the existing action, preserve the selected inverse data, and qualify the actual consumer against that condition. | Makes the coherence obligation explicit, but its sufficient formulation and concrete producer still require work. The first full-strict fibre candidate was stronger than intended for identities of lax endpoints; the relative alternative remains under review. |
| Preserve the existing assumption | Retain the generic whole inverse constructors, component beta rules and cancellation axioms, documenting their assumed status. | Could avoid much of the present profile/producer investigation. It carries an unqualified assembly principle whose adequacy for the retained lax semantics has not been established here. It does not require restoring unrelated global strictness leaks. |

Most recent member/cone/FibCov work supports the first option's actual rho
producer. Requiring an explicit profile was not merely a wrapper insertion:
the investigation also seeks to justify the producer rather than add an
unproved admission. Keeping the old primitive could have substantially
shortened this portion of the work, but no alternate complete integration
run establishes that the goal would already be finished. Remaining directed
consumers, promotion of prototype corrections, affected native/CAS/path
requalification, TypeScript conformance and final integration gates are
independent outstanding work. This records the first review's conclusion;
the later baseline decision changes the sequencing without claiming that the
unfinished profile research has been proved.

## Derived Retained-Member Route

The new proof keeps a whole section through the silent-law calculation.
For a retained member `(p,member)` over `V`, let `e` be its existing
`fib_cov_transf` section into the sieve extension and retain `m o e` as the
section into the completion. The proof does not replace this composite with
the represented section of `m[V](p,member)`, which was the historical
matching-naturality detour.

The derivation is:

1. Apply the qualified whole glue-substitution path at the original `m`.
2. Use the existing whole extension factorization to express the pulled
   matching map as `(m o e) o inclusion`; associativity supplies the path.
3. Apply the whole silent law to obtain `m o e` itself.
4. Evaluate that equality of whole sections at the identity of `V`.
   Yoneda precomposition computes directly, and public presheaf composition
   crosses its existing named representation path.
5. Compare with the original restriction-after-glue component using the
   existing identity-family precomposition comparison.

This proves the exact original
`restriction(glue(m))[V](p,member) = m[V](p,member)` statement. No additional
section or matching-map strictness premise, axiom, rewrite or unifier is
introduced. The fifteen support definitions retain the existing supplied
boundaries: the HIT glue profile and silent path, the whole extension-action
comparison and retained factorization, and the presheaf composition
representation path. They do not upgrade those supplied boundaries to
independently derived theorems.

One initially attempted projection change inferred the source annotation of
displayed composition from its constructor. It allowed the endpoint proof
to check but did not qualify the identity-order comparison control. It is
unselected and unnecessary: the final proof compares both public composition
presentations through the **same existing stable precomposition head** before
evaluating. This preserves the original maps and the distinct runtime family
representations. The preferred candidate core is byte-identical to the
preceding native/CAS/cubical qualification.

`api_direct_cover_retained_owner_position.lp` is a complete locality-source
copy with the old opaque retained-member constant replaced by this derived
definition. All eight public signatures through the pointwise-evidence
boundary are unchanged, apart from trailing whitespace. The original rho
projection tower, member equivalence and fibre pointwise evidence check
against that body. The three whole-assembly stages remain commented with
their profile restoration condition. The existing rho heads remain structural
declarations; this result does not establish their strictness or whole inverse
coherence.

The public theorem and two nonreflection controls pass. A joint review with
the complete profile reviewer and original glue reviewer passes 79 positive
and 18 negative assertions. The old opaque-assumption control is excluded
from that review. Its warning inventory and the derived owner have identical
1,058 critical-pair warnings and 150 pattern-variable diagnostics, with no
changes to heads, families, normalized owner locations or complete participant
templates. The strict LHS audit has zero unreviewed candidates.

## Whole Displayed Action Projection

`api_displayed_action_projection.lp` generalizes eight existing `fdapp1`
projection owners to distinct displayed endpoints `FF` and `GG`. The
projection rungs are definitions using the existing internal `tdapp1`
action. Two whole observation heads are structural declarations, following
the existing `fdapp1_comma_projection_func/transf` boundary. They are not
claimed to be derived from earlier component beta rules.

The resulting `api_transfd_transport_transf(eta,p)` has whole type

```text
D[p] o FF[x] => GG[y] o E[p].
```

Its component is the existing `tdapp1_int_cell`. Four candidate rules give
the whole functor's object projection, its component projection, and two
diagonal folds to the existing `fdapp1` owners. The diagonal keeps arbitrary
internal action, rather than recognizing only identity transformations.
Five initial controls and four additional diagonal-order controls pass,
including both complete application orders, typed reflexivity, the component
observation and the retained next-Hom functor.

A no-diagonal control retains three positive checks and rejects both new
diagonal computations. The no-rule and two-beta-rule variants have identical
warning inventories: 1,038 critical-pair warnings and 150 pattern-variable
diagnostics. The diagonal rules add one warning, at the overlap between
`fapp0` and `api_tdapp1_comma_projection_func`. It is emitted before the
adjacent transformation fold is read; the complete-order controls join after
that fold. Categories, heads, families, normalized locations and complete
participant templates were compared. This is a specific overlap analysis,
not a global confluence claim. Strict LHS audits find zero unreviewed
compound inferred slots in the projection and guarded assembly candidates.

## Unselected Profile And Assembly Boundary

The proposed `api_DisplayedTransforActionProfile(eta)` is defined from:

- `IsStrictTransfor` for each whole fibre transformation `eta[x]`;
- at every base arrow `p`, equalities of the whole projected action with
  both compositions through `FF` and `GG` laxity and the corresponding
  whiskered fibre component of `eta`.

These are conditions on existing action. The definition introduces no
generic profile admission. The base-action condition holds for the displayed
identity on arbitrary `FF`, while four raw equality/reflexivity controls
are rejected. This does not establish the full fibre profile for that
identity. Sufficiency of these conditions for inverse assembly, including
the remaining higher base action, still needs mathematical review against
the complete internal action and the actual producer.

The subsequent [relative-profile review](EMDASH_ACTION_PROFILE_RELATIVE_PROFILE_FEASIBILITY.md)
checks an important identity boundary: this fibre strictness factor, at the
displayed identity, implies strictness of every fibre functor. A separate
relative predicate over the complete ordinary internal actions admits raw
identities and path-induced comparisons without that endpoint premise. Its
actual matching producer and selected inverse profiles pass, but sufficiency
for generic/displayed inverse assembly remains unselected. The original
stronger profiles are unchanged.

The separate `api_profiled_transfd_pointwise_assembly.lp` restricts the
old primitive assembly interface by adding this explicit profile. Its two
inverse constructors and whole cancellation constants remain structural
declarations. Their existence and cancellation have **not** been derived
from the candidate conditions. Five positive and two negative controls
verify whole formation, preservation of both selected inverse projections,
and rejection of an omitted or differently indexed profile. Those checks
qualify interface bookkeeping, not the mathematical sufficiency of the
primitive. The profile and guarded assembly have identical warning inventories
(1,039 critical-pair warnings, 150 pattern-variable diagnostics), including
locations and complete participant templates.

Neither this assembler nor the raw unqualified control is in the selected
native/CAS/cubical interaction closure. The displayed half of the preferred
pointwise-equivalence owner remains commented with its restoration condition.

## Exact Evidence And Recovery

All checks below use source-only inputs, subject reduction, serial execution,
`OCAMLRUNPARAM=o=20,v=1024`, the default 2 GiB/90s profile and the existing
file/core/no-swap guards. The listed controls have warnings enabled.

| Check | Successful receipt | Seconds |
| --- | --- | ---: |
| Guarded represented-section controls | `20260926T174734Z-c20fb42989df45d58036165e85cf639c` | 7.534 |
| Whole/component/identity/next-Hom projection | `20260926T175340Z-471ea40410bd42728525ad276986f462` | 7.642 |
| No-diagonal control | `20260926T180558Z-0c1f977bac524c12be5ad32668e4fc1a` | 9.422 |
| No-rule formation baseline | `20260926T180815Z-be0e6fa64c3d4738a2629fa9e3c202a4` | 7.562 |
| Complete diagonal application orders | `20260926T180842Z-390355e37d4c4b1fa2e1be040cd59132` | 7.774 |
| Candidate profile controls | `20260926T180938Z-0f805f275e064582b1ab79f8857db2de` | 7.754 |
| Guarded primitive assembly controls | `20260926T180613Z-ce0b70232a214b9d92e70fcc2dde294f` | 7.525 |
| Actual glue-section premise controls | `20260926T181312Z-19437780a82545b49295cdd4bcd7d0eb` | 12.327 |

The unchanged production locality baseline passes in 0.749s
(`20260926T173038Z-a7f493cef6af4c879f1b174408fa08f2`). The failed
covariant-presentation attempt is retained separately, receipt
`20260926T181057Z-8a78a8744fdb4b8387a01ae51d7c814c`, and excluded from
successful candidate evidence. It is a source-presentation failure, not a
resource failure or a counterexample to the desired locality theorem.

`emdash2/tmp/probes/api_displayed_profile_current_investigation_manifest.json`
binds all eight successful receipts to 32 exact-current input files. Its
SHA-256 is `307516f1f161adabc59191f45875761f84f12289706323d851d4fdef0679aadd`.
The warning-comparison manifest is
`emdash2/tmp/probes/api_displayed_profile_warning_comparison.json`, SHA-256
`a3d40dccb216da59ea28728766f8c3ffcb4e9149335eed61fc46aafd22e28d17`.
The core remains
`ab48a85136935c5183b87bc0341fbb524a58be61083f1bbd9ad2563475df9965`.
There are no compiled objects in this package.

The subsequent retained-member qualification uses the same default guards
and warning settings:

| Check | Successful receipt | Seconds |
| --- | --- | ---: |
| Direct Yoneda precomposition evaluation | `20260926T182350Z-d763e2ad13144b7b8d515c82c06a7aa4` | 6.155 |
| Complete derived retained-member proof, unchanged core | `20260926T184306Z-0f3a712d5dee410390eb7f124acfd1f0` | 13.954 |
| Original owner and nonreflection controls | `20260926T184616Z-c34ca93a05ec46e884e0793d4b8d0e3b` | 14.363 |
| Full profile/glue interaction review | `20260926T184849Z-9e451b11eca8490ea8f992d1ab7d5403` | 17.486 |

The joint review's maximum child RSS is 837,724 KiB.
`emdash2/tmp/probes/api_cover_retained_current_qualification_manifest.json`
binds these four receipts to 47 exact-current inputs, the eight-signature
audit, supplied boundaries and rejected/unselected controls. Its SHA-256 is
`159dab73c637b4848d8b006199e9c7e5474bbd2fe85f28f2a7579e2b536cba58`.
The warning comparison is
`emdash2/tmp/probes/api_cover_retained_owner_warning_comparison.json`, SHA-256
`e28e8837efa46eaa9df1bea4cf8b63a5930affb014ca8a518595d41da1966837`.
Neither the old locality module containing the opaque theorem nor a modified
core is in this successful closure. The earlier conditional-section and
unselected displayed-profile investigations remain separate evidence.

Use the immutable receipt input blobs for exact recovery. The manifest also
records the authoring scripts, whose successive archive/control steps are
not an idempotent build. These are investigation artifacts, not a second
accepted library or a clean-checkout integration route.

## Next Required Work

The [whole matching-action continuation](EMDASH_ACTION_PROFILE_MATCHING_ACTION_FEASIBILITY.md)
now lifts the retained-section argument in that parameter, using an isolated
guarded whole precomposition comparison. Its 269-positive/77-negative joint
review has a different core pin; the unchanged-core evidence above retains
its original scope. Next account for the retained-member and base directions
and connect the complete construction to the actual rho owners. The component
theorem alone does not assemble directed higher coherence. Keep the actual
whole functors and both inverse choices; introduce no blanket rho admission.

Review the displayed candidate against the complete internal action before
selecting its primitive inverse interface. Check its sufficiency and whether
the actual producer can satisfy it with its retained lax endpoints. Then
qualify fibre, displayed and outer rho assembly in order. These
remain required `API-05` work. Other directed/simplex consumers, TypeScript,
production cut retirement and final integration gates remain required by
the parent plan; Op/duality repair and new Empty audits remain excluded.


## Whole FibCov Member Projection

The next member-direction prerequisite concerns the existing canonical
fibre-Yoneda construction. For a family `E` over `K`, form the whole functor

```text
P(E,x,y) = component_at(y) o fib_cov_src_func(E,x)
        : E[x] -> Functor_cat(Hom_cat K x y, E[y]).
```

Its point computation is already `P(E,x,y)[u][p] = E[p][u]`.
The exchanged family action `sym_func(fapp1_func(E,x,y))` has the same point
computation. Both point proofs check on the preceding telescope-corrected
core, while a typed-reflexivity comparison of the whole functors is rejected,
receipt `20260926T225335Z-1f9c461baf1b49aaa0643f4737d5edf0`.
Point equality alone is therefore not the supplied whole-action interface.

A separate full-file candidate adds one guarded proof-time comparison of
those whole functors, after the exchange owner is declared. It recognizes
`tapp0_func` composed with the actual `fib_cov_src_func`, retains the actual
family hom action on the other side, and checks the represented source,
`Hom_cat K x y`, and both endpoint fibres in side conditions. Runtime keeps
the two presentations distinct.

This is a **new whole constructor-projection agreement in the candidate**.
It specifies the canonical higher member action intended by the FibCov
projection cascade; it is not a rule-free theorem obtained by extensionality
from the point proofs. It introduces no profile admission for an arbitrary
family, section, matching map or rho transfor. Production adoption remains
part of the complete owner migration and its gates.

### Derived Member Transport And Actual Readouts

Using the existing exchange projection, the canonical readout at `p` is a
whole functor `E[x] -> E[y]`. Congruence of the new whole comparison and the
existing double-exchange computation give a path from that readout to the
original `E[p]`. At `p = id_x`, this is a path to `id_(E[x])`. A `PathOver`
observation retains its complete next Hom action and original endpoints.

The actual sieve-extension instance keeps the native `Op_cat K` source.
For `h : W -> V`, its readout is compared with the original whole transport
from the extension fibre at `V` to its fibre at `W`. No Sigma-Hom arrow
formula, alternative transport, or new opposite rule is introduced.

For a raw matching map `m`, a component-first readout postcomposes its
original fibre functor `m[V]` with the canonical identity member readout.
It is equal to `m[V]` as a whole functor, with a next-Hom observation. Its
object action at the original `(p,member)` computes to `m[V](p,member)`.
No section or matching-map strictness is a premise.

This is the specified canonical readout order. It does not assert an
unproved whole comparison with every raw evaluation/postcomposition
presentation. A later consumer that uses a different whole presentation
must compare it explicitly. Nor does this result give the missing whole
retained-factorization path as the member varies, or the base-direction
coherence needed for rho.

Controls reject runtime identification of the two whole member projections,
substitution of an unrelated action functor, the wrong base-arrow result,
raw functor composition (including the Cat-valued specialization), and raw
matching-map component naturality. The constructor comparison is not used
to make these ambient laws hold.

### Member-Projection Qualification

Four support modules contain thirteen definitions, with no new primitive,
rewrite or unification declaration in those modules. Their whole comparison
uses the single new core unifier described above. The actual readout and
next-Hom consumers pass in the combined review.

| Current check | Receipt | Seconds / maximum child RSS KiB |
| --- | --- | ---: |
| Whole constructor agreement and runtime distinction | `20260926T225600Z-df177946b2ce4ac2b20a2195637d9bb0` | 9.994 / 453,880 |
| Whole member transport, identity and next Hom | `20260926T225912Z-275cc25eead94ea59a8517100e3a47bb` | 7.858 / 454,000 |
| Combined actual member/matching/inverse/Gray/Gamma/H/Hom review | `20260926T230654Z-67acccdaeefa4ecb8ae869cf1c2e3e77` | 48.298 / 2,508,832 |

The final review passes **476 positive/131 negative assertions** over 233
inputs. Definition bodies check in addition to assertions. Focused checks
use 2 GiB/90s; the broad review uses the established 3 GiB/180s profile.
All use warnings, subject reduction, serial execution,
`OCAMLRUNPARAM=o=20,v=1024` and the existing file/core/no-swap guards. The
package is source-only with no compiled parents.

Focused warning counts remain 947 critical pairs/150 pattern diagnostics;
the broad scope remains 1,127/162. Heads, families, full participant templates
and source locations mapped across the insertion all have zero deltas.
Warning parsing reports no issues. The strict LHS audit has zero unreviewed
candidates, retaining 64 annotated slots across 41 clauses. This evidence
qualifies the scoped comparison, not global confluence or consistency.

The package is `emdash2/tmp/probes/api_fibcov_member_candidate/`.
Core SHA-256:
`5325e159fbb90db0564366acb0fcfe6b4cdd3ce75e346c7f7336cfb256b720e0`.
The profile owner remains
`f670814a83a508bd8a77a4000c7ab04690bbfc25978d106bb1d761ce6723a69c`.
The earlier telescope package is unchanged.

The manifest
`emdash2/tmp/probes/api_fibcov_member_current_qualification_manifest.json`
binds three current successful receipts, the 233-input union, thirteen
support definitions, the earlier no-whole-agreement control, source pins and
warning/authoring records. SHA-256:
`d3732ef476469fbb39d1cbd6095515e4ec91f2e1821bc25fc879259cdf4bf250`.
Exact emitted source is preserved in the immutable receipt input store;
authoring scripts still record an experiment sequence rather than a finished
production integration recipe.

Next lift the retained-factorization and glue/silent argument through the
varying member and base directions, preserving the whole matching parameter.
That complete construction must supply the actual rho action before the
explicit assembly profile can be selected and the three assembly stages
restored. The current result is a member-projection prerequisite, not a
rho admission or completed locality migration.

## Member-Indexed Question And Extension Families

The next candidate constructs a whole functor from the actual sieve-extension
member category at `V` to the total question category. It first applies the
original inclusion's fibre functor, then the question classifier's existing
whole action. This gives a functor to
`Path_cat(DirectCoverQuestionData K T V)`, with the original pulled question
as its object value. No set-truncation assumption on question data is used.

Two existing total-category presentations give the required object pair
`(V, pulled_question)`. The selected presentation uses
`sigma_pullback_total_func` along the constant functor from the terminal
category to `Op K`, after pairing the parameter with the terminal object.
Its existing whole base-projection comparison proves that the resulting
functor has constant base `V`. A path-core inclusion also recovers the same
objects, but a control rejects typed reflexivity between these two whole
presentations. Their object agreement is not treated as a whole equality.
The deferred arrow action of `sigma_intro_tapp0_func` is not supplied here.

Reindexing the existing extension and representable functors gives whole
contravariant families over the member category. The base comparison,
existing object-level Op/composition computation and Yoneda give a whole
path from the representable family to the constant family at `y(V)`.
The original inclusion transformation is reindexed through its existing
precomposition owner, preserving the given data.

### Retained Inclusion And The Normal Identity Join

The actual inclusion component exposes a projection-order gap. In an
opposite source, `id_(Op A)(x)` becomes `id_A(x)` before `tapp1` sees the
generic identity pattern. A generic theorem staged before specialization
already proves the normal-unit equality, while direct conversion remains
unavailable on the preceding core. The no-join control passes at
`20260927T000532Z-d41c22d1b1b3490c862057b37f97498b`.

The new full-file candidate adds one rule immediately after the generic
`tapp1` identity clause, recognizing the actual `Op A` source and its
projected `id_A(x)`. This joins that retained normal identity; it supplies
no composition or naturality profile and changes no Op variance or higher
action. Its explicit source discriminator has a local LHS audit annotation.

Retargeting the inclusion with `path_to_hom` of the representable-family
path forms a term, but fails the literal component-retention assertion
even after that identity join
(`20260927T000806Z-e6f47f8ebae2494abda117d9e617e574`). It remains an
unselected alternative. The selected construction instead composes staged
identity comparisons between the existing associativity and object-level
Op/composition presentations. These helpers are definitions using existing
computation, with no new rule or primitive action on arbitrary transfors.

The resulting `api_member_inclusion_fixed_target` has the original
pulled-sieve inclusion as its literal component. Its whole `tapp1_func`
and arbitrary-arrow `tapp1_fapp0` agree with the original reindexed
inclusion. The target comparison's components are identities. Thus the
new presentation retains the original inclusion's higher action; it does
not replace the inclusion or infer a strictness profile for it. Wrong-arrow
and unrelated-presentation controls remain negative.

### Family And Identity Qualification

Eight support modules contain 24 definitions, including the unselected
path-retargeted construction and the staged generic unit theorem. None of
those modules adds a primitive, rewrite or unifier. The only new core rule
relative to the preceding member candidate is the normal identity join.

| Current check | Receipt | Seconds / maximum child RSS KiB |
| --- | --- | ---: |
| Selected inclusion components, with question observations | `20260927T001131Z-cff053f0d6374b24915119e377574013` | 8.926 / 507,340 |
| Focused families, components and higher action | `20260927T002108Z-eb102917282141d98a9eb31c2a98c9cd` | 9.344 / 511,128 |
| Combined member/matching/inverse/Gray/Gamma/H/Hom review | `20260927T002324Z-12af2f7eab0a49b6ad5f7de79d3ee347` | 49.362 / 2,518,632 |
| Identity-join overlap controls | `20260927T002955Z-ddeb96b3b68c49e6a22ee25282a38b2d` | 12.054 / 457,384 |
| Separate next-construction base/unit observation | `20260927T003057Z-1fc1d3b878ab4aa5837d8b2f799926c2` | 10.102 / 457,052 |

The focused review has 17 positive/3 negative assertions. The combined
review has **493 positive/134 negative assertions over 245 inputs**; the
overlap control has 13 positive/8 negative assertions, including the five
positive/one negative unit controls it imports. The separate next-construction
observation checks formation and runtime nonconversion only. These counts
are overlapping closures and must not be added together.

Focused checks use 2 GiB/90s. The combined review retains the measured
3 GiB/180s profile of its preceding broad closure. All use warnings,
subject reduction, serial execution, `OCAMLRUNPARAM=o=20,v=1024` and the
existing file/core/no-swap guards. All packages are source-only.

The focused warning comparison changes 962/150 to 971/150; the broad
comparison changes 1,127/162 to 1,136/162. Both add exactly the same nine
complete critical-pair participant instances, with no removals or pattern
delta. Source locations mapped across the insertion agree as well: six
new warnings at the identity join and three at the existing profile
accumulators. Warning parsing reports no issues.

The added overlaps cover one represented-source action, three identity
presentations (Path, Terminal and Product), two opposite-source
presentations (Terminal and Product), and three profile accumulators
(lax precomposition, strict precomposition and strict postcomposition).
The focused overlap reviewer checks the existing normality/profile paths
and both rigid results of the represented-source branch. Several runtime
branches remain distinct, with explicit negative controls. This is scoped
overlap classification, not a confluence certificate. The strict LHS audit
has zero unreviewed candidates and 65 annotated slots across 42 clauses.

The current package is `emdash2/tmp/probes/api_member_identity_candidate/`.
Core SHA-256:
`b9cc2726d8614762f85d33a8f64adaaa78668518aa4ada4866abf82e861d7c10`.
The profile owner remains
`f670814a83a508bd8a77a4000c7ab04690bbfc25978d106bb1d761ce6723a69c`.
The current manifest is
`emdash2/tmp/probes/api_member_identity_current_qualification_manifest.json`,
SHA-256:
`3197623ca8d5f768f26327beb77660f7b2d0cdaa798850ef69b65a0de6809cb3`.
It binds the five successful receipts, 247 distinct current inputs, support
definitions, warning/audit records and the earlier failed approaches.
Exact emitted sources remain in the immutable receipt input store; the
authoring helpers are not a finished clean-checkout integration recipe.

### Remaining Pullback And Assembly Boundary

The whole question and extension families are prerequisites for a varying
pullback construction. The complete canonical pullback-arrow cone, its
comparison with the original `sigma_transport_arrow`, and the retained
factorization across members and base arrows remain open. The existing
supplied factorization path at each particular member is not, by itself,
a whole comparison in that variable.

The next-construction diagnostic forms the FibCov base-action cell at
`(p, id_x)` and finds it runtime-distinct from identity. This does not show
that an equality path is absent and does not authorize a new generic
unit-coherence axiom. Qualify the actual cone and its comparison using the
existing action owners before applying the glue/silent argument to it.
Then derive the actual rho profiles and select a sufficient explicit
assembly premise. All three assembly stages remain unrestored. Production
source is unchanged, and earlier native/CAS/all-path receipts retain their
earlier core pins until their affected closures are requalified.

## Whole FibCov Lift And Member Cone

The next experiment constructs the relevant whole section before trying to
identify its components with canonical transport. For a family `E` over `K`
and `u : E[x]`, define

```text
L(E,x,u) = sigma_map_func(fib_cov_transf(E,x,u))
        : PathOut_K(x) -> Sigma_K(E).

cone(E,x,u) : Pi_z Hom_(Sigma E)((x,u), L(E,x,u)[z]).
```

The cone is the existing `pathout_refl_arrow_sec(x)` mapped through
`fapp1_at_transf(L(E,x,u), pathout_refl_obj(x))`. Thus it is one whole
section produced by existing owners, with no new coherence declaration.
The lift's object action at `(y,p)` is `(y,E[p](u))`. The cone's generic component is
`sigma_map_transport_arrow(fib_cov_transf(E,x,u),p,id_x)`.

The original sieve inclusion's fibre functor, followed by a constant-base
totalization of the represented fibre, gives the whole map from actual
members at `V` into `PathOut_(Op K)(U)`. Reindexing the generic lift and cone
along that map yields `api_member_pulled_question_lift_func` and
`api_member_pulled_question_cone`. The object value is the original pulled
question. A staged generic proof supplies a path from the actual cone
component to the mapped PathOut transport arrow. The direct runtime
comparison at the concrete opposite-source presentation remains negative;
the path is the qualified interface.

### Whole Base Projection And Exact Comparison Gap

The whole target of the cone has constant base `V`. This is proved using
the existing whole projection laws for `sigma_map_func` and
`sigma_pullback_total_func`, associativity and congruence. An actual-member
`PathOver` observation retains the whole next Hom action of that base
comparison. A wrong-base comparison is rejected. No unrestricted Sigma-Hom
or Homd higher-action formula is used to justify a new computation.

The cone component has a specific remaining fibre cell:

```text
fdapp1_int_cell(fib_cov_transf(E,x,u), p, id_x)
  : E[p](u) -> E[p](u).
```

`api_sigma_fibcov_transport_unit_path` derives equality with the original
`sigma_transport_arrow(E,p,u)` **given a path identifying this cell with
identity**. Its body applies congruence to the existing Sigma-arrow
constructor. The premise is not supplied. Runtime conversion and direct
typed reflexivity for that cell are both rejected by controls; neither
negative proves that another equality path cannot be derived.

The actual cone also has a different whole question-target presentation
from the preceding constant-basechange construction. Their literal object
values agree, but typed reflexivity between the whole functors is rejected.
The new cone is therefore a coherent candidate section with checked
observations, not an established comparison with the original canonical
pullback cone. Its existence does not justify transferring the original
extension-pullback or retained-factorization contracts to it silently.

A separate control tests a possible semantic reconstruction of FibCov via
the ordinary internal action and displayed evaluation. The families
`Functor_catd(Const(A),E)` and `hom_(Cat,E,A)` have the same fibre categories.
The current environment rejects typed-reflexivity comparisons both of their
whole families and of their base-arrow action functors. In the latter case
the residual owners are `Hom_func` and `hom_postcomp_func`. This records a
prerequisite for that reconstruction, not an impossibility result or a new
family agreement. The reconstruction has not been installed.

### Cone Qualification And Resources

Seven new construction/proof modules contain nineteen definitions. They
add no primitive, rewrite, unifier, strictness assumption or rho admission.
The generic cone, its component path, the generic reindexing theorem and
the conditional canonical-arrow comparison check before specializing to
the actual question classifier. Early implicit-Sigma endpoint inference
failures are retained separately from the later runtime and resource results.

| Current check | Receipt | Seconds / maximum child RSS KiB |
| --- | --- | ---: |
| Actual member cone and mapped-arrow component path | `20260927T005539Z-eea9a3beed524efd96cdc4d5bb99fc9e` | 38.413 / 2,438,288 |
| Whole constant-base path and actual next Hom | `20260927T005835Z-ad8a39ae33004d40a6e591e03d634198` | 38.481 / 2,439,644 |
| Member/inclusion/cone interaction and evaluation-family controls | `20260927T005948Z-d8edb51646c64a249f851b0a53fd8dd6` | 43.737 / 2,441,696 |

The final focused interaction review passes **22 positive/12 negative
assertions over 36 inputs**. Definition bodies check in addition to these
assertions. This includes the preceding member-family/inclusion controls;
the three listed closures overlap and their counts must not be added.

The last staged actual-member proof exhausted 2 GiB in 28.930s, receipt
`20260927T005430Z-cb496b2775ce402e86852717d14bfd5f`. The first current
success above uses **identical source inputs** at 3 GiB/90s. All three
current checks use that measured profile, `OCAMLRUNPARAM=o=20,v=1024`,
warnings, subject reduction, serial execution and the existing file/core/
no-swap guards. The 2 GiB/90s defaults remain unchanged. The earlier expanded
and partly staged attempts also exhausted 2 GiB; they are historical
failures, not alternative successful recipes.

The previous focused review and the new joint review both have 971
critical-pair warnings and 150 pattern diagnostics. Heads, rule families,
complete participant instances and source locations all have zero deltas;
warning parsing reports no issues. The core and profile hashes remain
`b9cc2726d8614762f85d33a8f64adaaa78668518aa4ada4866abf82e861d7c10`
and `f670814a83a508bd8a77a4000c7ab04690bbfc25978d106bb1d761ce6723a69c`.
All 247 inputs of the preceding qualification manifest were rehashed and
remain unchanged. Its broader 493-positive/134-negative review retains
that exact scope; it does not include the new cone modules.

The package remains `emdash2/tmp/probes/api_member_identity_candidate/`,
with no compiled parents. The new manifest is
`emdash2/tmp/probes/api_member_cone_current_qualification_manifest.json`,
SHA-256:
`855b16003a22533d1832963facfef9f34b7a0f51fb649d0ea7bc4711a7bea388`.
It binds the current 36-input union, nineteen definitions, warning comparison,
source-preserving resource retry, failed approaches and immutable input blobs.
No production LP or TypeScript source changed.

Next qualify the complete FibCov base action and its normal-unit comparison
from its generic semantic owner. Any evaluation-based implementation first
needs the actual whole and base-action family comparisons identified above.
Then compare the candidate cone with the original canonical arrow family,
preserving the original inclusion and both inverse choices. Only after
those comparisons can this route discharge the retained-factorization,
glue/silent and rho-profile obligations. The three assembly stages and the
remaining parent-plan integration gates remain open.
