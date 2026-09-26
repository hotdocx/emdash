# Action-Profile Integration: Displayed Assembly Investigation

Date: 2026-09-26

Status: retained-member point and matching-action prerequisites pass; a whole
FibCov member-projection comparison is qualified in a further candidate;
complete displayed/rho profiles and inverse assembly remain open

Owner: [living plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), row `API-05`.
Production mathematics remains at checkpoint `f0f327d6`. This investigation
began in `emdash2/tmp/probes/api_ordinary_profile_minimal/`; the later
member-projection continuation below uses a separate corrected core. Neither
restores the commented displayed half of the pointwise-equivalence owner.

## Decision And Actual Consumer

The user selected an explicit action-based premise for displayed assembly.
The old unqualified primitive is not an accepted integration result.
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
