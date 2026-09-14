# Native Homology Model And Reifier: Living Implementation Plan

Date: 2026-09-14

Status: NUH-5B2c2 column/input/H comparisons qualified; TypeScript observation migration and retained nonsplit adoption remain required

Parent: [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

Ledger: [native owner and dependency ledger](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md)

## Scope And Existing Boundary

The native ordinary construction now supplies whole H, its induced maps,
the whole connecting transformation δ and all three native-window exactness
comparisons. Preserve these owners and their original K/Q, H, diagrams,
normality and inverse selections.

The retained TypeScript workflow already prepares equation, provider,
homology, raw-witness and model-observation inventories. Its nonsplit
consumer previously manually created rational coefficient names, a reifier,
formal ring/generator/model/normality references, their declarations and
the immutable environment. NUH-5A now automates this mechanical work.

The existing `FreydHomologyModel` is a supplied coherent legacy presentation:
it stores Z, W/V and whole presentations over those choices. Its H ultimately
uses the native whole owner. Its current connecting observation still uses
`homology_record_connecting` through the older model component interface.
Automating that context does not qualify a new whole-δ model consumer.

Keep these distinctions explicit:

| Boundary | Current evidence | Required treatment |
| --- | --- | --- |
| Matrix operations and retained selections | Existing native polynomial algorithms and checked selected results | Reuse the original result; do not recompute or reselect during preparation |
| Coefficient interpretation | Supplied formal ring/generator/coefficient references under an explicit realization | Generate deterministic names and all declarations before freezing the environment |
| Universal providers and coherent model | Supplied/trusted semantic contracts, not derived from finite matrix equations | Retain their classification and provenance |
| Model normality | Supplied model enhancement | Do not manufacture a correctness theorem by declaring its type |
| Whole δ and categorical exactness observations | Generic native theorem is qualified; retained concrete observation migration remains | Connect the model consumer to those actual native owners before NUH-5 completion |

## NUH-5A: Supported Retained-Model Preparation

Start with rational polynomial rings, the supported coefficient backend of
the retained nonsplit example. An immutable backend registration must record
its identity/revision and the explicitly supplied model/normality semantic
contracts. Registration and preparation do not adopt computation claims.

Given one already selected whole result, prepare a context that:

1. creates collision-free, deterministic formal ring and generator names;
2. collects canonical rational coefficient references while preparing all
   existing inventories;
3. seals that collection before constructing the immutable environment;
4. creates named model/normality inputs with their correct dependent types,
   explicitly classified as supplied assumptions;
5. returns the original bundle, existing issued preparations, references,
   environment and initial assumption source for the existing workflow; and
6. rejects unsupported coefficients, unissued registrations, missing
   prepared coefficients and invalid name scopes without partial adoption.

The helper is implemented in
[algebra_formal_freyd_rational_model_context.ts](../src/v3_2/algebra_formal_freyd_rational_model_context.ts).
`defineAlgebraFormalFreydRationalBackend` issues an immutable registration
with explicit coefficient, model and normality contracts.
`prepareAlgebraFormalFreydRationalModelContext` takes that registration,
the retained selected result and a name prefix. It returns the original
bundle, the three existing issued preparations, the sealed coefficient
inventory, model/normality references, environment and initial source.

Model and normality inputs are explicitly classified as supplied inputs;
`constructsModel`, `adoptsClaims` and `nativeWholeConnectingObservation`
remain false in this preparation profile. There is no public-barrel,
checker, Core-owner or mathematical-signature change. The retained nonsplit
consumer now calls this helper instead of constructing its inputs by hand.

Four focused tests cover no homology/universal/connecting reselection,
typed references and distinct namespaces, agreement with the independent
manual preparation interfaces, deterministic names/inventories, rejection
of forged registrations and unsupported coefficients, sealing against
unprepared coefficients, and an actual nonsplit replay without adoption.
They pass together. Full later assumption adoption remains an inherited
runtime boundary described below; native whole-δ observation migration is
still NUH-5B work.

## NUH-5B: Native Model Observation Migration

NUH-5B1 qualification (2026-09-14):
[FreydAdjunctionModel](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_models.lp)
transparently packages the original initial-zero capability and independent
whole P/Q. H delegates directly to the existing whole owner; its model core
does not import the ordinary homology-record adapter. The separate
[normality enhancement](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_model_normality.lp)
is the existing `OneCatAdjunctionNormality` at these same projections. H
does not require normality. The existing combined Abelian classifier remains
available; no additional combined-package wrapper is needed here.

The [legacy adapter](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_model_adapter.lp)
retains the old model's P/Q and identical whole H functor. Its original
native inputs, H points and whole Hom action are preserved by conversion.
No object cast or reselection is introduced. Native whole normality remains
an explicit contract over these same P/Q; it is not inferred from the old
pointwise lift/colift capabilities.

The [whole connecting specialization](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_model_connecting.lp)
and [three exactness specializations](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_model_exactness.lp)
are transparent partial applications of the existing owners. They inherit
the original dependent row-family telescope, original H endpoints, maps,
comparisons and inverse selections. Twelve definitions add no primitive,
runtime rewrite, unifier or earlier LP edit. The focused reviewers exercise
retained P/Q/H, independent native input, whole δ/Hom action and the three
actual fixed-comparison exactness witnesses.

Next, NUH-5B2 must assemble the concrete original raw rows and their maps
into this native window, then migrate the TypeScript observations to it.
The current supplied arbitrary row-family consumer is not yet that retained
nonsplit end-to-end consumer. Preserve every original selection and classify
the model/normality, row and complete-arrow interpretation contracts.

NUH-5B2a qualification (2026-09-14): the retained inverse-mate input and
direct raw input now have a derived categorical equivalence. Existing source
reconstruction and ordinary diagram reflection compare their whole
transformations J(A)⇒d. The [fibre inclusion](../emdash2/emdash3_2_one_cat_zero_cone_fibre_inclusion.lp)
uses existing Sigma/base-change/Op_func computation and retains both base
identities and the actual fibre cell. Its zero-cone interface is explicitly
restricted to ordinary C; no general higher-duality extension is asserted.

The [input comparison](../emdash2/emdash3_2_one_cat_chain_pair_input_comparisons.lp)
carries that derived fibre path through the whole inclusion functor. It uses
the existing `OmegaEquivAlong`, with the actual comparison fixed. The
[Freyd specialization](../emdash2/emdash3_2_commutative_algebra_freyd_native_input_comparisons.lp)
then applies the original whole H to the same comparison. Its inverse is
the image of the original selected input inverse. Neither H endpoint is
cast, replaced or reselected; there is no `Obj(C)` equality transport in this
construction. The original W/presentation occurs only in this legacy-input
adapter, not as a prerequisite of the independent native H construction.

The [raw-row family constructors](../emdash2/emdash3_2_commutative_algebra_freyd_native_row_families.lp)
embed a fixed raw row as a constant parameter family. Existing raw map
agreements feed the whole constant-transformation functor. Row points,
all three raw map components, off-diagonal action and higher action in the
agreement parameter are retained. These constructors need no K/Q, model,
normality or additional coherence-square input. Thirteen definitions add
no primitive, rewrite, unifier or earlier LP edit.

Next NUH-5B2b must assemble all four original rows and their maps, produce
the required whole chain-zero inputs from the existing raw agreements, and
connect the derived column inputs to the retained H observations. The
new equivalence covers the retained/direct input comparison at the same
outgoing diagram; a window's derived column input remains a further
comparison. Native row shortness stays an explicit model contract.
TypeScript observation migration and the complete retained nonsplit consumer
are still required. None of these obligations is discharged merely by the
row-family constructors or input equivalence.

NUH-5B2b experiment (2026-09-14): derive the whole zero-composite input
for constant raw row families through the existing weakening functor and
whole initial/terminal-family uniqueness. Compare the native whole row
projections with their constant raw morphisms, then apply these constructors
to all four original rows and three original row maps. The raw matrix
agreements must produce the two whole chain-zero inputs; no new caller
naturality or coherence-square proof is proposed. Native row shortness and
whole normality remain the explicitly supplied model contracts already
recorded above.

The first literal and typed-reflexivity probes do not compare the whole
constant-family observations, although their points already compute. A
first proof-time evaluation view fixes the immediate row projection but
still fails under the zero's nested initial/terminal compositions. The
accepted candidate instead adds the intended constant-diagram reduction
at the existing whole evaluation owner, together with its preprojected Hom
companion. Both normalization orders retain the original diagram and shape
point. This is a computation for literal constant diagrams, not arbitrary
pointwise extensionality.

One guarded proof-time comparison remains for the canonical Cat horizontal
action on a constant transformation. It retains both bases, the same
functor in both pairs, the original endpoints/arrow and an identity second
component. Its positive canonical-head query and changed-arrow/nonidentity-
second-component controls pass. Removing this view makes the positive query
fail. The raw row consumers supply its actual ordinary-target use. Generic
upstream facade queries stopped at their existing represented-parent typing
boundary; no additional facade theorem or arbitrary lax/profile claim is
promoted. The current constant-composition presentation must be requalified
when the deferred profile migration is integrated.

An ignored source overlay checks the full evaluation owner at its intended
position, while every other source remains a link to the current checkout.
The two runtime folds add no warning bodies or rule-family deltas relative
to the original owner. The four-row whole δ and all three raw exactness
specializations check in that overlay, as do the closest existing evaluation,
terminal-family, native connecting and model-window consumers.

NUH-5B2b qualification: [constant chain-zero laws](../emdash2/emdash3_2_one_cat_constant_chain_zeros.lp)
derive the whole zero from existing weakening and categorical initial/terminal
uniqueness. [Whole raw-row projections](../emdash2/emdash3_2_commutative_algebra_freyd_native_row_paths.lp)
retain all three original morphisms. The
[middle-column zero constructor](../emdash2/emdash3_2_commutative_algebra_freyd_native_row_zeros.lp)
then derives each actual native-window zero input from its original raw
middle-column agreement. It retains the literal additive projections used
by the generic window interface.

[Native raw-row shortness](../emdash2/emdash3_2_commutative_algebra_freyd_native_row_short_exact.lp)
is the existing whole P/Q predicate at that row; it remains supplied model
structure. The [four-row connecting constructor](../emdash2/emdash3_2_commutative_algebra_freyd_raw_window_connecting.lp)
uses the original raw rows and three raw maps, derives both whole zero
inputs, and applies the existing whole δ. The
[three exactness constructors](../emdash2/emdash3_2_commutative_algebra_freyd_raw_window_exactness.lp)
instantiate the same native fixed-comparison theorems at those identical
inputs. No output exactness, splitting, cover or new coherence proof is
supplied. Twelve definitions add no primitive. The only runtime changes
are the two constant-evaluation folds in the existing evaluation owner;
one guarded constant-transformation proof-time view is added separately.

Next NUH-5B2c must compare the derived column inputs with the original raw
homology inputs, then use the retained/direct input equivalences to preserve
the original selected H observations. This assembly currently retains the
native window's H endpoints; it is not yet the final retained-CAS observation
interface. TypeScript migration, the nonsplit end-to-end consumer and later
adoption remain required.

NUH-5B2c experiment (2026-09-14): separate two observations before changing
any interface. First compare a whole H-family point with original global H
applied to the observed native input. Then compare the actual derived
column diagram/transformation with the original raw input. These are
diagnostic conversion/reflexivity checks, not object-equality transport in
the theory. If an arbitrary diagram requires reconstruction, use the existing
categorical reconstruction comparison and retain its endpoints; do not add
a general diagram-object equality or reselect H.

NUH-5B2c1 qualification (2026-09-14): the
[point-input observer](../emdash2/emdash3_2_zero_arrow_family_point_inputs.lp)
retains `(A[x], D[x], h[x])` in the existing native zero-cone category.
It needs no P/Q, additive structure or ordinary-category profile. The
[H-point comparison](../emdash2/emdash3_2_homology_family_point_comparisons.lp)
then compares H(A,D,h)[x] with global H at that exact input, under the
global H owner's existing ordinary profile and the same whole P/Q.

The literal H-point conversion and typed-reflexivity diagnostics did not
join: the two actual boundary diagrams still occur beneath Q. Both are
canonical introductions of the same boundary, so the existing typed
point-introduction paths compare those diagrams. The construction maps
their categorical comparison through the original Q once. Existing
OmegaEquivAlong action retains its selected inverse and both actual H
objects. There is no intermediate quotient, H-object cast, new universal
choice or caller coherence proof. The diagram paths are derived canonical
introduction comparisons, not an equality of arbitrary diagrams or an
equality-based replacement for universality. Five definitions add no
primitive, runtime rule, unifier or change to an earlier LP owner.

This qualifies a point observation, including Q's full Hom action at those
endpoints; it does not assert a new whole natural comparison as x varies.
The outgoing right-column diagram also passes an existing typed
point-introduction comparison with the raw diagram in a diagnostic probe.
Its failed literal-conversion alternative does not require a new diagram
rule. Next NUH-5B2c2 derives the incoming-arrow observation and compares
the actual column input with the original raw input. Compose that comparison
with this H-point bridge and the retained/direct input equivalence before
migrating the retained TypeScript observations. NUH-5B2 is still open.

NUH-5B2c2 experiment (2026-09-14): observe the existing whole incoming
recovery law at x, then use ordinary diagram-map reflection and the native
fibre inclusion to compare with the original raw column input. The raw
column chain witness belongs to the retained comparison target; it is not
a new input to δ or an extra caller naturality square. Keep its original
identity and derive the incoming-arrow comparison from whole recovery and
the raw row-map projections. Reuse the already qualified outgoing-diagram
introduction view. Reject any route needing arbitrary diagram equality,
an H-object cast, or a new universal selection.

NUH-5B2c2 qualification (2026-09-14): both original whole column inputs
now have [raw-row specializations](../emdash2/emdash3_2_commutative_algebra_freyd_native_column_inputs.lp).
Their incoming point laws observe the existing whole source-recovery law;
the first attempt through the alternate postcomposition parent did not
join, while the original source-evaluation parent does. The
[ordinary input comparison](../emdash2/emdash3_2_one_cat_terminal_input_comparisons.lp)
retains both transformations at their actual outgoing diagram. Ordinary
diagram reflection derives their equality from the incoming observation
and terminal-tip uniqueness, then the existing whole fibre inclusion maps
the comparison and selected inverse. The
[introduced-point specialization](../emdash2/emdash3_2_one_cat_introduced_terminal_input_comparisons.lp)
uses the existing canonical diagram-introduction view; no new diagram
equality or normalization rule is added.

The [raw input comparisons](../emdash2/emdash3_2_commutative_algebra_freyd_native_column_input_comparisons.lp)
retain each original raw column chain witness as their target data. They
derive the incoming comparison internally. Original whole H then gives
[both H comparisons](../emdash2/emdash3_2_commutative_algebra_freyd_native_column_homology_comparisons.lp),
including fixed-map equivalence and the same selected inverse. The
[retained-model comparisons](../emdash2/emdash3_2_commutative_algebra_freyd_retained_column_homology_comparisons.lp)
compose with the inverse of the existing retained-to-native comparison.
Existing IsoEvidence symmetry and OmegaEquivAlong composition preserve
the older model's exact H objects; W/V remain in this optional adapter,
not in the native construction. Twenty-three definitions add no primitive,
runtime rule, unifier or edit to an earlier LP owner.

The connecting-endpoint reviewer uses the actual four-row whole δ. Both
column H maps have its original source/target points, and composing its
component with the selected source inverse and target comparison gives an
arrow between the original raw H objects. δ and its whole Hom action remain
the original owners. The comparison is qualified at points; no new whole
natural transformation into a constant raw-H presentation is asserted.

An exploratory reviewer imported all three exactness proof implementations
while checking these point comparisons. Several expanded equivalence and
inverse observations exceeded the unchanged memory guard. The same
interfaces pass with their actual column/H dependencies, and the separate
connecting-endpoint reviewer passes with the actual connecting owner. Keep
these observation dependencies focused; this is not a qualification of the
oversized all-exactness probe or permission to raise resource limits.

Next NUH-5B2d migrates the TypeScript observations to these native owners
and the actual whole δ. Preserve the original result, raw column chains,
row maps, H selections and sign. Register native whole normality and raw-row
shortness as explicit supplied contracts where still needed; do not infer
them from the old pointwise contracts or matrix equations. The retained
nonsplit replay/adoption and native exactness observations still require
qualification. NUH-5, NUH-6 snake comparison and NUH-7 remain open.

Audit the current model's P/Q projections and normality against the new
independent `KernelAdjunctionStructure`, `CokernelAdjunctionStructure` and
`OneCatAdjunctionNormality` owners. Prefer a native model surface indexed by
those whole structures, with legacy presentations as realization adapters.
Do not reinstate W/V as prerequisites of the primary formal H/δ construction.

Preserve the retained H selections and sign convention while exposing the
actual whole connecting transformation and the derived exactness maps to
the model observation workflow. Identify which agreements are derived,
which are supplied structural/model contracts, and which interpretations
remain explicitly trusted. An equation d∘G=0 is not evidence that G generates
the full kernel.

NUH-5 is not complete from preparation convenience alone. It requires the
retained nonsplit consumer at the qualified native observation boundary,
with every remaining contract accurately classified. The later NUH-6
snake/direct/native comparison and NUH-7 final qualification remain separate
requirements of the parent goal.

## Validation

NUH-5B2c2: seven new owners and three reviewers cover 23 definitions and
25 passing assertions. The reviewers check whole column inputs, both fixed-base
input projections, original input/H endpoints, both fixed-map equivalences,
the same selected inverses, the older retained H objects, and actual whole
δ/component/Hom-action endpoint compatibility. Checks remain localized
under the serial 90-second/2-GiB guard. No TypeScript implementation changed.

Final owner logs span `190816`–`190856`; the reviewer logs are
`freyd_native_column_comparisons-20260914-190908.log`,
`freyd_retained_column_comparisons-20260914-190918.log` and
`freyd_native_connecting_endpoints-20260914-190931.log`, under
`emdash2/logs/probes/`. Their import-only controls at `191133`, `191143`
and `191159` match complete inventories and raw warning blocks: 1,489/169
for native and retained column observations, and 1,490/169 for the actual
connecting consumer. The native/retained H owners match those same
controls. Exact evidence is `emdash2/tmp/probes/nuh5b2c2_warning_comparison.json`.

Affected strict LHS audits, catalog, source TOC and report-header checks
pass. Source-only health metrics cover 1,203 files. Earlier unchanged
whole exactness and TypeScript evidence is carried forward. The failed
all-exactness probes, smaller passing controls and generation scripts
remain under `emdash2/tmp/probes/nuh5b2c2_*`; active owners and this ledger
govern continuation. No repository-wide typecheck or aggregate was run.

NUH-5B2c1: two owners and two reviewers pass under the unchanged serial
90-second/2-GiB guard. Seven assertions cover all three stored point-input
projections without P/Q, the actual H-map endpoints, fixed-map equivalence,
the mapped selected inverse and Q's full Hom action. The existing H-family
consumer also passes with the new comparison module imported. No
repository-wide typecheck or aggregate was run.

Strict affected-owner LHS audits, the check catalog and source TOC pass.
Source-only health metrics cover 1,193 files; these metrics do not replace
the focused runtime checks above.

Owner logs are `emdash3_2_zero_arrow_family_point_inputs-20260914-182938.log`
and `emdash3_2_homology_family_point_comparisons-20260914-182941.log`;
reviewers are `zero_arrow_family_point_inputs-20260914-182945.log` and
`homology_family_point_comparisons-20260914-182948.log`, under
`emdash2/logs/probes/`. The import-only controls at `182953` and `182957`
match both complete inventories and raw warning blocks: respectively
1,157/159 and 1,255/169 critical-pair/pattern reports. Exact evidence is
`emdash2/tmp/probes/nuh5b2c1_warning_comparison.json`. The outgoing-diagram
diagnostic is `nuh5b2c_right_diagram_point_typed-20260914-180850.log`;
the H-point comparison failure is recorded at `181247`. Neither failed
literal comparison is promoted as a theory-level equality assumption.
The existing-consumer log is
`nuh5b2c1_h_family_regression-20260914-183050.log`.

NUH-5B2b: the changed evaluation owner, seven new owners and four reviewers
pass under the unchanged 90-second/2-GiB serial guard. Sixteen assertions
(13 positive, three rejection controls) cover whole/projected constant
evaluation and both reduction orders, the guarded Cat horizontal view,
whole zero derivation, actual raw-window H endpoints, full δ Hom action,
and all three original exactness witnesses. The five affected existing
evaluation, terminal-family, native-connecting and model-window consumers
also pass. No repository-wide typecheck or aggregate was run.

Final owning-file logs span `175420`–`175530`; new reviewer logs are
`diagram_constant_evaluation-20260914-175553.log`,
`one_cat_constant_transformation_views-20260914-175558.log`,
`one_cat_constant_chain_zeros-20260914-175623.log` and
`freyd_raw_native_window-20260914-175651.log` under `emdash2/logs/probes/`.
The existing-consumer checks span `175738`–`175832`. Complete owner/reviewer
inventories match: respectively 1,150/157, 1,150/157, 1,280/169 and 1,490/169
critical-pair/pattern reports. The original evaluation owner at `173719`
has the same warning bodies, heads and rule families; only source location
lines move at the two inserted rules. Exact evidence is
`emdash2/tmp/probes/nuh5b2b_final_warning_comparison.json`.

Strict affected-owner LHS audits, the check catalog and source TOC pass.
Source-only health metrics cover 1,189 files. The source overlay and failed
intermediate comparisons are retained under `emdash2/tmp/probes/` as
experimental evidence; active source and this plan govern continuation.

NUH-5B2a: five owners and three reviewers pass under the unchanged serial
90-second/2-GiB guard. Nineteen assertions cover point/fibre inclusion,
both base identities and the retained cell, fixed-input and H equivalences,
the mapped selected inverse, all three raw row-map components and whole
parameter Hom actions. No normality or extra coherence witness is needed
for these input comparisons. The earlier owner/window evidence is retained.

Final owner logs span `164422`–`164456`. Reviewer logs are
`one_cat_zero_cone_fibre_inclusion-20260914-164508.log`,
`freyd_native_input_comparisons-20260914-164514.log` and
`freyd_native_row_families-20260914-164527.log` under `emdash2/logs/probes/`.
Their import-only controls at `164535`, `164541` and `164553` have identical
complete inventories and raw warning blocks: respectively 1,157/159,
1,296/169 and 1,291/169 critical-pair/pattern reports. Exact comparison data
is in `emdash2/tmp/probes/nuh5b2_warning_comparison.json`. Catalog and source
TOC checks pass; source-only health metrics now cover 1,178 registered files.
All 13 production declarations are definitions; no primitive/rule/unifier
or earlier LP source was changed. No TypeScript implementation changed in
this tranche.

NUH-5B1: all five owners and both reviewers pass warning-enabled checks
under the existing serial 90-second/2-GiB guard. The 15 assertions include
14 positive observations and one changed-kernel rejection. Owning-file
logs span `161424`–`161500`; final reviewers, repeated after removing two
trailing blank lines, cover the exact final sources. Their logs are
`freyd_adjunction_models-20260914-162057.log` and
`freyd_adjunction_model_window-20260914-162110.log` under
`emdash2/logs/probes/`. Import-only controls at `161547` and `161557`
have identical complete warning inventories and raw warning blocks:
1,263 critical pairs / 169 pattern reports for the model adapter and
1,490 / 169 for the whole window. The comparison is recorded in
`emdash2/tmp/probes/nuh5b_warning_comparison.json`.

The first normality spelling used reduced Freyd projections. Its type
checked alone, but the later whole dependent comparison exhausted memory.
Keeping the original generic additive-projection expressions makes the
same specialization check without a new equality/comparison rule. The
redundant combined-package wrapper was not retained. The model core also
now imports the native whole H directly, without the unnecessary ordinary
record dependency; this makes the combined exactness check fit the guard.
No source or target is cast, no model is reselected, and no bound is raised.

The check catalog and source TOC pass; source-only health metrics include
the five new owners and two reviewers (1,170 registered files). The affected
metrics tool's 40 unit tests also pass. This is
localized qualification, not a new repository-wide typecheck claim.

Follow the root TypeScript handoff and nested Lambdapi SOP. The user's
localized-check policy overrides repository aggregates for this goal.
Use affected TypeScript modules and focused runtime tests; avoid loading or
typechecking the entire public barrel merely for convenience. Run any new
formal signature/term through bounded owner-position and consumer checks.

Compiler and mathematical probes remain serial under the existing resource
guard. The first existing-model runtime baseline hit `std::bad_alloc`;
explicit heap bounds, direct test imports and separately compiled execution
still did not complete the full later adoption case within 90 seconds.
The retained test and shared fixture now import their exact defining modules,
so focused checks avoid loading the whole workbench barrel.

An instrumented copy of the original compiled consumer locates preparation
at about one second, the whole replay at about two seconds, and the original
whole assumption adoption at about 21 seconds. The run then exceeds the
guard before selected-homology adoption finishes. This is not a new helper
regression or a completed full-adoption qualification. Preserve it as an
open runtime boundary for the required retained realization.

A local tsconfig emits only the affected test and its actual dependency
graph; the baseline contains 147 source files and two test files, without
an index barrel. Compilation and execution have separate bounded runs.
The four new preparation/replay tests finish in about 14 seconds together.
Their first combined run caught a test fixture retaining forbidden mock
implementations in a prepared engine; separating that throwaway preparation
from the subsequent replay fixture fixes it. No resource ceiling was raised.
Localized TypeScript compilation and ESLint pass. The generated model-input
probe also passes against the active Lambdapi model owners: six typed input
references for the ring, generator, two coefficients, model and normality.
This checks declaration conformance, not the supplied model's correctness.

Local evidence is retained under `emdash2/tmp/probes/`:
`nuh5_typecheck_qualified.txt`, `nuh5_context_tests_qualified.txt`,
`nuh5_context_lint.txt`, and `nuh5_context_lambdapi_check.txt`.
The generated input probe is `nuh5_registered_model_context.lp`; its full
Lambdapi log is `logs/probes/nuh5_registered_model_context-20260914-154909.log`
under `emdash2/`. The open inherited adoption baseline is recorded in
`nuh5_model_profile.txt`. No active Lambdapi owner or registry changed, so
the preceding mathematical warning/catalog/health evidence is unchanged.

Each checkpoint must synchronize this plan, the parent ledger and relevant
authority documentation, and preserve constructed/supplied/trusted
distinctions. No pushing, merging, publishing or cleanup is authorized here.
