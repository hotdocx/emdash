# Native Homology Model And Reifier: Living Implementation Plan

Date: 2026-09-15

Status: active — native context, H and complete-arrow realization qualified at their recorded consumers; native δ/exactness and whole-diagram coherence next; legacy comparisons and auxiliary normalization deferred

Parent: [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

Ledger: [native owner and dependency ledger](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_OWNER_LEDGER.md)

## Scope And Existing Boundary

Latest user-directed priority (2026-09-14): make the native whole development
interact directly with native model contracts. Preserve CAS-selected matrices,
witnesses, results and their provenance; preserving the older formal
H/maps/δ presentation is a separate compatibility requirement and is no
longer a prerequisite for the primary route. Keep the qualified 0caa19d0
workflow available as compatibility evidence.

Use the existing `FreydAdjunctionModel R` (whole P/Q, with H derived from
them), its native normality and native row hypotheses as the primary formal
model input. NUH-5N1 now provides a separate TypeScript context declaring
this native model directly. The older `FreydHomologyModel` context and its
adapter remain available for compatibility. State native realization contracts explicitly
and qualify their connection to the actual CAS data. Do not replace a
missing theorem by assuming output exactness or silently strengthen an old
contract. Exactness must continue to come from the existing native theorem.

Priority order:

1. NUH-5N1: direct native model/reifier context and exact signature mirrors,
   reusing the already selected supported CAS result and coefficient inventory;
2. NUH-5N2: native whole H/maps/δ/exactness consumers under those contracts,
   with checked concrete interaction and explicit trust/realization boundaries;
3. NUH-6: native snake/LES work, retaining the general six-term scope and sign
   requirements, followed by NUH-7 qualification; and
4. later compatibility work: agreement with older formal presentations and
   optional point/projection normalization. Reopen a deferred experiment only
   for a separately selected task or a demonstrated necessary native consumer.

The recent point-predicate/inverse-projection resource probes are deferred.
They involve the native exactness interface too, so bypassing the legacy
model does not establish that every such normalization problem disappears.
The primary route keeps whole categorical proofs and only requires the
observations its actual consumers use. Required native typing, computation
and CAS-realization checks remain completion gates. Snapshots and the
resumption boundary are in `emdash2/audits/deferred-native-exactness-observations/`.

The whole-interface prototype is available for the new route: twelve
comparison/type/evidence definitions and three constructor/predicate checks
pass. The latter evidence is `logs/probes/nuh5b2e1_whole_type_review-20260914-234202.log`.
It adds no axiom or opaque certificate. The separate NUH-5N1 context is now
qualified below; its complete native H/maps/δ/exactness consumer remains NUH-5N2.

Current NUH-5B2e clarification (2026-09-14): "exactness observations" means
formal model-facing terms and diagram comparisons, not empirical testing.
The required output connects the whole native Im⇒K equivalences with the
native model's H/maps/δ and their CAS realization under the declared
contracts. It does not require the older formal presentation as an
intermediate diagram.
The CAS computations, native δ integration and generic whole exactness
theorems already work. A particular explicit point-predicate normalization
is not itself a prerequisite for the computational/internal architecture.
Prioritize the whole categorical exactness interface and the required whole
diagram comparisons. Keep the failed pointwise probes as unqualified
experiments; resume them only for a concrete consumer. This does not waive
the native-diagram/CAS realization bridge or turn it into optional external
assurance. The subsequent priority above moves only the older formal
presentation comparison out of the primary route.

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
uses the native whole owner. Its legacy formal connecting entry still uses
`homology_record_connecting`; that entry remains available for the later
comparison. The TypeScript observation now uses the native whole-δ observer
described below, with distinct native normality and row contracts.

Keep these distinctions explicit:

| Boundary | Current evidence | Required treatment |
| --- | --- | --- |
| Matrix operations and retained selections | Existing native polynomial algorithms and checked selected results | Reuse the original result; do not recompute or reselect during preparation |
| Coefficient interpretation | Supplied formal ring/generator/coefficient references under an explicit realization | Generate deterministic names and all declarations before freezing the environment |
| Universal providers and coherent model | Supplied/trusted semantic contracts, not derived from finite matrix equations | Retain their classification and provenance |
| Model normality | Supplied model enhancement | Do not manufacture a correctness theorem by declaring its type |
| Whole δ and categorical exactness observations | Generic native theorem is qualified; retained concrete observation migration remains | Connect the model consumer to those actual native owners before NUH-5 completion |

## NUH-5N1: Direct Native Context — Qualified

The new [native rational context](../src/v3_2/algebra_formal_freyd_native_rational_model_context.ts)
accepts an issued native backend registration and the original supported CAS
selection. Its formal model inputs are exactly:

```text
M : FreydAdjunctionModel(R)
N : FreydAdjunctionModelNormality(M)
```

The [private signature mirrors](../src/v3_2/algebra_formal_freyd_native_model_signatures.ts)
map to the existing Lambdapi owners, including the implicit R of normality.
They introduce no mathematical primitive, runtime rule or formal adapter.
The environment contains neither `FreydHomologyModel` nor its H observer or
native-normality adapter. Native and legacy registrations are separately
issued; the native registration requires `adjunctionModelContract`, so an
older model contract cannot silently be relabelled.

Both contexts use the same [rational preparation](../src/v3_2/algebra_formal_freyd_rational_preparation.ts).
It collects and seals coefficient names while reading the original equation,
raw-witness and selected-result inventories. It takes no formal model value
or model type. Its existing `preparedModel` field denotes the CAS inventory
(18 H selections, eight maps and three windows in this fixture), not an old
formal model. This reuse does not require reconstructing the old formal H
objects or proving comparison with them.

Five focused tests pass in 29.91s. They check typed native inputs and dependent
normality, absence of legacy model signatures, immutable preparations,
unsupported/missing inputs, and no CAS universal/homology reselection during
preparation. Native and legacy contexts produce identical selected-data
inventories. Cross-model and cross-ring checks reject old models, old
normality, and normality belonging to another native model. The native CAS
consumer replays the original nonsplit result, explicitly adopts 55 computed
equations for 422 original labels, and constructs their typed raw witnesses
in the same native environment, adding no model-realization or exactness
assumptions. Four existing legacy preparation/replay tests pass in 9.51s.

Localized TypeScript compilation, affected-file ESLint and workspace checks
pass. The emitted native input probe passes six assertions against the active
Lambdapi owners with warnings enabled and the default 90s guard. No active
Lambdapi source, warning owner or generated catalog changed; prior mathematical
qualification evidence is carried forward. No repository aggregate ran.

Evidence under `emdash2/`: `tmp/probes/nuh5n1_types.txt`,
`nuh5n1_lint.txt`, `nuh5n1_tests.txt`, `nuh5n1_legacy_regression.txt` and
`nuh5n1_lambdapi.txt` in that same probe directory. The generated artifact is
`tmp/probes/nuh5n1_native_context.lp`; its full conformance log is
`logs/probes/nuh5n1_native_context-20260915-000534.log`.

**Boundary:** M, N and coefficient interpretation remain supplied inputs.
This is a checked native context and CAS equation/raw-witness integration,
not yet a realization of native H/maps/δ on those selected results and not
a closed construction of the native model. NUH-5N2 must expose those actual
native owners, connect them coherently to the computed data under explicit
realization and row contracts, and use the already derived whole exactness
theorems. Whole action must stay with the native functors/transformations;
caller-supplied naturality squares and assumed output exactness are not a
replacement. The deferred legacy comparisons and projection probes stay deferred.

## NUH-5N2A: Native H And Map Realization — First H Consumer Qualified

The next concrete interface is H_M(e,d,chain), defined by applying the existing
`freyd_adjunction_model_func M` to `freyd_raw_chain_native_cone e d chain`.
Its raw-map action specializes the existing
`freyd_raw_chain_adjunction_homology_map_func` to the P/Q projections of M.
Keep that internal functor as the owner; a readable map is its application,
not a separate map choice or manually supplied naturality proof. These
definitions require no old formal model, ordinary H record or output
exactness premise.

First qualify these native observations at their existing whole owners and
expose exact TypeScript signature mirrors. Then let the selected CAS H
presentation interact with that native H through an explicit realization
claim, classified as supplied/trusted presentation semantics. Such a claim
must not be described as a theorem for arbitrary M. Reuse model-independent
matrix/chain preparation and the original CAS result; no old H comparison
or selected-homology-provider adoption is a prerequisite. Whole H remains
the formal owner even when the CAS boundary requests one concrete observation.

Reject this design if the native terms require legacy W/V, replace the
whole action, lose the original raw endpoints, or can silently reinterpret
a legacy model as native. Required localized evidence: owner/application
checks in Lambdapi, exact frontend conformance, original nonsplit CAS
realization with an explicit trust boundary, and legacy observation regression
checks if shared implementation changes. Native complete-arrow/δ realization,
native row contracts and the whole exactness consumer remain subsequent
NUH-5N2 requirements.

The [native observation owner](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_model_observations.lp)
now implements those three definitions. Its five reviewer checks retain the
original whole H application, original raw-map functor, native map action,
literal H endpoints and Hom action. No primitive, rewrite or unification rule
was added. Both the affected predecessor reviewer and this reviewer pass
with warnings enabled and zero warnings.

The [native signature mirrors](../src/v3_2/algebra_formal_freyd_native_model_observation_signatures.ts)
add exact object/map observations and reuse the existing two model-independent
raw-chain-map mirrors. The native rational context advances to profile v2.
Legacy and native point observation adapters share the unchanged selected-data
checking/transport implementation, with separate model types, owner names,
operation IDs and profile revisions. Native queries cannot be mistaken for
legacy queries.

The [native H workflow](../src/v3_2/algebra_formal_freyd_native_homology_workflow.ts)
accepts a native model, original selected H realization and source. It finds
existing matrix proofs by their exact type, computes missing matrix facts
through the original CAS adapters, and constructs the original raw pair and
native H query. Callers do not assemble its proof references. The concrete
consumer uses degree-1 C from the original nonsplit result. Its 55 previously
adopted equations do not contain the precise semantic chain-zero formula used
by this observation, so one additional computed equation is needed. The
workflow computes it without replaying H or reselecting any universal.

It then records exactly one `trusted-presentation-semantics` claim identifying
this native H observation with the selected CAS presentation. This is a
selection-specific interpretation condition on the supplied model, not a
theorem for arbitrary P/Q and not a proof of whole realization coherence.
There are 56 computed equations and one model interpretation in the resulting
source; no old model, ordinary selected-provider proof, or output exactness
assumption is introduced. Repeating the request reuses all four prerequisite/
interpretation claims without another decision or source change.

Nine native tests pass in 53.85s, including wrong-model/foreign-query/stale-data
rejection and the map signature at actual native H endpoints. Four legacy
H/map observation regression tests pass in 7.68s. Focused TypeScript
compilation and lint pass. Three emitted Lambdapi files pass ten assertions:
six native inputs, the native H/CAS presentation/explicit realization, and
the native induced map. Together with the five owner reviewer assertions,
these are the affected formal checks. All use the default 90s guard.
The source-metrics registry/health report, catalog and source TOC checks are
current; health was refreshed with `--no-check`, not a repository typecheck.
No aggregate ran and the deferred normalization probes were not resumed.

Evidence under `emdash2/tmp/probes/`: `nuh5n2a_types.txt`, `nuh5n2a_lint.txt`,
`nuh5n2a_tests.txt`, `nuh5n2a_legacy_regression.txt`,
`nuh5n2a_native_observations.txt`, `nuh5n2a_conformance.txt`,
`nuh5n2a_catalog.txt`, `nuh5n2a_health.txt` and `nuh5n2a_toc.txt`.
The generated native context/H/map probes are respectively 2,052/172,465/4,341
bytes. Full logs are `logs/probes/freyd_adjunction_model_observations-20260915-001426.log`
and `logs/probes/nuh5n2a_native_{context,H,map}-20260915-{003403,003412,003420}.log`
(matching context/H/map in order).

**Next:** use the now-qualified native map owner for complete-arrow CAS
realization, then the native whole δ and categorical exactness consumers
with coherent realization and row contracts. A point agreement alone does
not supply that coherence. Preserve the original whole operations and use
the derived native exactness theorem; no return to the old formal diagram
or deferred projection-normalization studies is needed for this checkpoint.

## NUH-5N2B: Complete Native Arrow Realization — Qualified

Use the existing `FreydArrowObservation(R) = Obj(LaxArrow_cat(Freyd(R)))`
carrier for one complete native H-map observation. Move that carrier and
its raw-arrow introduction to a model-independent owner, preserving names
and bodies for the old workflow. The new native observation is `lax_edge`
at the two original H_M inputs and the already-qualified H_M map. No new
arrow record, naturality primitive or output exactness premise is needed.

The CAS workflow should automatically prepare the original source/target
raw inputs, three component maps, two chain-map agreements and computed
result map. Reuse the native matrix-prerequisite machinery, but do not
adopt independent H-point realization claims as prerequisites: the one
complete-arrow realization already includes both endpoints. Such an
agreement remains an explicit selected-model interpretation, not a theorem
for arbitrary M or proof of coherence over all diagrams.

Qualification must retain the whole H map owner and visible arrow
projections, a nonzero/nonidentity selected map from a nonsplit sequence,
rejection of legacy/mixed models and changed selections, source/proof reuse,
and exact emitted Lambdapi conformance. No universal/homology reselection
may occur while preparing or realizing that already-computed map. Native
whole δ, exactness and the remaining whole-realization coherence are still
required after this tranche.

The [shared carrier owner](../emdash2/emdash3_2_commutative_algebra_freyd_arrow_observations.lp)
now owns the two existing definitions, preserving their unqualified names
and bodies. There are no repository references to their old fully qualified
names. The old model-map module imports that owner. The
[native arrow observation](../emdash2/emdash3_2_commutative_algebra_freyd_adjunction_model_arrows.lp)
adds one definition using the original `lax_edge` and native H map; no
primitive or rewrite/unification rule is added. Native and legacy reviewer
projections both pass, with zero warnings before and after the extraction.

The native rational context advances to profile v3. Its private mirrors
include the shared arrow carrier/introduction and the native complete-arrow
observation. The map adapter shares the existing transport/checking code,
with separate native model, point-profile, observer and operation-ID choices;
mixed native/legacy profiles are rejected. The shared native
[realization session](../src/v3_2/algebra_formal_freyd_native_realization_session.ts)
can prepare point inputs without adopting their realization claims. The
existing standalone H workflow still adopts its one point claim explicitly.

The new [native map workflow](../src/v3_2/algebra_formal_freyd_native_map_workflow.ts)
takes the issued map preparation and native context, automatically wraps the
original source/target CAS H selections, computes/reuses matrix prerequisites,
and records one complete-arrow interpretation. It adopts no independent
endpoint-realization or selected-provider proof. Its concrete consumer is
the degree-0 inclusion x in the nonsplit sequence concentrated in degree 0:
`0 → R ─x→ R → R/(x) → 0`. The original CAS computation confirms that the
induced map is nonzero and differs from identity. This additional consumer
does not replace the earlier two-term nonsplit fixture or its three windows.

The first call reuses nine claims, computes three missing matrix equations
and adopts one `trusted-presentation-semantics` arrow agreement. Repeating
it reuses all thirteen requests without another decision or source change.
No H/map/universal algorithm is rerun during realization. The agreement
contains the original native source, target and H map, and their selected CAS
counterparts; it remains explicit model interpretation, not a theorem for
arbitrary M or a proof of coherence over every diagram.

Four native arrow tests pass in 33.62s. Nine native context/H regressions pass
in 53.47s, and four legacy H/map regressions pass in 6.63s. Focused types and
lint pass. The native and legacy arrow reviewers each pass four assertions;
four emitted native files pass thirteen assertions; the existing legacy
native-connecting reviewer passes six more after the shared-carrier move.
These 27 affected formal assertions run serially with warnings enabled under
the 90s guard. Each TypeScript group also has its own 90s guarded process.
The source registry, catalog, static health snapshot and source TOC are
current; health was refreshed with `--no-check`. No aggregate or deferred
normalization experiment ran.

Evidence under `emdash2/tmp/probes/`: `nuh5n2b_types.txt`, `nuh5n2b_lint.txt`,
`nuh5n2b_arrow_tests.txt`, `nuh5n2b_context_regression.txt`,
`nuh5n2b_legacy_regression.txt`, `nuh5n2b_arrow_owners.txt` and
`nuh5n2b_conformance.txt`. The emitted complete-arrow probe is
`nuh5n2b_native_arrow.lp` (111,127 bytes, three assertions). Full conformance
logs are `logs/probes/nuh5n2b_native_arrow-20260915-010627.log`, the native
context/H/map logs ending `010635`/`010644`/`010652`, and
`logs/probes/freyd_homology_model_native_connecting-20260915-010702.log`.

**Next:** native whole δ realization and categorical exactness under native
model/row contracts, followed by the complete bounded native diagram and
its coherence/qualification. Continue to retain the original CAS choices
and derived native output theorem. The one-arrow agreement does not close
the remaining whole-diagram coherence requirement.

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
`constructsModel` and `adoptsClaims` remain false in this preparation profile.
NUH-5B2d1 upgrades it to native connecting observations and requires the
explicit `nativeNormalityContract` registration field. Native row
interpretations remain separately adopted supplied contracts. NUH-5A changed
no public barrel, checker, Core owner or mathematical signature; NUH-5B2d1's
new observation signatures are explicit below. The retained nonsplit consumer
calls this helper instead of constructing its inputs by hand.

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

NUH-5B2d experiment (2026-09-14): replace the observation builder's old
component target with an explicit native wrapper: specialize the original
whole δ to the four raw rows over Terminal, then compose the retained-column
H comparisons at Terminal_obj. Package that arrow in the existing complete
arrow observation. Its formal normality and short-row aliases refer to the
native whole contracts through the original model adapter. Give all three
private LF signature mirrors new native names, so the checker rejects old
normality/row assumptions instead of silently reinterpreting their symbols.
Retain existing raw preparation, coefficient collection, H choices and
computed equation evidence. Row/whole-model semantics remain explicitly
supplied interpretations; this migration does not derive them from matrices.

The first combined checks exhausted the guard while rechecking imported
legacy comparison or native upper-lift modules, before reaching the new
wrapper body. Changing import order moved that boundary; a fresh dependency-
object experiment also exhausted the guard and is not the selected workflow.
The retained-input comparison now calls its existing incoming-source law
directly, without importing the unused whole-H recipe comparison proofs.
This preserves its proof body up to the old transparent alias. The native
raw-point and retained-model observation stages keep K and its point general;
only the final complete-arrow observation specializes to Terminal_obj.
These source checks pass without cached objects, new comparison assumptions
or raised limits. The failure was computational, not a mathematical rejection
of the native construction.

NUH-5B2d1 qualification (2026-09-14): the
[native model context](../emdash2/emdash3_2_commutative_algebra_freyd_homology_model_native_context.lp)
aliases native whole normality and shortness at the same original P/Q.
The [raw point observer](../emdash2/emdash3_2_commutative_algebra_freyd_raw_window_connecting_observation.lp)
uses the original whole δ and selected column comparisons. The
[retained-model observer](../emdash2/emdash3_2_commutative_algebra_freyd_homology_model_native_connecting.lp)
then applies the existing retained/native input comparisons at general K
and x; only its final complete-arrow wrapper fixes Terminal_obj. Both
original H objects remain literal observations. These are five definitions,
with no new primitive, rewrite or unifier. The narrower input-comparison
dependency preserves the old proof after unfolding its transparent alias.

The TypeScript builder now targets `freyd_homology_model_native_connecting_observation`.
All 47 argument positions and original raw/H selections remain unchanged.
The three private LF mirror names explicitly identify native normality,
native whole row shortness and the native observer. Valid legacy normality
or row terms are rejected at the new interface. Observation/registration
profiles advance to v2 and the bounded model profile to v3; the required
backend field is now `nativeNormalityContract`. The profiles explicitly
record categorical endpoint comparisons and no endpoint casts. No Core,
checker, evaluator or public-barrel implementation changed.

Eight focused TypeScript tests cover these contract distinctions, automatic
rational preparation/replay, retained nonzero nonsplit connecting adoption,
reuse without duplicate claims, original H chain identity and no universal,
homology or connecting reselection. The concrete emitted observation also
checks in Lambdapi. Its model, native normality, whole row shortness and
complete-arrow interpretation are still explicit supplied/trusted contracts;
the test does not construct a closed model or prove a general CAS realization.

[The focused gate](../emdash2/scripts/check_freyd_native_model_connecting.sh)
compiles only the affected test dependency tree, runs adoption/emission,
and checks the exact emitted LP artifact as separate guarded stages. A test
emission reports that oracle checking is pending; only the gate's final
Lambdapi stage establishes conformance. The combined adoption/oracle run
exceeded the guard and is not claimed green. No stage raises the existing
90-second/2-GiB limits or uses cached proof objects.

Next NUH-5B2d2 qualifies the complete automatic bounded-model adoption and
native exactness observations, keeping their supplied-contract boundary
explicit. The single-window gate does not discharge those requirements.
NUH-6 snake/native comparison and NUH-7 final qualification remain open.

NUH-5B2d2a experiment (2026-09-14): the phase profile reaches six actual
homology terms around 82 seconds; their term construction itself takes only
milliseconds. Nine source validations consume about 41 seconds. A second
profile separates unchanged adoption-current checks (roughly two seconds
per validation) from repeatedly rebuilding/typechecking declaration prefixes
(growing from roughly two to four seconds per validation). Test a body-free
opaque-declaration batch at the existing LF environment owner. Keep sequential
scope/duplicate checks, the same checker factory, a fresh full environment
typecheck, all adoption-current checks and final source/environment comparison.
No cached validity, skipped proof check, new conversion rule or general
endpoint-normalizer change is part of this experiment.

The implemented batch is `CoreLfDeclarationEnvironment.extendOpaqueBatch`.
Only `validateAlgebraFormalAssumptionSource` adopts it in this tranche.
It preserves the original prefix declarations and reviewed checker factory,
checks all scopes afresh in declaration order, then checks every declaration
type once through the existing checker. Bodies and transparent additions are
rejected; an existing transparent prefix remains available to its checker.
Every original adoption-current check and final retained-environment
comparison still runs. No validity cache or mathematical primitive is added.

The focused LF/source suite passes 18 tests, including dependent batches,
atomic failures, foreign checkers, existing transparent definitions, mutated
base types/forward references and repeated freshness checks on all adoptions.
The existing six-H/raw-witness/rejection consumer passes three tests in about
66 seconds. These are the existing selected terms and provider contracts;
this performance improvement does not turn them into native model exactness
observations. Focused compilation and ESLint pass. The existing staged native
δ gate passes its four tests and nine emitted LP assertions. The emitted
223,966-byte artifact is byte-identical to the preceding checkpoint's
artifact, SHA-256 `b898f3d82636b6d6835e8fd26ec4b9ec4a8b16f91a95d8b474bc76ca6a6113df`.
No LP source, rewrite, unifier, checker/conversion implementation or public
barrel changes. The generic LF declaration owner changes only by the additive
opaque-batch method. Validation stays local under D-NUH-016.

Measured evidence under the unchanged 90-second/2-GiB guard:

| Probe | Result |
| --- | --- |
| `tmp/probes/nuh5b2d2_phase_profile.txt` | Before batching: nine source validations take 41.16 seconds; actual-H construction returns at 82.32 seconds; the run expires during raw witnesses |
| `tmp/probes/nuh5b2d2_validate_profile.txt` | Separates repeated declaration-prefix checking from unchanged adoption-current checks |
| `tmp/probes/nuh5b2d2_model_profile.txt` | After batching: the nine validations take 16.01 seconds; actual-H returns at 54.10 seconds and raw witnesses at 58.28 seconds; all 18 point and eight map observation builders return; allocation fails near 89.5 seconds before the model workflow returns |
| `tmp/probes/nuh5b2d2_bounded_homology_tests.txt` | Uninstrumented affected six-H/raw-witness/rejection consumer: three passes in 65.94 seconds |
| `tmp/probes/nuh5b2d2_declaration_source_tests.txt` | Eighteen LF/source tests pass |
| `tmp/probes/nuh5b2d2_native_connecting_gate.txt` | Separate focused compilation, four adoption/emission tests and the actual emitted native δ LP target pass; detailed log is `logs/probes/native_connecting_20260914_205721_2451188.log` |
| `tmp/probes/nuh5b2d2_native_artifact_comparison.json` | Exact emitted source matches the preceding checkpoint |
| `tmp/probes/nuh5b2d2_typecheck.txt`, `tmp/probes/nuh5b2d2_lint.txt` | Focused compilation and affected-file lint pass |

These timings diagnose this fixture, not a general benchmark. The newest
full-run failure is an allocation failure, not a completed adoption or a
mathematical counterexample. Per-observation private signature construction
takes about 0.15–0.22 seconds and is secondary to the complete workflow cost.

Next NUH-5B2d2b should first audit the model test's actual prerequisites.
Its present fixture runs the older six-H construction and all raw witnesses,
then observes the model twice (points/maps first, then connecting upgrade).
The public model consumer accepts the retained whole adoption directly and
constructs its own missing input claims. Test a separate minimal model
consumer at that boundary, keeping the original selection, every required
adoption/current/type check and the larger combined-source integration case.
Do not remove either endpoint window, the nonzero middle δ, reuse tests or
supplied-contract classifications to fit the guard. If that boundary is still
too expensive, profile its remaining adoption/freshness and allocation costs
before selecting another local optimization. Native exactness observations,
NUH-6 and NUH-7 remain required.

User direction during NUH-5B2d2b (2026-09-14) permits increasing the previous
90-second check limit after review. The complete model test was still
progressing through its first observation pass at 86 seconds and then has
a second connecting/reuse pass to perform. Allow an explicit 180-second
guarded experiment for that selected test, retaining the 90-second default,
2-GiB memory cap, serial lock, file cap and ordinary checker. Record phase
times and memory use. A time increase alone cannot explain away the previous
allocation failure. This supersedes the earlier blanket time-limit ceiling,
not the localized-validation requirement or any mathematical gate.

The 180-second control at a 512-MiB V8 old-space allowance fails by allocation
at 99.3 seconds, after all eight induced-map observations. A 384-MiB control
returns the first model pass at 98.0 seconds and reaches the first connecting
workflow at 109.6 seconds, then fails by allocation at 111.5 seconds. Its
observed virtual peak is 2,096,952 KiB, very close to the 2-GiB address-space
cap; physical peak is about 733 MiB. These controls establish that raising
time alone is insufficient. Their logs are
`tmp/probes/nuh5b2d2b_model_180s_memory.txt` and
`tmp/probes/nuh5b2d2b_model_180s_heap384.txt`.

The next gate keeps the original combined fixture and tests a bounded young
generation (`--max-old-space-size=384 --max-semi-space-size=4`) within the
same process/aggregate memory limits. The new `--bounded` mode of
`scripts/check_freyd_native_model_connecting.sh` selects the original complete
point/map, rejection, connecting-upgrade and reuse tests, then emits all three
window probes. Each LP target is checked separately. The gate is an experiment
until every stage passes; emission marks its manifest as awaiting independent
Lambdapi validation. The smaller model-only fixture remains a possible
dependency test, not a replacement for the retained combined integration.

The first gate with CLI heap flags again fails by allocation. A small worker
probe then identifies the actual configuration error: this Node 24.11.1
build drops those V8 CLI flags when starting isolated test workers. The
worker's heap limit was 1,174,405,120 bytes, so the preceding 512/384/young-space
launcher comparisons are **not** evidence that those worker limits changed.
Passing the same flags through `NODE_OPTIONS` yields the intended 415,236,096
byte worker heap limit. The bounded gate now verifies this in a separate
worker preflight before the expensive fixture; the single-window gate also
passes its existing 512-MiB selection through the inherited environment.
Logs: `tmp/probes/nuh5b2d2b_node_heap_probe.txt` and
`tmp/probes/nuh5b2d2b_node_heap_inherited.txt`. All OS memory/serial/file caps
remain unchanged. Retest the complete gate under the verified worker limit.

That verified 396-MiB worker reaches the first connecting observer but exhausts
its JavaScript heap at 155.7 seconds. A preparation-only size probe measures
5.8 MB of connecting-preparation snapshots and a 12.5-MB model inventory.
Those already nested JSON strings are embedded again in request, result and
adoption records. Test the existing lossless shared-JSON-table codec only at
the connecting/row adapter's transport boundary. Keep original realization
snapshots, every current check, selected values and formal terms unchanged;
record the transport in observation profile v3 and test exact decoding back
to the original payload. This adds no validity cache or mathematical rule.
The complete gate and the original nonsplit gate must pass before promotion.

The compact-transport single-window gate passes focused compilation, four
adoption/signature tests (including exact payload round trips) and nine LP
assertions. Its emitted source remains byte-identical to cc8a4dc0/3871827c:
223,966 bytes, SHA-256
`b898f3d82636b6d6835e8fd26ec4b9ec4a8b16f91a95d8b474bc76ca6a6113df`.
Logs: `tmp/probes/nuh5b2d2b_single_compact_gate.txt`,
`logs/probes/native_connecting_20260914_212552_2517645.log`, and
`tmp/probes/nuh5b2d2b_compact_artifact_comparison.json`. The complete gate
with the same transport and verified worker limits is the next required
validation; its current run is recorded in
`tmp/probes/nuh5b2d2b_bounded_compact_gate.txt`.

The compact 396-MiB run completes the first connecting workflow at 158.4
seconds, then exhausts its V8 heap at the second; the guard subsequently
terminates the failed process at 180 seconds. Its virtual peak was 1,907,460
KiB. Select 512 MiB of old space with the same 4-MiB semispace and verify
the inherited worker limit (524 MiB on this build). This fits the remaining
address-space margin without raising the 2-GiB OS cap. The complete five-test
gate includes two more windows, a full connecting replay and rejection
checks after that first 158-second prefix; its reviewed deadline is now
240 seconds. The guard keeps 90 seconds as the default and permits this
explicit extension. No test/window/check is removed to meet the deadline.

The 524-MiB/240-second run completes all three connecting workflows at
151.9, 168.9 and 181.3 seconds, then exhausts its heap during the later full
reuse pass (207.6 seconds). Inspect adapter closure retention before another
limit change. Point/map/connecting adapters each retain an entire private
signature environment while comparing only their declared interface names.
A pure 18-point retention probe measures about 11.9 MB for those complete
environments. Keep the very same checked declaration objects needed for each
comparison, releasing only unused prerequisite-environment storage. Construction,
body rejection and every exact type comparison remain unchanged. This is
neither a proof-validity cache nor a change of signature/semantic policy.

With that retention fix, all three connecting workflows and the full reuse
pass return; the latter returns at 234.2 seconds. The 240-second deadline
then interrupts the final wrong-normality rejection, after its source check.
Unlike the preceding runs, this is a deadline exhaustion without a V8/OS
allocation failure. Select 300 seconds for the complete five-test gate,
including its final rejection and all-window emission; retain the verified
524-MiB worker heap and 2-GiB OS cap. Ordinary LP targets still default to
90 seconds. Evidence: `tmp/probes/nuh5b2d2b_bounded_trimmed_gate.txt` and
`logs/probes/native_connecting_20260914_220723_2582969.log`.

NUH-5B2d2b qualification: all five complete-workflow tests pass in 267.08
seconds under the 300-second deadline and verified 524-MiB V8 heap limit.
This retains all 18 H points, eight maps, all three connecting windows, both
zero endpoints and the nonzero middle, the complete source prefix, shared
row proofs, no-reselection assertions, full reuse and negative cases. The
connecting upgrade reuses 210 claims and adds 11 entries; the resulting
source contains 143 entries, of which 38 are explicitly trusted semantic
claims. Coherent model and normality remain supplied inputs.

The wrapper initially expected four assertions per emitted window; the
existing test emits six (both δ arrows, the interpretation proof and three
row maps). The count was corrected, the same manifest revalidated and the
three exact emitted files checked separately at 90 seconds each. All 18 LP
assertions pass. Do not describe the initial wrapper exit as a mathematical
failure or repeat the already passed adoption stage for that metadata typo.

The receipt `tmp/probes/nuh5b2d2b_qualification.json` records checked source
hashes, window hashes, counts, limits and logs. The complete TypeScript log is
`logs/probes/native_connecting_20260914_221409_2598565.log`; LP logs are
`logs/probes/connecting_0-20260914-221948.log`,
`logs/probes/connecting_1-20260914-222151.log`, and
`logs/probes/connecting_2-20260914-222303.log`. Focused compilation, affected
ESLint and ten resource-guard tests pass. Source-only LP inventories are
unchanged; no LP owner, rewrite or unifier was edited.

Next NUH-5B2e, native exactness observation owner inventory: the three
`freyd_raw_native_window_{middle,source,target}_exact` definitions already
return fixed-forward `OmegaEquivAlong` evidence on the original whole
Im⇒K comparisons. The existing `omega_equiv_along_fapp1_fapp0` can map that
evidence through an internal evaluation functor, retaining the selected
inverse action. The retained-model adapter supplies the same whole P/Q;
no ordinary kernel/cokernel record conversion is needed for this route.
The next observer must expose the actual comparison and its evidence, and
check its relation to retained-H endpoints before claiming exactness at a
retained displayed position. This inventory is a construction starting point,
not a completed point-observation or retained-endpoint theorem.

Earlier NUH-5B2e1 experiments (preserved history, superseded as an active queue
by the direct native priority above): expose the original whole raw-window comparisons as
thin specializations of `one_cat_native_window_*_exact_comparison`. Define
their point observations through `tapp0_fapp0`, and express point exactness
as existing `OmegaEquivAlong` on those actual arrows. Map the already derived
whole evidence through the existing `fapp0_func(x)` using
`omega_equiv_along_fapp1_fapp0`; the selected inverse must be that same
functor's action on the original inverse. Add no primitive, rewrite, unifier
or caller-supplied coherence equation. Qualify the whole comparisons, their
Hom action, point evidence and selected inverse observations on the original
raw window. This is the native observation prerequisite. The subsequent
retained-H/arrow comparison and TypeScript adoption remain required before
NUH-5B2e completion; point evaluation alone does not discharge them.

The first combined e1 probe exceeds the memory guard. Prefix checks isolate
the cost: all six model/raw whole-comparison definitions, the first point
arrow and its `OmegaEquivAlong` type check. Adding the direct fully
instantiated `omega_equiv_along_fapp1_fapp0` proof exhausts allocation.
The generic evaluation lemma over abstract F/G/h checks, including both
selected inverse projections. Test that derived lemma as the window proof's
application boundary; it adds no primitive or reduction rule. The generic
pass alone does not qualify the instantiated native observation.

The whole witness checks against the newly named comparison when its
category is explicitly `Functor_cat K (CommRingFreydPresentation_cat R)`.
Letting that category be inferred through Hom led to a failed sort problem.
The next point-proof probe retains this explicit whole type in a local
evidence binder before applying evaluation. This compares the same original
proof with the actual comparison; it introduces no cast, new inverse or
pointwise exactness premise.

The point proof is accepted with its inferred result type, but explicit
predicate/inverse review still exceeds the allocation guard. Before changing
any formal owner, test the same term with earlier major collection. The
installed OCaml 5.4 `Gc.control` documentation gives `space_overhead` default
120 and specifies that a lower value collects unreachable blocks earlier;
`startup_aux.c` maps runtime option `o` to that control. Probe `o=20` with the
unchanged 2-GiB guard, ordinary checker and subject reduction. This is runtime
configuration, not an endpoint-normalizer or opacity change. The review
remains required even though declaration inference succeeds.

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

NUH-5B2d1: the modified input-comparison owner and all three new owners pass
warning-enabled source checks. Six registered reviewer assertions check
the native contract aliases, original H endpoints and the stored complete
arrow. Four emitted generic assertions check the three exact private
signatures and the unchanged 47-argument conditional call.

Localized TypeScript compilation and ESLint pass. The focused gate runs
four tests (one nonzero nonsplit adoption/emission and three signature/legacy-
contract controls), then checks its exact 223,966-byte LP artifact with nine
assertions. Four automatic rational preparation/replay tests also pass.
The gate's test phase took about 33 seconds, under the unchanged guard.
No universal or connecting replay is introduced by model interpretation.

Owner logs span `194441`–`194506`; reviewer and generic conformance logs are
`freyd_homology_model_native_connecting-20260914-195745.log` and
`nuh5b2d_native_signatures-20260914-195543.log` under `emdash2/logs/probes/`.
The observer, reviewer and generic conformance inventories/raw warning
blocks match the import-only control at `201238`: 1,490 critical-pair and
169 pattern reports. The modified input owner matches its original at
`194319`: 1,290/169, with no warning-body or source-location delta. Exact
comparison data is `emdash2/tmp/probes/nuh5b2d_warning_comparison.json`.

The complete focused gate log is
`emdash2/logs/probes/native_connecting_20260914_201253_2325640.log`;
its exact emitted artifact is
`emdash2/tmp/probes/native_connecting_20260914_201253_2325640.lp`, checked
in `native_connecting_20260914_201253_2325640-20260914-201330.log`.
The broader automatic bounded-model adoption was reattempted separately
and still terminated under the guard; see
`emdash2/tmp/probes/nuh5b2d_bounded_model_adoption.txt`. Its current phase
has not yet been isolated. NUH-5B2d2 must locate that cost and qualify the
complete workflow; do not repeat the monolithic check merely for reassurance.

The existing native-input and retained-column reviewers also pass after the
dependency change (`202102` and `202124`). Affected strict LHS audits,
catalog, source TOC, report headers, script syntax and source-only health
checks pass; the health inventory covers 1,207 files. The focused gate
rechecks its affected TypeScript dependency tree, and the separate final
ESLint check is recorded in `nuh5b2d_lint_final.txt`. No repository-wide
typecheck, aggregate or general endpoint-checker experiment was run.

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
