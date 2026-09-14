# Native Homology Model And Reifier: Living Implementation Plan

Date: 2026-09-14

Status: NUH-5A preparation/replay and NUH-5B1 native model/whole δ/exactness interface qualified; raw-window observation migration and full later adoption remain required

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
Whole-H retention is established at the same input; it does not yet identify
the legacy inverse-mate input with a direct raw input or a window's derived
column input. Establish the required input/observation comparisons at the
original H during this assembly, without endpoint casts or reselection.

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
