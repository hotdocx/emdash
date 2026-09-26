# Action-Profile Integration: Displayed Assembly Investigation

Date: 2026-09-26

Status: conditional represented-section proofs and projection controls pass;
displayed profile and inverse-assembly candidates remain unselected

Owner: [living plan](EMDASH_ACTION_PROFILE_INTEGRATION_PLAN.md), row `API-05`.
Production mathematics remains at checkpoint `f0f327d6`. This investigation
uses `emdash2/tmp/probes/api_ordinary_profile_minimal/`; it does not restore
the commented displayed half of the candidate pointwise-equivalence owner.

## Decision And Actual Consumer

The user selected an explicit action-based premise for displayed assembly.
The old unqualified primitive is not an accepted integration result.
The actual consumer, `emdash3_2_direct_cover_completion_locality.lp`, has
three assembly stages: an ordinary fibre transformation, a displayed
transformation between matching maps, and an ordinary outer transformation
between matching endofunctors. Each needs its actual profile. `Psh_cat` is
Cat-valued; none of these profiles follows from a blanket ordinary-category
assumption.

An earlier prerequisite also needs migration. The retained-member theorem
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
displayed map. A producer of the required output-section profile has **not**
been established. Nor has the rest of the retained-member derivation or the
complete locality/rho construction been requalified.

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

Use the immutable receipt input blobs for exact recovery. The manifest also
records the authoring scripts, whose successive archive/control steps are
not an idempotent build. These are investigation artifacts, not a second
accepted library or a clean-checkout integration route.

## Next Required Work

Trace the actual glue-output and matching-map action prerequisites through
the retained-member derivation. Establish the required profiles from the
qualified producer, or revise the affected interface with an explicit,
reviewed contract. Do not introduce a blanket strictness or rho-admission
axiom merely to make the consumer check.

Review the displayed candidate against the complete internal action before
selecting its primitive inverse interface. Then qualify fibre, displayed
and outer rho assembly in order, preserving both inverse choices. These
remain required `API-05` work. Other directed/simplex consumers, TypeScript,
production cut retirement and final integration gates remain required by
the parent plan; Op/duality repair and new Empty audits remain excluded.
