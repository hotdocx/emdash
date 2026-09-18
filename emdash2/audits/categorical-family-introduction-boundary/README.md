# Whole Native Comma-Family Introduction: Partial Qualification

Status (2026-09-17, UA-4d): the isolated candidate checks constructor, point,
both arrow projections, retained triangle and the source projection through
third-level cells. The higher target projection and whole H comparison remain
open. The generic recursive Sigma actions are in the core; the two displayed
projection rules and Γ itself remain outside the library. The new isolated
whole source comparison p∘Γ ≅ A retains both maps and inverse laws, with
computing identity components. Its additional structural views are also
unpromoted; the source comparison does not establish the target or triangle
classification laws.
An intermediate target-section extraction now also has a checked whole
equivalence, with retained inverses/laws and identity components, using one
new unpromoted constant-section projection view. Its links to q∘Γ and D are
still open.

The active continuation is now the user-accepted
[universality assembly plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
(2026-09-17). This authorizes resuming the separate bounded Γ task; the
prototype remains unqualified. Its historical decision record is
[the consolidation ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_CORE_CONSOLIDATION_LEDGER.md#cc-4--comparison-consumer-review-in-progress).
This fragment is outside the positive library/check graph. The user selected completing consolidation first and retaining this meaningful
whole-interface refinement as follow-up work (2026-09-16). It is an experiment,
not a new primitive, a qualified higher-variance interface or a completed
whole H comparison. It does not resume the separate Op migration.

Given J:X→Y, A:K→X, D:K→Y and h:J∘A⇒D, the intended functor sends
x to (A(x),D(x),hₓ) in the existing RepresentedComma(J). It reuses the native
internal transformation-graph section, Σ base change along Op(A), an identity
Functord between accepted family presentations, and the outer opposite.
The six helpers are definitions. No naturality square is caller data.

The graph section helpers are protected. Consequently this experiment must
be appended to a full copy of their owning source; importing that source and
calling a protected helper from a separate module is rejected. From emdash2:

```bash
python3 - <<'PYCODE'
from pathlib import Path
owner = Path('emdash3_2_gray_transformation_graph.lp').read_text()
fragment = Path('audits/categorical-family-introduction-boundary/constructor_fragment.lp').read_text()
Path('tmp/probes/cc4_comma_replay.lp').write_text(owner + '\n' + fragment)
PYCODE
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/cc4_comma_replay.lp
```

At the original consolidation checkpoint, the constructors, object assertion
and source-arrow assertion pass. The target-arrow assertion fails. The
narrow displayed-identity guard corrections are independently covered by
`examples/displayed_identity_presentations.lp`; they do not qualify the
remaining target action. The residual target expression contains three
nonidentity displayed-Hom actions from the fibrewise Σ/internal action,
total base change and varying Σ projection. Do not replace those actions by
identities or claim their desired computation from the constructor type.

The checks run serially at 2GiB/90s with subject reduction enabled. The ledger
records source identity, earlier variants and the separate nucleus-diagnostic
6GiB qualification. Future promotion needs the target action, retained next
Hom/triangle data, actual homology specialization and warning/consumer checks.

## UA-4: Structural Projection Candidate

The current-source replay at baseline `2d5eb8a6` reproduced the failed target
assertion. A separate typed definition shows that this target observation is
an arrow D(x)→D(y); its normalization, rather than its formation, was missing.
Its normal form has three nested displayed actions: fibrewise Sigma of the
internal action, family-natural total base change, and the inner base
projection. The candidate observes their base coordinate without deleting
their retained fibre data.

`projection_action_rules.lpfragment` contains two unpromoted rules:

1. Projecting after fibrewise Sigma gives the projection of the original
   native dependent-Hom arrow.
2. Projecting after total base change along G:A→B gives G applied to that
   original base arrow.

The second rule permits a different outer displayed base because it observes
only the inner B-coordinate. Its visible endpoint pairs retain G(a) and G(b);
the input remains the actual typed base-change action. It neither identifies
outer base arrows nor replaces any filler by an identity. The selected
identity transformation in each whiskering pattern has its explicit
functor-category head: the less guarded direct-action attempt failed subject
reduction, and is not the candidate retained here.

Both rules typecheck at the existing `sigma_proj1_family_funcd` owner position.
The opposite-fibre Sigma consumer uses an arbitrary arrow in the native
dependent Hom, rather than manually reconstructing its fibre equation.
`projection_consumer.lpfragment` also checks that an arbitrary displayed map
between totals is not assumed to preserve the inner base. These computations
use the current family/opposite presentation; they do not qualify a general
ω-duality repair or change any Op signature.

With those two rules, the unchanged constructor fragment passes all three
assertions. The target observation normalizes to exactly D[g]. Removing
either rule makes that target assertion fail again. No Γ-specific action
axiom, new inverse choice, caller square or operational path cast is added.

`triangle.lpfragment` extracts the retained triangle at the original internal
Hom carrier, with A[g] and the actual retained second coordinate. It does not
claim that the raw nested-Sigma second coordinate itself converts to D[g].
Both next-action definitions in `next_source.lpfragment` and
`next_target.lpfragment` also typecheck with their intended endpoints.
At UA-4a their final assertions, asking for conversion to A[θ] and D[θ], both
failed. UA-4b's generic recursive Sigma owners now establish A[θ] and the next
source projection A[ξ]; D[θ] still fails. Typed whole action is retained, while
the target projection computation remains open. Nor do the whole source/target composite functors
already normalize to A and D merely because their point/arrow views do.

The core refinement keeps the first Hom owners for projection and base change,
computes their recursive next action, and totalizes the existing piapp1_func
section for section-total Hom action. It adds no primitive or unifier. The
first-Hom identity computations remain unchanged. The remaining target normal
form involves the displayed presheaf action of the varying Sigma projection;
a separate displayed-identity action probe alone did not close it.

The next task is the whole input/H comparison, addressing that displayed
Hom/projection boundary where the actual consumer needs it. Prefer canonical
whole comparisons with retained data over imposing a stronger global functor
eta/normalization requirement. Keep Γ outside the library while its required
qualification remains incomplete.

## Reproduce The UA-4 Candidate

From `emdash2`:

```bash
python3 - <<'PY'
from pathlib import Path
audit = Path('audits/categorical-family-introduction-boundary')
rules = (audit / 'projection_action_rules.lpfragment').read_text()
owner = Path('emdash3_2_cubical_square_total.lp').read_text()
marker = '// At a, totalize the b-indexed filler family.'
assert owner.count(marker) == 1
Path('tmp/probes/ua4_projection_replay.lp').write_text(
    owner.replace(marker, rules + '\n' + marker) + '\n' +
    (audit / 'projection_consumer.lpfragment').read_text())
comma = (Path('emdash3_2_gray_transformation_graph.lp').read_text() + '\n' +
         rules + '\n' + (audit / 'constructor_fragment.lp').read_text())
Path('tmp/probes/ua4_comma_replay.lp').write_text(
    comma + '\n' + (audit / 'triangle.lpfragment').read_text())
for side in ['source', 'target']:
    fragment = (audit / ('next_' + side + '.lpfragment')).read_text()
    Path('tmp/probes/ua4_next_' + side + '_types.lp').write_text(
        comma + '\n' + fragment.split('\nassert ', 1)[0])
    Path('tmp/probes/ua4_next_' + side + '_replay.lp').write_text(
        comma + '\n' + fragment)
Path('tmp/probes/ua4_source_third_replay.lp').write_text(
    comma + '\n' + (audit / 'next_source.lpfragment').read_text() + '\n' +
    (audit / 'third_source.lpfragment').read_text())
PY
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_projection_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_comma_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_next_source_types.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_next_target_types.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_next_source_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_source_third_replay.lp
# The stronger target conversion control is still expected to fail.
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_next_target_replay.lp
```

The runs use the serial 2GiB/90s guard, warnings and subject reduction enabled.
Relevant logs include:

- original target failure: `ua4_comma_baseline-20260917-164118.log`;
- typed target: `ua4_comma_target_typed-20260917-164649.log`;
- opposite Sigma projection: `ua4_sigma_op_projection_action-20260917-165104.log`;
- base-change owner: `ua4_sigma_basechange_projection_owner-20260917-165335.log`;
- actual target success: `ua4_comma_projection_actions-20260917-165354.log`;
- target normal form: `ua4_comma_projection_compute-20260917-165433.log`;
- retained triangle: `ua4_comma_triangle-20260917-170153.log`.

The two isolated rule owners add no warnings. In the graph consumer, the
candidate retains the same three inherited graph/strict-identity critical
pairs as the baseline, with identical term heads and rule families and no
parser issue. This is a scoped warning comparison, not a confluence theorem.
The living ledger records the final recipe replays and next-action boundary.

Source identity at the historical UA-4a audit (before the recursive Sigma
owner refinement; current core hashes and checks are in the living ledger):

| Source | SHA-256 |
| --- | --- |
| `emdash3_2.lp` | `24a4aab2c1691ca6baadf2a0a5900b2f6dbaf3f6bdc242ac8a368e75f2ba4ff9` |
| `emdash3_2_cubical_square_total.lp` | `bfc4acd2767fd2d794728912722121a9da24cbc81af17ec1e6d646e02c7a1101` |
| `emdash3_2_gray_transformation_graph.lp` | `d27e975c7652a5eaa6d4fbe51b4c9547f5125317521507c3cb938f9487623a75` |
| `constructor_fragment.lp` | `336faa2ae11a1093cb4e0552c3c46017e1dad1d99de3900cf9a5f8ccd54d5db7` |

## UA-4c: Whole Source Comparison

`whole_source_rules.lpfragment` and `whole_source.lpfragment` preserve a
checked construction of IsoEvidence(Functor_cat(K,X), p∘Γ, A). Its three
steps remove the family reframe from the projection, project total base
change, and project the totalized section. Precomposition, postcomposition
and composition of the existing IsoEvidence provide the forward map,
inverse and laws. Components in both directions compute to id at A(x).
The actual off-diagonal arrow action also forms at its original endpoints.
Callers supply only J,A,D,h; no additional square or inverse is an input.

The experiment makes its structural extensions explicit:

- a whole projection view for total(s), in the opposite presentation used by
  the existing comma encoding;
- corresponding opposite presentations of the existing Sigma-map and
  base-change projection equations;
- sufficient composition congruence with the same two operands and every
  endpoint compared;
- omission of repeated inferred source/target guards in the three existing
  ordinary identity-transformation projection rules, with their old RHSs.

The first projection view is a newly selected structural identification,
not a derivation from the old component beta rules. The other two present
the intended images of existing projection cuts under Op_func. Earlier
direct eq_ap attempts for those two did not check because the inner
composite normalized first; they are not counted as independent proofs.
These rules retain runtime functor heads. The actual maps are identities
at their original sources, whiskered and composed; no operational functor
data is obtained by equality transport.

This is a local comparison in the current comma presentation. It introduces
no Op signature, Op action on transformations, or new duality design, and
does not qualify unrestricted higher semantics. General Op/profile work
remains deferred. Full inference and owner/consumer qualification of these
candidate views remains necessary before promotion.

The ordinary identity-guard candidate also passes in a full owner-position
core copy. Its warning inventory retains 157 replaceable variables and
reduces inherited critical pairs from 1144 to 1140, with no added category,
term-head, rule-family or location count and no parser issue. The removed
diagnostics concern the three identity rules against product-valued functor
categories and the constant-terminal component overlap. This is scoped
diagnostic evidence, not a confluence theorem. Appending the rules in this
audit deliberately differs from replacing them at their owner; its warning
stream must not be used as that owner comparison.

Reproduce the actual source comparison independently of the two candidate
target-projection rules:

```bash
python3 - <<'PY'
from pathlib import Path
audit = Path('audits/categorical-family-introduction-boundary')
constructor = (audit / 'constructor_fragment.lp').read_text()
marker = '// The target side is the actual action'
assert constructor.count(marker) == 1
source = (Path('emdash3_2_gray_transformation_graph.lp').read_text() + '\n' +
          (audit / 'whole_source_rules.lpfragment').read_text() + '\n' +
          constructor.split(marker, 1)[0] + '\n' +
          (audit / 'whole_source.lpfragment').read_text())
Path('tmp/probes/ua4c_source_replay.lp').write_text(source)
PY
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4c_source_replay.lp
```

The replay passes eleven assertions at the serial 2GiB/90s profile with
warnings/SR enabled, including whole inverse-law projections and negative
controls. A projection of an arbitrary total-valued functor is not assumed
to be a section, unrelated endofunctors are not identified with id, and
composites with different supplied operands are not collapsed.

`whole_source_action_boundary.lpfragment` retains an additional, stronger
conversion assertion for the already-typed off-diagonal comparison arrow.
Appending it to the replay fails: that arrow does not yet convert to A[g].
This is separate from the existing source-projection computation A[g] and
from formation of the whole comparison and its inverse. Determine whether
the eventual H consumer needs this exact normal form; do not silently claim
it follows from identity point components. Its failure is not a timeout.

Relevant receipts are `ua4c_source_replay-20260917-192506.log` (eleven
assertions and typed arrow pass),
`ua4c_source_arrow_comparison-20260917-192636.log` (stronger conversion
fails), and `ua4c_identity_owner-20260917-184007.log` (owner-position guard
candidate passes). `tmp/probes/ua4c_identity_warning_comparison.json`
records the five-dimensional warning comparison with the current core.

The main remaining consumer is q∘Γ ≅ D together with recovery of h, followed
by the whole native H comparison. Its target uses the varying inner Sigma
projection and the transformation-graph section, rather than the outer
base projection settled here. Review those existing owners; do not install
a Γ-specific action axiom to hide that obligation.

## UA-4d: Native Target-Section Extraction

`target_section_extraction.lpfragment` uses the actual native graph section
s and the actual second projection, including Γ's family reframe. Reindex
that displayed projection along Op(A), calling the resulting map P. It has
constant target Op(Y). The two whole functors under comparison are

```text
U = π₂ ∘ Σ(P) ∘ total(s) : Op(K) → Op(Y),
V = P⋅s                  : Op(K) → Op(Y).
```

Here V is the existing postcomposed Pi section, read through the existing
constant-family section/functor interface. Postcomposing the existing whole
`section_total_postcomp_transf` by π₂ constructs U⇒V. The experiment adds
the explicit proof-time structural view π₂∘total(v) ≡ v for a section v of
a constant family. It is not a theorem derived from the old component beta
rules, and it does not change runtime functor normal forms. Its matched
section appears on the variable side; typed reflexivity exercises that
comparison successfully. Arbitrary product-valued functors do not receive it.

The existing `Op_transf` has the required reversed ordinary signature. It
therefore sends this one whole transformation to Vᵒ⇒Uᵒ, now between functors
K→Y. Both sides compute to D(x) on objects, and this transformation's
component is id at D(x). The existing strict pointwise inverse-assembly
interface then supplies fixed-forward OmegaEquivAlong evidence, retaining
both selected inverses and their whole laws. The native wrapper is guarded
by OneCat(Y); no separate OneCat(Op(Y)) input is introduced. This reuses a
declared structural inverse interface and its laws, not only beta reduction.
No pointwise naturality square is caller data, and no functor is constructed
by transporting it along an equality path. No Op declaration or rule changes.

This is an intermediate comparison, not the full target classification.
Two further whole identifications remain: Uᵒ with q∘Γ, using the Sigma
map/base-change operations, and Vᵒ with D, using the graph's retained whole
action. Recovery of h and the H comparison remain separate obligations.

From `emdash2`, reproduce the fourteen-assertion native replay:

```bash
python3 - <<'PY'
from pathlib import Path
audit = Path('audits/categorical-family-introduction-boundary')
constructor = (audit / 'constructor_fragment.lp').read_text()
marker = '// The target side is the actual action'
assert constructor.count(marker) == 1
source = (Path('emdash3_2_gray_transformation_graph.lp').read_text() + '\n' +
          constructor.split(marker, 1)[0] + '\n' +
          (audit / 'target_section_extraction.lpfragment').read_text())
Path('tmp/probes/ua4d_target_section_replay.lp').write_text(source)
PY
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4d_target_section_replay.lp
```

The fourteen assertions cover the inherited native object/source observations,
generic section-extraction components, actual D(x), the returned forward
and both inverse components, both whole inverse-law projections, and the
constant-section view with runtime/arbitrary-map negative controls. The
unchanged core already proves the section's ordinary arrow-action observation
through `piapp1_const_fapp0_eq`; that observation is not a runtime conversion.

The constant-section view also passes in a full core copy at its owning
position after `piapp1_const_fapp0_eq`. Its normalized warning inventories
agree with the baseline in all five dimensions: 157 replaceable variables,
1144 inherited critical pairs, no parser issue. This is the scope of the
owner audit, not a confluence or unrestricted higher-variance claim. The
view and the extraction definitions remain outside the positive library.

Receipts: `ua4d_target_section_replay-20260917-200815.log` (retained native
replay), `ua4d_target_section_without_view-20260917-200650.log` (expected
failure of the actual extraction declaration without the view), and
`ua4d_constant_section_owner-20260917-200428.log` (owner-position check).
The five-dimensional warning comparison is recorded in
`tmp/probes/ua4d_constant_section_warning_comparison.json`.
