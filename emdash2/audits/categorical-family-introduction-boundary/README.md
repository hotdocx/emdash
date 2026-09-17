# Whole Native Comma-Family Introduction: Partial Qualification

Status (2026-09-17, UA-4): the isolated candidate now checks constructor,
point, both arrow projections, retained triangle and next-action types.
The stronger next-Hom projection conversions and whole H comparison remain
open. No candidate rule or Γ definition is installed in the library.

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
Their final assertions, asking for conversion to A[θ] and D[θ], still fail.
Typed whole action is therefore retained; the stronger projection computation
has not been established. Nor do the whole source/target composite functors
already normalize to A and D merely because their point/arrow views do.

The next task is to expose the needed whole Hom/projection action at the
existing Sigma, base-change and section-total owners, then construct the whole
H comparison. Prefer whole owners and required projection-order joins over
a growing list of Γ-specific point rules. Keep the current candidate outside
the library while these qualification requirements remain open.

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
PY
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_projection_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_comma_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_next_source_types.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_next_target_types.lp
# Each of these two stronger conversion controls is expected to fail.
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua4_next_source_replay.lp
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

Source identity at this audit:

| Source | SHA-256 |
| --- | --- |
| `emdash3_2.lp` | `24a4aab2c1691ca6baadf2a0a5900b2f6dbaf3f6bdc242ac8a368e75f2ba4ff9` |
| `emdash3_2_cubical_square_total.lp` | `bfc4acd2767fd2d794728912722121a9da24cbc81af17ec1e6d646e02c7a1101` |
| `emdash3_2_gray_transformation_graph.lp` | `d27e975c7652a5eaa6d4fbe51b4c9547f5125317521507c3cb938f9487623a75` |
| `constructor_fragment.lp` | `336faa2ae11a1093cb4e0552c3c46017e1dad1d99de3900cf9a5f8ccd54d5db7` |
