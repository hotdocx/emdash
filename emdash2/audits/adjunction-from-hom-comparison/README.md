# Adjunction From A Whole Hom Comparison: Retained Candidate

Date: 2026-09-17
Status: retained non-library alternatives; scoped input agreement, derived whole η/ε agreement and family consumption checked; public promotion pending
Base: `10bff3059d999b7f0f59caa9977ad13ea034a0d3`

The [living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
and [assembly ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md)
own scope and qualification. This directory preserves the exact uncommitted
candidate while keeping its declarations and rules out of active imports,
library registration and reviewer discovery. It is not a second adjunction
theory or a completed goal result.

`candidate.patch.gz` preserves the exact patch containing two candidate modules, two reviewers and
three import/registration edits. It introduces an ordinary-category
constructor into the existing Adjunction relation from a whole ProfComparison.
The existing Hom-comparison projection returns the supplied witness; unit and
counit components compute by applying the selected comparison/inverse to
identities. The native whole unit/counit heads remain in use. The other module
generalizes four evaluated DefIso cuts to arbitrary ProfComparison inputs,
with a real Prof_cat guard.

This is a new structural introduction principle. The existing interface does
not derive its body. Its input is mathematically sufficient for an ordinary
adjunction, but broader higher/profile claims are not established by the
tests. The earlier adjunction-usability macros instead introduce trusted
instances with declaration-backed operation agreements.

The whole-family reviewer applies the already declared postcomposition lift
to the new constructor. It checks interoperability; it does not derive that
lift or remove one of the existing structural assumptions. A production
consumer holding independently constructed whole Hom-comparison data has
not yet been identified. Promotion must justify that benefit, then complete
owner-position warning/SR, inference, audit, catalogue and health gates.

The exact uncompressed patch SHA-256 is:

```text
85ffe36f790b2a93073a714a1762e5fdb012e166a029df5d190021cd81c9362c
```

On the recorded baseline, check applicability from the Git root with:

```bash
gzip -dc emdash2/audits/adjunction-from-hom-comparison/candidate.patch.gz | git apply --check -
```

The compressed patch keeps superseded implementation text out of normal
source searches and preserves Git patch context whitespace byte-for-byte.
Applying the patch is an explicit experiment resumption, not part of normal
validation. In an authorized isolated checkout, apply it and run the two
focused reviewers through the standard guard, from `emdash2`:

```bash
env OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 scripts/probe.sh examples/prof_comparison_components.lp
env OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 scripts/probe.sh examples/one_cat_adjunction_introduction.lp
```

The last candidate runs passed at the default serial 2GiB/90s profile, with
warnings and subject reduction enabled:

- `prof_comparison_components-20260917-132520.log`;
- `one_cat_adjunction_introduction-20260917-132907.log`.

Logs remain in this worktree's ignored `emdash2/logs/probes/` directory.
No full promotion warning comparison or catalogue/health registration was
completed. The exact patch was checked both for reverse applicability before
removal and for forward applicability after removal. The active adjunction
mate owner and registrations were restored to their committed contents;
the independently qualified UA-1a core computation was retained.

## Constructor-Scoped Input Agreement Review — 2026-09-18

The user proposed making the general Φ/Γ mate operations explicit and relating
them to constructor inputs through proof-time agreement. Existing owners
already provide this vocabulary: Adjunction_hom_prof_comparison holds the
whole comparison, and adjunction_transpose_func/untranspose_func project the
two mate functors. Their transparent names expose the stable selected DefIso
projections. There is no need for parallel primitive Φ/Γ symbols.

`input-agreement.lp.gz` retains a newer, separate experiment: one ordinary
constructor from a whole ProfComparison and seven scoped unif_rules. The
whole comparison includes both selected maps and inverse laws; two arbitrary
functions without that data would not suffice. The rules relate the original
comparison, both whole maps, components and point applications to the supplied
input while retaining the canonical runtime heads. This differs from the
older patch's eager Hom-comparison rewrite and adds no runtime rule.

For J=make_adjunction(i), the primary rule is schematically
`Adjunction_hom_prof_comparison(make_adjunction($i)) ≡ $j ↪ [$i ≡ $j]`.
The residual checks the actual supplied comparison. The other rules expose
this same agreement under existing projections, not independent choices of
mate maps and not an equation for an arbitrary unrelated J.

All seventeen assertions pass with SR/warnings enabled at 2GiB/90s/o20:
`ua2e_input_agreement_final-20260918-040641.log`. They include both generic
point and whole mate inverse cuts, negative unrelated-input controls and a
concrete reflexive input whose original component agrees at proof time but
does not replace the canonical mate at runtime. Expected negative assertions
can print unsolved constraints; they do not make the check fail.

The whole-comparison rule alone does not propagate through defiso_to/from;
map-level views alone do not propagate through tapp0. Direct projected views
are necessary for this tested interface. Reconstructing their residuals with
omitted arguments triggered an installed-checker eval.ml assertion. The
selected clauses retain actual evaluation endpoints explicitly in residuals.
This is a computational/elaboration finding, not a mathematical obstruction.

The original library also fails the stronger runtime reduction of an evaluated
reflexive ProfComparison to the plain identity functor, without this constructor
or its rules (`ua2e_reflexive_component_control-20260918-040609.log`). The
selected test retains the actual supplied projection, and does not claim that
this separate identity-presentation normalization has been repaired.

From emdash2, replay with:

```bash
gzip -dc audits/adjunction-from-hom-comparison/input-agreement.lp.gz \
  > tmp/probes/ua2g_input_agreement_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua2g_input_agreement_replay.lp
```

The adjacent manifest records the current bytes and scope. The current
25-check replay imports the public extraction owner and extends the seventeen
controls above with derived whole η/ε agreement, four family mate inverse
checks and both native Došen rectangles on arbitrary off-diagonal arrows.
All eight new proof bodies check. The native identity-image laws come
from adjunction_transpose_semantic_path and its inverse counterpart. The
scoped comparison input views identify their middle terms with the original
input, and one_cat_modification assembles the whole agreement. No additional
unit/counit unifier or agreement primitive is introduced.

The direct whole-unit unifier prototype left expanded curry/Hom constraints
unresolved; the selected derivation avoids that comparison. The family test
uses the existing postcomposition lift on the newly constructed adjunction,
with arbitrary whole family arrows and both inverse cuts. It does not derive
or replace that lift. Current logs are
`ua2g_derived_whole_agreement-20260918-043040.log` and
`ua2g_whole_family_consumer-20260918-043327.log`; the native rectangle
extension passes in `ua2g_native_rectangles-20260918-043652.log`.

Public factoring and owner/import qualification remain. A unit/counit-based
constructor is a related option, not a second required implementation in this
tranche.
