# Ordinary Adjunction Introduction From A Whole Hom Comparison

Date: 2026-09-18
Status: public owner implemented; qualification receipts in the living ledger
Baseline before promotion: `90d54841`

The [living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
and [assembly ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md#ua-2h--public-adjunction-introduction-with-retained-native-heads)
own scope and qualification. Active source is
[one_cat_adjunction_introduction](../../emdash3_2_one_cat_adjunction_introduction.lp),
with the two generic identity-image laws at the existing
[adjunction-mates owner](../../emdash3_2_adjunction_mates.lp).

## Interface And Structural Boundary

For ordinary A,B, F:A→B, G:B→A and a supplied whole comparison

```text
i : Hom_B(F−,−) ≅ Hom_A(−,G−),
J = one_cat_adjunction_from_hom_comparison(A1,B1,F,G,i) : Adjunction(F,G).
```

The input is the existing ProfComparison with both selected whole maps and
inverse laws. Two arbitrary functions without this data do not suffice.
The constructor is one explicit new structural introduction into the existing
classifier; its body is not derived from the previously opaque Adjunction
interface. The ordinary guards qualify its mathematical interpretation.
No unrestricted higher/profile theorem or closed Freyd model is claimed.

The primary proof-time rule is schematically

```text
Adjunction_hom_prof_comparison(make_adjunction($i)) ≡ $j
  ↪ [ $i ≡ $j ].
```

The residual checks the supplied comparison. Six additional scoped views
expose that agreement for the two selected maps, their components and point
applications. They do not apply to an unrelated J. Actual evaluation endpoints
are retained in residuals; an omitted-RHS reconstruction experiment triggered
an installed-checker assertion and was not selected.

All seven rules are unif_rules. The canonical comparison, selected-mate and
unit/counit runtime heads remain intact. Existing whole/point mate inverse
cuts and both native Došen rectangles retain their computation. These views
do not assert runtime replacement of a canonical mate by the supplied map,
or normalize every expanded concrete projection to a plain identity functor.

## Derived Whole Unit And Counit Agreement

The public [Hom-comparison data owner](../../emdash3_2_one_cat_hom_comparison_data.lp)
constructs actual whole η and ε from i and proves their component/action and
triangle laws. The generic mate owner now proves that a native adjunction's
unit and counit components are the corresponding mate identity images.
Combining these laws through the scoped input views gives component agreement;
existing one_cat_modification then gives the two whole modifications and
ordinary equality observations. The original whole terms are retained.

There is no new unit/counit agreement primitive or whole-unit unifier. The
initial direct unifier for the expanded unit left curry/Hom constraints
unresolved; the selected proof uses native mate laws instead. No operational
functor is defined by path transport and no caller supplies naturality squares.

The constructor owner has seven derived definitions: a public input-agreement
law, two protected point proofs, two public whole modifications and two public
whole paths. The two generic
native identity-image laws remain independently usable at the mate owner.

## Consumers And Replay

The public reviewer contains thirty-three assertions. It checks input, map,
component and application agreement; non-erasure and unrelated-input controls;
both point and whole mate inverse cuts; both Došen rectangles; imported whole
unit/counit comparison proofs; and whole-family mate consumption through the
existing postcomposition lift. That lift is consumed, not derived or replaced.
No extra model-entry API is introduced.

When the supplied i is itself Adjunction_hom_prof_comparison(J), direct typed
reflexivity at the whole comparison hits injectivity decomposition before
the scoped rule. Use one_cat_adjunction_from_hom_comparison_input_path, whose
generic proof is checked before specializing i. The public controls verify
this law and both projected-map views for that input. This adds a derived
law, not an adjunction η unifier or runtime erasure rule.

From emdash2:

```bash
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh examples/one_cat_adjunction_introduction.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh examples/adjunction_mates.lp
```

The owning source checks reproduce the same five inherited mate critical
pairs in all five normalized warning inventories. An imported source check
may reuse compiled parents and therefore omit their earlier warnings; the
ledger distinguishes those cases. Expected negative assertions may print
unsolved constraints while the completed check succeeds. Additional existing
consumer imports, integrated diagnostics and proof–CAS receipts are recorded
in the ledger. `manifest.json` records current owner and reviewer identities.

## Retired Experiments

Git preserves the earlier eager comparison rewrite, four generalized inverse
cuts and compressed constructor prototypes. Those duplicate implementation
bundles are removed from the current audit after promotion. The active owner
uses the user's selected proof-time agreement design. A separate constructor
from whole unit/counit plus triangle laws remains an option, not an additional
required implementation or a new notion of adjunction.
