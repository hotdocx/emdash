# Whole Identity Images Of A Hom Comparison

Date: 2026-09-18
Status: public definition owner and supporting clauses implemented; joint qualification recorded in the living ledger
Baseline before extraction promotion: `17ba33e0`

The [living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
and [assembly ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md#ua-1f--public-unitcounit-extraction-and-its-owner-clauses)
own scope and qualification. The public extraction reuses the qualified Γ machinery
to close the former whole-transformation formation gap. It is independent of
the [ordinary Adjunction introduction](../adjunction-from-hom-comparison/README.md),
which is a separate explicit structural interface over this derived data.

## Mathematical Result

For ordinary A,B, F:A→B, G:B→A and a supplied whole ProfComparison

```text
Φ : Hom_B(F−,−) ≅ Hom_A(−,G−),
```

the public owner constructs actual whole transformations

```text
η : id_A ⇒ G∘F,          ε : F∘G ⇒ id_B,
η_a = Φ_a,Fa(id_Fa),     ε_b = Φ⁻¹_Gb,b(id_Gb).
```

The given Φ and its selected inverse are retained. No componentwise naturality
or functoriality square is caller data, and no operational functor is obtained
by transporting along an equality. The two component formulas are proved
ordinary arrow equations. They are not a claim that every expanded runtime
presentation normalizes directly to the right-hand side.

The native tapp1_func action remains available. For a whole profunctor map
r:Hom_A(−,−)⇒Hom_C(P−,Q−), its reconstructed transformation α satisfies
α[f]=r_x,y(f), for arbitrary f:x→y. This equation is checked for the unit and
counit specializations too. The original comparison's native naturality and
selected inverse laws give both mate formulas and triangle laws:

```text
G[f] ∘ η_a = Φ_a,b(f),        ε_b ∘ F[g] = Φ⁻¹_a,b(g),
(ε ⋅ F) ∘ (F ⋅ η) = id_F,    (G ⋅ ε) ∘ (η ⋅ G) = id_G.
```

Here ⋅ denotes whiskering. The triangle results include whole modifications
and equations between the actual whole transformations, through the existing
ordinary modification interface. They are derived laws, not new runtime
triangle reductions. Controls reject collapsing arbitrary endomorphisms to
identities or discarding the supplied comparison. A direct normal-form
comparison for every expanded action presentation is still unqualified.
The owner does not introduce an Adjunction witness.

## Construction And New Interface Boundary

The generalized graph accepts a whole internal Hom action
Θ:Hom_X(−,−)⇒Hom_Y(P−,Q−), retaining hom_int as owner. Its object is
(P(x),Q(x),Θ_x,x(id_x)). Existing Sigma/section projection comparisons give
whole source and target comparisons to P,Q. Whiskering the existing ordinary
universal-arrow transformation along this graph and composing with those
comparisons gives P⇒Q. This is the previous Γ construction with its internal
action supplied directly, rather than first extracted from a transfor.

For η and ε, the original comparison and inverse are reindexed and composed
with Prof_func_hom(F) and Prof_func_hom(G), using the already qualified
comp_catd_fapp0 presentation. Currying these whole profunctor maps supplies
Θ. The native Hom-action conversion is defined before specializing its
endpoint functors to G∘F or F∘G; this retains the intended type through
composition normalization without another associativity rule.

Three supporting clauses now live at their semantic owners:

- Core `Hom_prof_along` owner: two proof-time comparisons between semantic
  currying of a represented profunctor and its native hom_int presentation.
  Residuals check the entire actual profunctor; unrelated data are not
  identified, and runtime heads remain distinct.
- `emdash3_2_one_cat_arrow_diagrams.lp`: one scoped identity observation at the
  existing OneCat universal-arrow transformation, after the opposite-source
  identity has normalized. It retains constructor-visible identical
  endpoints, like the existing zero-cone observation.

The whole unit/counit and all law helpers are definitions. Component proofs
stage existing evaluation/identity laws before product specialization, then
apply ordinary congruence. Their intermediate functor equations are laws;
no functor's action is defined by path transport. Ordinary guards qualify the
actual Hom-comparison consumers. General higher Op/profile semantics remain
outside this result.

Action and triangle proofs project the original displayed naturality cells
with `fdapp1_int_cell`. `hom_to_path` observes their equations only in the
discrete Homs supplied by the ordinary-category guards. Generic evaluation
and identity laws are staged before specializing to identity arrows or inverse
functors, so normalization does not erase the intermediate comparison. The
triangle proof uses the original DefIso through `defiso_fmap`; it requires no
new component-inverse rewrite. Existing `one_cat_modification` assembles the
whole law from those ordinary component proofs. This is internal derived
evidence, not an additional square obligation on users.

A rejected direct-normalization experiment added product identity/component
clauses. Its scoped version produced the expected unit normal form but 18
normalization overlaps, including identity erasure at existing category
facades. None of those three product clauses occurs in the library. The
component equations are instead derived from existing identity laws.

## Reproduction And Evidence

The public definition owner is
[emdash3_2_one_cat_hom_comparison_data.lp](../../emdash3_2_one_cat_hom_comparison_data.lp).
Its 42 definitions expose fifteen operations and keep 27 law helpers protected.
It imports the shared graph from the original represented-comma owner. The
former compressed candidate and duplicate clause fragments are retired to
Git history; normal recovery uses the active owners and public reviewers.
`manifest.json` records their exact source identities.

From emdash2:

```bash
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh examples/one_cat_hom_comparison_data.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh examples/prof_curry_hom_views.lp
```

The source checks both whole transformations, their whole action functors,
component laws, nonidentity action equations, whole triangle modifications
and equations, and noncollapse controls: sixteen assertions, with all
construction/proof bodies also checked. It uses 2GiB/90s/o20, serial execution,
and warnings/subject reduction. The imported public reviewer passes; the
owning-position and downstream warning comparisons are recorded in the ledger.

The two curry views pass in a fresh full core copy at their intended owner,
with five positive/negative controls. All five normalized warning inventories
match the prior core: 157 replaceable-variable warnings and 1140 inherited
critical pairs, no additions or parser issue. The scoped ordinary-arrow owner
also passes with the full extraction consumer and an empty warning inventory.
The thirteen affected reviewers cover mates, reindexing, family adjunctions,
Γ/H, the actual Freyd model and products. Their five warning inventories match
their predecessors after accounting for the recompiled core. The living
ledger records joint nonsplit and integrated diagnostic qualification.

The separate public constructor now connects these actual whole η/ε data
to its native projections by a derived whole comparison. Its scoped input
unifiers remain at the Hom comparison and mate projections; existing mate
formulas and ordinary modifications give η/ε agreement without another unit
unifier. Its source and import qualification is recorded in its own audit.
The product/weighted review selected no new bridge; higher terminality and
final book/audit work remain other plan rows.
