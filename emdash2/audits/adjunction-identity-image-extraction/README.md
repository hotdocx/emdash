# Whole Identity Images Of A Hom Comparison

Date: 2026-09-18
Status: checked extraction candidate importing the shared library graph; remaining owner clauses and extraction promotion pending
Baseline before shared-owner factoring: `06ddff1c`

The [living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
and [assembly ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md#ua-1e--share-the-hom-action-graph-at-its-existing-owner)
own scope and qualification. This candidate reuses the qualified Γ machinery
to close the former whole-transformation formation gap. It is independent of
the retained [Adjunction introduction candidate](../adjunction-from-hom-comparison/README.md),
which remains a separate structural interface and consumer decision.

## Mathematical Result

For ordinary A,B, F:A→B, G:B→A and a supplied whole ProfComparison

```text
Φ : Hom_B(F−,−) ≅ Hom_A(−,G−),
```

the candidate constructs actual whole transformations

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
The candidate does not introduce an Adjunction witness.

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

Three proposed owner clauses remain outside the library:

- `curry_hom_views.lpfragment`: two proof-time comparisons between semantic
  currying of a represented profunctor and its native hom_int presentation.
  Residuals check the entire actual profunctor; unrelated data are not
  identified, and runtime heads remain distinct.
- `arrow_identity_rule.lpfragment`: one scoped identity observation at the
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
facades. None of those three product clauses occurs in this candidate. The
component equations are instead derived from existing identity laws.

## Reproduction And Evidence

The compressed source imports the generalized graph from its existing
represented-comma owner. That shared derivation now serves both the original
Γ API and extraction; the former copied graph is preserved only in Git.
The candidate contains the extraction and law definitions, its sixteen
controls, and the three proposed owner clauses. `manifest.json` records the
exact source identity and required owner hashes.

From emdash2:

```bash
gzip -dc audits/adjunction-identity-image-extraction/candidate.lp.gz \
  > tmp/probes/ua1e_identity_image_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua1e_identity_image_replay.lp
```

The source checks both whole transformations, their whole action functors,
component laws, nonidentity action equations, whole triangle modifications
and equations, and noncollapse controls: sixteen assertions, with all
construction/proof bodies also checked. It uses 2GiB/90s/o20, serial execution,
and warnings/subject reduction. The original proof candidate and compressed
replay pass with empty warning inventories. The living ledger records logs.

The two curry views also pass in a full core copy at their intended owner,
with five positive/negative controls. All five normalized warning inventories
match the current core: 157 replaceable-variable warnings and 1140 inherited
critical pairs, no additions or parser issue. The scoped ordinary-arrow owner
also checks. These are candidate qualifications, not a positive-library or
full-repository promotion gate. The shared graph factoring passes the original
Γ/H/model consumers and integrated diagnostics; core rules and nonsplit
artifact bodies remain unchanged. The 94-assertion CAS receipt is the recorded
UA-4m run, not a newly executed aggregate in this factoring slice.

Next qualify the remaining owner clauses and public extraction interface,
retaining these component, action and triangle laws. The separate
Adjunction-constructor scope and remaining terminality/product reviews are
still open in the living plan.
