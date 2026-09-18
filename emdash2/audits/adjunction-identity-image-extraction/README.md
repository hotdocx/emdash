# Whole Identity Images Of A Hom Comparison

Date: 2026-09-18
Status: checked non-library candidate; shared-owner factoring and promotion pending
Baseline: `fef16d2f`

The [living plan](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_INVENTORY_AND_FOLLOWUP_REVIEW.md)
and [assembly ledger](../../../docs/TYPESCRIPT_EMDASH_CATEGORICAL_UNIVERSALITY_ASSEMBLY_LEDGER.md#ua-1c--revisit-hom-action-extraction-after-γ-qualification)
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

The native tapp1_func action remains available, and the controls reject
collapsing arbitrary input endomorphisms to the identity case. A direct
normal-form comparison of the recovered nonidentity action with Φ's action
is not yet qualified. The candidate does not introduce an Adjunction witness
or claim that formal triangle laws have already been derived.

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

A rejected direct-normalization experiment added product identity/component
clauses. Its scoped version produced the expected unit normal form but 18
normalization overlaps, including identity erasure at existing category
facades. None of those three product clauses occurs in this candidate. The
component equations are instead derived from existing identity laws.

## Reproduction And Evidence

The compressed source contains an isolated copy of the generalized graph
and its construction stages. It is retained outside normal source discovery
so it is not a duplicate active implementation. Public promotion must factor
that generalization with the existing Γ owner, retaining its public API and
original H consumers. `manifest.json` records the exact source identity and
baseline owner hashes.

From emdash2:

```bash
gzip -dc audits/adjunction-identity-image-extraction/candidate.lp.gz \
  > tmp/probes/ua1c_identity_image_replay.lp
OCAMLRUNPARAM=o=20 EMDASH_LAMBDAPI_WARNINGS=1 \
  scripts/probe.sh tmp/probes/ua1c_identity_image_replay.lp
```

The source checks both whole transformations, their whole action functors,
noncollapse controls and both component laws: eight assertions, with all
construction/proof bodies also checked. It uses 2GiB/90s/o20, serial execution,
and warnings/subject reduction. The original proof candidate and compressed
replay pass with empty warning inventories. The living ledger records logs.

The two curry views also pass in a full core copy at their intended owner,
with five positive/negative controls. All five normalized warning inventories
match the current core: 157 replaceable-variable warnings and 1140 inherited
critical pairs, no additions or parser issue. The scoped ordinary-arrow owner
also checks. These are candidate qualifications, not a positive-library or
full-repository promotion gate. The active library and its 94 nonsplit
Γ/H-integrated assertions remain unchanged.

Next factor the generalized graph and qualify the actual public extraction
interface, retain these component laws, and account for the required action
and triangle observations. The separate Adjunction-constructor scope and
remaining terminality/product reviews are still open in the living plan.
