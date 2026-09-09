# Strict Internal Homology Pilot

Date: 2026-09-08

Status: active whole-complex/homology redesign; structural evaluation qualified and promoted; general op repair deferred

Known limitation: [the internal-op empty-type diagnostic](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md)
is confirmed on the committed core and both reference baselines. Its general
repair is deferred. A pilot construction must have a justified mathematical
meaning without essential use of that defect; the spelling `Op_funcd` alone
is not a rejection criterion. The scoped structural evaluation tranche is
now active; the complete zero-complex/whole-homology interface is not.

Parent: [bounded long exact homology and book plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md)

Current sub-audit: [foundational variance owners and the dependent con ladder](TYPESCRIPT_EMDASH_HOMOLOGY_VARIANCE_OWNER_AUDIT.md)

Worktree: `/home/user1/emdash1-long-exact-v1`

Branch: `goal/bounded-long-exact-homology-book-v3.2`

## Decision And Scope

Latest user clarification (2026-09-08): deferring the general op/Sigma repair
does not abandon the pre-op whole-complex/homology redesign. The user linked
responses 0140, 0141 and 0142 and specifically recalled the dependent con
ladder and attempted `Op_funcd` rewrite. Recover that state and distinguish
a legitimate local opposite computation from exploitation of the known
inconsistency. Only a construction that essentially needs the invalid step
should be put aside. The broad fallback-to-component-chases wording in
`772f9d18` was an overinterpretation and is superseded by this clarification.

Accordingly, the following whole-functor-first sequencing remains current:

Following the [research review](TYPESCRIPT_EMDASH_HOMOLOGY_INTERNALIZATION_REDESIGN_REVIEW.md)
and the user's continuation/strictness clarifications, develop the bounded
whole-functor pilot before extending the remaining component-level window
exactness chases. The completed connecting-map checkpoint `b83a4d32` remains
a reference implementation, not an architecture that every new owner must
copy. The original window exactness, bounded assembly, formal-boundary audit
and book obligations remain in the parent goal.

Use the repository's ordinary primitive-head/projection/usability style when
new owners are needed. First reuse transparent semantic constructions that
already compute. General `make_cat`/`make_func`/`make_transf` record constructors
are not prerequisites. Do not introduce a second grammar of manually stored
commuting squares or reselect native kernels and homologies merely to make
endpoints convenient.

## Strict Working Profile

Use the current integrated globally strict functoriality/naturality cuts;
do not import the unrelated strictness-migration branch. The user's
`*_laxity*` clarification refers specifically to witnesses extracted from
internal hom-action:

- `functord_laxity_transf` projects `fdapp1_int_transfd` through the
  dependent-hom/self-comma identity-section ladder;
- `tapp1_post_laxity_transf` and `tapp1_pre_laxity_transf` specialize it to
  the fixed-source and fixed-target ordinary actions;
- their component projections and `fapp1_compositor` retain that same
  provenance. They are not independently supplied naturality squares.

If a pilot consumer requires these structural witnesses to compute as
identities, probe the canonical surviving projection owner and its exact
endpoints, then install the smallest justified strict computation. This
does not authorize a blanket rule erasing arbitrary directed higher cells.
Strictness also does not itself imply that every higher Hom is discrete.
An ordinary one-category specialization must state that additional boundary
if it needs it. Preserve whole action at every retained variable.

## Architecture To Qualify

For a shape I and category C, whole evaluation should supply

```text
I → Functor_cat(Functor_cat(I,C),C),     i ↦ ev_i,
u : i → j                            ↦ ev_u : ev_i ⇒ ev_j.
```

For the existing walking arrow this supplies source/target functors and
the universal differential as an actual transformation. Next qualify the
classification of concrete arrows and transformations using existing join,
Hom and displayed-family owners. A pointwise list of component formulas is
not a replacement for a whole diagram or its action.

In the strict arrow category, the intended universal pattern is

```text
J(X) = (X → 0),    J ⊣ Ker,
I(X) = (0 → X),    Coker ⊣ I.
```

Audit this against the actual universal capabilities. Current objectwise
contractible factor spaces do not by themselves constitute a whole
adjunction of arbitrary omega-categories. Either construct the appropriate
internal fibration/whole comparison, or state and justify the additional
coherent provider interface. A new functor name alone does not qualify.

On three-term complexes, use whole evaluation and differential
transformations, form cycles through the selected kernel interface, factor
the incoming differential into cycles, and apply the selected cokernel
interface. The resulting H must preserve the current native-selected
homologies or expose an explicit comparison where choices genuinely differ.
Keep public homology/long-exact operations independent of a snake-lemma
implementation detail; Posur's homology-map formulation is also a candidate.

## Ledger And Acceptance Tests

| Row | Status | Required result |
|---|---|---|
| `HINT-EVAL-1` | complete; checkpoint `e8af9cfc` | whole varying-shape evaluation, component/mixed computation and retained next Hom action |
| `HINT-ARROW-2` | whole natural-family route and terminal/initial embeddings implemented | actual eta:F⇒G yields K→Arr(C); whole observations recover F/G/eta and retained higher action; no raw mapping-category inverse claimed |
| `HINT-UNIVERSAL-3` | interface/rectangular/mate-inverse probes green; not promoted or qualified | whole kernel/cokernel interfaces with actual universal transformations, selected choices and justified capability boundary |
| `HINT-COMPLEX-4` | varying-source triangle-diagram prototype checked in part | bounded three-term complex category and whole H; identity, nonidentity composition, differential/reconstruction computation and retained higher action |
| `HINT-COMPLEX-4A` | local compatibility implemented; hybrid nonidentity edge computation recovered in scoped probes | globalize the native zero-triangle with correct flag variance and genuine chain-map Homs; do not require an ordinal/join interpretation as a prerequisite |
| `HINT-COMPLEX-4B` | fixed-pair boundary comparison implemented; zero-prism coherence open | re-present the existing chain-map factors through the derived cubical/internal-Hom owners, retaining the shared middle component and zero compatibility |
| `HINT-CONSUMER-5` | pending | original nonsplit proof-CAS example plus one formerly expensive consumer, with complete dependency/observation timings |
| `HINT-VARIANCE-6` | inventory checked; ordinary stable-owner port implemented; dependent mirror remains experimental | audit the complete internal-action/identity-section extraction ladder and the separate Op owner link; qualify the actual nonidentity edge observation |
| `HINT-SOUNDNESS-7` | general repair explicitly deferred; local non-reliance review remains | preserve the diagnostic and repair evidence; do not exploit invalid inversion/regrading in the homology construction |
| `HINT-RECOVERY-8` | pre-op state and narrow evaluation consumer recovered; owner-position qualification next | justify the native forward evaluation, qualify only the needed structural rules, then continue zero-complex/prism and whole universal/H interfaces |

This pilot does not claim a general Došen-style homology decidability theorem,
complete universal quotient effectiveness, or stable/derived/spectral theory.
If a proposed representation fails, retain the bounded probe and revise the
owner choice instead of hiding it behind opacity or a new equality axiom.

## Evaluation Result And Evidence

`emdash2/emdash3_2_diagram_evaluation.lp` defines evaluation by the existing
argument exchange applied to the identity of `Functor_cat(I,C)`. Its three
transparent definitions add no primitive, runtime rule or proof-time unifier.
The independent reviewers `examples/diagram_evaluation.lp` and
`examples/walking_arrow_diagram_evaluation.lp` check

```text
ev_i(F) → F[i],       ev_i[eta] → eta[i],
ev_u[F] → F[u],       ev_u[eta] → eta[u].
```

The mixed operation retains a whole functor and a typed next Hom action.
The walking-arrow identity diagram returns the original nonidentity
generator, and its endpoints do not collapse. These are 11 positive and
2 negative checks; they do not yet identify a strict arrow category with
the existing lax-arrow total category or supply a kernel adjunction.

The first alternative `curry(Eval ∘ swap)` formed typed definitions but
failed the desired direct object-evaluation beta in the ignored
`diagram_evaluation_family_curry.lp` probe. This is a projection/normal-form
finding, not a mathematical objection to currying. The existing direct
exchange owner already provides the needed computation, so no new curry
rule was added.

Validation logs are under `emdash2/logs/probes/`: quiet/warning evaluation
`diagram_evaluation-20260908-072107.log` / `-072111.log`, walking consumer
`walking_arrow_diagram_evaluation-20260908-072116.log` / `-072120.log`, and
the fresh recovery baseline `diagram_evaluation-20260908-073900.log`.

All three promoted source/reviewer targets also pass the ordinary scoped
`scripts/check.sh` dispatch. The exact warning inventories agree with the
core-only baseline at 1,117 critical pairs / 157 pattern reports, including
locations, term heads and rule families. All three strict rule audits have
zero clauses. The 42 focused metrics/TOC/registry/warning-parser tests pass,
as do shell syntax, catalog freshness/strict classification, source TOC,
active-reference and report-header hygiene. The source is registered in the
ordinary check/metrics lists; reviewer discovery remains automatic.

Use only scoped sources/reviewers, strict warning-inventory comparisons,
rule audits, catalog/TOC and relevant script tests. Retain the parent's
unrelated full-health exception; do not rerun repository-wide TypeScript,
Lambdapi or book aggregates for this independent helper. Local checkpoints
follow the parent authorization; no push, merge or publication is included.

## Walking-Arrow Introduction: Owner Audit

The first concrete introduction failed before any candidate rule: a constant
section selecting f:x→y was not accepted as a section of the still-rigid
`Prof_reindex(Unit_prof(C),const(x),const(y))`. A whole constant-family
normalization fixes the representation, without postulating cross data.
The broad arbitrary-profunctor version passes but also overlaps tensor and
both implications. The current consumer only needs the represented unit
case, so select that narrower rule instead of choosing runtime normal forms
for those unrelated constructions.

The same experiment found an actual ancestry-rule issue: the two
`Prof_func_hom` component/action rules required their reducible reindexed
target family literally on the LHS. The constant-family fold erased that
guard. Removing just that target guard restores the existing computation;
the final `Prof_func_hom` head still supplies the endpoint functor. The
product-base and unit-source guards remain for their previously measured
roles. The canonical already-normalized-target regression passes.

Join recursion also needed its ordinary hom-action beta on the actual
generating cross functor. The prior primitive `join_elim_cross_transf`
observation by itself does not make that ordinary action reduce. The
candidate supplies one whole-functor cut and its point-first projection
join, retaining the original supplied cross. These are constructor beta
rules, not duplicate generic functoriality. They must occur after the join's
endpoint betas for subject reduction: the earlier position failed because
the endpoint reconstruction rules had not yet been declared.

The full-owner candidate and independent consumer pass with subject
reduction enabled. Its warning boundary is 1,108/157 versus the previous
core-only 1,117/157, with no parser issues. The broad unselected experiment
was 1,123/157; neither count is a veto or proof of correctness. The selected
consumer checks whole and point-first cross computation, retained next Hom
action, the actual ordinary arrow, the normalized-target regression and
two noncollapse cases. Logs: `hint_join_arrow_unit_owner-20260908-075705.log`
and `hint_join_arrow_unit_consumer-20260908-075707.log`.

The promoted rules live at the corresponding profunctor/join positions in
`emdash2/emdash3_2.lp`. The two semantic definitions in
`emdash2/emdash3_2_walking_arrow_introduction.lp` construct the cross section
and its join recursor; no new primitive or proof-time rule is introduced.
`walking_arrow_func(f)` has the original endpoints and sends the actual
walking generator to f. The preceding evaluation transformation therefore
evaluates to f on this concrete diagram.

The active generic/introduced-arrow reviewers have 11 positive and 5 negative
checks. They include both revised `Prof_func_hom` projections with the target
already normalized, arbitrary cross data at arbitrary endpoints, whole and
point-first cross beta, the retained next Hom action, and noncollapse of
endpoints/arrows. Quiet and warning-enabled runs pass. Final warning logs:
`join_cross_computation-20260908-080301.log` and
`walking_arrow_introduction-20260908-080300.log`.

Warning classification: compared with the previous core, eleven canonical
overlap shapes disappear and two become exposed by target-guard removal.
The latter are generic transfor-naturality cuts whose syntactic unifier uses
`Prof_func_hom(Cat,Catᵒᵖ×Cat,Unit_prof(Cat))`. Its purported functor has the
source/target reversed: Unit_prof(Cat) has type `(Catᵒᵖ×Cat)→Cat`, not
`Cat→(Catᵒᵖ×Cat)`. The focused `assertnot` rejects that exact typed fragment.
These are not new well-typed computational overlaps. All 1,108 critical-pair
blocks parse, and all 157 pattern reports remain classified. This review does
not claim global confluence or use reduced totals as its correctness argument.

The central `emdash3_2_checks.lp` passes under the 90-second ceiling
(`emdash3_2_checks-20260908-080030.log`). Scoped regressions pass for directed
join, weighted profunctors, walking arrow, both evaluation reviewers, join
mapping recursion, both join compatibility reviewers and dependent-hom
laxity. The core strict audit reports zero unreviewed compound slots, with
61 annotated slots in 38 intentional clauses; the new source/reviewers
have no rules of their own. Catalog/TOC, script tests and document hygiene
are refreshed at the checkpoint. No unrelated aggregate or book render is
run, and the parent full-health exception remains explicit.

This completes the concrete introduction substep, not `HINT-ARROW-2` as a
whole. The next experiment must vary the supplied cross/arrow internally,
then qualify zero-arrow embeddings and the actual universal interface.
Neither the existing propositional join mapping comparisons nor these
pointwise introductions alone establish a whole mapping-category inverse.

## Naturally Varying Arrow Families: Construction And Qualification

For an actual transformation eta:F⇒G with F,G:K→C, apply the new walking
arrow introduction in the category `Functor_cat(K,C)`, then use argument
exchange. This constructs a whole functor K→Functor_cat([1],C) whose two
components are F and G and whose mixed generator action is eta[p]. The
input is one existing transformation, not a collection of manual squares.
This is the useful whole-family interface for universal constructions; it
does not require first constructing a general inverse from raw arrow data.

The first six component/mixed-action checks pass without new rules. The
whole identity check then exposes a projection-order gap: `sym_func`'s
fapp1 head reduces to `sym_tapp1_fapp0_transf` before generic identity matching.
The candidate adds identity/composition joins only at that existing stable
projection. Its eight checks pass, including composition on arbitrary base
arrows. The composition rule needs the `Functor_cat(A,C)` ambient-category
guard for subject reduction; all remaining inferred endpoint slots stay
variable or wildcard. The owner-position and promotion evidence is recorded
below.

The first universal consumer is the existing terminal-arrow transfor
id_C⇒const_t, giving the whole embedding X↦(X→t). The dual uses a supplied
TerminalObject(Cᵒᵖ,t) via Op_transf. This does not silently derive a whole
dual terminal structure from AdditiveCategory's currently objectwise initial
Hom contractibility; the coherent provider boundary must remain explicit.

Whole observations use exchange in the reverse direction: for D:K→(I→C),
the i-component is `sym(D)[i]` and a shape arrow is `sym(D)[u]`. Double
exchange then returns F, G and eta themselves for the introduced family,
not just their object components. The successful whole-evaluation raw
composition probe is retained as an alternative, but is not needed as an
additional runtime owner when observations use this uniform exchange form.

The initial-arrow consumer also exposes the missing capped instance of the
already existing whole `tapp1_func(Op_transf(...))` rule. Its minimal direct
projection join computes the mixed dual terminal action. A transparent
initial component alias states its type as Hom_C(t,x), avoiding the measured
opposite-endpoint inference false negative without an equality bridge,
opaque operation or new primitive. Full owner-position qualification of
double exchange and this opposite projection passes. Four preprojected
exchange rungs also join the alternate normalization order: their results
remain whole functors or original whole transformations. No pointwise
extensionality assumption is used.

The promoted owners are `diagram_family_at_func` and
`diagram_family_transf` in `emdash3_2_diagram_evaluation.lp`,
`transf_arrow_diagram_func` in `emdash3_2_arrow_diagram_families.lp`, and the
four terminal/initial definitions in `emdash3_2_zero_arrow_diagrams.lp`.
The whole observations compute as

```text
source(D_eta) → F,   target(D_eta) → G,   differential(D_eta) → eta.
```

Their full fapp1/tapp1 functors and the next Hom action recover those of the
original F/eta. On parameter arrows, the diagram transformation has source
F[p], target G[p] and mixed action eta[p]. This realizes internally natural
arrow families without first defining a new category of raw square records.
The zero embeddings then have whole source/target/differential observations
id/const_t/terminal_arrow_transf and const_t/id/initial_arrow_transf.

The core adds eight rules: the direct opposite tapp1 projection, exchanged
action identity/composition joins, double exchange, and its four already-
projected whole rungs. No new primitive or unifier is added. The generic
identity rule retains the same base category and object in its identity
argument; a merely wildcard-headed identity of an unrelated category is not
the intended discriminator.

Warning audit at the full owner gives 1,119/157 against 1,108/157. The eleven
additional reports are two product-projection/opposite-action orders, four
identity-normalization orders (Path, terminal, product and opposite), and
five nested/double-exchange orders. Both ordinary opposite projection routes
and both double-exchange whole/projection routes have typed positive checks.
The specialized product/opposite and canonical-unit cases are recorded
normal-form interactions, not evidence of subject-reduction failure or a
global confluence claim. Do not present the generic identity test as an
exhaustive audit of all already-reduced identity constructors; use the
existing generic law views when a later consumer needs those comparisons,
and add a narrow join at a measured consumer rather than broad identity eta.

The native-C typed alias at the dual component and an analogous reviewer
annotation avoid premature inferred comparison of opposite Hom wrappers.
The kernel's Hom alias is marked injective as an inference aid; these
annotations preserve the same reducible body and are not opaque seals or
propositional bridges. General Hom-inference policy is not migrated here.

The next row constructs or qualifies the whole kernel/cokernel universal
interface over these actual embeddings. It must still distinguish existing
objectwise contractible factors from a whole adjunction capability and retain
the native-selected objects. The current tranche does not declare that
adjunction, a complex category, a homology functor, or completed exactness.

The three promoted reviewers have 39 positive and 4 negative checks. Their
warning-enabled logs are `arrow_diagram_families-20260908-084626.log`,
`diagram_exchange_computation-20260908-084631.log` and
`zero_arrow_diagrams-20260908-084637.log`. The first two retain the exact
core 1,119/157 inventory. The zero-arrow module imports terminal objects;
its 1,126/159 inventory exactly equals the fresh terminal-object dependency
check `terminal_objects-20260908-085118.log`, including locations, heads and
families. No unclassified parser block is accepted.

The central diagnostic passes (`emdash3_2_checks-20260908-084437.log`), as
do the selected evaluation, walking-arrow, join-cross, dependent-hom-laxity
and terminal reviewers. The seven strict audits pass; the core has 62
annotated slots in 39 intentional clauses and zero unreviewed candidates.
The 42 focused metrics/TOC/registry/warning tests, shell syntax, catalog/TOC,
active references and report headers pass. The two new sources use ordinary
bounded dispatch; no new cache or special checking runner is introduced.
The existing full-health exception and the parent window-exactness,
bounded-assembly, formal-audit and book obligations remain unchanged.

The final exact-source quiet pass checks both new modules and all three
reviewers independently: `emdash3_2_arrow_diagram_families-20260908-085346.log`,
`emdash3_2_zero_arrow_diagrams-20260908-085350.log`,
`arrow_diagram_families-20260908-085354.log`,
`diagram_exchange_computation-20260908-085358.log` and
`zero_arrow_diagrams-20260908-085404.log`. All finish within the uniform
90-second per-target bound. No repository-wide aggregate or book render is
run for this tranche.

## Whole Universal Interface: Candidate And Probe Evidence

The candidate interface indexes the existing Adjunction notion by the actual
zero-arrow embeddings and explicitly supplied whole kernel/cokernel
functors. A selected zero object is a transparent pair of the existing
terminal structures in C and Cᵒᵖ. No opaque witness asserting that every
old PreAbelianCategory already supplies these whole adjunctions is allowed.
The old factor-space capabilities remain the reference semantics; a
choice-preserving adapter/qualification is a separate required substep.

First construct the whole kernel inclusion by applying domain evaluation to
the counit of J⊣K, and the whole cokernel projection by applying codomain
evaluation to the unit of Q⊣I. Their intended endpoints are K⇒domain and
codomain⇒Q. This creates a concrete consumer for the earlier whole
evaluation-after-exchange beta probe: domain∘J and codomain∘I must compute
as whole identity functors, not merely agree at isolated objects.

Then expose the actual whole mate functors from the existing unit/counit
and functor action, and test both ordinary inverse cuts and the nonidentity
Došen rectangular cuts after all zero-embedding projections. Use duplicated
instances only when a measured projection erases the generic triangle
pattern. A checked capability interface by itself is not qualification of
the native selected algorithms or a completed homology functor.

The whole inclusion/projection declarations and all four point/mixed
observations now pass in `hint_internal_kernel_interface.lp` and
`hint_internal_kernel_components.lp`. The latter log is
`hint_internal_kernel_components-20260908-093315.log`. Kernel-left and
cokernel-right rectangular cuts initially failed because exchange had erased
the generic fapp1 pattern. Two exchange-specific instances make all four
kernel/cokernel rectangles pass in the `*_rectangular_*_joined.lp` probes
(logs dated 20260908-092509 and 20260908-092515). Their image-object guards
are genuine cut discriminators, not redundant inferred endpoint expressions.

Literal whole mate formulas built from product composition compute their
applications, but inverse application fails
(`hint_adjunction_semantic_mates_inverse-20260908-093137.log`). The existing
Adjunction_hom_prof_comparison can instead supply both whole mate functors
through DefIso and fibre evaluation: no new primitive mate heads are needed.
A direct Prof_cat/Functor_cat proof-time comparison is needed because the
existing Prof→Catd and Catd→Functor comparisons are not transitively applied.
Both whole and point inverse cuts now pass in
`hint_adjunction_fibre_mate_inverse_captured-20260908-100717.log`.

The failed whole inverse attempts reconstructed an endpoint Hom category on
the RHS. Capturing the actual common category as a variable in the composition
pattern and returning its identity fixes subject reduction without additional
compound LHS guards. The first two point rules had already passed; the source
location identifies the failure in the third, whole-composition rule.
These remain ignored probes: owner-position warning audits, explicit
unit/counit semantic usability links and choice-preserving qualification are
not complete. No candidate rule or kernel/cokernel capability has been
promoted beyond implementation checkpoint `c7eabd58`.

## User Review: Native Zero-Triangles As The Complex Candidate

The user's dependent-hom/simplicial suggestion is directly supported by the
active native simplex owners. No category of complexes has yet been declared,
and no decision to represent complexes by functors out of iterated joins has
been implemented. The walking arrow currently supports single-arrow families
and the candidate adjunction interface; it need not define complex syntax.

For A─dNext→B─d→D, take E=Hom_C(A,−). A dependent arrow over d from dNext to
the selected zero A→D is the native triangle

```text
E[d](dNext) → 0,
```

with the readable source d∘dNext. Equivalently, fix the initial edge
e01=(B,dNext) in PathOut_C(A) and use an object of
PathOut_(PathOut_C(A))(e01) whose long edge is (D,0).
`DependentTriangle_catd`, `DependentTriangle_cat`,
`DependentSimplex2_cat` and `dependent_simplex2_visible` already implement
this local structure through homd_/Sigma; they are not an interpretation
through an ordinal join. Their own header explicitly leaves the whole
comparison with ordinal-functor categories unproved.

The scoped compatibility probe `hint_chain_pair_native_zero_triangle.lp`
passes (`hint_chain_pair_native_zero_triangle-20260908-101929.log`). It uses
the existing chain-zero path to form the native cell, and three projections
recover the original third object, zero long edge and second differential.
The first differential remains in the fixed flag. No rule, primitive,
replacement homology or manual square field is added by this probe.

Important remaining architecture checks:

1. The current native tower is flagged, not a global category of all
   three-term complexes. Internalize the varying initial vertex/edge with
   correct variance. A Hom in a fixed-flag triangle category is not
   automatically an arbitrary chain map between three independently varying
   terms; the resulting Hom must recover all three components and their
   compatibility through the internal Hom/fibration machinery.
2. A directed cell d∘dNext⇒0 is not automatically the old equality-valued
   chain condition in a general higher category. Preserve the strict or
   equality-valued zero fibre appropriate to the ordinary CAS models.
   Structural laxity normalization does not itself impose d∘dNext=0. The
   finite-free/Freyd Hom categories are actual Path categories of their
   matrix/quotient sets; this is the relevant concrete specialization.
3. The local bridge above is one direction, not yet a whole equivalence of
   complex categories or a global homology functor. Its use of the old zero
   proof is compatibility evidence, not a decision to store an additional
   path field in the final native presentation.
4. Compare direct hom/fibration or pullback-of-zero constructions of cycles
   with the candidate J⊣K presentation. Do not make a full walking/ordinal
   mapping-category inverse a prerequisite unless the chosen consumer needs
   it. Preserve the selected native kernels, boundaries and homologies.

The next architectural audit therefore tests the native zero-triangle route
before promoting further representation-specific prerequisites. This is not
a decision to exclude shape-indexed diagrams. It reorders the pilot, not
the full goal: generic window exactness, bounded assembly, formal-boundary
qualification and final book/consolidation work remain required.

## Complementary Shapes, Cells And Cubical Maps

The user's further clarification concerns reuse of the whole foundational
architecture, not replacement of shape categories by cells. The longer and
shorter appendices of `emdash2/tmp/EMAIL.md` have both been reviewed at their
cubical and simplicial passages. Their account agrees with the active
`emdash3_2_cubical_internalization.lp` and native simplex sources:

| Resource | Homological role to investigate | Verified starting point |
|---|---|---|
| combinatorial simplex/ordinal categories and face codes | diagram shapes, indexing and composition/substitution | existing shape constructors and scoped realization interfaces |
| native homd_/Sigma/PathOut simplicial cells | local zero-triangles, differentials and higher coherent data | existing triangle/tetrahedron owners; the chain-zero compatibility probe passes |
| cubical structure derived from nested simplicial structure | varying endpoints, chain maps and their coherences | homdc_int and LaxArrow reuse ordinary homd_int after Sigma/opposite variance adjustment |

In particular, homdc_int is homd_int applied to the appropriate opposite
edge family. Its Sigma-Hom projection computes
alpha:b∘u⇒v∘a. A chosen alpha is genuine cell data; what is absent is an
independent square former or a separately postulated commutativity law.
The complex-map investigation should reuse this same mechanism. A useful
next bounded comparison translates the existing two chain-map factor points
into the two corresponding derived squares, with their common middle map
retained once, before claiming a global category of complex maps.

Compare candidate presentations on the same three-term data, nonidentity
chain maps and original nonsplit proof-CAS selections. Require whole actions,
the correct strict/equality-valued zero condition, actual computations and
honest capability boundaries. A local shape/native comparison can be enough;
do not assume or require a global all-dimensional equivalence without a
consumer. Conversely, do not discard the shape route merely because the
first native point probe is simpler.

Keep the current committed implementation and all ignored alternative probes
as review/backtracking evidence. Failed candidates remain classified by their
actual failure (typing, projection matching, inverse computation or scope),
not erased or rejected merely for warning totals. Any later consolidation
must explain which parts are reused, replaced or retained as reference.

## Native Compatibility Implementation: Zero-Triangles And Map Boundaries

The next bounded slice promotes three rule-free modules:

- `emdash2/emdash3_2_hom_factor_cubical.lp`: pre/postcomposition factor
  points become arrows of the existing derived `LaxArrow_cat`; both
  fixed-boundary comparisons are also whole functors from the corresponding
  Path category, using the existing `path_lift_func`.
- `emdash2/emdash3_2_chain_pair_cubical_maps.lp`: the two original factor
  points of a `ComputationalChainPairMap` give the upper and lower native
  squares. A whole fixed-source/target-pair functor returns both boundary
  squares together.
- `emdash2/emdash3_2_chain_pair_native_triangles.lp`: the original chain pair
  becomes a native dependent zero-triangle. The initial vertex and first
  differential are retained in the flag; its visible projections retain
  the third vertex, zero long edge, second differential and original filler.

For a map from A₀─e₀→B₀─d₀→D₀ to A₁─e₁→B₁─d₁→D₁, write its original
components as a, b and c. The native boundary squares have cells

```text
upper: b ∘ e₀ ⇒ e₁ ∘ a,
lower: c ∘ d₀ ⇒ d₁ ∘ b.
```

The upper factor originally reconstructs e₁∘a=b∘e₀, so its path is
symmetrized before applying `path_to_hom`. The lower factor already has the
native orientation. No additional equation or filler is supplied. The cell
type is the existing Sigma-Hom projection of `homdc_int`, itself derived
from `homd_int`; these aliases do not postulate another square theory.
Both endpoint functors act computationally: upper gives a/b, lower gives
b/c. In particular, the middle components agree by reduction, not by a newly
stored gluing equality.

All eight new symbols are transparent definitions. No rewrite or unification
rule, stable primitive, opaque proof, reselected universal object or new
strictness assumption is added. Whole comparison functors retain the next
hom action instead of ending at their point formulas. The source of these
whole comparisons is the Path category of the old equality-valued factor
or map space; this does not invent arbitrary directed chain-map variations.

Boundaries remain explicit:

1. The paired-square target is a product of two native Homs. Its constructed
   image shares b, but an arbitrary pair in that product need not share a
   middle map. It is a boundary view, not `Complex_cat`.
2. The native zero-triangle is a fixed-flag compatibility image, not a global
   category of all three-term complexes. An arbitrary directed zero filler
   is not silently converted into the old equality-valued chain law.
3. The two squares do not by themselves supply the coherent prism between
   the two zero-triangles. The source and target retain their original zero
   witnesses separately. That coherence and flag globalization are the next
   architecture checks, not completed consequences of this tranche.
4. There is no claimed inverse/equivalence, homology functor, new exactness
   theorem or fresh qualification of native CAS providers in this slice.
   The original selected providers, connecting map and full-goal obligations
   are unchanged.

The reviewers `hom_factor_cubical.lp`, `chain_pair_cubical_maps.lp` and
`chain_pair_native_triangles.lp` contain 22 positive and two negative checks.
They test both retained cells and side actions, whole-to-point computation,
further whole hom action, the shared middle map, all visible zero-triangle
projections, noncollapse of distinct middle maps and rejection of a wrong
initial differential flag. Their first promoted quiet logs are
`hom_factor_cubical-20260908-110403.log`,
`chain_pair_cubical_maps-20260908-110405.log`, and
`chain_pair_native_triangles-20260908-110406.log`.

The exact dependency-union warning baseline and candidate inventories agree
in categories, source locations, term heads, rule families and parser issues:
1,243 critical-pair reports / 169 pattern reports. This is the combined
homological/native-simplex/cubical import boundary, not a change to the
core-only 1,119/157 boundary. Baseline log:
`hint_chain_pair_internalization_warning_baseline-20260908-110329.log`;
candidate log:
`hint_chain_pair_internalization_warning_candidate-20260908-110331.log`.
The candidate adds no new rule interactions. Preserve the earlier ignored
raw-data triangle and mate experiments as comparison evidence.

The promoted-owner union repeats that exact inventory in
`hint_chain_pair_internalization_warning_active-20260908-110809.log`.
All three source modules and all three reviewers pass the ordinary scoped
`scripts/check.sh` dispatch, with the unchanged 90-second bound per target.
All six strict rule audits report zero clauses. The 42 focused metrics,
source-TOC, registry and warning-parser tests pass; their printed timeout
messages are expected mocked failure cases, not live Lambdapi timeouts.
Catalog freshness/strict classification, source TOC, active-reference lint,
report-header lint, shell syntax and exact-diff hygiene also pass.
Sources are registered in both ordinary check/metrics lists; reviewer
discovery remains automatic. No broad TypeScript/kernel/book aggregate or
full health refresh is run; the parent scoped-validation exception remains
explicit, with no claim of a refreshed repository-wide health snapshot.

## Additional Cubical Reference Branch

The user identifies `goal/opaque-action-profile-classifiers-v3.2` and its
ancestors as additional cubical reference development, and authorizes
selective cherry-picking if a concrete consumer needs it. The observed tip
on 2026-09-08 is `114dc19fdee4b952f1c75be4e2000d6ff7195741`; this is a
reference snapshot, not a requested merge or reset target.

Do not merge the parallel branch or import its repository-wide migration
away from global strictness as part of this pilot. The current native
compatibility implementation needs no cherry-pick. For a later missing
cubical owner, first inspect the exact source/history and dependency closure,
separate the owner from profile-migration prerequisites, probe it against
this branch's actual strict working profile, and audit the focused
computations, subject reduction, warnings and noncollapse cases before
importing a bounded reviewed change. Record selected commit(s) and any
adaptation; keep unrelated parallel work untouched.

Read-only review at that snapshot inspected the full sources of
`emdash3_2_path_cubical_square_comparison.lp`,
`emdash3_2_path_cubical_structured_native_low_dimensions.lp` and
`emdash3_2_path_cubical_face_naturality.lp`. The first converts native path
squares to equality of path-edge objects and retains whole equality action
on the native Hom's path core. The second supplies low-dimensional
structured/native decoders, with a further readback capability explicit at
dimension three. The third proves inherited-face comparisons for a selected
native path cube. These are useful groupoidal references, not an already
available category of general directed three-term complexes. No files or
commits from the parallel branch have been imported.

The local compatibility tranche is checkpoint `febf287d`. Its next audit
must distinguish a genuinely varying native family from a raw function on
objects or a Path lift of such a function. The current
`PathOut_cat_func(C):Cᵒᵖ→Cat` is already a whole source-indexed family.
An arrow in `PathOut_C(A)` is the required local triangle, and maps between
such arrows suggest the existing derived lax-arrow construction. However,
the current `CubicalArrow_func(F,P)` takes a supplied functor and its
pseudofunctor evidence; it is not a declared whole endofunctor `Cat→Cat`
that can simply be composed with `PathOut_cat_func`. This is an interface
observation, not a failed probe or impossibility result.

Before adopting that candidate, qualify coherent reindexing of the arrow
family, its source/opposite variance, the zero-long-edge restriction and the
resulting prismatic Hom. Compare with the whole shape-diagram route on the
same original chain data. Do not replace a missing whole varying family by
a Path lift that retains only equality variation of the flags, or silently
treat strict structural naturality as discreteness of every ambient Hom.

## Varying Triangle Prototype And Dependent Variance Review

The next experiment combines the complementary shape and native routes:
the inner walking-arrow diagram lives in the already native
`PathOut_C(A)`, while `Functor_catd` internalizes its variation in A.
The total is `Op(Σ A:Cᵒᵖ, Op(Functor([1],PathOut_C(A))))`. It uses
existing mixed family, displayed evaluation, Sigma and Op owners and
requires no whole `CubicalArrow:Cat→Cat` operation.

`hint_triangle_diagram_family.lp` contains the prototype. A native triangle
is introduced through the checked walking-arrow recursor. A total map is a
base arrow a:A₀→A₁ and an actual natural transformation
T₀⇒PathOut(a)∘T₁, not a manually supplied collection of square equations.
Whole source, edge and other-vertex observations are typed. Nine runtime
checks pass in `hint_triangle_diagram_family_checks-20260908-112410.log`:
the three vertices, two outgoing edges, native triangle generator,
nonidentity initial-vertex action and both retained map fields.

The other edge action has a typed but noncomputing displayed-evaluation
projection. Its exact retained term and the unsuccessful direct rule probes
are recorded in the [variance audit](TYPESCRIPT_EMDASH_HOMOLOGY_VARIANCE_OWNER_AUDIT.md).
The all-wildcard and partially guarded attempts fail subject reduction; no
candidate rule is promoted and no warning threshold has been used as a veto.
The explicit goal remains to make this nonidentity action compute, not to
qualify the construction merely because its object formulas pass.

The user's con-owner and laxity-ladder suggestions now govern the next
sub-audit. Ordinary `hom_con_int` action and pre/right laxity already exist.
The dependent named mirror is absent. A correctly covariant reversed-Hom
family and a fixed-p native-typed opposite-action alias both pass scoped
probes; neither yet supplies the complete dependent internalization or a
stable runtime head. Audit the whole homd/action/identity-section ladder,
including higher transfor directions, instead of adding an isolated capped
mirror. Keep the separate `Op_catd_func`/`Op_funcd` action-link finding visible.

All current triangle and variance additions in this slice remain ignored
probes. Active implementation remains `febf287d`; existing dependent-Hom
laxity regression passes in `dependent_hom_laxity-20260908-114029.log`.
No parallel branch is imported and no new mathematical axiom or primitive
has been added. The generic window exactness proofs, bounded assembly,
provider qualification and final book update remain required by the parent.

The user's later specific import request identifies the next reusable slice:
`20c6dd2e8a7d939bf7f2b25a6578e5c072c6ccb3` stabilizes the four ordinary
contravariant internal-action/fixed-target heads, with runtime projections
and proof-time opposite comparisons. Port only that nucleus change and its
applicable checks after a full-owner probe against the present kernel.
Do not import the commit's gray-profile classifier changes, migrated
strictness rules, generated health snapshot or unrelated prose. Record the
selective provenance and this branch's own warning/regression evidence.

The selective port is now active: four ordinary con heads retain their
existing signatures, with six runtime projection/identity rules and four
proof-time opposite comparisons. No gray-profile classifier, ambient
strictness rule, parallel book artifact or foreign health snapshot is
imported. The two identity-category slots are additionally wildcarded after
a full-owner subject-reduction probe and a neutral-product control confirm
a real false negative with the original reducible guards.

The [variance audit](TYPESCRIPT_EMDASH_HOMOLOGY_VARIANCE_OWNER_AUDIT.md)
records exact provenance, the 17 positive/two negative owner tests, current
1,125/157 warning boundary and its six classified identity-normalization
reports, unchanged strict LHS audit, and the pre-existing fully expanded
product-identity limitation. The new ordinary mirror does not by itself
solve the separate Op_catd action-link or dependent evaluation projection;
both pending probes were rerun and retain their documented outcomes.

## Structural-Action Alternative And Orientation Audit

The next bounded experiment checks the actual opposite-evaluation consumer
before assuming that a new dependent con primitive is necessary. The retained
term contains composition of displayed functors, pointwise opposite,
displayed pairing, identity, and a constant argument. The ignored
`hint_displayed_action_composition.lp`,
`hint_displayed_evaluation_covariant.lp`,
`hint_displayed_evaluation_op_native_rhs.lp`,
`hint_displayed_pair_action.lp` and
`hint_displayed_identity_constant_action.lp` supply candidate projections
through those existing operators. No new primitive or independent laxity
witness is introduced. These rules are not yet promoted.

The displayed-evaluation result must retain its native opposite Hom
endpoints when the RHS is inferred. Reconstructing the same map immediately
as an ordinary mixed Eval hom action produces unsatisfiable unification
constraints; expressing it through the existing `Op_func` hom action passes
subject reduction and subsequently reduces by the ordinary Eval rules.
The fixed argument now uses the existing stable `section_weaken_funcd`,
rather than rebuilding its terminal-source composition. Only an explicitly
constant weakened section is collapsed; arbitrary sections and directed
laxity cells are not.

The actual nonidentity triangle action then reduces to `(a,eta[i])`. The
remaining conversion failure was in hidden metadata: its target diagram was
the canonical `Hom_fapp0(id,PathOut(a),T1)` owner while the original prototype
annotated eta with raw `PathOut(a)∘T1`. The canonical prototype now retains
the actual `Functor_catd` reindexing in its arrow constructor. Runtime edge
action and a typed reflexivity comparison with raw composition both pass in
`hint_triangle_structural_action_canonical-20260908-130513.log`.
No global Hom-to-composition rewrite was introduced to make this pass.
The earlier raw-annotation and whole-body-matcher probes remain available
as diagnostic/backtracking evidence.

The user's orientation requirement is explicit. The new decomposition
candidates concern a composite displayed **operator** GG∘FF and mirror the
existing hom action of a composite ordinary functor. They do not reverse the
existing accumulation rule for composition of mapped **arrows**. The focused
orientation reviewer passes unchanged arrow-action accumulation, equality of
two-stage Sigma action with action of the composite displayed functor,
associativity of the whole fixed-p hom action, and agreement between whole
and capped composite projections. Log:
`hint_displayed_action_orientation_checks-20260908-130957.log`.

These positive tests are not a global confluence or termination proof.
Warning classification, transported-identity/projection-order joins, full
owner-position qualification and relevant regressions remain promotion
gates. The correctly varianced native `homd_con_` and fixed-p con alias remain
separate interface evidence; a full dependent mirror is not silently
identified with pointwise opposite. The full long-exact goal is unchanged.

The broad structural probe reports 1,190 critical pairs / 186 pattern
diagnostics, versus the committed 1,125/157 boundary. Most added families
involve the three unrestricted composition recognizers. A more targeted
leading-Eval composition probe passes subject reduction, but its integrated
qualification was not completed before the soundness finding. The attempted
generic mapped-operator control fails while inferring the comparison's type;
it is not presented as a verified conversion counterexample. All these
alternatives remain ignored probes, not selected new kernel orientations.

The subsequent audit of whole `op` confirms a more fundamental defect,
independently of these candidate rules. The tracked non-library reproducer
and baseline controls are in the
[internal-op diagnostic](TYPESCRIPT_EMDASH_INTERNAL_OP_VARIANCE_DIAGNOSTIC.md).
The same source-level construction yields `τ Empty_grpd` in the current core,
the original main baseline and the separate post-migration tip. This changes
the earlier priority to variance repair. The user's subsequent deferral and
pre-op recovery clarification supersede that priority. Continue the whole
homology pilot through justified local operations; do not certify a candidate
by exploiting the defect. The hybrid construction remains a candidate whose
concrete evaluation instance is now recovered below, not a settled whole
complex category. Keep all prior checkpoints, code, CAS results and probes.

## Recovery Of The Pre-Op Milestone

The 2026-09-08 recovery reads responses 0140, 0141 and 0142 and the complete
current versions of this pilot, the variance-owner audit, the homology-
internalization redesign review, the bounded long-exact owner audit and the
master long-exact/book plan. The recovered sequence is:

1. `febf287d`/`b3144f40`: native zero-triangle compatibility and both derived
   chain-map squares; whole fixed-pair comparisons retain higher action.
2. `6fc0b02e`: selective port of the four ordinary con heads from `20c6dd2e`,
   including the inferred identity-slot correction; no parallel strictness
   migration and no complete dependent con mirror.
3. Varying triangle-diagram prototype: actual natural transformations supply
   the map/prism data, rather than manual square records. The retained edge
   action reaches `fdapp1_int_hom_fapp0(Op_funcd(eval_i), …, eta)`.
4. Structural-action probes: after canonical reindexing annotations, the
   nonidentity action computes to `(a, eta[i])`. Broad composition rules
   were a preliminary route; a leading-Eval-only route was not yet fully
   integrated when the independent op diagnostic intervened.

The concrete intended mathematics is

```text
eta : T0 ⇒ G ∘ T1
q : j → i
evaluation(eta,q) : T0[j] → G(T1[i])
evaluation(eta,id_i) = eta[i].
```

This uses ordinary evaluation, not an inverse to eta. The new independent
[`homology_triangle_eval_native_semantics.lp`](../emdash2/audits/homology_triangle_eval_native_semantics.lp)
derives the whole functor from `Eval_fapp1_func`, with G an arbitrary actual
functor. Four positive assertions, a wrong-direction negative and a further
whole Hom-action query pass. Neither op, Op_funcd, homd nor a new rule or
unifier is used to obtain that native result. This does not require every
selected implementation to be syntactically Op-free; it checks the meaning
of this particular instance independently of the dubious universe action.

The recovered rule candidate is
[`homology_triangle_eval_rules_prototype.lp`](../emdash2/audits/homology_triangle_eval_rules_prototype.lp).
Its 21 rules retain whole and point projections for leading evaluation,
displayed pairing, identity and an explicitly constant weakened argument.
It does not include the earlier unrestricted `Op_funcd(GG∘FF)` fold or the
two arbitrary-composite displayed-action expansions. The dedicated
[`recovery consumer`](../emdash2/audits/homology_triangle_eval_recovery_consumer.lp)
preserves the original source-indexed PathOut/diagram construction and now
computes the actual nonidentity edge to `(a,eta[i])`. Both it and the
independent native reviewer pass at the final tracked names in
`homology_triangle_eval_recovery_consumer-20260908-194831.log` and
`homology_triangle_eval_native_semantics-20260908-194831.log`.

The ignored broad pre-op consumer was also reproduced unchanged in
`hint_triangle_structural_action_canonical-20260908-193303.log`.
The narrowed consumer passes in
`hint_triangle_narrow_eval_consumer-20260908-193524.log`. Its rule-only
warning run (`hint_triangle_narrow_eval_rules-20260908-193658.log`) reports
1,138 critical pairs / 186 pattern reports versus the imported 1,125/157
core. All 1,138 pair structures parse. This is append-only diagnostic
evidence, not a complete owner-position warning/joining audit. The advisory
LHS scan finds no unreviewed tracked generic slots, but manual review of the
dependent-action and nested constructor positions remains required.

The first owning-position copy now also passes the complete nucleus source
check with the rules immediately after the existing section-weakening
projections (`hint_triangle_eval_owner_core-20260908-195941.log`). Its
strictly parsed warning counts remain 1,138/186, and the full-core LHS audit
retains 62 annotated slots / 39 clauses with no unreviewed generic slots.
The exact fresh package `/tmp/emdash-homology-eval-owner.eck6Hh` compiles that
core and checks both native semantics and the recovered nonidentity
consumer, with the latter importing the modified core rather than the
append-only prototype. Both pass. This qualifies the first producer/consumer
placement, not yet the remaining rule-hygiene, projection-order and
regression requirements or active-kernel promotion.

Recovery execution sequence (item 1 is completed by the qualification below):

1. Complete the narrow rules' owning-position qualification after the
   displayed weakening/evaluation declarations. Audit unused and reducible
   inferred slots, subject reduction, both projection orders, retained whole
   action and the existing arrow-composition accumulation orientation.
2. Do not infer a general inverse to an arbitrary laxity cell from the
   fixed-p con alias. If a broader dependent mirror becomes necessary, give
   its native variance and actual coherence/strictness assumptions explicitly.
   A new con name alone is not the current missing computation.
3. Continue the zero-long-edge restriction and the genuine coherent maps
   between varying triangles. Keep native cells and diagram shapes as
   complementary options. A successful point computation does not complete
   the zero-prism or whole complex-category interface.
4. Qualify the kernel/cokernel whole universal interfaces and their agreement
   with the original selected operations, then assemble whole homology and
   test a nonsplit proof-CAS consumer. Do not silently turn objectwise
   contractible factors into an arbitrary-omega whole adjunction, or treat
   set-valued Obj(Hom) as discreteness of every higher Hom.

The five rule-free zero-map proofs in the ignored
`kernel_cokernel_maps_of_zero.lp` and `homology_maps_of_zero.lp` are retained
as auxiliary reference work. Their final probes pass in
`kernel_cokernel_maps_of_zero-20260908-190207.log` and
`homology_maps_of_zero-20260908-190645.log`. They are not promoted and do not
replace this whole-functor milestone. General op repair remains deferred;
all of its checkpoints, source candidates and replay scripts are preserved.

## Qualified Structural Evaluation Tranche

The active nucleus now includes 31 runtime instances at the existing
displayed evaluation/section-weakening owners. They introduce no primitive,
unification rule, independently postulated laxity cell, or general duality
bridge. The earlier 21-rule audit remains historical; the current recovered
triangle consumer imports the nucleus directly. The independent native
ordinary-Eval audit remains rule-free and Op-free.

The rule inventory is:

| Structural operation | Selected computation |
|---|---|
| Leading `Eval_funcd ∘ FF`, ordinary and opposite presentations | Whole, point, and extracted-cell action through Eval after FF; arbitrary displayed composites are not opened. |
| `Eval_funcd`, ordinary and opposite presentations | Whole mixed Eval action, its point action on `(eta,q)`, and transported-identity cell at a visible `(U,i)`. |
| Displayed pairing, ordinary and opposite presentations | Whole, point, and cell projections are pairs of the original actions/cells. |
| Displayed identity | Whole identity Hom functor, unchanged point arrow, and transported-object identity cell. |
| Explicitly constant weakened section, ordinary and opposite presentations | Whole constant Hom action and identity-valued point action; the ordinary cell uses the pre-existing weakening projection and the original constant section. |
| Original constant section of a constant family | Whole constant Hom functor, point identity, and cell identity, including neutral terminal arguments. |
| Constant-section presentation joins | Terminal-source weakening returns the same constant section; its opposite is constant at the same object of the opposite target. |

Whole action is not inferred merely from the point formulas. The dedicated
[`displayed_evaluation.lp`](../emdash2/examples/displayed_evaluation.lp)
reviewer checks whole Hom functors, explicitly expanded competing projection
orders, the next Hom action, and generic arrow-composition accumulation. It
contains 32 positive assertions, one typed noncollapse negative, and one
higher-action query. The current triangle audit computes the nonidentity
edge observation to `(a,eta[i])`; no manual square/prism field is added.

### What The Projection-Order Review Changed

The first 21-rule candidate missed real transported-identity joins. Eval and
constant weakening could compute by their point formula while the existing
identity recognizer instead exposed an unreduced `fdapp1_int_cell`. Pairing
and leading evaluation likewise needed the corresponding cell projections.
These cells are extracted from the existing whole internal action. Pairing
retains arbitrary component cells, and the leading-Eval cell applies Eval
to the original FF cell; neither rule makes an arbitrary cell invertible.

The review also exposed terminal specialization false negatives. A weakened
constant section could acquire an ordinary `K → I` presentation before its
displayed component reduced, leaving its object applications stuck. The
narrow terminal/constant whole fold fixes that presentation, and the original
constant-section whole/point computations join the order that erases the
weakening head first. The point instance is needed even after the whole
instance: neutral arguments of terminal type need not have the literal
`Terminal_obj` syntax required by the older terminal-source recognizer.

Do not generalize the terminal fold to arbitrary sections. That trial
introduced a separate whole `1 → C` eta overlap between a neutral section
component and the constant functor at its point. The chosen rule requires
the explicitly constant target family and constant section, so it does not
install that eta principle. The generic-section negative reviewer confirms
that its extracted cell is not identified with an identity.

Relevant failing controls remain in ignored probes/logs:
`hint_eval_cell_order-20260908-201643.log`,
`hint_constant_section_cell_order-20260908-201643.log`,
`hint_eval_overlap_orders-20260908-204718.log`,
`hint_eval_terminal_weakening_endpoints-20260908-204820.log`,
`hint_eval_whole_owners-20260908-205437.log`, and
`hint_eval_whole_owners-20260908-205620.log`.
The completed whole reviewer passes in
`hint_eval_whole_owners-20260908-205708.log`. These are concrete projection
and endpoint tests, not a warning-count argument against intended rules.

### LHS And Orientation Audit

Twenty-nine unused candidate variables were replaced by `_`; no repeated
equality guard was removed mechanically. The four leading-Eval whole/point
rules retain the nested `Catd_cat(K)` composition category because both the
wildcard trial and a tied-outer-base trial fail subject reduction
(`hint_triangle_eval_guard_core-20260908-201442.log` and
`hint_triangle_eval_guard_core-20260908-201830.log`). The corresponding cell
rules use that same measured guard. Constant-section source/target families
are genuine semantic discriminators: a constant displayed operator with a
nonterminal source is a different case. Intentional nested guards are
annotated; the generic strict LHS scan still reports 62 reviewed slots in
39 clauses and no unreviewed candidates. Its limited head table does not
replace this manual nested/dependent-head audit.

Opening a displayed operator whose leading factor is Eval does not reverse
the global accumulation of mapped arrows. Both `F[g] ∘ F[f] → F[g ∘ f]`
and equality of two-stage Sigma evaluation with the action of the composite
operator pass. The unrestricted displayed-composite and
`Op_funcd(GG ∘ FF)` rules remain unpromoted historical probes.

### Warning Classification And Validation

The final active-core warning log is
`emdash3_2-20260908-210011.log`: 1,139 critical-pair reports / 157 replaceable
pattern reports, against the preceding 1,125/157 boundary. Every pair parses;
there is no removed old rule-family count. The 14 added family instances are:

| Family | Added reports | Typed control |
|---|---:|---|
| Point action versus transported-identity/terminal-source recognition | 8 | Op Eval (1), pairing (1), Op pairing (2), identity (2), and constant weakening (2); use the actual transported endpoint and its identity carrier. |
| Constant weakening unit versus extracted cell | 2 | Ordinary and opposite terminal/constant cell orders. |
| Constant weakening unit versus whole Hom action | 2 | Ordinary and opposite terminal/constant whole-functor orders. |
| Constant weakening unit versus point action | 2 | Ordinary and opposite terminal/constant point orders, including neutral terminal data. |

The raw overlap engine leaves endpoint/family variables independent which a
typed instance relates. One identity overlap even instantiates object/arrow
slots with a family and its category identity; it is not accepted as a
well-typed generic consumer. The reviewer checks the meaningful typed cases
and both explicitly exposed projection orders rather than declaring every
raw warning harmless. Earlier source-order reports were also reduced by
putting the existing selected cell joins before the corresponding point
rules. The remaining counts are accepted diagnostic evidence, not a proof
of global confluence, termination, or consistency.

The exact fresh package `/tmp/emdash-displayed-eval-final.IM4Zui` checks the
final nucleus, the dedicated reviewer, both native/recovered audits, central
`emdash3_2_checks.lp`, and 13 existing reviewers: dependent-Hom laxity,
ordinary con owners, products/Eval/curry, Sigma totalization, fibrewise Sigma,
diagram evaluation, arrow/zero-arrow families, diagram exchange, chain-pair
cubical/native views, PathOut transformation lift, and cubical-arrow functor
action. All 18 targets pass, each with a 90-second ceiling and ordinary
subject reduction. Logs are `logs/probes/final-staged-*.log`. Active-source
and dedicated-reviewer checks also pass; the latter is
`displayed_evaluation-20260908-210013.log`. The source bytes match the staged
core exactly.

The 42 focused metrics/TOC/registry/warning-parser tests, strict catalog
freshness, source TOC and LHS checks pass. Source-only metrics collect 739
registered files without checking unrelated targets. The parent full-health
exception is retained; no repository-wide TypeScript, reviewer/source
aggregate or book render is claimed.

### Next Architecture Gate

Resume the strict zero-long-edge restriction and coherent maps between the
varying triangles. The actual transformation remains the source of the
coherence/prism data; do not introduce a manual square record. Then qualify
whole kernel/cokernel capabilities against the original selected operations,
and build whole H. The present evaluation computation does not itself prove
those universal interfaces, identify a directed zero cell with an equality,
or turn objectwise factor contractibility into arbitrary-omega coherence.
General op repair stays deferred and preserved. Generic window exactness,
bounded assembly, retained proof–CAS choices and final book work are still
required by the parent goal.
