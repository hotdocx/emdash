# Strict Internal Homology Pilot

Date: 2026-09-08

Status: active bounded architectural slice within the long-exact goal

Parent: [bounded long exact homology and book plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md)

Worktree: `/home/user1/emdash1-long-exact-v1`

Branch: `goal/bounded-long-exact-homology-book-v3.2`

## Decision And Scope

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
| `HINT-UNIVERSAL-3` | next | whole kernel/cokernel interfaces with actual universal transformations, selected choices and justified capability boundary |
| `HINT-COMPLEX-4` | pending | bounded three-term complex category and whole H; identity, nonidentity composition, differential/reconstruction computation and retained higher action |
| `HINT-CONSUMER-5` | pending | original nonsplit proof-CAS example plus one formerly expensive consumer, with complete dependency/observation timings |

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
