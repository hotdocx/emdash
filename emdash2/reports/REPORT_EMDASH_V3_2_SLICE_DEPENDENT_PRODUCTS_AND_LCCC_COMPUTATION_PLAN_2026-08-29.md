# Emdash v3.2 Slice Dependent Products And LCCC Computation Plan

Date: 2026-08-29 (America/Toronto)

Plan-ID: `SLICE-DEPENDENT-PRODUCTS-LCCC-COMPUTATION-V3.2`

Status: **complete first computational/internal slice-dependent-product
tranche; proportional closeout is green in the dedicated worktree; local
checkpoint remains separately authorization-gated**.

Branch: `goal/slice-dependent-products-v3.2`

Worktree: `/home/user1/emdash1-slice-dependent-products-v3.2`

Baseline: `6d253e6`, the final generic-owner cleanup and documentation
checkpoint of the completed computational/internal `Σ_u ⊣ u*` pullback layer.

Depends-On: active `emdash3_2.lp`; `emdash3_2_presheaves.lp` slice owners;
`emdash3_2_pullbacks.lp`; indexed `Adjunction`; generic
`Adjunction_hom_prof_comparison`; whole `Catd`, functor, transfor, represented
Hom, and opposite action; the completed primitive `Pi_cat` section facade;
current Foundations, canonical syntax, SOP, and persistent-goal Git workflow.

Supersedes: no completed slice-dependent-product plan. It does not supersede
`REPORT_EMDASH_V3_2_PI_ALONG_FUNCTOR_IMPLEMENTATION_PLAN_2026-06-11.md`, whose
`Pi_along_func(f) : Catd(A) → Catd(B)` is a general right-Kan/direct-image
operation on Cat-valued families rather than the locally cartesian closed
slice functor `Π_u : C/X → C/Y`.

Side-Task-Ledger: `SDP-00`, `SDP-NAME-1`, `SDP-FAMILY-2`, `SDP-ACTION-3`,
`SDP-ADJ-4`, `SDP-USABILITY-5`, `SDP-AC-6`, `SDP-MATE-7`, `SDP-WHOLE-8`,
`SDP-LCCC-9`, `SDP-COHERENCE-10`, `SDP-DOC-11`, and `SDP-CLOSE-12`.

Infinity-Codex-Origin: session `01a02f68-6142-7e53-993a-4505aa8e2cbe`,
the reviewed pullback inventory/completion response followed by the user's
2026-08-29 approval and request to proceed to `Π_u`.

Infinity-Codex-Decision-Responses: `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a04ceb-e772-7b03-81df-ddf26832b2c4`
and the user's 2026-08-29 approval, generic-owner questions, and explicit
request to start the `Π_u` persistent goal immediately following the reviewed
completion response.

## Objective

Implement the computational and internal chosen dependent-product structure
along every internal arrow of a category already carrying the selected
pullback structure.

For every internal arrow

```text
u : X → Y
```

the completed pullback layer supplies

```text
Σᵤ : C/X → C/Y
u* : C/Y → C/X
Σᵤ ⊣ u*.
```

The genuinely additional structure is a chosen whole functor

```text
Πᵤ : C/X → C/Y
```

and a second instance of the existing adjunction interface

```text
u* ⊣ Πᵤ.
```

The intended completed chain is therefore

```text
Σᵤ ⊣ u* ⊣ Πᵤ.
```

The implementation must internalize `X`, `Y`, `u`, slice objects, slice
arrows, and their higher action. It must preserve the existing generic
adjunction and functoriality owners, add specialized runtime heads or
projection-order joins only after an owner-position probe demonstrates a real
normal-form obstruction, and provide Došen-style cut computation for canonical
`u* ⊣ Πᵤ` terms.

This goal does not attempt a free syntax or a global decision procedure. As in
the completed adjunction, monad, product, terminal, and pullback layers, useful
metatheoretical cut-elimination results are realized directly as rewrite and
proof-time usability computation over internal categorical terms.

## Completed Incoming Boundary

The pullback layer is complete at baseline `6d253e6` for the following
purposes:

- `SliceSigma_catd(C) : C → Cat` has exact fibre `C/X` and action `u ↦ Σᵤ`;
- `SliceBaseChange_catd(PB) : Cᵒᵖ → Cat` has exact fibre `C/X` and action
  `uᵒᵖ ↦ u*`;
- every internal `u` carries the existing adjunction `Σᵤ ⊣ u*`;
- the unit and counit are actual whole `Transf` objects;
- their off-diagonal `tapp1` observations are the stable Došen `γᶜ` and `φᵃ`
  heads;
- both full canonical Došen rectangles and their component triangles compute;
- generic composed-functor object beta owns `(u* ∘ Σᵤ)[a]`;
- generic functor identity owns `Σᵤ(id)` and `u*(id)`;
- no pullback-specific copy of those three generic laws remains;
- the pullback cone carrier is exactly the existing whole Hom category, with
  no record carrying a manually supplied square;
- the generic `Adjunction_hom_prof_comparison` supplies the whole semantic
  varying-endpoint Hom equivalence;
- specialized stable mate heads retain higher action and point computation;
- canonical body-unfolded whole unifiers compare those stable functors with
  their semantic bodies; and
- exact raw-Hom-guarded `Cat_cat` rules reduce both stable whole mate
  composites to identity without an additional `OmegaEquivAlong` package.

The `Πᵤ` work must reuse these conclusions rather than reopen them.

## Reviewed Mathematical Architecture

### Three whole slice families

The primary computational architecture has three whole indexed families:

| Whole family | Variance | Fibre at `X` | Action at `u:X→Y` |
| --- | --- | --- | --- |
| `SliceSigma_catd(C)` | `C → Cat` | `C/X` | `Σᵤ : C/X → C/Y` |
| `SliceBaseChange_catd(PB)` | `Cᵒᵖ → Cat` | `C/X` | `u* : C/Y → C/X` |
| proposed `SliceDependentProduct_catd(DP)` | `C → Cat` | `C/X` | `Πᵤ : C/X → C/Y` |

The third row is not an isolated family of point functions. Making it a whole
`Catd(C)` retains variation in the internal base arrow and the next categorical
actions. It is a selected coherent/split computational presentation; no claim
is made that arbitrary independently chosen right adjoints are judgmentally
strict under base composition.

### Proposed selected capability

Use a structure indexed by the already-selected pullback capability:

```text
DependentProductStructure(C,PB) : Grpd
```

with a whole family observation

```text
SliceDependentProduct_catd(DP) : Catd(C).
```

Its exact fibre should compute:

```text
SliceDependentProduct_catd(DP)[X]
  → C/X.
```

For `u:X→Y`, its action should project through a stable whole discriminator
only if needed:

```text
SliceDependentProduct_catd(DP)[u]
  → slice_dependent_product_func(DP,u)
  : C/X → C/Y.
```

The corresponding object action may use a stable point head when a concrete
unit/counit or rectangle consumer needs it:

```text
Πᵤ[b]
  → slice_dependent_product_obj(DP,u,b).
```

Do not add a point head merely for notation if the whole functor projection
already leaves an adequate discriminator.

### Second adjunction

For each internal `u:X→Y`, declare the existing indexed relation at the exact
two public functors:

```text
slice_dependent_product_adjunction(PB,DP,u)
  : Adjunction(u*,Πᵤ).
```

Using the generic adjunction orientation `F:R→L`, `G:L→R`, this instance has:

```text
R = C/Y
L = C/X
F = u*
G = Πᵤ.
```

Its actual whole transformations are:

```text
ηΠᵤ : id(C/Y) ⇒ Πᵤ ∘ u*
εΠᵤ : u* ∘ Πᵤ ⇒ id(C/X).
```

Stable whole observations are justified if the generic
`unit_adj_transf`/`counit_adj_transf` heads disappear before the canonical
runtime rules can match. If promoted, raw generic observations must reduce to
the stable heads; no propositional equality bridge is acceptable.

### Došen off-diagonal operations

The consequential and antecedential operations must be the actual `tapp1`
observations of those whole transformations:

```text
γΠᶜᵤ(k) = tapp1(ηΠᵤ,k)
φΠᵃᵤ(h) = tapp1(εΠᵤ,h).
```

Their types are:

```text
k : a → a' in C/Y
γΠᶜᵤ(k) : a → Πᵤ(u*(a')) in C/Y

h : b' → b in C/X
φΠᵃᵤ(h) : u*(Πᵤ(b')) → b in C/X.
```

If stable `γΠᶜ`/`φΠᵃ` heads are required for runtime discrimination, the
rewrite direction must be:

```text
tapp1(ηΠᵤ,k) → γΠᶜᵤ(k)
tapp1(εΠᵤ,h) → φΠᵃᵤ(h).
```

They remain canonical observations of actual transformations, not independent
unit/counit operations.

### Required rectangular cuts

The generic Došen `(ac)` laws specialize to:

```text
φΠᵃᵤ(h) ∘ u*(γΠᶜᵤ(k))
  → h ∘ u*(k)

Πᵤ(φΠᵃᵤ(h)) ∘ γΠᶜᵤ(k)
  → Πᵤ(h) ∘ k.
```

The first implementation attempt must use raw generic
`unit_adj_transf`/`counit_adj_transf` terms and the existing generic rectangle
rules. Add a slice-dependent-product-specific post-projection rule only if a
focused runtime-negative probe demonstrates that the canonical term has lost
the generic LHS discriminator.

At identities, the off-diagonal operations should recover the components:

```text
γΠᶜᵤ(idₐ) → ηΠᵤₐ
φΠᵃᵤ(idᵦ) → εΠᵤᵦ.
```

The component triangles are:

```text
εΠᵤ_(u*a) ∘ u*(ηΠᵤₐ)
  → id_(u*a)

Πᵤ(εΠᵤᵦ) ∘ ηΠᵤ_(Πᵤb)
  → id_(Πᵤb).
```

Generic functor identity and composed-functor object beta are the first owners
for all identity and composite point steps. The completed pullback cleanup is
a direct prohibition against adding `Πᵤ`-specific copies without a measured
failure.

## Hom Correspondence And Usability

The second adjunction gives the internal Hom correspondence:

```text
Hom(C/X; u*a, b)
  ⇄
Hom(C/Y; a, Πᵤb).
```

The semantic point formulas are:

```text
transposeΠ(h)
  = Πᵤ(h) ∘ ηΠᵤₐ

untransposeΠ(k)
  = εΠᵤᵦ ∘ u*(k).
```

The generic `Adjunction_hom_prof_comparison` is already the whole semantic
varying-endpoint equivalence. Reuse it as the semantic authority. Do not
introduce an `OmegaEquivAlong` merely to rename that result.

Stable whole mate functors or point heads may still be justified as runtime
normal forms if the two triangle cuts cannot recognize the transparent
semantic composites. If added:

- the whole functor must precede a point-only alias so higher action remains
  available;
- point agreement with the semantic formulas should be proof-time unification
  with non-opaque typed `eq_refl` paths;
- runtime should preserve the selected stable normal form;
- point cancellation does not imply whole-functor equality; and
- whole equality or `OmegaEquivAlong` packaging remains a separate consumer
  unless whole composite laws are actually constructed.

Candidate proof-time comparisons are:

```text
transposeΠstable(h)
  ≀ Πᵤ(h) ∘ ηΠᵤₐ

untransposeΠstable(k)
  ≀ εΠᵤᵦ ∘ u*(k).
```

No whole-functor unifier should be declared before checking that both sides
retain rigid heads and that the intended higher-action consumer exists.

## Distinction From Existing Pi Owners

Three notions must remain separate:

1. `Pi_cat(E)` is the category of global sections of one family
   `E : K → Cat`.
2. The proposed general `Pi_along_func(f) : Catd(A) → Catd(B)` is a
   comma/right-Kan direct image of Cat-valued families along an arbitrary
   functor.
3. The present `Πᵤ : C/X → C/Y` is a selected right adjoint to categorical
   slice base change in a locally cartesian closed category.

The third construction is not to be named `Pi_func`, `Pi_cat`, or
`Pi_along_func`. Prefer names such as:

```text
DependentProductStructure
SliceDependentProduct_catd
slice_dependent_product_func
slice_dependent_product_obj
slice_dependent_product_adjunction
```

Comparison with the general right-Kan owner may be mathematically useful
later, but it is not a prerequisite for the selected LCCC computation.

## Locally Cartesian Closed Packaging

The first semantic capability should be named for what it supplies:

```text
DependentProductStructure(C,PB).
```

A thin locally cartesian closed package may then combine:

```text
PullbackStructure(C)
DependentProductStructure(C,PB).
```

If the selected project convention requires an LCCC to carry explicit finite
limits, the thin package should additionally reference the already-existing
terminal-object capability. Do not bake a second terminal or product theory
into the dependent-product structure.

Every slice already has its identity arrow as a terminal object, and pullbacks
give binary products in slices. The later slice-exponential construction may
therefore derive exponentials from `Πᵤ`; it is a consumer after the second
adjunction, not primitive `Πᵤ` data.

## Coherence Boundary

The first tranche includes:

- the whole covariant family `u ↦ Πᵤ`;
- exact slice fibres;
- whole functor and object observations needed by consumers;
- the existing adjunction `u* ⊣ Πᵤ`;
- actual unit/counit transfors;
- their Došen off-diagonal actions;
- both canonical rectangular cuts;
- component triangles;
- semantic/proof-time mate usability; and
- a thin structure package if the exact dependencies are already available.

The following remain later layers unless a direct implementation prerequisite
forces them:

- Beck–Chevalley comparison for pullback squares;
- Frobenius reciprocity or distributivity;
- comparison with general `Pi_along_func`;
- strict-fibre or comma/right-Kan formulas;
- construction of exponentials in every slice;
- compatibility with the kernel `Pi_cat` section category;
- pushout/opposite duality;
- locally cartesian closed preservation theorems;
- TypeScript declaration generation; and
- whole equality or `OmegaEquivAlong` packaging of specialized mate facades.

## Module Boundary

The active owner is:

```text
emdash3_2_slice_dependent_products.lp
```

It should import `emdash3_2_pullbacks.lp` and remain separate from the active
kernel unless a genuinely generic prerequisite must be factored upstream.

The focused reviewer should be:

```text
examples/slice_dependent_products.lp
```

Central diagnostics and the focused reviewer now import this module.

## Implemented First Tranche

The active `emdash3_2_slice_dependent_products.lp` now contains:

- `DependentProductStructure(C,PB)`;
- the exact-fibre whole covariant `SliceDependentProduct_catd(DP)`;
- stable whole `slice_dependent_product_func(DP,u)` and object action;
- the existing indexed adjunction `u* ⊣ Πᵤ`;
- transparent names for the generic actual whole unit and counit;
- stable `γΠᶜ`/`φΠᵃ` result heads, reached directly from
  `tapp1(unit_adj_transf(...))` and `tapp1(counit_adj_transf(...))`;
- both exact post-opposite Došen rectangles;
- both identity component joins;
- transparent whole semantic transpose/untranspose functors and their point
  views; and
- a transparent readable name for the generic
  `Adjunction_hom_prof_comparison`; and
- the thin total `SliceDependentProducts(C)` Sigma capability pairing a
  selected pullback structure with the dependent-product structure indexed by
  it.

The first semantic-only candidate deliberately made the whole `Πᵤ` action,
object action, unit/counit, and `γΠᶜ`/`φΠᵃ` names transparent. Exact fibres,
whole action typing, retained next action, and the second adjunction all passed,
but both full canonical rectangles were runtime-negative. Normalization had
already replaced `fapp0(u*,a)` by the stable `slice_base_change_obj` head and
reversed the readable slice composite into its restriction-oriented
`Sigma_cat` presentation. The generic adjunction rectangle could no longer
match that post-projection term.

Owner-position computation then selected the smaller stable ladder

```text
SliceDependentProduct_catd
  → slice_dependent_product_func
  → slice_dependent_product_obj
```

and stable `γΠᶜ`/`φΠᵃ` result heads. Exact raw normal forms determined
the two post-opposite rectangle LHSs. When identity `tapp1` projections reduce
first, two component terms remain, so two narrow component joins close the
other reduction order.

A minimization probe then removed duplicated stable whole unit/counit heads.
The rigid generic `unit_adj_transf`/`counit_adj_transf`, indexed by
`slice_dependent_product_adjunction`, are sufficient discriminators for the
`γΠᶜ`/`φΠᵃ` projection rules and component joins. The public whole
unit/counit names are therefore transparent aliases of the actual generic
transformations.

No unification rule is added. Generic composed-functor object beta and generic
functor identity already own every composite point and identity action needed
by the unit/counit types and component triangles. The transparent mate functors
are the explicit semantic formulas themselves, so no stable-versus-semantic
point unifier is needed.

Current proportional evidence:

- inherited pullback owner and reviewer pass at baseline `6d253e6`;
- the active slice-dependent-product owner and focused reviewer pass quietly;
- affected central diagnostics pass;
- the reviewer covers exact fibres, whole and object action, another base
  action, the second adjunction, raw actual `tapp1` projections, both full
  rectangles, both component triangles, transparent whole mate action, the
  generic whole Hom comparison, and noncollapse from `Σᵤ` and `u*`;
- warning-enabled owner checking yields
  `1482 = 1325 critical-pair reports + 157 replaceable-variable reports`, a
  37-critical-pair delta over the whole-mate-complete pullback baseline
  `1288/157`; the additions
  are exactly whole `Πᵤ` action projection (3), `γΠᶜ(id)`/`φΠᵃ(id)`
  component folds (3+3), and the two rectangles (14+14); the two component
  joins add no report;
- strict LHS audit reports zero unreviewed candidates and 14 annotated slots
  across the four exact rectangle/component clauses; and
- no `unif_rule`, specialized composite-point rule, specialized identity
  action, stable whole unit/counit duplicate, stable mate-functor facade,
  `OmegaEquivAlong`, or manual coherence record is introduced;
- the strict catalog contains 2,359 checks across 116 areas, including 27
  pullback and 9 slice-dependent-product checks, with zero unclassified
  statements;
- source-only health metadata is fresh for 328 registered owner/reviewer files
  at snapshot
  `sha256:612715e4cbae9d012908bf1a6c344df3ea2e878f4a471bf69341f3ff3b4a7253`;
  and
- source TOC, active references, current-plan headers, catalog freshness,
  source-only health freshness, and exact diff hygiene pass.

## Implementation Order

### Phase 0: Baseline and owner inventory

1. Confirm the dedicated worktree is clean at baseline `6d253e6`.
2. Re-read the active kernel adjunction, functor, `Catd`, slice, and pullback
   owners.
3. Inventory `Pi_cat`, the proposed general `Pi_along_func`, and all public
   `Pi_*` names to prevent namespace collision.
4. Run the focused pullback owner and reviewer as the inherited baseline.
5. Record exact existing generic object-composition, identity-action,
   adjunction rectangle, and profunctor comparison owners.

### Phase 1: structure and exact whole family

Probe at owner position:

```text
DependentProductStructure(C,PB)
SliceDependentProduct_catd(DP) : Catd(C)
```

with exact fibre computation:

```text
SliceDependentProduct_catd(DP)[X] → C/X.
```

Reject any formulation that relates an arbitrary family to slices through an
opaque equality or recentering path.

### Phase 2: whole action and object observation

Probe:

```text
SliceDependentProduct_catd(DP)[u] → Πᵤ
Πᵤ[b] → Πᵤb.
```

Retain whole base-arrow and next-Hom actions. Add the object head only if a
unit/counit or rectangle consumer requires it.

### Phase 3: indexed second adjunction

Declare:

```text
slice_dependent_product_adjunction(PB,DP,u)
  : Adjunction(u*,Πᵤ).
```

Probe raw generic unit/counit observations, their components, and their
off-diagonal `tapp1` actions before adding stable observations.

### Phase 4: Lambdapi usability

Add only the proof-time comparisons required to elaborate conventional
semantic formulas against the selected declaration-backed owners. Use typed
`eq_refl` in both needed orientations and runtime-negative controls.

Do not add:

- a composite-point unifier already owned by generic functor composition;
- an identity-action rule already owned by generic functor identity;
- a bare-variable eta unifier;
- a propositional equality bridge in place of runtime observation; or
- a whole-functor unifier without a rigid-headed concrete consumer.

### Phase 5: Došen rectangles

First test the canonical raw terms through the existing generic rectangle
rules. If either fails after normalization, inspect the exact surviving shape
and add only the necessary stable ladder or post-projection instance.

For each promoted rule:

- validate the direct generic and projected routes;
- keep inferred slots `_` unless measured as subject-reduction guards;
- classify warning additions without treating them as a veto;
- verify identity boundaries;
- keep an unrelated functor/adjunction negative; and
- preserve the smaller-cut orientation on the right-hand side.

### Phase 6: mate computation and whole semantic comparison

Expose transparent semantic transpose/untranspose formulas and reuse
`Adjunction_hom_prof_comparison` for whole semantic equivalence.

Add stable whole/point mate heads only when triangle runtime matching needs
them. If added, check both point cancellations and another higher action, but
do not mislabel point cancellation as whole-functor equality.

### Phase 7: thin total capability and LCCC naming boundary

After the `u* ⊣ Πᵤ` calculus is green, use the neutral initial public
package:

```text
SliceDependentProducts(C)
```

as the dependent Sigma pairing of `PB` and `DependentProductStructure(C,PB)`.
Reserve the stronger `LocallyCartesianClosedCategory` name until the selected
terminal/finite-limit convention and derived slice exponentials are assembled.
This boundary introduces no duplicate pullback, product, or terminal operation.

### Phase 8: reviewer, diagnostics, and closeout

Add focused positive and negative reviewers, central diagnostics, catalog
registration, authority prose, canonical syntax, and source-only health
metadata. Run only the affected owner/reviewer/central checks and proportional
SOP gates; do not run unrelated repository-wide long aggregates.

## Side-Task Ledger

| ID | State | Deliverable |
| --- | --- | --- |
| `SDP-00` | complete | Dedicated worktree is isolated at `6d253e6`; inherited pullback owner/reviewer and workspace bootstrap are green. |
| `SDP-NAME-1` | complete | `Pi_cat`, proposed general `Pi_along_func`, and slice `Πᵤ` have distinct semantics and selected names. |
| `SDP-FAMILY-2` | complete implementation | `DependentProductStructure` and exact-fibre `SliceDependentProduct_catd` are active. |
| `SDP-ACTION-3` | complete implementation | Whole `u ↦ Πᵤ`, stable object projection, base-arrow action, and transparent Hom mate higher action are retained. |
| `SDP-ADJ-4` | complete implementation | Existing `Adjunction` is instantiated as `u* ⊣ Πᵤ`; public whole unit/counit transparently reuse the generic actual transfors. |
| `SDP-USABILITY-5` | complete minimal result | Semantic mate functors are transparent formulas and whole Hom semantics is generic; no proof-time unifier is necessary. |
| `SDP-AC-6` | complete implementation | Both exact post-opposite Došen rectangles, `tapp1` observations, identity component folds, and both component joins compute. |
| `SDP-MATE-7` | complete bounded result | Transparent whole/point transpose and untranspose expose `Πᵤ(h)∘η` and `ε∘u*(k)` with higher action. No duplicate stable mate or point-cancellation theory is added because generic `ProfComparison` owns whole semantics. |
| `SDP-WHOLE-8` | complete classification | `slice_dependent_product_hom_prof_comparison` transparently reuses the generic varying-endpoint adjunction comparison; optional specialized whole equality remains consumer-gated. |
| `SDP-LCCC-9` | complete bounded result | `SliceDependentProducts(C)` is the thin total Sigma capability pairing `PB` with `DependentProductStructure(C,PB)`. The stronger convention-sensitive `LocallyCartesianClosedCategory` name remains gated by selected terminal/finite-limit and derived slice-exponential surfaces. |
| `SDP-COHERENCE-10` | complete classification | Beck–Chevalley, Frobenius, exponentials, general Pi-along comparison, and strict/pseudo packaging remain later consumers. |
| `SDP-DOC-11` | complete | Foundations, canonical syntax, SOP/status, report index, owner, reviewer, central diagnostics, catalog, and health registrations are synchronized. |
| `SDP-CLOSE-12` | complete validation | Owner, reviewer, affected central diagnostics, exact `1325/157` warning boundary, strict audit, strict catalog, 328-file source-only health, document gates, and diff hygiene are green. No unrelated aggregate was run. |

## Decision Ledger

| ID | State | Decision |
| --- | --- | --- |
| `D-SDP-001` | accepted | `Πᵤ` is a whole covariant action on exact slice fibres, not an isolated point operation. |
| `D-SDP-002` | accepted | The selected dependent-product structure is indexed by the existing pullback structure and adds the second adjunction `u* ⊣ Πᵤ`. |
| `D-SDP-003` | accepted | `Pi_cat`, general `Pi_along_func`, and slice `Πᵤ` remain distinct owners and namespaces. |
| `D-SDP-004` | accepted | Existing generic `Adjunction` and `Adjunction_hom_prof_comparison` remain the semantic authorities; no second adjunction or Hom-equivalence theory is introduced. |
| `D-SDP-005` | accepted | Došen `γᶜ`/`φᵃ` operations, if given stable heads, are runtime observations of actual unit/counit `tapp1`, not independent structure. |
| `D-SDP-006` | accepted | Generic composed-functor object and functor identity laws are presumed sufficient until a focused owner-position runtime-negative proves otherwise. |
| `D-SDP-007` | accepted | Point cancellation of stable mate heads does not imply whole-functor equality; optional `OmegaEquivAlong` packaging is consumer-gated. |
| `D-SDP-008` | accepted | Beck–Chevalley, Frobenius, slice exponentials, and comparison with general Pi-along are later coherence/consumer layers. |
| `D-SDP-009` | accepted | TypeScript macros and metaprogramming are deferred; the usability discipline is implemented directly in Lambdapi first. |
| `D-SDP-010` | accepted diagnosis | A fully transparent semantic candidate types the family and adjunction but both canonical rectangles remain runtime-negative after `u*` object projection and opposite-slice reversal erase the generic LHS. Stable `Πᵤ`/object and `γΠᶜ`/`φΠᵃ` result heads plus exact post-opposite instances are therefore justified. |
| `D-SDP-011` | accepted minimization | Stable whole unit/counit duplicates are unnecessary. Generic `unit_adj_transf` and `counit_adj_transf` indexed by the rigid second-adjunction declaration directly project to the stable `tapp1` result heads and remain the actual whole transformations. |
| `D-SDP-012` | accepted and implemented | Generic composed-functor object beta and generic identity action close all required point/identity forms. The module adds no unifier or specialized copy of either law. |
| `D-SDP-013` | accepted and implemented | Readable slice rectangles normalize to reversed restriction-oriented `Sigma_cat` composites. Four clauses retain exact raw category/endpoint guards for subject reduction: two rectangles and two component joins. |
| `D-SDP-014` | accepted | Transparent semantic mate functors already retain higher action, and generic `Adjunction_hom_prof_comparison` owns whole equivalence. No stable mate facade, point-cancellation rules, or `OmegaEquivAlong` is added without a separate consumer. |
| `D-SDP-015` | accepted and implemented | The first total package is neutrally named `SliceDependentProducts(C)` and contains only the selected pullback structure plus its indexed dependent-product structure. Do not claim the convention-sensitive `LocallyCartesianClosedCategory` package before terminal/finite-limit selection and derived slice exponentials are assembled. |

## Required Positive Evidence

At minimum, durable checks must establish:

- exact fibre `SliceDependentProduct_catd(DP)[X] = C/X`;
- whole action `Πᵤ : C/X → C/Y` at every internal `u:X→Y`;
- another retained base-arrow or Hom action beyond the object point;
- object action at an arbitrary slice object when a stable point is selected;
- exact existing adjunction `u* ⊣ Πᵤ`;
- actual whole unit and counit transformation types;
- `tapp1` off-diagonal operations at arbitrary endpoint-changing arrows;
- both full Došen rectangles on canonical raw terms;
- both identity component triangles;
- semantic transpose/untranspose typing and required proof-time usability;
- point mate cancellation if stable mate heads are introduced;
- generic whole Hom-profunctor comparison specialized to the second
  adjunction; and
- a negative distinction among `Pi_cat`, general `Pi_along_func`, and slice
  `Πᵤ`.

## Required Negative Evidence

Durable controls must reject at least:

- covariant/contravariant reversal of `u*` or `Πᵤ`;
- an arbitrary category receiving dependent products without a supplied
  structure;
- `Πᵤ` collapsing to `Σᵤ` or `u*`;
- `SliceDependentProduct_catd` collapsing to `SliceSigma_catd` merely because
  their fibres agree;
- `Pi_cat`, `Pi_along_func`, and slice `Πᵤ` becoming definitionally
  identified;
- proof-time semantic usability becoming an unintended runtime fold;
- a point-only `Πᵤ` interface replacing the whole family/action;
- pullback-specific or dependent-product-specific copies of generic composite
  object or identity-action laws without a measured failure;
- point mate cancellation being claimed as whole-functor equality;
- an opaque equality witness replacing an observable unit, counit, or
  rectangle; and
- Beck–Chevalley, Frobenius, exponentials, or general right-Kan computation
  being claimed by the first tranche.

## SOP And Validation

Every nontrivial rule or unifier must be tested in a full-file copy at its
intended owner position before promotion. Use the uniform 90-second per-target
ceiling. For each candidate:

1. locate the generic owner and consumers with `rg`;
2. write the canonical positive term before the candidate;
3. confirm whether it is genuinely runtime-negative;
4. minimize non-discriminating LHS slots;
5. validate subject reduction and both reduction orders;
6. compare exact warning families;
7. add typed `eq_refl` checks for every unifier;
8. keep runtime-negative controls for proof-time-only comparisons;
9. run the strict LHS audit on every changed rule-bearing file; and
10. synchronize this ledger before any authorized checkpoint.

Proportional closeout includes the new owner, focused reviewer, affected
central diagnostics, warning inventory, strict audit, catalog, source TOC,
active-reference and report-header checks, source-only health freshness, and
exact diff hygiene. Do not run unrelated all-source, all-example, print, book,
or repository-wide aggregates merely for reassurance.

## Acceptance Boundary

The first slice-dependent-product tranche is complete when:

- the whole exact-fibre family `u ↦ Πᵤ` is active and retains higher action;
- each internal `u` carries the existing adjunction `u* ⊣ Πᵤ`;
- its whole unit/counit and off-diagonal observations are actual transfor
  projections;
- both full canonical Došen rectangles and component triangles compute;
- conventional semantic mate formulas elaborate through narrowly justified
  usability;
- generic functor laws remain the owners of composite points and identities;
- the generic profunctor comparison remains the whole Hom-equivalence owner;
- no `Pi_cat`/general-Pi/slice-Pi namespace or semantic collapse occurs;
- the thin dependent-product capability is documented as the LCCC foundation;
- coherence and derived-exponential layers are explicitly deferred; and
- proportional validation and documentation gates are green.

## Persistent-Goal Launch Prompt

> Continue the computational/internal slice-dependent-product and locally
> cartesian closed foundation in
> `/home/user1/emdash1-slice-dependent-products-v3.2` on branch
> `goal/slice-dependent-products-v3.2`. Treat
> `reports/REPORT_EMDASH_V3_2_SLICE_DEPENDENT_PRODUCTS_AND_LCCC_COMPUTATION_PLAN_2026-08-29.md`
> as the living authority for exact scope, design, side-task state, validation,
> and stop conditions. Re-read the active kernel, nested SOP, completed
> pullback owner/plan, and relevant `Pi_cat`/general-Pi plans on every
> continuation. Preserve `Σᵤ ⊣ u*` as the completed baseline; implement the
> second existing adjunction `u* ⊣ Πᵤ` through one whole exact-fibre slice
> family, actual unit/counit transfors, and Došen rectangle computation. Prefer
> generic composition, identity, adjunction, and profunctor owners; add stable
> heads, post-projection rules, or proof-time unifiers only after focused
> owner-position evidence. Keep `Pi_cat`, general `Pi_along_func`, and slice
> `Πᵤ` distinct. Update the living ledger and authority prose as findings
> evolve, use only proportional affected checks under the 90-second per-target
> ceiling, and stop rather than introduce opaque equality, manual coherence
> records, capped point substitutes, or unmeasured broad rewrites.
