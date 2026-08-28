# Emdash v3.2 Pullbacks And Slice Base-Change Computation Plan

Date: 2026-08-28 (America/Toronto)

Plan-ID: `PULLBACKS-SLICE-BASE-CHANGE-COMPUTATION-V3.2`

Status: **active implementation plan**.

Branch: `goal/pullback-computation-v3.2`

Worktree: `/home/user1/emdash1-pullbacks-v3.2`

Baseline: `9fe068348330668e1d131fadacb6fed22832022c`, the validated direct-parent
integration of the completed monad/product/terminal and
cubical/functor-property-profile branches.

Depends-On: active `emdash3_2.lp`; `emdash3_2_presheaves.lp` slice owners;
indexed `Adjunction`; `hom_con_int`, `homd_int`, Sigma totals, ordinary and
displayed action; the completed triangular product and terminal interfaces;
current Foundations, canonical syntax, SOP, and persistent-goal Git workflow.

Supersedes: no completed pullback plan. It promotes the deferred general
dependent-adjunction shadow only for categorical slices and base change; it
does not supersede generic family substitution `Pullback_catd`.

Side-Task-Ledger: `PB-00`, `PB-SLICE-1`, `PB-DOMAIN-2`, `PB-STRUCT-3`,
`PB-ADJ-4`, `PB-USABILITY-5`, `PB-CONE-6`, `PB-TRIANGLE-7`, `PB-PSEUDO-8`,
`PB-COMPAT-9`, `PB-DOC-10`, and `PB-CLOSE-11`.

Infinity-Codex-Origin: session `01a02f68-6142-7e53-993a-4505aa8e2cbe`,
review response `0028_2026-08-28T07-43-06Z_01a04745-7f87-7750-a3e1-2bdea720554d.md`.

Infinity-Codex-Decision-Responses: `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a04745-7f87-7750-a3e1-2bdea720554d` and the user's
2026-08-28 approval/adjunction-usability clarification immediately following
that response.

## Objective

Implement a computational and internal chosen pullback/base-change structure
for an emdash category `C`. The public structure must internalize objects and
base arrows, retain whole and higher action, reuse the existing adjunction
calculus, and expose the ordinary pullback object, projections, commuting
square, and universal lift without replacing the whole structure by a bare
point operation.

The target architecture is:

```text
SliceSigma(C) : C → Cat
X             ↦ C/X
f : X → Y    ↦ Σ_f : C/X → C/Y

SliceBaseChange(PB) : C^op → Cat
X                   ↦ C/X
f^op : Y → X       ↦ f* : C/Y → C/X

Σ_f ⊣ f*.
```

Here `⊣` denotes the existing `Adjunction` relation. The implementation is
chosen/coherent computational structure, not merely a proposition that some
pullbacks exist.

TypeScript macros, metaprogramming, surface declaration automation, free
pullback syntax, a global commuting decision procedure, and publication are
outside this goal.

## Reviewed Conclusion

The primary carrier is the codomain/slice family, not the raw family
`Hom(X,-)` in isolation.

A category has pullbacks precisely when its codomain projection is a
Grothendieck fibration. Choosing pullbacks gives the contravariant indexed
slice construction

```text
C^op → Cat,
X     ↦ C/X,
f     ↦ f*.
```

`Hom(X,-)` only postcomposes arrows with fixed domain; it does not choose the
new domain of a pullback. The relevant fibre over `Y` is the whole category of
arrows into `Y`, internally formed as a Sigma total of a represented hom
family. The existing `hom_con_int`, `Sigma_cat`, and `homd_int` owners build
that arrow/slice category and its triangles or higher cells. Pullback
structure supplies the missing opposite-variance action on those slice
fibres.

The minimal semantic characterization for one arrow remains useful:

```text
PullbackAlong(f,F) ≡ Adjunction(Σ_f,F).
```

It is the first fallback/probe boundary. It is not the preferred final public
interface because independent per-arrow data alone does not retain coherent
whole variation in `f`.

## Existing Emdash Substrate

The active presheaf/slice layer already defines:

```text
arrow_into_catd(C)[Y] = Sigma_{Z:C^op} Hom_C(Z,Y)
Into_restr_cat(C,Y)   = arrow_into_catd(C)[Y]
Slice_cat(C,Y)        = Op(Into_restr_cat(C,Y)).
```

The kernel's whole comma-family owner gives the covariant slice family at the
identity functor:

```text
CommaFib_catd(id_C)[Y] = C/Y.
```

Its base-arrow action is postcomposition, hence `Sigma_f`. The first probe
must determine whether the following selected presentation is definitionally
usable at fibre and action positions:

```text
SliceSigma_catd(C) ≡ CommaFib_catd(id_C).
```

If a canonical projection order prevents that exact presentation from
typing, use the existing transparent
`Op_catd(arrow_into_catd(C))`/`Op_func(into_restr_postcompose_func(f))`
route. Do not introduce two runtime owners for the same covariant slice
action.

Three existing notions must remain distinct:

1. `Pullback_catd(E,F)` is substitution/reindexing of an already-given
   Cat-valued family along a functor. It exists without categorical
   pullbacks in the base category.
2. `SliceBaseChange_catd(PB)` is the new chosen categorical base-change
   family whose action sends an arrow over `Y` to its pullback over `X`.
3. `homd_int` classifies dependent triangles/higher cells used inside slice
   arrows and pullback cones; it is not itself the choice of a pullback.

The generic whole `slice_domain_func : C/Y → C` currently lives too far
downstream in the commutative-algebra restriction module. The preferred
dependency correction is to move or factor the rule-free generic domain
functor into the slice/presheaf layer, preserving its exact body and all
downstream consumers. A temporary raw projection in the new module is allowed
only if that refactor would materially widen the initial tranche.

## Selected Enhanced Interface

Provisional declarations are:

```lambdapi
symbol SliceSigma_catd (C : Cat) : τ (Catd C)
≔ @CommaFib_catd C C (@id_func C);

injective symbol PullbackStructure (C : Cat) : Grpd;

injective symbol SliceBaseChange_catd
  [C : Cat]
  (PB : τ (@PullbackStructure C))
  : τ (Catd (Op_cat C));

rule @fapp0 _ Cat_cat
      (@SliceBaseChange_catd $C $PB)
      $X
  ↪ @Slice_cat $C $X;
```

The spelling is schematic; promoted Lambdapi uses the repository's Unicode
syntax and exact inferred slots selected by owner-position probes.

The exact fibre rule is intentional. It makes the chosen family's fibre
definitionally the existing `Slice_cat`, rather than relating an arbitrary
family to slices through an opaque equality or `IsoEvidence` transport.

For `f : X → Y`, define transparent action views:

```text
slice_sigma_func(f)
  ≡ fapp1_fapp0(SliceSigma_catd(C),f)
  : C/X → C/Y

slice_base_change_func(PB,f)
  ≡ fapp1_fapp0(SliceBaseChange_catd(PB),f^op)
  : C/Y → C/X.
```

The essential structural observation is indexed by the actual two functors:

```lambdapi
slice_base_change_adjunction(PB,f)
  : Adjunction
      (slice_sigma_func f)
      (slice_base_change_func PB f);
```

The base-change family itself owns identity, composition, and every next hom
action through the generic `Catd`/functor calculus. Do not add specialized
`id*` or composite-base runtime laws merely to restate generic
functoriality.

This initial interface carries the current normal-lax compositor of a whole
`Catd(Op C)`. Pullback reindexing is naturally pseudofunctorial rather than
canonically strict. Do not require `IsStrictFunctor`. An explicit invertible
compositor capability may be derived from adjoint uniqueness or supplied in a
later row. If the generic `IsPseudoFunctor` property is reused, first factor it
out of the Gray-specific dependency chain; foundational pullbacks must not
depend on Gray machinery only for a property name.

## Adjunction Runtime Ownership And Lambdapi Usability

The existing generic adjunction declarations remain the semantic and runtime
authority:

```text
unit_adj_transf(J_f)   : id_(C/X) => f* o Sigma_f
counit_adj_transf(J_f) : Sigma_f o f* => id_(C/Y),
```

where `J_f = slice_base_change_adjunction(PB,f)`. Their full components,
off-diagonal actions, and the two generic triangle reductions are the first
normalization route. The pullback module must not introduce independent unit,
counit, transpose, or mate axioms.

Nevertheless, generic ownership does not imply that every useful projected
slice/ambient term still syntactically contains the generic triangle LHS.
Following the established SOP for functoriality, products, and adjunction
usability, two additional classes are explicitly allowed when measured:

### Post-projection runtime instances

If `Slice_cat`, `slice_domain_func`, a stable base-change action, or a
constructor-visible slice arrow reduces away a discriminator required by the
generic triangle rule, add the smallest duplicated instance at the canonical
post-projection heads. Such a rule is a projection-order join, not a second
adjunction law.

Every candidate must:

- reproduce an already-valid generic adjunction reduction;
- use the surviving rigid operation/action heads as LHS discriminators;
- infer compound endpoints with `_` unless a measured guard is necessary;
- include the direct generic route and the projected route as typed positive
  consumers;
- include a relevant noncollapse/negative consumer; and
- classify warning deltas and both reduction orders.

Warnings alone do not veto a semantically intended join. A subject-reduction
failure, wrong endpoint, changed unrelated normal form, or runtime false
negative at the intended canonical term does.

### Proof-time usability rules

The Lambdapi layer needs the same declaration-to-use-site usability discipline
as the completed adjunction and monad work. Narrow bidirectional proof-time
comparisons may relate:

- `slice_sigma_func(f)` and the canonical
  `Op_func(into_restr_postcompose_func(f))` presentation;
- the public stable `f*` action and its whole
  `fapp1_fapp0(SliceBaseChange_catd(PB),f^op)` owner, if both heads survive;
- a readable pullback transpose/lift facade and the selected generic
  unit/counit composite; and
- any user-supplied named adjunction spelling and
  `slice_base_change_adjunction(PB,f)` when declaration-backed agreement is
  part of the selected structure.

Use a `unif_rule` only when neither side should erase the other at runtime.
Both sides should have rigid heads; avoid bare-variable eta rules and
nontransitive chains through a third reducible alias. Each orientation needed
by elaboration must be exercised by typed `eq_refl`, while `assertnot` or an
equivalent runtime-negative control confirms that proof-time usability did not
become a runtime reduction.

If the conventional semantic spelling and the stable computational owner can
be made definitionally identical by a transparent definition without losing a
runtime discriminator, prefer that definition and add no unifier. If a
runtime head is required by pullback beta/eta rules, retain it and relate the
semantic spelling at proof time.

TypeScript usability generation is deferred. This row implements the same
concepts directly in Lambdapi.

## Ordinary Pullback Objects And Projections

Given

```text
f : X → Y
g : Z → Y,
```

the chosen pullback is the slice object

```text
f*(g) : C/X.
```

Write its domain as `P`. Then:

- `π₁ : P → X` is the structure arrow of the slice object `f*(g)`;
- `π₂ : P → Z` is the ambient-domain projection of the counit component
  `ε_g : Σ_f(f*(g)) → g` in `C/Y`; and
- the commuting square `f ∘ π₁ = g ∘ π₂` is extracted from that slice arrow,
  not postulated as an unrelated path.

For a cone

```text
a : W → X
b : W → Z
q : f ∘ a = g ∘ b,
```

constructor-visible Sigma/homd data form a slice arrow

```text
b̄ : Σ_f(a) → g.
```

Its adjoint transpose is

```text
f*(b̄) ∘ η_a : a → f*(g)
```

in `C/X`. Applying the whole slice-domain functor gives the ambient mediator

```text
⟨a,b;q⟩_pb : W → P.
```

The primary transpose must remain whole in the cone arrow and retain higher
action. A bare primitive point `pullback_lift(a,b,q)` is not an accepted
highest-level owner. A stable point facade is allowed only as the canonical
projection of the selected whole operation when active runtime LHSs must
discriminate on it.

## Desired Triangular Computation

The generic adjunction triangles should yield, first in slice categories and
then after ambient projection:

```text
untranspose(transpose(b̄)) ↪ b̄
transpose(untranspose(k))     ↪ k

π₁ ∘ ⟨a,b;q⟩_pb ↪ a
π₂ ∘ ⟨a,b;q⟩_pb ↪ b

⟨π₁ ∘ h, π₂ ∘ h; square(h)⟩_pb ↪ h.
```

The first projection law may already be constructor/typing computation of an
arrow in `C/X`. The second beta and eta are the expected adjunction triangle
cuts. Probe the generic unit/counit composites before adding any direct rule.

If a stable projected head is required, the pullback-specific rules above are
the only expected new semantic runtime family. Naturality in cone arrows,
identity/composition of `f*`, and composition of transposes remain generic.
Do not add a pullback rule whose only content is ordinary functoriality or
adjunction naturality.

An `IsContr` factorization category recentered at the selected mediator or a
terminal-object presentation of the cone category is a valuable semantic
verification layer. It does not replace the whole computational transpose.

## Alternative Presentations And Their Roles

| Presentation | Selected role |
| --- | --- |
| Raw `Hom(X,-)` with a second variance | Rejected as primary: it cannot choose the new pullback domain. |
| Per-arrow `Adjunction(Sigma_f,F)` | Minimal semantic probe/fallback; useful but not the final coherent whole interface. |
| Binary products in every slice `C/Y` | Equivalent compatibility theorem and possible adapter; not the first owner of `f*`. |
| Terminal object in a cospan-cone category | Semantic verification/contractibility view; cone-category infrastructure is heavier. |
| Primitive cospan category and pullback-object functor | Possible later internalization, but unnecessary before the requested base-change action. |
| Bare primitive projections/lift | Rejected as primary because it caps higher action; allowed only as projections of whole owners. |
| Existing `Pullback_catd(E,F)` | Preserved as generic family substitution, a distinct construction. |

For locally discrete categories, the selected slice construction specializes
to ordinary categorical pullbacks. For a general emdash category, the existing
slice/comma totals retain directed higher cells; the feature is therefore a
chosen higher/lax base-change structure. Any later strict, pseudo, or
groupoidal pullback profile must be named explicitly rather than silently
conflated.

## Products, Terminal Objects, Weighted Limits, And Duality

Every slice of a category with pullbacks has binary products, and binary
products in all slices characterize pullbacks. This should be proved as a
compatibility theorem after the base-change computation is stable. Do not
first assemble a slice-indexed family of independently selected product
functors and call it `f*`.

With the existing selected terminal object, the pullback of `!_A` and `!_B`
gives a binary product. An independently selected `BinaryProducts(C,P)` need
not be definitionally the same choice. Relate the two by a canonical
`IsoEvidence`, `DefIso`, or assumption-explicit computational comparison only
to the extent existing constructors support it; do not postulate equality of
chosen product functors.

The weighted-limit layer remains a semantic presentation. A walking-cospan
weight can later compare a supplied weighted pullback with the slice
base-change structure, following the assumption-explicit binary-product
adapter. It is not the primary runtime calculus.

Pushouts are the opposite-category dual:

```text
PushoutStructure(C) ≡ PullbackStructure(C^op).
```

Keep this as a later measured `Op_*` consumer. Add stable mirror heads only if
normalization erases an actual runtime discriminator, following the narrow
monad/comonad precedent.

## Later Dependent Sigma And Pi Along A Map

There is no separate existence axiom for `Sigma_f`: it is postcomposition in
slices and exists in every category.

Chosen pullbacks provide:

```text
Σ_f ⊣ f*.
```

The genuinely additional locally cartesian closed structure is a chosen
right adjoint

```text
Π_f : C/X → C/Y
f* ⊣ Π_f.
```

Both adjunctions must instantiate the existing `Adjunction` interface and its
triangle/usability discipline. They must not duplicate a second adjunction
theory. Keep the names distinct from the kernel's `Sigma_cat(E)` total and
`Pi_cat(E)` section category.

Beck--Chevalley, Frobenius, substitution stability, and compatibility between
slice adjoints and the kernel total/section constructors are later coherence
layers. They are not hidden fields of the first pullback structure.

## Module And Authority Boundary

The intended implementation module is:

```text
emdash3_2_pullbacks.lp
```

It imports the active slice/presheaf layer and reuses the kernel adjunction
owners. It should not be placed in `emdash3_2.lp` unless a genuinely generic
slice-domain projection must be factored upstream. It must not import
commutative algebra, Gray-cube applications, or TypeScript tooling.

Durable consumers belong in:

```text
emdash3_2_checks.lp
examples/pullbacks.lp
```

Authorities, Foundations, canonical syntax, source registries, catalog, and
health metadata are synchronized only after the selected owner positions are
green.

## Implementation Sequence

1. Freeze baseline/worktree state and add this living plan.
2. Probe `CommaFib_catd(id_C)` versus the existing whole slice presentation at
   fibre, full action, capped action, and constructor-visible object action.
3. Factor or select the generic whole slice-domain functor at the lowest honest
   dependency boundary.
4. Promote `PullbackStructure`, `SliceBaseChange_catd`, its exact fibre rule,
   and transparent `f*` action.
5. Add the per-arrow existing-adjunction observation `Σ_f ⊣ f*`.
6. Probe both generic adjunction triangle reductions before naming any
   pullback-specific join.
7. Add typed bidirectional proof-time usability tests for every semantic/
   stable spelling that must elaborate interchangeably; retain runtime
   negatives.
8. Construct the pullback object, both projections, and square from the
   base-change action and counit.
9. Construct the whole cone transpose and ambient mediator; classify beta,
   eta, and any post-projection false negatives.
10. Add only necessary projection-order runtime instances and corresponding
    warning/subject-reduction audits.
11. Add direct central checks, a reviewer example, compatibility/negative
    evidence, docs, catalog, and health registration.
12. Run scoped validation and create local checkpoint commits only at coherent
    green tranche boundaries.

## Side-Task Ledger

| Row | State | Deliverable and acceptance boundary |
| --- | --- | --- |
| `PB-00` | complete | Dedicated branch/worktree created from exact integrated baseline; bootstrap and clean-state preflight pass; this plan is the living authority. |
| `PB-SLICE-1` | in progress | Exact whole covariant slice family and `Sigma_f` action selected through existing comma/arrow-into owners; fibre/action probes green without duplicate runtime owner. |
| `PB-DOMAIN-2` | pending | Generic whole slice-domain functor available at an honest dependency boundary and its object/arrow projections checked. |
| `PB-STRUCT-3` | pending | Chosen whole contravariant slice family with exact `Slice_cat` fibres and retained higher action. |
| `PB-ADJ-4` | pending | Per-arrow `Adjunction(Sigma_f,f*)` observation, unit/counit projections, and generic triangle consumers. |
| `PB-USABILITY-5` | pending | Required rigid-head proof-time orientations, typed `eq_refl`, runtime negatives, and any declaration-backed named-adjunction bridge. |
| `PB-CONE-6` | pending | Pullback object, domain, two projections, commuting square, constructor-visible cone arrow, whole transpose, and ambient mediator. |
| `PB-TRIANGLE-7` | pending | Both slice cancellations and ambient beta/eta; only measured post-projection instances promoted. |
| `PB-PSEUDO-8` | pending | Composition/identity higher action retained; invertible compositor derived, honestly supplied, or explicitly deferred without importing Gray-only infrastructure. |
| `PB-COMPAT-9` | pending | Products-in-slices, terminal-derived products, weighted pullback, and opposite pushout comparisons classified and implemented only where concrete. |
| `PB-DOC-10` | pending | Central checks, reviewer, Foundations/SOP/syntax/index/source maps, catalog, and health registries synchronized. |
| `PB-CLOSE-11` | pending | Focused checks, warnings, strict LHS audit, usability/noncollapse tests, catalog, health freshness, exact diff, and local checkpoint green. |

## Decision Ledger

| ID | State | Decision |
| --- | --- | --- |
| `D-PB-001` | accepted | Primary structure is the contravariant slice/base-change family, not raw `Hom(X,-)`. |
| `D-PB-002` | accepted | `Sigma_f` is the always-existing covariant slice action; pullbacks supply its chosen right adjoint `f*`. |
| `D-PB-003` | accepted | Exact slice fibres compute by a stable structure projection; no opaque equality bridge relates an arbitrary family to slices. |
| `D-PB-004` | accepted | Generic adjunction triangles remain semantic/runtime owners. Duplicated rules are allowed only as measured post-projection instances of those laws. |
| `D-PB-005` | accepted | Lambdapi usability may use narrowly typed, bidirectional rigid-head `unif_rule`s with runtime-negative controls; TypeScript generation is deferred. |
| `D-PB-006` | accepted | Whole cone transpose precedes point mediator; direct projection/lift heads are projections or justified discriminators, not independent axioms. |
| `D-PB-007` | accepted | Generic `Pullback_catd` family substitution remains distinct in name and ownership from categorical slice base change. |
| `D-PB-008` | accepted | Do not require strict base-change functoriality; retain current whole higher action and classify pseudo coherence separately. |
| `D-PB-009` | accepted | Products-in-slices, terminal-derived products, weighted limits, and pushout duality are compatibility consumers after the primary calculus. |

## Required Positive Evidence

At minimum, durable checks must establish:

- `SliceSigma_catd(C)[X]` has the exact `Slice_cat(C,X)` fibre;
- its action at `f` has type `C/X → C/Y` and agrees with canonical
  postcomposition;
- `SliceBaseChange_catd(PB)[X]` reduces to `Slice_cat(C,X)`;
- its action at `f^op` has type `C/Y → C/X` and retains another hom action;
- `slice_base_change_adjunction(PB,f)` is indexed by those exact functors;
- unit and counit components type at arbitrary slice objects;
- the two generic triangle terms compute before specialization;
- required semantic/stable spellings type by `eq_refl` through selected
  usability rules while remaining runtime distinct;
- the chosen pullback object's domain and first projection compute;
- the second projection is derived from the counit and whole domain action;
- the square is projected from the slice arrow;
- the cone transpose/mediator types and retains higher action;
- both pullback beta laws and eta/uniqueness compute or have precisely
  classified derived paths; and
- locally discrete/closed examples reject false endpoint or variance
  identifications.

## Required Negative And Noncollapse Evidence

Durable negatives must reject at least:

- `Pullback_catd(E,F)` as the same symbol or type as categorical `f*`;
- a covariant `f* : C/X → C/Y` variance mistake;
- arbitrary `SliceBaseChange_catd(PB)` fibres collapsing without the structure
  head;
- proof-time usability becoming a runtime fold;
- generic base-change action collapsing to identity or composition by a
  pullback-specific rule;
- a point lift replacing its whole transpose/hom action;
- direct equality of independently selected product and pullback-derived
  product functors;
- strict/pseudo/groupoidal pullbacks being silently conflated; and
- `Pi_f`, Beck--Chevalley, Frobenius, or pushout computation being claimed by
  the first tranche.

## SOP And Validation

For each rule or unifier:

1. locate the owner and all consumers with `rg`;
2. probe a full-file copy at the intended owner position;
3. keep reducible/compound implicit endpoints `_` unless measured as guards;
4. include typed positive and runtime-negative consumers;
5. compare warning inventories and inspect exact rule families;
6. run `audit_rule_lhs.py --strict` on every changed rule-bearing file;
7. promote only the smallest coherent owner;
8. update this ledger before a checkpoint.

Scoped closure runs the new module, directly affected upstream owner if
factored, central diagnostics, reviewer example, warning probes, strict LHS
audits, strict catalog, source TOC, active refs, report headers, health-source
freshness, and exact diff hygiene. Do not run unrelated repository-wide long
aggregates merely for reassurance.

## Acceptance And Stop Conditions

The first computational pullback tranche is complete only when:

- the whole covariant and contravariant slice families have exact variance and
  retained higher action;
- `Σ_f ⊣ f*` uses the existing adjunction authority;
- necessary adjunction usability is present at proof time without erasing
  runtime heads;
- pullback object, projections, square, whole transpose, and mediator are
  internal constructions;
- beta/eta reach their intended canonical terms through generic triangles or
  narrowly justified projection instances;
- no hidden propositional bridge substitutes for a feasible definitional
  fibre/action boundary;
- warnings and strict-LHS findings are classified;
- authorities, checks, reviewer, catalog, and health registrations agree; and
- the dedicated worktree is clean at a validated local checkpoint.

If exact slice fibres, slice-arrow projection, or ambient triangle projection
cannot be expressed without a materially stronger kernel migration, record
the smallest blocker and stop that dependent row. Do not replace it with an
opaque equality or broad rewrite.

## Persistent-Goal Launch Prompt

> Continue the computational/internal pullback and slice base-change goal in
> `/home/user1/emdash1-pullbacks-v3.2` on branch
> `goal/pullback-computation-v3.2`, delegating exact formulation, owner
> positions, adjunction runtime/usability instances, sequencing, validation,
> documentation, and Git discipline to
> `emdash2/reports/REPORT_EMDASH_V3_2_PULLBACKS_AND_SLICE_BASE_CHANGE_COMPUTATION_PLAN_2026-08-28.md`
> beneath active source/SOP. Preserve baseline `9fe0683`; make only validated
> local checkpoint commits authorized by the user; do not push, merge,
> publish, rewrite history, delete branches, or remove worktrees.
