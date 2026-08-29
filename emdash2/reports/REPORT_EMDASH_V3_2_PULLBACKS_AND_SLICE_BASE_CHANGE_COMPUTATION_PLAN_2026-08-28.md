# Emdash v3.2 Pullbacks And Slice Base-Change Computation Plan

Date: 2026-08-28 (America/Toronto)

Plan-ID: `PULLBACKS-SLICE-BASE-CHANGE-COMPUTATION-V3.2`

Status: **complete Došen-rectangle and whole-mate follow-up from checkpoint
`d24ed5c`, including the final generic-owner cleanup; validated for a local
checkpoint**.

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
`PB-COMPAT-9`, `PB-DOC-10`, `PB-CLOSE-11`, `PB-RUNTIME-12`,
`PB-SIGMA-13`, `PB-NOCONE-14`, `PB-RECLOSE-15`, `PB-RECT-16`,
`PB-RECT-PROBE-17`, `PB-RECT-CLOSE-18`, `PB-GENERIC-19`, and
`PB-FINAL-DOC-20`, `PB-WHOLE-MATE-21`, and `PB-WHOLE-CLOSE-22`.

Infinity-Codex-Origin: session `01a02f68-6142-7e53-993a-4505aa8e2cbe`,
review response `0028_2026-08-28T07-43-06Z_01a04745-7f87-7750-a3e1-2bdea720554d.md`.

Infinity-Codex-Decision-Responses: `infinity-codex:01a02f68-6142-7e53-993a-4505aa8e2cbe:01a04745-7f87-7750-a3e1-2bdea720554d` and the user's
2026-08-28 approval/adjunction-usability clarification immediately following
that response; review response
`0034_2026-08-29T09-56-34Z_01a04ceb-e772-7b03-81df-ddf26832b2c4.md`
and the user's approval immediately following it.

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

The 2026-08-28 continuation adds one overriding computational constraint:
the primary notion of cone is the internal hom object
`Hom_{C/Y}(Σ_f(a),g)`. The pullback theory must not introduce a cone record
whose fields manually store a strict, pseudo, or lax commuting square. A
semantic adapter may consume equality/cell evidence later, but such evidence
is not primary pullback syntax.

The implemented correction makes the same distinction at the generic Sigma
boundary. Slice objects and slice arrows now use transparent observations of
one arbitrary-object/arrow Sigma facade. The pullback module consumes those
existing slice arrows; it does not reconstruct or store their component
triangle as pullback data.

The 2026-08-29 follow-up closes a distinct adjunction-computation gap. The
abstract `(ac)` Došen rectangles compute for rigid generic `F`, `G`, and `J`,
and the stable pullback mate cancellations compute at fixed endpoints, but the
two canonical rectangles obtained by substituting `F := Σ_u` and `G := u*`
do not survive transparent slice/`Op` projection in runtime matching. This
tranche must add only the two necessary post-projection instances, keep the
fixed-endpoint cancellations, and prove their identity-boundary routes join.

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

Its base-arrow action is postcomposition, hence `Sigma_f`. The implemented
presentation is definitionally usable at fibre and action positions:

```text
SliceSigma_catd(C) ≡ CommaFib_catd(id_C).
```

The existing transparent
`Op_catd(arrow_into_catd(C))`/`Op_func(into_restr_postcompose_func(f))` route
is its canonical reduced action; no second covariant slice-action owner was
introduced.

Three existing notions must remain distinct:

1. `Pullback_catd(E,F)` is substitution/reindexing of an already-given
   Cat-valued family along a functor. It exists without categorical
   pullbacks in the base category.
2. `SliceBaseChange_catd(PB)` is the new chosen categorical base-change
   family whose action sends an arrow over `Y` to its pullback over `X`.
3. `homd_int` classifies the dependent higher component already internal to a
   generic Sigma/slice arrow; it is not a pullback cone field and is not itself
   the choice of a pullback.

The generic whole `slice_domain_func : C/Y → C` was factored from the
commutative-algebra restriction module into the slice/presheaf layer,
preserving its whole body and downstream consumers.

## Implemented Generic Sigma Correction

The first checkpoint used slice-specific stable record projections because an
arbitrary object or arrow of `Sigma_cat(E)` did not expose its raw
`Struct_sigma` representation. That workaround has been replaced at the
generic owner in `emdash3_2.lp`:

- `sigma_obj_base` and `sigma_obj_fibre` are transparent observations of an
  arbitrary total object;
- `sigma_arrow_intro` is the stable arbitrary-endpoint constructor needed
  when `Hom(Sigma_cat(E),q,r)` cannot reduce through variable endpoints;
- `Sigma_proj1_func` and `sigma_arrow_fibre` expose its two arrow components;
- composition of two such constructors computes at the guarded
  `Sigma_cat(E)` owner; and
- the constant-family specialization has one post-projection instance after
  `Sigma_cat(Const(A))` has become `Product_cat`.

The category guard on generic constructor composition is essential. A
category wildcard incorrectly let the forward Sigma law match composition in
`Op_cat(Sigma_cat(E))` before the opposite-category reversal. The guarded law
and a durable conventional-slice composition consumer now enforce the correct
order: reverse through `Op` first, then compose in Sigma. `Terminal_cat` no
longer overlaps that law.

The older transparent `sigma_arrow` remains the raw constructor-visible
encoding. `sigma_arrow_fibre` retains its raw beta, but there is deliberately
no runtime fold from a literal `sigma_arrow_intro` to `sigma_arrow`: that fold
creates mixed raw/stable composition peaks. Both constructors have their own
intended projection computations, and arbitrary arrow eta remains absent.

Generic Sigma-map object action uses the stable point `sigma_map_obj`.
Literal action and both total-object projections compute; one proof-time
comparison relates it to whole `fapp0(sigma_map_func,–)`. The pullback module
adds only the narrower runtime projection for the canonical represented
postcomposition action. Consequently `slice_sigma_obj` preserves the domain
and postcomposes the structure arrow definitionally, and every former
`path_to_hom` domain/square recentering operation has been removed.

The conventional slice observations and `slice_arrow_intro` are now
transparent aliases of this generic Sigma facade. No slice-specific record
theory or arbitrary-arrow eta remains.

## Implemented Došen Rectangle Follow-Up

For `u:X→Y`, put `F=Σ_u` and `G=u*`. The selected runtime facade now
retains the whole `G` functor, its object action, and the whole unit/counit as
stable declaration-backed heads. Their ordinary off-diagonal projections are

```text
γᶜ(k) = tapp1(unit_u,k),
φᵃ(h) = tapp1(counit_u,h).
```

The public `slice_base_change_gamma` and `slice_base_change_phi` heads are
only these projections. They introduce no second unit, counit, adjunction, or
cone data. The two canonical `(ac)` rectangles now reduce at runtime:

```text
φᵃ(h) ∘ Σ_u(γᶜ(k)) ↪ h ∘ Σ_u(k),
u*(φᵃ(h)) ∘ γᶜ(k) ↪ u*(h) ∘ k.
```

The rules live at the exact restriction-oriented post-`Op` normal forms.
Owner-position probes showed that replacing those category and intermediate
object guards by readability aliases allows Lambdapi to reconstruct the
hidden target index `Y` as `X`. The explicit `Sigma_cat`, `sigma_map_obj`, and
stable `f*` guards are therefore subject-reduction discriminators, not
anti-SOP decoration.

Identity off-diagonal observations compute to the unit/counit components.
The generic composed-functor object beta and generic functor identity rule
already expose the required point and identity actions; two component triangle
joins then make both identity-boundary rectangles reduce to identity, agreeing
with the fixed-endpoint mate cancellations. A final owner-position removal
probe confirmed that the former pullback-specific composite-point unifier and
two selected identity-action rules were redundant, so all three are absent.
The transparent semantic
`G[h]∘η`/`ε∘F[k]` implementations remain proof-time usability endpoints and
do not become competing runtime normal forms.

The stable mate functors are whole functors and therefore retain generic
higher action. Their point observations and whole functors compare at proof
time with the explicit semantic formulas through non-opaque typed-reflexivity
paths, while runtime keeps the stable and semantic presentations distinct.
After the semantic whole bodies normalize through the canonical post-`Op`
shape—in particular, `slice_sigma_obj` becomes `sigma_map_obj` and
non-discriminating slots are `_`—the two whole unifiers match directly.

Both stable whole composites also compute:

```text
Γstable ∘ Φstable → id
Φstable ∘ Γstable → id.
```

These are guarded `comp_fapp0 Cat_cat` rules. Repeating the exact raw
Hom-category source, middle, and target is necessary: a wildcard-only probe
could reconstruct `a` from `b` after opposite normalization even though the
rule declaration typechecked. The guarded rules retain the original endpoints
and join the point cancellations. Generic `Adjunction_hom_prof_comparison`
continues to supply the varying-endpoint profunctor presentation; no additional
`OmegaEquivAlong` package is needed for the runtime computation.

## Selected Enhanced Interface

The selected declarations are summarized below; the active source owns their
exact Lambdapi spelling:

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
- the internal square `g ∘ π₂ ⇒ f ∘ π₁` is projected from that
  slice arrow, not stored or postulated as unrelated pullback data.

For a cone

```text
h : Hom_{C/Y}(Σ_f(a),g),
```

its adjoint transpose is

```text
f*(h) ∘ η_a : a → f*(g)
```

in `C/X`. Applying the whole slice-domain functor gives the ambient mediator
from `domain(a)` to `P`.

The primary transpose must remain whole in the cone arrow and retain higher
action. A bare primitive point `pullback_lift(a,b,q)` is not an accepted
highest-level owner. A stable point facade is allowed only as the canonical
projection of the selected whole operation when active runtime LHSs must
discriminate on it.

## Desired Triangular Computation

The generic adjunction triangles yield the primary strict computation in the
whole slice hom categories:

```text
untranspose(transpose(h)) ↪ h
transpose(untranspose(k))  ↪ k.
```

Generic Sigma-backed slice-arrow projections do not obstruct these
reductions. Hence the underlying second leg and higher component of
`untranspose(transpose(h))` reduce to the corresponding observations of the
same existing arrow `h`. Conversely, transposing the arrow induced by a slice
lift reduces to that lift, which is the internal uniqueness computation. No
pullback-specific constructor accepts either observation as input.

The ambient interpretation must respect the repository's higher-categorical
slice encoding. A morphism in `C/X` contains a directed triangle rather than a
postulated strict equality. Accordingly the first projection result is the
retained cell

```text
π₁ ∘ lift(h) ⇒ arrow(a),
```

exposed by `pullback_lift_fst_cell`. The second result is the whole recovered
Hom arrow and its generic Sigma projections. Raw ambient composites
`π₁ ∘ lift(h)` and `π₂ ∘ lift(h)` deliberately do not
rewrite to bare arrows in an arbitrary emdash category: such rules would erase
the directed higher cells and silently replace the internal higher-categorical
observation by a 1-categorical equality. A locally discrete adapter may later
turn these retained cells into ordinary categorical equalities when the
required discreteness evidence is supplied.

Thus the selected computation is strict at its actual internal owner: the two
Hom-category mate cancellations are runtime reductions, and the Sigma domain
and structure observations are definitional. This does not mean that the
first higher arrow of an arbitrary ambient emdash category is definitionally
an equality. The derived square cell belongs to that ambient category; it is
not a lax/pseudo/strict square field of a pullback cone record.

The stable mate heads remain propositionally connected to the explicit
unit/counit composites by non-opaque typed-reflexivity paths. Those paths are
the theorem-level route for consumers that need the semantic
`f*[h] ∘ η` or `ε ∘ Σ_f[k]` presentation; they do not introduce a runtime
fold.

Outside the stable mate triangles, the only pullback-specific runtime
projection is canonical represented postcomposition from whole Sigma action to
`slice_sigma_obj`; the remaining object/arrow laws belong to generic Sigma.
Naturality in Hom arrows, identity/composition of `f*`, and composition of
transposes remain generic. Do not add a pullback rule whose only content is
ordinary functoriality or adjunction naturality.

An `IsContr` factorization category centred at the selected mediator or a
terminal-object presentation of the cone category is a valuable semantic
verification layer. It does not replace the whole computational transpose.

## Alternative Presentations And Their Roles

| Presentation | Selected role |
| --- | --- |
| Raw `Hom(X,-)` with a second variance | Rejected as primary: it cannot choose the new pullback domain. |
| Per-arrow `Adjunction(Sigma_f,F)` | Minimal semantic probe/fallback; useful but not the final coherent whole interface. |
| Binary products in every slice `C/Y` | Equivalent compatibility theorem and possible adapter; not the first owner of `f*`. |
| Pullback-specific cospan/cone record with a square field | Rejected: the internal Hom arrow is already the commuting triangle. |
| Terminal object in a separately assembled cospan category | Later semantic verification/contractibility view only; it must derive from the internal Hom presentation. |
| Primitive cospan category and pullback-object functor | Possible later internalization, but unnecessary before the requested base-change action. |
| Bare primitive projections/lift | Rejected as primary because it caps higher action; allowed only as projections of whole owners. |
| Existing `Pullback_catd(E,F)` | Preserved as generic family substitution, a distinct construction. |

For locally discrete categories, the selected slice construction specializes
to ordinary categorical pullbacks. For a general emdash category, the existing
slice/comma totals retain directed higher cells; the feature is a chosen
internal base-change structure in that ambient category. Later comparison
with 1-categorical, pseudo, or groupoidal semantic presentations must be named
explicitly and must not add a square field to the primary cone syntax.

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
| `PB-SLICE-1` | complete, checkpoint `a055eb0` | `SliceSigma_catd(C)` is the existing `CommaFib_catd(id_C)` owner. Exact fibre, capped/full action, canonical postcomposition, and constructor-object probes are green without a duplicate runtime owner. |
| `PB-DOMAIN-2` | corrected after checkpoint `e9ac7e6` | Generic whole slice-domain functors remain factored into `emdash3_2_presheaves.lp`; the former slice-specific stable record surface has been replaced by transparent consumers of the generic arbitrary-object/arrow Sigma facade. The downstream commutative-algebra duplicates remain removed. |
| `PB-STRUCT-3` | complete, checkpoint `a055eb0` | `PullbackStructure(C)` owns one whole `SliceBaseChange_catd(PB):Catd(Op C)` with exact `Slice_cat` fibres and generic retained higher action. |
| `PB-ADJ-4` | complete, checkpoint `a055eb0` | Every internal `f:X→Y` supplies the existing `Adjunction(Σ_f,f*)`; readable unit/counit and component observations use the generic authority. |
| `PB-USABILITY-5` | complete implementation | Stable whole/point mate heads retain triangle discriminators. Two point and two canonical body-unfolded whole proof-time rules identify them with explicit unit/counit semantics; all non-opaque semantic paths are typed reflexivity and runtime remains distinct. |
| `PB-CONE-6` | corrected after checkpoint `e9ac7e6` | Pullback slice object/domain, two projections, derived square, whole Hom cone category, whole transpose/inverse, slice lift, ambient mediator, and first directed projection cell are implemented. The former pullback-specific cone constructors are removed. |
| `PB-TRIANGLE-7` | complete implementation | Both stable mate point cancellations and the generic Sigma-backed slice projections are green. Recovery and uniqueness compute on an arbitrary existing Hom object. Raw ambient 1-arrow collapses remain registered negatives because the internal slice stores directed higher arrows; no pullback-specific runtime join is warranted. Whole semantic Hom equivalence is separately owned by the generic adjunction profunctor comparison. |
| `PB-PSEUDO-8` | complete classification | Identity, composition, and higher action are retained by the one whole `Catd(Op C)` owner. No strictness claim or Gray-only pseudo-property dependency is added; an explicit invertible compositor certificate remains consumer-gated. |
| `PB-COMPAT-9` | complete classification | Products-in-slices, terminal-derived products, weighted pullbacks, opposite pushouts, `Π_f`, Beck–Chevalley, and Frobenius remain assumption-explicit later consumers. No concrete canonical-choice comparison is available in this tranche, so none is postulated. |
| `PB-DOC-10` | superseded by `PB-RECLOSE-15` | The checkpoint documentation/catalog described the former slice-record and literal-cone workaround. The correction tranche updates the same authorities and focused reviewers before a new closeout. |
| `PB-CLOSE-11` | complete, checkpoint `d572193` | Focused sources/reviewer, the affected moved-definition downstream module/example, central diagnostics, exact `1116/159` warnings, empty strict audits, catalog/health/document/script/diff hygiene, and worktree bootstrap are green. The validated implementation/documentation tranche is locally checkpointed. |
| `PB-RUNTIME-12` | complete implementation | `sigma_map_obj` owns arbitrary-point action, agrees with whole Sigma action at proof time, and has literal/base/fibre runtime observations. One narrow represented-postcomposition projection makes `slice_sigma_obj` preserve domains and postcompose structure arrows definitionally. Every pullback `path_to_hom` recentering helper is removed. |
| `PB-SIGMA-13` | complete implementation | Generic `sigma_obj_base`, `sigma_obj_fibre`, `sigma_arrow_intro`, and `sigma_arrow_fibre` replace the slice-specific record workaround. Sigma composition is guarded against `Op`; the constant-family `Product_cat` post-projection instance is executable; raw fibre projection remains; arbitrary eta and a mixed raw/stable literal fold are absent. |
| `PB-NOCONE-14` | complete implementation | `pullback_cone_cat` is exactly the internal Hom category. Both pullback-specific constructors that manually accepted a commuting cell/path are removed, and whole lift consumes an existing Hom object directly. |
| `PB-RECLOSE-15` | complete validation | Authority claims and focused generic-Sigma/slice/pullback consumers are synchronized. The final `1117/157` warning inventory is classified, strict audits are clean, the 2,338-check/115-area catalog and source-only health report are fresh, and proportional closeout is green for the containing local checkpoint. |
| `PB-RECT-16` | complete implementation | Both canonical pullback-specialized `(ac)` rectangles compute: `φᵃ(h)∘Σ_u(γᶜ(k)) → h∘Σ_u(k)` and `u*(φᵃ(h))∘γᶜ(k) → u*(h)∘k`. Whole `f*`, object action, unit, and counit now have stable declaration-backed heads; `γᶜ` and `φᵃ` remain their `tapp1` projections, not independent adjunction data. |
| `PB-RECT-PROBE-17` | complete | Exact post-`Op`/represented owner shapes are selected. Both general rectangles, generic-unit/counit spellings, fixed-endpoint mate cancellations, `γᶜ(id)`/`φᵃ(id)` component folds, and both component triangle joins are executable. Fully expanded semantic mate implementations deliberately remain runtime-distinct. |
| `PB-RECT-CLOSE-18` | complete validation | Active owner, reviewer, raw-generic specialization probe, central diagnostics, and strict audit are green. The `1268/157` warning boundary adds 151 classified projection-order reports in nine intended rules. Authorities, 2,344-check catalog, 326-file source-only health, and document hygiene are synchronized for the containing authorized checkpoint. |
| `PB-GENERIC-19` | complete correction | Owner-position removal probes confirm that `(u*∘Σ_u)[a]` is reconstructed by the generic composed-functor object beta and that both selected identity actions are owned by generic functor identity. The redundant pullback-specific unifier and two runtime rules are removed; both component triangles, owner, and reviewer remain green. The pullback warning boundary improves by 22 critical-pair reports to `1246/157`, and the strict LHS audit improves to 15 annotated slots across five intentional clauses. |
| `PB-FINAL-DOC-20` | complete documentation | The settled inventory distinguishes actual unit/counit transfors and their `tapp1` `γᶜ`/`φᵃ` observations from stable runtime heads, records generic ownership of composite and identity action, and distinguishes the generic whole Hom-profunctor comparison from the optional stable-mate whole-functor bridge. |
| `PB-WHOLE-MATE-21` | complete implementation | Canonical body-unfolded whole `Φ`/`Γ` unifiers use `sigma_map_obj` discriminators and `_` in non-discriminating slots, admit typed `eq_refl`, and keep runtime stable/semantic forms distinct. Two exact raw-Hom-guarded `comp_fapp0 Cat_cat` rules reduce `Γ∘Φ` and `Φ∘Γ` to identity functors. The rejected wildcard-only cancellation probe reconstructed the wrong endpoint after `Op`; it is not promoted. |
| `PB-WHOLE-CLOSE-22` | complete validation | Pullback owner/reviewer, slice-dependent-product downstream owner/reviewer, and central diagnostics are green. The guarded whole cancellations add 42 classified critical-pair reports, the whole unifiers add no warning family, and strict LHS audit remains clean. Catalog, health, authority, and diff evidence are synchronized in the containing checkpoint. |

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
| `D-PB-010` | superseded correction | Arbitrary slice objects/arrows do not Sigma-expand, but their reusable boundary belongs at generic Sigma. Slice object/domain/arrow observations and introduction are transparent consumers of `sigma_obj_base`, `sigma_obj_fibre`, `sigma_arrow_intro`, and `sigma_arrow_fibre`; no slice-specific record theory or arbitrary eta is installed. |
| `D-PB-011` | accepted and completed | Stable whole mate functors and point heads are necessary post-projection instances of the existing adjunction computation. Their point and whole cancellations are runtime rules; pointwise and whole semantic agreement is proof-time and exposed by non-opaque typed-reflexivity paths. They retain higher action while runtime stable/semantic forms remain distinct. The generic `Adjunction_hom_prof_comparison` remains the varying-endpoint profunctor presentation. |
| `D-PB-012` | accepted | The internal cone carrier is the whole hom category `Hom_{C/Y}(Σ_f a,g)`. Recovery and uniqueness compute on its arrow-term objects and now also at the stable whole mate-functor composites. The generic adjunction profunctor comparison supplies the parallel whole semantic presentation; no extra `OmegaEquivAlong` package is required. |
| `D-PB-013` | accepted | In an arbitrary emdash category, pullback projection laws retain directed cells. Raw `πᵢ ∘ lift` to bare-arrow rewrites are false runtime expectations and would impose unrequested strictness; no such join is promoted. |
| `D-PB-014` | accepted | Generic whole functoriality supplies current base identity/composition/higher action. Explicit pseudo invertibility and every product/weighted/dual/dependent comparison remain later assumption-explicit consumers. |
| `D-PB-015` | accepted and implemented | A pullback cone is an arrow in the internal Hom category, never a pullback-specific record carrying a manually supplied commutativity equality/cell. `pullback_cone_intro` and `pullback_cone_constructor` are removed. |
| `D-PB-016` | accepted and implemented | Propositional domain/square recentering is not an acceptable primary computational normal form when runtime Sigma action can expose the same endpoint. All pullback recentering paths are removed. Warnings remain diagnostic; subject reduction and typed reduction-order joins decide promotion. |
| `D-PB-017` | accepted | Strict computation means runtime mate beta/eta on Hom-arrow objects, both full Došen rectangles, and definitional Sigma observations, while the generic profunctor comparison owns whole semantic equivalence. The ambient higher square is derived from an existing slice arrow, not stored as a lax/pseudo/strict field. Univalence may compare later semantic structures but is not needed for this primary computation. |
| `D-PB-018` | accepted | Generic `sigma_arrow_intro` composition must discriminate on `Sigma_cat(K,E)`. A category wildcard is invalid because it matches `Op_cat` before variance reversal. Constant-family reduction is handled by one explicit `Product_cat` post-projection instance. |
| `D-PB-019` | accepted | The stable arbitrary-endpoint Sigma constructor and raw constructor-visible `sigma_arrow` remain distinct runtime forms. Both project computationally; a literal fold is rejected because it produces mixed raw/stable composition peaks. Arbitrary arrow eta remains absent. |
| `D-PB-020` | accepted diagnosis | Fixed-endpoint mate cancellation is not the complete pullback instance of Došen's `(ac)` calculus. At checkpoint `d24ed5c`, canonical `Σ_u`/`u*` rectangles passed runtime-negative probes after their discriminating functor shape unfolded. The follow-up closes that gap with the stable projection ladder and exact post-`Op` instances; proof-time comparison alone was insufficient. |
| `D-PB-021` | accepted and implemented | Canonical rectangle matching needs the stable projection ladder `SliceBaseChange_catd → slice_base_change_func → slice_base_change_obj` and stable whole unit/counit observations. Their `tapp1` projections are the stable `slice_base_change_gamma`/`slice_base_change_phi` heads. This is a declaration-backed computational facade, not a second adjunction theory. |
| `D-PB-022` | accepted | Readability aliases in the rectangle LHS reconstruct `Y` as `X` after opposite normalization. Promoted rules therefore use exact raw `Sigma_cat`/`sigma_map_obj` endpoint guards, annotated as subject-reduction discriminators. The remaining 129 resulting critical-pair reports are diagnostics, not vetoes; focused rules and both reduction orders are green. |
| `D-PB-023` | accepted and implemented | Generic `fapp0` composition and `fapp1` identity computation already own `(u*∘Σ_u)[a]` and the selected `Σ_u(id)`/`u*(id)` cases. Pullback-specific copies are unjustified when owner-position removal retains the two component triangles, so the former unifier and two rules are removed rather than retained as warning-producing joins. |
| `D-PB-024` | accepted and implemented | A stable specialized mate functor being callable at higher arrows did not by itself identify that action with the transparent semantic mate functor. Canonical body-unfolded whole unifiers now provide that proof-time identification, and exact raw-Hom-guarded `comp_fapp0 Cat_cat` rules reduce both stable whole composites to identity. The wildcard-only cancellation formulation is rejected because it reconstructed the wrong endpoint after `Op`. Generic `ProfComparison` remains available without requiring an additional `OmegaEquivAlong`. |

## Implementation Checkpoints

- `a055eb0` is the recovered, focused-green first computational checkpoint.
  It contains the slice substrate refactor, chosen whole base-change family,
  adjunction/mate calculus, pullback projections and square, and whole
  cone/lift interface. The source was reconstructed exactly from recorded
  successful patches after an external full-disk incident truncated the
  then-untracked new module; the focused module check passed immediately
  before the checkpoint.
- `d572193` is the validated implementation/documentation closeout checkpoint:
  it adds explicit mate-semantic paths, the complete reviewer and central
  diagnostics, warning-neutral SOP cleanup, authority prose, registrations,
  catalog, and source-only health synchronization.
- The containing local checkpoint records `PB-RUNTIME-12` through
  `PB-RECLOSE-15`: generic Sigma ownership replaces the slice-record
  workaround, all pullback recentering and cone-constructor code is removed,
  and the corrected scoped evidence below is synchronized.
- The next containing local checkpoint records `PB-RECT-16` through
  `PB-RECT-CLOSE-18`: the stable declaration-projection ladder, both full
  `(ac)` rectangles, their identity component joins, and the follow-up
  evidence below are synchronized.
- The final generic-owner cleanup records `PB-GENERIC-19` and
  `PB-FINAL-DOC-20`: generic composition/identity laws replace three redundant
  pullback clauses, and the semantic/stable whole-mate boundary is stated
  without treating optional `OmegaEquivAlong` packaging as missing adjunction
  semantics.
- The next containing checkpoint records `PB-WHOLE-MATE-21` and
  `PB-WHOLE-CLOSE-22`: both canonical whole unifiers, non-opaque reflexivity
  paths, exact guarded whole cancellations, their rejection control, and the
  synchronized evidence are active.

## Prior Checkpoint Evidence

Checkpoint `d572193` had the following evidence for the now-superseded first
implementation shape:

- `emdash3_2_presheaves.lp`, `emdash3_2_pullbacks.lp`, and
  `examples/pullbacks.lp` pass focused Lambdapi checking under the uniform
  90-second ceiling.
- The moved generic slice-domain owner is rechecked through
  `emdash3_2_commutative_algebra_ringed_space_restrictions.lp` and
  `examples/commutative_ring_ringed_space_restrictions.lp`.
- The affected aggregate `emdash3_2_checks.lp` passes once after importing the
  pullback module and adding its 13-check catalog area.
- Warning-enabled no-color checks report exactly
  `1275 = 1116 unjoinable critical pairs + 159 replaceable variables` for the
  kernel, modified presheaf substrate, and pullback module. The pullback
  tranche therefore adds no warning relative to the kernel. Both changed
  rule-bearing files have zero unreviewed strict LHS-audit candidates.
- The generated strict catalog contains 2,336 classified checks across 115
  areas, including 13 pullback checks, with zero unclassified statements.
- Source-only health metadata is fresh for 326 registered files with snapshot
  `sha256:720f360507519e4505d5408aaf196f263935f98d4d13d7b9ba2b21fbd640a0d0`;
  focused check evidence above is recorded separately rather than represented
  as a repository-wide health run.
- The source TOC has 87 valid headings; active-reference lint, 26 current-plan
  headers, 17 relevant Python tests, Python/shell syntax, generated catalog
  freshness, health freshness, and exact diff hygiene pass.
- The dedicated worktree's generated pnpm link graph has been restored and its
  workspace contract passes.

The user's scoped-validation policy excludes an unrelated full `make check`,
all-example sweep, health resume, or repository-wide CI run. No changed
cross-layer/release boundary requires those aggregates; the affected central
diagnostics and downstream consumer have been checked directly.

## Strict-Computational Correction Evidence

The completed correction has the following proportional evidence:

- the active kernel, presheaf substrate, pullback module, and focused
  `sigma_total`, `presheaf_facade`, and `pullbacks` reviewers pass under the
  uniform 90-second ceiling;
- a guarded owner-position Sigma probe passes quiet checking, with the generic
  composition law no longer matching either `Op_cat` or `Terminal_cat`;
- the conventional-slice composition reviewer confirms that opposite reversal
  precedes forward Sigma composition;
- the warning-enabled kernel, presheaf, and pullback-module inventories are
  all
  `1274 = 1117 unjoinable-critical-pair reports + 157 replaceable-variable
  reports`. Relative to checkpoint `d572193`'s `1116/159`, the correction adds
  one report: generic Sigma-constructor composition versus the earlier
  constant-family total-to-product fold. The later explicit `Product_cat`
  instance is exercised by a typed reviewer and closes the canonical
  post-projection term. The invalid `Op_cat` and `Terminal_cat` overlaps of the
  category-wildcard experiment are absent;
- the active generic Sigma/presheaf/pullback LHS audits have no unreviewed
  candidates (`63` annotated slots across `38` intentional kernel clauses);
- the affected central diagnostics pass and the fresh strict catalog contains
  2,338 classified checks across 115 areas, including 15 pullback checks, with
  zero unclassified statements;
- the moved slice substrate still passes through the directly affected
  commutative-ringed-space restriction owner and reviewer;
- source-only health metadata is fresh for 326 registered files at snapshot
  `sha256:4cc54a5084388daf8533e51d1a0631b56c75be0089344cc18913d5f988e3053c`;
  and
- source TOC, active-reference lint, current-plan headers, 17 relevant Python
  tests, catalog/health freshness, and exact diff hygiene pass.

Per the user's scoped-validation policy, this closeout does not run the
unrelated all-source check, all-example sweep, health resume, repository-wide
CI, print, or book aggregates.

## Došen Rectangle Follow-Up Evidence

Current proportional closeout evidence is:

- the active pullback owner, focused reviewer, affected central diagnostics,
  and an owner-position full-file probe pass under the 90-second ceiling;
- both stable public rectangles and the raw generic
  `unit_adj_transf`/`counit_adj_transf` spellings reduce to the selected
  smaller-cut right-hand sides;
- `γᶜ(id)` and `φᵃ(id)` compute to the unit/counit components, and both
  component triangles reduce to identity alongside the existing mate
  cancellations;
- the fully expanded semantic mate implementations remain registered runtime
  negatives, preserving the selected stable normal form;
- after whole-mate completion, the warning-enabled pullback inventory is
  `1445 = 1288 unjoinable-critical-pair reports + 157 replaceable-variable
  reports`. Relative to `d24ed5c`'s `1117/157`, all 171 additions are
  classified in nine intended rules: whole `f*` projection
  (12), `γᶜ`/`φᵃ` projections (3+3), left/right component triangles
  (27+12), F/G rectangles (48+24), and the two guarded whole cancellations
  (24+18). The two whole unifiers add no warning family. The removed selected
  identity copies still account exactly for the 22-report improvement over the
  earlier uncleaned rectangle checkpoint;
- strict LHS audit reports zero unreviewed candidates and 21 annotated slots
  across seven intentional pullback clauses; and
- the fresh strict catalog contains 2,359 classified checks across 116 areas,
  including 27 pullback checks and 9 slice-dependent-product checks, with zero
  unclassified statements;
- source-only health metadata is fresh for 328 registered owner/reviewer files at snapshot
  `sha256:612715e4cbae9d012908bf1a6c344df3ea2e878f4a471bf69341f3ff3b4a7253`;
  and
- source TOC, active references, current-plan headers, 17 relevant Python
  tests, catalog/health freshness, and exact diff hygiene pass.

Per the user's scoped-validation policy, this follow-up does not run the
unrelated all-source check, all-example sweep, health resume, repository-wide
CI, print, or book aggregates.

## Required Positive Evidence

At minimum, durable checks must establish:

- `SliceSigma_catd(C)[X]` has the exact `Slice_cat(C,X)` fibre;
- its action at `f` has type `C/X → C/Y` and agrees with canonical
  postcomposition;
- `SliceBaseChange_catd(PB)[X]` reduces to `Slice_cat(C,X)`;
- its action at `f^op` has type `C/Y → C/X` and retains another hom action;
- `slice_base_change_adjunction(PB,f)` is indexed by those exact functors;
- unit and counit components type at arbitrary slice objects;
- both abstract generic rectangles and their canonical `Σ_u`/`u*`
  specializations compute;
- the stable whole unit/counit and their `γᶜ`/`φᵃ` `tapp1` projections retain
  all declaration indices;
- required semantic/stable spellings type by `eq_refl` through selected
  usability rules while remaining runtime distinct;
- the chosen pullback object's domain and first projection compute;
- whole Sigma postcomposition projects to the stable arbitrary-object point,
  whose domain and structure arrow compute without equality transport;
- the second projection is derived directly from the counit and generic Sigma
  observations;
- the square is projected from the slice arrow;
- the cone transpose/mediator types and retains higher action;
- both pullback beta laws and eta/uniqueness compute at the Hom owner; and
- both identity-boundary rectangles join the unit/counit component triangles
  and fixed-endpoint mate cancellations; and
- locally discrete/closed examples reject false endpoint or variance
  identifications.

## Required Negative And Noncollapse Evidence

Durable negatives must reject at least:

- `Pullback_catd(E,F)` as the same symbol or type as categorical `f*`;
- a covariant `f* : C/X → C/Y` variance mistake;
- arbitrary `SliceBaseChange_catd(PB)` fibres collapsing without the structure
  head;
- proof-time usability becoming a runtime fold;
- a pullback-specific cone constructor accepting a square witness;
- generic base-change action collapsing to identity or composition by a
  pullback-specific rule;
- a point lift replacing its whole transpose/hom action;
- direct equality of independently selected product and pullback-derived
  product functors;
- the ambient higher square being replaced by a stored strict/pseudo/lax cone
  field; and
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
- the primary cone is only `Hom_{C/Y}(Σ_f(a),g)`, with no pullback-specific
  record or constructor carrying a square;
- beta/eta reach their intended canonical terms through generic triangles or
  narrowly justified projection instances;
- both full Došen `(ac)` rectangles reach their smaller-cut right-hand sides
  on canonical pullback terms;
- generic Sigma and canonical `Σ_f` domain/structure observations compute,
  and no hidden propositional bridge substitutes for that definitional
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
