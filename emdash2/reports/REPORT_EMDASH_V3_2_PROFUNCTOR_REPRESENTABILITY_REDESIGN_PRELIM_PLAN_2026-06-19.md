# EMDASH v3.2 Profunctor Representability Redesign Preliminary Plan

Date: 2026-06-19

Status: proposed redesign plan. This report records a retrospective
architecture review of the implemented profunctor, implication, weighted-limit,
duality, and join work. It is intentionally provisional. No migration described
here has yet replaced the active implementation in `emdash3_2.lp`.

The recommendations below are not a commitment to reproduce the obsolete
`cartierSolution13.lp` presentation. They are reassessed from the traditional
enriched-category and profunctor-equipment semantics, the current v3.2 kernel,
and focused Lambdapi feasibility evidence. Every proposed interface remains
subject to adjustment, replacement, or a prerequisite kernel side task as
implementation probes expose better normal forms.

The immediate motivation is the current implementation of:

```text
right_adjoint_preserves_weighted_limit_cov
right_adjoint_preserves_weighted_limit_cov_univ_transf
```

but the review treats those symbols as symptoms of broader architectural
issues rather than as an isolated rewrite cleanup.

## Assessment

The concern about the current preservation implementation is correct. It is
computationally useful, but it is not a satisfactory theorem architecture.

In the current implementation,
`right_adjoint_preserves_weighted_limit_cov` is a symbol without a definition.
Formally, it introduces an inhabitant rather than constructing one from `isl`
and `adj`. Its projection rules characterize some behavior, but do not turn it
into a derived lemma.

The large rewrite folding an explicit preservation composite to
`right_adjoint_preserves_weighted_limit_cov_univ_transf`, together with the
constructor-local cancellation rules for the resulting witness, compensates
for missing general infrastructure.

The preferred redesign is therefore not a theorem-local rewrite cleanup. It is
a strict closed-profunctor-equipment and representability layer whose immediate
algebra lives in fixed profunctor hom-categories. Endpoint-changing equipment
cells remain useful, but they should not be the default language for vertical
universal properties.

### Cartier Retrospective: Invertible Does Not Mean Identity

The obsolete `cartierSolution13.lp` did not avoid isomorphisms. It encoded
several isomorphisms as unnamed pairs of operations with direct beta/eta
rewrite rules:

```text
Eval_cov_transf / Lambda_cov_transf;
limit_cov_univ_transf / limit_cov_cone_transf;
Adj_cov_hom / Adj_con_hom.
```

For example, the two weighted-limit comparison maps compose to
`Id_transf`, but neither map is generally an identity transformation. The old
preservation symbol:

```text
righ_adjoint_preserves_limit_cov
```

was a transparent composite constructing the forward universal
transformation. It did not construct a complete new `limit_cov` witness with
both inverse maps and cancellation laws. Its apparent simplicity therefore
does not establish that right-adjoint preservation can generally be represented
by an identity-arrow isomorphism.

The old file did use genuine identity-arrow strictification in narrower
contexts:

```text
type_intro_hom(eq_refl) -> identity;
classification followed by decoding in the strict universe -> original data;
identity functors/transformations used as unchanged legs of larger composites.
```

This supports a bounded optimization principle:

```text
when a comparison path is reflexivity, its induced equivalence arrow computes
to identity;
```

but not the stronger and generally false principle:

```text
every representability, adjunction, or preservation comparison is itself an
identity arrow.
```

## Root Causes

### 1. Destructor-Only Weighted-Limit Witness

`WeightedLimit_cov` is a primitive classifier with projection/destructor
operations:

```text
weighted_limit_cov_univ_transf
weighted_limit_cov_cone_transf
```

There is no introduction constructor from a universal map, inverse map, and
inverse laws. Consequently, a theorem that should construct a weighted-limit
witness cannot simply assemble one from derived data.

### 2. Over-Externalized Universal Property

The current universal property quantifies externally over every:

```text
I : Cat
M : Functor I B.
```

Instead, one profunctor isomorphism at `M = id_B` should contain the fully
internalized universal property. Every shaped instance should then be derived
by profunctor reindexing.

The current witness therefore stores a family of maps for every `M` without
expressing naturality between those maps. An internalized profunctor
isomorphism would make this naturality part of the construction itself.

### 3. Missing Generic Invertibility Infrastructure

Invertible pairs are repeatedly implemented independently:

```text
weighted-limit universal/cone maps
adjunction transpose/untranspose
implication eval/lambda
opposite involutions
```

There is no generic computational strict-isomorphism or equivalence layer that
owns:

```text
forward and inverse projections
inverse cancellation
identity isomorphisms
symmetry
composition
functorial image of an isomorphism
```

This forces each subsystem to install its own cancellation rules.

The missing layer must not prematurely identify three different strengths:

```text
identity-arrow comparison;
strict isomorphism with on-the-nose inverse equations;
weak/recursive equivalence with higher cancellation data.
```

The present weighted-limit calculus uses strict inverse cancellation. A
globally univalent omega-categorical foundation is now the intended
architecture, but it is not yet active and should not be silently conflated
with this immediate strict interface.

### 4. General Equipment Composition Used For Vertical Maps

Weighted-limit calculations use the general six-endpoint
`Prof_comp_transf`, even when every relevant map is vertical inside one fixed
`Prof_cat(A,B)`.

This produces large endpoint-explicit terms and makes ordinary composition of
universal maps harder to reuse. The architecture does not clearly separate:

```text
vertical profunctor maps in one Prof_cat
general endpoint-changing equipment cells.
```

### 5. Closed Operations Lack Functorial Ownership

`Prof_imply_cov_transf` exists as a mixed-variance operation, but implication
is not exposed as the arrow action of a functor such as:

```text
Prof_imply_cov_func(W).
```

Consequently, implication cannot generically map isomorphisms. The
right-adjoint preservation proof manually builds the corresponding cell
instead.

### 6. The Adjunction Hom Bridge Is Also Over-Externalized

`Adjunction_prof_transpose` and `Adjunction_prof_untranspose` are parameterized
by an external probe:

```text
M : I -> A.
```

They should instead arise from one ambient hom-profunctor isomorphism, with the
component at arbitrary `M` obtained by reindexing.

### 7. No Generic Representability Abstraction

Weighted limits are representability statements, but the implementation has no
generic `RepresentedBy` layer. The weighted-limit subsystem directly encodes
the expanded universal-property components instead of reusing a general
representability concept.

## Recommended Architecture

### Semantic Strength: Three Distinct Equivalence Layers

Do not overload one `Equiv` name for three different constructions.

First, HoTT equivalence between groupoid/type classifiers:

```text
TypeEquiv(A,B)
```

should eventually be based on a map whose homotopy fibres are contractible, or
on an equivalent half-adjoint formulation. A pair of potentially different
left and right inverses is a useful bi-invertible presentation, but plain
quasi-inverse data should not silently be treated as the final
proof-irrelevant `IsEquivMap` predicate.

Second, strict isomorphism arrows in a category:

```text
StrictIso(C,x,y)
strict_iso_to
strict_iso_from
strict_iso_refl
strict_iso_sym
strict_iso_comp
strict_iso_fmap(F,i)
```

should consist of arrows `to : x -> y` and `from : y -> x` with equality paths
showing that both composites are identities. It needs an introduction form so
that preservation theorems can construct witnesses.

Third, weak omega-categorical equivalence arrows:

```text
OmegaEquiv(C,x,y)
omega_equiv_to
omega_equiv_left_inv
omega_equiv_right_inv
omega_equiv_left_cancel
omega_equiv_right_cancel
```

may use distinct left and right inverse arrows. Their cancellation data should
be equivalences recursively in the next hom-categories rather than necessarily
groupoid equality proofs. A feasible Lambdapi presentation may declare the
`OmegaEquiv` classifier first and expose the recursive structure through
separate destructor/constructor symbols.

There are canonical bridges:

```text
StrictIso(C,x,y) -> OmegaEquiv(C,x,y);
path x y         -> OmegaEquiv(C,x,y).
```

The path bridge should compute by equality induction:

```text
idtoequiv_cat(refl_x) -> omega_equiv_refl(x);
omega_equiv_to(omega_equiv_refl(x)) -> id_x.
```

Thus identity-arrow computation is the reflexivity specialization of the
general equivalence story. It must not replace nonidentity representability or
adjunction comparisons.

For the immediate weighted-limit redesign, two implementation routes remain
mathematically legitimate:

```text
strict-first:
  implement StrictIso and later map it into OmegaEquiv and paths;

path/equivalence-first:
  implement enough global univalence that representability is stored as a path,
  then recover the strict comparison maps needed by the current API.
```

The selected first implementation is `strict-first`. This is an implementation
priority, not a rejection of global univalence. The existing weighted-limit API
requires strict inverse comparison maps, and the current equality kernel can
already express the data of a strict isomorphism. Path ownership additionally
requires computational laws for `idtoequiv_cat` over path composition and
functorial path action.

The path/equivalence route should proceed in parallel and may become the deeper
owner after focused probes show that its projections reproduce the strict
comparison calculus without theorem-specific folds.

General `OmegaEquiv` is the largest foundational feasibility risk in this
layer. Recursive cancellation data is coinductive in character: a naive
ordinary inductive encoding risks describing only finite-height invertibility.
Initial probes should compare:

```text
primitive classifier plus recursive destructor/constructor heads;
finite-height OmegaEquiv_n approximations;
path-first equivalence under the global univalence bridge;
strict isomorphisms embedded into a deferred weak-equivalence interface.
```

No general `OmegaEquiv` encoding should block the strict weighted-limit
migration.

Broad raw composition-associativity rewrites should not be introduced merely
to support this layer.

Following the project's cut-elimination/Dosen discipline, associativity should
normally remain a metatheorem rather than a reduction rule. A carefully
oriented unification rule may identify:

```text
f o (g o h)  =?=  (f o g) o h
```

during elaboration or proof checking without making associativity part of
runtime normalization. The same possibility applies to
`comp_catd_fapp0`. Such rules still require focused probes: a broad
associativity unification hint can create ambiguous metavariable solutions or
unification loops even when it introduces no rewrite reduction. Constructor
projection computation should remain the primary mechanism.

### Foundational Decision: `Cat` Classifies Univalent Categories

The intended foundational contract is now:

```text
every C : Cat is an internally univalent omega-category;
Cat_cat is itself univalent.
```

This replaces the previously safer proposal to introduce a separate `UCat`
subuniverse. The implementation must distinguish the global availability of
univalence from full computation for every category constructor.

A schematic interface is:

```text
idtoequiv_cat [C] [x y] :
  (x = y) -> OmegaEquiv(C,x,y)

equivtoid_cat [C] [x y] :
  OmegaEquiv(C,x,y) -> (x = y)

idtoequiv_cat(equivtoid_cat(e)) -> e
equivtoid_cat(idtoequiv_cat(p)) -> p.
```

The exact ownership may instead use:

```text
CatUnivalence(C)
cat_univalence(C) : CatUnivalence(C)
```

with the two conversions as projections. The latter makes the foundational
assumption explicit and gives constructor-specific closure rules a stable
owner. Focused probes should compare both formulations.

Because `Cat_cat` is itself a `Cat`, the same interface specializes to:

```text
(A = B) ~= OmegaEquiv(Cat_cat,A,B).
```

The right side is an omega-categorical equivalence whose underlying arrow is a
functor `A -> B`. This is the category-universe analogue of Voevodsky
univalence.

This is a strong universe-level contract because:

```text
Cat_cat : Cat;
Obj(Cat_cat) = Cat;
Cat_cat is univalent.
```

Before making consistency or model-existence claims, the development must state
which interpretation is intended:

```text
an operational specification axiom;
a universe-stratified family Cat_i with Cat_i : Cat_(i+1);
or a deliberate impredicative/self-universe model.
```

This question does not block focused Lambdapi experiments, but it must remain
explicit rather than being hidden by the single current `Cat` classifier.

The groupoid/type universe requires a parallel but distinct interface:

```text
idtoequiv_grpd : (A = B) -> TypeEquiv(A,B)
ua_grpd        : TypeEquiv(A,B) -> (A = B).
```

It should not be defined by identifying `TypeEquiv` with
`OmegaEquiv(Grpd_cat,A,B)` until the truncation and higher-cell semantics of
`Grpd_cat` are settled.

The global categorical bridge also supplies the previously deferred
path-to-arrow inclusion:

```text
path_to_hom_fapp0(C,p)
  := omega_equiv_to(idtoequiv_cat(C,p));

Core_incl_func(C) : Core_cat(C) -> C.
```

Its object action is identity and its arrow action is the formula above. This
keeps the safe `path -> arrow` direction computational while univalence owns
the reverse `equivalence arrow -> path` direction.

### Incremental Univalence Closure

Global univalence can be available before every constructor has specialized
computation. Generic `idtoequiv_cat` and `equivtoid_cat` terms may remain stuck
for a constructor whose closure laws are deferred.

The development should add univalence closure in parallel with the existing
directed `Obj`/`Hom_cat` computation:

| Category constructor | Directed computation already owned by | Undirected/univalence closure |
| --- | --- | --- |
| `Path_cat(A)` | equality paths and `eq_trans` | path equivalences reduce to path algebra |
| `Op_cat(C)` | reversed homs/composition | equivalences reverse coherently |
| `Product_cat(A,B)` | projections and component homs | paths/equivalences compute componentwise |
| `Functor_cat(A,B)` | `fapp0`, `fapp1_func`, transformations | functor paths correspond to natural equivalences |
| `Catd_cat(K)` | natural family morphisms | family paths correspond to natural fibre equivalences |
| `Sigma_cat(E)` | total objects and directed dependent homs | total paths/equivalences decompose into base and fibre data |
| `Pi_cat(E)` | sections and section action | section paths/equivalences compute pointwise and naturally |
| `Prof_cat(A,B)` | Cat-valued families on `A^op x B` | profunctor paths correspond to natural pointwise equivalences |
| `Cat_cat` | functor categories | category paths correspond to omega-equivalences of categories |

Closure should follow existing semantic ownership. In particular:

```text
Catd_cat(K) = Functor_cat(K,Cat_cat);
Prof_cat(A,B) = Catd_cat(Op_cat(A) x B).
```

Their first univalence behavior should therefore be inherited from
`Functor_cat`, `Cat_cat`, `Op_cat`, and `Product_cat`, rather than duplicated by
new primitive closure heads. A specialized `Catd_cat` or `Prof_cat` head is
justified only when a focused projection or normalization test demonstrates
that the inherited route is too reducible, stuck, or expensive.

The initial implementation should target only the obvious/high-value cases:

```text
reflexivity/identity equivalence;
Path_cat;
Op_cat;
Product_cat;
Cat_cat at least at the generic univalence interface;
Prof_cat only as far as representability immediately consumes it.
```

Functor, family, Sigma/Pi, and full profunctor closure can remain stuck but
must be listed explicitly. This mirrors the existing kernel strategy: a
constructor may exist globally before its entire projection ladder computes.

### Univalence Rewrite Discipline

Global univalence must not be implemented by directly rewriting category
objects or arbitrary arrows:

```text
do not rewrite A to B merely because e : OmegaEquiv(Cat_cat,A,B);
do not identify every arrow with an equality path;
do not install evidence-irrelevance for equivalence witnesses by default.
```

Keep explicit stable heads:

```text
idtoequiv_cat;
equivtoid_cat;
omega_equiv_to;
omega_equiv_*_inv;
strict_iso_to_omega.
```

The principal generic computation should be cancellation of adjacent
conversion heads:

```text
idtoequiv_cat(equivtoid_cat(e)) -> e;
equivtoid_cat(idtoequiv_cat(p)) -> p;
idtoequiv_cat(refl) -> omega_equiv_refl;
omega_equiv_to(omega_equiv_refl) -> id.
```

Path-owned representability additionally requires explicit compatibility laws:

```text
idtoequiv_cat(eq_trans p q)
  -> omega_equiv_comp(idtoequiv_cat p,idtoequiv_cat q);

idtoequiv_cat(ap F p)
  -> omega_equiv_fmap(F,idtoequiv_cat p).
```

Equality induction alone computes only the reflexivity case. Without these
laws, composing representability paths gives concise syntax but leaves the
universal comparison arrow stuck.

Constructor-specific closure rules should be keyed on visible constructors
such as `Path_cat`, `Op_cat`, or `Product_cat`. Unification rules may help
compare path/equivalence normal forms during proof checking, but they must not
turn univalence into an unrestricted bidirectional conversion procedure.

### Separate Vertical Maps From Equipment Cells

Use fixed profunctor hom-categories as the default semantic layer:

```text
ProfMap(P,Q) := Hom_(Prof_cat A B)(P,Q)

ProfCell(R',F,R,G)
  := ProfMap(R', Prof_reindex(R,F,G)).
```

Universal properties and profunctor isomorphisms should use vertical
`ProfMap`s. Endpoint-changing constructions should use `ProfCell`s.

This is not an additional nonstandard notion: the right-hand side is exactly
the traditional restriction/base-change reading of an equipment cell. The
existing `Prof_transf_cat` is already definitionally close to this formula and
may remain the implementation of `ProfCell`.

The redesign should nevertheless avoid `ProfCell` whenever all endpoints are
fixed. In particular, strict isomorphisms, representability, implication
functoriality, and weighted-limit preservation should be composed using the
ordinary identity and composition operations of one `Prof_cat`. The
six-endpoint `Prof_comp_transf` should be a derived equipment facade used only
when endpoint change is semantically present.

This vertical-core architecture is preferable to retaining the generalized
Cartier-style shaped-cell calculus merely because it was previously successful.
If the standard `ProfMap` semantics suffices, it is both smaller and more
reusable.

### Companions, Conjoints, And Representables

Organize representables using the standard equipment interpretation. For a
functor `F : A -> B`, distinguish:

```text
Companion_prof(F) := Hom_prof_along(F,id_B)  : Prof(A,B)
Conjoint_prof(F)  := Hom_prof(F)             : Prof(B,A)
Unit_prof(A)      := Companion_prof(id_A)
                  := Conjoint_prof(id_A)
```

The existing symmetric form:

```text
Hom_prof_along(F,G)
```

is then the restriction of the unit/hom profunctor along the pair `(F,G)`.
This explains its legitimate role without making every downstream theorem use
two external shaped functors.

`Hom_prof`, `Unit_prof`, and `Hom_prof_along` may retain their current stable
normal forms. The conceptual companion/conjoint names can initially be
transparent aliases unless focused rewrite discrimination requires stable
heads.

### Functorial Representables And Closed Operations

Introduce or expose:

```text
Hom_prof_func(J,B)
  : Functor(Functor_cat J B, Prof_cat B J)

Prof_imply_cov_func(W)
  : Functor(Prof_cat A J, Prof_cat A J')

Prof_reindex_func(F,G)
  : Functor(Prof_cat A B, Prof_cat A' B')
```

`Prof_reindex_func` is already mostly active. The missing work is to make the
representable and closed operations equally functorial.

The eventual owner of implication variance should be a bifunctor of the
schematic form:

```text
Prof_imply_cov_func2 :
  Prof_cat(A,X) x Op_cat(Prof_cat(B,X))
    -> Prof_cat(A,B).
```

The fixed-weight unary `Prof_imply_cov_func(W)` is the correct first
implementation slice because it is exactly what weighted-limit preservation
needs. It should be obtained from, or remain compatible with, that eventual
mixed-variance owner.

Eventually tensor and implication should be packaged as an adjunction at the
functor level:

```text
Prof_tensor_right_func(W) ⊣ Prof_imply_cov_func(W).
```

The current eval/lambda operations would then become projections of this
reusable adjunction rather than an independent inverse-pair API.

## Weighted Limits As Representability

Define the weighted-cone profunctor:

```text
WeightedCone_prof(F,W)
  := Prof_imply_cov(Hom_prof(F),W).
```

Separate a representability property from a chosen representation:

```text
IsRepresentedBy_strict(P,L)
  := StrictIso(Prof_cat B J', P, Conjoint_prof(L)).

Representation_strict(P)
  := Sigma L, IsRepresentedBy_strict(P,L).
```

Under global univalence there is also a path-oriented formulation:

```text
IsRepresentedBy_path(P,L)
  := P = Conjoint_prof(L).

Representation_path(P)
  := Sigma L, IsRepresentedBy_path(P,L).
```

The two are connected by:

```text
idtoequiv_cat :
  IsRepresentedBy_path(P,L)
    -> OmegaEquiv(Prof_cat B J',P,Conjoint_prof(L));

equivtoid_cat :
  OmegaEquiv(Prof_cat B J',P,Conjoint_prof(L))
    -> IsRepresentedBy_path(P,L).
```

A strict isomorphism maps to the same `OmegaEquiv`. Recovering a
`StrictIso` from an arbitrary omega-equivalence is not automatic; it is valid
only for the strict fragment or with an additional strictification result.

Consequently, strict and weak weighted-limit properties must be distinguished:

```text
IsWeightedLimit_cov(F,W,L)
  := IsRepresentedBy_strict(WeightedCone_prof(F,W),L);

IsBiWeightedLimit_cov(F,W,L)
  := IsRepresentedBy_path(WeightedCone_prof(F,W),L).
```

The existing public `WeightedLimit_cov(F,W,L)` should remain strict during the
migration, initially as a compatibility name for `IsWeightedLimit_cov`.
Path/omega-equivalence representability must use an explicitly weak name such
as `IsBiWeightedLimit_cov` or `IsWeakWeightedLimit_cov`; it must not silently
change the meaning of the existing theorem.

A globally selected weighted-limit operation is a separate later layer:

```text
WeightedLimit_cov_chosen(F,W)
  := Sigma L, IsWeightedLimit_cov(F,W,L).
```

The preservation theorem currently needs only the property at an explicit
candidate `L`; it does not require globally chosen limits.

The selected first owner is strict representability:

```text
strict owner:
  compose strict isomorphisms directly;

path owner:
  compose paths by eq_trans/ap and derive comparison arrows through
  idtoequiv_cat.
```

The path owner is architecturally attractive because path composition,
symmetry, and functorial action can replace a separate strict-isomorphism
algebra. It is feasible only when `Prof_cat` univalence exposes comparison maps
with the required strict beta/eta behavior and with computation over
`eq_trans` and `ap`. Until those focused probes succeed, path
representability remains the weak/biweighted parallel layer rather than the
owner of the strict theorem.

The strict formulation removes the need for a primitive destructor-only
weighted-limit witness immediately. The path formulation may later provide a
deeper owner after a proven strictification/computation bridge.

For a shaped probe `M : I -> B`, derive:

```text
weighted_limit_cov_comparison_at(isl,M)
  := strict_iso_fmap(Prof_reindex_func(M,id_J'),isl)

weighted_limit_cov_univ_transf(isl,M)
  := strict_iso_to(weighted_limit_cov_comparison_at(isl,M))

weighted_limit_cov_cone_transf(isl,M)
  := strict_iso_from(weighted_limit_cov_comparison_at(isl,M)).
```

For a path-owned witness, replace `strict_iso_fmap` by path action:

```text
weighted_limit_cov_path_at(isl,M)
  := ap(Prof_reindex_func(M,id_J'),isl);

weighted_limit_cov_equiv_at(isl,M)
  := idtoequiv_cat(weighted_limit_cov_path_at(isl,M)).
```

The universal and cone maps are then projections of
`weighted_limit_cov_equiv_at`. They compute to identities when the
representability path is reflexivity, but are not generally identity arrows.

Thus the current shaped API can remain as a compatibility or presentation
layer, while its implementation is derived from one internalized
strict representability isomorphism.

## Adjunction Bridge

Define one ambient comparison, initially as a strict isomorphism:

```text
Adjunction_hom_prof_iso(adj,F) :
  StrictIso(
    Prof_cat A J,
    Hom_prof_along(left(adj),F),
    Hom_prof(right(adj) o F)).
```

The component at an arbitrary:

```text
M : I -> A
```

should be obtained by:

```text
strict_iso_fmap(
  Prof_reindex_func(M,id_J),
  Adjunction_hom_prof_iso(adj,F)).
```

The current `Adjunction_prof_transpose` and
`Adjunction_prof_untranspose` can initially remain as projections of this
isomorphism.

Merely packaging the current primitive transpose/untranspose pair would improve
ownership but would not remove its axiom-like status. The intended endpoint is
to define `Adjunction_hom_prof_iso` from:

```text
unit_adj_transf;
counit_adj_transf;
representable hom pre/postcomposition;
the existing triangle cut-elimination rules.
```

A temporary primitive ambient comparison is acceptable only as an explicitly
documented intermediate slice with this derivation remaining as tracked debt.

Under `Prof_cat` univalence, the same comparison induces:

```text
Adjunction_hom_prof_path(adj,F) :
  Hom_prof_along(left(adj),F)
    = Hom_prof(right(adj) o F)
  := equivtoid_cat(strict_iso_to_omega(Adjunction_hom_prof_iso(adj,F))).
```

If the path-oriented route proves computationally cleaner, this path should
become the semantic owner and the transpose/untranspose maps should be recovered
by `idtoequiv_cat`. The focused probe must check both beta directions before
changing ownership.

The first implementation may keep `F` external. The most-internal eventual
form should be a natural strict isomorphism between functors of:

```text
F : Functor_cat(J,B).
```

That later internalization would make naturality in `F` structural rather than
a collection of component rules. It is not necessary for the first replacement
of the externally quantified probe `M`.

## Derived Right-Adjoint Preservation

The preservation theorem can be the composition of three generic strict
isomorphisms:

```text
right_adjoint_preserves_weighted_limit_cov(isl,adj)
  :=
  Adjunction_hom_prof_iso(adj,L)
  o
  strict_iso_fmap(Prof_reindex_func(left(adj),id),isl)
  o
  strict_iso_fmap(
    Prof_imply_cov_func(W),
    strict_iso_sym(Adjunction_hom_prof_iso(adj,F))).
```

Semantically:

```text
Imply(Hom_A(-,right(F)),W)
  ~= Imply(Hom_B(left(-),F),W)
  ~= Hom_B(left(-),L)
  ~= Hom_A(-,right(L)).
```

This would be an actual definition. Its universal and cone projections would
follow from generic:

```text
strict_iso_to
strict_iso_from
strict_iso_comp
strict_iso_fmap
```

computations.

The theorem-specific large fold and constructor-local preservation rules would
then be unnecessary.

The globally univalent weak/biweighted alternative composes the corresponding
three paths:

```text
right_adjoint_preserves_biweighted_limit_cov_path(isl_path,adj)
  :=
  Adjunction_hom_prof_path(adj,L)
  · ap(Prof_reindex_func(left(adj),id),isl_path)
  · ap(
      Prof_imply_cov_func(W),
      inverse(Adjunction_hom_prof_path(adj,F))).
```

Here `·`, `inverse`, and `ap` are path composition, path reversal, and
functorial action on equality. The public universal and cone transformations
are obtained by applying `idtoequiv_cat` to this composite path.

This path formula should become the owner of the weak/biweighted theorem once
focused probes show that:

```text
idtoequiv_cat(path composite)
```

projects to the expected composite of universal maps without theorem-specific
folds. The strict-isomorphism composite remains the selected owner of the
strict theorem. It may also be converted to a path using univalence, but that
conversion does not identify arbitrary weak equivalence with strict
isomorphism.

The left-adjoint weighted-colimit theorem should remain a transparent dual of
this genuinely defined theorem.

## Focused Feasibility Evidence

Two focused probes already support the central internalization claim.

### Internalized Weighted-Limit Universal Cell

One ambient universal cell at the identity probe:

```text
Prof_imply_cov(Hom_prof(F),W)
  ->
Hom_prof(L)
```

was successfully reindexed along arbitrary:

```text
M : I -> B
```

to exactly the current shaped universal-map type.

Successful probe log:

```text
logs/probes/profunctor_weighted_limit_internalized_probe-20260619-135634.log
```

### Internalized Adjunction Hom Bridge

One ambient adjunction hom-profunctor cell was successfully reindexed along
arbitrary:

```text
M : I -> A
```

to exactly the current shaped transpose type.

Successful probe log:

```text
logs/probes/profunctor_weighted_limit_internalized_probe-20260619-135825.log
```

These probes establish that the proposed internalization does not require a
new base-reindexing mechanism. The missing work is the generic
isomorphism/representability and functorial-closed-operation infrastructure.

### Basic Equality And Strict-Isomorphism Data

A final-review probe established that the current kernel can already express:

```text
eq_sym by equality induction;
nondependent ap by equality induction;
Sigma-encoded strict-isomorphism data;
the reflexivity strict isomorphism.
```

Successful probe log:

```text
logs/probes/profunctor_representability_final_review_probe-20260619-184248.log
```

This narrows the strict-route risk. Basic data representation is feasible; the
remaining difficulty is generic strict-isomorphism composition, associativity
evidence, functorial image, and the desired projection normal forms.

They also support a selective internalization policy:

```text
internalize the probe M now;
internalize variation in F when naturality in F is consumed;
keep F, W, and L as external theorem parameters until simultaneous
internalization has a concrete downstream use.
```

Internalization should remove duplicated external quantification and expose
actual functorial action. It should not be pursued solely to maximize the
number of variables hidden inside one primitive.

## Feasibility Risks And Required Probes

### Strict Isomorphism Composition

The current kernel has equality induction and transitivity, generic identity
cuts, and specialized composition normal forms. It does not yet expose a
generic proof-level associativity theorem for arbitrary `comp_fapp0` or
`comp_catd_fapp0`.

Therefore the following must be probed before selecting a representation:

```text
strict_iso_intro
strict_iso_to
strict_iso_from
strict_iso_refl
strict_iso_sym
strict_iso_comp
strict_iso_fmap
```

The probe should compare:

```text
nested Sigma data with explicit equality evidence;
a dedicated strict-isomorphism classifier with constructor projections;
identity-arrow specializations for judgmentally equal endpoints.
```

The basic Sigma representation and reflexivity constructor have already passed
a focused probe. The next probe should concentrate on `strict_iso_comp`,
`strict_iso_fmap`, and their cancellation proofs rather than repeating the
object-data experiment.

If composition of equality evidence is blocked only by bracketing, first test a
narrow associativity unification rule. Do not turn arbitrary arrow
associativity into a global reduction rule.

### Global Equivalence And Univalence Infrastructure

Equivalence and univalence are no longer treated only as an optional
subuniverse side quest. They are part of the intended meaning of `Grpd`,
`Cat`, and `Cat_cat`. Their implementation must still be staged.

The groupoid/HoTT layer first needs focused designs for:

```text
eq_sym;
ap and dependent ap;
dependent groupoid-level Pi or an adequate classifier;
IsContr(A);
homotopy fibre of a map;
IsEquivMap(f);
TypeEquiv(A,B);
idtoequiv_grpd / ua_grpd.
```

Some initial probes may use bi-invertible map data before `IsContr` and
dependent Pi are available. That temporary representation must be documented
and connected to the final `IsEquivMap` interface rather than silently
becoming the definition.

The categorical layer must determine:

```text
whether OmegaEquiv is inductive, coinductive, or encoded by destructors;
how separate left and right inverse data are represented;
how cancellation recurses through higher hom-categories;
how StrictIso maps into OmegaEquiv;
how OmegaEquiv relates to the existing groupoid equality;
which computation is definitional and which is propositional;
whether CatUnivalence(C) is an explicit structure or direct global operations;
how constructor-specific univalence closure is registered incrementally.
```

The foundational commitment that every `C : Cat` is univalent may initially be
implemented by a generic primitive bridge with only reflexivity computation.
That is an explicit kernel assumption, not a derived closure theorem.
Constructor-specific computation should then progressively reduce the generic
bridge for `Path_cat`, `Op_cat`, products, functor categories, family
categories, Sigma/Pi, profunctors, and `Cat_cat`.

For weighted limits, the implementation should probe both:

```text
StrictIso representability;
path representability via univalence.
```

Strict representability is the selected first active implementation. Path
representability remains a parallel weak/biweighted experiment and may become a
deeper owner only after `idtoequiv_cat` computes over path composition and
functorial action. General `OmegaEquiv` and full univalence closure are not
prerequisites for replacing the current strict preservation theorem.

### Completeness Boundary

This redesign addresses:

```text
the global univalence contract for Cat and Cat_cat;
the initial TypeEquiv/OmegaEquiv distinction and path bridges;
vertical profunctor maps and endpoint restriction;
representables and their functoriality;
closed implication functoriality;
strict representability of weighted limits;
right-adjoint preservation;
left-adjoint preservation by duality.
```

It does not by itself provide:

```text
coend/end semantics for tensor and implication;
general tensor associators and unitors;
weak/pseudo weighted limits;
full computation of univalence for every category constructor;
all HoTT laws for Sigma, Pi, identity, and universe types;
generic directed-inductive types or a semantic collage construction.
```

The first two univalence interfaces are part of the foundational architecture;
their complete constructor-specific computation remains incremental rather than
a prerequisite for the first representability migration.

## Migration Strategy

The work should proceed on two tracks. Global univalence remains a foundational
commitment, but it is not on the critical path for repairing strict weighted
limits.

### Critical Path: Strict Representability

1. Expose vertical `ProfMap` composition as the default algebra and treat
   endpoint-changing `ProfCell` as restriction into a fixed target.
2. Promote the already-probed strict-isomorphism data representation and probe
   `strict_iso_comp`, `strict_iso_fmap`, identity fast paths, and any narrowly
   required associativity unification support.
3. Add companion/conjoint presentation names where they clarify variance, and
   add `Hom_prof_func`.
4. Add fixed-weight `Prof_imply_cov_func`, checked against the eventual
   mixed-variance bifunctor signature.
5. Introduce `IsRepresentedBy_strict`,
   `IsWeightedLimit_cov`, and a compatibility presentation of the existing
   `WeightedLimit_cov`.
6. Define the ambient `Adjunction_hom_prof_iso` from unit, counit,
   representable hom action, and triangle computation. Use a temporary
   primitive only if a focused probe demonstrates a missing lower-level
   constructor.
7. Define `right_adjoint_preserves_weighted_limit_cov` as the
   three-strict-isomorphism composite.
8. Derive the existing shaped universal/cone API by reindexing the one ambient
   strict isomorphism.
9. Compare all current regression checks against the new implementation.
10. Retire the primitive preservation theorem and its large theorem-specific
    rewrite rules only after the replacement passes `make check`, `make health`,
    and `make ci`.
11. Keep left-adjoint preservation as a transparent dual of the genuinely
    defined right-adjoint theorem.

### Parallel Track: Equivalence And Computational Univalence

1. Record the foundational contract that `Cat` classifies univalent
   omega-categories and that `Cat_cat` is univalent, including the unresolved
   universe-stratification/impredicativity interpretation.
2. Add the minimum equality infrastructure: `eq_sym`, `ap`, dependent `ap`,
   and the groupoid-level classifiers needed for `TypeEquiv`.
3. Design `TypeEquiv` using `IsEquivMap`, with temporary bi-invertible data only
   as an explicitly bridged prototype.
4. Probe `OmegaEquiv` using primitive recursive destructors, finite-height
   approximations, or path-first ownership. Do not require a final solution for
   the strict profunctor migration.
5. Add `idtoequiv_cat`, `equivtoid_cat`, reflexivity computation, and the
   `Core_cat(C) -> C` path-to-arrow bridge.
6. Add compatibility computation for path composition and functorial `ap`
   before using paths as computational owners.
7. Add univalence closure by semantic ownership: first `Path_cat`, `Op_cat`,
   `Product_cat`, `Functor_cat`, and `Cat_cat`; inherit `Catd_cat` and
   `Prof_cat` behavior through their definitions whenever feasible.
8. Introduce `IsBiWeightedLimit_cov` or `IsWeakWeightedLimit_cov` as the
   path/omega-equivalence representability property.
9. Define the path-based right-adjoint-preservation theorem and compare its
   projected maps against the strict theorem.
10. Promote path ownership only if those projections compute without
    theorem-specific folds and a strictification theorem justifies any claimed
    strict result.

### Later Consolidation

After the two tracks stabilize:

1. Refactor eval/lambda and other inverse-pair APIs onto the reusable strict or
   weak equivalence infrastructure according to their actual semantic strength.
2. Refactor weighted colimits through duality without duplicating the proof
   calculus.
3. Add chosen representation/limit operations only when a downstream consumer
   needs:

```text
Representation_strict(P);
WeightedLimit_cov_chosen(F,W).
```

4. Extend constructor-specific univalence closure and document every remaining
   stuck projection.

## Acceptance Criteria

The strict migration is complete only when all of the following hold:

```text
right_adjoint_preserves_weighted_limit_cov has a defining body;
its forward and inverse maps are projections of constructed generic data;
their beta/eta laws follow from generic StrictIso computation;
the one ambient witness reindexes to every shaped probe M;
the old theorem-specific exact-syntax fold is unnecessary;
the preserved cone is as explicit and computational as the universal map;
left-adjoint colimit preservation remains a transparent dual;
all existing diagnostics pass without hidden primitive replacement axioms.
```

The implementation must also document any temporary primitive, especially:

```text
Adjunction_hom_prof_iso;
strict_iso_comp/fmap;
closed implication arrow action.
```

For each temporary primitive, the report/code should state its intended
derivation and the missing lower-level constructor or computation law.

The internalization target is:

```text
one ambient representability comparison internalizes the probe M;
variation in F is internalized when a natural comparison functor is consumed;
F, W, and L remain theorem parameters until simultaneous internalization has a
concrete downstream use.
```

The weak/path track is computationally ready only when:

```text
idtoequiv_cat computes on reflexivity, path composition, and ap;
path-owned representability projects to the expected nonidentity maps;
strict and weak weighted-limit names remain semantically distinct;
constructor-inherited Prof_cat univalence does not require duplicate broad
rewrite rules.
```

Every migration slice should use focused probes, then `make check`; substantial
handoffs should refresh `make health` and pass `make ci`.

## Current Provisional Conclusion

The object-level `Prof_tensor` and `Prof_imply_cov` may remain primitive while
coend/end semantics are absent. Their primitivity is not the main problem.

The missing architectural pieces are:

```text
global but incrementally computational univalence for Cat and Cat_cat;
separate TypeEquiv, StrictIso, and OmegaEquiv layers;
functorial ownership of representables and closed operations;
vertical ProfMap ownership beneath endpoint-changing ProfCell;
generic strict computational isomorphisms with identity-arrow fast paths;
generic representability;
internalized rather than externally repeated universal properties;
companion/conjoint organization of representables;
an explicit boundary between strict and weak weighted-limit semantics.
```

The final review selects the strict vertical-representability route as the
immediate implementation and keeps computational univalence as a parallel
foundational track. This is currently the best balance of traditional
semantics, full computation, internalization, kernel compatibility, and
feasibility.

The redesign should still be evaluated globally against tensor, co-Yoneda,
implication, weighted limits, duality, and join usage. It must not be
implemented as a theorem-local cleanup. The next work is the first critical-path
probe: vertical `ProfMap` ownership together with `strict_iso_comp` and
`strict_iso_fmap`.
