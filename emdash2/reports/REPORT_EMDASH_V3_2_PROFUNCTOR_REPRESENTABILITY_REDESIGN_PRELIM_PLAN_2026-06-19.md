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

The present weighted-limit calculus uses strict inverse cancellation. A future
omega-categorical equivalence and univalence layer may be more foundational,
but it is not yet available and should not be silently conflated with this
immediate strict interface.

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

### Semantic Strength: Identity, Strict Isomorphism, And Equivalence

For the immediate redesign, use an explicitly strict computational interface:

```text
StrictIso(C,x,y)
strict_iso_to
strict_iso_from
strict_iso_refl
strict_iso_sym
strict_iso_comp
strict_iso_fmap(F,i)
```

`StrictIso(C,x,y)` should initially mean arrows:

```text
to   : x -> y
from : y -> x
```

with both composites equal to the corresponding identity arrows. It must have
an introduction form so that preservation theorems can construct witnesses,
rather than only project behavior from primitive inhabitants.

When `x` and `y` reduce to the same object and the intended maps reduce to
identity arrows, use `strict_iso_refl` or a similarly narrow identity-arrow
constructor. This stronger case should be preferred whenever it genuinely
applies because its projections and cancellations can compute without any
general inverse or associativity proof. It must not be asserted for a general
weighted-limit or adjunction comparison merely to simplify normalization:
those comparisons are not ordinarily identity arrows.

An eventual equivalence layer may have a different shape. For example:

```text
Equiv(C,x,y)
equiv_to
equiv_left_inv
equiv_right_inv
equiv_left_cancel
equiv_right_cancel
```

Here `equiv_left_inv` and `equiv_right_inv` may be distinct arrows from `y` to
`x`. Their cancellation witnesses need not be equality proofs: they may
themselves be recursively expressed by equivalences in the appropriate next
hom-category. This is compatible with a later account of:

```text
univalent category: object paths correspond to equivalences;
univalent Cat universe: paths in Cat correspond to category equivalences.
```

It is plausible that this recursive `Equiv` interface will eventually be the
deeper foundation and that `StrictIso` will be a strict specialization.
However, it is not yet established that a coinductive/co-recursive equivalence
encoding is easier to implement in Lambdapi. It depends on unresolved equality,
universe, productivity, and higher-coherence design. It should be explored as a
separate foundational side quest rather than made a prerequisite for replacing
the current preservation axiom.

This leaves two legitimate implementation branches:

```text
strict-first:
  implement StrictIso directly and later embed it into Equiv;

equivalence-first:
  implement Equiv, then define the immediate weighted-limit interface by a
  strict/identity specialization whose maps and cancellations compute more
  strongly than a general equivalence.
```

The first focused probes should compare these branches. The plan defaults to
the strict-first branch only because it matches the active theorem's required
computation and has fewer currently unresolved dependencies, not because
`StrictIso` is assumed to be the final foundational notion.

The first strict layer might use nested `Σ_` data and equality proofs, or a
dedicated generic computational structure. Focused probes must decide which
representation gives acceptable normal forms.

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

Define generic representability:

```text
RepresentedBy(P,L)
  := StrictIso(Prof_cat B J', P, Conjoint_prof(L)).
```

Then define:

```text
WeightedLimit_cov(F,W,L)
  := RepresentedBy(WeightedCone_prof(F,W),L).
```

This removes the need for a primitive destructor-only weighted-limit witness.

For a shaped probe `M : I -> B`, derive:

```text
weighted_limit_cov_iso_at(isl,M)
  := strict_iso_fmap(Prof_reindex_func(M,id_J'),isl)

weighted_limit_cov_univ_transf(isl,M)
  := strict_iso_to(weighted_limit_cov_iso_at(isl,M))

weighted_limit_cov_cone_transf(isl,M)
  := strict_iso_from(weighted_limit_cov_iso_at(isl,M)).
```

Thus the current shaped API can remain as a compatibility or presentation
layer, while its implementation is derived from one internalized
representability isomorphism.

## Adjunction Bridge

Define one ambient isomorphism:

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

The first implementation may keep `F` external. The most-internal eventual
form should be a natural strict isomorphism between functors of:

```text
F : Functor_cat(J,B).
```

That later internalization would make naturality in `F` structural rather than
a collection of component rules. It is not necessary for the first replacement
of the externally quantified probe `M`.

## Derived Right-Adjoint Preservation

The preservation theorem should be the composition of three generic
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

If composition of equality evidence is blocked only by bracketing, first test a
narrow associativity unification rule. Do not turn arbitrary arrow
associativity into a global reduction rule.

### Equivalence And Univalence Side Quest

A recursive `Equiv`, univalent categories, and univalence of `Cat_cat` are
globally relevant to the project and may ultimately subsume strict
isomorphisms. They are not currently a proven prerequisite for the strict
weighted-limit theorem.

A separate probe/report should determine:

```text
whether Equiv is inductive, coinductive, or encoded by destructors;
how separate left and right inverse data are represented;
how cancellation recurses through higher hom-categories;
how Equiv relates to the existing groupoid equality;
which computation is definitional and which is propositional;
whether a univalence bridge is an axiom, structure, or derived construction.
```

Until that design is validated, the representability migration should use the
smallest strict interface required by the active theorem.

### Completeness Boundary

This redesign addresses:

```text
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
recursive omega-categorical equivalence or univalence;
generic directed-inductive types or a semantic collage construction.
```

Those remain compatible follow-up layers rather than hidden obligations of the
first migration.

## Migration Strategy

1. Record the immediate semantic target as strict Cat-enriched weighted limits.
   Probe strict-first versus equivalence-first ownership, while reserving full
   recursive `Equiv` and univalence for a separately validated side quest.
2. Expose vertical `ProfMap` composition as the default algebra and treat
   endpoint-changing `ProfCell` as restriction into a fixed target.
3. Probe `StrictIso`, its identity-arrow specialization, composition, functorial
   image, and any narrowly required associativity unification support.
4. Add companion/conjoint presentation names where they clarify variance, and
   add `Hom_prof_func`.
5. Add fixed-weight `Prof_imply_cov_func`, checked against the eventual
   mixed-variance bifunctor signature.
6. Introduce `RepresentedBy` and a parallel internalized weighted-limit type.
7. Package the ambient transpose pair as `Adjunction_hom_prof_iso`, with shaped
   components derived by reindexing.
8. Define the new preservation theorem using the three-strict-isomorphism
   composite.
9. Derive the existing shaped API as compatibility projections.
10. Compare all current regression checks against the new implementation.
11. Retire the primitive preservation theorem and its large theorem-specific
    rewrite rules only after the replacement passes all gates.
12. Refactor eval/lambda, weighted colimits, and other inverse-pair APIs onto
    the same generic infrastructure where this improves computation and
    ownership.

## Current Provisional Conclusion

The object-level `Prof_tensor` and `Prof_imply_cov` may remain primitive while
coend/end semantics are absent. Their primitivity is not the main problem.

The missing architectural pieces are:

```text
functorial ownership of representables and closed operations;
vertical ProfMap ownership beneath endpoint-changing ProfCell;
generic strict computational isomorphisms with identity-arrow fast paths;
generic representability;
internalized rather than externally repeated universal properties;
companion/conjoint organization of representables;
an explicit boundary between strict results and future Equiv/univalence.
```

The proposed redesign should be evaluated globally against tensor,
co-Yoneda, implication, weighted limits, duality, and join usage. It should not
be implemented as a theorem-local cleanup. The next work on this report is to
refine the proposal with more detailed type signatures, critical-pair and
termination analysis, unification-rule risk analysis, compatibility strategy,
and focused feasibility probes.
