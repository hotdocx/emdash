# EMDASH v3.2 Profunctor Representability Redesign Preliminary Plan

Date: 2026-06-19

Status: proposed redesign plan. This report records a retrospective
architecture review of the implemented profunctor, implication, weighted-limit,
duality, and join work. It is intentionally provisional. No migration described
here has yet replaced the active implementation in `emdash3_2.lp`.

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

### 3. Missing Generic Isomorphism Infrastructure

Invertible pairs are repeatedly implemented independently:

```text
weighted-limit universal/cone maps
adjunction transpose/untranspose
implication eval/lambda
opposite involutions
```

There is no generic computational `Iso` or `Equiv` layer that owns:

```text
forward and inverse projections
inverse cancellation
identity isomorphisms
symmetry
composition
functorial image of an isomorphism
```

This forces each subsystem to install its own cancellation rules.

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

### Generic Computational Isomorphisms

Introduce a generic computational isomorphism layer for any category:

```text
Iso(C,x,y)
iso_to
iso_from
iso_refl
iso_sym
iso_comp
iso_fmap(F,i)
```

This layer should have an introduction form. An initial implementation might
use nested `Σ_` data and equality proofs, or a dedicated generic computational
structure. Focused probes must decide which representation gives acceptable
normal forms.

Broad raw composition-associativity rewrites should not be introduced merely
to support this layer. The intended computation should be owned by the
isomorphism constructors and their projections.

### Separate Vertical Maps From Equipment Cells

Use a clear conceptual distinction:

```text
ProfMap(P,Q) := Hom_(Prof_cat A B)(P,Q)

ProfCell(R',F,R,G)
  := the current endpoint-changing Prof_transf_cat construction.
```

Universal properties and profunctor isomorphisms should use vertical
`ProfMap`s. Endpoint-changing constructions should use `ProfCell`s.

The existing `Prof_transf_cat` may remain the semantic owner for both initially,
but APIs and normal forms should distinguish its identity-endpoint
specialization from genuinely endpoint-changing cells.

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
  := Iso(Prof_cat B J', P, Hom_prof(L)).
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
  := iso_fmap(Prof_reindex_func(M,id_J'),isl)

weighted_limit_cov_univ_transf(isl,M)
  := iso_to(weighted_limit_cov_iso_at(isl,M))

weighted_limit_cov_cone_transf(isl,M)
  := iso_from(weighted_limit_cov_iso_at(isl,M)).
```

Thus the current shaped API can remain as a compatibility or presentation
layer, while its implementation is derived from one internalized
representability isomorphism.

## Adjunction Bridge

Define one ambient isomorphism:

```text
Adjunction_hom_prof_iso(adj,F) :
  Iso(
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
iso_fmap(Prof_reindex_func(M,id_J),Adjunction_hom_prof_iso(adj,F)).
```

The current `Adjunction_prof_transpose` and
`Adjunction_prof_untranspose` can initially remain as projections of this
isomorphism.

## Derived Right-Adjoint Preservation

The preservation theorem should be the composition of three generic
isomorphisms:

```text
right_adjoint_preserves_weighted_limit_cov(isl,adj)
  :=
  Adjunction_hom_prof_iso(adj,L)
  o
  iso_fmap(Prof_reindex_func(left(adj),id),isl)
  o
  iso_fmap(
    Prof_imply_cov_func(W),
    iso_sym(Adjunction_hom_prof_iso(adj,F))).
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
iso_to
iso_from
iso_comp
iso_fmap
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

## Migration Strategy

1. Add generic vertical `Iso` infrastructure and validate its computation.
2. Add `Hom_prof_func` and fixed-weight `Prof_imply_cov_func`.
3. Introduce `RepresentedBy` and a parallel internalized weighted-limit type.
4. Package the current transpose pair as `Adjunction_hom_prof_iso`.
5. Define the new preservation theorem using the three-isomorphism composite.
6. Derive the existing shaped API as compatibility projections.
7. Compare all current regression checks against the new implementation.
8. Retire the primitive preservation theorem and its large theorem-specific
   rewrite rules only after the replacement passes all gates.
9. Refactor eval/lambda, weighted colimits, and other inverse-pair APIs onto
   the same generic infrastructure where this improves computation and
   ownership.

## Current Provisional Conclusion

The object-level `Prof_tensor` and `Prof_imply_cov` may remain primitive while
coend/end semantics are absent. Their primitivity is not the main problem.

The missing architectural pieces are:

```text
functorial ownership of representables and closed operations;
generic computational isomorphisms;
generic representability;
internalized rather than externally repeated universal properties;
a clear vertical-map versus endpoint-changing-equipment-cell distinction.
```

The proposed redesign should be evaluated globally against tensor,
co-Yoneda, implication, weighted limits, duality, and join usage. It should not
be implemented as a theorem-local cleanup. The next work on this report is to
refine the proposal with more detailed type signatures, critical-pair and
termination analysis, compatibility strategy, and focused feasibility probes.
