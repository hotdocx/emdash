# Native Duality: Mathematical Specification

Date: 2026-09-12

Status: active semantic specification; implementation follows the living plan

Parent: [native universality and homology plan](TYPESCRIPT_EMDASH_NATIVE_UNIVERSALITY_AND_HOMOLOGY_PLAN.md)

## Current Direction

The user has clarified the priority: formulate an ordinary, coherent and
usable mathematical theory of opposites/duality. Prototype global
strictness rules and handcrafted Empty derivations are outside the current
work queue. The separate `goal/opaque-action-profile-classifiers-v3.2`
branch will be integrated after this goal, not during it.

This document specifies the mathematics independently of those rewrite
issues. It starts with strict ω-categories and strict ω-functors, where
dimension-selected duality is unambiguous. Cartesian, lax and oplax
transformation contexts are named when they matter. Their mathematical
distinction does not launch a strictness-rule migration here.

Native hom_int/homd_int remain foundational syntactic owners. The formulas
below interpret and organize their operations; they do not redefine them
through an external total-category Hom projection.

## 1. Reverse A Specified Set Of Dimensions

For S⊆ℕ₊, let D_S(C) reverse the n-cells of C exactly when n∈S. Write

```text
S↓ = {n≥1 | n+1∈S},       S↑ = {n+1 | n∈S}.

D_∅ = Id
D_S D_T = D_(S△T)
D_S² = Id.
```

The last two formulas express coherent involutions; one can choose strict
representatives for this dimension calculus. They do not require an
implementation to erase every distinct presentation by rewriting.

Objects are unchanged. The recursive Hom formula is

```text
Hom_(D_S C)(x,y) = D_(S↓)(Hom_C(y,x))    if 1∈S,
Hom_(D_S C)(x,y) = D_(S↓)(Hom_C(x,y))    if 1∉S.
```

This gives the intended principal operations:

| Name | Reversed dimensions | Hom formula |
| --- | --- | --- |
| O(C), proposed public Op_cat(C) | all n≥1 | O(Hom_C(y,x)) |
| R(C), prototype CoAbove2_cat(C) | all n≥2 | O(Hom_C(x,y)) |
| T(C)=R(O(C)) | dimension 1 only | Hom_C(y,x) |
| D₂(C) | dimension 2 only | T(Hom_C(x,y)) |
| D≥3(C) | all n≥3 | R(Hom_C(x,y)) |
| D₁₂(C)=D≥3(O(C)) | dimensions 1 and 2 | T(Hom_C(y,x)) |

In particular, the user's proposed recursive rule has exactly the intended
total-duality meaning:

```text
Hom_cat (Op_cat A) X Y  ↪  Op_cat (Hom_cat A Y X).
```

Ordinary Hom contravariance uses T, since reversing its source variable
should reverse the 1-arrows in that variable while keeping the higher Hom
action in its required direction. Total O and transpose T consequently
have different jobs, even though they coincide on an ordinary 1-category.

## 2. Functors And The Shift At The Universe

Every strict F:A→B has a strict dual

```text
D_S F : D_S A → D_S B.
```

It has the same object assignment. Its full Hom action is D_(S↓) applied
to the original Hom action, with the two endpoints exchanged exactly when
1∈S. This specifies the complete action recursively, including every
higher dimension.

Let 𝒞 be the Cartesian ω-category of strict ω-categories, strict
ω-functors and strict higher transformations. Write [A,B]ₛ for its Hom.
Since D_S preserves Cartesian products, it transports Cartesian internal
Homs:

```text
D_S([A,B]ₛ) ≅ [D_S A,D_S B]ₛ.
```

The corresponding internal universe operation has type

```text
d_S : D_(S↑)(𝒞) → 𝒞.
```

The shift is forced by the dimensions: a component k-cell of a higher
transformation is a (k+1)-cell in the universe. Functors remain covariant;
the reversal of their transformations starts one dimension higher.

The three useful instances are therefore

```text
op  : R(𝒞)   → 𝒞,       A ↦ O(A)
r   : D≥3(𝒞) → 𝒞,       A ↦ R(A)
t   : D₂(𝒞)  → 𝒞,       A ↦ T(A).
```

Thus `op : Op2 Cat → Cat` is mathematically appropriate if Op2 means R
and Op_cat means total O. If Op_cat instead meant dimension-1 transpose,
its universe source would be D₂(Cat), not R(Cat).

This also explains the ordinary-category convention. On the external
1-category of categories and functors, opposite is a covariant functor
Cat₁→Cat₁. In the 2-category retaining natural transformations its source
is Cat₂ᶜᵒ. On individual 1-categories O=T and R=Id; the universe of those
categories still has nontrivial natural transformations in dimension 2.

## 3. Families: Dualize Fibres And Shift The Base

For a strict family E:K→𝒞 define

```text
E^S = d_S ∘ D_(S↑)(E) : D_(S↑)(K) → 𝒞.

E^S(k) = D_S(E(k)).
```

The base change is part of the construction. In the Cartesian family
classifier Famₛ(K)=[K,𝒞]ₛ, the whole operation is

```text
D_(S↑)(Famₛ(K)) → Famₛ(D_(S↑)(K)).
```

On a family map η:E→F, its fibre component is the ordinary dual functor
D_S(η_k). Higher family transformations follow the same shifted rule.
This determines the operation on the whole family classifier rather than
only on family objects.

For total duality:

```text
E^O : R(K) → 𝒞
Op_family : R(Famₛ(K)) → Famₛ(R(K)).
```

For an ordinary 1-category K, R(K)=K, so the familiar pointwise opposite
really is a same-base construction at that level. With higher base cells,
the shifted base remains visible. Reindexing is compatible in the precise
form

```text
(E∘F)^S = E^S ∘ D_(S↑)(F).
```

This is the equation to use when transporting a whole family operation
through a changed base.

## 4. Lax/Oplax Contexts: Transport The Structure Too

A duality transports the chosen transformation structure along with the
objects. There is a general mathematical construction that makes this
coherent without guessing a same-profile signature.

Given a monoidal tensor ⊗ on strict ω-categories, define its transported
tensor and internal Homs by

```text
A ⊗^S B = D_S(D_S A ⊗ D_S B)
[A,B]^S = D_S([D_S A,D_S B]).
```

Here each left/right internal Hom is transported with its matching
adjunction. Units, associators, evaluation and composition are transported
by the same equivalence. In particular,

```text
D_S(A⊗B) ≅ D_S A ⊗^S D_S B
D_S([A,B]) ≅ [D_S A,D_S B]^S.
```

Transport twice combines the labels by symmetric difference. Applying
D_S to the Homs of an enriched category gives a category enriched in
⊗^S, with the induced shift of ambient cell dimensions. This supplies a
coherent meaning for every dimension set S. When the transported tensor
has a familiar name, that name can be used through its canonical comparison.

For the standard Gray tensor, total O preserves the tensor; odd-dimensional
and even-dimensional duals reverse its factor order. The corresponding
lax/oplax Hom comparisons exchange the two orientations for the odd/even
duals and preserve them for total O. Arbitrary dimension-selected duals
need not preserve that particular tensor. These standard identifications
are recorded in Ara–Guetta,
[§§2.22–2.27](https://arxiv.org/pdf/2503.08832v3#page=24).

Our R and T must not be confused with the even/odd duals in that notation:
R reverses every dimension ≥2, and T reverses only dimension 1. They
coincide with the even/odd choices only through dimension 2. The transport
construction above specifies their meaning when an unchanged standard
Gray profile is unavailable.

For example, a lax family comparison

```text
F(p)∘η_x ⇒ η_y∘E(p)
```

is transported with its direction and whole higher action. It is not
declared to belong to the original transformation classifier solely
because the fibre functors have the expected object values. This is
mathematical bookkeeping for the operation, not an instruction to migrate
this branch's prototype strictness rules.

## 5. Sections And Totals By Their Whole Universal Interfaces

Sections 1–4 specify the duality framework itself. The following sections
apply it to the native section, total and Homd interfaces. They distinguish
the chosen universal constructions from the still-unfinished full native
target/module implementation.

Fix a family-map profile p. Its section category is the native Hom

```text
Π_(p,K)(E) = Hom_(Fam_p(K))(const_K(1),E).
```

For the positive section convention, the observed base-arrow component is
E(a)(s_x)→s_y. Constant-family positive sections are ordinary functors
K→A. A Cartesian strictly natural family-map profile and this positive
section profile have different meanings and should carry the appropriate
mathematical names.

The constant view can be checked by interpreting positive sections as
sections of π:Σ⁺E→K, with their chosen higher structure over K. For a
constant family this projection is K×A→K, whose strict section category is
[K,A]ₛ. This is a semantic interpretation of the native section owner; it
is not an identification with every possible lax higher-transformation
classifier or a replacement of the syntactic foundations.

Let U=S↑ and p^U denote the transported family-map profile from §4. The
whole family duality then gives

```text
D_S(Π_(p,K)(E)) ≅ Π_(p^U,D_U K)(E^S).
```

This follows by applying the Hom formula to the whole family classifier:
1∉U, so the two family endpoints stay in order and U↓=S. It accounts for
both the changed base and the changed section profile.

Likewise, specify a totalization through its whole cocone interface

```text
[Σ_(p,K)(E),C]ₛ ≅ Hom_(Fam_p(K))(E,const_K(C)).
```

Transporting this universal construction gives

```text
D_S(Σ_(p,K)(E)) ≅ Σ_(p^U,D_U K)(E^S).
```

The total's projection is transported too. If π:ΣE→K, its dual lands in
D_S K. One must not independently assign it the family base D_U K: these
are different axes of the construction. This distinction is already
visible for total O, where the total projection reverses base arrows while
the pointwise-dual family's base is R(K).

These are universal categorical interfaces, not instructions for users to
assemble pointwise cone records in the formal layer.

## 6. Covariant And Contravariant Totalizations

Write Σ⁺_K(E) for positive Grothendieck totalization of E:K→𝒞. For a
presheaf H:T(K)→𝒞 define the contravariant version by

```text
Σ⁻_K(H) = O(Σ⁺_(O K)(H^O)).
```

It is well typed: H^O has base R(TK)=OK. The outer O sends the total's
projection to a projection over K, and restores its original fibres.

The familiar arrow observations make the distinction concrete:

```text
Σ⁺E: (x,u)→(y,v) is (a:x→y, β:E(a)u→v).
Σ⁻H: (x,u)→(y,v) is (a:x→y, β:u→H(a)v).
```

For constant families both totals have the expected product K×A. The
inner fibre dual and outer total dual serve distinct roles; the recursive
Hom rule determines their higher-cell action.

The dependent-Hom observation

```text
χ_(x,u;y,v)(a) = Hom_(E(y))(E(a)u,v)
χ_(x,u;y,v) : T(Hom_K(x,y)) → 𝒞
```

therefore yields the mathematical Sigma-Hom formula

```text
Hom_(Σ⁺E)((x,u),(y,v)) ≅ Σ⁻_(Hom_K(x,y))(χ_(x,u;y,v)).
```

In emdash, χ is the existing native dependent-Hom observation at id_E.
This formula relates the native Hom and Sigma owners. It does not replace
homd_int by a definition using a total-category projection.

## 7. Negative Sections And The Native Shared Index

The earlier negative-section expression has a useful direct meaning:

```text
Π⁻_K(E) = O(Π⁺_(R K)(E^O)).
```

It switches the section profile as explained in §5. In particular,

```text
Π⁻_K(const_K(A)) ≅ [T(K),A]ₛ,
```

because O([RK,OA]ₛ)≅[O(RK),A]ₛ and O(RK)=TK. This derives the constant
view from ordinary duality rather than postulating another section rule.

The existing [shared native index design](TYPESCRIPT_EMDASH_NATIVE_HOMD_INDEX_TARGET_DESIGN.md)
can use the same dimension calculus. With C=Σ⁺D, π:C→Z and the native
represented family H_x=hom_int(π)[x], its carrier expression is

```text
J_x = Σ⁺_(R C)(H_x^O)
S_x(D) = R(J_x).
```

Its points retain (y,v,a:x→y), and its arrows retain the triangle
(s,β:D(s)v→w,θ:b⇒s∘a). The native dependent-Hom value remains

```text
M_(x,u)(y,v,a) = Hom_(E(y))(E(a)u,FF_y(v)).
```

For strict E and a family comparison E(s)FF_y⇒FF_zD(s), the arrow
observation sends h to the composite

```text
E(b)u → E(sa)u = E(s)E(a)u
      → E(s)FF_y(v) → FF_zD(s)(v) → FF_z(w).
```

The successive actions are E(θ), E(s)(h), the supplied family's own
comparison, and FF_z(β). No inverse comparison is inserted. This formula
explains the intended mathematical action; full native packaging remains
the implementation row recorded in the shared-index plan.

The previously derived Cartesian source dimensions fit the uniform shifts:

```text
S : D₁₂(Z) → 𝒞
P_D : D₂(Z) → 𝒞,       P_D(x) = [S_x(D),𝒞]ₛ
T_*(E) : D₂(Z) → 𝒞.
```

Thus the intended native homd source/target use the same base D₂(Z), and
the source fibre is T(E(x)). Its exact whole transformation context is
carried with the supplied family data. The dimensions are not inferred
from an equality of bases or from a replacement input family.

## Implementation Direction

Use total O as Op_cat and retain R as its homwise shift. Derive T=R∘O,
D₂=R∘D≥3 and D₁₂=D≥3∘O. The public mathematical account should expose
the dimension sets and the shift rule, so the additional operators do not
look like unrelated special cases.

Resume the native shared-index/module construction using these meanings,
then the whole-universality and homology rows of the living plan. Validate
the affected operations through their typed whole action, nonidentity
examples and higher projections. Prototype strictness migration, Empty
reproducer work and the unrelated branch integration remain deferred.
