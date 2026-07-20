<a id="chapter-13"></a>

# 13. Yoneda, Representability, And Profunctors

Representable families turn arrows into data that can be transported,
composed, and recognized by universal properties. Profunctors extend this
idea to two endpoints. They behave like generalized homs: contravariant in a
source category, covariant in a target category, and composable by a
coend-like tensor.

The central computation of this chapter is a co-Yoneda cut elimination. A
profunctor element tensored with the appropriate identity element returns to
itself when the co-Yoneda map is applied. The active calculus checks this
equation at shaped elements and checks its fusion with arbitrary vertical
maps. It deliberately stops short of claiming a general coend construction or
a fully developed bicategory of profunctors.

[Kelly](#ref-kelly) provides the enriched categorical background for many of
these representability patterns, while [Bénabou](#ref-benabou) is a classical
reference for bicategorical organization. This chapter uses those ideas as
mathematical orientation and states separately what the active emdash artifact
actually checks.

## 13.1 Cat-Valued Profunctors

For categories `A` and `B`, a Cat-valued profunctor from `A`
to `B` is a functorial family

$$
P:A^{\mathrm{op}}\times B\longrightarrow\mathsf{Cat}.
$$

We write `P:A prof B` informally and write its fibre at `(a,b)`
as `P(a,b)`. The opposite on `A` records the variance:

- an arrow $p:a'\to a$ acts contravariantly in the first endpoint;
- an arrow $q:b\to b'$ acts covariantly in the second endpoint.

Profunctors with fixed endpoints form a category. A vertical map

$$
r:P\Longrightarrow Q
$$

is a natural family morphism over `A^op times B`. Its identity,
vertical composition, components, and higher action are inherited from the
directed-family and transfor calculus of Chapters 2 and 9.

<!-- evidence:PROF-CATEGORY -->

> **Formal status — checked.** Evidence `PROF-CATEGORY`.
> `Prof_base(A,B)=A^op times B`; `Prof_cat` is the fixed-endpoint
> category and `ProfMap` its vertical-map classifier.

This definition introduces no new primitive notion of naturality. A
profunctor is a familiar Cat-valued functor on a product base, viewed through
notation that makes its two variances visible.

## 13.2 The Unit Hom Profunctor

Every category `X` has a canonical profunctor

$$
U_X:X^{\mathrm{op}}\times X\longrightarrow\mathsf{Cat},
\qquad
U_X(x,y):=\operatorname{Hom}_X(x,y).
$$

On an arrow pair

$$
p:x'\to x,
\qquad
q:y\to y',
$$

it acts by cutting on both sides:

$$
h\longmapsto q\circ h\circ p.
$$

The opposite variance is not decorative: it is exactly what makes the first
composition type-correct. Identity and composite action follow from the
generic hom bifunctor.

More generally, given functors

$$
F:A\longrightarrow X,
\qquad
G:B\longrightarrow X,
$$

reindex the unit to obtain the binary representable

$$
\operatorname{Hom}_X(F{-},G{-}):A\rightsquigarrow B
$$

with fibres

$$
\operatorname{Hom}_X(Fa,Gb)
$$

and action

$$
h\longmapsto G(q)\circ h\circ F(p).
$$

<!-- evidence:PROF-REPRESENTABLE -->

> **Formal status — checked.** Evidence `PROF-REPRESENTABLE`.
> `Unit_prof` owns the hom profunctor, and `Hom_prof_along(F,G)` is
> its endpoint-reindexed presentation with the two-sided `Hom_fapp0`
> action.

Two specializations are useful. The **companion** of
$F:A\to B$ is represented covariantly by `F`; the **conjoint** is
represented contravariantly by `F`. These are not assumed to be inverse
profunctors. They are the two variance choices obtained from the same ambient
hom.

## 13.3 Reindexing Endpoints

Let `P:A prof B`, $F:A'\to A$, and $G:B'\to B$.
Endpoint reindexing is

$$
(F,G)^*P:A'\rightsquigarrow B',
\qquad
((F,G)^*P)(a',b'):=P(Fa',Gb').
$$

Semantically this is pullback along

$$
F^{\mathrm{op}}\times G:
(A')^{\mathrm{op}}\times B'
\longrightarrow
A^{\mathrm{op}}\times B.
$$

The operation acts on vertical maps, is neutral at identity endpoint
functors, and accumulates nested reindexings by composing both endpoints. For
representables, it gives the expected equation

$$
(F',G')^*\operatorname{Hom}_X(F{-},G{-})
=
\operatorname{Hom}_X((F\circ F'){-},(G\circ G'){-}).
$$

<!-- evidence:PROF-REINDEXING -->

> **Formal status — checked.** Evidence `PROF-REINDEXING`.
> `Prof_reindex` is the stable object owner and
> `Prof_reindex_func` provides its vertical functorial action.

The separation between a profunctor and its reindexed view is analogous to the
separation between WalkingEnd and `BNat`. A readable model or pullback
presentation does not become a definitional replacement for the object it
explains.

## 13.4 Representability As A Chosen Comparison

A profunctor `P:B prof J` is right-represented by a functor
$L:J\to B$ when it is isomorphic, in the fixed-endpoint profunctor
category, to the conjoint of `L`:

$$
P\cong\operatorname{Hom}_B(-,L{-}).
$$

A representation package retains both the chosen functor and its
isomorphism evidence:

$$
\sum_{L:J\to B}
\mathsf{IsoEvidence}
  \bigl(P,\operatorname{Hom}_B(-,L{-})\bigr).
$$

<!-- evidence:PROF-REPRESENTATION-PACKAGE -->

> **Formal status — checked.** Evidence
> `PROF-REPRESENTATION-PACKAGE`. The classifiers are
> `IsRepresentedBy_iso` and `Representation_iso`; the current
> comparison is ordinary isomorphism evidence in `Prof_cat`.

This is a useful universal-property interface even before uniqueness of the
representing object is packaged. A weighted limit, for example, can be
presented as a chosen representation of a cone profunctor. The computational
strength of that use depends on how much of the comparison is exposed by the
consumer.

## 13.5 Cells With Moving Endpoints

Vertical maps keep endpoints fixed. Equipment-style cells allow endpoint
functors to move as well. Given

$$
R':A'\rightsquigarrow B',
\quad
R:A\rightsquigarrow B,
\quad
F:A'\to A,
\quad
G:B'\to B,
$$

a cell over `F,G` is a natural family morphism

$$
c:R'\Longrightarrow(F,G)^*R.
$$

If the source profunctor is the unit `U_I`, such a cell is a shaped
element of `R` with endpoint functors $I\to A$ and $I\to B$.
The narrow application operation sends a shaped element of `R'` through
`c` to the corresponding shaped element of `R`.

<!-- evidence:PROF-SHAPED-CELLS -->

> **Formal status — checked.** Evidence `PROF-SHAPED-CELLS`.
> `Prof_transf_cat` is the endpoint-changing cell category,
> `Prof_hom` is its unit-source specialization, and
> `Prof_cell_apply` is the selected application operation.

The operation is intentionally narrower than arbitrary horizontal
composition of equipment cells. It supplies the consumer needed by the
co-Yoneda calculation without pretending that all bicategorical coherence is
already present.

## 13.6 Tensor As A Selected Composite

For

$$
P:A\rightsquigarrow B,
\qquad
Q:B\rightsquigarrow X,
$$

write

$$
P\otimes_B Q:A\rightsquigarrow X
$$

for their selected profunctor tensor. In ordinary enriched category theory
one expects a coend-like formula

$$
(P\otimes_B Q)(a,x)
\simeq
\int^{b:B}P(a,b)\times Q(b,x).
$$

This formula is the intended mathematical reading, not a definition unfolded
by the active kernel. `Prof_tensor` is opaque. What is exposed is the
behavior required by current consumers:

- reindexing in the outer endpoints distributes through the tensor;
- the middle category stays fixed;
- vertical maps in both factors induce a vertical map of tensors;
- compatible shaped elements compose to a shaped tensor element.

<!-- evidence:PROF-TENSOR -->

> **Formal status — checked.** Evidence `PROF-TENSOR`. The fixed-middle
> object is `Prof_tensor`; `Prof_tensor_func` owns fixed-endpoint
> bifunctoriality and `Prof_tensor_hom_hom` composes shaped elements.

Opacity is mathematically honest here. A genuine coend construction would
need a quotient or universal colimit with its own eliminator and computation
rules. The selected tensor can support tested cut-elimination interfaces
without serving as evidence that this general construction has already been
built.

## 13.7 The Co-Yoneda Cut

The unit profunctor should behave as a unit for tensor. The active interface
supplies natural maps in both orientations:

$$
\begin{aligned}
\varepsilon^R_P &: P\otimes_B U_B\Longrightarrow P,\\
\varepsilon^L_P &: U_A\otimes_A P\Longrightarrow P.
\end{aligned}
$$

They are components of transformations natural in `P`, rather than a
collection of unrelated vertical maps.

Now let `p` be a shaped element of `P` with middle shape
$M:I\to B$. The unit profunctor has a canonical shaped element given by
the identity transformation on `M`. Tensor the two elements and apply the
right co-Yoneda map. The cut eliminates:

$$
\varepsilon^R_P
  \bigl(p\otimes\mathrm{id}_M\bigr)
=p.
$$

Dually, for an `A`-shaped endpoint `F`,

$$
\varepsilon^L_P
  \bigl(\mathrm{id}_F\otimes p\bigr)
=p.
$$

<!-- evidence:PROF-COYONEDA -->

> **Formal status — checked.** Evidence `PROF-COYONEDA`.
> `Prof_coyoneda_cov_transf` and
> `Prof_coyoneda_con_transf` are the two natural transformations;
> their component maps have the shaped-element beta equations above.

These equations are the chapter's central theorem. They express Yoneda-style
evaluation as computation: insert an identity-shaped hom, form the composite,
and the co-Yoneda counit removes the cut.

The transformations also fuse with an arbitrary vertical map
$r:P\to P'$. Applying the naturality component of co-Yoneda to
$p\otimes\mathrm{id}$ reduces to applying `r` directly to `p`:

$$
\varepsilon_{P'}
  \bigl((r\otimes\mathrm{id})(p\otimes\mathrm{id})\bigr)
=r(p),
$$

with the analogous left-unit equation. This is not a separate law attached to
every `r`; it is the off-diagonal action of the co-Yoneda transfor from
Chapter 9.

## 13.8 What This Says About Yoneda

The computations capture an essential Yoneda idea: represented hom data can
be inserted as an identity-shaped cut and then eliminated. The existing
right-representable embedding, endpoint reindexing, shaped cells, and
co-Yoneda maps give a credible computational core for a broader theorem.

A full Cat-valued Yoneda theorem would package more. One expects a functor
from `A` into an appropriate presheaf or profunctor category, a precise
mapping-category equivalence, naturality in the represented object and the
presheaf, and a proof that the embedding is fully faithful at every retained
cell level. Those data have not been gathered into one active theorem.

<!-- evidence:YONEDA-FULLY-FAITHFUL -->

> **Formal status — research boundary.** Evidence
> `YONEDA-FULLY-FAITHFUL`. The intended future owner should be built
> from the existing representable functor, shaped-cell, and co-Yoneda
> interfaces and should expose a reusable equivalence rather than add isolated
> projection rules.

The checked beta equations remain valuable without that package. They are
local computational theorems, not merely motivational analogies.

## 13.9 The Coend And Bicategorical Boundary

To promote the tensor to a general profunctor composition, one would need:

- a coend or coinserter construction for Cat-valued data;
- its dinatural elimination and computation principles;
- associativity and left/right unit comparisons;
- coherent higher cells for those comparisons;
- horizontal composition of arbitrary endpoint-changing cells;
- compatibility with opposites, reindexing, and internal homs.

Only selected parts of this list are active. Fixed-endpoint tensor action,
outer reindexing, shaped composition, and both co-Yoneda counits have checked
owners. They do not automatically assemble into a bicategory.

<!-- evidence:PROF-GENERAL-COEND -->

> **Formal status — research boundary.** Evidence
> `PROF-GENERAL-COEND`. A future implementation should give the opaque
> tensor a universal semantics or relate it to a separately constructed
> coend; it should not infer general coherence from the current endpoint beta
> rules alone.

This staged boundary mirrors the rest of the book. We expose enough
functorial structure to compute a central example, retain the higher action
that example consumes, and state the missing universal package explicitly.
