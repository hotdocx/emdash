<a id="chapter-13"></a>

# 13. Yoneda, Representability, And Profunctors

Representability turns the arrows out of, or into, one object into a universal
coordinate system. Yoneda says that a natural map out of such a coordinate
system is determined by its value at an identity. Adjunction says that one
hom coordinate system is represented by another object. Weighted limits will
repeat the same argument for a more elaborate functor.

The ordinary Yoneda lemma is therefore the conceptual center of this part of
the book. We first develop its univalent 1-categorical form, then identify the
native representable families already used by arrow induction, and finally
pass to Cat-valued profunctors. The chapter's central *checked* computation is
a shaped co-Yoneda cut: tensor an element with the appropriate identity-shaped
hom, apply the co-Yoneda map, and recover the original element.

The full ordinary Yoneda lemma below is mathematical development adapted from
the [HoTT Book](#ref-hott-book). The active artifact checks native
representables and the shaped Cat-valued co-Yoneda beta/fusion equations. It
does not yet package a general Cat-valued Yoneda equivalence or a semantic
coend. [Kelly](#ref-kelly) supplies enriched background for these patterns,
while [Bénabou](#ref-benabou) is a classical reference for their bicategorical
organization.

## 13.1 Representables And Variance

Let $\mathcal A$ be an ordinary precategory. A presheaf is a functor

$$
P:\mathcal A^{\mathrm{op}}\longrightarrow\mathsf{Set}.
$$

For $a:\mathcal A$, the contravariant representable presheaf is

$$
y(a):=\operatorname{Hom}_{\mathcal A}(-,a).
$$

An arrow $u:a\to b$ induces a natural transformation
$y(u):y(a)\Rightarrow y(b)$ by postcomposition:

$$
y(u)_x(f)=u\circ f=u_*(f).
$$

This defines the Yoneda embedding

$$
y:\mathcal A\longrightarrow
[\mathcal A^{\mathrm{op}},\mathsf{Set}].
$$

The active formal development also lifts this picture from sets to
Cat-valued presheaves. Its Yoneda presheaf evaluates to the represented hom,
and restriction reuses the existing pullback of directed families. Gathering
all arrows into $a$ produces the restriction-oriented total

$$
\operatorname{Into}^{-}_{\mathcal A}(a)
  :=\sum_{x:\mathcal A^{\mathrm{op}}}
       \operatorname{Hom}_{\mathcal A}(x,a)
$$

whose opposite is the conventional slice $\mathcal A/a$. A Cat-valued family
on this total is a higher sieve; requiring its values to be subterminal gives
an ordinary sieve. [Chapter 18](#chapter-18) begins the local-to-global spiral
by developing these constructions as mathematics, separating witness-bearing
higher sieves from proposition-valued membership, and explaining why sieve
pullback is the natural language of a changing probe.

This bridge does not strengthen the Yoneda theorem claimed in the present
chapter. A general Cat-valued Yoneda equivalence and full-faithfulness theorem
remain separate from the checked representable action and shaped co-Yoneda
calculation below.

There is a covariant mirror

$$
y^{a}:=\operatorname{Hom}_{\mathcal A}(a,-):
\mathcal A\longrightarrow\mathsf{Set}.
$$

It is contravariant in the represented object $a$: an arrow $u:a\to b$
induces precomposition

$$
u^*:\operatorname{Hom}_{\mathcal A}(b,-)
\Longrightarrow
\operatorname{Hom}_{\mathcal A}(a,-).
$$

The lower-star and upper-star actions from Chapter 9 are therefore the two
variance legs of representability.

## 13.2 The Ordinary Yoneda Equivalence

For a presheaf $P:\mathcal A^{\mathrm{op}}\to\mathsf{Set}$, the Yoneda
equivalence is

$$
\operatorname{Nat}(y(a),P)\simeq P(a).
$$

Its forward map evaluates a natural transformation at the identity:

$$
\operatorname{encode}(\alpha)
:=\alpha_a(\mathrm{id}_a).
$$

For $p:P(a)$, the reverse map defines a natural transformation by

$$
\operatorname{decode}(p)_x(f)
:=P[f](p),
\qquad
f:x\to a.
$$

The first composite is immediate from preservation of identity:

$$
\operatorname{encode}(\operatorname{decode}(p))
=P[\mathrm{id}_a](p)
=p.
$$

For the other composite, naturality of $\alpha$ at $f:x\to a$ gives

$$
P[f]\bigl(\alpha_a(\mathrm{id}_a)\bigr)
=\alpha_x(f).
$$

Thus
$\operatorname{decode}(\operatorname{encode}(\alpha))=\alpha$ by
extensionality. The proof has the same shape as Chapter 8: choose a code by
evaluation, decode it by functorial transport, and calculate both composites.
Here the distinguished constructor is the identity arrow of a representable.

The covariant form is equally important. For
$Q:\mathcal A\to\mathsf{Set}$,

$$
\operatorname{Nat}
  \bigl(\operatorname{Hom}_{\mathcal A}(a,-),Q\bigr)
\simeq Q(a),
$$

and the inverse sends $q:Q(a)$ to the family
$f:a\to x\mapsto Q[f](q)$.

<!-- evidence:UCAT-YONEDA -->

> **Formal status — mathematical development.** Evidence
> `UCAT-YONEDA`. These are the ordinary set-valued Yoneda equivalences.
> They are stated under the HoTT precategory assumptions and are not labeled
> as the active full Cat-valued theorem.

## 13.3 Full Faithfulness And Uniqueness Of Representation

Apply Yoneda with $P=y(b)$. One obtains

$$
\operatorname{Nat}(y(a),y(b))
\simeq
\operatorname{Hom}_{\mathcal A}(a,b).
$$

Under this equivalence, an arrow $u:a\to b$ corresponds to
postcomposition by $u$. Hence the Yoneda embedding is fully faithful: it
recovers every hom from the natural maps between representables.

More generally, a representation of $P$ consists of an object $a$ and a
natural isomorphism $y(a)\cong P$. If $a$ and $b$ both represent $P$, full
faithfulness produces a canonical isomorphism $a\cong b$. When
$\mathcal A$ is a univalent category, this isomorphism corresponds to object
identity, and representability becomes a property rather than an uncontrolled
choice of presentation.

> **Formal status — mathematical development.** This full-faithfulness and
> uniqueness result is part of evidence `UCAT-YONEDA`. The conclusion uses
> ordinary category univalence exactly where an isomorphism of representing
> objects is turned into identity.

## 13.4 Native Representable Families

For a native category $Z$ and an object $x$, emdash has the Cat-valued
fixed-source representable

$$
\operatorname{Rep}_Z(x)[y]
:=\operatorname{Hom}_Z(x,y).
$$

Its target action is postcomposition. Its dependence on the represented
source is contravariant: for $p:x\to y$, the transport

$$
\operatorname{Rep}_Z(y)\longrightarrow\operatorname{Rep}_Z(x)
$$

acts by

$$
q\longmapsto q\circ p=p^*(q).
$$

The full operation is a functor between directed families, so it retains
action on cells between possible $q$'s.

<!-- evidence:CAT-REPRESENTABLE -->

> **Formal status — checked.** Evidence `CAT-REPRESENTABLE`.
> `Rep_catd` owns the fixed-source family and
> `Rep_transport_func` owns its upper-star source action.

The outgoing-arrow category from Chapter 5 is the total category

$$
\operatorname{PathOut}_Z(x)
=\sum_{y:Z}\operatorname{Hom}_Z(x,y).
$$

Its distinguished object $(x,\mathrm{id}_x)$ and its canonical arrow to every
$(y,p)$ are built from the representable family. Arrow induction extends data
from that reflexive outgoing arrow.

This is Yoneda-shaped, but it is not literally the ordinary Yoneda lemma.
Yoneda classifies natural transformations from a representable; the selected
arrow-induction theorem eliminates a dependent motive over the total category
of outgoing arrows. Both begin at an identity arrow because identities are
the universal points of representables.

## 13.5 From One Endpoint To Two

Opposites and products make the two variances explicit. In the ordinary
1-categorical setting, currying and uncurrying compare functors

$$
\mathcal A\times\mathcal B\longrightarrow\mathcal C
$$

with functors

$$
\mathcal A\longrightarrow[\mathcal B,\mathcal C].
$$

Applying this organization to composition shows that hom is functorial in
both endpoints, contravariantly in its source and covariantly in its target.

The two representable variances combine in the hom bifunctor

$$
\operatorname{Hom}_{X}(-,-):
X^{\mathrm{op}}\times X\longrightarrow\mathsf{Cat}.
$$

Reindexing its two endpoints along functors $F:A\to X$ and $G:B\to X$
gives

$$
\operatorname{Hom}_{X}(F{-},G{-}):
A^{\mathrm{op}}\times B\longrightarrow\mathsf{Cat}.
$$

This two-variable view is the bridge from Yoneda to profunctors. It makes
contravariance and covariance simultaneous, lets endpoint functors vary, and
turns hom transposition for an adjunction into a comparison of profunctors.

The price of the richer codomain is that ordinary elementwise proofs no longer
automatically supply all higher naturality. The active development therefore
selects shaped elements and explicit comparison maps before claiming a
general coend-based composition.

## 13.6 Cat-Valued Profunctors

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

## 13.7 The Unit Hom Profunctor

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

## 13.8 Reindexing Endpoints

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

## 13.9 Representability As A Chosen Comparison

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

## 13.10 Cells With Moving Endpoints

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

## 13.11 Tensor As A Selected Composite

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

## 13.12 The Shaped Co-Yoneda Cut

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

## 13.13 Adjunctions As Representable Hom Comparisons

Chapter 12 characterized a right adjoint $G:B\to A$ to $F:A\to B$ by
representations

$$
\operatorname{Hom}_B(F{-},b)
\simeq
\operatorname{Hom}_A({-},Gb).
$$

Yoneda explains both the representing object and its uniqueness. The
profunctor formulation adds simultaneous naturality in the source probe and
in $b$. For arbitrary $M:I\to A$ and $H:K\to B$, the active comparison is

$$
\operatorname{Hom}_B(FM,H)
\simeq
\operatorname{Hom}_A(M,GH).
$$

<!-- evidence:ADJ-HOM-PROF-COMPARISON -->

> **Formal status — checked.** Evidence
> `ADJ-HOM-PROF-COMPARISON`. The adjunction supplies this reindexable
> `ProfComparison`; its push and pull operations have the generic
> comparison beta/eta laws.

Conversely, an ordinary pointwise family of such representations reconstructs
a right adjoint only after the representing objects and comparisons have been
made coherent in $b$. The active representation package records a chosen
representing functor and ordinary isomorphism evidence in the profunctor
category, but no general reverse constructor from that package to
`Adjunction` is asserted.

<!-- evidence:UCAT-ADJOINT-REPRESENTABILITY -->

> **Formal status — mathematical development.** The ordinary reverse
> representability theorem is part of
> `UCAT-ADJOINT-REPRESENTABILITY`. Evidence
> `PROF-REPRESENTATION-PACKAGE`, checked in Section 13.9, supplies the
> native chosen representation interface on which a future reverse
> construction could be based.

This is the bridge to weighted universals. A weighted cone construction will
produce another profunctor; a weighted limit is the functor that represents
it. The same comparison beta/eta laws will eliminate the corresponding
universal cuts.

## 13.14 The Full Cat-Valued Yoneda Boundary

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

## 13.15 The Coend And Bicategorical Boundary

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
