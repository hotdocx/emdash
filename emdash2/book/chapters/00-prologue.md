<a id="prologue"></a>

# Prologue: The Natural Number Hidden In A Directed Loop

Imagine a world with one distinguished place and one permitted step that
returns to it. Call the place `*` and the step `ell`. We may
stand still, take the step once, take it twice, and continue:

$$
\mathrm{id}_*,\qquad
\ell,\qquad
\ell\circ\ell,\qquad
\ell\circ\ell\circ\ell,\qquad\ldots .
$$

If this is the *free* directed situation, every journey from `*` back
to `*` should have a unique length. That sentence sounds obvious
only because it quietly identifies two descriptions:

1. the syntactic description of a journey as a finite word in one generator;
2. the universal object characterized by how maps out of it behave.

Functorial type theory keeps them apart. The walking endomorphism `W`
is presented opaquely by a category, a base, a directed loop, explicit
one-dimensionality, and a contextual elimination principle. Its object type,
hom-categories, identities, and composition do not reduce to a word datatype.

<!-- evidence:WE-SIGNATURE -->
<!-- evidence:WE-ONE-DIMENSIONAL -->

> **Formal status — checked.** Evidence `WE-SIGNATURE` and
> `WE-ONE-DIMENSIONAL`. One-dimensionality says that each
> hom-category is discrete; it neither makes `W` a discrete category
> nor makes `ell` invertible.

There is also a concrete category `BNat`. It has one object, natural
numbers as endomorphisms, zero as identity, and addition as composition. The
recursor for `W` gives a functor

$$
W\longrightarrow BNat
$$

sending `*` to the sole object and `ell` to one. This is the
expected arithmetic model. It is not a definition of `W`, and a
functor into a model cannot by itself prove that two arrows of `W`
with the same image are equal.

<!-- evidence:WE-BNAT-MODEL -->

> **Formal status — checked.** Evidence `WE-BNAT-MODEL`.
> `BNat` is separate model evidence. A reverse functor and a
> categorical equivalence have not been packaged.

The central theorem supplies the missing exhaustiveness statement by a
different route.

<!-- evidence:WE-HOM-NAT-CARRIER -->

> **Theorem preview.** There is an equivalence of underlying carriers
>
> $$
> \operatorname{Hom}_{W}(*,*)\simeq\mathbb{N}.
> $$
>
> **Formal status — checked.** Evidence `WE-HOM-NAT-CARRIER`. The
> current package is a `TypeEquiv`, together with a native
> equality-valued facade. A monoid or hom-category equivalence is not being
> asserted here.

## Measuring An Abstract Arrow

How can an opaque arrow be assigned a number? We construct a Cat-valued family

$$
\mathsf{Code}:W\longrightarrow\mathsf{Cat}
$$

whose fibre at `*` is the path category of natural numbers. The
generator acts by the successor functor. For any endpoint `x` and any
based arrow $p:* \to x$, define

$$
\mathsf{encode}_x(p)\;=\;\mathsf{Code}[p](0).
$$

This is directed transport in its plainest form: a functor acts on an object.
When `p` begins with the generator, its code begins with a successor.
There is no predecessor action because none was requested by the signature.

To go back, natural numbers produce powers:

$$
\ell^0=\mathrm{id}_*,
\qquad
\ell^{n+1}=\ell\circ\ell^n.
$$

At first this decoder exists only over the base. The decisive move is to
generalize it over every endpoint. The based representable family

$$
\mathsf{Rep}_*(x)=\operatorname{Hom}_W(*,x)
$$

acts on a base arrow by postcomposition. A displayed transformation

$$
\mathsf{decode}^{d}:\mathsf{Code}\Longrightarrow\mathsf{Rep}_*
$$

must therefore reconcile successor in `Code` with postcomposition by
`ell` in the representable. Its coherence winds forward through the
natural levels:

$$
\ell\circ\ell^n\longrightarrow\ell^{n+1}.
$$

This family of higher arrows is the **directed spiral**.

## Normalize Before Comparing

Applying the displayed decoder’s arrow action to
$p:* \to x$ at zero produces

$$
\nu_p:
p\longrightarrow
\mathsf{decode}_x(\mathsf{encode}_x(p))
$$

inside the hom-category `Hom_W(*,x)`. This is not initially an
equation. It is a directed 2-cell whose orientation records a normalization
process.

<!-- evidence:WE-NORMALIZATION-CELL -->

> **Formal status — checked.** Evidence `WE-NORMALIZATION-CELL`.
> The normalization cell is obtained from the contextual displayed
> eliminator; it is not postulated as a word-reduction axiom.

Only now is one-dimensionality used. The hom-category is discrete, so a cell
between parallel based arrows determines equality:

$$
p =
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

At the base, `decode` computes to `power`. Reversing the
displayed equality gives

$$
\ell^{\mathsf{encode}(p)}=p.
$$

The other composite is arithmetic. The generator-prefix equation and natural
number induction give

$$
\mathsf{encode}(\ell^n)=n.
$$

These two equations package the carrier equivalence.

<!-- evidence:WE-NORMALIZATION-PATH -->
<!-- evidence:WE-POWER-ENCODE -->
<!-- evidence:WE-ENCODE-POWER -->

> **Formal status — checked.** Evidence
> `WE-NORMALIZATION-PATH`, `WE-POWER-ENCODE`, and
> `WE-ENCODE-POWER`. Direction is retained until the first of these
> equalities is extracted.

## Why The Answer Is Not The Integers

For the circle, a loop is an equality path and therefore has an inverse. Its
powers are indexed by integers. Here `ell` is a directed arrow.
Nothing in the category laws manufactures a reverse arrow, and the calculation
detects that absence.

Encoding sends `ell` to one and the identity to zero. Consequently
the generator is not the identity. If an arrow `r` were a right
inverse, then encoding $\ell\circ r=\mathrm{id}$ would force a
successor to equal zero. Hence no right inverse exists, and in particular
`ell` carries no native omega-equivalence evidence.

<!-- evidence:WE-LOOP-NOT-IDENTITY -->
<!-- evidence:WE-LOOP-NO-RIGHT-INVERSE -->
<!-- evidence:WE-LOOP-NONINVERTIBLE -->

> **Formal status — checked.** Evidence
> `WE-LOOP-NOT-IDENTITY`,
> `WE-LOOP-NO-RIGHT-INVERSE`, and
> `WE-LOOP-NONINVERTIBLE`.

The missing negative integers are therefore not an incomplete case of the
proof. They are the numerical trace of directionality.

## The Road To The Proof

The next seven chapters unpack the interfaces used above.

- [Chapter 1](#chapter-1) separates definitional computation, proof-time
  comparison, and equality evidence.
- [Chapter 2](#chapter-2) introduces iterated hom-categories, functors,
  transfors, and directed Cat-valued families.
- [Chapter 3](#chapter-3) develops constructive logic, propositions, and sets.
- [Chapter 4](#chapter-4) distinguishes equality, ordinary equivalence,
  categorical isomorphism, and univalence.
- [Chapter 5](#chapter-5) moves from ordinary induction to arrow induction and
  contextual universal properties.
- [Chapter 6](#chapter-6) states the selected directed higher-inductive
  signature and its contextual eliminator.
- [Chapter 7](#chapter-7) explains categorical height and why a directed cell
  in a discrete hom-category yields equality.
- [Chapter 8](#chapter-8) returns to every step of the construction, including
  the spiral, the two inverse laws, and the noninvertibility consequences.

The second spiral asks what the same computational discipline contributes to
category theory. [Chapter 9](#chapter-9) isolates its cut calculus; Chapters
[10](#chapter-10)–[15](#chapter-15) develop categorical identity, functor
categories, adjunctions, Yoneda, duality, and saturation; and Chapters
[16](#chapter-16)–[17](#chapter-17) organize limits, colimits, and join by
representability and opposite duality. [Appendix G](#appendix-formal-presentation)
collects the formal rule schemas and states the metatheoretic boundary.

The third spiral asks how local questions become geometry. Chapters
[18](#chapter-18)–[20](#chapter-20) pass from presheaves and sieves through
sites and descent to direct Cat-valued sheafification. Chapters
[21](#chapter-21)–[24](#chapter-24) develop universal-property algebra and
affine localization, place the invertibility sieve before any representing
open, and assemble site-relative scheme and supplied projective-line
presentations without concealing their hypotheses.

The fourth spiral returns to the relation between paths and arrows.
[Chapter 25](#chapter-25) realizes selected directed action inside path
categories and compares product transport with equality induction.
[Chapter 26](#chapter-26) restores the inverse powers missing from the central
WalkingEnd theorem by proving the Circle/Integer encode–decode equivalence.
[Chapter 27](#chapter-27) upgrades that comparison to free inversion, first
for one- and two-endpoint walking shapes and then for an arbitrary source
category. [Chapter 28](#chapter-28) keeps the target directed again: whole
laxity, a computational strict profile, and one right Gray closure produce a
nonidentity walking-square interchanger with higher action still available.

The fifth spiral asks what that still-available action constructs when it is
iterated. [Chapter 29](#chapter-29) combines a computing category of injective
faces with the native recursion
$S_{n+1}=\operatorname{PathOut}_{S_n}(s_n)$. It constructs a canonical
ordinal dependent simplex in variable dimension, maps it into arbitrary
targets, and retains both face action and another hom action without
postulating a new coherence record at every dimension.

The larger aim is not merely to calculate one hom. It is to show how a type
theory can let groupoidal equality and noninvertible arrows coexist, interact,
and compute—without quietly turning one into the other.
