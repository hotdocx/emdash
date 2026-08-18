<a id="appendix-hott-correspondence"></a>

# Appendix C. From The Circle To The Walking Endomorphism—And Back

The proof of Theorem 8.1 is inspired by the encode-decode calculation of the
loop space of the circle in the [*Homotopy Type Theory* book](#ref-hott-book).
This appendix
records the correspondence so that the analogy can guide the reader without
smuggling groupoidal assumptions into the directed theorem.

The comparison is no longer merely retrospective or prospective. Chapter 26
checks the Circle side of the analogy with a successor-localized Integer
classifier, while Chapter 27 proves that mapping out of the Circle into a
groupoid is equivalent, as a whole mapping object, to mapping out of
WalkingEnd through paths. The appendix therefore records both the deliberate
change from inverse to forward powers and the checked free-inversion passage
back.

The source reference is revision
`578b85cc8d586b1677ec4335148adeb443057d24` of the HoTT Book
repository. The detailed, machine-readable adaptation ledger is
`book/references/third-party-sources.json`.

## C.1 The Rhetorical Spine

The HoTT calculation proceeds through four questions:

1. What are the evident powers of the loop, and how might a loop be assigned a
   winding number?
2. What does the classical free/universal-cover picture predict?
3. How can the cover be represented internally as a family?
4. How do encode and decode become inverse after the endpoint is generalized?

Chapter 8 retains that sequence. It changes the mathematical answer at every
point where the circle proof uses reversibility.

| Circle calculation | Walking-endomorphism calculation |
| --- | --- |
| A base point and an identity loop in `S¹` | A base object and a directed arrow `ell` in `W` |
| Loop carrier `base = base` | Based hom carrier `Hom_W(*,*)` |
| Integer-indexed positive and negative powers | Natural-number-indexed forward powers |
| A cover with integer fibre | A Cat-valued code with `Path(Nat)` base fibre |
| Successor equivalence on integers | Successor functor on naturals |
| A universe path obtained through univalence | A directed endofunctor accepted directly by recursion into `Cat` |
| Transport zero along an identity path | Apply the Code functor to zero along a directed arrow |
| Decode by dependent circle induction | Decode by the contextual displayed eliminator |
| Hard inverse by generalized path induction | Directed normalization cell, then hom-discreteness |
| Easy inverse by integer/circle induction | Easy inverse by Nat induction |
| `Omega(S¹) ≃ Int` | `Hom_W(*,*) ≃ Nat` as carriers |
| Group structure and inverse loops | Free-monoid direction and a noninvertible generator |

The table is a dependency map, not a dictionary identifying the objects.

## C.2 Where Univalence Moves

In the circle proof, a family $\mathsf{Code}:S^1\to\mathsf{Type}$ must map the loop of
`S¹` to a loop in the universe. Successor on the integers is an
equivalence, and univalence converts that equivalence into the needed universe
identity. Its inverse supplies predecessor action.

In the directed proof,

$$
\mathsf{Code}:W\longrightarrow\mathsf{Cat}
$$

is specified by a category and an endofunctor. Natural-number successor is
therefore accepted without being an equivalence. No universe identity and no
predecessor are needed.

This does not make univalence irrelevant to functorial type theory. It
clarifies its jurisdiction. Equality, transport, equivalence, and univalent
universes govern groupoidal identification. A directed family may additionally
act along arrows that are not identities and whose action is not invertible.
The title of this book refers to a foundation containing both layers.

> **Formal status — mathematical development.** The comparison of the roles
> of univalence is explanatory. The individual emdash interfaces cited by
> Chapter 8 are checked; a general metatheorem comparing all directed families
> with HoTT fibrations is not claimed.

## C.3 The Generalized Endpoint

Both proofs teach the same strategic lesson in different formal languages:
when a statement about a fixed loop cannot be inducted on, vary its endpoint.

For the circle, one considers all `x:S¹` and paths
`base=x`. For `W`, one considers all objects `x`
and based arrows $*\to x$. The target family is the representable

$$
x\longmapsto\operatorname{Hom}_W(*,x).
$$

The crucial difference is what generalized elimination produces. Groupoidal
path induction produces equality. The contextual directed eliminator first
produces coherent arrow action, and at an arbitrary based arrow it yields a
directed 2-cell

$$
p\longrightarrow
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

Only the separate one-dimensionality premise converts that cell into
equality. Thus the directed proof factors the groupoidal conclusion into two
conceptually independent steps: normalization and dimension.

## C.4 What Was Not Transferred

The adaptation removes, rather than renames, the following ingredients:

- inverse paths and negative powers;
- predecessor action on the code;
- the claim that successor is an equivalence;
- a universe path produced from successor;
- cancellation in a group;
- equality as the first output of the hard inverse;
- the conclusion that the result is already a group isomorphism.

It also adds ingredients absent from the circle proof in this form:

- a separate `BNat` model whose definitional structure is not imposed
  on the HIT;
- a displayed contextual algebra comparing postcomposition with successor;
- a coherent directed spiral;
- a dimension witness used explicitly at the equality boundary;
- negative results proving the generator has no right inverse or
  omega-equivalence evidence.

These changes explain why a textual search-and-replace from
`S¹/Int` to `W/Nat` would be mathematically misleading.

## C.5 Stronger Comparisons

The carrier equivalence suggests two different strengthenings.

First, composition/addition compatibility should package the comparison as a
monoid isomorphism. Chapter 8 records this as a formal consequence of the
checked recursion and inverse laws, but the library does not yet expose the
package.

Second, free groupoidal realization should invert the generator without
silently adding an inverse inside the original directed category. That
comparison is now active. The functor from WalkingEnd to the Circle sends
natural powers to nonnegative Circle powers, and restriction along it is a
whole mapping equivalence from Circle maps into a groupoid to path-valued
WalkingEnd functors.

<!-- evidence:WE-GROUP-COMPLETION -->

> **Formal status — checked.** Evidence `WE-GROUP-COMPLETION`. This is a
> categorical universal property, not merely a carrier comparison with an
> integer one-object category. Chapter 27 develops the theorem and its
> category-indexed successor.

A reverse `BNat` functor, a packaged monoid isomorphism for the Chapter 8
carrier theorem, source functoriality of generic groupoidification, and the
resulting adjunction remain future layers. Keeping those claims separate is
precisely why the completed Circle comparison does not retroactively turn the
directed Nat proof into a group-valued proof.

## C.6 Attribution Method

The subsection order and proof strategy are structural adaptations from the
pinned HoTT sources. The prose in this edition is newly written. Each target,
source file, source label, and adaptation type is recorded before the
adaptation is committed. The book’s CC BY-SA 3.0 license and
[credits](#book-credits) preserve the upstream attribution and ShareAlike
requirements.
