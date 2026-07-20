<a id="chapter-10"></a>

# 10. Categories, Precategories, And Categorical Identity

Chapter 2 introduced the categorical language needed for the WalkingEnd
calculation. We now return to the word *category* with a different question:
when should equality of objects agree with categorical sameness? The answer
depends on which categorical layer is under discussion. This second pass is a
spiral over Chapters 2, 4, and 7, not a replacement for their definitions.

The distinction is foundational. Ordinary univalent category theory begins
with set-valued homs and asks for an identity-to-isomorphism map to be an
equivalence. Emdash begins with iterated hom-categories, where arrows may have
directed higher arrows between them. The ordinary theory is therefore an
important specialization of functorial type theory, but it cannot serve as the
definition of the ambient native category.

## 10.1 A Translation Table, Not A Collapse

The following table fixes the translation used throughout the remainder of
the book.

| Layer | Characteristic data | Equality or height condition | Role here |
| --- | --- | --- | --- |
| Native `Cat` | objects and iterated `Hom_cat` classifiers | no set-valued-hom premise in the definition | ambient directed higher language |
| Equality-local `Path(A)` | elements of $A$ and identity evidence between them | every arrow is induced by equality | groupoidal specialization used for ordinary type theory |
| Finite `IsNCat` evidence, including `OneCat` | a native category plus a recursive hom-height witness | one-dimensionality makes each next hom discrete | bridge to ordinary category-shaped examples |
| HoTT precategory | a type of objects and set-valued homs | equality between parallel arrows is proposition-valued | ordinary 1-categorical specialization |
| HoTT category | a HoTT precategory for which object identity agrees with isomorphism | `idtoiso` is an equivalence | univalent 1-category notion, not the definition of native `Cat` |
| HoTT strict category | a HoTT precategory whose object type is a set | object identity is proposition-valued, without assuming `idtoiso` is an equivalence | a qualified truncation notion, unrelated to runtime strictness |

Three warnings belong beside the table.

First, *set-valued hom* means a truncation condition, not that a hom must be
presented by a classical set outside type theory. Second, *strict category* in
the HoTT sense refers to the truncation level of the object type; it says
nothing about which emdash expressions reduce at runtime. Third, a HoTT
strict category need not be a univalent category: object identity may be
proposition-valued while nontrivial isomorphisms remain. Finally, a `OneCat`
witness controls the height of a native category but does not by itself
identify object equality with isomorphism.

> **Formal status — mathematical development.** The table is a translation
> discipline, not an implemented equivalence of packages. A generic
> construction identifying native finite-height categories with HoTT
> precategories would have to choose the ordinary hom-set presentation and
> prove compatibility with native composition and object equality.

## 10.2 The Ordinary Precategory Specialization

An ordinary HoTT precategory $\mathcal A$ consists of:

- a type $\operatorname{Obj}(\mathcal A)$ of objects;
- for each $a,b$, a set $\operatorname{Hom}_{\mathcal A}(a,b)$;
- identity arrows $\mathrm{id}_a$;
- composition $g\circ f$, typed so that $f:a\to b$ and $g:b\to c$;
- left-unit, right-unit, and associativity equalities.

Because each hom is a set, equality between parallel arrows is a proposition.
The category laws therefore do not require an additional tower of coherence
data. This is precisely the simplifying hypothesis that ceases to be
available in a genuinely higher native category: there, the equality or cell
between two composites may itself have nontrivial higher structure.

The emdash specialization replaces an external record of hom sets by a native
category $C$ equipped with one-dimensional evidence. For every pair $x,y$,
the witness

$$
\operatorname{IsNCat}(1,C)
$$

makes the next hom-category
$\operatorname{Hom}_{C}(x,y)$ discrete. Its objects are the ordinary arrows;
the discreteness evidence controls their higher equality. The same witness
also implies the corresponding truncation bound on
$\operatorname{Obj}(C)$, but it still says nothing about whether every
ordinary isomorphism comes from object identity.

<!-- evidence:CAT-ITERATED-HOMS -->
<!-- evidence:CAT-DIMENSION -->

> **Formal status — checked.** Evidence `CAT-ITERATED-HOMS` and
> `CAT-DIMENSION`. Native `Cat` has category-valued homs, `IsNCat`
> recurses through those homs, and finite-dimensional evidence yields the
> predicted truncation evidence for the object classifier.

This gives a reliable rule of reading: use ordinary precategory reasoning
when the hom-height assumptions make it valid, but keep the native iterated
owner visible whenever a construction must act on the next cell.

## 10.3 Isomorphism And Identity-To-Isomorphism

For objects $a,b$ of an ordinary precategory, an isomorphism
$a\cong b$ consists of arrows

$$
f:a\longrightarrow b,
\qquad
g:b\longrightarrow a
$$

with $g\circ f=\mathrm{id}_a$ and
$f\circ g=\mathrm{id}_b$. Since the homs are sets, an inverse to a fixed
$f$ is unique when it exists. Consequently the type of isomorphism evidence
between two fixed objects is itself a set.

Object identity always produces an isomorphism. Given
$p:a=b$, identity induction defines

$$
\operatorname{idtoiso}_{\mathcal A}(p):a\cong b
$$

by sending reflexivity to the identity isomorphism. This map exists before
assuming univalence. The additional assertion that $\mathcal A$ is a
*category* in the HoTT sense is that

$$
\operatorname{idtoiso}_{\mathcal A}:
 (a=b)\longrightarrow(a\cong b)
$$

is an equivalence for every $a,b$.

<!-- evidence:UCAT-IDENTITY-ISOMORPHISM -->

> **Formal status — mathematical development.** Evidence
> `UCAT-IDENTITY-ISOMORPHISM`. This is the ordinary univalent
> 1-categorical theorem adapted from the HoTT category spine. It is not a
> theorem about every native `Cat`.

Univalence changes how one reasons about structure. A property or
construction invariant under isomorphism can be transported along object
identity because isomorphism and identity carry the same information. It
also implies that the object type of an ordinary category is a 1-type:
its identity types are equivalent to isomorphism types, and those are sets.

The effect on arrows is concrete. If $p:a=a'$, $q:b=b'$, and $f:a\to b$,
then transporting $f$ across both endpoint identities agrees with

$$
\operatorname{idtoiso}(q)
\circ f\circ
\operatorname{idtoiso}(p)^{-1}
:a'\longrightarrow b'.
$$

Thus endpoint transport is a lower-star cut at the target and an upper-star
cut at the source. This ordinary formula anticipates the represented-hom
actions used throughout the native calculus.

The implication should not be reversed carelessly. Having a 1-type of
objects does not make a precategory univalent, just as having discrete homs
does not force isomorphic objects to be equal.

## 10.4 Five Nearby Notions Of Sameness

The native theory places several useful notions next to one another. Their
proximity is a feature, but it is not an identification.

| Notion | Typical expression | What it compares |
| --- | --- | --- |
| object identity | $p:x=y$ in $\operatorname{Obj}(C)$ | two objects in the underlying equality layer |
| path-generated arrow | $\operatorname{path\_to\_hom}(p):x\to y$ | the directed arrow induced by object identity |
| ordinary isomorphism | $\operatorname{IsoEvidence}_C(x,y)$ | inverse arrows with equality-valued cancellation |
| carrier equivalence | $A\simeq B$ via `TypeEquiv` | two decoded groupoidal carriers |
| native omega-equivalence | $\operatorname{OmegaEquiv}_C(x,y)$ | a selected arrow with recursively usable inverse evidence |

There are checked maps between some adjacent entries. Object identity yields a
path-generated arrow and a transparent native omega-equivalence package.
Ordinary isomorphism evidence also yields native omega-equivalence evidence.
A `TypeEquiv`, however, compares carriers rather than two objects of an
arbitrary category, and it must not be substituted for categorical
equivalence without an explicit construction.

<!-- evidence:EQUIV-OMEGA -->
<!-- evidence:EQUIV-TYPE -->

> **Formal status — checked.** Evidence `EQUIV-OMEGA` and `EQUIV-TYPE`.
> The active interfaces expose object-path and carrier-equivalence
> constructions separately; neither declaration asserts a blanket
> identification of all five rows.

This ladder explains why the book qualifies the word *equivalence*. A theorem
about carrier equivalence, ordinary categorical equivalence, or recursive
omega-equivalence has different inputs and different higher consequences.

## 10.5 Equality-Local Categories

For a groupoidal classifier $A$, the native category

$$
\operatorname{Path}(A)
$$

has the elements of $A$ as objects and identity evidence $x=y$ as the hom
from $x$ to $y$. Reflexivity supplies identities, and ordinary functions act
functorially on paths. This is the native home of the familiar principle that
equality behaves like a groupoid.

<!-- evidence:CAT-PATH-CATEGORY -->

> **Formal status — checked.** Evidence `CAT-PATH-CATEGORY`.
> `Path_cat`, `Path_cat_func`, and `path_map_func` retain the
> equality-local category and its iterable functor action.

The ordinary and native readings coincide only under the appropriate height
condition. If $A$ is a 1-type, each identity type $x=y$ is a set, so
$\operatorname{Path}(A)$ can be read as an ordinary HoTT precategory. For a
general $A$, its identity types may have higher identity types, and the native
iterated-hom presentation retains them rather than truncating them away.

This example also separates groupoidality from directed categorical
univalence. Every arrow in $\operatorname{Path}(A)$ comes from identity by
construction. An arbitrary native category may contain noninvertible arrows,
and its identity layer cannot be recovered merely by declaring those arrows
to be paths.

## 10.6 Preorders, Posets, And Skeletal Reasoning

An ordinary preorder can be regarded as a precategory whose homs are mere
propositions: there is at most one arrow from $a$ to $b$. Isomorphism then
means $a\leq b$ and $b\leq a$. The preorder is a univalent category exactly
when this mutual reachability agrees with identity—the type-theoretic form of
antisymmetry. Thus posets are the proposition-valued-hom examples of the
general identity-to-isomorphism principle.

This example is useful because it exposes a frequent confusion. A skeletal
presentation says that isomorphic objects are literally or propositionally
the same in a chosen presentation. Univalence says that the canonical map
from identity to isomorphism is an equivalence, so the identification is
stable under dependent reasoning. The latter is an internal principle, not
merely a convention for selecting representatives.

The category of small sets is the other basic example. Its arrows are
functions, and its identity-to-isomorphism map is the restriction of the
identity-to-equivalence map for types. Universe univalence therefore makes it
a univalent category. Categories of groups, rings, and similar structures
follow when equivalence of carriers preserving the structure is shown to
agree with identity of the structured object. Chapter 15 develops that
structure-identity pattern.

> **Formal status — mathematical development.** The preorder/poset example is
> ordinary univalent 1-category theory, as are the category-of-sets and
> structured-object examples. The active code has proposition and set
> truncation evidence plus selected universe-univalence results, but no generic
> packaged preorder or structured-category construction is claimed here.

## 10.7 The Checked Ordinary-Isomorphism Lift

The active calculus supports one direction of the native comparison with no
finite-height premise. Given ordinary isomorphism evidence $i:x\cong y$, its
forward arrow and inverse laws define

$$
\operatorname{iso\_evidence\_omega\_equiv}(i):
\operatorname{OmegaEquiv}_C(x,y).
$$

The construction keeps the forward arrow selected by $i$ and packages its
inverse evidence in the recursive native facade. It is a structural lift, not
a decoder identifying isomorphism evidence with object identity.

<!-- evidence:EQUIV-ORDINARY-ISO-LIFT -->

> **Formal status — checked.** Evidence
> `EQUIV-ORDINARY-ISO-LIFT`. The owners are
> `iso_evidence_omega_along` and
> `iso_evidence_omega_equiv`; diagnostics check their projections and
> reflexive behavior.

This is the chapter's central checked theorem. It says that ordinary inverse
data is strong enough to enter the native equivalence calculus. It does not
say that native equivalence, ordinary isomorphism, and object identity are
interchangeable in every category.

## 10.8 The Native Univalence Boundary

A full categorical identity theorem for the ambient directed theory would
need to answer at least four questions.

1. Which equivalence classifier is compared with object identity?
2. Does the comparison retain a selected directed arrow?
3. How does it act on every next hom-category?
4. Under what height, saturation, or groupoidality hypotheses are the two
   directions inverse?

The active code has selected univalence theorems for groupoidal and truncated
universes, object-path-to-equivalence constructions, finite-height truncation,
and the one-way ordinary-isomorphism lift. It does not package a general
equivalence

$$
(x=y)\simeq\operatorname{IsoEvidence}_C(x,y)
$$

for arbitrary native $C$, nor a general saturation theorem that freely adds
such identities.

<!-- evidence:UNIV-FULL-OBJECT-ISO -->

> **Formal status — research boundary.** Evidence
> `UNIV-FULL-OBJECT-ISO`. A future owner must compare object identity and
> the selected categorical equivalence notion while remaining coherent with
> iterated hom action. Chapter 15 returns to this problem through the
> structure identity principle and Rezk-style saturation.

The title *univalent foundations* should therefore be read layer by layer.
Univalence is the disciplined alignment of identity with the appropriate
equivalence, not a license to erase the distinctions that make the directed
higher theory computational.
