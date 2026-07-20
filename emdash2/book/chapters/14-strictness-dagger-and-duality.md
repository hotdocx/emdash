<a id="chapter-14"></a>

# 14. Strictness, Dagger Structure, And Duality

The word *strict* enters category theory by several doors. A HoTT strict
category has a set of objects. An emdash naturality cut is strict when it
selects a runtime normal form. A rewrite is strict in yet another sense when
it is judgmental computation rather than internal equality. None of these
conditions implies either of the others.

The neighboring notion of a dagger illustrates why this vocabulary matters.
A dagger is a *chosen* reversal internal to one category, whereas the
opposite construction reverses any category from the outside. The distinction
is the same one that has guided the book throughout: a generic operation, a
selected structure, and a computational presentation have different owners.

This chapter adapts the strict- and dagger-category discussions of the
[HoTT Book](#ref-hott-book) to the ordinary 1-categorical specialization,
then states the additional coherence a native directed version would need.
Its central checked theorem is opposite duality. The dagger theory is
mathematical development with an explicit implementation boundary.

## 14.1 A Qualified Strictness Vocabulary

The following terms remain separate throughout the book.

| Qualified notion | Meaning | Does not imply |
| --- | --- | --- |
| HoTT strict category | an ordinary precategory whose object type is a set | category univalence |
| HoTT category | an ordinary precategory for which `idtoiso` is an equivalence | that the object type is a set |
| gaunt category | a HoTT category that is also strict | runtime strictness |
| native `IsNCat(n,C)` | recursive finite height of the hom-categories | object identity agrees with isomorphism |
| strict naturality cut | a selected `tapp1` composite reduces to one off-diagonal action | all coherence is judgmental |
| runtime strictness | an oriented kernel reduction chooses a normal form | object truncation or invertibility |
| dagger category | identity agrees with *unitary* isomorphism | identity agrees with every isomorphism |

In particular, the HoTT phrase *strict category* begins with a
**precategory**, not with a univalent category. Chapter 10’s translation table
uses this definition. A strict precategory may still have nontrivial
automorphisms that cannot come from its proposition-valued object identity.

## 14.2 Strict Categories In Ordinary Univalent Foundations

Let $\mathcal A$ be an ordinary precategory. It is *strict* when
$\operatorname{Obj}(\mathcal A)$ is a set:

$$
\prod_{x,y:\operatorname{Obj}(\mathcal A)}
\operatorname{isProp}(x=y).
$$

This condition says that two proofs of equality between objects agree. It
does not say that every isomorphism comes from equality. For example, the
one-object category associated to a nontrivial group is strict: its object
type is the unit type. It is not a HoTT category, since its nonidentity group
elements are automorphisms while the unique object has only the reflexive
identity path.

A poset on a set-valued carrier gives the contrasting example. Its homs are
propositions and antisymmetry identifies mutual reachability with object
identity, so it is both strict and univalent. More generally, a HoTT category
is strict exactly when it is *gaunt*: its isomorphisms contain no additional
object sameness beyond proposition-valued identity.

Strict categories therefore support a stricter package-level notion of
sameness than categorical equivalence. Equality of their presentations agrees
with isomorphism of the corresponding precategory structures, whereas an
equivalence can still change a presentation by choosing merely equivalent
objects. This can be useful, but it is not the default notion of sameness in
univalent category theory.

<!-- evidence:UCAT-STRICT-CATEGORY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-STRICT-CATEGORY`. The definition and the gauntness comparison belong
> to ordinary univalent 1-category theory. They are not a definition of
> native `Cat` or a theorem about arbitrary finite-dimensional native
> categories.

## 14.3 Three Native Notions That Strict Categories Do Not Control

Finite directed height is the first separate notion. A witness

$$
\operatorname{IsNCat}(n,C)
$$

recurses through native hom-categories. At dimension one it says that every
hom-category is discrete and entails that the object classifier is a
1-type. HoTT strictness instead asks directly that the object classifier be a
set. Neither condition supplies a native identity-to-isomorphism theorem.

The second notion is strict naturality. For an ordinary transfor
$\eta:F\Rightarrow G$, the generic off-diagonal action has the two reductions

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

The phrase *strict transfor* in this book describes this selected two-sided
cut behavior; it is not a new classifier of categories. A displayed lax
comparison can instead retain a directed naturality cell without forcing it
to equality.

The third notion is runtime strictness itself. The arrow
$t\rightsquigarrow u$ records a chosen normal form in the Lambdapi theory.
An internal equality $t=u$, a proof-time comparison, and a free-form
mathematical equation have different force. A category can have
proposition-valued object identity while none of its interesting operations
compute, or support rich directed higher cells while selected naturality cuts
do compute.

<!-- evidence:CAT-DIMENSION -->
<!-- evidence:TRANSF-STRICT-NATURALITY -->

> **Formal status — checked.** Evidence `CAT-DIMENSION` and
> `TRANSF-STRICT-NATURALITY`. The active theory separately checks recursive
> dimension/object truncation and the two ordinary `tapp1` naturality
> reductions. No checked theorem identifies these interfaces.

## 14.4 Opposite Duality Computes

For every native category $C$, the opposite category has the same objects and
reversed homs:

$$
\operatorname{Hom}_{C^{\mathrm{op}}}(x,y)
=\operatorname{Hom}_{C}(y,x).
$$

Identity arrows are unchanged, while the factors of composition reverse.
The active operation is involutive not only on categories but through the
iterable functor and transfor layers:

$$
\begin{aligned}
(C^{\mathrm{op}})^{\mathrm{op}}&\rightsquigarrow C,\\
(F^{\mathrm{op}})^{\mathrm{op}}&\rightsquigarrow F,\\
(\alpha^{\mathrm{op}})^{\mathrm{op}}&\rightsquigarrow\alpha.
\end{aligned}
$$

Opposite reverses vertical composition of transfors. It also turns an
adjunction

$$
F\dashv G
$$

into

$$
G^{\mathrm{op}}\dashv F^{\mathrm{op}}.
$$

The new unit is the opposite of the old counit, and the new counit is the
opposite of the old unit. Applying opposite twice reduces to the original
adjunction package. This is a computational duality, not a silent convention
that suppresses variance.

<!-- evidence:OP-DUALITY -->

> **Formal status — checked.** Evidence `OP-DUALITY`. The principal owners
> are `Op_cat`, `Op_func`, `Op_transf`, and `Op_adjunction`. Their
> involution and variance-reversal rules are the checked basis for the
> weighted-colimit duality in Chapter 17.

## 14.5 Dagger Structure Is Chosen Self-Duality

An ordinary †-precategory is a precategory $\mathcal A$ equipped with an
operation

$$
(-)^\dagger:
\operatorname{Hom}_{\mathcal A}(x,y)
\longrightarrow
\operatorname{Hom}_{\mathcal A}(y,x)
$$

satisfying

$$
\begin{aligned}
(\mathrm{id}_x)^\dagger&=\mathrm{id}_x,\\
(g\circ f)^\dagger&=f^\dagger\circ g^\dagger,\\
(f^\dagger)^\dagger&=f.
\end{aligned}
$$

Equivalently, it is an identity-on-objects functor-like map

$$
D:\mathcal A^{\mathrm{op}}\longrightarrow\mathcal A
$$

with a chosen involution law. The word *chosen* is essential. The opposite
construction gives $\mathcal A^{\mathrm{op}}$ for every $\mathcal A$; it
does not give a functor from that opposite back to $\mathcal A$, much less
one that fixes objects and squares to the identity.

## 14.6 Unitary Arrows And Dagger Univalence

An arrow $f:x\to y$ is *unitary* when its dagger is its two-sided inverse:

$$
f^\dagger\circ f=\mathrm{id}_x,
\qquad
f\circ f^\dagger=\mathrm{id}_y.
$$

Every unitary arrow is an isomorphism, but an isomorphism need not be unitary.
Object identity always produces a unitary isomorphism by identity induction,
so there is a canonical map

$$
\operatorname{idtoUnitary}_{\mathcal A}:
(x=y)\longrightarrow(x\cong_\dagger y).
$$

A †-category is a †-precategory for which this map is an equivalence. Its
selected notion of object sameness is unitary isomorphism, not arbitrary
isomorphism.

Two examples separate the notions. In a groupoid, define
$f^\dagger=f^{-1}$; then every arrow is unitary. For finite-dimensional inner
product spaces with arbitrary linear maps, the dagger is the adjoint linear
map. The unitary isomorphisms are the isometries, while many invertible linear
maps are not unitary. Thus this †-category need not be a HoTT category under
ordinary isomorphism.

<!-- evidence:UCAT-DAGGER-CATEGORY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-DAGGER-CATEGORY`. This is the ordinary set-valued-hom theory:
> dagger laws are equalities, unitarity is a property, and dagger univalence
> compares object identity with unitary isomorphism.

## 14.7 Opposite, Duality, And Dagger Compared

The three reversal notions have different input data.

| Construction | Data supplied | Result |
| --- | --- | --- |
| opposite | any category $C$ | a category $C^{\mathrm{op}}$ with arrows reversed |
| categorical duality | a chosen equivalence $C^{\mathrm{op}}\simeq D$ | a comparison between two categories |
| dagger | a chosen identity-on-objects involutive map $C^{\mathrm{op}}\to C$ | a unitary notion internal to $C$ |

A native dagger would have to act at every retained hom dimension. At minimum
it would require:

1. a functor $D:C^{\mathrm{op}}\to C$;
2. identity-on-objects data, with an explicit decision about whether it
   computes or is witnessed coherently;
3. an involution comparison between $D\circ D^{\mathrm{op}}$ and
   $\mathrm{id}_C$;
4. compatibility of that comparison with off-diagonal and higher action;
5. a unitary-arrow classifier whose evidence is stable under identity,
   composition, and the next hom action;
6. a qualified identity-to-unitary-equivalence interface.

The ordinary equations above are a plausible strict specialization of this
design, not a license to erase the higher coherence. In particular,
`Op_cat` supplies only the first half of the ambient reversal and cannot
serve as a native dagger by itself.

<!-- evidence:NATIVE-DAGGER-INTERFACE -->

> **Formal status — research boundary.** Evidence
> `NATIVE-DAGGER-INTERFACE`. No dagger/unitary owner is active. Side task
> `FTTX-S12` remains a specification target, and this chapter does not add
> a prose-only kernel name or infer dagger structure from opposite duality.

## 14.8 Duality As A Proof Method

Opposite duality becomes useful when a theorem has already exposed its
variance. A right adjoint preserves weighted limits because a representable
comparison can be transported through its hom adjunction. Passing to
opposites exchanges:

$$
\begin{aligned}
\text{right adjoint}&\longleftrightarrow\text{left adjoint},\\
\text{weighted limit}&\longleftrightarrow\text{weighted colimit},\\
\text{unit}&\longleftrightarrow\text{counit},\\
\text{upper-star source action}&\longleftrightarrow
  \text{lower-star target action}.
\end{aligned}
$$

Chapter 17 will use these checked opposite owners to derive the colimit
preservation theorem rather than repeat the limit proof with reversed arrows.
A dagger could internalize a particular self-dual instance of such an
argument, but the general theorem needs only opposite duality. This is why the
book includes dagger structure for conceptual completeness without making it
the foundation of categorical duality.
