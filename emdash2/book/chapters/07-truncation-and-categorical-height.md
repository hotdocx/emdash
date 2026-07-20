<a id="chapter-7"></a>

# 7. Truncation And Categorical Height

An induction principle tells us how to construct data. A truncation principle
tells us how much distinction that data can retain. These ideas meet in the
walking-endomorphism proof: contextual elimination first constructs a
directed 2-cell, and one-dimensionality then shows that the parallel
1-arrows it connects are equal.

There are two related height measures in emdash. Recursive groupoidal
truncation measures the identity types of a classifier. Recursive categorical
dimension measures the hom-categories of a directed category. They agree in
important boundary cases, but they are not the same definition. Keeping them
separate lets us use equality locally without declaring all directed arrows
invertible.

## 7.1 Recursive Truncation

The truncation levels begin at `-2` and continue by successor. For a
classifier `A`, define

$$
\begin{aligned}
\mathsf{isTrunc}_{-2}(A)
  &:=\mathsf{isContr}(A),\\
\mathsf{isTrunc}_{n+1}(A)
  &:=\prod_{x,y:A}\mathsf{isTrunc}_{n}(x=y).
\end{aligned}
$$

Thus:

- a `(-2)`-truncated classifier is contractible;
- a `(-1)`-truncated classifier is a proposition;
- a `0`-truncated classifier is a set;
- a `1`-truncated classifier has set-valued identity types;
- each further level permits one more layer of identity structure.

The recursive equation is the important part. To prove that `A` is
`(n+1)`-truncated, one proves that every identity classifier `x=y`
is `n`-truncated. Truncation arguments can therefore descend through
identity types until they reach contractibility.

<!-- evidence:LOGIC-TRUNCATION-PREDICATE -->

> **Formal status — checked.** Evidence
> `LOGIC-TRUNCATION-PREDICATE`. `IsTruncGrpd` implements this
> recursion, with `IsPropGrpd` and `IsSetGrpd` as the proposition
> and set abbreviations.

This is a property of an existing classifier. Supplying
`h:isTrunc_n(A)` does not replace `A` by a quotient, erase its
points, or create a new type. It certifies that higher identity distinctions
already collapse at the stated level.

## 7.2 Truncation Evidence Is Itself A Property

There may be many expressions witnessing that `A` is `n`-truncated.
Mathematically, the choice should not matter. The evidence classifier itself
is proposition-valued:

$$
\mathsf{isProp}\bigl(\mathsf{isTrunc}_n(A)\bigr).
$$

Consequently any two truncation witnesses are equal. Packages may retain the
witness for later use without turning it into observable structure.

<!-- evidence:LOGIC-TRUNCATION-EVIDENCE-PROP -->

> **Formal status — checked.** Evidence
> `LOGIC-TRUNCATION-EVIDENCE-PROP`. The theorem is uniform in the
> truncation level and the classifier.

There is a useful distinction between **retaining** evidence and
**erasing** it. Emdash generally retains evidence in Sigma-like packages so a
consumer can project it. Proposition-valuedness then proves that two choices
are equal when equality is needed. This is constructive proof irrelevance,
not an instruction to remove the field from the data representation.

## 7.3 Closure Principles

The recursive definition supports the standard structural operations.

First, truncation is monotone:

$$
\mathsf{isTrunc}_n(A)
\longrightarrow
\mathsf{isTrunc}_{n+1}(A).
$$

A type with no distinctions above level `n` also has none above the
weaker level `n+1`.

Second, dependent functions preserve a pointwise truncation bound. If every
`B(x)` is `n`-truncated, then

$$
\prod_{x:A}B(x)
$$

is `n`-truncated. At successor levels the proof uses the equivalence
between equality of functions and pointwise equality.

Third, dependent sums preserve a common bound. If `A` and every
`B(x)` are `n`-truncated, then

$$
\sum_{x:A}B(x)
$$

is `n`-truncated. The successor proof analyzes equality of dependent
pairs as a base path together with a path over it.

<!-- evidence:TRUNC-CLOSURE -->

> **Formal status — checked.** Evidence `TRUNC-CLOSURE`. The active
> operations are `is_trunc_grpd_succ`, `is_trunc_pi`, and
> `is_trunc_sigma`, each with recursive base and successor behavior.

Truncation is also invariant under equivalence and closed under retracts. For
the latter, suppose `Y` is a retract of `X`: there are maps

$$
Y\xrightarrow{s}X\xrightarrow{r}Y
$$

with `r circ s` equal to the identity on `Y`. Any truncation
bound on `X` descends to `Y`.

<!-- evidence:TRUNC-RETRACT -->

> **Formal status — checked.** Evidence `TRUNC-RETRACT`.
> `is_trunc_retract` works uniformly at every recursive truncation
> level from explicit retraction data.

These closure results are not merely a catalogue. Pi closure makes
proposition evidence stable under universal quantification; Sigma closure
controls total spaces and evidence-retaining universes; retract closure lets a
normalization or equivalence argument transfer height to a less explicit
carrier.

## 7.4 Universes Of Truncated Classifiers

For each level `n`, the package

$$
\mathsf{TruncGrpdU}(n)
  :=\sum_{A:\mathsf{Grpd}}\mathsf{isTrunc}_n(A)
$$

retains a classifier and its truncation evidence. Since the evidence is a
proposition, equality of packages is governed by the carriers rather than by
an arbitrary choice of proof.

The selected truncated-universe univalence theorem identifies package
equality with carrier equivalence:

$$
(X=Y)
\simeq
\mathsf{TypeEquiv}
  (\mathsf{carrier}(X),\mathsf{carrier}(Y)).
$$

Both directions and their round trips are named. This is a useful, precise
univalent universe: it ranges over classifiers already equipped with one
fixed truncation bound.

<!-- evidence:UNIV-TRUNCATED -->

> **Formal status — checked.** Evidence `UNIV-TRUNCATED`. The package
> is `TruncGrpdU`; `trunc_grpd_univalence_type_equiv` supplies the
> carrier equivalence between package identity and `TypeEquiv`.

The adjective “restricted” matters. This theorem does not by itself identify
objects in an arbitrary directed category with ordinary categorical
isomorphisms. Nor does it construct a truncation of an arbitrary input. It is
a univalence theorem for an evidence-retaining subuniverse of the groupoidal
classifier universe.

## 7.5 Finite Directed Dimension

Truncation follows identity types. Directed dimension follows hom-categories.
The nonnegative dimension codes are generated by

$$
0_{\mathsf{cat}}
\qquad\text{and}\qquad
\mathsf{succ}_{\mathsf{cat}}(n).
$$

Their classifier is recursive:

$$
\begin{aligned}
\mathsf{isNCat}(0,C)
  &:=\mathsf{isDiscreteCat}(C),\\
\mathsf{isNCat}(n+1,C)
  &:=\prod_{x,y:\operatorname{Obj}(C)}
       \mathsf{isNCat}
       \bigl(n,\operatorname{Hom}_C(x,y)\bigr).
\end{aligned}
$$

A zero-dimensional category is discrete. A one-dimensional category may have
nonidentity directed 1-arrows, but each of its hom-categories is discrete. A
two-dimensional category may have nontrivial 2-cells, while the next homs are
discrete, and so on.

There is a corresponding object-truncation level:

$$
\begin{aligned}
\mathsf{catLevel}(0)&=0,\\
\mathsf{catLevel}(n+1)&=mathsf{catLevel}(n)+1.
\end{aligned}
$$

If `C` has categorical dimension `n`, then its object classifier is
truncated at `catLevel(n)`. In particular, objects of a discrete category
form a set, and objects of a one-dimensional category form a 1-truncated
classifier.

<!-- evidence:CAT-DIMENSION -->

> **Formal status — checked.** Evidence `CAT-DIMENSION`. `IsNCat`
> owns the homwise recursion, `cat_dim_trunc_level` computes the
> corresponding groupoidal level, and `ncat_obj_trunc` proves the
> object-truncation consequence.

This bridge does not collapse the two notions. `IsNCat` constrains all
iterated directed homs; object truncation records only equality structure on
the object classifier. Two categories can have equally truncated object
classifiers while differing radically in their directed arrows.

## 7.6 One-Dimensionality Of The Walking Endomorphism

The WalkingEnd signature contains

$$
\mathsf{isNCat}(1,W).
$$

Unfolding the successor clause gives, for every `x,y:Obj(W)`,

$$
\mathsf{isDiscreteCat}
  \bigl(\operatorname{Hom}_W(x,y)\bigr).
$$

In particular the based hom

$$
H_x:=\operatorname{Hom}_W(*,x)
$$

is discrete. Given two based arrows `p,q:*\to x`, a directed
2-cell

$$
\alpha:p\longrightarrow q
\quad\text{in }H_x
$$

can therefore be converted to an equality `p=q` of objects of the
hom-category.

<!-- evidence:WE-ONE-DIMENSIONAL -->

> **Formal status — checked.** Evidence `WE-ONE-DIMENSIONAL`.
> `walking_end_hom_discrete` specializes the dimension witness, and
> `walking_end_based_cell_to_path` converts a based 2-cell to equality.

This operation is local to the next hom. It does **not** produce an arrow
`q\to p`, an inverse for `p`, or an inverse for `ell` in
`W`. Equality between the *objects of a discrete hom-category* and
invertibility of those objects as *arrows of the ambient category* are
different statements.

## 7.7 The Exact Height Step In Encode–Decode

Chapter 8 constructs, for every based arrow `p:*\to x`, a directed
normalization cell

$$
\nu_p:
p\longrightarrow
\mathsf{decode}_x(\mathsf{encode}_x(p))
$$

inside `H_x`. Only then does hom-discreteness give

$$
p=
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

This is the sole step in the hard inverse where one-dimensionality is used.
It converts already-constructed directed information into equality; it does
not help construct the information.

The other inverse,

$$
\mathsf{encode}_*(\ell^n)=n,
$$

is proved independently by Nat induction using the zero and successor
computations. It does not require hom-discreteness. Nat sethood plays two
nearby but distinct roles: it makes the concrete `BNat` hom-category
discrete, and it can be transported backward along the final carrier
equivalence to give a second proof that the based-endomorphism carrier is a
set. Neither role should be substituted for the directed normalization step.

This separation is a model for later proofs:

1. build a cell using functorial or contextual action;
2. invoke a dimension hypothesis at the exact hom level where the cell lives;
3. extract equality only if the target theorem needs it.

The intermediate cell can carry an orientation or support further
composition even when its equality shadow cannot.

## 7.8 Properties Are Not Reflectors

A general truncation operation would assign to every classifier `A` a
new classifier `||A||_n`, together with a universal map and an
elimination principle into `n`-truncated targets. In a directed setting
one may also ask for categorical truncations that collapse cells above a
chosen dimension while preserving lower directed structure.

The active layer does not provide either general reflector. It provides
predicates on existing classifiers, closure theorems, evidence-retaining
universes, and consequences of finite categorical dimension. Those tools are
enough for the WalkingEnd calculation because its one-dimensionality is
signature data rather than something that must be freely imposed afterward.

<!-- evidence:TRUNC-REFLECTOR -->

> **Formal status — research boundary.** Evidence `TRUNC-REFLECTOR`.
> A general truncation HIT or directed categorical reflector remains future
> work and must come with its own universal and computational properties.

We now have every prerequisite for the main proof: equality-local action,
functors and directed families, contextual elimination, equivalence packages,
recursive truncation, and homwise categorical height. The next chapter puts
them together without identifying direction with invertibility.
