<a id="chapter-17"></a>

# 17. Weighted Colimits, Duality, And Join

The preceding chapter classified cones by homs *into* a representing object.
Colimits classify cocones by homs *out of* one. Every variance reverses:
companions replace conjoints, left adjoints replace right adjoints, and the
universal arrows point away from the colimit.

Opposite duality makes this reversal a proof method rather than an invitation
to duplicate the theory. The active weighted-colimit classifier is defined
through the weighted-limit classifier in opposite categories. Its
preservation theorem is therefore the right-adjoint theorem of Chapter 16
applied once to the opposite adjunction.

The second half of the chapter gives this duality a directed geometry. The
join $A\star B$ contains a left part, a right part, and an internally natural
family of arrows directed from left to right. Its recursor has the same input
shape as the collage of a terminal profunctor. That observation connects
joins to weighted cone data while leaving the stronger collage semantics
explicitly open.

## 17.1 Weighted Cocones

Let

$$
F:J\longrightarrow B
$$

be a diagram and let

$$
W:J\rightsquigarrow J'
$$

be a contravariant weight, meaning a Cat-valued profunctor

$$
W:J^{\mathrm{op}}\times J'\longrightarrow\mathsf{Cat}.
$$

For fixed $j':J'$, the weight $W(-,j')$ is contravariant in $J$. At a
candidate target $b:B$, its expected cocone category is

$$
\operatorname{Cocone}_{W}(F;j',b)
\simeq
[J^{\mathrm{op}},\mathsf{Cat}]
\bigl(W(-,j'),\operatorname{Hom}_{B}(F-,b)\bigr).
$$

A $W$-weighted colimit is a functor

$$
C:J'\longrightarrow B
$$

with a representation

$$
\operatorname{Cocone}_{W}(F;j',b)
\simeq
\operatorname{Hom}_{B}(Cj',b)
$$

natural in $j'$ and $b$. Compare this with the limit equation

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
\operatorname{Hom}_{B}(b,Lj').
$$

The same words “represented by” occur in both formulas, but the representable
hom has changed side.

## 17.2 One Universal Owner Through Opposite Categories

For

$$
F:J\to B,
\qquad
W:J\rightsquigarrow J',
\qquad
C:J'\to B,
$$

the active definition is

$$
\operatorname{IsWeightedColimit}_{B}(F,W,C)
:=
\operatorname{IsWeightedLimit}_{B^{\mathrm{op}}}
\bigl(F^{\mathrm{op}},W^{\mathrm{op}},C^{\mathrm{op}}\bigr).
$$

Reversing the profunctor endpoints gives

$$
W^{\mathrm{op}}:(J')^{\mathrm{op}}\rightsquigarrow J^{\mathrm{op}},
$$

which is exactly the variance expected by the limit classifier in the
opposite categories. The representing equation there is

$$
\operatorname{Hom}_{B^{\mathrm{op}}}(b,Cj')
=
\operatorname{Hom}_{B}(Cj',b),
$$

so it recovers the desired cocone orientation.

The owner `WeightedColimit_con` is transparent to
`IsWeightedLimit_cov_comp` after applying `Op_func` and
`Op_prof`. The conversion operations between a limit witness and the
corresponding opposite colimit witness are identity-like wrappers after
double-opposite and product-swap computation. Colimit beta/eta therefore
comes from the same profunctor comparison used for limits.

<!-- evidence:OP-DUALITY -->

> **Formal status — checked.** Evidence `OP-DUALITY`. The involutive
> category, functor, transfor, profunctor, and adjunction operations justify
> the variance reversal. No independent colimit cancellation calculus is
> introduced.

## 17.3 Conical Colimits And Left Kan Extensions

The terminal-weight specialization now uses the opposite orientation:

$$
\mathbf 1^{J}:J\rightsquigarrow\mathbf 1.
$$

For a vertex $c:\mathbf 1\to B$, the active classifier

$$
\operatorname{IsWeightedColimit}
\bigl(F,\operatorname{TerminalProf}(J,\mathbf 1),c\bigr)
$$

is well formed. Under the standard semantic interpretation its fibres become
ordinary cocone categories, and the representation reads

$$
\operatorname{Cocone}(F,b)
\simeq
\operatorname{Hom}_{B}(c,b).
$$

Thus initial objects, coproducts, pushouts, and coequalizers are terminal
weight specializations on their usual indexing categories.

For a functor

$$
K:J\longrightarrow J',
$$

the companion has the required colimit variance:

$$
K_{\ast}:J\rightsquigarrow J',
\qquad
K_{\ast}(j,j')
=\operatorname{Hom}_{J'}(Kj,j').
$$

A selected left Kan-extension comparison is therefore

$$
\operatorname{IsWeightedColimit}
\bigl(F,K_{\ast},\operatorname{Lan}_{K}F\bigr).
$$

With the expected coend or cocone semantics, it gives the pointwise formula

$$
\operatorname{Hom}_{B}
\bigl((\operatorname{Lan}_{K}F)(j'),b\bigr)
\simeq
\operatorname{Nat}
\left(
  \operatorname{Hom}_{J'}(K-,j'),
  \operatorname{Hom}_{B}(F-,b)
\right).
$$

The focused variance audit checks both active substitutions:
`Terminal_prof J Terminal_cat` and `Companion_prof K` inhabit the
weight slot of `WeightedColimit_con`. As in Chapter 16, this does not by
itself identify the opaque opposite residual with a semantic category of
cocones.

<!-- evidence:WEIGHTED-COLIMIT-SPECIALIZATIONS -->

> **Formal status — formal consequence.** Evidence
> `WEIGHTED-COLIMIT-SPECIALIZATIONS`. The terminal-weight and companion
> classifiers, together with their preservation instances, follow from the
> active types and the opposite definition. Their standard conical and
> pointwise-left-Kan interpretations remain mathematical development under
> `WEIGHTED-END-KAN-SEMANTICS`.

The companion/conjoint distinction is now visible in one table:

| Construction along $K:J\to J'$ | Weight | Fibre |
| --- | --- | --- |
| right Kan extension | conjoint $K^{\ast}:J'\rightsquigarrow J$ | $\operatorname{Hom}_{J'}(j',Kj)$ |
| left Kan extension | companion $K_{\ast}:J\rightsquigarrow J'$ | $\operatorname{Hom}_{J'}(Kj,j')$ |

Suppressing the profunctor endpoints would make these formulas look
deceptively interchangeable. The endpoints are the type-level variance audit.

## 17.4 Left Adjoints Preserve Weighted Colimits

Let

$$
S:A\longrightarrow B,
\qquad
R:B\longrightarrow A,
\qquad
S\dashv R,
$$

and suppose

$$
C:J'\longrightarrow A
$$

carries a comparison certifying it as the $W$-weighted colimit of
$F:J\to A$. Passing to opposites turns the data into:

1. a weighted-limit comparison for $C^{\mathrm{op}}$ and
   $F^{\mathrm{op}}$ in $A^{\mathrm{op}}$;
2. the opposite adjunction
   $R^{\mathrm{op}}\dashv S^{\mathrm{op}}$;
3. a right adjoint $S^{\mathrm{op}}:A^{\mathrm{op}}\to B^{\mathrm{op}}$.

Theorem 16.1 therefore supplies a weighted-limit comparison represented by

$$
S^{\mathrm{op}}C^{\mathrm{op}}
=(SC)^{\mathrm{op}}.
$$

Turning the result back around gives a $W$-weighted-colimit comparison for
$SF$ represented by $SC$.

At the level of cocones, the three-comparison proof is the familiar chain

$$
\begin{aligned}
\operatorname{Cocone}_{W}(SF;b)
&\simeq
\operatorname{Cocone}_{W}(F;Rb),\\
&\simeq
\operatorname{Hom}_{A}(C,Rb),\\
&\simeq
\operatorname{Hom}_{B}(SC,b).
\end{aligned}
$$

The first and last steps are adjunction mates, and the middle step is the
given colimit representation. The implementation obtains this chain by
calling the right-adjoint theorem on `Op_adjunction`; it does not repeat the
three steps under new primitive names.

<!-- evidence:WEIGHTED-COLIMIT-PRESERVATION -->

> **Theorem 17.1 — Left adjoints preserve selected weighted colimits.**
> Given a computational $W$-weighted-colimit comparison for $F$ and an
> adjunction $S\dashv R$, the active construction returns a computational
> comparison for $SF$ represented by $SC$.
>
> **Formal status — checked.** Evidence
> `WEIGHTED-COLIMIT-PRESERVATION`. The owner
> `left_adjoint_preserves_weighted_colimit_con` applies
> `right_adjoint_preserves_weighted_limit_cov_comp` to the opposite
> adjunction. The theorem is conditional on the supplied colimit comparison.

Consequently, the terminal and companion specializations yield the familiar
interface-level corollaries: left adjoints preserve selected conical colimits
and selected left Kan extensions. No new proof is hidden behind either
phrase.

## 17.5 A Variance Ledger

The dual theorem can be remembered without reversing formulas in one’s head:

| Feature | Weighted limit | Weighted colimit |
| --- | --- | --- |
| weight | $J'\rightsquigarrow J$ | $J\rightsquigarrow J'$ |
| universal data | arrows $b\to Fj$ | arrows $Fj\to b$ |
| represented hom | $\operatorname{Hom}_{B}(b,Lj')$ | $\operatorname{Hom}_{B}(Cj',b)$ |
| Kan weight | conjoint | companion |
| preserving adjoint | right | left |
| proof | direct three-comparison chain | the same chain in opposites |

This ledger is more than notation. It identifies which endpoint acts by
upper-star precomposition and which acts by lower-star postcomposition. The
opposite construction exchanges those actions while preserving their
computational owners.

## 17.6 The Directed Join Signature

For native categories $A$ and $B$, the primitive join is a category

$$
A\star B
$$

with inclusion functors

$$
\iota_A:A\longrightarrow A\star B,
\qquad
\iota_B:B\longrightarrow A\star B.
$$

Its characteristic constructor is not an equality between the two parts. It
is an internally natural family of arrows from the left part to the right
part:

$$
\chi:
\mathbf 1_{A,B}
\Longrightarrow
\operatorname{Hom}_{A\star B}(\iota_A- ,\iota_B-),
$$

where

$$
\mathbf 1_{A,B}:A\rightsquigarrow B
$$

is the terminal profunctor. At objects, $\chi$ supplies

$$
\chi_{a,b}:\iota_A(a)\longrightarrow\iota_B(b).
$$

Because $\chi$ is a profunctor cell, naturality in both $a$ and $b$ is part
of one internal datum. It is not an externally quantified family followed by
a separately asserted equation. For shaped functors $a:I\to A$ and
$b:I\to B$, `join_cross_hom` evaluates the same cell to the corresponding
shaped cross arrow and retains its higher action.

There is no reverse constructor
$\iota_B(b)\to\iota_A(a)$. The join is directed even when $A$ and $B$
individually happen to be groupoidal.

## 17.7 Recursion And Its Three Beta Observations

To define a functor

$$
H:A\star B\longrightarrow E,
$$

the active nondependent recursor accepts:

1. a functor $F:A\to E$;
2. a functor $G:B\to E$;
3. an internally natural cross cell

   $$
   \gamma:
   \mathbf 1_{A,B}
   \Longrightarrow
   \operatorname{Hom}_{E}(F-,G-).
   $$

It returns `join_elim_func F G gamma`. The two restrictions compute:

$$
\begin{aligned}
H\circ\iota_A&\rightsquigarrow F,\\
H\circ\iota_B&\rightsquigarrow G.
\end{aligned}
$$

The selected observation of the image of the universal cross cell also
computes:

$$
H(\chi)\rightsquigarrow\gamma.
$$

The literal third owner is `join_elim_cross_transf`. It records the
cross-cell beta rule without adding a broad equation for arbitrary functor
application to primitive join syntax.

<!-- evidence:JOIN-RECURSOR -->

> **Formal status — checked.** Evidence `JOIN-RECURSOR`. The active
> owners are `Join_cat`, `join_fst_func`, `join_snd_func`,
> `join_cross_transf`, `join_cross_hom`, `join_elim_func`, and
> `join_elim_cross_transf`. The checked interface is a nondependent
> recursor with its three observations; it is not yet a uniqueness theorem
> for all functors out of the join.

The recursor repeats the book’s computational pattern. The inclusions and
cross cell introduce the join; restriction and the selected cross
observation eliminate it; matching introduction/elimination cuts reduce to
the supplied data.

## 17.8 Ordinary Cones And Cocones As Join Diagrams

The join makes the orientation of conical universal data concrete. A functor

$$
\mathbf 1\star J\longrightarrow B
$$

can be constructed from:

- an object $b:B$;
- a diagram $F:J\to B$;
- a natural family of cross arrows $b\to Fj$.

That is precisely the data of a cone from $b$ to $F$. Reversing the two
parts, a functor

$$
J\star\mathbf 1\longrightarrow B
$$

can be constructed from $F$, an object $c$, and arrows
$Fj\to c$: the data of a cocone.

This is an interface-level construction supplied by the recursor. It does not
yet assert an equivalence between a full mapping category out of the join and
a category of cones. Such an equivalence would require an eta or uniqueness
principle for join maps and coherent action on transformations between them.

The connection to weights is now visible. A conical cone uses the terminal
weight, and the join internalizes a terminal profunctor as its family of
left-to-right cross arrows. Replacing that terminal profunctor by an arbitrary
$P:A\rightsquigarrow B$ leads to the notion of a collage.

## 17.9 Join As A Directed Higher-Inductive Pattern

The join has the shape of a directed higher-inductive specification:

- two strata of objects, introduced through $A$ and $B$;
- a family of directed arrow constructors from every left object to every
  right object;
- a recursor into an arbitrary target;
- beta observations on the two strata and the cross family.

This comparison is architectural, not a claim that `Join_cat` was generated
by a general directed-HIT compiler. The primitive join is one selected
signature. Its cross constructor is already internally natural, which is the
category-level analogue of giving all boundary coherence with the
constructor.

WalkingEnd and join illustrate two different levels of the same programme.
WalkingEnd has an opaque point and endomorphism together with a contextual
dependent eliminator strong enough for encode-decode. Join has two
category-shaped introductions and a nondependent recursor, but no dependent
eliminator or computation of all its hom-categories. Thus join supplies a
promising stress test for a future directed-HIT schema without borrowing
properties proved only for WalkingEnd.

## 17.10 The Collage Comparison

For a profunctor

$$
P:A\rightsquigarrow B,
$$

its expected collage $\operatorname{Coll}(P)$ contains $A$ and $B$ as two
parts and uses $P(a,b)$ as the category of arrows from the left object $a$ to
the right object $b$. Its universal mapping property has the schematic form

$$
\operatorname{Fun}\bigl(\operatorname{Coll}(P),E\bigr)
\simeq
\sum_{F:A\to E}
\sum_{G:B\to E}
\operatorname{ProfCell}
\bigl(P,\operatorname{Hom}_{E}(F-,G-)\bigr).
$$

Taking $P=\mathbf 1_{A,B}$ gives exactly the *input shape* of the active join
recursor. This is strong design evidence for reading $A\star B$ as the
prospective collage of the terminal profunctor.

It is not yet a proof of that reading. A checked collage theorem would need:

1. an object decomposition into the left and right strata;
2. left-left and right-right hom comparisons recovering $A$ and $B$;
3. a left-right hom comparison recovering $P$;
4. a right-left hom description, normally initial in the free collage;
5. composition and higher action compatible with those four regions;
6. full faithfulness of the inclusions;
7. an equivalence of mapping categories, including uniqueness and higher
   transformations;
8. a dependent eliminator with beta behavior on the cross cells.

The active primitive supplies the inclusions, one terminal cross cell, and
the forward recursor only. It exposes none of the required hom
decompositions. Likewise, one expects an opposite comparison

$$
(A\star B)^{\mathrm{op}}
\simeq
B^{\mathrm{op}}\star A^{\mathrm{op}},
$$

but no such comparison is currently selected.

<!-- evidence:JOIN-COLLAGE-BOUNDARY -->

> **Formal status — research boundary.** Evidence
> `JOIN-COLLAGE-BOUNDARY`. Side task `FTTX-S13` owns the proposed
> collage semantics and dependent elimination. The current chapter claims
> only that the checked recursor has the terminal-collage input shape.

## 17.11 From Universal Cuts To Directed Geometry

Weighted limits and colimits began with a mapping problem: a profunctor of
cones or cocones is represented by a hom. Join begins with the same data from
the other side. Instead of representing a terminal family of cross arrows
inside a target, it freely presents a domain from which such data can be
interpreted by recursion.

The two constructions therefore complement one another:

$$
\begin{array}{c|c}
\text{weighted representation}
&
\text{directed join recursion}\\
\hline
\text{classifies maps into or out of a vertex}
&
\text{internalizes a family of cross arrows}\\
\text{beta/eta from a profunctor comparison}
&
\text{beta from introduction/recursion}\\
\text{arbitrary weight}
&
\text{currently the terminal profunctor}\\
\text{right/left adjoint preservation}
&
\text{prospective collage and dependent elimination}
\end{array}
$$

This is the globally coherent role of the active universal-construction
interfaces. Tensor, residuals, weighted representation, duality, and join are
not isolated features. Each controls a different kind of cut, and each leaves
enough categorical action visible for a future elaboration layer to compile
surface mathematics into the same computational core.
