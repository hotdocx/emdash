<a id="chapter-3"></a>

# 3. Logic, Propositions, And Sets

The propositions-as-types reading begins with a useful ambiguity. Any
classifier may be read as a proposition: to prove it is to construct an
inhabitant. But not every classifier behaves like a truth value. An inhabitant
of Bool tells us which Boolean was chosen; a natural number contains still
more data. Logic becomes precise only after we distinguish *having evidence*
from *having no relevant choice of evidence*.

This distinction is particularly important in a directed foundation. A
classifier may carry higher identity information even when the surrounding
category also carries noninvertible arrows. Proposition and set evidence
control the groupoidal identity layer; they do not erase directed structure.

<a id="chapter-3-1"></a>

## 3.1 Propositions As Types, Broadly Read

The basic logical readings are constructive:

$$
\begin{array}{c|c}
\text{statement} & \text{classifier}\\ \hline
P\text{ and }Q & P\times Q\\
P\text{ implies }Q & P\longrightarrow Q\\
\text{for every }x:A,\ P(x) & \prod_{x:A}P(x)\\
\text{there is }x:A\text{ with }P(x) & \sum_{x:A}P(x)\\
\text{falsehood} & \mathsf{Empty}.
\end{array}
$$

Under this reading, a proof of an existential statement contains a witness and
its evidence. A proof of an implication is an operation that transforms
evidence. Negation is

$$
\neg P:=P\longrightarrow\mathsf{Empty}.
$$

This is enough to state the negative theorems of Chapter 8. To prove that the
walking loop is not the identity, for instance, one assumes an equality and
constructs an inhabitant of Empty by mapping it to an impossible Nat equality.

What this reading does not supply is automatic proof irrelevance. If `P`
has two inhabitants, the bare fact that both prove a statement says nothing
yet about whether they are equal. That is a separate property of `P`.

<a id="chapter-3-2"></a>

## 3.2 Contractibility And Proposition-Valuedness

A classifier `A` is **contractible** when it has a chosen centre and a
path from that centre to every point:

$$
\mathsf{isContr}(A)
:=\sum_{a_0:A}\prod_{a:A}(a_0=a).
$$

Contractibility contains both existence and uniqueness, with uniqueness
understood homotopically. The centre is data, but the total classifier of
contractibility evidence is itself proposition-valued: any two such packages
are equal.

A classifier is **proposition-valued** when its identity classifiers are
contractible. In the familiar shorthand, any two of its inhabitants are
equal, and there is no further choice among the paths witnessing that fact.
It may be inhabited, like Unit, or uninhabited, like Empty. If it is inhabited,
it is contractible.

The adjective “proposition-valued” is deliberate. We still use every
classifier as a proposition in the broad Curry–Howard reading. The additional
property says that inhabitation carries no mathematical information beyond
truth.

<!-- evidence:LOGIC-TRUNCATION-PREDICATE -->

> **Formal status — checked.** Evidence `LOGIC-TRUNCATION-PREDICATE`
> covers `IsContr` and the recursive truncation predicate whose
> `-1` and `0` specializations are proposition- and set-valuedness.

<a id="chapter-3-3"></a>

## 3.3 Sets As A Homotopical Property

A classifier `A` is **set-valued** when every identity classifier
`x=y` is proposition-valued. Equivalently, any two parallel paths in
`A` are equal. This is the type-theoretic notion of a set: it concerns
the height of identity information, not membership in a global cumulative
set universe.

The hierarchy begins

$$
\begin{array}{ccl}
-2 &:& \text{contractible classifiers},\\
-1 &:& \text{proposition-valued classifiers},\\
0 &:& \text{set-valued classifiers},\\
1 &:& \text{groupoid-valued classifiers},\\
&\vdots&
\end{array}
$$

and each successor level asks that every identity classifier lie one level
lower. Chapter 7 develops this recursion uniformly. For now, sethood provides
the exact uniqueness principle needed for arithmetic codes.

Unit is proposition-valued because it is contractible. Empty is
proposition-valued by elimination: from an alleged first inhabitant one may
derive the required path data. Nat is set-valued by nested induction on its
visible constructors. Equality of zero with a successor reduces to Empty;
equality of two successors reduces to predecessor equality; the remaining
cases reduce to the proposition evidence for Unit or Empty.

<!-- evidence:LOGIC-NAT-SETHOOD -->

> **Formal status — checked.** Evidence `LOGIC-NAT-SETHOOD` supplies
> explicit terms witnessing that Unit and Empty are proposition-valued and
> Nat is set-valued. Nat sethood is not inferred merely from a rewrite table;
> it is an inhabitant of the internal `IsSetGrpd(Nat)` classifier.

<a id="chapter-3-4"></a>

## 3.4 Evidence Is Not Erasure

It is tempting to read “being a property” as permission for the kernel to
erase every proof to one constant. That is not the policy here. Emdash retains
evidence terms and proves that the classifier containing them is
proposition-valued.

For every level `n` and classifier `A`, the classifier

$$
\mathsf{isTrunc}_n(A)
$$

of evidence that `A` lies at level `n` is proposition-valued. Hence two
truncation witnesses are equal, but their constructors and projections remain
available to computation. This matters for packaged universes: a package can
retain both a carrier and its truncation evidence while still having equality
controlled by the carrier.

The same style recurs for equality-valued equivalence evidence. Rather than
declaring inverse-law proofs irrelevant by fiat, the theory proves that their
classifier is a proposition. Retained evidence supports computation and
transport; proposition-valuedness supports uniqueness and truncation.

<!-- evidence:LOGIC-TRUNCATION-EVIDENCE-PROP -->

> **Formal status — checked.** Evidence
> `LOGIC-TRUNCATION-EVIDENCE-PROP` establishes property-valuedness at
> every recursive truncation level. It introduces no proof-erasure rewrite.

<a id="chapter-3-5"></a>

## 3.5 Constructive Reasoning

The foundational rules used in this book are constructive. To prove
`P or Q` one must select a side in whatever sum-like interface is in
scope; to prove an existential one must provide a witness; to refute a claim
one must map its evidence to Empty. The law of excluded middle and double
negation elimination are not silently used as global inference rules.

This does not forbid classical mathematics. A classical principle can be
studied as additional structure, restricted to a suitable proposition-valued
universe, or derived in a context where decidability data are available. The
point is bookkeeping: a proof should reveal when such data enter.

The WalkingEnd theorem needs none. Its code is computed by functor action, its
inverse laws by contextual elimination and Nat induction, and its
noninvertibility by successor/zero discrimination. The argument is therefore
valid in the constructive core presented here.

> **Formal status — mathematical development.** This section states the
> logical discipline of the book. It does not claim a complete internal
> library of all connectives, propositional truncations, choice principles, or
> classical axioms.

<a id="chapter-3-6"></a>

## 3.6 Two Uses Of Sethood In The Main Calculation

Sethood enters Chapter 8 in two distinct ways.

First, Nat sethood controls equality in the code fibre `Path(Nat)`.
It ensures that higher coherence between arithmetic equalities is unique at
the needed level. This lets the power construction lift equality of naturals
without introducing uncontrolled higher data.

Second, the based hom carrier is proved set-valued after the calculation. One
proof comes directly from the one-dimensional signature of `W`; another
transports Nat sethood backward across the carrier equivalence. Agreement of
the conclusions does not collapse the proofs: each exposes a different reason
for sethood.

This is typical of univalent foundations. A property may be reached through
dimension, through equivalence, or through a direct induction. Since the
classifier of evidence is proposition-valued, the resulting witnesses agree,
yet their constructions remain mathematically informative.
