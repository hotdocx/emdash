<a id="chapter-28"></a>

# 28. Laxity, Interchange, And The Gray Direction

Functoriality is often printed as an equation:

$$
F(g)\circ F(f)=F(g\circ f).
\tag{28.1}
$$

In a directed higher setting, the more informative object is the comparison
cell that (28.1) would erase. Its source is the composite of the two separate
arrow actions, its target is the action on the composite arrow, and its next
action records how that comparison varies. When the cell is invertible, one
has pseudo-functorial behaviour. When it is an identity, one has a selected
strict behaviour. When it is merely directed, one has genuine laxity.

The previous chapters repeatedly changed the *target* of such a witness. In a
path category it became invertible. In a strict computational profile it
specialized to identity. This chapter keeps the target directed and asks where
the noninvertible cell itself comes from. The answer is not an extra square
axiom. It is a component of the same whole internal action that already
supports dependent transport and ordinary naturality.

The geometric test is the walking square. Let
$I=\mathsf{WalkingArrow}$ and consider a selected tensor-shaped category
$I\otimes_R I$. Its four vertices and four boundary arrows are derived from
coevaluation. The two routes from the source corner to the opposite corner
need not be equal. A directed **interchanger** compares them. Recovering that
cell from whole laxity, and retaining one further action, is the checked
centre of the chapter.

## 28.1 Whole Laxity Before Components

Let $F,G:A\to B$ be functors and let
$\epsilon:F\Rightarrow G$ be a transformation. The off-diagonal action of
$\epsilon$ does more than assign a component at each object. Given an arrow
$f:X\to Y$, it supplies a cell

$$
\epsilon[f]:F(X)\longrightarrow G(Y)
\tag{28.2}
$$

in the appropriate internal hom. Now compose on the target side with an arrow
$g:Y\to Z$. There are two whole functors, varying in $f$, whose readable
values are

$$
G(g)\circ\epsilon[f]
\qquad\text{and}\qquad
\epsilon[g\circ f].
\tag{28.3}
$$

More explicitly, after $X$, $g$, and the transformation have been fixed, the
two expressions in (28.3) are the object actions of functors

$$
\operatorname{Hom}_A(X,Y)
\longrightarrow
\operatorname{Hom}_B(FX,GZ).
$$

The comparison between them is therefore allowed to vary over the *whole*
hom category. This is the categorical content hidden by the familiar
pointwise naturality equation: the input arrow is still an object of an
internal hom and may itself have higher arrows.

The internal displayed action supplies a whole transformation from the first
functor to the second. Its component is the post/left laxity cell

$$
\lambda^{\mathrm{post}}_{\epsilon,g,f}:
G(g)\circ\epsilon[f]
\Longrightarrow
\epsilon[g\circ f].
\tag{28.4}
$$

There is a target-internalized mirror producing the pre/right comparison.
These are not two unrelated naturality squares. Both are ordinary
specializations of a displayed transformation acting in a dependent hom. The
displayed owner first retains transport in the source and target fibres; the
ordinary surfaces appear only after the relevant families are specialized to
representables.

The pre/right mirror fixes the target side and varies an arrow entering the
source. Its readable comparison has the complementary form

$$
\epsilon[f]\circ F(h)
\Longrightarrow
\epsilon[f\circ h].
$$

Post/left and pre/right are skew views of one off-diagonal action. They need
not be identified by a pointwise square equation before their whole owners
have been compared. The explicit orientation becomes important when one of
the two views is selected for the Gray interchanger.

This order of construction matters. If one wrote only the component (28.4),
the variable $f$ and its higher arrows would already have been capped. By
retaining the whole transformation first, the ordinary hom action may be
applied again. The next level acts on a cell between $f_0$ and $f_1$ and
returns a cell between the corresponding laxity boundaries. Iteration, not a
manually appended coherence record, supplies the higher observation.

The usual functor compositor is obtained by taking
$\epsilon$ to be the identity transformation of $F$. At the appropriate
identity component, (28.4) reads

$$
\phi^F_{g,f}:F(g)\circ F(f)\Longrightarrow F(g\circ f).
\tag{28.5}
$$

Thus the compositor is an identity-transformation specialization of whole
naturality. It is not postulated independently of the transformation
calculus. The same provenance is what allowed Chapter 25 to realize it as a
path and Chapter 27 to retain it on the groupoidification unit.

<!-- evidence:FUNCTORD-WHOLE-LAXITY -->

> **Formal status — checked.** Evidence `FUNCTORD-WHOLE-LAXITY`. The displayed
> internal action owns a whole laxity transformation. Ordinary post/left and
> pre/right transformations are transparent specializations; their capped
> cells recover the displayed witness; and the ordinary functor compositor is
> the identity-transformation specialization. The next hom action remains
> available. No independent naturality square is added.

## 28.2 Strictness As A Computational Profile

It is tempting to define a strict functor as an ambient functor equipped with
a path saying that its compositor equals an identity. In a univalent setting
that path describes an invertible comparison, but it does not make the
compositor compute to identity. It is therefore evidence of canonical
pseudo-functoriality, not a computational strictness discriminator.

An evidence package
$\sum_{F:\operatorname{Functor}(A,B)}\mathsf{IsStrict}(F)$ would have the same
problem if its second field were merely path-valued. Projecting its first
field would return an arbitrary ambient functor, after which conversion could
no longer tell whether strict computation had been selected. The code sort in
(28.6) keeps the discriminator at the head of the decoded term.

The selected strict boundary is instead a code and decoder:

$$
\begin{aligned}
\mathsf{StrictFunctorData}(A,B)&:\mathcal U,\\
\operatorname{decode}_{A,B}&:
\mathsf{StrictFunctorData}(A,B)\longrightarrow\operatorname{Functor}(A,B).
\end{aligned}
\tag{28.6}
$$

The decoder is a stable head. When the generic compositor (28.5) is applied
to a decoded strict code, it reduces to the identity cell. A rigid ambient
functor outside this code sort does not acquire that reduction. Strictness is
therefore selected by syntax with computational meaning rather than inferred
from a propositional field after the fact.

This does not require a second functor theory. Define the profiled internal
hom

$$
\mathsf{GrayHom}_{\mathrm{lax}}(A,B)
\tag{28.7}
$$

to have strict-functor codes as objects and the existing ambient
transformation categories between their decoded carriers as homs:

$$
\begin{aligned}
\operatorname{Obj}(\mathsf{GrayHom}_{\mathrm{lax}}(A,B))
  &\equiv\mathsf{StrictFunctorData}(A,B),\\
\operatorname{Hom}(S,T)
  &\equiv
  \operatorname{Transf}(\operatorname{decode}S,\operatorname{decode}T).
\end{aligned}
\tag{28.8}
$$

Identity and composition delegate to the ambient functor category. Homs
between transformations are the existing modification categories, and every
subsequent hom is reused. A whole inclusion decodes objects into
$\operatorname{Functor}(A,B)$ and acts as the identity on this shared
transformation tower.

The word *lax* in (28.7) describes the arrow profile. Objects are
computationally strict functors; arrows are the ambient transformations whose
off-diagonal action retains laxity. The category is not definitionally the
ambient functor category, and an arbitrary ambient functor is not silently
accepted as one of its objects.

The selected identity illustrates the separation. There is an identity
strict code whose decoded carrier has a whole equality to the ambient identity
functor. The decoder does not simply unfold to that identity everywhere:
keeping its head stable is what lets compositor computation recognize the
strict profile without racing the generic object and arrow actions. Semantic
comparison and computational discrimination are both retained, but they have
different owners.

This profile architecture scales better than duplicating products, pullbacks,
transformations, and modifications for each preservation mode. A later
consumer may introduce another code sort or another object profile while
sharing the same hom tower. Duplication is justified only where a genuinely
different computation must be selected.

<!-- evidence:GRAY-COMPUTATIONAL-PROFILE -->

> **Formal status — checked.** Evidence `GRAY-COMPUTATIONAL-PROFILE`.
> Computational strictness is selected by a primitive code sort and stable
> decoder. Its generic compositor specializes to identity, while a rigid
> unprofiled functor does not. GrayHom_lax reuses the complete ambient
> transformation and higher-hom tower and includes wholly into the functor
> category; no duplicate modification hierarchy or broad category-head
> conversion is introduced.

## 28.3 One Selected Right Closure

The tensor-shaped category used here is characterized through one right
closure. For categories $A,B,C$, the checked boundary is

$$
\mathsf{GrayHom}_{\mathrm{lax}}(A\otimes_R B,C)
\simeq_{\omega}
\mathsf{GrayHom}_{\mathrm{lax}}
  \bigl(A,\mathsf{GrayHom}_{\mathrm{lax}}(B,C)\bigr).
\tag{28.9}
$$

The tensor head $A\otimes_R B$ is stable and distinct from the Cartesian
product. Curry and uncurry in (28.9) are whole computationally strict functors
between the two profile categories. Their composites are compared with the
appropriate identity functors by whole beta and eta paths, and the resulting
fixed-forward equivalence retains hom action.

Equation (28.9) is an equivalence of profiled mapping *categories*. On the
left, objects are strict codes for maps out of the selected tensor and arrows
are ambient transformations. On the right, an outer strict code selects, at
each object of $A$, an inner strict code $B\to C$; its arrows are allowed the
lax transformation behaviour retained by (28.7). Curry and uncurry transport
not only objects but this transformation tower.

The adjective *right* fixes which variable is moved into the internal hom. A
mirror closure would instead expose the opposite orientation and its
corresponding lax or oplax convention. The present theorem chooses one of
these directions rather than asserting that they have already been related.

Coevaluation is not another primitive:

$$
\operatorname{coev}_{A,B}:
A\longrightarrow
\mathsf{GrayHom}_{\mathrm{lax}}(B,A\otimes_R B)
\tag{28.10}
$$

is curry applied to the strict identity code on $A\otimes_R B$. Dually,
evaluation is uncurry applied to the strict identity code of the internal hom.
These two maps give introduction and elimination for the selected tensor
boundary.

The introduction/elimination reading is concrete. Coevaluation builds a
generic tensor point by currying the identity, while evaluation consumes a
profiled inner map by uncurrying the identity. Their whole beta/eta paths are
the computational boundary through which the walking-square observations are
derived. The square is not added beside the closure.

<!-- evidence:GRAY-RIGHT-CLOSURE -->

> **Formal status — checked.** Evidence `GRAY-RIGHT-CLOSURE`. Whole strict curry
> and uncurry package the right-closure equivalence (28.9), with whole beta/eta
> and hom action. Coevaluation and evaluation are derived at selected identity
> codes. The tensor remains distinct from the Cartesian product and the beta
> comparison is equality evidence, not a competing object-level runtime fold.

There is a complementary combinatorial route to Gray products. In
[Hadzihasanovic](#ref-hadzihasanovic), Gray products are constructed on
directed cell complexes and oriented cubes are studied as shapes in their own
right. That perspective supplies an important model-independent picture of
the square and its higher-dimensional successors. The emdash result has a
different boundary: it begins with one profiled internal hom and selects the
right closure (28.9). It does not construct the tensor combinatorially or
prove agreement with Hadzihasanovic's Gray product.

## 28.4 The Walking Square From Coevaluation

Take $I=\mathsf{WalkingArrow}$, the join-derived directed interval of
Chapter 27, and form

$$
\mathsf{Square}_R:=I\otimes_R I.
\tag{28.11}
$$

Evaluating coevaluation at the two outer endpoints produces two strict inner
functors $I\to\mathsf{Square}_R$. Evaluating those functors at the two inner
endpoints gives four vertices
$v_{00},v_{01},v_{10},v_{11}$. Their arrow actions on the walking generator
give the horizontal edges $a_0,a_1$. The outer generator acts through
coevaluation as one whole transformation between the inner functors; its two
components give the vertical edges $b_0,b_1$:

$$
\begin{array}{ccc}
v_{00}&\xrightarrow{\ a_0\ }&v_{01}\\
{\scriptstyle b_0}\big\downarrow&&\big\downarrow{\scriptstyle b_1}\\
v_{10}&\xrightarrow{\ a_1\ }&v_{11}.
\end{array}
\tag{28.12}
$$

The first index in $v_{ij}$ records the outer endpoint and the second records
the inner endpoint. Thus $a_0$ and $a_1$ are the inner generator evaluated in
the two outer fibres. The arrows $b_0$ and $b_1$ are not obtained by applying
two unrelated maps: they are the two object components of the *same* outer
transformation. This shared owner is precisely what supplies a naturality
comparison between the two boundary routes.

Every displayed object and arrow in (28.12) is therefore an observation of
coevaluation and the existing walking generator. None is postulated as a
standalone tensor constructor. The four vertex normal forms remain pairwise
distinct, and the selected square does not convert to $I\times I$.

The two routes around the boundary are

$$
a_1\circ b_0
\qquad\text{and}\qquad
b_1\circ a_0.
\tag{28.13}
$$

In a Cartesian product these would be forced to commute by the relevant
strict interchange. Here their difference is the feature being measured.

## 28.5 The Oriented Interchanger

Let $\epsilon$ be the whole outer transformation generated by coevaluation,
and let $g$ be the inner walking arrow. The post/left laxity action from
Section 28.1 has readable direction

$$
G(g)\circ\epsilon[-]
\Longrightarrow
\epsilon[g\circ -].
\tag{28.14}
$$

Evaluate this whole transformation at the identity of the outer source
endpoint. Its component is the square's interchanger:

$$
\chi:
a_1\circ b_0
\Longrightarrow
b_1\circ a_0.
\tag{28.15}
$$

The formal source and target are owned by the stable transport functors of the
internal action; (28.13) gives their readable composite presentations under
the current strict endpoint conversions. The direction (28.15), rather than
the choice of a terminology convention in isolation, is why the internal hom
is named $\mathsf{GrayHom}_{\mathrm{lax}}$.

The cell $\chi$ is not an independently declared filler. The whole
post/left transformation exists first; $\chi$ is its identity component. Nor
does the component end the construction. The transformation's next hom action
is retained as a functor, and evaluating that next owner at its identity
recovers $\chi$. This confirms that the square has not capped the common
action calculus one dimension too early.

The retained action can accept a higher arrow of the input hom and return a
higher cell between interchanger boundaries. In a larger cubical consumer it
would be the route by which faces of a three-dimensional comparison are
observed. This chapter checks only the owner and its identity observation; it
does not claim that a walking cube, all of its faces, or a general cubical
coherence theorem has been constructed.

Finally, the interchanger is not collapsed to an identity term. Its
post/left provenance also remains distinct from the pre/right mirror. If the
same cell were realized in a path-valued target, symmetry would provide an
inverse as in Chapter 25. Inside the directed square, no such inversion is
assumed.

<!-- evidence:GRAY-WALKING-INTERCHANGER -->

> **Formal status — checked.** **Theorem 28.1 (the walking-square
> interchanger).** Evidence `GRAY-WALKING-INTERCHANGER`. The four vertices and
> two coordinate arrow families are derived from right coevaluation. The
> oriented nonidentity interchanger is the identity component of the existing
> whole post/left laxity transformation, remains distinct from its pre/right
> mirror, and retains one next hom action. No square filler, endpoint rewrite,
> or unification rule is added independently.

## 28.6 What This Does And Does Not Call Gray

The low-dimensional picture agrees with the characteristic reason for using a
Gray rather than Cartesian tensor: currying a strict map produces strict
inner functors while allowing transformation-level laxity, and $I\otimes_R I$
exposes a directed interchanger instead of forcing a commuting square. This is
enough to test the architecture of profiles, closure, and extracted laxity.

Terminology in the literature can exchange *lax* and *oplax* when tensor
variance or diagrammatic composition conventions are reversed. The invariant
statement here is the displayed direction (28.14): postcomposition by the
target action points toward the action on the composite. That typed direction,
not the name alone, is the comparison surface for any later mirror closure or
literature equivalence.

It is not enough to assert a full Crans–Gray monoidal structure. Such a claim
would require at least:

- the mirror closure and a settled comparison between the two orientations;
- functorial action of the tensor in both parameters;
- associativity and unit data, with their higher coherences;
- compatibility of curry, uncurry, evaluation, and coevaluation with those
  actions; and
- a comparison with an established combinatorial or globular construction in
  the dimensions being claimed.

None of these is manufactured by adding fields to Theorem 28.1. They are new
whole constructions. The tensor in this chapter is consequently written
$\otimes_R$: it records the selected right closure rather than pretending
that the mirror and monoidal boundaries have already been built.

There is a second historical boundary. Some ambient functoriality and
naturality endpoints are still identified by global prototype conversion
rules. The strict code correctly selects where the compositor cell itself
computes to identity, and the unprofiled interchanger remains nonidentity, but
the eventual migration must re-home endpoint conversions at explicit strict
profiles. This chapter does not perform that repository-wide normal-form
change.

## 28.7 The End Of The Fourth Spiral

The fourth spiral began by placing equality inside the directed language.
Product paths showed groupoidal closure without a category-head rewrite. The
Circle turned reversible motion into the Integer line. Groupoidification then
freely realized arbitrary directed cells as paths. The Gray square now returns
to a target where the comparison cell is directed and worth keeping.

These movements are not separate foundations. They are different readings of
one iterable calculus:

$$
\begin{array}{c|c}
\text{target or profile}&\text{behaviour of the comparison cell}\\ \hline
\text{arbitrary directed target}&\text{lax, possibly noninvertible}\\
\text{path-valued target}&\text{pseudo, invertible by symmetry}\\
\text{decoded strict profile}&\text{computes to identity}.
\end{array}
\tag{28.16}
$$

This table also explains why the historical strict endpoint conversions do
not invalidate the experiment. They may simplify the written source and
target of a comparison, but they do not turn the unprofiled cell into the
identity. The path target, strict decoder, and arbitrary directed target still
select observably different behaviours of the retained witness.

The three rows of (28.16) should be read as operations on one owner, not as
three parallel theories. The arbitrary directed cell is primary. A
path-valued target changes its hom into equality and thereby supplies an
inverse. A strict decoder matches a computationally distinguished head and
thereby selects the identity reduction. Neither specialization requires the
ambient compositor, its whole transformation, or its next action to be
redeclared.

This suggests a discipline for extending the higher theory. First locate the
whole internal action before introducing a pointwise coherence name. Second
select the target or code profile that gives the desired invertibility or
strictness. Third derive the geometric consumer—such as the walking square—
from evaluation, coevaluation, and existing generators. Finally check both a
non-collapse boundary and one further hom action. A pointwise cell without its
owner is too easy to postulate; an owner without a concrete consumer is too
easy to misorient.

The mirror Gray closure can follow the same discipline. Its construction
should begin from the pre/right whole action, not by reversing the arrow in
(28.15) after the fact. Comparing the two closures will then be a theorem
about their whole curry and evaluation structures. Likewise, a future
associator for the tensor should be derived at the mapping-category level
before its components are named. This keeps higher coherence attached to the
operations that generate it.

The walking square is therefore valuable even though it is small. It tests
all of the architectural seams at once: strict codes versus ambient functors,
profiled homs versus duplicated hierarchies, closure versus an opaque tensor,
whole transformations versus square axioms, and directed cells versus paths.
Passing that test does not finish Gray theory, but it gives the unfinished
theory a computational spine.

The result is deliberately asymmetric. Groupoidal realization explains how
directed coherence may become invertible; the Gray direction explains why it
should not have been erased beforehand. [Chapter 29](#chapter-29) now uses the
same retained action recursively: a dependent arrow between dependent arrows
becomes a simplex with another dimension. The appendices then give the ledger
of exact notation, evidence, provenance, computation, and remaining research
boundaries for all five spirals.
