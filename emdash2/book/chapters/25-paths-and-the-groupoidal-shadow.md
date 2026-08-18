<a id="chapter-25"></a>

# 25. Paths And The Groupoidal Shadow

A directed arrow remembers which way it points. An equality path may also be
followed, but it can be reversed. Functorial type theory keeps these two forms
of motion in one language without identifying them. This is important both
mathematically and computationally. Directed categories are needed for maps
that need not be invertible: inclusions, restriction maps, substitutions, and
the morphisms of algebra and geometry. Paths are needed for identity,
transport, and homotopy. If every arrow were silently turned into a path, the
directed theory would disappear. If paths could not enter the categorical
calculus, the homotopical theory would become a detached second foundation.

The bridge is the path category. For a groupoidal classifier $A$, the category
$\operatorname{Path}(A)$ has elements of $A$ as objects and equality evidence
as arrows:

$$
\operatorname{Obj}(\operatorname{Path}(A))=A,
\qquad
\operatorname{Hom}_{\operatorname{Path}(A)}(x,y)=(x=y).
\tag{25.1}
$$

Reflexivity is the identity arrow. Categorical composition has the same
mathematical effect as path concatenation, with a proved comparison between
the two presentations. Every arrow in $\operatorname{Path}(A)$ is invertible
because every path has a reverse. Thus equality can be observed through the
same object, hom, functor, transformation, and higher-action interfaces used
by the directed theory.

This chapter develops three consequences of that bridge. First, paths in a
product split into their two coordinate paths and can be reconstructed from
them. Second, dependent transport over a product can be performed directly or
one coordinate at a time, and the resulting routes form a coherent diamond.
Third, a generic directed laxity cell becomes invertible when it is realized
in a path category. The point is not to add parallel copies of products,
transport, or functoriality for the groupoidal world. It is to show how one
iterable categorical calculus changes character when its homs are paths.

## 25.1 Equality In Categorical Form

Let $f:A\to B$ be an ordinary function between groupoidal classifiers. Its
action on equality is familiar:

$$
p:x=y
\quad\longmapsto\quad
\operatorname{ap}_f(p):f(x)=f(y).
\tag{25.2}
$$

In the categorical presentation, (25.2) is the arrow action of a whole
functor

$$
\operatorname{Path}(f):\operatorname{Path}(A)
  \longrightarrow \operatorname{Path}(B).
\tag{25.3}
$$

The adjective *whole* matters. Equation (25.3) is not merely a function on
objects together with a separately stated congruence lemma. It is the first
action of an internal path-category construction. Equality between functions
therefore has a next action, equality between those equalities has another,
and the same mechanism remains available at every represented hom level.
Functoriality is not reconstructed from a finite record each time the
dimension rises.

This is the **groupoidal shadow** of ordinary function action. It should not
be confused with the groupoidification of a directed category. The path
category begins with a type-like classifier and exposes its existing
equalities as arrows. Groupoidification, studied in Chapter 27, begins with
directed arrows and freely realizes them as paths. The first construction
reveals identity already present; the second imposes invertibility on motion
that was not initially invertible.

The path category also gives a common surface for equality induction and
categorical induction. Fix $x:A$. The objects of the outgoing-path category
are pairs $(y,p)$ with $p:x=y$. Its distinguished object
$(x,\operatorname{refl}_x)$ is initial in the groupoidal sense: a family over
outgoing paths is determined by what it does there, and its value at $(y,p)$
is obtained by transport along $p$. In the directed presentation this is the
`PathOut` principle of Chapter 5. In the equality presentation it is the
usual eliminator $J$. They are two views of one operation, not competing
eliminators.

The computational boundary is precise. Primitive right-based $J$ computes at
reflexivity. Structured categorical transport and structured `PathOut`
induction are transparent presentations of the same movement, and there are
paths comparing each with primitive $J$. Those comparisons are mathematical
equalities; the book does not promote all three surface expressions to one
runtime normal form. This separation lets conversion remain controlled while
still proving that the categorical and groupoidal readings agree.

## 25.2 A Product Path Has Two Coordinates

Consider two groupoidal classifiers $A$ and $B$. There are two evident ways
to form a category of paths of pairs:

$$
\operatorname{Path}(A\times B)
\qquad\text{and}\qquad
\operatorname{Path}(A)\times\operatorname{Path}(B).
\tag{25.4}
$$

Their objects are the same pairs. Their category heads, however, are not
declared definitionally equal. The comparison is instead carried by a
canonical functor

$$
\chi_{A,B}:\operatorname{Path}(A\times B)
\longrightarrow
\operatorname{Path}(A)\times\operatorname{Path}(B),
\tag{25.5}
$$

which is judgmentally the identity on objects. For
$s=(a_0,b_0)$ and $t=(a_1,b_1)$, its action on homs reads

$$
(s=t)
\longrightarrow
(a_0=a_1)\times(b_0=b_1).
\tag{25.6}
$$

The forward map *splits* a path of pairs by projecting it to the two
coordinates. Conversely, a pair

$$
p:a_0=a_1,
\qquad
q:b_0=b_1
\tag{25.7}
$$

can be *joined* to a path

$$
\langle p,q\rangle:(a_0,b_0)=(a_1,b_1).
\tag{25.8}
$$

The construction of (25.8) uses the stable path view of a dependent pair. A
path in a sigma type consists of a base path together with a path over it in
the fibre. For an ordinary product the fibre is constant, so the second
component of (25.7) is converted into the required path-over and the two
pieces are assembled. Splitting after joining and joining after splitting are
both propositionally the identity. Hence, for every pair of endpoints, (25.6)
is a type equivalence:

$$
\bigl((a_0,b_0)=(a_1,b_1)\bigr)
\simeq
\bigl((a_0=a_1)\times(b_0=b_1)\bigr).
\tag{25.9}
$$

<!-- evidence:GROUPOIDAL-PRODUCT-CLOSURE -->

> **Formal status — checked.** **Theorem 25.1 (product-path closure).** Evidence
> `GROUPOIDAL-PRODUCT-CLOSURE`. The canonical comparison (25.5) is
> judgmentally identity on objects, and its actual action on every hom has an
> explicit split/join equivalence. The theorem does not add a category-head
> rewrite between the two categories in (25.4), nor does it postulate a whole
> inverse functor or a complete equivalence of categories.

The restraint in the final sentence is useful. The mathematical content
needed by later transport arguments is already present: a product path may be
read componentwise and component paths may be assembled. Turning that fact
into a new definitional equality of large category expressions would choose a
global normal form and create interactions with every consumer of products
and paths. Homwise equivalence records the invariant without forcing such a
choice.

This example illustrates what **groupoidal closure** means in the present
development. It is not the assertion that every categorical former preserves
path structure. It is a checked comparison for a selected former—in this
case, products—showing how the path realization is recovered from the
component realizations. Other formers require their own comparison or a later
general closure theorem.

## 25.3 Three Routes Through Dependent Transport

The split/join theorem becomes more informative when the codomain depends on
the pair. Let

$$
P:A\times B\longrightarrow\mathcal U
\tag{25.10}
$$

be a groupoidal family, let $p:a_0=a_1$ and $q:b_0=b_1$, and take
$u:P(a_0,b_0)$. Joining $p$ and $q$ gives the simultaneous path (25.8), so
primitive equality transport gives a direct route

$$
T_{\mathrm{dir}}(p,q,u)
:
P(a_1,b_1).
\tag{25.11}
$$

There are also two broken-line routes through the square of indices. The
base-first route moves from $(a_0,b_0)$ to $(a_1,b_0)$ along $p$, then from
$(a_1,b_0)$ to $(a_1,b_1)$ along $q$. The fibre-first route changes the
$B$-coordinate before the $A$-coordinate:

$$
\begin{aligned}
T_{A;B}(p,q,u)&:
P(a_0,b_0)\longrightarrow P(a_1,b_0)
                 \longrightarrow P(a_1,b_1),\\
T_{B;A}(p,q,u)&:
P(a_0,b_0)\longrightarrow P(a_0,b_1)
                 \longrightarrow P(a_1,b_1).
\end{aligned}
\tag{25.12}
$$

All three expressions have the same endpoint, but they are not selected as
one judgmental normal form. Equality induction on $p$ and $q$ instead proves
two comparisons

$$
T_{\mathrm{dir}}(p,q,u)=T_{A;B}(p,q,u),
\qquad
T_{\mathrm{dir}}(p,q,u)=T_{B;A}(p,q,u).
\tag{25.13}
$$

At reflexivity, direct transport and both sequential routes reduce to the
original $u$. The general comparisons are then generated by the same $J$
principle. Reversing the first path in (25.13) and following the second gives
the coherence edge between the broken-line routes:

$$
T_{A;B}(p,q,u)=T_{B;A}(p,q,u).
\tag{25.14}
$$

Equations (25.11)–(25.14) form the transport diamond

$$
\begin{array}{ccc}
&T_{\mathrm{dir}}(p,q,u)&\\[-2mm]
\swarrow&&\searrow\\[-1mm]
T_{A;B}(p,q,u)&&T_{B;A}(p,q,u),
\end{array}
\tag{25.15}
$$

where the lower edge is induced by the two displayed comparisons. The
diamond answers the ordering question raised by product transport. There is
no need to declare that transport *is* first-$A$-then-$B$, nor that it *is*
first-$B$-then-$A$. Direct transport is the neutral centre. Both sequential
calculations are valid, and their agreement is retained as data that can
itself be transported or acted upon at a higher level.

Nothing Gray-like is required for this theorem. Gray interchange concerns
directed two-dimensional composition when comparison cells need not be
invertible. Here the base arrows are equality paths and the two routes are
compared by equality induction. Chapter 28 will return to the directed
interchanger after the groupoidal examples have made this distinction
visible.

<!-- evidence:GROUPOIDAL-PRODUCT-TRANSPORT -->

> **Formal status — checked.** **Theorem 25.2 (the product-transport
> diamond).** Evidence
> `GROUPOIDAL-PRODUCT-TRANSPORT`. Transport along the joined product path
> agrees with both coordinate orders, and the comparisons compose to the
> coherent lower edge (25.14). The construction uses primitive right-based
> equality induction; it introduces no product-specific transport axiom and
> no second eliminator.

## 25.4 One Transport, Three Presentations

The family $P$ in (25.10) can also be presented categorically. Apply the path
category to every fibre and use path action to obtain a displayed category
over $\operatorname{Path}(A\times B)$. A path $r:s=t$ in the base then acts
on a fibre object $u:P(s)$ by displayed functorial transport. In symbols, the
three readings are

$$
\begin{aligned}
T_J(r,u)&=\text{primitive equality transport},\\
T_{\mathrm{disp}}(r,u)&=\text{displayed categorical action},\\
T_{\mathrm{out}}(r,u)&=\text{structured induction over outgoing paths}.
\end{aligned}
\tag{25.16}
$$

The second line sees $r$ as an arrow of the path category. The third sees
$(t,r)$ as an object of the outgoing-path category based at $s$. These
descriptions organize transport differently, but both compare to the first:

$$
T_{\mathrm{disp}}(r,u)=T_J(r,u),
\qquad
T_{\mathrm{out}}(r,u)=T_J(r,u).
\tag{25.17}
$$

Thus the displayed and `PathOut` interfaces are not alternative axioms for
transport. They are categorical structures whose computation is justified
by the primitive equality eliminator. Conversely, (25.17) shows that $J$ is
not stranded in a purely syntactic equality layer. It can be used through the
same displayed-action and section interfaces that support directed dependent
type theory.

There is a deliberate difference between *computes* and *agrees*. Primitive
$J$ computes judgmentally on reflexivity. The two structured expressions in
(25.16) agree propositionally with it, including at the reflexive case; they
are not installed as additional runtime reductions. This is enough to move
between representations in a proof while avoiding three rival normal forms
for the same operation.

The result is a useful design test. A computational homotopy layer need not
duplicate a primitive eliminator for every categorical presentation of a
family. It can keep one $J$, expose structure through functorial interfaces,
and prove that the interfaces return to the same transport. The product
diamond then becomes a substantive consumer of the arrangement rather than a
second definition of it.

## 25.5 When Directed Laxity Becomes Pseudo

We can now return to the whole path action (25.3). In the directed calculus, a
functor carries a compositor comparing two ways of acting on composable
arrows. For $p:x=y$ and $q:y=z$, specialize that generic compositor to
$\operatorname{Path}(f)$. Its source and target have the familiar readings

$$
\operatorname{ap}_f(p)\mathbin{\cdot}\operatorname{ap}_f(q)
\qquad\text{and}\qquad
\operatorname{ap}_f(p\mathbin{\cdot}q),
\tag{25.18}
$$

where $\cdot$ denotes path concatenation in diagrammatic order. Formally, the
kernel retains represented postcomposition expressions as the compositor's
runtime endpoints. Separate paths compare those endpoints with the readable
$\operatorname{ap}$/concatenation expressions in (25.18). The presentation is
therefore recognizable without selecting the notation of (25.18) as a second
normal form.

For an arbitrary directed codomain, the compositor is a directed cell and
need not have an inverse. Here its codomain is

$$
\operatorname{Hom}_{\operatorname{Path}(B)}(f(x),f(z))
=(f(x)=f(z)).
\tag{25.19}
$$

A cell between the two arrows in (25.18) is consequently an equality between
paths. Path symmetry supplies its inverse. No inverse field is postulated and
no second pseudofunctor hierarchy is introduced. The generic lax witness has
become a pseudo witness because it landed in a groupoidal hom.

This gives a simple three-way interpretation of the same internal action:

$$
\begin{array}{rcl}
\text{directed target}&:&\text{the compositor may be noninvertible},\\
\text{path target}&:&\text{the compositor is invertible by symmetry},\\
\text{selected strict profile}&:&\text{the compositor specializes to identity}.
\end{array}
\tag{25.20}
$$

Strictness and pseudo-functoriality are therefore not obtained by erasing the
generic witness. They are two special behaviours of it. This is especially
important when a strict specialization is also available. The witness cell
remains visible before that specialization, while an explicit strict profile
can state exactly where identity behaviour is intended. Chapter 28 will use
that distinction when comparing Cartesian and Gray-style closure.

The compositor is retained before it is capped at the particular path $p$.
At that whole level it is a transformation, functorial in the first path.
Taking its next hom action yields a functor from paths between paths to paths
between the corresponding compositor endpoints. Thus the construction has
not discarded higher input merely to prove pointwise invertibility. It
preserves one explicit next stage of the same internal action, and the generic
action can be iterated further.

<!-- evidence:PATH-PSEUDO-LAXITY -->

> **Formal status — checked.** **Theorem 25.3 (path-realized
> pseudo-laxity).** Evidence
> `PATH-PSEUDO-LAXITY`. The generic compositor of
> $\operatorname{Path}(f)$ decodes to an equality between paths; symmetry
> gives its inverse; its formal endpoints compare propositionally with the
> two expressions in (25.18); and its whole form retains one next hom action.
> No new rewrite or unification rule, pseudofunctor classifier, inverse
> record, or complete weak $\omega$-groupoid theorem is claimed.

Theorem 25.3 is small but conceptually decisive. It shows that the directed
and groupoidal layers do not need unrelated accounts of coherence. A witness
generated by the directed internal-action machinery can be read as a path
when the target says that its arrows are equalities. Invertibility then comes
from the target's geometry. The change from lax to pseudo is semantic in the
best computational sense: it is witnessed by the actual type of the cell.

## 25.6 Closure, Truncation, And Free Inversion

Three nearby operations can now be separated cleanly.

**Groupoidal closure** starts with groupoidal data and asks whether a former
preserves it. Theorem 25.1 answers this for the selected product comparison,
hom by hom. **Truncation** starts with a groupoidal classifier and reflects it
to a prescribed homotopy level. The active tower and its eliminators were
introduced in Chapter 7; Chapter 26 will use the $0$-truncated Integer line
when calculating the loop space of the Circle. **Groupoidification** starts
with a directed category and freely makes its arrows invertible, together
with the coherence required by composition. That is neither path exposure
nor truncation, and it will occupy Chapter 27.

The boundaries of this chapter are just as important as its theorems. The
product comparison is identity on objects and an equivalence on each hom, but
is not promoted to a whole category equivalence. The transport comparisons
are propositional rather than competing conversion rules. The path-valued
compositor retains higher action, but does not by itself establish a complete
weak $\omega$-groupoid semantics or a global normalization theorem. These are
not missing qualifications attached after the mathematics; they locate the
exact reusable interface that has been checked.

These distinctions suggest a useful discipline for working between the two
layers. When equality-local data should participate in directed machinery,
place it in a path category and preserve the whole categorical action for as
long as possible. Do not cap immediately at objects or arrows if a later
argument may need the next hom action. When a former such as a product has
both a groupoidal and a categorical presentation, compare the actual object
and hom actions before considering a new equality of classifier heads. And
when a directed comparison lands in a path-valued hom, obtain invertibility
from path reversal rather than copying the comparison into an unrelated
pseudo structure.

The common theme is that coherence should be **observed where it lives**.
Product paths live homwise, so their split/join theorem is homwise. Dependent
transport lives in a fibre, so its order comparison is an equality in that
fibre. The functor compositor lives one dimension above arrows, so its
path-valued realization is an equality between paths and retains a next
action. None of these facts is improved by flattening it prematurely into an
external collection of equations. Keeping the owner whole makes both the
computation and its possible iteration visible.

This is also why the word *shadow* does not mean approximation. The path
category forgets none of the equality evidence it exposes. Rather, it changes
the angle from which that evidence is viewed: a path becomes an arrow, a
path-over becomes displayed action, and higher equality becomes higher
categorical action. What remains outside the shadow is genuinely directed
information—arrows that were never equalities in the first place. Free
inversion will act on precisely that remainder.

The next chapter gives that interface its first geometric test. The Circle is
generated by one point and one reversible loop. Mapping it into a type $X$
should therefore amount to choosing a point of $X$ and a loop at that point.
When $X$ is the universe of sets and the loop acts by successor, repeated
transport records winding number. The result is the Integer line—not because
the Circle was declared to be arithmetic, but because groupoidal motion can
be followed forward and backward.
