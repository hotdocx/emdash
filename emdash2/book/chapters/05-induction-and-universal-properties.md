<a id="chapter-5"></a>

# 5. Induction, Arrow Induction, And Universal Properties

Induction is often introduced as a collection of unrelated proof rules: one
for natural numbers, another for equality, and still others for higher
inductive types. A more durable view is that an inductively presented object
comes with a way to extend compatible data from its generators. Recursion
extends nondependent data; induction extends data in a family; contextual
elimination lets both the source and target vary. The increasing amount of
context is not bureaucratic overhead. It is what records naturality.

In a functorial setting, this extension principle should itself preserve
arrows and higher cells. That demand turns a familiar logical rule into a
categorical construction. This chapter begins with ordinary induction, then
develops the outgoing-arrow category and the arrow-induction interface used
throughout emdash. The result is a bridge between equality induction and the
contextual eliminator of the walking endomorphism.

## 5.1 Data On Generators

For the natural numbers, dependent induction has the familiar shape. Given a
family `P(n)`, a base element

$$
z:P(0),
$$

and a step operation

$$
s_n:P(n)\longrightarrow P(n+1),
$$

there is a section

$$
\mathsf{ind}_{\mathbb N}(z,s):\prod_{n:\mathbb N}P(n)
$$

whose observations at zero and successor compute to the supplied data. If
`P` is constant, the same interface is recursion. Thus recursion is not a
second principle: it is dependent elimination with no meaningful dependency.

The same pattern appears for a category presented by an object and an
endomorphism. To map it into a category `C`, one supplies an object of
`C` and an endomorphism of that object. To define a dependent section,
one supplies an object in the fibre over the generating object and a lift over
the generating arrow. To compare two varying families, one supplies a functor
between their base fibres and a coherent cell over the generator. Chapters 6
and 8 will instantiate precisely these three levels.

This perspective separates two questions:

1. what data an eliminator accepts; and
2. how its observations compute at the constructors.

Both matter. Existence without computation cannot drive a normalization
proof; computation without a coherent extension does not define an action on
the whole object.

## 5.2 Equality Induction As The Local Case

For a type `A`, right-based equality induction says that, with the right
endpoint `y` fixed, a family

$$
C(x,p)\qquad(x:A,\;p:x=y)
$$

is determined by its value at `(y,refl_y)`. In one conventional
orientation,

$$
\frac{d:C(y,\mathsf{refl}_y)}
     {\mathsf J(d,x,p):C(x,p)}.
$$

The reflexive observation computes to `d`. Ordinary action on paths and
dependent action on paths are specializations of this principle. They explain
why a function respects equality and how a section over a family produces a
dependent path.

<!-- evidence:TT-EQUALITY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-EQUALITY-INDUCTION`. The
> equality-local layer provides reflexivity, right-based dependent induction,
> ordinary path action, and dependent path action.

Equality induction is already functorial when it is read inside the path
category `Path(A)`: objects are elements of `A`, arrows are
equalities, and every arrow is invertible. But this is a special, groupoidal
base. A directed category contains arrows that need not have inverses, so we
want an induction interface whose statement does not presuppose that a given
arrow is an equality.

## 5.3 The Category Of Outgoing Arrows

Fix a category `Z` and an object `x`. The category of arrows leaving
`x` is the total category of the represented family

$$
\mathsf{PathOut}_Z(x)
  :=\sum_{y:\,Z}\operatorname{Hom}_Z(x,y).
$$

Its objects are pairs `(y,p)` with $p:x\to y$. It has a
distinguished reflexive object

$$
\mathsf{reflout}_x:=(x,\mathrm{id}_x).
$$

For every outgoing arrow $p:x\to y$, functorial action of the
representable family supplies a canonical total arrow

$$
\rho_{x,y,p}:
(x,\mathrm{id}_x)\longrightarrow(y,p)
\quad\text{in }\mathsf{PathOut}_Z(x).
$$

Its base component is `p`; its fibre endpoint reduces by the unit law
$p\circ\mathrm{id}_x=p$. The direction of `rho` is significant. It
starts at the reflexive arrow and reaches `p`. Nothing in the
construction produces a reverse arrow, and no invertibility premise is used.

<!-- evidence:IND-PATHOUT -->

> **Formal status — checked.** Evidence `IND-PATHOUT`.
> `PathOut_cat` is the Sigma total of the fixed-source
> representable, `pathout_refl_obj` is its distinguished object, and
> `pathout_refl_arrow` is the canonical Sigma transport arrow
> `rho`.

The name “PathOut” emphasizes an analogy, not an identification. When
`Z=Path(A)`, its objects really are equality paths out of `x`.
For a general `Z`, they are directed arrows. The same categorical shape
therefore hosts both ordinary path induction and a genuinely directed
extension principle.

The source object also varies contravariantly. An arrow $r:x\to y$
induces a functor

$$
\mathsf{PathOut}_Z(y)\longrightarrow\mathsf{PathOut}_Z(x),
\qquad
(z,q)\longmapsto(z,q\circ r).
$$

Precomposition changes which object the arrows leave, while postcomposition
changes where they arrive. Keeping these variances separate will prevent a
common mistake in Chapter 8: the based representable there varies
covariantly in its endpoint, not contravariantly in its source.

## 5.4 Fixed-Source Arrow Induction

Let

$$
E:\mathsf{PathOut}_Z(x)\longrightarrow\mathsf{Cat}
$$

be a directed family. An element

$$
u\in E[\mathsf{reflout}_x]
$$

can be transported along every canonical arrow `rho`. This produces a
section

$$
\mathsf{path\_ind}(x,E,u):
\prod_{q:\,\mathsf{PathOut}_Z(x)}E[q],
$$

whose readable value is

$$
\mathsf{path\_ind}(x,E,u)(y,p)
  = E[\rho_{x,y,p}](u).
$$

This formula is arrow induction: data at the identity arrow extends along
every outgoing arrow. Because `E` is Cat-valued, the result is a section
with coherent action, rather than merely a function that chooses one object
in each fibre.

<!-- evidence:IND-ARROW -->

> **Formal status — checked.** Evidence `IND-ARROW`. The fixed-source
> section is `path_ind_sec`; `PathInd_func` packages its action in the
> motive and base datum, and `PathInd_transfd` internalizes the theorem
> while the source object varies.

There are three layers here, and it helps not to conflate them:

- `path_ind_sec` is the readable theorem at a fixed source;
- `PathInd_func` says that this theorem acts functorially on motives and
  their data;
- `PathInd_transfd` records coherence as the source object moves.

The third layer uses the contravariant source action of `PathOut` and
the corresponding pullback of motives. Its naturality is internal to the
displayed transformation. One need not append an external family of
hand-written commuting squares.

## 5.5 Composition As A Diagnostic

An abstract eliminator earns its keep by recovering an operation we already
understand. Fix `x` and give `(y,p)` the represented motive

$$
E(y,p):=
\bigl(\operatorname{Rep}_Z(y)\longrightarrow
      \operatorname{Rep}_Z(x)\bigr).
$$

At the reflexive arrow, the identity transformation supplies the base datum.
Arrow induction then extends it to every $p:x\to y$. Evaluating the
result at $q:y\to z$ gives

$$
q\circ p:x\longrightarrow z.
$$

Thus ordinary categorical composition appears as transport from the identity
case. The resulting operation is still packaged functorially, so its action on
higher cells remains available to later constructions.

<!-- evidence:IND-COMPOSITION -->

> **Formal status — checked.** Evidence `IND-COMPOSITION`.
> `CompMotive_catd` is the represented motive,
> `path_comp_sec` is the induced section, and
> `path_comp_func` exposes composition as the object action of a
> functor.

This benchmark is more informative than a proof that some carrier-level
function exists. It checks the direction of `rho`, the variance of the
representable, and the agreement of the generic Sigma and Pi constructions.
If any of those are reversed, the result has the wrong endpoints before one
even asks for associativity.

## 5.6 Returning To Literal Equality

Set `Z=Path(A)` and let `D` be a directed family over that path
category. There are now two ways to move `u` along an equality
`p:x=y`:

1. use the functorial action of `D` on the arrow `p`; or
2. use primitive equality induction with a function-valued motive.

They need not be definitionally the same expression. The active calculus
proves that they are propositionally equal:

$$
\mathsf{transport}^{\mathrm{structured}}_D(p,u)
=
\mathsf{transport}^{\mathsf J}_D(p,u).
$$

<!-- evidence:IND-PATH-COMPARISON -->

> **Formal status — checked.** Evidence `IND-PATH-COMPARISON`.
> `path_cat_structured_transport_agrees_ind_eqr` compares the existing
> directed-family action with primitive right-based equality induction. It
> does not introduce a second equality eliminator or turn the comparison into
> a global rewrite.

This is the precise relation between the equality-local and directed views.
Functorial transport extends beyond equality paths; on a literal path
category, it agrees with `J` by a theorem. The groupoidal case is
therefore recovered without making all directed arrows groupoidal.

## 5.7 Contextual Elimination

Fixed-source arrow induction varies a motive over outgoing arrows. A
contextual eliminator goes one step further: it compares two families over an
inductively presented base. Schematically, suppose
$R,D:K\to\mathsf{Cat}$.
At each base object it should provide a functor

$$
T_k:R[k]\longrightarrow D[k],
$$

and for each base arrow $f:k\to k'$ a directed comparison

$$
D[f]\circ T_k
\Longrightarrow
T_{k'}\circ R[f].
$$

This is exactly the data of a displayed functor in the lax direction selected
by the calculus. If `R` is terminal, a displayed functor becomes a
section of `D`. If both `R` and `D` are constant, it becomes an
ordinary functor out of `K`. Section induction and recursion are therefore
special cases of contextual elimination.

For an inductively presented `K`, the desired eliminator should build the
whole displayed functor from compatible data at the constructors. The
WalkingEnd interface of Chapter 6 realizes this pattern for one point and one
directed loop. Chapter 8 then uses the genuinely contextual form: its source
is the code family and its target is a representable family, so neither side
can be discarded as mere bookkeeping.

## 5.8 Universal Properties: What Is And Is Not Packaged

Induction principles often admit a universal-property formulation. For an
ordinary inductive type, one expects the canonical algebra to be initial, or
homotopy-initial when maps carry higher equality. For a directed higher
inductive category, one similarly expects a category of algebras, structured
functors, and coherent transfors in which the presented object is suitably
initial.

That formulation is mathematically attractive because it gathers recursion,
induction, uniqueness, and higher coherence into one statement. It is also
more demanding than writing a selected eliminator. One must define the
algebra category at every relevant cell dimension, identify its notion of
equivalence, and prove contractibility or an equivalent universal mapping
property.

<!-- evidence:IND-GENERAL-INITIALITY -->

> **Formal status — research boundary.** Evidence
> `IND-GENERAL-INITIALITY`. The current calculus packages Nat and equality
> induction, generic `PathOut` arrow induction, and the selected
> WalkingEnd eliminator. It does not yet prove a general equivalence between
> such interfaces and homotopy-initial categorical algebras.

We will therefore use “walking” in its presentation-theoretic sense and use
the eliminator that is actually checked. Full functor-category initiality is
a strengthening target, not an implicit premise of the computation.

## 5.9 The Interface Needed For Encode–Decode

The next two chapters isolate the additional ingredients required by the
walking-endomorphism calculation:

- Chapter 6 supplies a contextual eliminator whose generator datum is a
  coherent directed transformation;
- Chapter 7 supplies one-dimensionality, allowing a directed 2-cell between
  parallel based arrows to be read as equality.

The roles are deliberately ordered. Elimination constructs directed data.
Truncation may later show that some of that data is unique or equality-like.
Reversing the order would erase the very directionality the example is meant
to expose.
