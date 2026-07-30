<a id="chapter-2"></a>

# 2. Categories, Functors, And Directed Families

An ordinary type family varies with a term and transports along equality. A
directed family varies with an object and acts along arrows that need not be
equalities. This small change reorganizes the entire dependent calculus. The
action is no longer reconstructed only from path induction: it is presented
as a functor and is therefore available at every cell dimension.

The central example already suggests the shape. `Code` is not merely an
assignment of a category to the base object of `W`. It must send the
generator to the successor functor. The based representable is not merely the
collection of hom carriers. It must act on an arrow by postcomposition. The
decoder is not merely a family of functions. It must compare these two
actions coherently.

For classical category-theoretic background, see
[Mac Lane](#ref-mac-lane). For broader context on directed type theory, see
[GPT 5.6 Codex](#ref-gpt-codex). The present calculus makes its own
computational and formal choices.

<a id="chapter-2-1"></a>

## 2.1 Categories With Iterated Homs

For a category `A`, write

$$
\operatorname{Obj}(A)
$$

for its classifier of objects. For `x,y:Obj(A)`, emdash does not take
`Hom_A(x,y)` to be only a set or a type of arrows. It is another
category. Its objects are 1-arrows `f:x -> y`; its arrows are 2-cells
between such arrows; iterating `Hom` reveals 3-cells and beyond.

Schematically,

$$
\begin{aligned}
f &: x\longrightarrow y,\\
\alpha &: f\Longrightarrow g,\\
\Gamma &: \alpha\Rrightarrow\beta,\\
&\ \vdots
\end{aligned}
$$

are read by repeatedly taking the object classifier of a hom-category. This
is the strict/lax omega-oriented *shape* of the implementation. It should not
be mistaken for a completed semantics of every weak omega-category: the
available composition, action, and coherence interfaces are explicit and
grow as consumers require them.

Every object has an identity arrow, and composable arrows have a composite

$$
x\xrightarrow{f}y\xrightarrow{g}z
\qquad\leadsto\qquad
g\circ f:x\longrightarrow z.
$$

We always read `g o f` as first `f`, then `g`. Identity,
composition, and their higher actions are global operations of the category
calculus. Some laws are selected as runtime reductions; others are exposed as
typed propositional or proof-time comparisons. The mathematical reading is
the familiar category law, while the implementation distinguishes which
direction is a useful normal form.

<!-- evidence:CAT-ITERATED-HOMS -->

> **Formal status — checked.** Evidence `CAT-ITERATED-HOMS` covers the
> category, object, and iterated-hom interface. The phrase “omega-oriented”
> describes this unbounded hom iteration; it does not claim a finished theory
> of arbitrary weak coherence.

<a id="chapter-2-2"></a>

## 2.2 The Equality-Local Category

Every groupoid classifier `A` determines a path category

$$
\mathsf{Path}(A).
$$

Its objects are elements of `A`, and its hom from `x` to `y` is
the path category of the identity classifier `x=y`. Its identity is
reflexivity and its composition is path concatenation. Since paths have
symmetry, this is the groupoidal fragment of the categorical universe.

An ordinary function `f:A -> B` lifts to an iterable functor

$$
\mathsf{Path}(f):\mathsf{Path}(A)\longrightarrow\mathsf{Path}(B).
$$

On objects it is `f`; on a path it is `ap_f`; on higher paths it
continues by the generic functor calculus. This is a precise bridge between
the type-theoretic material of Chapter 1 and the directed material here.

It is important that the bridge is an inclusion of a special case, not a
collapse. A directed category `C` may contain an arrow `x -> y`
without any path `x=y`. Conversely, an object path can be mapped to an
arrow through the equality-local core inclusion. Later equivalence interfaces
state when that inclusion captures all arrows.

<!-- evidence:CAT-PATH-CATEGORY -->

> **Formal status — checked.** Evidence `CAT-PATH-CATEGORY` covers the
> recursive path category and the functor induced by an ordinary function.
> No rule identifies a general directed hom-category with an equality type.

<a id="chapter-2-3"></a>

## 2.3 Functors Act At Every Dimension

A functor `F:A -> B` has an object action

$$
x\longmapsto F[x]
$$

and, for every pair `x,y`, a hom functor

$$
F_1[x,y]:\operatorname{Hom}_A(x,y)\longrightarrow
\operatorname{Hom}_B(F[x],F[y]).
$$

Evaluating the hom functor at an arrow `f` gives the familiar
`F[f]`. Because the result before evaluation is itself a functor, the
same construction already acts on 2-cells between `f` and `g`, then
on higher cells. The notation suppresses this projection ladder, but the
structure does not stop at the first arrow.

Functoriality has the expected equations

$$
F[\mathrm{id}_x]=\mathrm{id}_{F[x]},
\qquad
F[g\circ f]=F[g]\circ F[f].
$$

In the active calculus these are owned globally. A named construction that is
already a functor does not receive a private copy of the identity and
composition laws. This is more than code reuse: it expresses the foundational
thesis that substitution-like operations should be internalized until their
action and coherence come from the generic functor structure.

<!-- evidence:CAT-FUNCTOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-FUNCTOR-CALCULUS` covers
> object action, full hom action, capped arrow action, and the generic identity
> and composition surfaces.

<a id="chapter-2-4"></a>

## 2.4 Transfors And Naturality

Given functors `F,G:A -> B`, the next hom-category is written

$$
\mathsf{Transf}(F,G).
$$

An object `eta:F => G` has a component at every object,

$$
\eta[x]:F[x]\longrightarrow G[x].
$$

Its action over an arrow `f:x -> y` expresses naturality. In a
1-categorical shadow, this is the familiar square comparing

$$
G[f]\circ\eta[x]
\qquad\text{and}\qquad
\eta[y]\circ F[f].
$$

In the iterated-hom presentation, naturality is not an external proposition
attached after the components are chosen. It is part of the higher action of
the transfor object. Further homs between transfors provide higher transfors
and their components.

Vertical composition is computed componentwise, and identity transfors have
identity components. Whiskering and functor action provide horizontal
interaction. Chapter 8.2 uses precisely this infrastructure when the two
compositions on 2-endomorphisms meet in the Eckmann–Hilton calculation.

<!-- evidence:CAT-TRANSFOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-TRANSFOR-CALCULUS` covers
> transfors, their point components, and the next naturality projection. The
> book uses “transfor” for the dimension-uniform notion and “transformation”
> when discussing its ordinary categorical shadow.

<a id="chapter-2-5"></a>

## 2.5 The Directed Universe And Its Families

The category of categories has

$$
\operatorname{Obj}(\mathsf{Cat})=\mathsf{Cat},
\qquad
\operatorname{Hom}_{\mathsf{Cat}}(A,B)=\mathsf{Functor}(A,B).
$$

Thus an arrow in the categorical universe is a functor. A Cat-valued directed
family over `K` is consequently a functor

$$
E:K\longrightarrow\mathsf{Cat}.
$$

We write its fibre over `k` as `E[k]`. A base arrow
`p:k -> l` induces the reindexing functor

$$
E[p]:E[k]\longrightarrow E[l].
$$

This is covariant directed transport. It can carry an object `u:E[k]`
forward to `E[p](u)` even when `p` has no inverse. Ordinary path
transport is recovered when `K` is a path category, but directed
transport is strictly more general.

A morphism between families `E,D:K -> Cat` is a displayed or
fibrewise functor

$$
\Phi:E\Longrightarrow D.
$$

It has a functor `Phi[k]:E[k] -> D[k]` in each fibre. Over a base
arrow `p:k -> l`, its coherent comparison has the directed form

$$
D[p](\Phi[k](u))
\longrightarrow
\Phi[l](E[p](u)).
$$

The arrow points from “map, then transport in `D`” toward “transport in
`E`, then map.” It need not be an identity and need not be invertible.
This is the first elementary appearance of laxity in the dependent calculus.
Strict/cartesian constructions may make the comparison compute to an
identity, but that is additional structure or focused computation, not the
default meaning of a family morphism.

<!-- evidence:CAT-DIRECTED-FAMILIES -->

> **Formal status — checked.** Evidence `CAT-DIRECTED-FAMILIES` covers
> Cat-valued families, fibres, arrow reindexing, fibre functors, and the
> canonical displayed comparison cell. A general directed family is not
> required to send its base arrows to equivalences.

<a id="chapter-2-6"></a>

## 2.6 Totals And Sections

A family can be read in two complementary ways. Its **total category** gathers
all fibre objects together:

$$
\sum_{k:K}E[k].
$$

An object is a pair `(k,u)` with `u:E[k]`. An arrow

$$
(k,u)\longrightarrow(l,v)
$$

contains a base arrow `p:k -> l` and a fibre arrow

$$
\alpha:E[p](u)\longrightarrow v
$$

in `E[l]`. The canonical transport arrow is the special case

$$
(p,\mathrm{id}_{E[p](u)}):
(k,u)\longrightarrow(l,E[p](u)).
$$

This description makes directed dependence concrete. Transport is an actual
arrow in the total category, and its direction is inherited from the base.

The **section category** is the dependent product

$$
\prod_{k:K}E[k].
$$

A section `s` assigns an object `s[k]:E[k]` and, for every base
arrow, a coherent comparison

$$
s[p]:E[p](s[k])\longrightarrow s[l].
$$

An arrow between sections is not an arbitrary pointwise family of fibre
arrows. Its components must be natural over the base. This distinction
disappears over a trivial base but is essential over a directed one.

For a constant family with fibre `A`, the total is the product category
`K x A`, while the section category is the functor category
`Functor(K,A)`. These are useful checks on the definitions: a section of
a constant family is precisely a functorial choice varying over `K`.

<!-- evidence:CAT-SIGMA-PI -->

> **Formal status — checked.** Evidence `CAT-SIGMA-PI` covers the Sigma
> total, its canonical transport arrow, the Pi section facade, and section
> evaluation. Some broader Sigma/Pi adjunctions and generic section-total
> packaging remain future work; they are not prerequisites for Chapter 8.

### 2.6.1 Fibrewise Contexts

Totals make genuine dependence visible, but not every pair of declarations
over a base depends on one another. Let
$B,C:K\vdash\mathsf{Cat}$ be two families over the same category. Their
fibrewise product is the transparent family

$$
P(B,C)[k]:=B[k]\times C[k],
\qquad
P(B,C)[p]:=B[p]\times C[p].
$$

The second formula uses the same base arrow $p$ in both components. It is the
action required by a context of independent siblings

$$
k:K,\qquad b:B[k],\qquad c:C[k].
$$

This differs from a genuinely dependent context

$$
k:K,\qquad a:A[k],\qquad b:B[k,a].
$$

In the first context, $b$ and $c$ may be projected, paired, exchanged, or
contracted while the common prefix $k$ is fixed. In the second, exchanging
$a$ and $b$ without transporting the classifier of $b$ is generally
ill-typed.

The fixed-base structural maps are

$$
\begin{aligned}
\mathsf{projL}_d(B,C)&:P(B,C)\Longrightarrow B,\\
\mathsf{projR}_d(B,C)&:P(B,C)\Longrightarrow C,\\
\mathsf{pair}_d(\Phi,\Psi)&:E\Longrightarrow P(B,C),
\end{aligned}
$$

where $\Phi:E\Longrightarrow B$ and $\Psi:E\Longrightarrow C$. They satisfy
the displayed product cuts

$$
\mathsf{projL}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Phi,
\qquad
\mathsf{projR}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Psi.
$$

Their fibre functors, base-arrow actions, and selected internalized higher
cells compute componentwise. Exchange and contraction are consequently
derived maps:

$$
\begin{aligned}
\mathsf{swap}_d(B,C)
  &:=\mathsf{pair}_d(\mathsf{projR}_d,\mathsf{projL}_d),\\
\mathsf{diag}_d(B)
  &:=\mathsf{pair}_d(\mathsf{id}_d,\mathsf{id}_d).
\end{aligned}
$$

The family $P(B,C)$ is built from ordinary categorical product functoriality;
it is not a new primitive family former. Reindexing a grouped context is
presented canonically by reindexing its two families and rebuilding their
fibrewise product.

<!-- evidence:CAT-FIBREWISE-CONTEXT -->

> **Formal status — checked.** Evidence `CAT-FIBREWISE-CONTEXT` covers the
> transparent fibrewise family, its displayed projections and pairing,
> componentwise object, arrow, and selected higher action, the two product
> cuts, and the derived swap and diagonal. It does not license exchange
> across a genuine dependency edge.

### 2.6.2 Base Change And Evaluation

A functor $F:A\vdash K$ can change the base of a family
$D:K\vdash\mathsf{Cat}$. The pulled-back family $F^*D$ has fibre
$(F^*D)[a]=D[F[a]]$. Its total category carries a canonical functor

$$
\mathsf{Tot}(F,D):
\sum_{a:A}(F^*D)[a]\longrightarrow\sum_{k:K}D[k]
$$

with computations

$$
(a,u)\longmapsto(F[a],u),
\qquad
(p,\alpha)\longmapsto(F[p],\alpha).
$$

The base component is acted on by $F$, while the fibre component is retained.
This is the asymmetric Grothendieck totalization of family reindexing. It is
not a claim that arbitrary functors between total categories admit a
computational pullback.

The same fibrewise structure supports coherent evaluation. Fix an ordinary
category $A$ and a family $B:K\vdash\mathsf{Cat}$, and write

$$
S(A,B)[k]:=\operatorname{Functor}(A,B[k]).
$$

Then

$$
\mathsf{Eval}_d(B):
P\bigl(S(A,B),\mathsf{Const}_K(A)\bigr)\Longrightarrow B
$$

projects in each fibre to ordinary functor evaluation:

$$
\mathsf{Eval}_d(B)[k]=\mathsf{Eval}(A,B[k]).
$$

Weakening is supplied by the displayed terminal map

$$
\mathsf{Terminal}_d(E):
E\Longrightarrow\mathsf{Const}_K(1).
$$

Composing it with a constant section yields a fixed argument. Pairing that
argument with a varying functor and applying $\mathsf{Eval}_d$ therefore
interprets application without asking the user to supply a separate
naturality square. Base-arrow and higher action are inherited from the
internal functorial calculus.

<!-- evidence:CAT-BASE-CHANGE-TOTALIZATION -->
<!-- evidence:CAT-DISPLAYED-EVALUATION -->

> **Formal status — checked.** Evidence
> `CAT-BASE-CHANGE-TOTALIZATION` covers the object and arrow action of
> asymmetric pullback totalization. Evidence `CAT-DISPLAYED-EVALUATION`
> covers constant-domain displayed evaluation, terminal weakening, and their
> retained generic base and higher action. Arbitrary mixed-domain evaluation
> remains outside this result.

<a id="chapter-2-7"></a>

## 2.7 Representables And Variance

Fix `x:K`. The covariant fixed-source representable family is

$$
\mathsf{Rep}_x[k]:=\operatorname{Hom}_K(x,k).
$$

For `p:k -> l`, it acts by postcomposition:

$$
\mathsf{Rep}_x[p](q)=p\circ q.
$$

This is exactly the action used in the WalkingEnd decoder: a based arrow
`q:* -> k` is carried along `p` to `p o q:* -> l`.

The source variable is contravariant. Given `r:x -> y`,
precomposition defines a family morphism

$$
\mathsf{Rep}_y\Longrightarrow\mathsf{Rep}_x,
\qquad
q\longmapsto q\circ r.
$$

Keeping these two variances distinct is not pedantry. Postcomposition changes
the target of an arrow; precomposition changes its source. Emdash gives them
separate runtime owners and compares alternate presentations only where the
types justify it.

<!-- evidence:CAT-REPRESENTABLE -->

> **Formal status — checked.** Evidence `CAT-REPRESENTABLE` covers the
> fixed-source representable and its contravariant source action. Generic
> functoriality owns its action in the varying target.

<a id="chapter-2-8"></a>

## 2.8 The Interfaces Needed By The Main Proof

The Chapter 8 calculation uses only a compact part of this chapter:

1. `Code:W -> Cat` is a directed family, so every based arrow
   `p:* -> x` acts by a functor `Code[p]`.
2. The target family is the representable `Rep_*`, whose base-arrow
   action is postcomposition.
3. Natural powers form a functor from `Path(Nat)` to the based
   hom-category, not merely a function on objects.
4. A contextual decoder is a family morphism from `Code` to
   `Rep_*`; its base-arrow comparison produces the normalization cell.
5. The ordinary and higher functor laws supply identity, composite, and cell
   action without WalkingEnd-specific copies.

The proof therefore depends on category theory at exactly the point where a
carrier-only argument would lose direction. The next chapters add the logical,
equivalence, induction, and height interfaces needed to turn that directed
construction into a numerical classification.
