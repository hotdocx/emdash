<a id="chapter-11"></a>

# 11. Functors, Transfors, And Functor Categories

Chapter 9 studied transfors as a calculus of cuts. We now make their
categorical organization explicit. Functors are objects of a functor
category, transfors are arrows between those objects, and higher transfors
are obtained by iterating the same hom construction.

This is another spiral rather than a repetition. Ordinary 1-category theory
starts from object functions, hom functions, and pointwise naturality
squares. The native calculus packages all of these as iterable categorical
action. A point component is the identity-boundary case of an off-diagonal
action, and a naturality square is the visible boundary of a computation.

## 11.1 Functors Act At Every Retained Dimension

For ordinary precategories $\mathcal A$ and $\mathcal B$, a functor
$F:\mathcal A\to\mathcal B$ consists of an object function and functions

$$
F_{a,b}:
\operatorname{Hom}_{\mathcal A}(a,b)
\longrightarrow
\operatorname{Hom}_{\mathcal B}(Fa,Fb)
$$

that preserve identities and composition. In the set-valued-hom
specialization, these are ordinary functions between hom sets.

A native emdash functor retains more structure. Its action on a pair of
objects is itself a functor

$$
F_{x,y}:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(Fx,Fy).
$$

Evaluating that functor at an arrow $f:x\to y$ gives $F[f]$. Keeping the full
hom functor visible also keeps its action on 2-cells between arrows, and then
on higher cells by iteration.

<!-- evidence:CAT-FUNCTOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-FUNCTOR-CALCULUS`.
> `fapp0` is object action, `fapp1_func` is the full next-hom action,
> and `fapp1_fapp0` is its value at one arrow. Identity and composition
> reductions belong to these generic owners.

The preservation law is oriented as cut elimination:

$$
F[g]\circ F[f]\rightsquigarrow F[g\circ f].
$$

This is not a theorem copied onto each constructor. It is computation of the
global functor-action interface. A specialized construction should expose its
own semantic projections, while ordinary functoriality remains owned here.

## 11.2 From Natural Transformations To Transfors

For ordinary functors $F,G:\mathcal A\to\mathcal B$, a natural transformation
$\eta:F\Rightarrow G$ is usually presented by arrows

$$
\eta_x:Fx\longrightarrow Gx
$$

such that every $f:x\to y$ satisfies

$$
G[f]\circ\eta_x=\eta_y\circ F[f].
$$

The native transfor retains the common interior of this square. For every
pair $x,y$ it supplies an off-diagonal functor

$$
\eta_{x,y}:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(Fx,Gy).
$$

We write $\eta[f]:Fx\to Gy$ for its value at $f$. The point component is
recovered at the identity:

$$
\eta[\mathrm{id}_x]\rightsquigarrow\eta_x.
$$

<!-- evidence:TRANSF-POINT-OFFDIAGONAL -->

> **Formal status — checked.** Evidence
> `TRANSF-POINT-OFFDIAGONAL`. The point projection is
> `tapp0_fapp0`; `tapp1_func` and `tapp1_fapp0` expose the full and
> capped off-diagonal actions.

This presentation does not add exotic data to an ordinary natural
transformation. In the one-dimensional specialization, naturality determines
the off-diagonal value in either familiar way:

$$
\eta[f]
=G[f]\circ\eta_x
=\eta_y\circ F[f].
$$

In the native higher setting, however, retaining $\eta_{x,y}$ as a functor
also retains its action on cells between possible $f$'s. Point components
alone would hide that action and force it to be reconstructed later.

## 11.3 Naturality Is A Pair Of Family Cuts

Take composable arrows

$$
h:w\to x,\qquad f:x\to y,\qquad g:y\to z.
$$

The two strict naturality computations are

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

Setting $f$ to an identity makes the usual naturality square reappear. Both
boundary composites normalize through the same off-diagonal interior
$\eta[f]$. Thus naturality is not merely a proposition verified after a
family of components has been assembled; it is the way the family action
absorbs neighboring cuts.

<!-- evidence:TRANSF-STRICT-NATURALITY -->

> **Formal status — checked.** Evidence
> `TRANSF-STRICT-NATURALITY`. Both capped equations and their uncapped
> hom-functor forms are runtime reductions of the global `tapp1*`
> calculus. The full forms retain action on the next cells.

This is the chapter's central checked theorem. It explains why the calculus
uses a transfor rather than a bare dependent function of point components:
the transfor is the computational natural family.

## 11.4 The Functor Category

For native categories $A$ and $B$, the category

$$
[A,B]:=\operatorname{Functor\_cat}(A,B)
$$

has functors $A\to B$ as objects. Its hom-category between $F$ and $G$ is

$$
\operatorname{Transf\_cat}(F,G).
$$

An identity arrow in $[A,B]$ is the identity transfor. Composition in
$[A,B]$ is vertical composition of transfors. Iterating the hom of
$\operatorname{Transf\_cat}(F,G)$ yields modifications and higher transfors
without changing the ambient notion of category.

<!-- evidence:CAT-TRANSFOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-TRANSFOR-CALCULUS`.
> `Functor_cat` and `Transf_cat` are active native categories, and
> `Hom_cat(Functor_cat(A,B),F,G)` reduces to the corresponding transfor
> category.

In the ordinary set-valued-hom specialization, the same construction gives a
precategory of functors and natural transformations. Equality between natural
transformations is pointwise because the codomain homs are sets. A natural
transformation is a natural isomorphism exactly when each component is an
isomorphism.

The native formulation is intentionally stronger at the interface. It does
not force all higher transfor structure to be proposition-valued merely
because the first components resemble ordinary natural transformations.

## 11.5 Whiskering And Horizontal Composition

Functor composition acts on transfors in two one-sided ways. If
$\eta:F\Rightarrow G$ and $K:B\to C$, post-whiskering gives

$$
K\eta:KF\Rightarrow KG.
$$

If $H:X\to A$, pre-whiskering gives

$$
\eta H:FH\Rightarrow GH.
$$

These are the transfor-level actions of the same postcomposition and
precomposition functors studied in Chapter 9. They are not independent
definitions of naturality.

Now take

$$
\alpha:F\Rightarrow G:A\to B,
\qquad
\beta:H\Rightarrow K:B\to C.
$$

Their horizontal composite can be read at an object $a$ in either of the
ordinary forms

$$
\beta_{Ga}\circ H[\alpha_a],
\qquad
K[\alpha_a]\circ\beta_{Fa}.
$$

Naturality of $\beta$ identifies the two. The native calculus packages the
pair $(\alpha,\beta)$ under the product-composition action, so its
off-diagonal value first transports the $A$-arrow through $\alpha$ and then
through $\beta$. This gives a single iterable owner rather than two competing
component formulas.

<!-- evidence:TRANSF-HORIZONTAL-CALCULUS -->

> **Formal status — checked.** Evidence
> `TRANSF-HORIZONTAL-CALCULUS`. The generic owner is
> `comp_prod_fapp1_fapp0`; diagnostics check its point, full
> off-diagonal, and capped off-diagonal projections. The ordinary two-formula
> equality is its 1-categorical reading.

## 11.6 Interchange And Controlled Coherence

Vertical and horizontal composition satisfy interchange. Schematically, for
a composable four-cell grid,

$$
(\beta_2\circ\beta_1)\ast(\alpha_2\circ\alpha_1)
=
(\beta_2\ast\alpha_2)\circ(\beta_1\ast\alpha_1).
$$

In an ordinary functor precategory this is an equality of natural
transformations, proved componentwise using associativity and naturality. In
the native calculus, the corresponding computation is organized by the
generic product-composition action and the off-diagonal vertical-composite
folds. A representable four-cell instance is exposed as propositional
interchange evidence.

The equality mode matters. Functor composition has associativity and unit
comparisons, and ordinary category theory packages their familiar pentagon
and triangle coherences. Emdash does not install unrestricted reassociation
in both directions as runtime computation. Instead:

- a semantic owner absorbs a neighboring cut when it has a selected normal
  form;
- proof-time comparison is used when two presentations should elaborate
  together but neither should replace the other globally;
- propositional equality records a theorem without changing runtime normal
  forms;
- higher transfors retain coherence data that is not truncated away.

This is the categorical version of controlling associativity. Parentheses may
be suppressed in mathematical prose when the intended composite is
unambiguous, but the formal presentation must still select an owner and an
equality mode.

## 11.7 The Ordinary Functor-Category Theorem

Let $\mathcal A$ be an ordinary precategory and $\mathcal B$ an ordinary
univalent category. Then the functor precategory
$[\mathcal A,\mathcal B]$ is a univalent category. The reason is
pointwise but not merely syntactic:

1. an identity $F=G$ gives a natural isomorphism by identity induction;
2. a natural isomorphism gives pointwise isomorphisms $Fx\cong Gx$;
3. univalence of $\mathcal B$ turns those into pointwise identities;
4. function extensionality assembles equality of object functions;
5. the functor laws and naturality data are propositions at this height, so
   the assembled equality determines the whole functor.

The same analysis shows that identity between ordinary functors agrees with
natural isomorphism.

<!-- evidence:UCAT-FUNCTOR-CATEGORY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-FUNCTOR-CATEGORY`. This is the HoTT 1-categorical theorem under
> set-valued-hom and univalent-codomain hypotheses. The active native
> `Functor_cat` supplies the categorical object, but this general
> identity-to-natural-isomorphism equivalence is not a checked emdash theorem.

## 11.8 The Native Functor-Category Boundary

A native analogue cannot be obtained by deleting the word *set* from the
ordinary proof. One must choose the relevant sameness of functors—object
identity, ordinary isomorphism in `Functor_cat`, pointwise native
omega-equivalence, or a higher adjoint equivalence—and then prove that the
comparison respects:

- point components;
- off-diagonal arrow action;
- cells between source arrows;
- vertical and horizontal composition;
- every further retained hom level.

Pointwise object formulas are therefore necessary but insufficient. The
active code has the functor category, the full transfor calculus, and selected
object-path and ordinary-isomorphism lifts. It does not yet combine them into
a general univalence theorem for native functor categories.

> **Formal status — research boundary.** The missing owner is a native
> category-univalence package stable under `Functor_cat` and coherent with
> `tapp1_func` at every retained dimension. Chapter 15 discusses the
> saturation problem that such a theorem would have to solve.

The computational lesson survives independently of that boundary. Functors
and transfors already form a native higher category, and their naturality is
already internal computation. Univalence would identify the right notion of
sameness in this existing structure.
