<a id="chapter-9"></a>

# 9. Transfors And The Calculus Of Cuts

Composition is indispensable, but a syntax made only of nested composites
quickly forgets why a particular reassociation matters. Functorial type theory
therefore gives important cuts a name and a computational owner. A functor
acts on an arrow; postcomposition and precomposition act on represented homs;
a transfor acts off the diagonal; and a universal construction eliminates a
map through the object it represents. Each operation controls its own
reassociation.

This point of view is inspired by the categorical proof theory of
[Došen's *Cut Elimination in Categories*](#ref-dosen-cut-elimination).
We use that work only as a conceptual reference. The presentation below is
newly written for emdash, whose iterated homs and directed families require a
different formal architecture.

The gain is not merely prettier notation. A selected cut can compute while
retaining the functor or transfor that acts on the next hom. An unrestricted
associativity rewrite would erase that information, create competing normal
forms, or loop by repeatedly changing brackets. Controlled cut elimination
instead answers three questions at once: what is being eliminated, where its
normal form lives, and which higher action survives.

## 9.1 Four Levels Of Cuts

We shall use four levels throughout the rest of the book.

1. An **arrow cut** composes one chosen arrow on the left or right. Its
   owners are the lower-star postcomposition and upper-star precomposition
   actions.
2. A **family cut** composes next to an arrow that varies naturally. Its
   owner is the off-diagonal action of a transfor.
3. A **structural cut** eliminates data introduced by a product, dependent
   total, curry, or related type former. Its owner is the corresponding
   projection or eliminator.
4. A **universal cut** factors through a chosen representing object. Its
   owner is an adjunction, representability comparison, or another explicit
   universal-property interface.

These levels are not four unrelated collections of rewrite rules. They form a
progression. Arrow cuts explain local composition; family cuts explain
naturality; structural cuts explain computation for categorical type formers;
and universal cuts explain why constructions such as adjoints, Yoneda maps,
and weighted limits compute.

We also keep four equality modes distinct. A runtime reduction selects a
normal form. A proof-time comparison helps Lambdapi elaborate two intended
presentations without making either one compute to the other. A propositional
equality is an internal witness. A mathematical equality in free-form theory
states the intended theorem while naming the interface still needed to check
it. The symbol $\rightsquigarrow$ below is reserved for an actual selected
runtime reduction; an ordinary equality sign does not silently make that
claim.

In the terminology of
[Appendix G.4](#appendix-formal-presentation-g4), each named cut is an
elimination followed by a computation rule. Its formation and introduction
data determine which composite is well typed; its full functor or transfor
owner supplies higher action; and any eta or uniqueness principle is stated
separately. This is why a pointwise naturality equation cannot replace
`tapp1_func`, and why a universal comparison needs both beta and eta rather
than one attractive factorization formula.

## 9.2 Arrow Cuts

Composition is written $g\circ f$: first $f$, then $g$. The two star actions
record which side of a represented hom is moving.

If $g:w\to x$ and $u:x\to y$, then

$$
u_*(g):=u\circ g:w\to y
$$

is **postcomposition** by $u$. If $u:x\to y$ and $h:y\to z$, then

$$
u^*(h):=h\circ u:x\to z
$$

is **precomposition** by $u$. Lower star is covariant in the moving target;
upper star is contravariant in the moving source. They are different
operations, not typographic variants.

The implemented forms are slightly more general. For $K:A\to B$ and
$p:x\to y$ in $A$, postcomposition uses $K[p]$ on a hom ending at $Kx$,
while precomposition uses $K[p]$ on a hom beginning at $Ky$. Retaining $K$
is what lets the action iterate on higher cells.

### 9.2.1 Example 1: Postcomposition Accumulates

Let

$$
g:w\to x,\qquad u:x\to y,\qquad v:y\to z.
$$

Two consecutive lower-star cuts reduce to one:

$$
v_*(u_*(g))\rightsquigarrow(v\circ u)_*(g).
$$

Both sides are arrows $w\to z$. The selected normal form retains a single
postcomposition action whose moving arrow is $v\circ u$; it does not expand
to a raw threefold composite. The generic owner is
`hom_postcomp_fapp0`, and the displayed equality mode is runtime reduction.
Before capping at $g$, `hom_postcomp_func` remains a functor between
hom-categories, so its action on 2-cells between possible values of $g$ is
still available.

The functor-indexed version says the same thing. If $p:x\to y$ and
$q:y\to z$ in $A$, then consecutive action by $K[p]$ and $K[q]$ accumulates
under the single arrow $q\circ p$. Ordinary functoriality belongs to the
generic `fapp*` calculus; no constructor receives a private composition law.

### 9.2.2 Example 2: Precomposition Reverses The Action Order

Let

$$
u:w\to x,\qquad v:x\to y,\qquad h:y\to z.
$$

The corresponding upper-star reduction is

$$
u^*(v^*(h))\rightsquigarrow(v\circ u)^*(h).
$$

Both sides are arrows $w\to z$. The selected normal form is one
precomposition action along $v\circ u$. The generic owner is
`hom_precomp_along_fapp0`, and this is again runtime reduction. Its uncapped
form `hom_precomp_along_func` remains a functor on the represented hom, with
the next hom-action intact.

The order is worth reading twice. Starting with $h$, we first precompose by
$v$ and then by $u$, but the accumulated base arrow is $v\circ u$. Thus

$$
u^*\circ v^*=(v\circ u)^*.
$$

That reversal is contravariance, not a special exception to associativity.

<!-- evidence:CAT-HOM-CUTS -->

> **Formal status — checked.** Evidence `CAT-HOM-CUTS`. The full and capped
> lower-star and upper-star actions have identity, consecutive-action, and
> adjacent raw-cut computations. Their ordinary-composition readings remain
> proof-time comparisons where selecting a second runtime normal form would
> be harmful.

### 9.2.3 Why There Is No Global Associativity Rewrite

The ordinary associator is available as a proof-time comparison and as
propositional evidence. It is not installed as a pair of unrestricted runtime
rules. Such rules would either orient every composite toward a normal form
that ignores semantic owners or permit both bracketings and loop.

Star accumulation is narrower. It reassociates exactly when one side is a
represented-hom action, and its result retains that action as a stable head.
The same policy will govern the next three levels: eliminate the cut at the
construction that understands it.

## 9.3 Family Cuts

Let $F,G:A\to B$ and let $\eta:F\Rightarrow G$. A point component
$\eta_x:Fx\to Gx$ is only the diagonal of a more useful operation. For every
$x,y:A$ there is an off-diagonal functor

$$
\eta_{x,y}:\operatorname{Hom}_A(x,y)\longrightarrow
           \operatorname{Hom}_B(Fx,Gy).
$$

For $f:x\to y$, write its value as $\eta[f]:Fx\to Gy$. Setting
$f=\mathrm{id}_x$ recovers $\eta_x$; retaining the whole functor retains its
action on 2-cells between arrows $f$.

<!-- evidence:TRANSF-POINT-OFFDIAGONAL -->

> **Formal status — checked.** Evidence `TRANSF-POINT-OFFDIAGONAL`.
> `tapp0_fapp0` observes the point component, while `tapp1_func` and
> `tapp1_fapp0` expose the iterable and capped off-diagonal actions.

### 9.3.1 Example 3: The Two Naturality Cuts

Take arrows

$$
h:w\to x,\qquad f:x\to y,\qquad g:y\to z.
$$

There are two neighboring cuts, one on each side of the varying arrow:

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

The first source and target are $Fx\to Gz$; the second are $Fw\to Gy$.
In each case the selected normal form is one off-diagonal action on the
composite source arrow. The generic owner is `tapp1_fapp0`, and both
displayed equalities are runtime reductions. At the uncapped level
`tapp1_func` remains a functor between hom-categories, so a 2-cell between
$f$ and $f'$ is carried to a 2-cell between $\eta[f]$ and $\eta[f']$ after
the cut has normalized.

<!-- evidence:TRANSF-STRICT-NATURALITY -->

> **Formal status — checked.** Evidence `TRANSF-STRICT-NATURALITY`. Both
> full-functor and capped-arrow forms are owned by the generic `tapp*`
> calculus. Constructor-specific copies of ordinary naturality are neither
> needed nor desired.

The familiar naturality square is the identity-boundary instance. For
$f:x\to y$, the expressions $G[f]\circ\eta_x$ and
$\eta_y\circ F[f]$ both normalize through the common interior $\eta[f]$.
Naturality is therefore not an equality proof added after defining a family
of point components. It is computation exposed by the family action itself.

Identity and vertical composition follow the same architecture. The identity
transfor and a vertical composite live in the transformation category, so
their component projections use the generic identity and composition
calculus. Higher transfors arise by iterating the next hom rather than by
inventing a separate coherence language at every dimension.

## 9.4 Structural Cuts

A structural cut applies an eliminator to data whose introduction form is
known. Product projections are the simplest case, but they already reveal an
important distinction between the general categorical theory and the
currently checked category-of-categories instance.

### 9.4.1 Example 4: The Product/Projection Benchmark In A General Category

Let $K$ be a category equipped with chosen binary products. Take objects

$$
A_0,A_1,B_0,B_1,C:\operatorname{Obj}(K)
$$

and arrows

$$
h:A_0\to A_1,\qquad
k:B_0\to B_1,\qquad
g:A_1\to C.
$$

Write $h\times k:A_0\times B_0\to A_1\times B_1$ for the induced product
arrow, and distinguish the two projections by

$$
\pi_1^1:A_1\times B_1\to A_1,
\qquad
\pi_1^0:A_0\times B_0\to A_0.
$$

Upper-star precomposition in $K$ gives

$$
(\pi_1^1)^*(g):A_1\times B_1\to C.
$$

The Došen-style product cut is the equation

$$
(\pi_1^1)^*(g)\circ(h\times k)
=
(\pi_1^0)^*(g\circ h),
$$

with both sides in $\operatorname{Hom}_K(A_0\times B_0,C)$. Its intended
computational orientation is left to right. The calculation combines two
controlled steps:

$$
\pi_1^1\circ(h\times k)=h\circ\pi_1^0
$$

by product projection, followed by upper-star accumulation. The arrow $k$
disappears because the first projection observes only the first component.

The source is a composite out of $A_0\times B_0$ and the target is a single
upper-star cut with the same source and codomain. The proposed normal form is
$(\pi_1^0)^*(g\circ h)$. Its future generic owners should be the upper-star
action together with chosen product projections and the bifunctorial action
of the product structure in $K$. The equality mode here is mathematical
development: emdash does not yet package binary products of objects in an
arbitrary ambient category with this universal computation. Such an owner
should retain the next-hom actions of the projection and product-arrow
operations, rather than stop at a 1-categorical equation.

> **Formal status — mathematical development.** The general theorem assumes a
> chosen binary-product interface internal to an arbitrary category $K$,
> including product arrows, projection beta, and iterable higher action. The
> active product package instead supplies binary products of categories, which
> gives the specialization $K=\mathsf{Cat}$ described next.

### 9.4.2 The Checked Cat-Specialized Legs

Set $K=\mathsf{Cat}$. Then $A_i,B_i,C$ are categories and $h,k,g$ are
functors. The active product-valued-functor representation exposes projection
by a Sigma observation. Its checked structural reduction is

$$
\mathsf{fst}(h\times k)\rightsquigarrow h\circ\pi_1^0.
$$

The checked, owner-aligned upper-star cut is

$$
(\pi_1^0)^*(h^*(g))
\rightsquigarrow
(h\circ\pi_1^0)^*(g),
$$

and $h^*(g)$ is proof-time comparable with the readable composite
$g\circ h$. Both owner-aligned sides retain the upper-star precomposition
head and therefore its higher action on transfors between possible functors
$g$.

The literal $\mathsf{Cat}$ instance of the general equation is not currently
one runtime reduction. A focused typed audit found both sides well formed,
checked the two owner-aligned legs, and found that neither runtime conversion
nor typed reflexivity joins the raw composite
$\pi_1^1\circ(h\times k)$ directly to the selected observation
$\mathsf{fst}(h\times k)$. Packaging that narrow projection/composition
comparison would suffice. Installing a broad product eta rewrite would be a
much stronger and unsafe response.

<!-- evidence:CUT-PRODUCT-PROJECTION -->

> **Formal status — formal consequence.** Evidence
> `CUT-PRODUCT-PROJECTION`. The $\mathsf{Cat}$-specialized equation follows
> from controlled associativity, upper-star composition, and the checked
> product projection. The diagnostic suite checks the owner-aligned
> reduction. The literal raw-composite bridge is not packaged, so the
> textbook display is not labeled a checked kernel reduction.

### 9.4.3 Example 5: Product Beta Is Elimination After Introduction

In a category $K$ with chosen products, arrows $p:X\to A$ and $q:X\to B$
have a pairing $\langle p,q\rangle:X\to A\times B$. The characteristic
structural cuts are

$$
\pi_1\circ\langle p,q\rangle=p,
\qquad
\pi_2\circ\langle p,q\rangle=q.
$$

The source and target of the first equation lie in
$\operatorname{Hom}_K(X,A)$, and those of the second lie in
$\operatorname{Hom}_K(X,B)$. Their proposed normal forms are $p$ and $q$.
For arbitrary $K$, the owners and higher action belong to the same future
chosen-product interface as Example 4, so these equations are mathematical
development rather than claims about the present kernel.

The active category-of-categories specialization is nevertheless concrete.
For arrows $p:a\to a'$ in $A$ and $q:b\to b'$ in $B$, the pair $(p,q)$ is an
arrow $(a,b)\to(a',b')$ in the product category. The projection functors
compute:

$$
\pi_1[p,q]\rightsquigarrow p,
\qquad
\pi_2[p,q]\rightsquigarrow q.
$$

Here the selected normal forms are the component arrows themselves. The
specialized owners are the capped hom-actions of
`Product_projL_func` and `Product_projR_func`, and the equality mode is
runtime reduction. Before capping, each full hom-action remains a projection
functor from a product of hom-categories, so higher component cells remain
available.

<!-- evidence:CAT-PRODUCT-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-PRODUCT-CALCULUS`. Product
> categories, product maps, projection functors, and their object and hom
> projections have focused componentwise computations. This is evidence for
> the desired general architecture, not an assertion that arbitrary
> object-level products in every $K$ are already implemented.

### 9.4.4 Fibred Structural Cuts

The same introduction/elimination pattern appears in a dependent categorical
context. Let $B,C:K\vdash\mathsf{Cat}$ be independent families over one base,
and let $P(B,C)$ be their fibrewise product. For displayed functors

$$
\Phi:E\Longrightarrow B,
\qquad
\Psi:E\Longrightarrow C,
$$

pairing introduces a map
$\mathsf{pair}_d(\Phi,\Psi):E\Longrightarrow P(B,C)$, while the two displayed
projections eliminate it. Their structural cuts are whole displayed-functor
reductions:

$$
\mathsf{projL}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Phi,
\qquad
\mathsf{projR}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Psi.
$$

These equations say more than pointwise product beta. At an object $k:K$,
pairing is the ordinary product pairing in the fibre. Over a base arrow
$p:k\to l$, its action is the pair of the two displayed actions over the
same $p$. Its canonical internalized cell at a fibre object $u$ is likewise
componentwise:

$$
\mathsf{cell}\bigl(\mathsf{pair}_d(\Phi,\Psi),p,u\bigr)
=
\bigl(
  \mathsf{cell}(\Phi,p,u),
  \mathsf{cell}(\Psi,p,u)
\bigr).
$$

Thus the elimination cuts remain valid while object action, base-arrow
action, and the selected next-cell observation stay internally functorial.
This is the structural calculus of independent siblings
$k:K,b:B[k],c:C[k]$; it does not exchange a variable with another whose
classifier depends on it.

<!-- evidence:CAT-FIBREWISE-CONTEXT -->

> **Formal status — checked.** Evidence `CAT-FIBREWISE-CONTEXT` covers the
> fixed-base displayed projections and pairing, both whole
> projection-after-pairing reductions, and their componentwise fibre,
> base-arrow, internalized-cell, and selected higher observations. The
> arbitrary-$K$ chosen-object-product interface of Examples 4 and 5 remains a
> separate mathematical development.

## 9.5 Universal Cuts

A universal property turns a family of maps into a chosen object together
with inverse ways of introducing and eliminating a factorization. Its
computation laws are higher-level cut elimination. Adjunction triangles are
the first example; representability, co-Yoneda, and weighted limits continue
the same line.

### 9.5.1 Example 6: The Two Adjunction Triangles

Let $F:R\to L$ be left adjoint to $G:L\to R$, with unit
$\eta:\mathrm{id}_R\Rightarrow GF$ and counit
$\varepsilon:FG\Rightarrow\mathrm{id}_L$.

For $g:X\to X'$ in $R$ and $f:FX'\to Y$ in $L$, the left triangle cut is

$$
\varepsilon[f]\circ F[\eta[g]]
\rightsquigarrow
f\circ F[g].
$$

Both sides have source $FX$ and target $Y$. The selected normal form removes
the adjacent unit-counit detour while preserving the ordinary functor action
$F[g]$.

Dually, for $f:X\to GY'$ in $R$ and $g:Y'\to Y$ in $L$, the right triangle
cut is

$$
G[\varepsilon[g]]\circ\eta[f]
\rightsquigarrow
G[g]\circ f.
$$

Both sides have source $X$ and target $GY$. The selected normal form again
removes the universal detour and retains the functorial image of the boundary
arrow.

The owners are not arbitrary transformations with the same types. They are
the stable unit and counit observations of the indexed `Adjunction` witness,
and both equations are runtime reductions. Their components use the
off-diagonal `tapp1` action, so action on higher cells in $f$ and $g$ remains
part of the surrounding functorial calculus.

<!-- evidence:ADJ-TRIANGLE-CUTS -->

> **Formal status — checked.** Evidence `ADJ-TRIANGLE-CUTS`.
> `unit_adj_transf` and `counit_adj_transf` are the selected observations
> that trigger the two reductions. Independently named unit-shaped and
> counit-shaped transfors do not acquire these computations by type alone.

### 9.5.2 Example 7: The Shaped Co-Yoneda Beta Cut

For a profunctor $P:A\rightsquigarrow B$, the right and left unit maps have
the forms

$$
P\otimes_B U_B\Longrightarrow P,
\qquad
U_A\otimes_A P\Longrightarrow P.
$$

If $p$ is a shaped element and $\mathrm{id}$ is the matching identity-shaped
hom element, their component cuts reduce as

$$
\varepsilon^R_P(p\otimes\mathrm{id})\rightsquigarrow p,
\qquad
\varepsilon^L_P(\mathrm{id}\otimes p)\rightsquigarrow p.
$$

The source is a shaped element of the corresponding tensor and the target is
the original shaped element of $P$. The normal form is $p$; the owners are the
two `Prof_coyoneda_*` transformations; and the equality mode is runtime
reduction on the selected shaped cells. Naturality-fusion remains available
for a profunctor map $P\to P'$, so this beta law is not merely a capped
set-level equation.

<!-- evidence:PROF-COYONEDA -->

> **Formal status — checked.** Evidence `PROF-COYONEDA`. Chapter 13 develops
> the representable and profunctor context required to read this calculation
> as the computational core of Yoneda.

### 9.5.3 Example 8: Weighted-Limit Beta And Eta

A computational weighted-limit witness is a comparison between the weighted
cone profunctor and the representable hom profunctor at the proposed limit.
After reindexing along a probe $M:I\to B$, it supplies operations

$$
\mathsf{push}(r):R\Longrightarrow\operatorname{Hom}(M,L),
\qquad
\mathsf{pull}(s):R\Longrightarrow\operatorname{Cone}_W(M,F).
$$

Their universal cuts reduce in both directions:

$$
\mathsf{pull}(\mathsf{push}(r))\rightsquigarrow r,
\qquad
\mathsf{push}(\mathsf{pull}(s))\rightsquigarrow s.
$$

The source and target are profunctor maps of the displayed kinds, and the
normal forms are the original maps $r$ and $s$. The generic owners are
`prof_comparison_push` and `prof_comparison_pull`; the weighted names
merely specialize their types. The equality mode is runtime beta/eta
reduction. The comparison can still be reindexed, symmetrized, and composed,
so the higher universal structure is retained instead of being collapsed to
a chosen set-level bijection.

<!-- evidence:PROF-COMPARISON-BETA-ETA -->

> **Formal status — checked.** Evidence
> `PROF-COMPARISON-BETA-ETA`. Chapter 16 turns this general comparison
> calculus into the weighted-limit interface.

### 9.5.4 Example 9: A Right Adjoint Preserves The Weighted Limit

Suppose $L_{\!a}:A\to B$ is left adjoint to $R_{\!a}:B\to A$, and a
comparison certifies $L:J'\to B$ as the $W$-weighted limit of $F:J\to B$.
Three universal cuts compose: move a cone across the adjunction, use the
given representation, and move the representing hom back. The output is a
comparison certifying $R_{\!a}L$ as the weighted limit of $R_{\!a}F$.

The source is the supplied weighted-limit comparison together with the
adjunction; the target is the transported comparison in $A$. The selected
normal form is the composite of the two adjunction-mate comparisons and the
reindexed limit comparison. Its owner is
`right_adjoint_preserves_weighted_limit_cov_comp`. This is a checked
construction, not a rewrite asserting that arbitrary limit syntax commutes
with every right adjoint. The resulting comparison retains its push/pull
beta-eta action on every probe and profunctor map.

<!-- evidence:WEIGHTED-LIMIT-PRESERVATION -->

> **Formal status — checked.** Evidence
> `WEIGHTED-LIMIT-PRESERVATION`. The theorem is developed in Chapter 16
> after weights, cones, and mate comparison have been introduced.

### 9.5.5 Example 10: The Weighted-Colimit Dual

A $W$-weighted colimit in $B$ is represented by the corresponding weighted
limit in $B^{\mathrm{op}}$. Applying the preceding theorem to the opposite
adjunction gives the dual statement: a left adjoint preserves the selected
weighted colimit.

The source is a weighted-colimit comparison and an adjunction; the target is
the transported comparison after the left adjoint. The selected normal form
is the opposite of the right-adjoint preservation composite, with double
opposites and reversed composition reduced by the generic duality owners. The
construction is checked under
`left_adjoint_preserves_weighted_colimit_con`. Its output is still a full
comparison with push/pull behavior after passing to opposites, not merely an
equality of chosen objects.

<!-- evidence:WEIGHTED-COLIMIT-PRESERVATION -->

> **Formal status — checked.** Evidence
> `WEIGHTED-COLIMIT-PRESERVATION`. Chapter 17 develops the variance and
> opposite-category calculation in full.

## 9.6 What Cut Elimination Preserves

The ten examples have a common shape:

$$
\text{introduction or action}
\quad+\quad
\text{matching elimination}
\quad\longrightarrow\quad
\text{one semantic owner}.
$$

Their normal forms are deliberately not all raw composites. Lower star keeps
postcomposition visible; upper star keeps precomposition visible; `tapp1`
keeps the varying arrow family visible; product projection keeps a structural
component visible; and a universal comparison keeps its inverse operations
visible. This is what makes the calculus iterable.

In particular, a capped equation is not the whole meaning of a construction.
The full `hom_postcomp_func`, `hom_precomp_along_func`, and
`tapp1_func` operations act on the next hom. Product projection has a full
hom-functor. Profunctor comparison can be reindexed and composed. A good
reduction removes the cut without discarding the object that
higher-dimensional consumers need.

## 9.7 Directed Family Transfors And Lax Comparison

Strict cut elimination should not be confused with strictness of every
directed comparison. Let $E,D:K\to\mathsf{Cat}$ be directed families and let

$$
\Phi:E\Longrightarrow D
$$

be a natural family morphism. At each $k:K$ it has a fibre functor
$\Phi_k:E[k]\to D[k]$. A transfor $\epsilon:\Phi\Rightarrow\Psi$ has a
fibrewise transfor and point components at objects of each fibre.

<!-- evidence:TRANSFD-FIBRE-COMPONENTS -->

> **Formal status — checked.** Evidence `TRANSFD-FIBRE-COMPONENTS`. The
> stable displayed presentations are `Transfd_cat` and `Transfd`;
> `Fibre_transf` and `Fibre_transf_app` expose their fibre and object
> projections.

When the base moves along $p:x\to y$, the two relevant transports do not have
to be equal. Starting with $u:E[x]$, the internal displayed hom action gives
a directed cell

$$
\chi^\Phi_{p,u}:
D[p](\Phi_xu)\longrightarrow\Phi_y(E[p]u)
$$

in $D[y]$. This is the displayed laxity cell. It has a direction and need not
be invertible. The generic functor and transfor cuts around it compute
strictly, but the comparison itself remains mathematical data.

<!-- evidence:FUNCTORD-DISPLAYED-LAXITY -->

> **Formal status — checked.** Evidence
> `FUNCTORD-DISPLAYED-LAXITY`. The endpoint functors are
> `functord_transport_lhs_func` and `functord_transport_rhs_func`; the
> active component is `fdapp1_int_cell`.

For a fibre arrow $\alpha:E[p](u)\to v$, the capped displayed action has the
readable form

$$
\Phi_y[\alpha]\circ\chi^\Phi_{p,u}:
D[p](\Phi_xu)\longrightarrow\Phi_yv.
$$

The direct internal-hom projection is the runtime owner. Expanding it into
this composite on every use would discard the stable higher action and give
the comparison a second owner.

## 9.8 Total Categories And The WalkingEnd Decoder

The family morphism induces a functor on total categories,

$$
\Sigma\Phi:\sum_{k:K}E[k]\longrightarrow\sum_{k:K}D[k].
$$

An arrow in the source has the form $(p,\alpha):(x,u)\to(y,v)$, where
$\alpha:E[p](u)\to v$. Its image is

$$
(p,\Phi^d[p,u,v,\alpha]).
$$

Thus the base arrow is retained and the fibre arrow is exactly the capped
displayed hom action. The laxity cell is the special case in which
$v=E[p](u)$ and $\alpha$ is the identity.

<!-- evidence:FUNCTORD-SIGMA-ACTION -->

> **Formal status — checked.** Evidence `FUNCTORD-SIGMA-ACTION`.
> `sigma_map_func` owns the total functor, whose arrow projection uses the
> capped internal displayed action rather than reconstructing a comparison
> composite.

For the contextual WalkingEnd decoder

$$
\mathsf{decode}^d:\mathsf{Code}\Longrightarrow\mathsf{Rep}_*,
$$

the generator comparison is the spiral. Evaluated at a base arrow $p:*\to x$
and zero, its endpoints reduce to

$$
p
\qquad\text{and}\qquad
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

The generic laxity component is therefore the directed normalization cell of
Chapter 8. Replacing it by a commuting equality at the outset would erase the
content of normalization. Equality is extracted only later, using
discreteness of the target hom-category.

## 9.9 The Packaging Boundary

The calculus now has a continuous line from local arrow composition to
weighted universal properties. Its discipline is equally important in the
negative direction.

- The arbitrary-$K$ product benchmark needs a general chosen-product
  interface. Its $\mathsf{Cat}$ instance still awaits one narrow packaged
  projection/composition comparison; neither gap justifies broad product eta.
- A displayed family morphism has the component-level laxity cell and its
  full internal projection ladder, but no duplicate whole-square facade.
- General ends, coends, and arbitrary Kan extensions require universal
  interfaces stronger than the selected profunctor operations.
- Runtime conversion, proof-time comparison, internal equality, and
  equivalence remain different judgments.

<!-- evidence:FUNCTORD-WHOLE-LAXITY -->

> **Formal status — research boundary.** Evidence
> `FUNCTORD-WHOLE-LAXITY`. A future whole-transfor comparison between
> $D[p]\circ\Phi_x$ and $\Phi_y\circ E[p]$ should be derived from the internal
> displayed action, project coherently through higher homs, and serve a
> concrete consumer. It must not duplicate the component semantics.

Cut elimination is therefore not a feature catalogue. It is the organizing
principle by which functorial type theory decides what should compute, what
should merely compare, and what higher structure must remain visible after a
calculation is complete.
