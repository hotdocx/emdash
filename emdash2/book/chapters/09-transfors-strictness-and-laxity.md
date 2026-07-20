<a id="chapter-9"></a>

# 9. Transfors, Strictness, And Laxity

A functor acts on arrows. A transformation acts one dimension higher: it
compares functors and acts coherently on the arrows between their inputs.
Classical category theory usually packages this coherence as a naturality
square. In an iterated-hom calculus there is a more computational reading.
The square is the boundary of one **off-diagonal action**, and naturality says
that adjacent cuts accumulate into that action.

This chapter develops that reading and then explains why a morphism between
directed families exhibits a different, genuinely lax phenomenon. The
distinction is central to functorial type theory:

- ordinary transfor naturality is strict computation under its generic owner;
- displayed transport comparison is a directed higher cell and need not be
  invertible or judgmentally trivial.

The WalkingEnd decoder already used both ideas. Here we study them in their
own right.

## 9.1 Transformations As The Next Hom

Let `F,G:A\to B` be functors. Their transformation category is the hom
between them in the functor category:

$$
F\Rightarrow G
  :=\operatorname{Hom}_{A\Rightarrow B}(F,G).
$$

An object `eta` of this category is a transfor from `F` to
`G`. At each `x:Obj(A)` it has a component

$$
\eta_x:F(x)\longrightarrow G(x).
$$

Because the transformation category is itself a category, transformations
also have arrows between them. Iterating homs continues to modifications and
higher transfors; the notation changes less than the dimension.

The point component is only the diagonal shadow of a stronger operation. For
objects `x,y` there is a functor

$$
\eta_{x,y}:
\operatorname{Hom}_A(x,y)longrightarrow
\operatorname{Hom}_B(Fx,Gy).
$$

For `f:x\to y`, write its value as

$$
\eta[f]:Fx\longrightarrow Gy.
$$

Taking `f=id_x` recovers the point component. Retaining the whole
functor `eta_{x,y}` also retains its action on 2-cells between source
arrows.

<!-- evidence:TRANSF-POINT-OFFDIAGONAL -->

> **Formal status — checked.** Evidence
> `TRANSF-POINT-OFFDIAGONAL`. `tapp0_fapp0` is the point
> projection, while `tapp1_func` and `tapp1_fapp0` expose the
> iterable and capped off-diagonal actions.

This formulation is especially useful in an omega-categorical setting. If we
stored only the family `eta_x`, every higher consumer would have to
reconstruct naturality before it could act on a cell. The off-diagonal functor
keeps the next hom available from the beginning.

## 9.2 Naturality As Cut Accumulation

Suppose

$$
f:x\to y,
\qquad
g:y\to z.
$$

Postcomposing the off-diagonal component by `G(g)` gives

$$
G(g)\circ\eta[f]:Fx\longrightarrow Gz.
$$

The generic transfor calculus reduces this cut to

$$
\eta[g\circ f].
$$

Dually, if `h:w\to x`, then

$$
\eta[f]\circ F(h)
\quad\rightsquigarrow\quad
\eta[f\circ h].
$$

These are the two strict naturality laws:

$$
\begin{aligned}
G(g)\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F(h)&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

The orientation is cut elimination. A neighboring functor action is absorbed
into the source arrow of the transfor action. Repeated post- or
precomposition can therefore accumulate without expanding the action into a
nest of point components.

<!-- evidence:TRANSF-STRICT-NATURALITY -->

> **Formal status — checked.** Evidence
> `TRANSF-STRICT-NATURALITY`. Both full-functor and capped-arrow
> forms are owned by the generic `tapp*` calculus; the rules are not
> reintroduced for individual transformation constructors.

The usual naturality equation is the identity-boundary case. For
`f:x\to y`, the two routes

$$
G(f)\circ\eta_x
\qquad\text{and}\qquad
\eta_y\circ F(f)
$$

both normalize through the off-diagonal term `eta[f]`. The square
commutes because its two boundary cuts share a canonical interior, not because
every transformation carries an unrelated equality proof attached after the
fact.

This perspective scales. A higher cell between `f` and `f'` is
sent by the functor `eta_{x,y}` to a higher cell between
`eta[f]` and `eta[f']`. Naturality at the next dimension is
therefore ordinary functoriality of an already internalized action.

## 9.3 Identity And Vertical Composition

The identity transfor on `F` has identity point components. If

$$
F\xRightarrow{\eta}G\xRightarrow{\theta}H,
$$

their vertical composite has point component

$$
(\theta\circ\eta)_x
=\theta_x\circ\eta_x.
$$

The same orientation persists at higher projections. In emdash these are
generic identity and composition operations in the transformation category.
They are not constructor-specific definitions of “identity natural
transformation” and “vertical composition.”

This uniformity matters operationally. A component projection may fire before
or after a vertical composite is exposed; both routes meet in the same
pointwise composite. The normal form remains under the operation that owns
the corresponding categorical cut.

## 9.4 Transfors Between Directed Families

Now let `E,D:K\to Cat` be directed families. A natural family morphism

$$
\Phi:E\Longrightarrow D
$$

has a fibre functor

$$
\Phi_k:E[k]\longrightarrow D[k]
$$

at every base object. A transformation

$$
\epsilon:\Phi\Longrightarrow\Psi
$$

has, in turn, a fibrewise transformation

$$
\epsilon_k:\Phi_k\Longrightarrow\Psi_k
$$

and point components at objects `u:E[k]`.

<!-- evidence:TRANSFD-FIBRE-COMPONENTS -->

> **Formal status — checked.** Evidence
> `TRANSFD-FIBRE-COMPONENTS`. The stable displayed presentations are
> `Transfd_cat` and `Transfd`; `Fibre_transf` and
> `Fibre_transf_app` expose their fibre and object projections.

These fibrewise components do not exhaust the structure. When the base moves
along `p:x\to y`, the source and target families transport in
different places. Starting with `u:E[x]`, compare

$$
D[p](\Phi_xu)
\qquad\text{and}\qquad
\Phi_y(E[p]u).
$$

The internal displayed hom action supplies a directed cell

$$
\chi^{\Phi}_{p,u}:
D[p](\Phi_xu)
\longrightarrow
\Phi_y(E[p]u)
$$

in the fibre `D[y]`.

<!-- evidence:FUNCTORD-DISPLAYED-LAXITY -->

> **Formal status — checked.** Evidence
> `FUNCTORD-DISPLAYED-LAXITY`. The endpoint functors are
> `functord_transport_lhs_func` and
> `functord_transport_rhs_func`; the active component is
> `fdapp1_int_cell`.

This is the displayed laxity cell. It has a direction. It is not assumed to
be an equality and it is not assumed to have an inverse. The terminology
“lax” refers to this higher comparison, even though the ordinary functor and
transfor actions surrounding it obey strict computational laws.

## 9.5 Why The Laxity Cell Is Not An Added Square

One might try to define `Phi` as fibre functors plus a separately named
transformation

$$
D[p]\circ\Phi_x
\Longrightarrow
\Phi_y\circ E[p]
$$

for every `p`. This is useful surface notation, but it is not the active
computational representation. Emdash derives the component
`chi(Phi,p,u)` by projecting the internal displayed hom action through
its source, target, presheaf, base-arrow, and fibre-arrow stages.

That longer route has a purpose. Before capping at `u`, it retains the
functorial action needed on fibre arrows and higher cells. The readable
component is the final observation of an iterable construction, not isolated
data with coherence still to be supplied.

For an arbitrary fibre arrow

$$
\alpha:E[p](u)\longrightarrow v,
$$

the capped action gives

$$
\Phi^{d}[p,u,v,\alpha]:
D[p](\Phi_xu)\longrightarrow\Phi_yv.
$$

Its surface reading is

$$
\Phi_y[\alpha]\circ\chi^{\Phi}_{p,u},
$$

but the direct internal-hom projection is the selected runtime owner. This
avoids expanding a stable higher action into an artificial composite every
time it is used.

## 9.6 Total Categories Remember The Comparison

The family morphism induces a functor between total categories

$$
\Sigma\Phi:\sum_{k:K}E[k]\longrightarrow\sum_{k:K}D[k].
$$

An arrow in the source total category consists of

$$
(p,\alpha):(x,u)\longrightarrow(y,v),
$$

where `p:x\to y` and
`alpha:E[p](u)\to v`. Its image is

$$
(p,\Phi^{d}[p,u,v,\alpha]).
$$

Thus the base arrow is preserved and the fibre component is exactly the
capped displayed hom action. The laxity cell is the special case
`v=E[p](u)` and `alpha=id`.

<!-- evidence:FUNCTORD-SIGMA-ACTION -->

> **Formal status — checked.** Evidence `FUNCTORD-SIGMA-ACTION`.
> `sigma_map_func` owns the total functor and its arrow projection uses
> `fdapp1_int_hom_fapp0` rather than rebuilding a separate comparison
> composite.

This gives a concrete meaning to the higher cell: it is precisely the fibre
part required for the induced total functor to act on a canonical transport
arrow.

## 9.7 Strict And Cartesian Specializations

Laxity is permitted, not compulsory. Certain constructions have comparison
cells that collapse in focused situations.

For a section of a constant family, the displayed component agrees
propositionally with ordinary functor arrow action. The agreement is a typed
proof-time comparison; it does not select a second global runtime normal
form.

Representable precomposition is stricter. Given `p:x\to y`, the family
morphism

$$
\operatorname{Rep}_Z(y)\longrightarrow\operatorname{Rep}_Z(x)
$$

sends `q:y\to z` to `q circ p`. On the canonical transported
identity arrow, its displayed comparison reduces to the identity at the
composite. This cartesian behavior is why the `PathOut` composition
benchmark of Chapter 5 computes sharply even though arbitrary family
morphisms remain lax.

The lesson is not that strictness is always preferable. A strict projection
is justified when the construction supplies it and a consumer needs it. The
generic theory remains lax enough to express the contextual WalkingEnd
algebra, whose spiral is intentionally a directed nontrivial cell.

## 9.8 The Decoder Revisited

For the contextual decoder,

$$
\Phi=\mathsf{decode}^{d}:
\mathsf{Code}\Longrightarrow\mathsf{Rep}_*,
$$

the generator comparison is the spiral. At an arbitrary base arrow
`p:*\to x`, evaluate the displayed comparison at zero. The two
endpoints reduce to

$$
p
\qquad\text{and}\qquad
\mathsf{decode}_x(\mathsf{encode}_x(p)),
$$

so the generic laxity component becomes the directed normalization cell of
Chapter 8.

This example explains why it would be misleading to replace displayed
laxity by a commuting equality. Its orientation is the mathematical content
of normalization. Equality is recovered later only because the target
hom-category is discrete.

## 9.9 The Current Packaging Boundary

The calculus has the component-level cell and the entire internal projection
ladder from which it comes. It deliberately does not expose an independent
whole-transformation symbol for

$$
D[p]\circ\Phi_x
\Longrightarrow
\Phi_y\circ E[p]
$$

at every `p`. Adding that facade before it projects coherently through
the source object and higher hom action would create a second owner for the
same semantics.

<!-- evidence:FUNCTORD-WHOLE-LAXITY -->

> **Formal status — research boundary.** Evidence
> `FUNCTORD-WHOLE-LAXITY`. A future whole-square interface should be
> derived from the internal displayed action, come with projection theorems,
> and have a concrete consumer; it must not duplicate component semantics.

The broader principle is now visible. Strictness belongs to generic
functorial and natural cut elimination. Laxity belongs to a higher directed
comparison whose orientation must survive. Both can coexist because they
live at different structural levels.
