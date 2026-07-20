<a id="chapter-6"></a>

# 6. Directed Higher Inductive Types

An ordinary inductive type is specified by point constructors. A higher
inductive type may also be specified by path constructors and constructors
between paths. In a directed foundation, the corresponding presentation may
contain objects, directed arrows, and higher directed cells. The change is
small in notation and large in meaning: an arrow constructor does not carry
an inverse unless inverse data are separately supplied.

This chapter develops the one directed higher-inductive interface that the
current emdash calculus actually implements. It is enough to support the
central calculation of Chapter 8 and to reveal what a reusable directed-HIT
schema would have to provide. We will not promote this single example into a
general theorem about all cell presentations.

## 6.1 Constructors With Direction

At a schematic level, a directed higher-inductive category may have:

- **object constructors**, such as `b:Obj(W)`;
- **arrow constructors**, such as $\ell:b\to b$;
- **cell constructors**, identifying or comparing composites of arrows;
- **dimension conditions**, controlling which higher cells remain
  nontrivial.

The eliminator must mirror these constructors. A nondependent recursor into a
category `C` asks for an interpretation of every object, arrow, and cell
constructor in `C`. A dependent eliminator into a family `D` asks for
lifts in the appropriate fibres. A contextual eliminator between two families
asks for fibre functors together with comparison cells. In each case,
constructor computations say that the induced map observes the supplied data
at the constructors.

For a groupoidal path constructor, one may freely use inverse paths in later
reasoning. For a directed arrow constructor, that move is unavailable. If a
presentation contains only

$$
\ell:b\longrightarrow b,
$$

then it generates forward composites
$\mathrm{id}_b,\ell,\ell\circ\ell,\ldots$; no negative power has been
introduced. This is the fundamental distinction between the walking
endomorphism and the circle.

The formal ledger for such a signature is therefore longer than a constructor
list. It records formation, introductions and their boundaries, the chosen
eliminator, constructor beta rules, higher action and coherence, dimension
data, and the current uniqueness status. The general template and the exact
WalkingEnd instance are collected in
[Appendix G.6](#appendix-formal-presentation-g6); this chapter develops the
same clauses in mathematical order.

## 6.2 The Selected Walking Signature

Write `W` for the category `WalkingEnd`, with constructors

$$
*:\operatorname{Obj}(W),
\qquad
\ell:\operatorname{Hom}_W(*,*).
$$

The category is opaque. Its object classifier, hom-categories, identities,
and composition are not defined by reducing them to a Nat model. Alongside
the constructors, the signature retains evidence that `W` is
one-dimensional: every hom-category is discrete.

<!-- evidence:WE-SIGNATURE -->

> **Formal status — checked.** Evidence `WE-SIGNATURE`.
> `WalkingEnd_cat`, `walking_base`, and `walking_loop` are
> opaque declarations. `walking_end_is_one_cat` is explicit signature
> evidence; it does not unfold the category into a concrete presentation.

One-dimensionality is a height condition, not an invertibility condition. It
says that parallel 2-cells in each hom are equality-like and that there are no
nontrivial higher directed layers there. It does not say that every 1-cell of
`W` has a reverse. Chapter 7 will make the distinction precise.

Why keep `W` opaque? Because the theorem in Chapter 8 is then a
consequence of its constructors, eliminator, and dimension evidence. If its
based hom were defined to be Nat, the calculation would merely restate a
definition. Opacity turns the comparison with Nat into a normalization
theorem.

## 6.3 The Contextual Algebra

Let

$$
R,D:W\longrightarrow\mathsf{Cat}
$$

be directed Cat-valued families. At the base, suppose we are given a functor

$$
u:R[*]\longrightarrow D[*].
$$

There are two ways to move an element of `R[*]` once around the
generator and then apply `u`:

$$
D[\ell]\circ u,
\qquad
u\circ R[\ell].
$$

The selected lax orientation asks for a transformation

$$
\sigma:
D[\ell]\circ u
\Longrightarrow
u\circ R[\ell].
$$

These data form the contextual algebra of the walking endomorphism. Its
eliminator produces a displayed functor

$$
\mathsf{ind}^{d}(R,D,u,\sigma):R\Longrightarrow D
$$

over the whole of `W`.

<!-- evidence:WE-CONTEXTUAL-ELIMINATOR -->

> **Formal status — checked.** Evidence
> `WE-CONTEXTUAL-ELIMINATOR`. The owner is
> `walking_end_ind_funcd`. Its base component computes to `u`, and
> its displayed action on the literal generator computes to the component of
> `sigma` at the selected source object.

The direction of `sigma` deserves attention. It is not an equality
asserting strict commutation, nor is it automatically reversible. It is a
directed cell comparing the two composites. This is the right amount of
coherence for the displayed-functor interface used by emdash: composition
with base action commutes laxly in the selected direction, and higher
naturality continues through the generic transfor calculus.

The word “contextual” means that the eliminator retains `R`, the context
from which inputs are drawn. Removing `R` too early would reduce `u`
to a single object and `sigma` to a single lift. That specialization is
useful, but it cannot construct Chapter 8's decoder from one nonconstant
family to another.

## 6.4 Sections And Recursors Are Special Cases

Take `R` to be the constant terminal family. A functor
$R[*]\to D[*]$ is determined by an object `d` of the base
fibre. The generator coherence reduces to an arrow

$$
\bar\ell:D[\ell](d)\longrightarrow d.
$$

Contextual elimination then yields a dependent section

$$
\mathsf{ind}(D,d,\bar\ell):
\prod_{x:\,W}D[x].
$$

Take `D` constant as well, at a category `C`. Its transport is the
identity, so the data become an object `c:Obj(C)` and an endomorphism
$f:c\to c$. The resulting section is an ordinary functor

$$
\mathsf{rec}(C,c,f):W\longrightarrow C
$$

with the expected observations

$$
\mathsf{rec}(*)=c,
\qquad
\mathsf{rec}[\ell]=f.
$$

<!-- evidence:DHIT-DERIVED-ELIMINATORS -->

> **Formal status — checked.** Evidence `DHIT-DERIVED-ELIMINATORS`.
> `walking_end_ind_sec` and `walking_end_rec_func` are transparent
> specializations of the contextual eliminator, with checked base and loop
> observations.

This dependency is architecturally important. There is one semantic
elimination principle, not three unrelated black boxes. The derived views
retain the generic functor and transfor action, which is why a recursor-built
object such as `Code` can later be acted on at higher cells.

## 6.5 What “Computes” Means

A constructor computation can be visible in several ways:

1. a runtime reduction may expose the supplied constructor datum;
2. a typed equality may state that two stable observations agree;
3. a proof-time comparison may join expressions without selecting either as
   the runtime normal form.

For the walking eliminator, the contextual base projection and the displayed
generator cell are the constructor-specific runtime owners. Narrow
projections expose the same data through the derived section and recursor
views. Transparent equality theorems record those observations at their
readable types.

This distinction prevents a tempting but dangerous simplification. One
should not add a new constructor-specific rewrite merely because a theorem is
mathematically true. Generic functoriality already owns preservation of
identities, composition, and ordinary naturality. The HIT-specific rules own
only what observing the literal constructors must reveal.

The book will normally write a constructor equation with `=`. A formal
status note determines whether that equation is runtime computation,
propositional equality, or a mathematical development. This keeps the main
line readable without blurring the operational contract.

## 6.6 From A Pointwise Step To A Coherent Spiral

Chapter 8 requires more than the ordinary recursor. Its code family and based
representable family are both nonconstant:

$$
\mathsf{Code},\mathsf{Rep}_*:W\longrightarrow\mathsf{Cat}.
$$

At the base, natural-number powers give a carrier function

$$
n\longmapsto\ell^n.
$$

Because the source is the path category of Nat, equality action lifts this
function to a functor

$$
\mathsf{power}:\mathsf{Path}(\mathbb N)
  \longrightarrow\operatorname{Hom}_W(*,*).
$$

The contextual algebra still needs a transformation

$$
\mathsf{Rep}_*[\ell]\circ\mathsf{power}
\Longrightarrow
\mathsf{power}\circ\mathsf{Code}[\ell].
$$

Pointwise, the endpoints are $\ell\circ\ell^n$ and
$\ell^{n+1}$. Nat recursion makes them propositionally equal, but a
family of equalities is not by itself the required transformation into a
directed hom-category. The higher action and endpoint comparisons must be
assembled coherently.

Emdash does this through a restricted equality-local core inclusion and a
`PathLift` construction. Informally, `PathLift` turns a function
whose source carries equality paths into a functor with directed target. The
non-strict spiral inserts the necessary comparison before the lifted step;
ordinary path functoriality discharges the other side. Its readable component
has the forward direction

$$
\ell\circ\ell^n\longrightarrow\ell^{n+1}.
$$

<!-- evidence:WE-SPIRAL -->

> **Formal status — checked.** Evidence `WE-SPIRAL`. The selected
> `walking_power_spiral` is the explicit restricted-core-inclusion
> construction, and `walking_power_spiral_cell` exposes the directed
> component shown above.

The spiral is a small but representative lesson in functorial type theory.
Carrier equality supplies useful input, yet the consumer asks for a coherent
cell with functorial higher action. The bridge between the two must be an
explicit construction; it cannot be hidden by treating every directed hom as
an identity type.

## 6.7 The Derived Decoder Interface

Substituting

$$
R=\mathsf{Code},\qquad
D=\mathsf{Rep}_*,\qquad
u=\mathsf{power},\qquad
\sigma=\mathsf{spiral}
$$

into contextual elimination yields

$$
\mathsf{decode}^{d}:\mathsf{Code}\Longrightarrow\mathsf{Rep}_*.
$$

Its fibre component at `x` is a functor from codes over `x` to
based arrows ending at `x`; at the base it computes to the power
functor. Naturality of this single displayed functor is what later produces a
directed normalization cell for every opaque based arrow.

This is stronger than defining only a function
`Nat -> Hom_W(*,*)`. The latter supplies candidate normal forms but
contains no explanation of why an arbitrary arrow reaches its candidate. The
contextual eliminator supplies exactly that missing action.

## 6.8 Toward A General Directed-HIT Schema

The walking interface suggests a reusable architecture. A general schema
would need at least:

- a language of object, arrow, and higher-cell boundaries;
- generated recursion, dependent elimination, and contextual elimination;
- functorial action at every exposed cell level;
- a policy distinguishing computational constructor rules from
  propositional coherences;
- subject-reduction and overlap checks for the generated rules;
- algebra and morphism categories suitable for universal-property theorems;
- optional dimension or truncation constructors whose consequences are
  separately controlled.

Pushouts, quotients, directed intervals, and cell complexes would test
different parts of such a design. None follows merely by changing the name of
the walking generator.

<!-- evidence:DHIT-GENERAL-SCHEMA -->

> **Formal status — research boundary.** Evidence `DHIT-GENERAL-SCHEMA`.
> The active code implements the selected opaque WalkingEnd signature and its
> eliminator interfaces. It does not yet implement a generic signature
> compiler or arbitrary directed higher-inductive categories.

The selected example is nevertheless substantial enough to guide that future
work. It forces object action, arrow action, a genuine lax coherence cell,
higher functorial lifting, constructor computation, and an interaction with
finite categorical height. The next chapter develops the last item before we
use all of them together.
