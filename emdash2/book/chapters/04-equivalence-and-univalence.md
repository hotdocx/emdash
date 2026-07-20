<a id="chapter-4"></a>

# 4. Equivalence And Univalence

Univalence is often summarized by the phrase “equivalent things may be
identified.” In a directed setting, that sentence must be typed with care.
Equivalent *classifiers*, isomorphic objects of a 1-category, recursively
invertible arrows, and arbitrary functors are different notions. The theory
becomes clearer, not more cumbersome, when each receives its own interface.

The WalkingEnd example is the test. Its generator is a perfectly good arrow,
and `Code` sends it to a perfectly good functor, but neither is an
equivalence. At the same time, the final comparison between its endomorphism
carrier and Nat is a type equivalence. Univalent foundations must support both
statements without forcing one into the shape of the other.

<a id="chapter-4-1"></a>

## 4.1 Maps With Contractible Fibres

For a function `f:A -> B` and `b:B`, its homotopy fibre is

$$
\mathsf{fib}_f(b)
:=\sum_{a:A}(f(a)=b).
$$

The function is an equivalence when every such fibre is contractible. A
`TypeEquiv(A,B)` packages `f` with this evidence. The centre of the
fibre over `b` selects an inverse value `f^{-1}(b)`, and its path
component gives

$$
f(f^{-1}(b))=b.
$$

Contractibility of the fibre also yields the other law

$$
f^{-1}(f(a))=a.
$$

This definition has two advantages. It treats being an equivalence as a
property of a fixed map, and it supplies a canonical selected inverse from the
contractible-fibre evidence. Conversely, explicit inverse data with both
homotopies can be adjusted and converted into contractible-fibre evidence.
That is the route used by the WalkingEnd carrier comparison: `encode` and
`power` are built first, their two round trips are proved, and then the
equivalence package is formed.

<!-- evidence:EQUIV-TYPE -->

> **Formal status — checked.** Evidence `EQUIV-TYPE` covers homotopy
> fibres, the equivalence-map predicate, `TypeEquiv`, its selected
> inverse, and both inverse paths.

<a id="chapter-4-2"></a>

## 4.2 Algebra Of Type Equivalences

Equivalences have reflexivity, symmetry, and composition:

$$
\begin{aligned}
\mathsf{id}_A &: A\simeq A,\\
e^{-1} &: B\simeq A,\\
e_{BC}\circ e_{AB} &: A\simeq C.
\end{aligned}
$$

Composition is written in categorical order; the forward map of the last
line sends `a` first through `e_AB` and then through `e_BC`.
The inverse laws are constructed from explicit quasi-inverse data and the
path algebra of Chapter 1.

Not every mathematically true equation between equivalence packages is chosen
as a runtime eta rule. What computes is the public interface needed by
consumers: the selected forward map of reflexivity, symmetry, and composition,
together with designated projections of inverse data. Remaining coherence is
propositional. This is the same separation between computation and evidence
that we saw for Nat associativity.

<!-- evidence:EQUIV-TYPE-ALGEBRA -->

> **Formal status — checked.** Evidence `EQUIV-TYPE-ALGEBRA` covers
> reflexivity, symmetry, composition, and their selected forward-map
> computation.

<a id="chapter-4-3"></a>

## 4.3 Univalence In The Groupoid Universe

Every universe path `p:A=B` induces a type equivalence by transporting
elements:

$$
\mathsf{idtoequiv}(p):A\simeq B.
$$

Univalence supplies the converse in a coherent way. In the groupoid universe,
emdash has an operational decoder

$$
\mathsf{ua}(e):A=B
$$

and named round trips

$$
\mathsf{ua}(\mathsf{idtoequiv}(p))=p,
\qquad
\mathsf{idtoequiv}(\mathsf{ua}(e))=e.
$$

Transport along the decoded path agrees propositionally with the forward map
of `e`. The qualification “propositionally” is important. A single
operational decoder owns the comparison; the kernel does not turn every
universe transport expression into arbitrary equivalence application by a
broad rewrite.

This gives the groupoid/type layer its univalent reading: identity in the
universe and equivalence of decoded classifiers carry the same information
through the named interface. It does not say that a noninvertible arrow in an
arbitrary category is an identity.

<!-- evidence:UNIV-GROUPOID -->

> **Formal status — checked.** Evidence `UNIV-GROUPOID` covers the
> decoder-oriented groupoid-univalence equivalence, both round trips, and the
> selected transport agreement.

<a id="chapter-4-4"></a>

## 4.4 Universes With Retained Truncation Evidence

For each truncation level `n`, the theory also packages a classifier
together with evidence that it is `n`-truncated:

$$
\mathsf{TruncU}_n
:=\sum_{A:\mathsf{Grpd}}\mathsf{isTrunc}_n(A).
$$

The evidence is retained, not erased. Nevertheless, because truncation
evidence is proposition-valued, equality of packages is controlled by
equality of their carriers. Combining that fact with groupoid univalence gives
the restricted comparison

$$
(A,h_A)=(B,h_B)
\simeq
A\simeq B.
$$

The familiar universes of propositions, sets, and groupoids are the `-1`,
`0`, and `1` cases of this package. This is a concrete example of
structure identity: once a field is proposition-valued, identifying the
carrier supplies the dependent identification of that field.

<!-- evidence:UNIV-TRUNCATED -->

> **Formal status — checked.** Evidence `UNIV-TRUNCATED` covers the
> carrier-equivalence view of paths between packaged truncated classifiers and
> its named encode/decode laws. It is a restricted univalence theorem, not a
> truncation reflector.

<a id="chapter-4-5"></a>

## 4.5 Three Categorical Notions Of Invertibility

At the categorical layer we distinguish three interfaces.

An ordinary isomorphism between objects `x,y:C` consists of a forward
arrow, one inverse arrow, and equality-valued left and right inverse laws:

$$
f:x\to y,\qquad
g:y\to x,\qquad
g\circ f=\mathrm{id}_x,\qquad
f\circ g=\mathrm{id}_y.
$$

For a fixed arrow `f`, the native classifier
`OmegaEquivAlong(f)` carries recursively equality-valued inverse
evidence. Its selected left and right inverse arrows may be presented
separately, with their laws living in the next hom-categories. Finally,
`OmegaEquiv(C,x,y)` packages a chosen forward arrow together with such
evidence.

The distinction allows the interface to remain iterable. Inverse laws at one
dimension are equality data in a hom-category, where the same machinery can
act again. An ordinary isomorphism has a checked one-way lift into the native
omega-equivalence package, but the notions are not collapsed definitionally.

<!-- evidence:EQUIV-OMEGA -->
<!-- evidence:EQUIV-ORDINARY-ISO-LIFT -->

> **Formal status — checked.** Evidence `EQUIV-OMEGA` covers the
> fixed-arrow and packaged equality-valued interfaces and the transparent
> package built from an object path. Evidence
> `EQUIV-ORDINARY-ISO-LIFT` covers the one-way lift from ordinary
> isomorphism evidence.

For an object path `p:x=y`, path induction constructs a forward arrow,
an inverse, and both cancellation laws. Thus equality can be *reified* as a
computational equivalence package. A bare classifier-level cast may permit an
identity term to be used at the stable equivalence facade, but it does not
magically give that term the projections of a package; observable computation
uses the explicit construction.

The converse direction has a more delicate status. The current native surface
supports selected equality/equivalence casts and rigid universe boundaries,
but a full general equivalence between arbitrary object equality and ordinary
1-categorical isomorphism evidence is not a compatibility prerequisite and is
not claimed here.

<!-- evidence:UNIV-FULL-OBJECT-ISO -->

> **Formal status — research boundary.** Evidence
> `UNIV-FULL-OBJECT-ISO` records the intentionally absent two-sided
> ordinary-isomorphism/object-equality theorem. Its absence does not weaken the
> checked path-to-equivalence construction used elsewhere in the book.

<a id="chapter-4-6"></a>

## 4.6 Equivalence Evidence Is A Property

For a fixed arrow `f`, two complete choices of equality-valued inverse
evidence are equal. The proof does not erase the choices. It shows that the
left- and right-inverse fibres are contractible, using ordinary associativity,
unit laws, and the supplied inverse equations, and then transfers that
contractibility to the native record.

Consequently,

$$
\mathsf{OmegaEquivAlong}(f)
$$

is proposition-valued for every category and fixed arrow, without assuming
that the category has finite height or locally set-valued homs. This is the
categorical analogue of the fact that “is an equivalence” should be a property
of a map even though an explicit quasi-inverse package may contain choices.

<!-- evidence:EQUIV-EVIDENCE-PROP -->

> **Formal status — checked.** Evidence `EQUIV-EVIDENCE-PROP` is the
> dimension-independent property theorem for the native fixed-arrow evidence.

<a id="chapter-4-7"></a>

## 4.7 Hom Action And Groupoidal Sources

Equivalence evidence must itself act functorially if the foundation is to be
usable at higher dimension. The one-way derived hom-action layer sends
fixed-arrow omega-equivalence evidence through the next hom action of an
ordinary functor. In particular, if a category is coherently groupoidal, its
core inclusion is an omega-equivalence and each directed arrow can be related
to an object path through the selected homwise inverse.

For a directed family `D:C -> Cat`, coherent groupoidality of `C`
then implies that transport along a base arrow is an equivalence:

$$
D[f]:D[x]\simeq D[y].
$$

This recovers the familiar groupoidal behavior of path-indexed families as a
special case. It also states the boundary sharply: without groupoidality,
`D[f]` remains only a functor.

<!-- evidence:EQUIV-HOM-ACTION -->

> **Formal status — checked.** Evidence `EQUIV-HOM-ACTION` covers the
> one-way next-hom action and its specialization to equivalence of fibre
> transport over a coherently groupoidal source.

<a id="chapter-4-8"></a>

## 4.8 Why Successor Needs No Univalence In Chapter 8

The circle's universal cover sends an invertible loop to successor on the
integers. To define it as a universe-valued family, one first recognizes
successor as an equivalence and then uses univalence to obtain a universe
path.

The WalkingEnd code has a different type:

$$
\mathsf{Code}:W\longrightarrow\mathsf{Cat}.
$$

Its generator is a directed arrow in `W`, so its image need only be a
functor. Natural-number successor qualifies directly even though it misses
zero and has no inverse. Forcing univalence into this step would change the
mathematics by demanding reversibility where the signature deliberately has
none.

The carrier equivalence at the end of the proof is nevertheless genuinely a
type equivalence, and the surrounding universes retain their checked
univalence interfaces. The lesson is not that univalence disappears. It is
that univalence governs equivalence and identity, while directed functoriality
also governs noninvertible action.
