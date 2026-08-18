<a id="chapter-27"></a>

# 27. Free Inversion And Groupoidification

Chapter 26 calculated what happens when one directed endomorphism acquires an
inverse: natural powers expand to integer powers. But a universal construction
cannot be characterized by its elements alone. It must say what maps *out* of
the realized object are, how they vary, and why their restriction remembers
exactly the original directed data.

The relevant operation is **groupoidification**. Starting from a directed
category $C$, it produces a groupoidal classifier
$\mathsf{Groupoidify}(C)$ and a whole functor

$$
\eta_C:C\longrightarrow
\operatorname{Path}(\mathsf{Groupoidify}(C)).
\tag{27.1}
$$

The functor $\eta_C$ is the unit of free inversion. Its object action names
represented points; its arrow action turns a directed arrow into a path; its
iterated hom action carries represented higher cells; and its compositor
records how images of composable arrows compare with the image of their
composite.

The universal property is tested against a groupoidal target $G$. A map
$h:\mathsf{Groupoidify}(C)\to G$ restricts along (27.1) to a path-valued
functor on $C$. Conversely, any
$F:C\to\operatorname{Path}(G)$ extends to a map from the groupoidification.
The checked theorem says that restriction and extension are inverse at the
level of whole mapping categories:

$$
\operatorname{Map}_{\mathsf{Grpd}}
  (\mathsf{Groupoidify}(C),G)
\simeq_{\omega}
\operatorname{Fun}
  (C,\operatorname{Path}(G)).
\tag{27.2}
$$

Before studying the arbitrary category $C$, we will derive (27.2) twice for
finite shapes. The walking endomorphism tests inverse powers at one point.
The walking arrow tests a generator whose endpoints differ. Together they
show why the general constructor must be a whole functor rather than a set of
objects followed by an unrelated graph of arrows.

There are two complementary ways to recognize a free object. A constructor
presentation says how its points and paths are generated and how its
eliminator computes. A mapping property says that every interpretation of the
generators extends, and that the extension is unique. Either view alone can
hide an error. Constructors without uniqueness may admit unintended extra
maps; an opaque equivalence of mapping carriers may assert the right answer
without explaining how the generators compute. The constructions below keep
both: point and dependent-cell beta rules on one side, whole beta/eta
uniqueness on the other.

The word *whole* also changes the level of the claim. We are not merely
counting functions in and out. The left and right sides of (27.2) are
categories with homs, higher homs, and internal action. Restriction and
extension act on those levels before they are packaged as an equivalence.
This is what makes groupoidification reusable in later mathematics: a proof
between representations is itself transported across the universal property.

## 27.1 The One-Point Test: WalkingEnd And Circle

There is a canonical functor

$$
w:\mathsf{WalkingEnd}\longrightarrow\mathsf{Circle}_{\mathrm{cat}}
\tag{27.3}
$$

sending the unique point to $\mathsf{base}$ and the directed generator to
$\mathsf{loop}$. Its action on the $n$th directed power is the $n$th positive
Circle power. Following this action by the Circle encoder gives the canonical
inclusion of natural numbers into the localized Integer line:

$$
\operatorname{encode}\bigl(w(\mathsf{gen}^{n})\bigr)=[0,n].
\tag{27.4}
$$

The comparison is retained not only for each $n$ but as equality of the two
whole carrier functions from WalkingEnd based arrows to Integer: map through
the Circle and encode, or normalize to a natural number and include it. This
is the arithmetic shadow of free inversion.

Now let $G$ be any groupoidal target. Precomposition with $w$ restricts a
function $h:\mathsf{Circle}\to G$ to a functor

$$
R_G(h):\mathsf{WalkingEnd}\longrightarrow\operatorname{Path}(G).
\tag{27.5}
$$

Because restriction itself is a whole functor, it also acts on equalities
between Circle functions and on their higher equalities. Evaluating its whole
comparison at the walking point returns $h(\mathsf{base})$. Its generator
observation is naturally dependent: the endpoint of the loop changes when
the whole functor changes, so the comparison is a path-over whose target is
$\operatorname{ap}_h(\mathsf{loop})$.

The inverse construction reads a path-valued WalkingEnd representation $F$.
It extracts the image of the walking point and the image path of the
generator, then applies Circle recursion:

$$
E_G(F)(x):=
\mathsf{circle\_rec}
  \bigl(G,F(\mathsf{pt}),F(\mathsf{gen}),x\bigr).
\tag{27.6}
$$

The object action in (27.6) is only the first layer. The extension varies as a
whole functor in $F$. A transformation between two representations in
$\operatorname{Path}(G)$ is pointwise equality-valued, hence pointwise
invertible. The whole univalence machinery turns it into a path of
representations, and applying (27.6) gives the corresponding path of Circle
functions. One more hom action remains available after that step.

The categorical-HIT uniqueness clauses state

$$
R_G E_G=\operatorname{id},
\qquad
E_G R_G=\operatorname{id}
\tag{27.7}
$$

as paths between whole functors. Their projections recover the expected base
and generator equations, but the whole statements are stronger: they also
control transformations and higher action. Thus

$$
\operatorname{Map}_{\mathsf{Grpd}}(\mathsf{Circle},G)
\simeq_{\omega}
\operatorname{Fun}
  (\mathsf{WalkingEnd},\operatorname{Path}(G)).
\tag{27.8}
$$

It is important that (27.8) holds for every groupoidal $G$, not only for the
Circle itself or for the Integer classifier used in Chapter 26. A
path-valued WalkingEnd representation in $G$ consists of an object $a:G$ and
a loop $p:a=a$, together with the functorial action inherited from the source.
Circle recursion turns exactly this pair into a function from the Circle.
Conversely, evaluation at the base and action on the loop recover the pair.
The whole theorem says there is no additional choice hidden at
transformations or higher paths.

The one-point result also illustrates why free inversion differs from merely
adding a formal inverse symbol. Once $p^{-1}$ exists in $G$, all negative
powers and their cancellation laws are already determined by equality. The
extension does not ask the representation to supply an independent image for
every negative word. This economy is the universal content behind the
arithmetic passage from natural to integer powers.

<!-- evidence:WE-GROUP-COMPLETION -->

> **Formal status — checked.** Evidence `WE-GROUP-COMPLETION`. The functor
> (27.3) sends every directed natural power to the corresponding positive
> Circle power. For every groupoidal $G$, whole restriction and whole Circle
> extension give the fixed-forward equivalence (27.8), with beta/eta,
> dependent generator projections, and retained higher action. This theorem
> is the free inversion of one source shape, not by itself the generic
> category-indexed construction.

## 27.2 The Two-Endpoint Test: WalkingArrow And Interval

One point can conceal an important issue: every generator in WalkingEnd is an
endomorphism. A generic directed arrow has a source and target that need not
coincide. The next source shape is therefore

$$
\mathsf{src}\xrightarrow{\mathsf{edge}}\mathsf{tgt},
\tag{27.9}
$$

the walking arrow. It is not an ad hoc three-field record. It is obtained from
the join of two terminal categories, and its generator is a projection of the
whole cross action. Consequently the source already retains a next hom action
beyond the displayed edge.

Its groupoidal counterpart is the interval HIT:

$$
\mathsf{Interval}:\mathcal U,
\qquad
i_0,i_1:\mathsf{Interval},
\qquad
\mathsf{seg}:i_0=i_1.
\tag{27.10}
$$

For a family $D:\mathsf{Interval}\to\mathcal U$, the eliminator takes
$b_0:D(i_0)$, $b_1:D(i_1)$, and a dependent path over
$\mathsf{seg}$. It computes judgmentally at both endpoints and at the
canonical dependent action on the segment. As for the Circle, the ordinary
constant-family `ap` equation is retained propositionally rather than
installed as a second runtime normal form.

The comparison functor

$$
j:\mathsf{WalkingArrow}\longrightarrow
\operatorname{Path}(\mathsf{Interval})
\tag{27.11}
$$

sends source to $i_0$, target to $i_1$, and edge to $\mathsf{seg}$. For any
groupoidal $G$, restricting along $j$ records the two endpoint values of an
Interval function and its action on the segment. Extension uses Interval
recursion on exactly those three pieces. The whole beta/eta paths give

$$
\operatorname{Map}_{\mathsf{Grpd}}(\mathsf{Interval},G)
\simeq_{\omega}
\operatorname{Fun}
  (\mathsf{WalkingArrow},\operatorname{Path}(G)).
\tag{27.12}
$$

The right side of (27.12) has a particularly direct reading. A functor from
the walking arrow chooses two objects $a_0,a_1:G$ and one path
$p:a_0=a_1$. A transformation between two such functors chooses endpoint
components compatible with that path, and its next action records equality of
such compatibility data. The left side organizes the same information as a
whole function on the Interval. Thus the equivalence tests not just two-point
recursion but the dependent geometry of the segment.

This is where an underlying-graph construction would first become visibly
insufficient. It could remember a source vertex, target vertex, and edge, but
it would have to recover from elsewhere how transformations act at both
endpoints and over the edge. In the present construction those observations
are projections of whole functor paths. Endpoint variation is not metadata
attached after the free groupoid has been formed.

Equation (27.12) is stronger evidence for the intended operation than the
observation that the interval is contractible. Contractibility describes the
homotopy type after it has been formed. The mapping theorem says why its two
points and one path are freely generated by a directed arrow. It also tests
the endpoint transport that an endomorphism-only theorem cannot see.

<!-- evidence:WALKING-INTERVAL-GROUPOIDIFICATION -->

> **Formal status — checked.** Evidence
> `WALKING-INTERVAL-GROUPOIDIFICATION`. The interval has judgmental endpoint
> and dependent-segment computation. Restriction and extension are inverse as
> whole functors for every groupoidal target, with separate endpoint and
> generator projections and retained next action. The two endpoints remain
> genuinely distinct in the tested interface.

## 27.3 One Whole Constructor For An Arbitrary Category

The two examples suggest what the generic signature must retain. For every
category $C$, there is a primitive groupoidal HIT
$\mathsf{Groupoidify}(C)$ and the whole unit (27.1). The constructor is not
split into a point constructor for every object, a path constructor for every
arrow, and an external list of coherence constructors. Those observations
are projections of one iterable functor.

At the first two levels, the unit reads

$$
\begin{aligned}
x\in\operatorname{Obj}(C)
&\longmapsto \eta_C(x):\mathsf{Groupoidify}(C),\\
f:x\to y
&\longmapsto
  \eta_C(f):\eta_C(x)=\eta_C(y).
\end{aligned}
\tag{27.13}
$$

Reapplying the generic hom action exposes the image of a source 2-cell, and
the process continues at represented higher levels. The use of the word
“category-indexed” refers to this complete source $C$; it does not mean that
only the object set of $C$ is retained.

This arrangement should be read as an indexed HIT signature. Formation is
primitive at the groupoidal level; the whole unit is its constructor owner;
and recursion supplies elimination. The theory does not pretend to construct
the carrier by taking an external quotient of strings of arrows. Such a
quotient would immediately face choices of word representation,
normalization, and higher coherence. Instead, the computational interface
specifies what represented cells do, while the mapping theorem specifies
their universal uniqueness.

Nor does one need a primitive symbol named
$\mathsf{Groupoidify}_n$ at every dimension. The first hom action of
$\eta_C$ already turns source arrows into paths. Its next hom action handles
arrows between arrows, and iteration continues through the ordinary
categorical classifiers. This is the same compression principle used
throughout the book: internalization plus iteration replaces an indefinitely
growing external declaration schema.

Given $F:C\to\operatorname{Path}(G)$, the recursor produces

$$
\operatorname{rec}_F:
\mathsf{Groupoidify}(C)\longrightarrow G.
\tag{27.14}
$$

It computes judgmentally on every represented source object, and its
canonical dependent action on every represented source arrow computes to the
corresponding arrow of $F$ embedded in the constant motive:

$$
\begin{aligned}
\operatorname{rec}_F(\eta_C(x))
  &\equiv F(x),\\
\operatorname{apd}(\operatorname{rec}_F,\eta_C(f))
  &\equiv \operatorname{constPathOver}(F(f)).
\end{aligned}
\tag{27.15}
$$

Arbitrary points and arbitrary paths of the groupoidification do not match
these constructor reductions. The rules compute because the inputs are
manifestly represented by the whole unit.

The recursor is itself organized as a whole extension functor

$$
E_{C,G}:
\operatorname{Fun}(C,\operatorname{Path}(G))
\longrightarrow
\operatorname{Map}_{\mathsf{Grpd}}
  (\mathsf{Groupoidify}(C),G).
\tag{27.16}
$$

Its object action is (27.14), its first hom action maps transformations of
representations to equalities of recursor functions, and a next action is
retained. This target-varying mapping object is the computational eliminator
needed by the universal property; a bare function for each individual $F$
would not express how extension behaves on proofs between representations.

The requirement that $G$ be groupoidal is doing real work. Each directed
arrow $F(f)$ lands in a path category and is therefore invertible, so the
recursor may interpret the inverse motion freely added to the source. If the
target were an arbitrary directed category, a chosen image of $f$ would not
in general determine an image for its formal inverse. The right side of
(27.16) is consequently not the ordinary category of all directed functors
$C\to G$; it is the category of functors into the path realization of a
groupoidal target.

At the same time, nothing forces the original arrows of $C$ to have been
invertible. The unit accepts all of them. Groupoidification changes their
ambient interpretation rather than filtering the source. This is precisely
the opposite of taking the core.

## 27.4 Composition Is Represented, Not Forgotten

Suppose $f:x\to y$ and $g:y\to z$ are composable arrows in $C$. Since
$\eta_C$ is a whole functor, its internal action supplies a compositor

$$
\phi_{g,f}:
\eta_C(g)\cdot\eta_C(f)
\Longrightarrow
\eta_C(g\circ f).
\tag{27.17}
$$

The codomain of the unit is a path category. Therefore the directed
compositor is realized as an equality between paths and is invertible by
symmetry, exactly as in Chapter 25. It is nevertheless an explicit cell: it
is not definitionally collapsed to an identity term. Its whole transformation
form retains a next hom action.

This observation explains why the construction begins with $C$, not with its
underlying graph. A graph-level free groupoid would create inverse paths for
edges but would then need composition, identities, and every represented
higher relation reintroduced by hand. The unit functor already knows those
relations. The recursor computation in (27.15) says that a path-valued
representation consumes them using its own whole action.

Identity and composition are therefore not quotient equations checked after
paths have been created. They are visible through functorial action. At an
identity arrow the selected unit profile supplies the appropriate unit
behaviour. At a composite, (27.17) compares the composite of the two image
paths with the image of the source composite. A representation $F$ carries
the corresponding compositor, so extending $F$ respects the same boundary.
The generic theorem is sensitive to the categorical structure of $C$, not
only to its collection of arrows.

In a strict specialization the two endpoints displayed in (27.17) may become
convertible. That does not make the compositor term itself an identity, and
the active negative check confirms it is not collapsed to one. This is useful
for eventual migration away from historical global strict endpoint cuts: the
coherence witness and its next action are already present rather than having
to be reconstructed from an equation that erased them.

Nor is an infinite record of associators and higher laws added beside the
unit. The compositor in (27.17) is projected from the same internal-action
calculus used for ordinary and displayed functors. Its next action provides
the first higher observation. This does not amount to a completed independent
metatheory of all weak $\omega$-groupoids, but it demonstrates that free
inversion has not discarded composition or capped coherence at arrows.

## 27.5 The Generic Mapping Theorem

Restriction is obtained by applying the path-category action to a map
$h:\mathsf{Groupoidify}(C)\to G$ and precomposing with $\eta_C$:

$$
R_{C,G}(h)=\operatorname{Path}(h)\circ\eta_C.
\tag{27.18}
$$

Like extension, $R_{C,G}$ is a whole functor. The categorical-HIT beta and
eta clauses are whole paths

$$
R_{C,G}E_{C,G}=\operatorname{id},
\qquad
E_{C,G}R_{C,G}=\operatorname{id}.
\tag{27.19}
$$

The first says that extending a complete path-valued representation and then
observing it on every represented source cell returns the original
representation. The second is uniqueness: a groupoidal map is determined by
its restriction to the generating whole functor. Projecting (27.19) gives
pointwise equalities, but the statements themselves compare endofunctors of
mapping categories.

Packaging restriction as the selected forward direction and extension as its
inverse gives the promised arbitrary-source theorem:

$$
R_{C,G}:
\operatorname{Map}_{\mathsf{Grpd}}
  (\mathsf{Groupoidify}(C),G)
\simeq_{\omega}
\operatorname{Fun}(C,\operatorname{Path}(G)).
\tag{27.20}
$$

<!-- evidence:GENERIC-GROUPOIDIFICATION-MAPPING -->

> **Formal status — checked.** **Theorem 27.1 (generic free inversion at the
> fixed-forward boundary).** Evidence `GENERIC-GROUPOIDIFICATION-MAPPING`.
> Formation, whole unit, point and dependent first-cell computation, whole
> target extension/restriction, beta/eta, explicit compositor, and retained
> next actions are active for arbitrary $C$ and groupoidal $G$. The theorem is
> a fixed-forward `OmegaEquivAlong` of mapping categories. Source action,
> `Groupoidify_func`, and the packaged adjunction remain outside this boundary.

The adjective *fixed-forward* records real data, not a weakness in the
equivalence. The forward functor in (27.20) is specifically restriction along
$\eta_C$; it is not merely some equivalence between carriers. What remains
unbuilt is variation in the source category $C$ itself.

Equation (27.20) is also more than an objectwise recursor theorem. Its left
side contains maps $\mathsf{Groupoidify}(C)\to G$ as objects and equality
action between them as homs. Its right side contains whole path-valued
functors and their transformations. The extension functor transports those
transformations to equalities of recursive maps; restriction transports
equalities of maps back to transformations. The beta and eta paths compare
the resulting whole endofunctors, not only their values at one selected
representation.

This strength is why the remaining qualification must be phrased carefully.
Formation depends on any supplied category $C$, and the theorem quantifies
over arbitrary $C$ and $G$. Nothing here is restricted to the objects of a
single category. The missing operation is instead *functorial dependence on
$C$*: given a functor between two source categories, the current public
interface has not yet packaged its induced groupoidal map and higher action
as one functor on the category universe.

This distinction between quantification and functorial packaging recurs
throughout category theory. A theorem may be uniform in an arbitrary
parameter before the parameter has been made the object action of an internal
functor. Here the formula for source action is already visible, but its
identity, composition, and higher observations have not yet been promoted.
Keeping those stages separate lets (27.20) be used now without pretending
that its future naturality proofs have already computed.

The target side, by contrast, is complete at the mapping-object boundary
needed here. For each groupoidal $G$, extension and restriction are whole
functors between the displayed mapping categories, and their inverse laws are
whole paths. The chapter can therefore compare concrete target presentations
and transport higher evidence even while source functoriality remains a
later construction.

## 27.6 Recovering The Interval From The Generic Theorem

The generic construction and the concrete interval were formed independently,
so their comparison is a useful recovery test. Specialize
$\mathsf{Groupoidify}$ to $\mathsf{WalkingArrow}$. Extending the concrete unit
(27.11) through the generic recursor gives

$$
u:\mathsf{Groupoidify}(\mathsf{WalkingArrow})
\longrightarrow\mathsf{Interval}.
\tag{27.21}
$$

In the other direction, extend the generic unit through the concrete Interval
recursor:

$$
v:\mathsf{Interval}
\longrightarrow\mathsf{Groupoidify}(\mathsf{WalkingArrow}).
\tag{27.22}
$$

The generic beta/eta laws and the Interval beta/eta laws identify the
restrictions of the two composites with the relevant identity
representations. Their whole uniqueness clauses then give

$$
v\circ u=\operatorname{id},
\qquad
u\circ v=\operatorname{id}.
\tag{27.23}
$$

Hence

$$
\mathsf{Groupoidify}(\mathsf{WalkingArrow})
\simeq\mathsf{Interval}.
\tag{27.24}
$$

<!-- evidence:GROUPOIDIFICATION-INTERVAL-RECOVERY -->

> **Formal status — checked.** Evidence
> `GROUPOIDIFICATION-INTERVAL-RECOVERY`. The maps (27.21) and (27.22) are
> selected by the two whole extension owners; both composites have whole and
> pointwise cancellation paths; and the result is packaged as a `TypeEquiv`.
> The two HIT classifier heads remain non-convertible.

The lack of a definitional identification is desirable. The concrete
Interval offers a compact two-endpoint eliminator. The generic object records
that it arose by applying one operation to a source category. Equivalence
shows that the presentations have the same groupoidal content without
forcing every calculation to unfold through the same syntax.

The comparison illustrates a general method for relating independently useful
HIT presentations. Map each presentation into the other by the appropriate
recursor. Do not try to compare raw constructors syntactically. Instead,
restrict each composite to the generating whole representation and use the
two uniqueness principles to identify it with the identity. This method
preserves the computational advantages of each presentation while producing
an explicit equivalence that later proofs can transport across.

It also validates the generic construction against the feature that motivated
the Interval: distinct endpoints. The recovered equivalence could not pass
the endpoint and segment projections if the generic unit had silently reduced
the source to one-object endomorphism data. WalkingEnd/Circle and
WalkingArrow/Interval are therefore complementary regression theorems, not
two decorative examples of the same calculation.

## 27.7 Three Operations With Different Directions

Groupoidification sits near two other operations used in the book. Their
similar notation can obscure opposite universal roles:

$$
\begin{array}{c|c|c}
\text{operation}&\text{effect}&\text{characteristic map}\\ \hline
\operatorname{Core}(C)&
  \text{retain invertibles}&
  \iota_C:\operatorname{Path}(\operatorname{Core}C)\to C\\
\|A\|_n&
  \text{forget above }n&
  |-|_n:A\to\|A\|_n\\
\mathsf{Groupoidify}(C)&
  \text{freely invert}&
  \eta_C:C\to\operatorname{Path}(\mathsf{Groupoidify}C).
\end{array}
\tag{27.25}
$$

The core deletes noninvertible motion and keeps what was already reversible.
Truncation preserves the groupoidal direction but forgets homotopy above a
chosen level. Groupoidification keeps every represented directed arrow and
adds inverse motion coherently. Applying truncation after groupoidification
is meaningful; identifying the two operations would lose the order of those
steps. The table suppresses only information already stated in prose: the
inputs to Core and Groupoidify are directed categories, while the input to
truncation is groupoidal.

Their mapping directions make the distinction even sharper. A map from a
groupoidification into $G$ is classified by a path-valued representation of
the original directed category. A map from an $n$-truncation into an
$n$-truncated target is classified by a map from the original groupoidal
type. The core instead supplies a groupoidal object mapping into the original
category by retaining already-invertible arrows. These point in reflective,
truncating, and core-inclusion directions respectively; substituting one for
another would reverse which information is freely added and which is
discarded. The present statement concerns those maps and mapping properties,
not a packaged three-adjunction chain.

There is one final boundary. A functor $H:C\to D$ should induce a map
$\mathsf{Groupoidify}(C)\to\mathsf{Groupoidify}(D)$ by extending the composite
$\eta_D\circ H$. Identity and composition paths should then follow from
whole uniqueness. That construction is the planned source action. Until its
higher action has been checked, there is no public whole functor

$$
\mathsf{Groupoidify}_{\mathrm{fun}}:
\mathsf{Cat}\longrightarrow\mathsf{Grpd}
\tag{27.26}
$$

and therefore no packaged adjunction with the path-category functor. The
mapping theorem (27.20) is already valid for every fixed $C$ and $G$; it
should not be weakened to “object-only.” But neither should that family of
theorems be renamed a completed functorial left adjoint before source action,
unit/counit observations, and triangle laws are assembled.

The proposed source action has a canonical formula, so the deferral is not a
lack of mathematical direction. Given $H:C\to D$, extend
$\eta_D\circ H$ across $\mathsf{Groupoidify}(C)$. Whole uniqueness should
then prove identity and composition laws and supply higher action. What
remains is to carry out that construction at the same computational standard
as (27.15)–(27.20), rather than postulating a functor and an adjunction record
whose fields merely restate the desired answer.

The next chapter turns from inversion to interchange. Here the unit compositor
is invertible because it lands in a path category; in a genuinely directed
two-dimensional target it need not be. The Gray direction asks how that
noninvertible cell is projected from the same whole internal action.
