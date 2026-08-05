<a id="chapter-21"></a>

# 21. Commutative Algebra By Universal Property

Algebraic geometry begins with rings, but it rarely cares how a ring was
manufactured. A polynomial algebra may be presented by finite expressions; a
localization may be presented by fractions; a quotient may be presented by
equivalence classes. These descriptions are indispensable for hand
calculation. They are not, however, the invariant meaning of the objects they
describe. Change the representation and the same algebra survives.

This matters acutely in a computational foundation. A convenient syntax can
make examples reduce, yet it can also make every later construction depend on
accidental choices of normal form. Conversely, a universal property can be
stated so weakly that it says merely that a map exists, leaving no usable
factor and no uniqueness with which to compare two constructions. The middle
course taken here is to make the universal property itself data of the
theory. The space of admissible factors is not merely inhabited: it is
contractible. It therefore has a selected center and a path from every
competitor to that center.

That principle gives a representation-free but still computational account
of the algebra needed by the geometry ahead. Commutative rings have
set-valued carriers and structured maps. Finite unit-ideal certificates carry
the algebraic content of basic-open covers. Polynomial algebras are free
extensions, and localizations are initial ways of making a chosen element
invertible. Unit, zero, and idempotent localizations then show that the
interface is not empty formalism. Finally, uniqueness alone constructs the
comparison between localization at a product and localization in two stages.

## 21.1 Rings As Structured Set-Carriers

A commutative ring $R$ consists first of a set $|R|$, with operations

$$
0_R,1_R:|R|,
\qquad
+_R,\cdot_R:|R|\times |R|\longrightarrow |R|,
\qquad
-_R:|R|\longrightarrow |R|,
$$

and then the usual associativity, commutativity, unit, inverse, and
distributivity laws. Calling the carrier a set is not decorative. It says
that equality proofs between ring elements carry no higher ambiguity. The
algebraic laws are consequently properties of the selected operations rather
than new layers of structure that can vary above a fixed equality.

The definition does **not** require $0_R\ne1_R$. This convention retains the
zero ring, whose carrier has one element and whose two distinguished constants
coincide. Excluding it would make some later universal statements awkward or
false. Localization at zero, for example, naturally lands in the zero ring:
forcing zero to be a unit forces every element to coincide.

A map $h:R\to S$ is more than a function of carriers. It comes with the five
preservation laws

$$
h(0)=0,
\quad h(1)=1,
\quad h(x+y)=h(x)+h(y),
\quad h(-x)=-h(x),
\quad h(xy)=h(x)h(y).
$$

Because the target carrier is a set, this preservation evidence is
proposition-valued. Two structured maps are equal once their carrier
functions agree pointwise. Identities and composites again preserve all five
operations, so commutative rings and their structured maps form a
one-category, written $\mathbf{CRing}$.

This choice of morphism is part of the mathematics. A bare function between
carriers forgets the equations that make substitution legitimate. A
structured map carries those equations once, after which every derived finite
sum, product, unit witness, and factorization can be transported through it.
Later base-change arguments therefore do not reopen the ring laws term by
term. They use the fact that the arrow already lives in $\mathbf{CRing}$.

Sethood plays a second role here. A structured map contains both a function
and proofs that it respects the operations. If those proofs carried
independent higher data, pointwise equality of the functions would not settle
equality of the complete maps. Since equality in the target ring is
proposition-valued, preservation proofs create no such ambiguity. This is why
the ordinary-looking extensionality principle is available without flattening
the ambient functorial type theory.

There is a useful restraint here. Extensionality for maps is not a global
principle saying that any two ring packages with equivalent carriers are
equal. No structure identity principle for arbitrary rings is being smuggled
in. The objects remain chosen carrier-operation-law packages; the homs have
the extensionality required to calculate with them.

<!-- evidence:COMM-RING-STRUCTURED-CATEGORY -->

> **Formal status — checked.** Evidence
> `COMM-RING-STRUCTURED-CATEGORY`. The active algebra packages a set-valued
> carrier, operations, and ring laws; admits the zero ring; packages
> operation-preserving carrier functions as structured maps; proves their
> extensionality; and assembles them into the one-category
> $\mathbf{CRing}$. No inequality $0\ne1$, global equality of ring packages,
> or general structure identity theorem is assumed.

Several small models keep this abstraction honest. The zero ring computes on
the one-point carrier. The two-element ring $\mathbb F_2$ computes on the
booleans, with exclusive-or as addition and conjunction as multiplication.
If $R$ and $S$ are rings, their cartesian carrier $|R|\times|S|$ has
componentwise operations and hence a ring structure $R\times S$. A pair of
maps induces a componentwise map between such products, and these maps obey
whole identity and composition paths.

This last construction should not be overread. We have constructed a product
ring and functorial action on paired maps. We have not yet selected projections
and proved the entire categorical product universal property inside
$\mathbf{CRing}$. The componentwise model is exactly what the later
split-idempotent calculation needs, and no stronger theorem is required for
that calculation.

## 21.2 Finite Certificates For Covering

The first geometric-looking datum is still entirely algebraic. Let
$f_1,\ldots,f_n$ be elements of a ring $R$. They are **unimodular** when one
retains coefficients $a_1,\ldots,a_n$ and an equality

$$
a_1f_1+\cdots+a_nf_n=1.
\tag{21.1}
$$

The coefficients are important. The bare proposition that the $f_i$ generate
the unit ideal forgets how that fact was witnessed. Equation (21.1), by
contrast, is finite input that can be transported, inspected, and used in a
construction. The family together with its coefficients and equality is a
**unimodular presentation**.

For two generators the picture is especially sharp. From $af+bg=1$, any map
out of $R$ that makes both $f$ and $g$ vanish would also make $1$ vanish.
Unless the target has collapsed to the zero ring, that is impossible.
Geometrically, no nontrivial affine point can lie outside both regions of
invertibility at once. The equation is already the finite algebraic shadow of
a covering statement, even though the regions and their topology remain to
be constructed.

Every ring map $h:R\to S$ transports such a presentation. Preservation of
finite sums and products turns (21.1) into

$$
h(a_1)h(f_1)+\cdots+h(a_n)h(f_n)=1
$$

in $S$. Thus a certificate does not merely remain true after base change; its
chosen witnesses move pointwise with the generators. The singleton family
$[1]$ has the canonical certificate $1\cdot1=1$, and a two-element helper
packages the familiar equation $af+bg=1$.

Why call this cover data? In ordinary affine geometry, (21.1) says that the
basic opens $D(f_i)$ cover the whole spectrum. But that geometric conclusion
uses meanings that have not yet been introduced in this spiral: a spectrum,
basic opens, a topology, and the relationship between unit-ideal generation
and coverage. The present layer records precisely the algebraic premise from
which those notions will be built. It does not call a finite family a cover by
fiat.

There is a second reason to retain the presentation rather than immediately
truncate it to a proposition. Different coefficient families may witness the
same unit-ideal equation. The classifier of presentations is set-valued, not
claimed proposition-valued. Later invariant constructions may forget that
choice; earlier computational constructions are allowed to consume it. This
separation between witness-rich input and invariant output is the same
pattern used for generated topologies in Chapter 19.

<!-- evidence:FINITE-UNIMODULAR-COVER-DATA -->

> **Formal status — checked algebraic boundary.** Evidence
> `FINITE-UNIMODULAR-COVER-DATA`. Finite sums and dot products compute on
> visible families, structured ring maps preserve them, and a finite Zariski
> presentation retains generators, coefficients, and their unit-ideal law.
> Such presentations are stable under structured base change and include the
> singleton $[1]$ and binary $af+bg=1$ cases. At this layer they are not yet
> basic opens, covering sieves, localization families, or a Grothendieck
> topology.

## 21.3 Free Variables Without A Syntax Of Polynomials

Fix a ring $R$ and a set or groupoid $X$ of variable names. A polynomial
algebra on $X$ should contain a base map

$$
\iota:R\longrightarrow P
$$

and a valuation $v:X\to |P|$. Its meaning is determined by what happens when
the variables are interpreted elsewhere. Given a ring $S$, a base map
$h:R\to S$, and a valuation $u:X\to|S|$, consider structured maps
$k:P\to S$ satisfying

$$
k\circ\iota=h,
\qquad
k(v(x))=u(x)\quad(x:X).
\tag{21.2}
$$

Both equations are retained pointwise, and the complete factor consists of
$k$ together with those agreements. The universal property says that the
classifier of such factors is contractible for every $S$, $h$, and $u$.
There is therefore one coherently selected extension, and every rival
extension is equal to it as a structured map with its agreement evidence.

Contractibility is stronger than the phrase “there exists a unique map” when
that phrase is read externally. It gives a center of the complete factor
classifier and, internally, a path from every other inhabitant to that
center. The center can be projected whenever an actual extension is needed;
the contraction can be invoked whenever two independently constructed
extensions must agree. Because the classifier retains the equations in
(21.2), uniqueness does not forget that the comparison lies over $R$ and has
the prescribed values on variables.

This is the familiar freeness of $R[X]$, but it does not select a
representation of its elements. There is no list of monomials, finitely
supported coefficient function, inductive expression grammar, quotient by
the ring laws, or preferred normalization order. Those are possible models
of the universal property, not fields of the property itself.

The omission is not hostility to syntax. A concrete evaluator might sensibly
represent a polynomial by normalized coefficient data, and a parser might let
a reader write $x^2+2x+1$. What matters is the direction of dependence. Such
a representation should prove that it satisfies (21.2); the geometry should
then consume the universal property. The later theory is insulated from
whether one implementation uses Horner forms, sparse monomials, or an
external computer-algebra package.

For a single variable $t$, this says that a map out of a supplied $R[t]$ is
determined by two observations: what it does to coefficients and where it
sends $t$. Familiar evaluation is recovered by choosing the target value of
$t$. For many variables the same sentence is indexed by $X$, with no need to
choose an ordering at the universal boundary. The interface states exactly
what symbolic substitution is meant to accomplish while declining to
legislate how symbols are stored.

There is already a closed sanity check. When $X$ is empty, there is no variable
data to choose. The ring $R$ itself, with the identity base map, satisfies the
polynomial universal property: every $h:R\to S$ is its own unique extension.
This case exercises the complete factor classifier and its contractibility,
not merely the formation of a record.

**Theorem 21.1 (universal polynomial extension).** A supplied polynomial
algebra package on $(R,X)$ classifies extensions of every base map and
valuation by a contractible factor space. For the empty variable classifier,
the identity extension on $R$ supplies a checked model.

<!-- evidence:COMM-RING-POLYNOMIAL-UNIVERSALITY -->

> **Formal status — checked interface and closed model.** Evidence
> `COMM-RING-POLYNOMIAL-UNIVERSALITY`. The active universal property retains
> base and variable agreements and proves the complete extension space
> contractible. The empty-variable identity model is checked. No construction
> of a polynomial algebra for every $R$ and $X$, concrete monomial syntax,
> quotient presentation, normalization theorem, runtime rule, or package
> uniqueness theorem is claimed.

## 21.4 Making One Element Invertible

Let $f\in R$. A localization of $R$ at $f$ begins with a ring $L$ and a map

$$
\ell:R\longrightarrow L
$$

for which $\ell(f)$ is a unit. Unit evidence is explicit: it consists of an
inverse $y$ and an equality $\ell(f)y=1$. Commutativity proves that the inverse
is unique, and sethood of the carrier proves that the entire evidence is a
proposition. Asking for a unit therefore does not introduce a meaningful
choice of inverse into the geometry.

The uniqueness calculation is elementary but instructive. If $y$ and $z$ are
both inverses to $x$, then

$$
y=y\cdot1=y(xz)=(yx)z=(xy)z=1\cdot z=z.
$$

Associativity and commutativity do the algebraic work; sethood then says that
the displayed equality has no further choices. The predicate “$x$ is
invertible” may consequently be used as the fibre of an ordinary sieve, as in
Chapter 18, rather than as a higher coefficient carrying distinct inverse
witnesses.

The universal property considers any map $h:R\to S$ for which $h(f)$ is a
unit. A factor is a structured map $k:L\to S$ together with the pointwise
triangle

$$
k(\ell(x))=h(x)\qquad(x\in R).
\tag{21.3}
$$

The localization property says that this factor space is contractible. We may
write the selected target suggestively as $R[1/f]$, while remembering that the
notation names the role of $L$, not a fraction grammar inside its carrier.
Then (21.3) is the invariant content of the usual substitution

$$
\frac{x}{f^n}\longmapsto h(x)h(f)^{-n}.
$$

The displayed fraction explains the classical formula; it is not used to
define the map. Contractibility supplies the map and all comparisons between
maps satisfying the same triangle without choosing numerators, denominators,
or exponents.

Admissibility belongs to the target map $h$. The localization package does not
choose, for every ring in the universe, whether the image of $f$ is a unit.
Rather, when a caller supplies unit evidence, the universal property returns
the unique factor. This keeps constructive content visible: testing
invertibility may be undecidable, but using an explicit proof of invertibility
is computationally straightforward.

This stronger uniqueness is what makes the interface computationally useful.
From a contractible factor space one projects a center, hence an actual map
$R[1/f]\to S$. Given another construction with the same universal property,
one obtains maps in both directions. Their composites and the identities are
competitors in suitable factor spaces, so uniqueness produces the inverse
laws. The universal property is thus a source of programs and equations, not
an after-the-fact slogan attached to an opaque object.

It also separates existence from characterization. A **localization package**
contains a chosen $L$, a chosen structure map, its unit evidence, and the
contractible factorization theorem. The general interface says what any such
package does. It does not yet construct a package for every pair $(R,f)$.
That remaining existence problem can be solved by a fraction model, by a
quotient, by a suitable higher-inductive construction, or by importing a
certified algebra library, without changing the consumers of localization.

<!-- evidence:COMM-RING-LOCALIZATION-UNIVERSALITY -->

> **Formal status — checked interface.** Evidence
> `COMM-RING-LOCALIZATION-UNIVERSALITY`. Unit evidence is proposition-valued,
> and a supplied localization package inverts the chosen element and gives a
> contractible space of structured factors through every admissible target
> map. The factor retains a whole ring map and its pointwise triangle. No
> general existence theorem for arbitrary $(R,f)$, fraction or power
> representation, quotient syntax, or equality of arbitrary localization
> packages is asserted.

## 21.5 Three Localizations One Can See

The abstract interface has concrete edges where no fraction construction is
needed.

First suppose $f$ is already a unit in $R$. The identity map
$R\to R$ is a localization at $f$. Every admissible map $h:R\to S$ factors
through the identity by $h$ itself, and extensionality makes that factor
unique. In particular, every ring has a canonical identity localization at
$1$.

At the opposite extreme, localize at $0$. If $h:R\to S$ sends zero to a unit,
then $0_S$ is invertible. Since a ring map preserves zero, one obtains
$0_S=1_S$, and hence every element of $S$ equals zero. The target is
contractible as a carrier. It follows that the unique map from $R$ to the zero
ring has the localization property at $0$. The zero ring is not a nuisance
case patched into the theory; it is the correct universal endpoint.

The third case is more revealing. Let $e\in R$ be idempotent, so $e^2=e$.
Consider the fixed-image carrier

$$
eR=\{x\in R\mid ex=x\}.
$$

It is closed under the inherited additive operations and multiplication. Its
zero is $0_R$, while its multiplicative unit is $e$. Scaling defines a ring
map

$$
R\longrightarrow eR,
\qquad x\longmapsto ex.
\tag{21.4}
$$

The image of $e$ under (21.4) is the unit of $eR$, and any map that makes $e$
invertible factors contractibly through this fixed image. Thus $eR$ is a
localization at $e$, constructed without a quotient and without fractions.

The factor has a simple formula. If $h:R\to S$ makes the idempotent $e$
invertible, then idempotence of $h(e)$ and cancellation by its inverse force
$h(e)=1$. On an element $x$ fixed by multiplication by $e$, the factor sends
$x$ to $h(x)$. Conversely, the original element $r$ reaches the fixed image as
$er$, and then

$$
h(er)=h(e)h(r)=h(r),
$$

which is the required triangle. The fixed-point equation retained in the
carrier supplies exactly the coherence needed for this formula to define a
structured map.

Take now $R=\mathbb F_2\times\mathbb F_2$ and $e=(1,0)$. Componentwise
multiplication makes $e$ idempotent, yet boolean discrimination proves
$e\ne(0,0)$ and $e\ne(1,1)$. Its fixed image consists of the first component
with the second forced to zero. This is a closed, genuinely non-endpoint
localization: neither the identity localization nor the zero localization is
being disguised by notation.

<!-- evidence:COMM-RING-LOCALIZATION-MODELS -->

> **Formal status — checked models.** Evidence
> `COMM-RING-LOCALIZATION-MODELS`. The identity ring localizes at any supplied
> unit and canonically at $1$; the zero ring localizes every ring at $0$; and
> the fixed image $eR$ localizes at an idempotent $e$. The product ring
> $\mathbb F_2\times\mathbb F_2$ supplies a checked idempotent $(1,0)$ distinct
> from both endpoints, so the fixed-image construction has a concrete
> nondegenerate instance. These models do not amount to arbitrary
> localization existence.

## 21.6 Localizing Once Or Twice

Universal properties earn their keep when two descriptions must be compared.
Choose a localization of $R$ at $f$, and then localize its target at the image
of $g$. Also choose a localization of $R$ at the product $fg$. In customary
notation the two targets are

$$
R[1/f][1/g]
\qquad\text{and}\qquad
R[1/(fg)].
$$

No fraction calculation is needed to compare them. In the iterated target,
the images of both $f$ and $g$ are units, so their product is a unit. The
universal property of $R[1/(fg)]$ therefore gives a forward map

$$
\Phi:R[1/(fg)]\longrightarrow R[1/f][1/g].
$$

Conversely, if $fg$ is invertible in a commutative ring, then both $f$ and
$g$ are invertible: an inverse to $f$ is $g(fg)^{-1}$, and symmetrically for
$g$. The product localization consequently admits first a factor through
$R[1/f]$ and then a factor through the localization at the image of $g$. This
gives

$$
\Psi:R[1/f][1/g]\longrightarrow R[1/(fg)].
$$

This elementary implication is the hinge of the comparison. If $w$ is an
inverse to $fg$, then

$$
f(gw)=(fg)w=1,
\qquad
g(fw)=(fg)w=1.
$$

It converts one unit witness into the two witnesses demanded by the staged
universal properties. No appeal to prime ideals, open subsets, or a spectrum
is involved; the overlap theorem is already present in commutative algebra.

The two composites are not reduced by a hidden fraction normalizer. Instead,
$\Psi\Phi$ and the identity are factors of the same map through the product
localization, so contractibility identifies them. The other direction needs
one additional step: uniqueness at the first localization aligns the maps on
the intermediate ring, after which uniqueness at the second localization
identifies $\Phi\Psi$ with the identity. Both results are equalities of whole
structured ring maps.

**Theorem 21.2 (product and iterated localization).** For any supplied
localizations in the preceding configuration, the canonical comparison maps
satisfy both whole cancellation laws and exhibit an omega-equivalence in
$\mathbf{CRing}$,

$$
R[1/(fg)]\simeq R[1/f][1/g].
\tag{21.5}
$$

<!-- evidence:COMM-RING-ITERATED-LOCALIZATION-EQUIV -->

> **Formal status — checked.** Evidence
> `COMM-RING-ITERATED-LOCALIZATION-EQUIV`. The active comparison constructs
> canonical forward and reverse structured maps from the supplied universal
> properties. Contractibility proves their left and right whole-map laws and
> packages the selected forward map as an omega-equivalence in
> $\mathbf{CRing}$. Equation (21.5) does not identify the carrier packages by
> raw equality, provide fraction computation, or choose either localization
> globally.

This proof displays the intended style of computation. A representation-first
development might multiply fractions and cancel powers until both composites
normalize. Here the observable computation is composition of structured maps,
and the universal property closes the comparison. Concrete models remain free
to normalize fractions internally; nothing downstream is allowed to depend
on that choice.

## 21.7 From Localization To The Sieve $D(f)$

Localization answers a transformational question: what is the universal ring
under $R$ in which $f$ has become invertible? The sieve of Chapter 18 answers
a relational question: along which probes is the image of $f$ already
invertible? These are two faces of the same algebraic event.

Given a ring map $u:R\to S$, membership in the sieve $D_R(f)$ is unit evidence
for $u(f)$. Whenever a localization $R\to R[1/f]$ has been supplied, the
factorization theorem turns that membership into a structured map

$$
R[1/f]\longrightarrow S
$$

over $R$, and contractibility makes all choices of such a factor coherently
unique. Conversely, any map over $R$ carries the selected inverse of the
localized image of $f$ to an inverse of $u(f)$. The localization therefore
represents the question posed by the invertibility sieve when a representing
object is available.

The order of ideas is deliberate. The sieve $D_R(f)$ exists from the
invertibility predicate alone; it need not wait for a chosen fraction object.
A supplied localization then represents that sieve on affine points. Thus the
geometry can be organized around **invertibility's sieve**, while
localization supplies a computational chart rather than defining openness by
decree.

The next chapter makes this bridge precise. It constructs the affine functor
of points, reads $D(f)$ as an ordinary sieve on an affine, and shows how
unimodular families become finite basic-open covers. The algebra developed
here will reappear there not as an internal manual of ring operations, but as
the universal language in which affine geometry recognizes its charts.
