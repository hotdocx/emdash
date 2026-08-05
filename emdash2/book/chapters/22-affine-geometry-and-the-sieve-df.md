<a id="chapter-22"></a>

# 22. Affine Geometry And The Sieve $D(f)$

An affine scheme is often introduced as a set of prime ideals equipped with a
topology and a sheaf. That description is powerful, but it begins at the end
of several constructions. Constructively, even the set of prime ideals can be
difficult to use: the familiar argument that a proper ideal lies in a prime
ideal invokes a choice principle that one may have deliberately declined.
More importantly for the present book, a point-set spectrum hides the
functorial action that makes geometry computational.

There is another beginning. Instead of asking first which ideal-valued points
a ring has, ask how the ring can be mapped into every test ring. Instead of
declaring a subset on which an element is nonzero, ask along which of those
maps its image becomes invertible. The answers are already organized by
composition. They form a functor of points and, inside it, an ordinary sieve

$$
D_R(f)=\{h:R\longrightarrow S\mid h(f)\text{ is invertible in }S\}.
$$

This sieve is the geometric form of localization. A chosen localization
$R\to R[1/f]$ represents its points: maps out of $R[1/f]$ are exactly maps out
of $R$ along which $f$ is a unit. Products encode intersections,
$D_R(fg)=D_R(f)\cap D_R(g)$, and finite unit-ideal presentations generate the
Zariski topology on the big affine slice. Only after those constructions are
in place do we ask for a structure sheaf and its locality.

The order matters. The sieve exists before it is represented by one chart;
the topology exists before a sheafification for commutative-ring values has
been constructed; and the computing coordinate presheaf exists before it is
equipped with supplied sheaf and locality witnesses. Affine geometry becomes
executable without pretending that each of its classical existence theorems
has already been rebuilt.

## 22.1 Affines As Questions Of Points

Let $\mathbf{Aff}=\mathbf{CRing}^{\mathrm{op}}$. A ring map
$h:R\to S$ is read geometrically in the opposite direction,

$$
\operatorname{Sp}(S)\longrightarrow\operatorname{Sp}(R).
$$

The notation $\operatorname{Sp}(R)$ is deliberately functorial. At a test ring
$S$, define

$$
\operatorname{Sp}(R)(S)
  =\operatorname{Hom}_{\mathbf{CRing}}(R,S).
\tag{22.1}
$$

If $\alpha:S\to T$, composition sends a point $h:R\to S$ to
$\alpha\circ h:R\to T$. Thus (22.1) is not a disconnected family of sets. It
is the representable presheaf on $\mathbf{Aff}$, with all change-of-test-ring
maps supplied by Yoneda.

This definition changes the meaning of “point” in a useful way. A point is
not required to land in a field, an algebraic closure, or a two-valued truth
object. Every ring $S$ is an admissible stage of observation. Nilpotents,
idempotents, infinitesimal extensions, and degenerate rings are visible when
the chosen tests can detect them. A classical prime ideal may later be
recovered through a suitable field-like test, but it does not monopolize the
notion of observation.

Generalized points can distinguish phenomena that field-valued points erase.
For example, a nilpotent element must map to zero in every reduced field, but
it may remain visible under a map to a ring with nilpotents. Likewise, an
idempotent can reveal a decomposition through product test rings even when a
single ordinary point sees only one side. The functor of points does not force
one preferred class of tests to carry the entire geometry. It records the
response at all stages and lets later hypotheses specify which stages are
sufficient for a particular theorem.

There is a useful logical economy in this approach. To compare two candidate
affine constructions, one may compare how maps into every test ring are
classified rather than inspect a chosen point-set representation. Conversely,
an explicit test ring can refute an overstrong identification by exhibiting a
point seen on one side and not the other. The functor is therefore both an
extensional language and an experimental instrument. The representation
theorem below uses the second role directly: it constructs and compares actual
maps at an arbitrary supplied test ring.

The functor of points also remembers direction for free. Suppose
$R\to S\to T$ is a commuting triangle of ring maps. The corresponding
geometric arrows compose in the reverse order, and evaluating
$\operatorname{Sp}(R)$ simply composes the ring maps. No separate substitution
operation has to be appended to the set of points, and no proof is needed
that this operation respects identity and composition: those laws are the
ordinary Yoneda action already developed in Chapters 13 and 18.

One should not confuse this representable with the completed geometric object
traditionally denoted $\operatorname{Spec}(R)$. At this stage we have a functor
of affine tests. We have not yet selected a Zariski topology, a structure
sheaf, a local-ring condition, or a comparison with a prime-ideal spectrum.
The notation records the intended geometry while leaving each additional
layer visible.

## 22.2 Invertibility Is A Sieve

Fix $f\in R$. For every test ring $S$, let

$$
D_R(f)(S)
  =\sum_{h:R\to S}\mathsf{Unit}_S(h(f)),
\tag{22.2}
$$

where $\mathsf{Unit}_S(x)$ is the proposition that $x$ has a multiplicative
inverse. An element of (22.2) is therefore a point $h$ together with actual
evidence that the image of $f$ is invertible.

The construction is stable under refinement of the test. If
$\alpha:S\to T$, a unit witness for $h(f)$ is carried by $\alpha$ to a unit
witness for $\alpha(h(f))=(\alpha\circ h)(f)$. Hence every further probe of a
$D_R(f)$-point is again a $D_R(f)$-point. In the geometric category
$\mathbf{Aff}$, this downward closure says precisely that $D_R(f)$ is a sieve
on $\operatorname{Sp}(R)$.

Unit evidence is proposition-valued, so the sieve is ordinary rather than a
higher sieve with a nontrivial category of witnesses. The selected inverse is
retained during a calculation, but any two inverse witnesses agree. The
predicate can therefore be used as a subterminal fibre of the representable
without erasing computational access to the inverse when it is needed.

This definition avoids two premature decisions. It does not ask whether
invertibility is decidable, and it does not ask whether all the successful
probes factor through one previously chosen open object. A caller may supply a
unit witness even when no decision procedure exists. The resulting collection
of successful probes is meaningful even when no single object represents it.

Invertibility is stronger than nonvanishing. Over a field the two conditions
coincide away from zero, which can make the distinction disappear in a
point-set picture. Over a general test ring an element may be nonzero without
being a unit. The basic open $D_R(f)$ therefore does not classify probes on
which $f$ merely survives; it classifies probes on which $f$ has become
reversibly usable. That is precisely the condition needed for a map out of a
localization.

Two endpoint examples calibrate the definition. Every ring map preserves one,
and one has a canonical inverse, so $D_R(1)$ is the maximal sieve. By contrast,
membership in $D_R(0)$ forces zero to be a unit in the test ring and hence
forces that ring to collapse. The latter sieve is not literally empty when
the zero ring is admitted, but it is geometrically empty relative to
nondegenerate tests. The convention from Chapter 21 makes this boundary exact
rather than exceptional.

In a posetal presentation of geometry, a sieve represented by an open
$V\le U$ consists of precisely the probes that factor through $V$. Max Zeuner's
constructive development organizes affine geometry through the Zariski
lattice of compact opens and, in a locally ringed lattice, assigns a section
its largest compact-open invertibility support. From the present viewpoint,
that compact open is a particularly economical representative of the sieve
$D_U(s)$ when such a representative exists. The sieve is primary on a general
site; the compact open is the coherent or qcqs form in which all of its probes
can be summarized by one lattice element.

This chapter is structurally adapted from the Zariski-lattice, coverage,
compact-open, and functor-of-points development in
[Zeuner](#ref-zeuner). The change of viewpoint is substantial: rather than
define invertibility's locus first as a compact open, we define the ordinary
sieve of all invertibility probes and ask for representability afterward.
Nothing in that change invalidates the compact-open account in its intended
scope.

> **Formal status — mathematical development and attribution boundary.** The
> comparison with compact opens is an attributed reformulation of Zeuner's
> presentation. The active construction at this point is the ordinary sieve
> (22.2). No general theorem that $D_U(s)$ is compactly representable, no
> comparison with Zeuner's qcqs schemes, and no point-set spectrum theorem is
> claimed.

## 22.3 Localization Represents The Basic Open

Now suppose a localization has been selected,

$$
\iota_f:R\longrightarrow R[1/f].
$$

The notation again names a universal role rather than a fraction syntax. By
definition, $\iota_f(f)$ is a unit, and every map $h:R\to S$ for which $h(f)$
is a unit factors contractibly through $\iota_f$.

There are two immediate constructions at every test ring $S$. A map
$k:R[1/f]\to S$ gives

$$
\Phi_S(k)
 =\bigl(k\circ\iota_f,
        \text{$k(\iota_f(f))$ is a unit}\bigr)
 \in D_R(f)(S).
\tag{22.3}
$$

Conversely, a point $(h,u)\in D_R(f)(S)$ is exactly an admissible target for
the localization property. The center of its contractible factor space gives
a structured map

$$
\Psi_S(h,u):R[1/f]\longrightarrow S
\quad\text{with}\quad
\Psi_S(h,u)\circ\iota_f=h.
\tag{22.4}
$$

The inverse laws require no calculation with fractions. Starting with $k$,
the map $k$ itself is a competitor in the factor space used to select
$\Psi_S\Phi_S(k)$. Contractibility identifies the selected factor with $k$ as
a whole structured map. Starting with $(h,u)$, the factor triangle identifies
the map component of $\Phi_S\Psi_S(h,u)$ with $h$; proposition-valued unit
evidence then completes the equality of the dependent pairs.

**Theorem 22.1 (pointwise representation of the basic open).** For every test
ring $S$ and every supplied localization of $R$ at $f$, the maps (22.3) and
(22.4) form an explicit equivalence

$$
\operatorname{Hom}_{\mathbf{CRing}}(R[1/f],S)
  \simeq D_R(f)(S).
\tag{22.5}
$$

<!-- evidence:AFFINE-BASIC-OPEN-POINT-REPRESENTATION -->

> **Formal status — checked, pointwise.** Evidence
> `AFFINE-BASIC-OPEN-POINT-REPRESENTATION`. Both maps and both inverse laws in
> (22.5) are constructed from the localization universal property, whole
> ring-map extensionality, and proposition-valued unit evidence. The
> equivalence is available for each test ring. Both sides retain their
> functorial action through existing owners, but the active result does not
> package these components as a whole natural equivalence or equality of
> presheaves.

That last qualification is not a defect in the mathematical idea. Formula
(22.5) is exactly the component expected from representability, and its maps
are defined canonically from composition and factorization. A complete
presheaf-level equivalence would additionally assemble the components as
internal transformations and prove their whole inverse laws in the relevant
functor category. The current theorem records the strength that has actually
been checked rather than replacing that missing assembly by an external
assertion of naturality.

Representability also separates invariance from choice. Two constructions of
a ring called $R[1/f]$ need not be definitionally equal as carrier packages.
Each nevertheless classifies the same factorization problem, so their
universal properties construct comparison maps and the relevant inverse laws.
Geometry may consequently use “the chart $D(f)$” without requiring every
implementation to share one fraction representation or normal form. What is
invariant is the question asked by the sieve; a selected localization is a
computational coordinate presentation of it.

This reverses a common expository dependency. If one defines $D(f)$ to be the
spectrum of a fraction ring, openness is tied immediately to the chosen
construction of fractions. If one begins with (22.2), closure under refinement
follows from preservation of units alone. The universal property then proves
that a fraction model, quotient model, idempotent fixed-image model, or any
other certified localization presents the same geometric question.
Representation becomes a theorem with executable maps.

The case $f=1$ recovers the whole affine: the identity localization at an
already invertible element represents the maximal invertibility question. The
case $f=0$ reaches the opposite boundary. Localization at zero is the zero
ring, so maps out of it represent precisely those test maps under which zero
has become a unit—that is, the degenerate stages where the target ring has
collapsed. These endpoints arise from the same universal statement as every
other basic open.

## 22.4 Multiplication Computes Intersection

The elementary algebra of units already knows how basic opens intersect. For
a fixed point $h:R\to S$, if $h(fg)$ is invertible with inverse $w$, then

$$
h(f)\bigl(h(g)w\bigr)=1,
\qquad
h(g)\bigl(h(f)w\bigr)=1.
$$

Thus $h(f)$ and $h(g)$ are both units. Conversely, the product of two units is
a unit. Since all three unit predicates are propositions, these operations
give an equivalence between unit evidence for $h(fg)$ and paired unit evidence
for $h(f)$ and $h(g)$.

Holding the underlying point $h$ fixed and summing over all points yields

$$
D_R(fg)(S)
 \simeq
 \sum_{h:R\to S}
   \bigl(\mathsf{Unit}_S(h(f))\times
         \mathsf{Unit}_S(h(g))\bigr).
\tag{22.6}
$$

The right side is the explicit pointwise intersection of $D_R(f)$ and
$D_R(g)$: one point of the whole affine carrying membership in both sieves.
No equality of chosen localization packages is needed. If a localization at
$fg$ is supplied, Theorem 22.1 represents the left side, and composition with
(22.6) represents the intersection by maps out of $R[1/(fg)]$.

This is the geometric face of Theorem 21.2. The algebraic equivalence

$$
R[1/(fg)]\simeq R[1/f][1/g]
$$

says that entering $D(f)$ and then $D(g)$ has the same coordinate ring as
entering their product open at once. In the functor-of-points picture,
equation (22.6) says that the two procedures admit the same tests. The first
statement compares coordinate rings by whole structured maps; the second
compares membership types at every test ring. Together they explain why
multiplication is the algebra of intersection.

<!-- evidence:AFFINE-BASIC-OPEN-INTERSECTION -->

> **Formal status — checked, pointwise.** Evidence
> `AFFINE-BASIC-OPEN-INTERSECTION`. The active maps give the equivalence
> (22.6), and a supplied localization at $fg$ gives an executable two-step
> representation of its right side with both component inverse laws. This is
> not yet a whole-presheaf intersection theorem, an external naturality
> family, a topology, or an appeal to univalence.

The formula is already the meet law of the Zariski lattice. Zeuner writes the
standard compact-open support as $D(fg)=D(f)\wedge D(g)$. Here the same law is
seen one probe at a time before a compact-open classifier is assumed. When a
compact open represents each sieve, pointwise intersection descends to the
lattice meet. When no such representative is known, equation (22.6) still
calculates the intersection of the sieves themselves.

Multiplication governs finite meets, but covering uses addition as well. A
certificate $a_1f_1+\cdots+a_nf_n=1$ says that the chosen basic regions are
jointly sufficient. The robust geometric form of that sufficiency is obtained
by declaring their arrows to generate a cover and then closing under the
Grothendieck laws. The equation supplies finite algebraic evidence; the
topology below supplies invariant coverhood. This keeps the meet calculation
(22.6) distinct from the join-like operation of generating a covering sieve.

## 22.5 The Big Affine Slice And Its Coordinates

To pass from one affine to its charts, fix $R$ and consider every ring map
$h:R\to S$. Geometrically it is a chart

$$
\operatorname{Sp}(S)\longrightarrow\operatorname{Sp}(R).
$$

These charts form the **big affine slice over** $\operatorname{Sp}(R)$. A
morphism from the chart $R\to T$ to the chart $R\to S$ is a ring map
$\beta:S\to T$ whose triangle over $R$ commutes. Its geometric direction is

$$
\operatorname{Sp}(T)\longrightarrow\operatorname{Sp}(S),
$$

and it carries the whole structured restriction map $S\to T$ that coordinates
must follow.

There is consequently a tautological commutative-ring-valued coordinate
presheaf $\mathcal O_{\mathrm{coord}}$. It sends the chart $R\to S$ to $S$ and
the geometric arrow represented by $\beta:S\to T$ to the same structured ring
map $\beta$. At the whole chart $R\to R$ its value is $R$. At the basic-open
chart $R\to R[1/f]$ its value is the chosen localization ring. Nothing is
defined only on objects: the restriction maps and their identity and
composition laws are part of the existing whole functorial structure.

Theorem 22.1 now receives its geometric reading. The chart

$$
\operatorname{Sp}(R[1/f])\longrightarrow\operatorname{Sp}(R)
$$

has, at every test ring $S$, exactly the points of the sieve $D_R(f)$. The
active theorem proves this statement componentwise; the big slice supplies
the chart object and its coordinate restriction. Representation is therefore
not used to define the sieve, but once a localization is selected it produces
the expected geometric chart.

The overlap comparison from Chapter 21 also lifts into the slice. The two
whole ring maps between $R[1/(fg)]$ and $R[1/f][1/g]$ become chart arrows in
opposite geometric directions. Applying $\mathcal O_{\mathrm{coord}}$ to
those arrows computes back to the same structured comparison maps, and their
already-proved cancellation laws give an equivalence of the coordinate rings.
No new overlap equation is copied into the chart record; it is inherited from
the algebra that owns it.

Why use the big slice rather than immediately restrict to the small category
of basic opens of $\operatorname{Sp}(R)$? The big slice accepts every
$R$-algebra as a chart. Base change, comparison maps, degenerate targets, and
future affine realizations can therefore be expressed without first proving
that each object belongs to a chosen basis. A small site is often more
economical for compactness or cohomological arguments, but equivalence between
the two presentations is a theorem. Starting big keeps the functor-of-points
semantics literal and postpones that theorem rather than assuming it.

The price is controlled redundancy. Many big-slice objects describe regions
already covered by smaller basic charts, and equivalent localizations may
appear as distinct packages. The coordinate presheaf handles this without
quotienting the objects: it follows every whole ring map, while universal
properties supply comparisons where needed. A later basis theorem may show
that suitable redundancies are invisible to local data. They are not erased
at the computational boundary.

<!-- evidence:AFFINE-BIG-SLICE-COORDINATES -->

> **Formal status — checked.** Evidence `AFFINE-BIG-SLICE-COORDINATES`. The
> conventional big affine slice, the whole coordinate presheaf, literal
> charts, localization charts, commuting chart arrows, and the two
> product/iterated-localization overlap directions are active. Coordinate
> restriction along a chart arrow computes to its supplied whole ring map.
> The big slice is not identified with a small site of opens and does not by
> itself provide a topology, sheaf, locally ringed space, or complete scheme.

## 22.6 Finite Families Generate The Big Zariski Topology

The algebraic certificate from Chapter 21 becomes geometric on every chart.
Let $h:R\to S$ be an object of the big affine slice, and choose a finite family
$f_1,\ldots,f_n\in S$ together with coefficients satisfying

$$
\sum_i a_if_i=1.
\tag{22.7}
$$

For each $f_i$, also choose a universal-property localization of $S$ at
$f_i$. It determines a whole chart arrow

$$
\operatorname{Sp}(S[1/f_i])
  \longrightarrow\operatorname{Sp}(S)
  \longrightarrow\operatorname{Sp}(R).
\tag{22.8}
$$

Equation (22.7) is the finite certificate that these basic charts cover. To
turn that statement into a topology without discarding its computational
input, first call a sieve on the chart a **generator** when it contains every
arrow in one selected family (22.8). The generators remember the family,
coefficients, localization packages, and literal containments. They are
witness-rich data, not merely truth values.

Now intersect all Grothendieck topologies on the big affine slice that accept
those generators. The result is a lawful topology, denoted
$J_{\mathrm{Zar}}^{\mathrm{big}}(R)$. Every selected finite family covers in
it by construction, and it is least in the precise sense that

$$
J_{\mathrm{Zar}}^{\mathrm{big}}(R)\le J
$$

for every other Grothendieck topology $J$ accepting the same generators. The
presentation witnesses remain available at the generating boundary, while
the statement that a sieve covers is proposition-valued. This is the same
useful separation encountered in Chapter 19: rich evidence enters the
generator; invariant coverhood leaves it.

**Theorem 22.2 (the generated big Zariski topology).** The selected finite
unimodular localization families on all charts of the big affine slice
generate a Grothendieck topology with computing generator inclusion and the
leastness property above.

<!-- evidence:AFFINE-BIG-ZARISKI-TOPOLOGY -->

> **Formal status — checked.** Evidence `AFFINE-BIG-ZARISKI-TOPOLOGY`. Each
> chosen localization is a whole internal chart arrow whose coordinate
> restriction is the localization map. The generator retains finite
> containment, and the generic generated-topology construction supplies a
> lawful least topology. No global choice of localization packages,
> cover-derivation syntax, coverhood decision procedure, subcanonicity theorem,
> sheafification, or comparison with the small Zariski site is asserted.

This construction parallels the finite Zariski coverage in Zeuner's
functorial account, but the bookkeeping is arranged around sieves. A finite
family presents probes that must cover; Grothendieck closure then adds all
maximal, pulled-back, and locally implied covers. In a coherent setting the
same information may be summarized by joins in the Zariski lattice. The big
site keeps the probes and their restriction maps explicit, which is exactly
what the later computational structure presheaf consumes.

The Grothendieck closure is doing real work. A displayed family such as
(22.8) is only one cover presentation on one chart. Pulling a covering sieve
back along a chart arrow must again cover, and a sieve covered locally by
covering pullbacks must cover globally. Stability and local character come
from the generated topology, not from repeatedly manipulating the
coefficients in (22.7). When an explicit mapped family is desired, structured
ring maps transport the unimodular coefficients, while target localization
packages are supplied rather than chosen globally. The topology can therefore
be invariant even though computational presentations retain choices.

Leastness is equally important. One could declare every sieve to cover and
satisfy the Grothendieck axioms vacuously. The chaotic topology is a useful
feasibility model, but it forgets Zariski geometry. Intersecting all accepting
topologies includes exactly the consequences forced by the selected finite
families and the topology laws. The construction is impredicative rather than
an inductive syntax of derivations, so it proves the universal property of
generated coverhood without claiming a normalizer or decision procedure.

A small but concrete example comes from
$R=\mathbb F_2\times\mathbb F_2$. The complementary idempotents
$e=(1,0)$ and $1-e=(0,1)$ satisfy $e+(1-e)=1$. Their fixed-image
localizations therefore give two selected basic charts in a finite Zariski
cover. Since $e(1-e)=0$, their algebraic intersection is represented by the
zero localization. The corresponding overlap coordinate ring computes to the
zero ring. Even this degenerate overlap is informative: the two charts are
disjoint pieces of the product affine, and that fact is witnessed by
restriction maps rather than inferred from an external picture of points.

## 22.7 The Structure Sheaf Is A Separate Commitment

The coordinate presheaf $\mathcal O_{\mathrm{coord}}$ computes, but
computation alone does not prove descent. To call it a structure sheaf on the
generated big site, one needs commutative-ring-valued sheaf semantics and a
comparison identifying the selected sheaf with these coordinates.

The Cat-valued reflector constructed in Chapter 20 does not automatically
supply that result. Lifting it to commutative-ring values would require the
ring operations and laws to survive the completion coherently, and the active
development has not claimed such a lift. The affine interface therefore
makes the missing theorem an explicit input. An **affine structure-sheaf
presentation** first supplies a reflective sheaf theory for
commutative-ring-valued presheaves on the exact topology
$J_{\mathrm{Zar}}^{\mathrm{big}}(R)$. It then selects a sheaf object
$\mathcal O$ and a whole computational isomorphism from its included
presheaf to $\mathcal O_{\mathrm{coord}}$.

The comparison is whole functorial data, not a list of unrelated
object-by-object ring isomorphisms. Its component at a chart compares the
selected structure sheaf with the chart ring, while its internal
transformation action retains compatibility with every restriction. This is
strong enough for downstream computation, but it is supplied evidence. The
package does not construct the reflector or prove from first principles that
the coordinate presheaf satisfies descent.

The whole comparison matters whenever a section is transported before it is
inspected. An objectwise list of ring isomorphisms could identify
$\mathcal O(U)$ with the coordinate ring of each chart and still fail to
commute with restriction. A transformation in the presheaf category carries
that compatibility internally. Its cancellation laws let a calculation move
to the transparent coordinate presheaf, compute there, and return to the
selected sheaf without adding a new naturality square at every use.

<!-- evidence:AFFINE-STRUCTURE-SHEAF-PRESENTATION -->

> **Formal status — checked, assumption-explicit.** Evidence
> `AFFINE-STRUCTURE-SHEAF-PRESENTATION`. Given a reflective
> commutative-ring-valued sheafification capability, a sheaf object, and a
> whole computational isomorphism to the coordinate presheaf, the active
> presentation constructs the corresponding reflective ringed big site and
> exposes the comparison at every chart. Neither the capability nor the
> comparison is constructed by this affine layer.

There is a second locality condition that should not be confused with sheaf
descent. Let $U$ be a chart, let $s\in\mathcal O_{\mathrm{coord}}(U)$, and
choose a localization of the chart ring at $s$. Restricting a localization
element along every member of the sieve $D_U(s)$ gives a coherent matching
family. Cartier locality says that this restriction functor is an
equivalence: every coherent family on the invertibility sieve glues uniquely
to an element of the localized ring.

The active affine locality capability supplies this whole equivalence for
every chart, section, and supplied localization package. Its inverse is a
whole glue functor, and both composite-functor laws are retained. Yet
$D_U(s)$ need not cover $U$. Cartier locality describes the coordinate ring
of a basic-open region; ordinary sheaf descent describes reconstruction from
a covering sieve. A stalk-local-ring theorem is different again. Keeping
these three statements separate prevents the word “local” from doing more
work than the mathematics.

This distinction mirrors the sieve-first viewpoint. Sheaf descent starts with
a sieve certified to cover $U$ and asks whether compatible data on that cover
have a unique global amalgamation. Cartier locality starts with an arbitrary
section $s$ and studies the possibly noncovering region where $s$ is
invertible. Its global object is not a section over all of $U$ but an element
of the localized coordinate ring. A local-ring condition, finally, controls
how unit evidence can be found locally from algebraic alternatives such as
the invertibility of a sum. The three interfaces cooperate in scheme theory,
but none is a synonym for either of the others.

## 22.8 A Thin Computational Affine Presentation

Once the preceding commitments have been named, the affine package itself can
be small. For a ring $R$, an affine-scheme presentation consists of

$$
\begin{aligned}
\mathsf{AffPres}(R)=\bigl(&\text{structure-sheaf presentation on }
  J_{\mathrm{Zar}}^{\mathrm{big}}(R),\\
  &\text{coordinate localization locality}\bigr).
\end{aligned}
\tag{22.9}
$$

The ring $R$ already determines the big affine slice, its coordinate
presheaf, the whole chart, and the generated topology. The first entry of
(22.9) relates a supplied reflective structure sheaf to those computing
coordinates. The second supplies the whole restriction-and-glue equivalence
on every basic invertibility sieve. There is no benefit in copying chart
actions, overlap maps, or coherence equations into a larger record: they are
already inherited from the functors and universal properties that own them.

<!-- evidence:AFFINE-THIN-SCHEME-PRESENTATION -->

> **Formal status — checked, assumption-explicit.** Evidence
> `AFFINE-THIN-SCHEME-PRESENTATION`. The active affine presentation pairs the
> supplied whole structure-sheaf presentation with supplied whole coordinate
> localization locality. It projects the exact generated big-Zariski ringed
> site, the whole coordinate comparison, and locality at each selected chart
> and localization. The product ring
> $\mathbb F_2\times\mathbb F_2$ supplies a closed reviewer in which the two
> capabilities remain explicit inputs while the complementary-idempotent
> cover, chart rings, restriction maps, and zero overlap compute.

The smallness of (22.9) is evidence of internal organization, not of missing
coherence being ignored. The topology owns pullback stability and local
character. The coordinate presheaf owns restriction. Localization owns basic
charts, and the whole locality equivalence owns glue over $D(s)$. An affine
presentation selects only the capabilities that cannot yet be derived.
Duplicating their component operations would create new obligations to prove
that the copies agree with these established owners.

Calling (22.9) an affine scheme is therefore a qualified statement. It is a
computational presentation whose assumptions are visible. The active work
does not construct commutative-ring-valued sheafification, prove coordinate
locality, compare the big site with the small Zariski site, construct stalks,
establish a stalk-local-ring theorem, or build a representation-independent
category of affine schemes. Nor does it prove Zeuner's comparison between
locally ringed lattices and functorial qcqs schemes.

What it does construct is already a coherent geometric chain:

$$
\text{ring map}
\longrightarrow
\text{affine probe}
\longrightarrow
D(f)
\longrightarrow
R[1/f]
\longrightarrow
\text{basic chart}
\longrightarrow
J_{\mathrm{Zar}}^{\mathrm{big}}.
$$

Every arrow in that chain carries computation. Composition changes probes;
unit preservation restricts the sieve; localization selects factors;
multiplication computes intersections; the coordinate presheaf computes chart
restriction; and generated topology turns finite algebraic certificates into
coverhood. The supplied sheaf and locality capabilities begin exactly where
the constructed chain ends.

The next chapter starts from the complementary direction. Instead of fixing a
ring and generating its affine world, it assumes a global ringed object and a
covering sieve, selects affine charts inside that cover, and asks which
restrictions and overlaps can be inherited from the global object. That
global-first viewpoint is the bridge from one affine presentation to
site-relative schemes.
