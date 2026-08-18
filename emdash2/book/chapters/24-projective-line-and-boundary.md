<a id="chapter-24"></a>

# 24. The Projective Line And The Boundary Of Construction

The projective line is the first scheme whose picture seems to demand gluing.
One affine coordinate sees every finite point and misses infinity; a second
coordinate sees infinity and misses a different point. Where both coordinates
are visible, each is the inverse of the other. The whole geometry is contained
in that short sentence, but its formal meaning divides into several tasks that
are easy to conflate.

One may construct the two affine lines, construct their principal regions,
identify those regions by inversion, and then prove that the identification is
effective. That is the atlas-first route. Or one may begin with a global object
already carrying two affine-line charts, take their actual intersection, and
check that its two inherited coordinate descriptions are Laurent coordinates.
That is the global-first route. The present development reaches the second
route exactly. It does not silently acquire the first.

This distinction makes the projective line an unusually revealing example.
The coordinate calculation is not deferred: it is constructed from polynomial
and localization universal properties. The common region is not an invented
overlap: it is an actual selected intersection of charts in the global slice.
Yet the global object itself remains supplied. The calculation is complete at
its stated boundary, and the boundary says precisely what a later construction
must add.

## 24.1 Two Affine Views Of One Line

Let $A$ be a commutative ring. The familiar projective-line atlas has two
charts

$$
U_0\simeq \operatorname{Spec} A[t],
\qquad
U_1\simeq \operatorname{Spec} A[u].
\tag{24.1}
$$

In homogeneous coordinates $[x_0:x_1]$, the first coordinate is
$t=x_1/x_0$ where $x_0$ is invertible, and the second is $u=x_0/x_1$ where
$x_1$ is invertible. Both descriptions apply precisely where neither
homogeneous coordinate vanishes. Thus the expected intersection has the two
coordinate presentations

$$
U_{01}\simeq D(t)\subseteq U_0,
\qquad
U_{01}\simeq D(u)\subseteq U_1,
\qquad
u=t^{-1}.
\tag{24.2}
$$

In ordinary algebraic notation its ring is therefore written

$$
A[t,t^{-1}]\simeq A[u,u^{-1}].
\tag{24.3}
$$

These formulas are a specification, not yet a construction. The symbols
$D(t)$ and $D(u)$ can name open subspaces only after one knows what represents
the corresponding invertibility conditions. The isomorphism in (24.3) can be
written down informally, but a computational account should explain why its
maps exist and which equations they satisfy. Finally, even perfect overlap
data do not by themselves produce the union $U_0\cup U_1$.

The finite-cover rhythm here follows the constructive scheme architecture
developed by [Zeuner](#ref-zeuner): global schemes are recognized through
finite affine covers, and open or functorial presentations are compared only
by an explicit theorem. The present chapter borrows that rhythm and its
careful separation of presentation from comparison. Its projective-line and
Laurent constructions are not taken from Zeuner's thesis, and no part of
Zeuner's qcqs comparison theorem is claimed below.

> **Status of (24.1)--(24.3).** These are the standard mathematical model for
> the chapter. The checked artifact has no closed term denoting
> $\mathbf P^1_A$, no general `Proj`, and no polynomial or Laurent expression
> syntax whose normal forms are the displayed rings. Its owners instead work
> with rings, structured maps, and their universal properties directly.

## 24.2 Laurent Maps Without Fractions

Begin with two supplied one-variable polynomial algebras over $A$. Write them
conventionally as $A[t]$ and $A[u]$, although what is retained formally is a
base map, a distinguished variable, and the universal property of a
one-variable polynomial algebra. Select a localization of each algebra at its
distinguished variable:

$$
\iota_t:A[t]\longrightarrow L_t,
\qquad
\iota_u:A[u]\longrightarrow L_u.
\tag{24.4}
$$

The element $\iota_u(u)$ is a unit in $L_u$. Its chosen inverse therefore
defines a valuation of the one-variable family in $L_u$. Polynomial
universality selects the unique structured map

$$
\varphi_{tu}:A[t]\longrightarrow L_u,
\qquad
\varphi_{tu}(t)=\iota_u(u)^{-1},
\tag{24.5}
$$

with the prescribed action on $A$. The image of $t$ is again a unit. The
localization universal property now extends (24.5) to a whole ring map

$$
\Phi_{tu}:L_t\longrightarrow L_u.
\tag{24.6}
$$

Reversing the two polynomial and localization presentations constructs
$\Phi_{ut}:L_u\to L_t$. Nothing in this construction parses a Laurent
polynomial, reduces a fraction, or chooses representatives. The inverse
coordinate is selected as an element of the target ring; polynomial
universality constructs the first map; localization universality constructs
the extension. The factor triangle records, for every element of $A[t]$, that
the extension after $\iota_t$ agrees with $\varphi_{tu}$.

This order matters. If one began with a formula on fractions, one would still
have to prove that it respects the localization relation and the ring
operations. The universal property performs exactly that proof while also
choosing the map. The formula $t\mapsto u^{-1}$ is not discarded; it appears
as the named coordinate equation (24.5), now attached to a whole structured
map.

**Theorem 24.1 (canonical Laurent transition).** For two supplied
one-variable polynomial algebras over $A$ and supplied localizations at their
coordinates, there is a canonical whole map from the first localization to
the second sending the first coordinate to the inverse of the second.
Reversing the inputs gives the opposite orientation, and each map carries its
whole localization-factor agreement.

<!-- evidence:LAURENT-TRANSITIONS-BY-UNIVERSALITY -->

> **Formal status — checked.** Evidence
> `LAURENT-TRANSITIONS-BY-UNIVERSALITY`. The construction is transparent and
> rule-free. It supplies neither a global projective object nor a theorem that
> the two maps in (24.6) are inverse for arbitrary polynomial and localization
> presentations.

## 24.3 One Overlap Ring, Not Two Isomorphic Copies

The generic construction still has two target rings, $L_t$ and $L_u$. A
global scheme supplies something stronger. Let $U_0$ and $U_1$ be its selected
charts, let $U_{01}$ be their selected actual intersection, and evaluate the
single global structure presheaf:

$$
R_0=\mathcal O(U_0),
\qquad
R_1=\mathcal O(U_1),
\qquad
L=\mathcal O(U_{01}).
\tag{24.7}
$$

Contravariance gives the two inherited restrictions

$$
\rho_0:R_0\longrightarrow L,
\qquad
\rho_1:R_1\longrightarrow L.
\tag{24.8}
$$

Suppose now that $R_0$ and $R_1$ are supplied as one-variable polynomial
algebras over the same base ring $A$, with coordinates $t$ and $u$, and that
the literal maps $\rho_0$ and $\rho_1$ are supplied as their localizations at
those coordinates. The Laurent construction no longer produces maps between
two disconnected candidates for the overlap. Both of its endpoints reduce to
the exact ring $L$. It constructs two endomorphisms

$$
\Theta_{tu}:L\longrightarrow L,
\qquad
\Theta_{ut}:L\longrightarrow L,
\tag{24.9}
$$

each expressing one coordinate in terms of the inverse of the other.

The final comparison is deliberately assumption-explicit. A Laurent overlap
presentation retains whole paths

$$
\Theta_{tu}=\operatorname{id}_L,
\qquad
\Theta_{ut}=\operatorname{id}_L.
\tag{24.10}
$$

The maps in (24.9) are constructed; the paths in (24.10) are supplied. This
is the exact honest boundary. Polynomial and localization universality tell us
how to extend prescribed coordinate values, but arbitrary supplied
presentations of two maps into one ring need not automatically assert that
the resulting endomorphisms are its identity. Retaining the whole paths says
that these two coordinate descriptions really are the two Laurent views of
the same inherited ring.

**Theorem 24.2 (literal common-overlap coordinates).** Two literal maps into
one ring, each presented as a one-variable polynomial chart followed by
localization at its coordinate, determine canonical coordinate-inversion
endomorphisms of that ring. A supplied Laurent overlap presentation identifies
both endomorphisms wholly with its identity.

<!-- evidence:LAURENT-COMMON-OVERLAP -->

> **Formal status — checked and assumption-explicit.** Evidence
> `LAURENT-COMMON-OVERLAP`. The identity paths are whole paths of
> structured maps, not elementwise equations gathered into an external
> compatibility square. No claim is made that every pair of localization
> presentations admits those paths.

## 24.4 The Sieve Beneath The Principal Region

The notation $D(t)$ in (24.2) is best read through the principle developed in
Chapters 18 and 22. Before it is an open, invertibility is an ordinary sieve.
On the chart $U_0$, the sieve $D_{U_0}(t)$ asks of a probe $v:V\to U_0$ whether
the restricted coordinate $t|_V$ is a unit. It is defined whether or not the
site possesses a chosen open object representing that question.

Localization is the algebraic representation theorem. A map out of
$A[t,t^{-1}]$ is the same data as a map out of $A[t]$ for which $t$ becomes
invertible. Thus the selected restriction $\rho_0:R_0\to L$, when supplied as
localization at $t$, gives the overlap ring the universal property expected of
the region $D(t)$. The second restriction gives the same actual ring the
universal property expected of $D(u)$.

This is the projective-line instance of the sieve-first insight:

$$
\begin{aligned}
\text{invertibility question}
&\longrightarrow \text{ordinary sieve}\\
&\longrightarrow \text{represented principal region}.
\end{aligned}
\tag{24.11}
$$

The first arrow is definitional; the second is a theorem or supplied
presentation. In the present package, the actual geometric intersection is
already selected, and its two ring restrictions are presented as the relevant
localizations. The Laurent identities then say that the two coordinate
answers agree on that one region.

There is a useful restraint here. The package does not prove a general
site-level equality between every selected chart intersection and an abstract
sieve classifier. It connects the actual overlap to the principal-open story
at the literal coordinate-ring and restriction-map endpoints. Chapter 22's
pointwise representability theorem explains why those localization endpoints
have the intended invertibility meaning. A whole comparison between arbitrary
site presentations would be additional geometry.

## 24.5 Laurent Coordinates On The Actual Scheme Overlap

Return to a binary site-relative scheme $S$. Its global object and structure
presheaf are already retained once. Its two chart realizations are already
affine. After a selected product in the slice supplies the actual intersection
$\Omega$, the ring $L$ and both maps (24.8) are derived by evaluating that
single presheaf. The Laurent adapter adds only a common base ring $A$ and a
coordinate presentation of those exact endpoints:

$$
\mathsf{Laurent}(S,\Omega)
=
\sum_{A:\mathsf{CommRing}}
\mathsf{LaurentOverlap}
\bigl(A,R_0,R_1,L,\rho_0,\rho_1\bigr).
\tag{24.12}
$$

The dependency in (24.12) is the point. One cannot quietly substitute an
isomorphic overlap ring, replace a restriction map, or attach the coordinates
to a different pair of charts. The types refer to the rings and maps already
computed from $S$ and $\Omega$. Conversely, the adapter does not pretend to
discover a common base ring or polynomial structures automatically. Those are
the mathematical coordinate data being supplied.

**Theorem 24.3 (actual-overlap Laurent adapter).** Given a supplied binary
site-relative scheme and its selected actual chart intersection, a common base
ring and Laurent coordinate presentation can be attached directly to the
literal chart rings, overlap ring, and inherited restriction maps, without
duplicating any of those global owners.

<!-- evidence:ACTUAL-SCHEME-LAURENT-OVERLAP -->

> **Formal status — checked.** Evidence
> `ACTUAL-SCHEME-LAURENT-OVERLAP`. This is a thin dependent adapter. It does
> not add a transition or cocycle field to the general scheme presentation,
> construct the overlap, infer Laurent coordinates from arbitrary charts, or
> glue a global scheme from them.

## 24.6 The Supplied Projective-Line Total

All the pieces can now be named as one object. For an ambient category
$\mathcal K$, define the supplied projective-line presentation by the
dependent total

$$
\mathsf{PLine}_{\mathrm{sup}}(\mathcal K)
=
\sum_{S:\mathsf{Scheme}^{(2)}_{\mathcal K}}
\left(
  \sum_{\Omega:\mathsf{Overlap}(S)}
  \mathsf{Laurent}(S,\Omega)
\right).
\tag{24.13}
$$

The first component is the already-global site-relative scheme of Chapter 23.
It owns the ringed object, local-ring certificate, covering sieve, two
constructively generating charts, and their whole affine realizations. The
second component selects their actual intersection. The third says that the
two actual structure-ring restrictions present one-variable polynomial charts
over a common base and satisfy the Laurent identities on the shared ring.

Nothing else is required because nothing else is free-floating. The overlap
projections belong to the selected product. The ring restrictions belong to
the structure presheaf. Their functoriality belongs to that presheaf as well.
The coordinate-transition maps are constructed by the universal properties in
Section 24.2. The identity comparisons are retained by the Laurent package.
Adding another transition map or cocycle field would create a second account
of data that the global object already owns.

**Theorem 24.4 (supplied projective-line capability).** From an element of
(24.13), the global scheme, actual overlap, common base ring, and exact Laurent
package are recovered by projection. Its coordinate-inversion endomorphisms
are the internally constructed maps of Theorem 24.2 and carry the supplied
whole identity paths.

<!-- evidence:SUPPLIED-P1 -->

> **Formal status — checked, supplied, and conditional.** Evidence
> `SUPPLIED-P1`. The total and its observations compute by dependent-pair
> projection. It neither constructs a closed global object nor proves
> projectivity or non-affineness.

$$
\begin{aligned}
\text{supplied global scheme}
&\longrightarrow \text{actual chart intersection}\\
&\longrightarrow \text{two localization presentations}\\
&\longrightarrow \text{Laurent coordinate identities}.
\end{aligned}
\tag{24.14}
$$

Read from top to bottom, every arrow in (24.14) has a different logical force.
The first passage uses a
selected limit in the slice. The second adds algebraic presentations to maps
already inherited from the global object. The third constructs transition maps
and retains their whole comparison with identity. None of them reverses the
chain and constructs the global scheme from the local data.

## 24.7 What A Construction Of The Line Would Require

There are two natural ways to cross the remaining boundary. The first is
atlas-first. Construct $\operatorname{Spec}A[t]$ and
$\operatorname{Spec}A[u]$, represent the two invertibility sieves by their
localizations, construct the inversion comparison, and prove that the diagram
glues effectively. The result must carry a structure sheaf whose restrictions
recover the two affine sheaves, a local-ring certificate, and a proof that the
selected charts cover. One must then compare the constructed object, wholly,
with the supplied presentation (24.13). Merely packaging two charts and an
isomorphism cannot replace this effectivity theorem.

The second route is graded. Give $A[x_0,x_1]$ its standard grading and form

$$
\mathbf P^1_A=\operatorname{Proj} A[x_0,x_1].
\tag{24.15}
$$

Here ordinary localization is only an intermediate step. For a homogeneous
element $x_i$, one localizes the graded ring and then takes its degree-zero
part. The two standard regions should compute as

$$
\begin{aligned}
D_+(x_0)&\simeq
  \operatorname{Spec} A[x_1/x_0],\\
D_+(x_1)&\simeq
  \operatorname{Spec} A[x_0/x_1].
\end{aligned}
\tag{24.16}
$$

Their common region is obtained by inverting the displayed ratio, returning
exactly the Laurent calculation of this chapter. A complete `Proj`
construction therefore needs graded commutative rings, homogeneous
localization, a degree-zero functor, the irrelevant ideal or its covering
condition, a structure sheaf, and the relevant local-ring and descent
theorems. None of these objects is hidden inside the ungraded Laurent owner.

The same route explains projective $n$-space:

$$
\mathbf P^n_A
=
\operatorname{Proj} A[x_0,\ldots,x_n].
\tag{24.17}
$$

Its $n+1$ standard charts have coordinates $x_j/x_i$ for $j\ne i$; on
intersections, ratios invert and compose. The binary projective-line package
is therefore the smallest nontrivial test of the coordinate machinery, not an
implementation of the graded theory in disguise. A future construction
should instantiate the existing site-relative and Laurent boundaries and
prove a whole comparison with them, rather than introduce a competing notion
of scheme.

That comparison must recover, chart by chart and on the actual intersections,
the same structure-presheaf restrictions and Laurent identities. Until it
does, (24.17) describes the destination rather than a second implementation.

> **Formal status — mathematical development and research boundary.**
> Equations (24.15)--(24.17) describe the standard graded construction and the
> intended next theorem. No active emdash owner defines graded rings,
> homogeneous localization, degree zero, an irrelevant ideal, `Proj`, or
> general projective space. No non-affineness theorem is claimed, even for the
> supplied line.

## 24.8 The Boundary Is Part Of The Mathematics

The achievement of this chapter is not that a familiar object has been renamed
as a dependent record. It is that the local coordinate calculation takes place
on the actual inherited overlap of one global structure presheaf. The two
restriction maps are not copied. The Laurent transitions are not postulated as
unstructured functions. The equation $u=t^{-1}$ is realized by polynomial and
localization universality and compared wholly on one literal ring.

At the same time, existence remains visible. The global object, its cover, its
affine realizations, the selected intersection, and the Laurent identity paths
are supplied at the points where the current theory needs them. This prevents
a computational presentation from being mistaken for an atlas-effectivity
theorem. It also turns future work into a precise mathematical program: build
the missing global object, then discharge the assumptions of the existing
consumer.

The larger methodological lesson reaches beyond projective geometry. Actual
presheaves, sieves, sites, rings, and categorical limits can be computationally
internal because they live inside a functorial type theory whose equations are
checked by an outer logical framework. One need not replace them with an
abstract modal object language in order to compute. But internal computation
does not abolish mathematical hypotheses. It makes their location observable.

The third spiral of the book therefore ends where a good construction should
end: not with a vague promise that gluing will work, and not with a denial that
gluing matters, but with a coordinate theorem on an honest overlap and a clear
account of the global theorem still owed.

The fourth spiral changes direction without abandoning that discipline. It
returns to the book's first contrast—reversible paths and noninvertible
arrows—and asks what computation survives when directed structure is viewed
groupoidally, freely inverted, and then placed back inside a genuinely lax
higher-categorical comparison. The next chapter begins with the smallest
bridge: paths in a product and transport through their two coordinates.
