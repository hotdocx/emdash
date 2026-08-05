<a id="chapter-23"></a>

# 23. Schemes From Covering Charts

An atlas is persuasive because its pieces are familiar. If a space can be
covered by affine charts, one is tempted to say that the scheme is simply the
charts plus instructions for gluing them. But this description suppresses an
important choice of direction. We may begin with charts and try to construct a
global object, or we may begin with a global object and recognize some of its
regions as affine. The two directions ask for different theorems.

This chapter follows the second, **global-first** direction. A global object
$X$ is already present in a ringed site, with one structure presheaf
$\mathcal O$ and one covering sieve $\mathcal R$ on $X$. Two selected members
$u_0:U_0\to X$ and $u_1:U_1\to X$ will generate that sieve constructively.
Each chart is then compared, as a whole functorial restriction, with affine
coordinates. Local-ring behaviour is imposed on the actual slice over $X$.
The result is a binary, site-relative computational scheme presentation.

Starting globally pays a coherence dividend. Restriction maps already belong
to $\mathcal O$; their identity and composition laws are already functor laws.
An intersection, once selected as an actual product in the slice over $X$,
inherits its two projections and both maps on rings. There is no reason to
copy those maps into an atlas record and then ask whether the copies agree.
The global object is the common source from which they are computed.

The price is equally clear. This chapter does not construct $X$ from an
abstract atlas. Its slice sites, affine-basis comparisons, and one selected
chart intersection are assumption-explicit. “Scheme” here means a scheme
presentation relative to those supplied categorical semantics, not yet a
representation-independent category identified with every classical or
functorial definition of schemes.

## 23.1 Two Directions Through An Atlas

Suppose first that two affine objects $U_0$ and $U_1$ have been given, along
with a candidate overlap $U_{01}$, maps to the charts, and a transition
between coordinate descriptions. The atlas-first problem is to construct an
object $X$ for which the diagram is effective: $U_0$ and $U_1$ should cover
$X$, $U_{01}$ should be their intersection, and functions agreeing on the
overlap should glue uniquely. Even for two charts, that is a colimit and
descent theorem. For more charts one must also control triple overlaps and
cocycles. Merely storing the expected diagrams does not prove that a global
object exists.

Now reverse the situation. Let $X$ already be an object of a category
$\mathcal K$, and let $u_i:U_i\to X$ be actual arrows. Their intersection, if
the needed product exists in the slice $\mathcal K/X$, is no longer an
invented compatibility object. It is the categorical object

$$
U_{01}=U_0\times_X U_1.
\tag{23.1}
$$

If a single presheaf $\mathcal O$ is already defined on $\mathcal K$, then its
values $\mathcal O(U_i)$ and $\mathcal O(U_{01})$ and its two restriction maps
are forced by (23.1). Repeated restriction agrees because $\mathcal O$ is a
functor. Global-first geometry therefore shifts the hard question. We no
longer ask whether chart data can be glued to create $X$; we ask whether
selected regions of $X$ really are affine and whether they cover in the
chosen topology.

Max Zeuner develops two constructive architectures for qcqs schemes: finite
affine covers of locally ringed lattices and affine compact-open covers of
functors of points, followed by a comparison theorem between them. The
finite-cover rhythm is an important model for the present exposition, but the
emdash construction changes both its starting point and its classifier of
locality. The global object and its ringed categorical semantics are supplied
first; coverhood is carried by an ordinary sieve; and the locus where a
section is invertible is the sieve $D_U(s)$ of all successful probes. A compact
open can represent that sieve in a coherent setting, but such a
representability theorem is not assumed merely in order to speak about the
sieve.

The distinction is not a contest between definitions. A global-first package
is useful when a semantic object has already been built and one wants a
computational account of its charts. An atlas-first theorem is indispensable
when the charts are the input from which the object must be created. Zeuner's
comparison explains why two mature theories of qcqs schemes agree. Here the
more modest task is to identify exactly how far one can travel on the first
route with the current owners.

> **Attribution and comparison boundary.** This chapter comparatively adapts
> the finite affine-cover and functor-of-points architecture of
> [Zeuner](#ref-zeuner), especially Sections 3.3, 4.2, 5.1, and 5.3. It does
> not import the theorem that affine charts glue to a qcqs scheme, the compact
> open classifier, or the equivalence between functorial and locally
> ringed-lattice schemes. The site-relative global-first presentation below
> is the active emdash result.

## 23.2 One Covering Sieve, Two Generators

Let $\mathcal A$ be a reflective commutative-ringed site with base category
$\mathcal K$. Its included structure presheaf will be written

$$
\mathcal O:\mathcal K^{\mathrm{op}}\longrightarrow\mathbf{CRing}.
$$

Choose an object $X\in\mathcal K$, an ordinary sieve $\mathcal R$ on $X$,
and evidence that $\mathcal R$ covers $X$ in the selected Grothendieck
topology. This is already global geometric data. Every arrow $q:V\to X$ in
$\mathcal R$ is a region of $X$, and every further restriction of $q$ remains
in $\mathcal R$. Grothendieck stability also says that pulling $\mathcal R$
back along any arrow into $X$ produces a covering sieve on its domain.

A selected chart is initially nothing more than a selected member of this
sieve. Thus an arrow $u:U\to X$ becomes a chart when accompanied by
$u\in\mathcal R$. The name does not make $U$ affine. It records that $u$ is
one of the regions accepted by the global cover; affineness requires the
separate comparison developed in Section 23.5.

Select two such members $u_0:U_0\to X$ and $u_1:U_1\to X$. Their membership
alone does not say that they cover. A sieve can contain two arrows while also
containing regions that factor through neither one. The computational
generation condition supplies the missing direction: for every
$q:V\to X$ in $\mathcal R$, it returns a Boolean side $b$, a map
$h:V\to U_b$, and the triangle

$$
q=u_b\circ h.
\tag{23.2}
$$

In dependent notation, the content is

$$
\prod_{q:V\to X}
\bigl(q\in\mathcal R\bigr)\longrightarrow
\sum_{b:\mathbf 2}\sum_{h:V\to U_b}(q=u_bh).
\tag{23.3}
$$

Equation (23.3) is stronger computationally than the mere assertion that
some chart contains every covered region. Given a membership witness, one can
execute the selection, inspect which chart was chosen, and use the actual
factor map. No propositional truncation hides the branch. Conversely, because
both $u_0$ and $u_1$ are themselves members and a sieve is closed under
precomposition, every arrow factoring through either chart belongs to
$\mathcal R$. The retained sieve is therefore exactly generated, in this
witness-rich sense, by the two selected arrows.

There are two cautions. First, (23.3) does not construct a second sieve: it
explains the already-selected covering sieve $\mathcal R$. Its coverhood comes
from the global package, not from the unsupported observation that two arrows
have been named. Second, a general member $q$ need not itself be affine. It is
a refinement of one affine generator once the relevant Boolean branch is
computed. Affineness belongs to the generator's whole realization and does
not automatically descend to every arbitrary arrow without another theorem.

<!-- evidence:GLOBAL-RINGED-COVER-BINARY-GENERATION -->

> **Formal status — checked.** Evidence
> `GLOBAL-RINGED-COVER-BINARY-GENERATION`. The global package retains the
> reflective ringed site, object, ordinary covering sieve, structure
> presheaf, and Grothendieck-stable pullbacks. Binary generation computes a
> selected chart, factor map, and triangle for every sieve member. The active
> result does not infer affineness from sieve membership, construct an
> atlas-first object, or turn arbitrary refinements into affine charts.

The choice to retain a sieve rather than just a two-element family has a
further advantage. Pulling the cover back along a region does not require a
new ad hoc list of chart fragments. The sieve pullback contains exactly the
arrows whose composites lie in $\mathcal R$, and Grothendieck stability makes
it covering. When an explicit generator is needed, (23.3) still computes a
factor through $U_0$ or $U_1$. Invariant coverhood and executable chart
selection coexist without being collapsed into the same representation.

## 23.3 Local Rings Without Stalks

A sheaf of rings is not automatically a sheaf of local rings. Descent says
that compatible sections glue; locality says, roughly, that algebraic
alternatives can be resolved after passing to a cover. Classically the latter
is often phrased by requiring every stalk to be a local ring. A computational
site can express the needed alternatives directly, before stalks have been
constructed.

Let $T$ be a Grothendieck topology on a category and let $\mathcal O$ be a
commutative-ring-valued presheaf. For $s\in\mathcal O(U)$, recall the ordinary
sieve $D_U(s)$ of arrows $q:V\to U$ along which $s|_q$ is invertible. Two
support laws are automatic in the ordinary algebraic account: one is
invertible everywhere, and a product becomes invertible precisely where both
factors do. In sieve notation these give the expected equations

$$
\begin{aligned}
D_U(1)&=\top,\\
D_U(st)&=D_U(s)\cap D_U(t).
\end{aligned}
\tag{23.4}
$$

Equation (23.4) is mathematical orientation here; the local-ring interface
below packages the two nonautomatic topology laws, not new whole sieve
equalities for one and products.

The local-ring content lies in the two remaining directions. If zero becomes
invertible at $U$, then $U$ is locally void: the literal empty sieve must cover
$U$. And if $s+t$ is invertible, there must be a covering sieve $\mathcal S$
such that every $q:V\to U$ in $\mathcal S$ comes with a selected alternative

$$
s|_q\text{ is invertible}
\quad\text{or}\quad
t|_q\text{ is invertible}.
\tag{23.5}
$$

The disjunction in (23.5) is a Boolean-indexed dependent pair. It remembers
which summand is usable and retains its unit evidence. Thus the condition is
the executable Kripke--Joyal form of

$$
D_U(0)=\bot,
\qquad
D_U(s+t)\le D_U(s)\vee D_U(t).
\tag{23.6}
$$

No raw union of sieves has to be constructed for (23.6). The right side is
presented by a chosen cover subordinate to the two alternatives, and a branch
is requested only after an actual member of that cover is supplied. Nor is
the choice erased into a mere proposition. This is exactly the kind of local
information a later calculation can consume: restrict to a cover member,
inspect the side, and use the selected inverse.

The formulation is categorical semantics, not an auxiliary modal object
language. Objects, arrows, sieves, restrictions, unit witnesses, covers, and
branches all live inside the functorial theory represented in the outer
logical framework. Lambdapi's conversion and unification rules execute the
transparent projections and functor actions; the same interfaces can be
targeted by an explicit TypeScript core. Computation therefore does not
require replacing the site by a primitive modality. It comes from making the
categorical data sufficiently internal and functorial.

<!-- evidence:TOPOLOGY-LOCAL-RING-CERTIFICATE -->

> **Formal status — checked, topology-local.** Evidence
> `TOPOLOGY-LOCAL-RING-CERTIFICATE`. The presentation executes empty-cover
> nontriviality and coverwise Boolean splitting of an invertible sum. It is a
> site-level local-ring certificate for a whole commutative-ring presheaf. It
> does not construct stalks, prove equivalence with stalk-local rings, form a
> raw sieve join, decide unit evidence, or identify the chosen topology with
> the classical Zariski topology.

This condition must be attached to the correct object. Our global structure
presheaf lives on $\mathcal K$, whereas the local geometry of $X$ lives on the
slice $\mathcal K/X$. The next section constructs the presheaf restriction to
that whole slice and makes its sheaf boundary explicit. Only then can (23.5)
be read as local-ring behaviour of the global object $X$ rather than of an
unrelated family of rings.

## 23.4 Restricting The Whole Structure

For any $U\in\mathcal K$, the conventional slice $\mathcal K/U$ has a domain
functor

$$
\operatorname{dom}_U:\mathcal K/U\longrightarrow\mathcal K,
\qquad
(q:V\to U)\longmapsto V.
\tag{23.7}
$$

Precomposition with its opposite constructs the ambient restriction

$$
\mathcal O|_U
  =\mathcal O\circ\operatorname{dom}_U^{\mathrm{op}}
  :(\mathcal K/U)^{\mathrm{op}}\longrightarrow\mathbf{CRing}.
\tag{23.8}
$$

At a slice object $q:V\to U$, formula (23.8) computes to
$\mathcal O(V)$. At a triangle over $U$, it computes the corresponding
restriction homomorphism. Identity, composition, and naturality are inherited
from ordinary functor composition. Thus the whole presheaf needed on a chart
slice is constructed, not copied object by object.

What (23.8) does **not** construct is a topology and sheaf theory on
$\mathcal K/U$. The active interface asks for a reflective commutative-ringed
site on that actual slice and a whole isomorphism

$$
\iota_U\mathcal O_U\;\cong\;\mathcal O|_U
\tag{23.9}
$$

in the commutative-ring presheaf category. Here $\mathcal O_U$ is the selected
structure sheaf of the supplied slice site and $\iota_U$ includes it as a
presheaf. The topology, reflector, and sheaf object on the left of (23.9) are
hypotheses. The right side and its restriction action are the computing
ambient object.

The word “whole” in (23.9) matters. A separate ring isomorphism at every
slice object would not ensure compatibility with restriction. A functor-level
isomorphism carries that compatibility internally and supplies inverse laws
in the presheaf category. One may compute using the transparent right side,
then pass back to the selected sheaf semantics without introducing a new
naturality square for each calculation.

For the whole object $X$, the topology-local ring certificate of Section 23.3
is attached to the computing presheaf $\mathcal O|_X$ using the topology of
the supplied slice site. The resulting local presentation combines supplied
reflective semantics on $\mathcal K/X$, a whole bridge to ambient
restriction, and executable local-ring forcing on that bridge's target. It
does not claim that the slice topology was induced from the ambient topology
or that a general sheaf-pullback theorem has been proved.

## 23.5 When A Selected Region Is Affine

Return to one selected cover member $u:U\to X$. To call it affine, it is not
enough to attach a ring name $R$ to $U$. We must compare the actual global
structure restricted over $U$ with the affine coordinates developed in
Chapter 22.

Begin with the supplied reflective slice presentation (23.9). Choose a ring
$R$ and a thin affine-scheme presentation for $R$. Its big affine slice has
the generated Zariski topology and coordinate presheaf
$\mathcal O_{\mathrm{coord},R}$. Next choose a whole basis functor

$$
i:\mathbf{Aff}/\operatorname{Sp}(R)\longrightarrow\mathcal K/U.
\tag{23.10}
$$

The direction of (23.10) says that affine coordinate probes are realized as
actual regions over $U$. It is accompanied by two supplied comparisons. The
first is a sheaf-basis equivalence along $i$: restriction relates the selected
sheaf categories on the affine basis and on the actual slice. This is an
equivalence of sheaf semantics along the displayed functor, not an assertion
that the two base categories are themselves equivalent. The second is a
direct whole isomorphism from the ambient restriction to the included
presheaf of the selected affine presentation. That affine presentation
already retains its own whole coordinate comparison. Together they form the
chain

$$
i^*(\mathcal O|_U)
  \;\cong\;\iota_R\mathcal O_R^{\mathrm{aff}}
  \;\cong\;\mathcal O_{\mathrm{coord},R}.
\tag{23.11}
$$

Equation (23.11) is the computational heart of the affine label. On every
affine probe, the structure inherited from the global object agrees with the
coordinate ring; on every arrow between probes, the agreement respects the
restriction homomorphism. Composing the supplied first bridge with the
affine scheme's retained coordinate bridge derives the displayed
ambient-to-coordinate comparison.
Nothing has to be postulated separately for individual chart arrows.

An **affine realization** of $u$ retains exactly these inputs: the supplied
reflective site on $\mathcal K/U$, the coordinate ring $R$, its thin affine
presentation, the basis functor (23.10), and the whole basis realization.
The region $u$ is now affine in the precise, site-relative sense that its
actual restricted structure is realized by affine coordinates along the
selected basis.

<!-- evidence:WHOLE-SLICE-AFFINE-REALIZATION -->

> **Formal status — checked, assumption-explicit.** Evidence
> `WHOLE-SLICE-AFFINE-REALIZATION`. Whole ambient restriction is constructed
> by precomposition with the slice-domain functor. The reflective slice,
> sheaf-basis equivalence, affine scheme presentation, basis functor, and
> direct ambient-to-affine-underlying comparison are supplied; composition
> with the affine presentation's retained bridge derives a whole coordinate
> isomorphism. No induced slice topology, raw
> base-category equivalence, arbitrary basis theorem, or general transport of
> local exactness is claimed.

Applying this package to both $u_0$ and $u_1$, and adjoining the generation
witness (23.3), gives a binary affine-cover presentation. It retains two
actual regions of the one global object, two coordinate rings, and two whole
affine realizations. For an arbitrary $q\in\mathcal R$, the Boolean generator
computes which affine chart it refines and exposes that chart's already-owned
realization and coordinate ring. It still does not declare $q$ itself affine.

## 23.6 The Site-Relative Scheme Total

The pieces can now be gathered without enlarging their claims. A binary
site-relative scheme presentation consists of the following dependent data:

$$
\begin{aligned}
\mathsf{Scheme}_{\mathcal K}^{(2)}=\sum_{(\mathcal A,X,\mathcal R)}
  \bigl(&\text{whole-slice local presentation of }X,\\
        &u_0,u_1\in\mathcal R,\\
        &\text{constructive generation as in (23.3)},\\
        &\text{whole affine realizations of }u_0,u_1\bigr).
\end{aligned}
\tag{23.12}
$$

The first summation variable includes the global reflective ringed site,
distinguished object, covering sieve, and proof of coverhood. The dependent
certificate then adds local-ring forcing on the actual slice and the binary
affine atlas. Because each later field is indexed by the object selected
before it, malformed combinations are not representable: an affine
realization cannot silently refer to a different chart, site, or global
object.

**Theorem 23.1 (global-first binary scheme presentation).** Given the data in
(23.12), there is one transparent site-relative scheme total that retains the
global ringed object exactly once and exposes its structure presheaf, whole
object, covering sieve, local-ring certificate, two selected generators, and
two whole affine realizations through their existing owners.

<!-- evidence:BINARY-SITE-RELATIVE-SCHEME -->

> **Formal status — checked, site-relative.** Evidence
> `BINARY-SITE-RELATIVE-SCHEME`. The constructor and all named observations
> compute through the dependent total. The global structure presheaf is
> inherited rather than stored again; the local and atlas halves remain their
> exact existing packages. No overlap, transition, cocycle, gluing field,
> scheme morphism, effectivity theorem, or representation-independent
> category of schemes is added.

The absence of overlap and cocycle fields is deliberate. Suppose a section is
restricted from $X$ to $U_0$, from $U_0$ to an overlap region, and perhaps
farther to another refinement. These maps are all values of the same
contravariant functor $\mathcal O$. Their agreement with direct restriction is
the functor's composition law. Adding parallel restriction maps to (23.12)
would create a second source of truth and an obligation to compare it with
the first.

The theorem is nevertheless conditional in meaningful ways. It does not
construct the global object, the reflective slice sites, or the affine-basis
equivalences. It packages them at endpoints where every downstream action can
compute. Nor does it say that all finite atlases reduce to two charts. The
binary case is the active vertical slice: rich enough to expose genuine
covering, local forcing, affineness, refinement, and intersection, but narrow
enough that the supplied boundary remains visible.

The qualifier **site-relative** prevents a more subtle overstatement. The
chosen topology decides which sieves cover and the supplied basis semantics
decides what counts as an affine chart. Another site may present equivalent
geometry, but (23.12) alone does not construct that equivalence. In
particular, it does not identify this presentation with Zeuner's compact-open
qcqs schemes, with classical locally ringed spaces, or with all local
functors on the big Zariski site.

## 23.7 The Intersection Belongs To The Global Object

Although an overlap should not be copied into the scheme total, a consumer
may still need an explicit one. For the two slice objects
$u_0,u_1\in\mathcal K/X$, supply a selected binary product with its whole
universal property,

$$
u_{01}=u_0\times u_1
\quad\text{in }\mathcal K/X.
\tag{23.13}
$$

Its domain in $\mathcal K$ is an actual object $U_{01}$ equipped with arrows
$p_i:U_{01}\to U_i$ whose composites to $X$ agree. Applying the whole domain
functor to the product projections derives these arrows; no base-level
projections are supplied separately.

The global structure presheaf then computes three rings and two homomorphisms:

$$
\mathcal O(U_0)
  \xrightarrow{\,p_0^*\,}
\mathcal O(U_{01})
  \xleftarrow{\,p_1^*\,}
\mathcal O(U_1).
\tag{23.14}
$$

The variance in (23.14) is the familiar geometric one: an arrow from the
intersection to a chart restricts functions from the chart to the
intersection. Every term is evaluated from an existing whole owner. The
overlap ring is not a new coordinate choice, and the homomorphisms are not
transition fields. They are the value and arrow action of $\mathcal O$ on the
selected categorical intersection.

<!-- evidence:ACTUAL-BINARY-CHART-OVERLAP -->

> **Formal status — checked after a supplied product.** Evidence
> `ACTUAL-BINARY-CHART-OVERLAP`. A selected binary product in the conventional
> slice retains its whole universal property. Its two slice projections,
> underlying arrows, overlap ring, and both restriction homomorphisms are
> derived. The active owner does not construct arbitrary pullbacks, prove
> every pair of charts has an intersection, identify the overlap as affine or
> as a localization, or add an atlas-gluing theorem.

This is the exact sense in which coherence is inherited. If another selected
restriction $W\to U_{01}$ is introduced, the maps from the chart rings to
$\mathcal O(W)$ agree with the composites through $\mathcal O(U_{01})$
because presheaf action respects composition. If triple intersections are
later supplied, the same principle handles their restriction diagrams.
Existence of the needed limits remains a separate categorical hypothesis;
compatibility of the resulting restriction maps does not.

One should also resist a plausible but invalid inference: because $U_0$ and
$U_1$ have affine realizations, $U_{01}$ has not thereby been proved affine.
In familiar schemes the intersection of two affine opens is often
quasi-affine and, under additional separatedness or basic-open hypotheses,
admits more precise affine presentations. None of those theorems is smuggled
into (23.13). Chapter 24 supplies a much narrower Laurent-coordinate adapter
for the selected overlap used in the projective-line presentation.

## 23.8 What Has Been Built, And What Has Not

The global-first construction has now crossed a genuine threshold. It starts
with one ringed object and proves that a selected binary covering sieve is
generated by two regions whose whole restrictions have affine coordinate
realizations. It attaches an executable local-ring condition to the actual
slice over the object. It packages those data in one dependent total. And,
when a product is supplied in that slice, it computes the chart intersection,
its ring, and both restriction maps from the global presheaf.

The resulting chain is worth reading from left to right:

$$
\begin{aligned}
\text{global ringed object}
&\longrightarrow \text{covering sieve}\\
&\longrightarrow \text{two constructive generators}\\
&\longrightarrow \text{whole affine realizations}\\
&\longrightarrow \text{site-relative scheme total}\\
&\longrightarrow \text{inherited intersection}.
\end{aligned}
\tag{23.15}
$$

At each arrow, either a new hypothesis is named or a new construction is
performed. The global object, reflective slice semantics, affine presentations,
basis equivalences, local-ring certificate, and selected slice product are
supplied. Sieve pullbacks, whole ambient restrictions, generator refinements,
coordinate comparisons, total projections, overlap arrows, and ring
restrictions are derived. This ledger is mathematical content: it says which
theorems a future construction must prove before an input can disappear.

Several larger results remain outside (23.15). There is no constructor taking
two abstract affine schemes and transition data to their glued global object.
There is no effectivity or independence-of-atlas theorem, no arbitrary finite
atlas interface, no category of scheme morphisms, and no proof that changing
the selected site preserves the notion. There is no comparison with a
prime-spectrum locally ringed space, with Zeuner's locally ringed lattices, or
with functorial qcqs schemes. There is also no general theorem representing
every invertibility sieve by a compact open.

Those absences locate the work rather than diminish it. Classical definitions
often bundle the results of several deep comparison theorems into one word.
The site-relative presentation instead exposes a computational semantic
boundary: once the global object and its honest affine comparisons are
available, restrictions and overlaps should be inherited, not restated.
Conversely, when only charts are available, one still owes a gluing theorem.

The next chapter tests this boundary on the first non-affine object one wants
to draw: the projective line. Two affine-line charts should meet where their
coordinates are invertible, and the transition should send one coordinate to
the inverse of the other. The current library can package that Laurent
calculation on an inherited actual overlap once the global projective-line
presentation has been supplied. It does not yet construct that global object
from the two charts, nor does it build $\operatorname{Proj}$ or general
projective space. That precise mixture of calculation and boundary is where
the global-first method is most revealing.
