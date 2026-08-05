<a id="chapter-18"></a>

# 18. Presheaves And Sieves

An object rarely reveals its geometry all at once. We learn about it by
probing it from other objects, by changing the probe, and by asking which
properties survive that change. For an object $U$ of a category
$\mathcal K$, the probes are simply the arrows

$$
p:V\longrightarrow U.
$$

The domain $V$ is a stage of observation. A further arrow $q:W\to V$
refines the observation, and the composite $p\circ q:W\to U$ is the same
probe viewed at the finer stage. This elementary picture contains the
beginning of presheaf semantics, the definition of a sieve, and eventually
the local-to-global language of schemes.

The decisive shift is from asking for *the* region where a property holds to
recording *every probe along which it holds*. The latter collection is
automatically adapted to change of stage. It is a sieve. An open subobject may
represent that sieve, but representation is an additional theorem, not part
of the initial definition.

This chapter develops that distinction in three steps. A presheaf gives a
coherent field of views. A higher sieve may retain a category of witnesses at
each probe. An ordinary sieve remembers only a proposition: whether the probe
belongs. The recurring example is the invertibility sieve $D_U(s)$ of a
section $s$ over $U$.

## 18.1 A Coherent Field Of Views

Let $\mathcal K$ be a category. A set-valued presheaf is a functor

$$
X:\mathcal K^{\mathrm{op}}\longrightarrow\mathsf{Set}.
$$

Thus every object $U$ has a set $X(U)$ of observations, and every arrow
$p:V\to U$ has a restriction map

$$
p^*=X(p):X(U)\longrightarrow X(V).
$$

Restriction along an identity does nothing, and restriction along a composite
is successive restriction:

$$
(\mathrm{id}_U)^*=\mathrm{id}_{X(U)},
\qquad
(p\circ q)^*=q^*\circ p^*.
$$

These equations say more than “data vary with $U$.” They say exactly how one
view becomes another. A section at a large stage can be inspected at every
smaller stage, and two routes to the same refined view agree.

Two familiar examples give the variance its geometric meaning. On a
topological space, one may assign to every open $U$ the continuous
real-valued functions on $U$. An inclusion $V\subseteq U$ restricts a
function on $U$ to one on $V$. On the opposite of a category of commutative
rings, the functor of points of a ring $R$ assigns to a test ring $S$ the
maps $R\to S$. A map of test rings changes the point by composition. In both
cases, the presheaf is not merely a table indexed by objects. Its restriction
maps are the mathematical content that lets observations move.

The examples also warn against reading “smaller stage” as literal spatial
inclusion. A probe can be an open subset, an étale map, a ring map viewed in
the opposite category, or some other morphism selected by the geometry. The
categorical definition uses only arrows. Spatial language becomes justified
when a later representation theorem supplies it.

Functorial type theory keeps the same idea but permits each $X(U)$ to be a
category rather than merely a set:

$$
X:\mathcal K^{\mathrm{op}}\longrightarrow\mathsf{Cat}.
$$

Now a stage may contain objects, arrows between observations, and higher
coherence inherited from the ambient categorical structure. Restriction is a
functor. It transports both observations and their comparisons. Presheaf maps
are natural family maps, so they too act coherently at every stage.

There is also a useful change-of-base operation. Given
$F:\mathcal A\to\mathcal B$ and a presheaf $X$ on $\mathcal B$, precomposition
produces a presheaf on $\mathcal A$:

$$
F^*X:=X\circ F^{\mathrm{op}}.
$$

The active construction realizes this whole operation by reusing the existing
pullback of directed Cat-valued families. It does not invent a second calculus
for presheaves. That economy will matter repeatedly: local geometry should
inherit functoriality from the categorical structure already present.

## 18.2 The Representable Field Of Probes

Every object $U$ supplies a canonical presheaf

$$
yU:=\operatorname{Hom}_{\mathcal K}(-,U).
$$

At a stage $V$, its objects are precisely the probes $p:V\to U$. If
$q:W\to V$, restriction sends $p$ to $p\circ q$. Nothing has been added to
the category: the presheaf merely organizes all arrows into $U$ as one
coherent field.

This is the contravariant Yoneda construction from
[Chapter 13](#chapter-13), now read geometrically. There it served as a
universal coordinate system. Here its elements are stages of observation.
The two readings are the same mathematics: a map out of a representable is
controlled by what happens at the identity probe
$\mathrm{id}_U:U\to U$.

The total category of the family $yU$ has objects $(V,p)$ with $p:V\to U$.
For restriction it is convenient to orient its arrows in the direction in
which data are reindexed. Taking the opposite recovers the conventional slice
category $\mathcal K/U$. Keeping both orientations visible prevents a common
mistake: a refinement of a probe and a map in the displayed family carry the
same information, but variance determines which way the corresponding arrow
points.

A **higher sieve** on $U$ is a Cat-valued coefficient system over this
restriction-oriented category of probes. Equivalently, it may be read as a
Cat-valued presheaf on the conventional slice. At each $p:V\to U$ it assigns
a category $S(p)$, and a refinement $q:W\to V$ induces a functor

$$
S(p)\longrightarrow S(p\circ q).
$$

The category $S(p)$ can retain choices of witnesses and arrows between them.
This is why “higher sieve” does not yet mean ordinary sieve. The maximal
higher sieve assigns the terminal coefficient category to every probe. If the
base probe $V\to U$ is changed, the entire coefficient system pulls back by
postcomposing probes, and the maximal higher sieve remains maximal.

<!-- evidence:PSH-YONEDA-HIGHER-SIEVE -->

> **Formal status — checked.** Evidence `PSH-YONEDA-HIGHER-SIEVE`. The active
> construction has a visible category of Cat-valued presheaves, restriction
> along a functor, the Yoneda presheaf with value
> $\operatorname{Hom}_{\mathcal K}(V,U)$, the restriction-oriented arrow
> total and opposite slice, and a higher-sieve classifier whose maximal
> object is stable under pullback. The slice and higher-sieve presentations
> compare through a shared family representation; they are not declared to
> be definitionally identical.

## 18.3 From Witnesses To Membership

An ordinary sieve is what remains when each coefficient category answers only
a yes-or-no question. Constructively, “yes or no” does not mean that a Boolean
decision has been chosen. It means that the space of answers is a
proposition: if it is inhabited, all of its inhabitants agree.

Classically, a sieve $R$ on $U$ is a collection of arrows into $U$ such that

$$
p\in R, q:W\longrightarrow V
\quad\Longrightarrow\quad
p\circ q\in R.
$$

The presheaf formulation replaces the collection by a subterminal value at
every probe. Write $R(p)$ for the coefficient at $p:V\to U$. Its object
classifier is the proposition

$$
p\in R.
$$

The action of the underlying higher sieve carries a witness of $p\in R$ to a
witness of $p\circ q\in R$. Closure under refinement is therefore not an
extra law written beside the data. It is the functorial action of the data.

Why require a *subterminal category* rather than merely proposition-valued
objects? Because a category with a unique object can still have many directed
endomorphisms. Ordinary membership is intended to retain no such hidden
motion. The active condition combines proposition-valued objects with exact
groupoidality, leaving the categorical analogues of the empty and terminal
possibilities. The evidence that a coefficient is subterminal is itself a
proposition, so it does not create competing ways for one arrow to belong.

Two examples orient the definition.

1. The maximal sieve contains every arrow into $U$. Its membership proposition
   is always inhabited.
2. If a monomorphism $j:W\to U$ is regarded as a subobject, it determines the
   sieve of arrows $p:V\to U$ that factor through $j$. Monicity makes the
   factorization proposition-valued. Refining a factorization gives another
   factorization automatically.

The second example is important but not exhaustive. A sieve need not be
represented by one monomorphism. It can be a genuinely distributed local
question whose answer is stable under refinement without having a single
object that names all affirmative probes.

## 18.4 Pulling Back A Local Question

Suppose $R$ is a sieve on $U$ and $p:V\to U$. To ask the same question over
$V$, test every $q:W\to V$ after postcomposition with $p$:

$$
q\in p^*R
\quad:\!\!\Longleftrightarrow\quad
p\circ q\in R.
$$

This defines a sieve $p^*R$ on $V$. Indeed, if $q$ belongs and
$r:Z\to W$, then

$$
p\circ(q\circ r)=(p\circ q)\circ r
$$

belongs by closure of $R$. More conceptually, the higher-sieve action already
postcomposes every probe with $p$. Pointwise subterminality is preserved by
selecting the old witness at that postcomposed probe. Ordinary pullback is
therefore inherited structure, not a separately engineered operation.

**Theorem 18.1 (pullback of ordinary sieves).** For every sieve $R$ on $U$
and arrow $p:V\to U$, there is an ordinary sieve $p^*R$ on $V$. Its
underlying higher sieve is the higher pullback of the underlying higher sieve
of $R$, and membership at $q:W\to V$ is old membership at
$p\circ q:W\to U$.

<!-- evidence:ORDINARY-SIEVE-PULLBACK -->

> **Formal status — checked.** Evidence `ORDINARY-SIEVE-PULLBACK`. The active
> construction supplies the pullback sieve, reuses the whole higher-sieve action,
> preserves subterminal evidence, and exposes the membership computation.
> Because an ordinary sieve retains proof fields, identity pullback is not
> claimed to reconstruct the entire package by raw definitional reduction;
> this does not change the membership formula above.

Pullback is the reason sieves are the right language for locality. A property
stated only at $U$ can be accidental. A sieve records in advance how the
property appears after every change of stage. A topology will later decide
which such stable questions count as *covering* questions, but the variance
has already been settled.

Represented sieves make this calculation visible as ordinary base change.
Suppose the sieve $R$ is represented by a monomorphism $j:A\to U$, and
suppose the pullback square

$$
\begin{array}{ccc}
A\times_U V & \longrightarrow & A\\
\downarrow & & \downarrow j\\
V & \xrightarrow{p} & U
\end{array}
$$

exists. A probe $q:W\to V$ belongs to $p^*R$ exactly when
$p\circ q$ factors through $j$. By the universal property of the pullback,
this is exactly when $q$ factors through $A\times_U V\to V$. Hence $p^*R$
is represented by the base-changed monomorphism.

This is the bridge between sieve pullback and the usual restriction of an
open. The sieve calculation requires only postcomposition and membership. The
spatial calculation additionally requires a representing monomorphism and
the relevant pullback. When those hypotheses are available, the two
descriptions agree; when they are not, the sieve calculation still makes
sense.

## 18.5 Invertibility Before Opens

Let $\mathcal O$ be a presheaf of commutative rings on $\mathcal K$, let
$U$ be a stage, and let $s\in\mathcal O(U)$ be a section. For a probe
$p:V\to U$, restriction produces

$$
p^*s\in\mathcal O(V).
$$

Define the **invertibility sieve** of $s$ by

$$
D_U(s)(p)
\;:=\;
\text{“$p^*s$ is a unit in $\mathcal O(V)$.”}
$$

This is a sieve because ring homomorphisms preserve units. If $p^*s$ has an
inverse and $q:W\to V$, applying the restriction homomorphism along $q$
gives an inverse for $(p\circ q)^*s$. Thus invertibility propagates toward
finer probes.

<!-- evidence:COMM-RING-INVERTIBILITY-SIEVE -->

> **Formal status — checked.** Evidence
> `COMM-RING-INVERTIBILITY-SIEVE`. For a selected commutative-ring-valued
> presheaf and section, the active construction supplies an ordinary sieve, and
> membership at $p:V\to U$ computes to unit evidence for the restricted
> section $p^*s$.

The notation $D_U(s)$ is familiar from algebraic geometry, but the order of
ideas matters. We have not first constructed an open object and then asked
which probes land in it. We first have the stable family of all invertibility
probes. The question whether that family is represented by an open object is
asked afterward.

This reverses a habitual abbreviation. In settings where basic opens are
already known to exist, one says “the open on which $s$ is invertible.” The
sieve formulation separates two claims hidden in that phrase:

1. invertibility is stable under change of stage, so it defines $D_U(s)$; and
2. the sieve $D_U(s)$ is represented by a suitable open object over $U$.

The first statement is formal and functorial. The second depends on the
geometry of the site. In affine geometry, localization will supply the
representing object for a basic invertibility sieve. On a more general site,
there may be no single representative, while the sieve itself remains
perfectly meaningful.

This point also clarifies the relation with Max Zeuner's constructive account
of algebraic geometry. In the locally ringed lattices of
[Zeuner](#ref-zeuner), the invertibility support of a section is presented as
the largest compact open below $U$ on which that section is invertible. In a
posetal site, such a largest open represents the sieve $D_U(s)$: a probe lies
in the sieve exactly when it factors through that open. Conversely, a compact
open representing $D_U(s)$ has the required largest-property interpretation.

The sieve-centered formulation is therefore a generalization, not a
rejection, of the compact-open one. It asks the useful comparison question:

> When is the invertibility sieve $D_U(s)$ representable by a compact open?

On a coherent or qcqs presentation, representability can recover the compact
geometry emphasized by Zeuner. On an arbitrary site, the sieve remains the
primary object even when that recovery is unavailable. In a higher setting,
one may go further and retain a category of invertibility witnesses before
subterminality is imposed.

The posetal case makes the comparison exact. Regard a lattice of opens below
$U$ as a category, with one arrow $V\to W$ when $V\leq W$. If an open
$A\leq U$ represents $D_U(s)$, then for every $V\leq U$,

$$
s|_V\text{ is invertible}
\quad\Longleftrightarrow\quad
V\leq A.
$$

Taking $V=A$ shows that $s|_A$ is invertible. Taking any $V$ on which $s$
is invertible shows $V\leq A$. Thus $A$ is the largest invertibility open.
Conversely, if a largest such $A$ exists, invertibility is preserved by
restriction, so precisely the opens below $A$ belong to $D_U(s)$. The largest
open represents the sieve. Compactness is a further finiteness property of
that representative, important in coherent algebraic geometry but not needed
to define membership.

The distinction separates existence from use. One can calculate with
$D_U(s)$, pull it back, and ask whether it covers before finding a representing
open. Once a compact representative is constructed, the same sieve acquires
the economical lattice presentation. The two layers reinforce rather than
compete with one another.

> **Formal status — mathematical development.** The comparison with Zeuner's
> compact-open support is an attributed reformulation of the representation
> problem, principally adapted from his definition of locally ringed lattices
> and his functor-of-points development. The active emdash result in this
> chapter is the ordinary invertibility sieve. No theorem identifying the
> general emdash site-relative scheme interface with Zeuner's qcqs schemes is
> claimed here.

## 18.6 Categorical Semantics As Executable Mathematics

Presheaves, slices, and sieves are often introduced as an external semantics
for some other formal language. That is not the only way to make them
computational. In the emdash architecture, the categories and functors just
described are themselves expressed in an inner functorial type theory. They
are ordinary mathematical objects of that theory: a presheaf is a functor, a
slice is a category, and pullback is functorial reindexing.

The inner theory is hosted in an outer dependent logical framework. Lambdapi,
or the bounded TypeScript emdash Core, supplies explicit binders, checking,
rewrite computation, comparison, and unification. Consequently, categorical
semantics can be internal enough to calculate with while remaining
recognizably the traditional semantics of presheaves and sites.

This is a claim about relative internality, not about replacing every modal
or internal language. A modal type theory may provide elegant syntax for
local reasoning. Here the chosen route is to make the categorical objects
themselves executable and then state locality directly in them. The advantage
for the present development is transparency: the probe, its refinement, the
sieve pullback, and later the matching family remain visible mathematical
data.

Nor does executability settle the metatheory. Local computations accepted by
the outer framework do not by themselves prove global normalization,
confluence, consistency, or semantic soundness for the combined rewrite
system. The categorical constructions and their checked observations are the
evidence used here; the larger metatheorems retain their separate boundary.

## 18.7 From Sieves To Covers

A sieve answers a local question. It does not yet say that the affirmative
probes are sufficient to recover information on $U$. For that, one must
select the sieves that count as covers and demand three kinds of stability:
the maximal sieve covers, a covering sieve remains covering after pullback,
and covers may be refined locally.

Those laws turn a category into a site. They also prepare a more delicate
question. Given compatible observations on every probe in a covering sieve,
when do they determine one observation on $U$? That is descent, and its
objects are matching families and their amalgamations.

The next step in the local-to-global spiral therefore does not abandon the
sieve for an open. [Chapter 19](#chapter-19) asks which sieves cover, and what
it means for a presheaf to solve every covering question. Geometry will emerge
from the answers, but the questions already have their correct functorial
shape.
