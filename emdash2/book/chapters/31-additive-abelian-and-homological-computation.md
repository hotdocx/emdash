<a id="chapter-31"></a>

# 31. Additive, Abelian, And Homological Computation

How can a connecting homomorphism be computed while keeping the universal
properties that explain it? An element chase suggests a procedure: choose a
preimage, apply a differential, lift into a subobject, and pass to a quotient.
Each instruction conceals a mathematical obligation. A preimage may exist
only after an epimorphic cover; a lift must respect relations; a quotient map
requires an annihilation equation. The choices must also agree with the
homology objects already in use.

The answer developed here makes these obligations internal. A universal
factor consists of an arrow and its reconstruction path. Contractibility
selects such a factor and compares it with every competitor. Addition allows
one to correct a candidate by a difference; monic and epic cancellation then
turn local reconstructions into global equations. These operations suffice
for the checked six-term snake theorem.

The same constructions have an executable interpretation in polynomial
Freyd categories. There the result is a bounded long exact sequence with
retained maps, equations, and exactness witnesses. Its formal reconstruction
retains the same raw chain spine and constructs homology and exactness at
every interior position, relative to explicitly adopted equations and
selected-provider semantics. This result is distinct from the generic
homology-window theorem, whose formal proof remains in progress.

## 31.1 Addition Belongs To The Homs

A preadditive category has a set-valued abelian group
$\operatorname{Hom}_C(A,B)$ for every pair of objects, and composition is
bilinear. Thus parallel arrows can be added and subtracted, and

$$
h\circ(f+g)=h\circ f+h\circ g,
\qquad
(f+g)\circ k=f\circ k+g\circ k.
\tag{31.1}
$$

There is a zero arrow for every ordered pair of objects. Composing a zero
arrow on either side gives zero. The set-valued hypothesis concerns these
particular Homs; it does not impose a global truncation on the ambient
functorial type theory.

To obtain an additive category, supply the selected cartesian structure of
[Chapter 30](#chapter-30). A binary product becomes a biproduct. If its
projections are $p_A,p_B$, define the injections by

$$
\iota_A=\langle\operatorname{id}_A,0\rangle,
\qquad
\iota_B=\langle0,\operatorname{id}_B\rangle.
$$

The product laws give the four projection–injection equations, and
bilinearity gives

$$
\iota_A\circ p_A+\iota_B\circ p_B
=\operatorname{id}_{A\oplus B}.
\tag{31.2}
$$

Consequently arrows out of the same object $A\oplus B$ are assembled by
$f\circ p_A+g\circ p_B$. Product and coproduct are two universal uses of
this selected object. No equality between independently chosen objects is
needed. The chosen terminal object is also initial: its identity is zero,
which forces every arrow from it to be the corresponding zero arrow. We
therefore write this object as $0$.

Finite-free modules give a concrete model. Direct sum supplies the product,
rank zero supplies the zero object, and matrix addition supplies the Hom
groups. This explains why block matrices become useful later: they express
operations already available in any additive category.

<!-- evidence:ADDITIVE-HOM-BIPRODUCTS -->

> **Formal status — checked.** Evidence `ADDITIVE-HOM-BIPRODUCTS`.
> `PreadditiveCategory` supplies the abelian Hom structures and bilinearity;
> `AdditiveCategory` combines them with selected cartesian structure. The
> biproduct and initial-zero consequences are derived. The finite-free and
> Freyd additive instances reuse their existing matrix and quotient owners.

## 31.2 Kernels And Cokernels As Internal Factor Spaces

Fix an arrow $d:B\to D$. A kernel test consists of an arrow $h:T\to B$
and a path $d\circ h=0$. For a proposed kernel embedding $k:Z\to B$,
the factors of that test form the internal space

$$
\sum_{u:T\to Z}(k\circ u=h).
\tag{31.3}
$$

A selected computational kernel retains $Z$, $k$, the annihilation path
$d\circ k=0$, and a contraction of (31.3) for every test. Its center gives
the lift $u$ together with the reconstruction. Its contraction supplies
uniqueness when another arrow has the same reconstruction.

This is an instance of the ordinary internal Hom fibre. More generally,
postcomposition by $k$ has a fibre over any $h$, whether or not a kernel is
involved. Precomposition has the dual fibre: given $q:B\to Q$ and
$h:B\to T$, its points are arrows $v:Q\to T$ with $v\circ q=h$.
A cokernel of $d:A\to B$ makes these latter fibres contractible whenever
$h\circ d=0$.

The quantifier over tests matters. Recording $d\circ k=0$ says that $k$
is a candidate cone. An effective weak kernel additionally supplies a factor
for every annihilated test. A genuine computational kernel supplies the
contractible factor spaces, including uniqueness. A finite list of successful
tests does not provide this all-test operation.

These packages also explain how choices are compared. Two supplied kernels
of the same arrow factor through each other. Uniqueness identifies the two
composites with identities, producing an isomorphism with both inverse laws.
The same argument applies to cokernels. Later constructions can therefore
retain a supplied choice and compare it with another, instead of replacing
its object silently.

<!-- evidence:INTERNAL-KERNEL-COKERNEL-FACTORS -->

> **Formal status — checked.** Evidence
> `INTERNAL-KERNEL-COKERNEL-FACTORS`. `HomPostcompFactor` and
> `HomPrecompFactor` are transparent internal fibres.
> `ComputationalKernel` and `ComputationalCokernel` supply selected factors,
> reconstruction, and uniqueness. The map/isomorphism owners construct
> comparisons between supplied universal objects.

The associated equations are theorem-level paths. Projecting a constructed
pair computes by the existing pair calculus; arbitrary reconstruction and
uniqueness are consumed as equality evidence. This distinction allows the
new Abelian constructions to remain transparent definitions without adding
their own rewrite or unification rules.

## 31.3 Normality And The Image Comparison

A pre-Abelian capability combines additive structure with selected kernels
and cokernels. Abelian structure adds the normal universal operations. For a
monomorphism $m:A\to B$, an arrow $h:T\to B$ killed by the selected
cokernel of $m$ has a selected lift through $m$. Dually, an arrow out of the
source of an epimorphism descends through it when it kills its selected
kernel.

Monicity and epicity themselves are cancellation operations. They consume
equalities after postcomposition or precomposition and return equalities of
the original arrows. Normality supplies additional existence data. In
particular, knowing that $m$ is monic does not establish the cokernel-zero
test required to lift a given $h$.

For $f:A\to B$, form

$$
\operatorname{Coim}(f)=\operatorname{Coker}(\operatorname{Ker}(f)),
\qquad
\operatorname{Im}(f)=\operatorname{Ker}(\operatorname{Coker}(f)).
$$

Kernel and cokernel universality construct a comparison $\chi_f$ and a
factorization

$$
A\xrightarrow{p_f}\operatorname{Coim}(f)
\xrightarrow{\chi_f}\operatorname{Im}(f)
\xrightarrow{i_f}B,
\qquad f=i_f\circ\chi_f\circ p_f.
\tag{31.4}
$$

The factorization already exists at the pre-Abelian boundary. With Abelian
normality, the comparison is proved monic and epic. A monic epic arrow has
an inverse: lift its codomain identity through the monomorphism, using
epicity to establish the normal test, and use cancellation for the other
inverse law. Applying this construction to $\chi_f$ gives the coimage–image
isomorphism.

This formulation retains the two objects and the comparison between them.
The isomorphism is computed from universal operations and cancellation;
there is no identification of independently selected image and coimage
objects by fiat.

<!-- evidence:ABELIAN-NORMALITY-IMAGES -->

> **Formal status — checked.** Evidence `ABELIAN-NORMALITY-IMAGES`.
> `ComputationalAbelianCategory` retains one pre-Abelian capability and its
> normal lift/colift families. The image, image-bimorphism, and bimorphism
> owners derive (31.4) and the comparison isomorphism. These generic
> capabilities remain explicit when passed to a concrete implementation.

## 31.4 Homology Retains Its Cycles And Boundary

Consider a chain pair

$$
A\xrightarrow{d_{n+1}}B\xrightarrow{d_n}D,
\qquad d_n\circ d_{n+1}=0.
$$

Select the cycles as the kernel $k_n:Z_n\to B$ of $d_n$. The chain law is
exactly the test required to lift $d_{n+1}$ into this kernel. Write the
resulting boundary arrow as $b_n:A\to Z_n$. Homology is its selected
cokernel:

$$
k_n\circ b_n=d_{n+1},
\qquad
q_n:Z_n\longrightarrow H_n,
\qquad q_n\circ b_n=0.
\tag{31.5}
$$

The whole homology result retains these universal objects and their
reconstructions. Its cycle object, boundary, homology object, and projection
are observations of that result. Supplying a whole homology value therefore
fixes the cycle kernel as well as the final quotient.

A map of chain pairs is represented by a middle component $f:B\to B'$
and two existing Hom-factor points. Their arrows supply the neighboring
components; their reconstruction paths give the familiar chain-map
compatibilities. The lower compatibility makes $f\circ k_n$ land in the
target cycles, so kernel universality constructs a cycle map $z$. The upper
compatibility and kernel uniqueness then show that $z$ preserves boundaries.
Cokernel universality gives the induced homology map, characterized by

$$
H_n(f)\circ q_n=q'_n\circ z.
\tag{31.6}
$$

Identity and composition laws follow from the same uniqueness arguments.
They compare maps between the supplied homologies. Other choices of whole
homology receive comparison isomorphisms, preserving the distinction between
an invariant object up to isomorphism and the particular object used in a
calculation.

<!-- evidence:SELECTED-HOMOLOGY-MAPS -->

> **Formal status — checked.** Evidence `SELECTED-HOMOLOGY-MAPS`.
> `ComputationalHomologyAt` retains the actual cycle kernel and boundary
> cokernel. The chain-pair-map and homology-map owners construct the cycle
> action, boundary compatibility, induced map, and its laws. A separately
> packaged internal category-of-complexes homology functor is a further
> construction; the checked map laws do not assert that package implicitly.

## 31.5 Exactness Is A Property Of The Actual Boundary

For $A\xrightarrow{i}B\xrightarrow{p}D$ with zero composite, let
$b:A\to\operatorname{Ker}(p)$ be the boundary in the chosen homology.
Exactness at $B$ is the statement that this $b$ is epic. The definition uses
the actual kernel factor and its cancellation operation. A short exact row
additionally retains monicity of $i$ and epicity of $p$.

In an Abelian category, this definition admits the following useful local
description. Every $h:T\to B$ with $p\circ h=0$ factors through $i$ after
an epimorphic cover: there are $e:T'\to T$, epic, and $a:T'\to A$ with

$$
h\circ e=i\circ a.
\tag{31.7}
$$

If $b$ is epic, pull it back along the kernel lift of $h$ to obtain these
data. Conversely, apply such a family of covers to the kernel embedding.
The resulting factor and the epic cover prove that the original boundary
$b$ is epic. This is a constructive replacement for choosing an elementwise
preimage in a diagram chase.

There is also a sufficient dual criterion. A test $h:B\to T$ killed by
$i$ can be extended through $p$ after a monomorphism $m:T\to U$:

$$
m\circ h=a\circ p
\qquad(a:D\to U).
\tag{31.8}
$$

A family of these extensions proves the same exactness property. The
checked development uses this direction on the cokernel side of the snake
proof; it does not claim a separately packaged equivalence for the dual
criterion.

For a short exact row, its source is isomorphic to the selected kernel of
its projection, and the selected cokernel of its inclusion is isomorphic to
its target. The first forward map is the original boundary $b$. The second
inverse lands in that cokernel. Neither comparison chooses a section of
the projection into the middle object. This matters already for the
polynomial row $0\to R\xrightarrow{x}R\to R/(x)\to0$.

<!-- evidence:SELECTED-EXACTNESS-COVERS -->

> **Formal status — checked.** Evidence `SELECTED-EXACTNESS-COVERS`.
> `ComputationalExactAt` is indexed by the supplied whole homology.
> The exactness-cover owners prove the local-cover equivalence; the
> extension owners prove the sufficient dual criterion. Short-exact
> comparison isomorphisms retain the original boundary and quotient factors.

## 31.6 Fibre Products, Pushouts, And Stability

The cover argument requires genuine fibre products. Given $f:X\to Z$ and
$g:Y\to Z$, form the difference arrow

$$
[f,-g]:X\oplus Y\longrightarrow Z.
$$

Its selected kernel is a fibre product. Composing the kernel embedding with
the biproduct projections gives $p:E\to X$ and $q:E\to Y$, with
$f\circ p=g\circ q$. An equalizing pair becomes a kernel test by pairing
its legs. The kernel factor then reconstructs both projections. Replacing
the genuine kernel with a weak kernel gives a weak pullback, with the weaker
factor capability retained explicitly.

The direct dual constructs the pushout of $f:Z\to X$ and $g:Z\to Y$
as the selected cokernel of

$$
\begin{bmatrix}
f \\
-g
\end{bmatrix}:Z\longrightarrow X\oplus Y.
$$

Its injections have the required compatibility, and its cofactor operation
reconstructs both legs of every compatible cocone. The matrix notation is
the biproduct notation of Section 31.1; it does not require a new datatype
for commuting squares.

Abelian normality proves the stability facts needed by the chase. A
pullback projection opposite an epimorphism is epic. A pushout injection
opposite a monomorphism is monic. These properties are derived from the
selected difference kernel or cokernel, its universal factor spaces, and
the normal lift/colift operations. They are available with the same whole
fibre product or pushout that supplies the structural maps.

<!-- evidence:ABELIAN-FIBER-PUSHOUT-STABILITY -->

> **Formal status — checked.** Evidence
> `ABELIAN-FIBER-PUSHOUT-STABILITY`. The computational fibre-product and
> pushout owners construct both reconstructions. The Abelian stability owner
> proves the indicated epicity and monicity. All are transparent
> constructions over the existing additive and universal-property layers.

## 31.7 Constructing The Snake Arrow

The generic snake begins with a particularly small input:

$$
A\xrightarrow{\delta}B\xrightarrow{\beta}X
\xrightarrow{\lambda}D,
\qquad \lambda\circ\beta\circ\delta=0.
\tag{31.9}
$$

Select the cokernel $\epsilon:B\to\operatorname{Coker}(\delta)$ and
the kernel $\mu:\operatorname{Ker}(\lambda)\to X$. Universality gives

$$
\begin{aligned}
\alpha &: A\longrightarrow\operatorname{Ker}(\lambda),
&\mu\circ\alpha&=\beta\circ\delta,\\
\gamma &: \operatorname{Coker}(\delta)\longrightarrow D,
&\gamma\circ\epsilon&=\lambda\circ\beta.
\end{aligned}
\tag{31.10}
$$

The intended connecting arrow goes from $\operatorname{Ker}(\gamma)$ to
$\operatorname{Coker}(\alpha)$. These are new universal constructions on
the induced maps in (31.10), so their identities must be kept visible.
Write $\iota:\operatorname{Ker}(\gamma)\to\operatorname{Coker}(\delta)$
and $\pi:\operatorname{Ker}(\lambda)\to\operatorname{Coker}(\alpha)$
for their structural arrows.

Pull back $\epsilon$ along $\iota$. This gives
$p_1:E\to\operatorname{Ker}(\gamma)$ and $p_2:E\to B$, with
$\iota\circ p_1=\epsilon\circ p_2$. Stability makes $p_1$ epic.
Push out $\mu$ along $\pi$. Its injections $q_1:X\to Q$ and
$q_2:\operatorname{Coker}(\alpha)\to Q$ satisfy
$q_1\circ\mu=q_2\circ\pi$, and $q_2$ is monic.

The existing annihilation and image consequences establish the two normal
tests. Normal-epi colifting first constructs
$u:\operatorname{Ker}(\gamma)\to Q$. Normal-mono lifting then constructs $\partial$ with

$$
u\circ p_1=q_1\circ\beta\circ p_2,
\qquad
q_2\circ\partial=u.
\tag{31.11}
$$

This order explains the role of the cover. There is no chosen section of
$p_1$, and hence no instruction to select a global preimage in $E$.
The normal universal operations descend and lift an arrow only after the
corresponding test has been proved.

There is a useful reconstruction before leaving the cover. The arrow
$\beta\circ p_2$ is killed by $\lambda$, so its selected kernel lift is
$L:E\to\operatorname{Ker}(\lambda)$ with $\mu\circ L=\beta\circ p_2$.
Postcomposing the two candidates below with monic $q_2$, and using
(31.11) and pushout compatibility, proves

$$
\partial\circ p_1=\pi\circ L.
\tag{31.12}
$$

The equality retains the original cover, lift, and connecting arrow. It is
especially useful when the connecting construction must later be compared
with cycles and homology.

<!-- evidence:ABELIAN-SNAKE-CONNECTING -->

> **Formal status — checked.** Evidence `ABELIAN-SNAKE-CONNECTING`.
> `AbelianSnakeTriple` retains (31.9). The connecting-result owner constructs
> both normal factors and their reconstructions. The covered-reconstruction
> owner proves (31.12) by cancelling the existing monic $q_2$; no connecting
> formula, normal test, or factor is postulated.

## 31.8 The Six-Term Exact Sequence

**Theorem 31.1 (selected six-term snake sequence).** In a supplied
computational Abelian category, the triple (31.9) determines the sequence

$$
\begin{aligned}
&\operatorname{Ker}(\alpha)\longrightarrow
\operatorname{Ker}(\beta)\longrightarrow
\operatorname{Ker}(\gamma)\\
&\qquad\xrightarrow{\partial}\operatorname{Coker}(\alpha)\longrightarrow
\operatorname{Coker}(\beta)\longrightarrow
\operatorname{Coker}(\gamma),
\end{aligned}
\tag{31.13}
$$

with four adjacent-zero paths and exactness at its four interior objects.
All maps and exactness witnesses refer to the universal objects selected by
the construction. The input does not assert that the two outer arrows are
monic or epic, so no zero endpoints are added to (31.13).

The kernel-side arrows follow from $\delta$ and $\epsilon$ by kernel
universality; the cokernel-side arrows follow from $\mu$ and $\lambda$ by
cokernel universality. Their reconstruction paths give the four
adjacent-zero equations by cancellation. Exactness then needs a further
argument at each interior object.

At $\operatorname{Ker}(\beta)$, take a test killed by the next arrow.
The canonical cokernel row for $\delta$ gives an epic cover and a
$\delta$-preimage. Equation (31.10) and monicity of $\mu$ force that
preimage into $\operatorname{Ker}(\alpha)$. Kernel uniqueness identifies
the resulting map with the covered test, establishing the local-cover
criterion.

At $\operatorname{Ker}(\gamma)$, pull a test killed by $\partial$ back
along $p_1$. On that cover, its lifted $L$-component is killed by $\pi$.
The canonical cokernel row for $\alpha$ supplies a second epic cover and
an $\alpha$-preimage. Subtracting its $\delta$-image from the covered
$p_2$-leg produces an arrow killed by $\beta$. Its factor through
$\operatorname{Ker}(\beta)$ reconstructs the test after both covers.
Composition of those covers completes the proof.

The two cokernel positions use the extension criterion. At
$\operatorname{Coker}(\alpha)$, push out $q_2$ along a test killed by
$\partial$, then use a canonical kernel-row extension. A corrected
difference kills $\beta$ and descends through its cokernel. Epic
cancellation identifies the resulting coextension. At
$\operatorname{Coker}(\beta)$, a test killed by the incoming arrow
extends through $\lambda$ after a monomorphism; the reconstruction for
$\gamma$ makes it descend through $\operatorname{Coker}(\gamma)$.

The result stores the six-term snapshot together with exactness evidence
indexed by that snapshot. This dependency is part of the theorem: a proof
about another pair of arrows cannot be inserted into the result merely
because its object names look similar.

<!-- evidence:ABELIAN-SNAKE-SIX-TERM-EXACT -->

> **Formal status — checked.** Evidence `ABELIAN-SNAKE-SIX-TERM-EXACT`.
> `abelian_snake_six_term_exact_result` constructs
> `AbelianSnakeSixTermExactResult` from the original Abelian capability and
> triple. Its projections recover the canonical five arrows, four zero
> paths, and four exactness instances. This is the generic theorem of this
> chapter; it is independent of the concrete polynomial tests below.

## 31.9 Bounded Complexes And The Homology Connecting Map

A bounded complex retains a finite family of objects and differentials,
together with the adjacent-zero laws. One-degree homology applies to each
neighboring pair. A bounded chain map retains its components and their
compatibilities. A degreewise short exact sequence retains three such
complexes and the existing inclusion and projection maps, with a whole
short exact row in every degree.

For such a sequence $0\to A_\bullet\to B_\bullet\to C_\bullet\to0$,
the homological target is

$$
\cdots\longrightarrow H_n(A)\longrightarrow H_n(B)
\longrightarrow H_n(C)\xrightarrow{\partial_n}H_{n-1}(A)
\longrightarrow\cdots.
\tag{31.14}
$$

The public connecting operation has precisely the homology endpoints in
(31.14). Its present native implementation uses the snake construction as
a method. The two rows at degrees $n$ and $n-1$ give the snake input;
short-exact comparison isomorphisms relate its source to the supplied
cycles of $C$ and its target to the cokernel of the incoming differential
of $A$.

There is a canonical monomorphism

$$
j_A:H_{n-1}(A)\longrightarrow\operatorname{Coker}(d^A_n).
\tag{31.15}
$$

It is induced from the actual cycle embedding and boundary cokernel; its
monicity is a checked generic consequence of pushout stability.

<!-- evidence:HOMOLOGY-COKERNEL-INCLUSION -->

> **Formal status — checked.** Evidence `HOMOLOGY-COKERNEL-INCLUSION`.
> The homology-inclusion owner constructs $j_A$ at the supplied whole
> homology, and `abelian_homology_cokernel_inclusion_monic` proves its
> monicity. It preserves the original cycles and boundary cokernel.

The native method factors the compared snake arrow through $j_A$, then descends
through the source homology projection. If $s$ and $v$ denote the source
and target comparison isomorphisms, its retained reconstruction is

$$
j_A\circ\partial_n\circ q_C=v\circ\partial\circ s.
\tag{31.16}
$$

Both factor operations retain their effective tests. This avoids requiring
a global lift from source cycles into raw target cycles. A different future
algorithm can implement the same homology operation, provided it preserves
the supplied objects and proves the corresponding comparison.

The native polynomial implementation assembles all windows into one bounded
sequence. It constructs each degree's homologies and ordinary induced maps
once, then shares them between neighboring windows. Exactness at $H_n(B)$
and $H_n(C)$ comes from the window at $n$; exactness at $H_n(A)$ comes from
the window at $n+1$. The retained witnesses refer to the actual displayed
adjacent pairs. Outside finite support, the endpoints are the selected
outside-support homologies with explicit zero-object witnesses.

These are also whole operations in the computational category interface.
A retained program declares its kernel, cokernel, normal-factor, and other
prerequisites; compilation lowers the operation to the native algebra
engine. Observations return the stored homologies and windows. Direct and
compiled execution are compared on their complete serialized results.

This operation-and-prerequisite design takes inspiration from
[CAP](#ref-cap-project) and the separation of categorical algorithms from
ring computations in [homalg](#ref-homalg-meta). The native emdash
implementation owns its polynomial algorithms; those reference systems
are not required at runtime.

The examples exercise nonsplit polynomial rows, nonzero boundaries, and
nonzero connecting maps. An independent field-linear calculation over
$\mathbb Q$ compares the results in explicit quotient coordinates,
including connecting maps of both signs and endpoint cases. This comparison
uses constant polynomials, where the coefficient ring is already
$\mathbb Q$. It does not specialize a polynomial variable and assume that
exactness survives such a change of scalars.

> **Formal status — mathematical development.** The generic long exact
> homology theorem (31.14) remains a formalization target. The native
> homology-connecting, window, bounded-long-exact, and categorical-program
> implementations already compute the described selected results.
> Their focused tests and field/quotient-coordinate comparisons provide
> executable evidence, separate from the Lambdapi theorem register. They
> do not supply a generic homology-window or bounded long-exact proof.

The executable reviewers are
`tests/v3_2_algebra_polynomial_freyd_homology_connecting_tests.ts`,
`tests/v3_2_algebra_polynomial_freyd_long_exact_tests.ts`,
`tests/v3_2_algebra_polynomial_freyd_long_exact_category_tests.ts`, and
`tests/v3_2_algebra_polynomial_freyd_long_exact_differential_tests.ts` in the
root workbench. They check selected-object reuse, the full bounded output,
compiled agreement, and the independent coordinate comparisons respectively.

## 31.10 Presentations, Matrices, And Formal Replay

Concrete computation needs an effective representation. A Freyd
presentation over a commutative ring $R$ has a relation map
$\rho_P:R^{r_P}\to R^{p}$. A raw morphism from $P$ to $Q$ retains a
generator matrix $F$ and a relation-coefficient matrix $W$ satisfying

$$
\rho_Q W=F\rho_P.
\tag{31.17}
$$

Equality of represented morphisms has its own witness. Two generator
matrices $F,G$ agree in the quotient when a retained matrix $H$ satisfies
$\rho_Q H=F-G$. The relation witness in (31.17) and this equality witness
have different jobs. The first makes a raw map well formed; the second
compares quotient maps.

For the supported polynomial provider, effective syzygy and membership
operations supply these witnesses. Kernels use the two-weak-pullback Freyd
construction; normal lifts and colifts consume the corresponding explicit
agreements. A successful computational decision supplies data for the next
map. A failed decision remains negative computational information, while an
unsupported operation or exhausted resource does not prove nonexistence.

The formal interface can use a supplied finite-free weak-kernel capability
and explicit raw agreements. This yields the witnessed Freyd universal
operations. It does not decode an arbitrary propositionally truncated
quotient equality into a chosen raw witness. Native effectiveness and this
formal input contract are separate aspects of the implementation.

The constructive Freyd-category account in [Posur](#ref-posur-freyd)
explains why relation witnesses, weak-kernel factor operations and effective
agreement solving must be distinguished. The broader algorithmic setting
is developed in [the homalg axiomatic setup](#ref-homalg-axiomatic).

The proof–CAS workflow first replays a whole selected computation and
compares its complete serialization. It then presents the exact matrix
equations, with fixed coefficient bindings, for explicit adoption into a
proof environment. Running the computation alone changes no proof
assumptions. Adoption is a recorded trust decision; the subsequent typecheck
checks the construction relative to those adopted equations.

Those equations can also be consumed as data. A transparent introduction
packages a retained coefficient matrix and its equation as the original
raw agreement value. The whole inventory can therefore expose its
degreewise, connecting and snake witnesses as typed raw terms, with every
label retained even when identical terms share one representation. This
construction needs no additional trust decision.

<!-- evidence:FREYD-RAW-WITNESS-INTRO -->

> **Formal status — checked.** Evidence `FREYD-RAW-WITNESS-INTRO`.
> The explicit-matrix introduction returns the original raw agreement and
> preserves its coefficient witness. It does not decode a truncated
> quotient equality or turn a literal matrix equation into an unproved
> semantic-composition equation.

The next step now constructs an actual formal raw spine. Each displayed
arrow is built by (31.17) using the original generator and relation data.
For consecutive arrows $F:P_2\to P_1$ and $G:P_1\to P_0$, the retained
equation

$$
\rho_{P_0}H=GF-0
\tag{31.18}
$$

constructs their original Freyd chain-pair agreement. Its right-hand side
is the formal matrix composite, so it addresses the composed arrows in the
term itself. The bounded constructors assemble these morphisms and laws
into one sequence. The displayed left-to-right order is translated into
the formal convention in which index zero names the rightmost object.

The completed term is checked as a whole. This goes beyond checking a list
of equation types: the constructors must fit together at their actual
endpoints, with every projected arrow preserved. It establishes a formal
chain spine. It does not yet establish its exactness.

<!-- evidence:FREYD-FORMAL-RAW-SPINE -->

> **Formal status — checked.** Evidence `FREYD-FORMAL-RAW-SPINE`.
> `comm_ring_presentation_morphism_from_matrices` and
> `comm_ring_freyd_chain_pair_from_matrices` return the existing formal
> owners, which assemble raw morphisms and adjacent-zero agreements through
> the existing bounded constructors. No primitive matrix algorithm, quotient
> decoder, or new Core structure is introduced.

The executable bridge and its trust boundary are reviewed separately in
`tests/v3_2_algebra_formal_freyd_long_exact_tests.ts` and
`tests/v3_2_algebra_formal_freyd_spine_tests.ts`. Their live consumers check
the constructed whole term, including nontrivial bounded and short-tail
cases, relative to the explicitly adopted equations.

## 31.11 What A Boundary-Epicity Witness Proves

At an interior position, the native exactness calculation retains a boundary
$F:P\to Z$. Write $Q$ for the relation matrix of its target presentation
$Z$. Its epimorphism data provide matrices $U,V$ with

$$
QU+FV=\operatorname{id}.
\tag{31.19}
$$

The identity says that every target generator is the sum of a target
relation and a boundary image. The canonical cokernel of $F$ has relation
matrix $[Q\ F]$, so the vertical block satisfies

$$
[Q\ F]\begin{bmatrix}
U \\
V
\end{bmatrix}
=\operatorname{id}.
\tag{31.20}
$$

Thus its cokernel projection agrees with zero. This is exactly the
existing formal Freyd epimorphism witness. The explicit constructor derives
it from (31.19), together with the original relation-preservation law for
$F$; the block identity itself is not an opaque declaration of epicity.

The whole-long-exact consumer applies this construction to each retained
interior boundary. It uses the boundary's own target cycle presentation
and original morphism, reusing an exactly matching relation equation or
explicitly adopting a missing one. It does not rerun homology separately
for each witness. Each resulting epicity term is then checked in the
extended proof environment.

Equation (31.19) proves epicity onto $Z$, but exactness needs more: $Z$
must have the kernel universal property for the outgoing arrow, and $F$
must reconstruct the incoming arrow through its kernel embedding. The
bridge therefore retains the two actual weak pullbacks used to construct
the cycle presentation. Each carries an operation that factors every
admissible test, together with its reconstruction law. Their ranks and
projection matrices are observations of those same packages.

The native factor algorithms are bound to these packages by an explicit
trust decision. A finite collection of matrix equations does not prove the
all-test law. The adopted provider semantics name the represented ring,
the selected data, and the retained factor operation. They are kept distinct
from the computed equations used for individual morphisms and agreements.

This distinction also prevents an invalid change of scalars. Multiplication
by $x$ has zero kernel over $k[x]$, but becomes a zero map after passing to
$k[x]/(x)$. Its selected kernel cannot simply be carried across that
quotient. The polynomial provider is therefore interpreted over its original
coefficient ring. Modules presented by relations over that ring, including
$k[x]/(x)$ as a $k[x]$-module, remain ordinary supported inputs.

<!-- evidence:FREYD-FORMAL-BOUNDARY-EPICITY -->

> **Formal status — checked.** Evidence `FREYD-FORMAL-BOUNDARY-EPICITY`.
> `comm_ring_freyd_epimorphism_from_matrices` constructs
> `CommRingFreydEpimorphismWitness` from the block equation and original
> morphism law. This proves formal epicity relative to the supplied
> equations. The provider and homology constructions below supply the
> separate cycle and boundary data needed to use it as exactness.

The root reviewers
`tests/v3_2_algebra_formal_freyd_epimorphism_tests.ts` and
`tests/v3_2_algebra_formal_freyd_long_exact_epimorphisms_tests.ts` exercise
the explicit-equation bridge and its application to every retained interior
boundary. They separately check original-morphism preservation, adoption
bindings, and the constructed formal witness terms.

With those cycle choices fixed, the homology constructor accepts the
original raw boundary and its reconstruction agreement, then builds the
existing witnessed cokernel of that boundary. It does not replace a raw
relation witness merely because another one represents the same quotient
map. The epimorphism term from (31.19) is then exactness at precisely this
stored boundary.

<!-- evidence:FREYD-SELECTED-HOMOLOGY-EXACTNESS -->

> **Formal status — checked.** Evidence
> `FREYD-SELECTED-HOMOLOGY-EXACTNESS`. The selected-kernel and homology
> constructors retain the two weak pullbacks, their universal operations,
> the supplied raw boundary, its reconstruction, and its cokernel. The
> exactness introduction reuses the existing epicity witness at that same
> boundary; it adds no opaque exactness theorem.

The whole-result consumer performs this construction at every retained
interior position. One proof environment contains the original spine and
the homology/exactness terms for each displayed pair. The two-degree
nonsplit example checks the spine and all twelve interior terms together,
without another kernel or homology selection. The executable reviewers are
`tests/v3_2_algebra_formal_freyd_actual_homology_tests.ts` and
`tests/v3_2_algebra_formal_freyd_long_exact_homology_tests.ts`.
Their conclusion is relative to the recorded equation and provider
assumptions, not a generic theorem about arbitrary Abelian categories.

## 31.12 The Remaining Universal Obligations

The generic homology-window proof must still connect the theorem of
Section 31.8 to the actual homologies in (31.14). The checked row
comparisons and monic inclusion (31.15) provide its endpoints. To factor the
compared snake arrow through that inclusion, one must prove the required
normal test. To descend through $q_C$, one must prove annihilation of the
actual source boundary. The neighboring chain laws and degreewise
monic/epic maps enter these arguments; the two snake rows alone do not
supply all of them. Exactness at the three positions of the homology window
and its generic bounded iteration then require their own proofs.

> **Formal status — research boundary.** Generic homology-window and
> bounded long-exact exactness remain open in the formal development.
> Formal exactness at all interior positions of the selected native spine
> is already reconstructed relative to its explicit provider semantics.
> The checked generic snake theorem, selected-result construction, and
> prospective generic long-exact theorem have different hypotheses and
> conclusions.

A possible later computation mode would represent a universal diagram and
solve its witness equations once. To turn that calculation into a theorem
about arbitrary Abelian categories, it would also need an encoding of the
premise and an exact-functor interpretation. Adding zero-composition
relations alone does not encode exactness hypotheses. Rational examples
cannot serve as universal instances for categories with integral torsion.

Such a mode would also require its own category constructor. A one-sided
Freyd presentation, an image/subquotient representation, and a free Abelian
Adelman construction have different data and computational hypotheses.
Likewise, a generalized inverse in a relation calculus must be shown to
recover an ordinary arrow before it can replace a lift in the present
interface. These are prospective comparisons with the retained construction,
not completed layers of the kernel.

The relevant reference distinctions are developed in Posur's
[constructive methods](#ref-posur-methods),
[image completion](#ref-posur-images), and
[free Abelian categories for theorem proving](#ref-posur-free-abelian).

> **Formal status — research boundary.** Universal-diagram solving and
> generalized-morphism compilation are future interfaces. Their
> interpretation, effective solving capabilities, and recovery of ordinary
> arrows are additional obligations. The current concrete Freyd provider
> remains an executable model with explicitly recorded trust and selection
> boundaries.
