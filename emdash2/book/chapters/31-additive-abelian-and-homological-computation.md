<a id="chapter-31"></a>

# 31. Additive, Abelian, And Homological Computation

How can a connecting homomorphism be computed while keeping the universal
properties that explain it? An element chase suggests a procedure: choose a
preimage, apply a differential, lift into a subobject, and pass to a quotient.
Each instruction conceals a mathematical obligation. A preimage may exist
only after an epimorphic cover; a lift must respect relations; a quotient map
requires an annihilation equation. The choices must also agree with the
homology objects already in use.

The answer developed here has two complementary levels. Internal factor
spaces give the selected lifts, quotients and reconstruction laws needed
by a constructive chase. Coherent kernel and cokernel presentations make
these operations whole functors. Their adjunctions then build homology as
a whole functor on an existing category of zero-composition diagrams.
Addition and monic/epic cancellation supply the exactness arguments; actual
transformations retain the naturality of the resulting operations.

The same constructions have an executable interpretation in polynomial
Freyd categories. There the result is a bounded long exact sequence with
retained maps, equations, and exactness witnesses. Its formal reconstruction
retains the same raw chain spine and constructs homology and exactness at
every interior position, relative to explicitly adopted equations and
selected-provider semantics. The generic five-term homology window and its
three interior exactness results are also checked, as is finite iteration
over coherent rows. Attaching the final symbolic zero-endpoint theorem to
the conventional bounded display remains a separate, deferred interface.
The formal-status notes describe the current research calculus, with the
foundational qualifications recorded in [Appendix F](#appendix-status).

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
factor computes; arbitrary reconstruction and uniqueness are consumed as
equality evidence. These factor spaces are the operational interface to
universality, not a requirement that every later construction be assembled
as an isolated arrow calculation.

For coherent families, use the arrow-diagram category
$\mathcal D_C=\operatorname{Functor}(\mathbf 2,C)$, where $\mathbf 2$ is
the walking arrow. The zero object gives whole functors

$$
J(A)=(A\longrightarrow0),\qquad
I(A)=(0\longrightarrow A).
$$

A kernel presentation supplies a whole $K:\mathcal D_C\to C$ and an
adjunction $J\dashv K$ over the original selected kernels. A cokernel
presentation supplies $Q:\mathcal D_C\to C$ and $Q\dashv I$ over the
original selected cokernels. Evaluating their counit and unit gives the
kernel embedding and cokernel projection. Transposition gives the universal
lifts and colifts. Thus the adjunction and factor-space descriptions are
two interfaces to the retained universal operations.

The presentation includes coherent structure: it is not an automatically
constructed witness for every previously supplied kernel or cokernel family.
Proof-time usability relates its observations to those original choices,
while the whole functor heads remain available for the generic adjunction
cuts. Conversely, the adjunctions supply operational universal records at
their actual objects, so a later construction need not move between two
independently selected kernels merely to use universality.

<!-- evidence:WHOLE-KERNEL-COKERNEL-PRESENTATIONS -->

> **Formal status — checked.** Evidence
> `WHOLE-KERNEL-COKERNEL-PRESENTATIONS`. The two presentation classifiers
> supply actual functors and adjunctions, with object, structural-arrow and
> map usability for the original selections. Their mate and record interfaces
> retain the universal factors. Existence of a coherent presentation remains
> an explicit input, not a consequence inferred from finite matrix tests.

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

## 31.4 Whole Homology Retains Its Cycles And Boundary

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

These constructions give a useful selected-record interface. Its map laws
follow from uniqueness and compare maps between the supplied homologies.
Other choices receive comparison isomorphisms, preserving the distinction
between an invariant up to isomorphism and the particular object used in
a calculation.

<!-- evidence:SELECTED-HOMOLOGY-MAPS -->

> **Formal status — checked.** Evidence `SELECTED-HOMOLOGY-MAPS`.
> `ComputationalHomologyAt` retains the actual cycle kernel and boundary
> cokernel. The chain-pair-map and homology-map owners construct the cycle
> action, boundary compatibility, induced map, and its laws. The whole
> functor below supplies the primary interface for coherent families.

Now let a category $\mathcal B$ parameterize the data. Supply actual functors
$A:\mathcal B\to C$ and $D:\mathcal B\to\mathcal D_C$, together with an
actual transformation $h:J\circ A\Rightarrow D$. The kernel adjunction
constructs the boundary transformation directly:

$$
\beta=K(h)\circ\eta_A:A\Longrightarrow K\circ D.
$$

At a point this is precisely the lift of the incoming differential into
cycles. But the formula is already a composition of whole transformations;
there is no additional family of naturality squares to supply. Introducing
its walking-arrow diagram gives a functor
$\operatorname{Arr}(\beta):\mathcal B\to\mathcal D_C$. Define

$$
H_{A,D,h}=Q\circ\operatorname{Arr}(\beta):\mathcal B\longrightarrow C.
$$

This is a derived whole functor, not a new primitive homology algorithm.
Its identity and composition computations are the existing generic functor
computations, including the accumulation direction
$H(g)\circ H(f)\longrightarrow H(g\circ f)$. Its Hom actions remain
available at further dimensions. The selected-record views recover its
actual cycles, boundary and quotient; in particular, the record's homology
object is the original $H[b]$, not a replacement object reached by transport.

There is also one native source for these coherent diagrams:

$$
\mathcal Z_C=(J\downarrow\operatorname{id}_{\mathcal D_C}).
$$

This uses the existing internal Hom-comma construction. An object is
$(A,d,h)$ with $h:J(A)\Rightarrow d$. Its source component is the incoming
arrow; naturality and the zero-object property give the zero composite with
the differential of $d$. Maps and their compatibility come from the native
Hom structure, not a newly introduced datatype of hand-written commuting
squares. In the ordinary-target profile used here, where $C$ is used as a
one-category, the tautological whole transformation is available. Applying
the preceding family construction to
it gives $H:\mathcal Z_C\to C$.

This is whole one-degree homology on zero-composition diagrams. It is not a
claim that every possible category of bounded or unbounded complexes, or a
global graded homology functor, has already been packaged. The local
ordinary-target hypothesis and the two coherent presentations stay explicit;
the polynomial Freyd interface fills its ordinary-target profile from its
existing set-valued Hom presentation.

<!-- evidence:WHOLE-HOMOLOGY-FUNCTOR -->

> **Formal status — checked.** Evidence `WHOLE-HOMOLOGY-FUNCTOR`.
> `homology_family_func` derives the whole functor; its boundary is an actual
> transformation. `zero_arrow_cone_homology_func` specializes it to the
> native source with the ordinary-target profile. The family-record
> projection returns the same H object. Reviewers exercise nonidentity
> action, generic identity/composition and further Hom action.

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
> paths, and four exactness instances. This generic snake theorem is
> independent of the concrete polynomial tests below.

## 31.9 Exact Homology Windows And Bounded Assembly

A bounded complex retains a finite family of objects and differentials,
together with the adjacent-zero laws. A degreewise short exact sequence
retains three such complexes and their inclusion and projection maps, with
a short exact row in each degree. In the coherent formal interface, the
rows are whole functors into the native zero-cone category and their maps
are actual transformations. Four consecutive rows provide one homology
window; shifting the window reuses three of those rows.

**Theorem 31.2 (selected homology window).** In an ordinary-target
computational Abelian category with supplied coherent kernel and cokernel
presentations, such a window determines

$$
\begin{aligned}
H_n(A)&\xrightarrow{H(i_n)}H_n(B)\xrightarrow{H(p_n)}H_n(C)\\
&\xrightarrow{\partial_n}H_{n-1}(A)
\xrightarrow{H(i_{n-1})}H_{n-1}(B).
\end{aligned}
\tag{31.14}
$$

The three adjacent composites are zero, and the sequence is exact at its
three interior objects. Its homologies are the actual whole-H observations
of Section 31.4. No replacement homology object or endpoint transport is
needed to state the connecting map.

Here is the constructive idea behind the direct connecting operation.
Pull back the row projection $p_n:B_n\to C_n$ along the actual cycle
embedding $k_C:Z_n(C)\to C_n$. Write its legs as
$e:E\to Z_n(C)$ and $b:E\to B_n$, so
$p_n b=k_C e$; the first leg is epic. Applying the middle differential
to $b$ gives an arrow killed by the next row projection. That row's
kernel property lifts it through its original inclusion into $B_{n-1}$.
The following chain law and monicity then force this lift into the actual
cycles of $A$. Write the resulting cycle arrow as
$c:E\to Z_{n-1}(A)$.

The normal universal operations descend $q_Ac$ along the cover, and the
upper neighboring row proves that the resulting map kills the source
boundary. Cokernel universality therefore gives $\partial_n$, with

$$
\partial_n\circ q_C\circ e=q_A\circ c.
$$

All tests needed for these operations are derived. The caller does not
provide a section of $e$, a connecting arrow, or extra normal-test
equations. Since $q_C\circ e$ is epic, the covered formula also
characterizes the resulting arrow.

The exactness proofs use the same cover-and-correction method. At
$H_n(B)$, represent a test by a middle cycle after an epic cover. Its
projection is a boundary; lift a boundary preimage through the upper row,
then subtract its middle differential. The corrected cycle has zero
projection and hence comes from the left column.

At $H_n(C)$, a class killed by $\partial_n$ has a covered lift whose
left-column cycle is a boundary. Subtract the corresponding inclusion
from its middle-column lift. The corrected lift is a middle cycle and
reconstructs the original class under $H(p_n)$.

At $H_{n-1}(A)$, a class killed by $H(i_{n-1})$ becomes a middle
boundary after a cover. Projecting a boundary preimage to the right column
gives a cycle. The covered connecting formula sends its class back to the
original left-column class. These all-test constructions establish the
three exactness predicates at the same H objects.

<!-- evidence:HOMOLOGY-DIRECT-CONNECTING -->
<!-- evidence:HOMOLOGY-WINDOW-EXACTNESS -->

> **Formal status — checked.** Evidence `HOMOLOGY-DIRECT-CONNECTING` and
> `HOMOLOGY-WINDOW-EXACTNESS`. The direct connecting factor, source-boundary
> descent and covered reconstruction are constructed at the retained
> homologies. The first, second and third window owners prove all three
> interiors; `homology_whole_exact_window` packages those original witnesses.
> These are generic formal results, not deductions from polynomial examples.

Naturality is also a whole interface. For a window family over
$\mathcal B$, let $R,L:\mathcal B\to\mathcal Z_C$ be its right and left
vertical zero-diagram functors in degrees $n$ and $n-1$, respectively.
Composing them with H gives the source and target homology functors.
The connecting interface is an actual transformation

$$
\partial_w:H\circ R\Longrightarrow H\circ L.
$$

Its component observation computes to the direct connecting construction.
Generic transfor action supplies the naturality and further Hom-action
interfaces; no separately supplied naturality square or transformation
constructor is part of the input. Whole column observations retain the
original row functors, with proof-time comparisons for the alternative
Hom-action projection order.

<!-- evidence:HOMOLOGY-CONNECTING-TRANSFORMATION -->

> **Formal status — checked.** Evidence
> `HOMOLOGY-CONNECTING-TRANSFORMATION`. The whole source and target are
> composites with the original H. `homology_window_connecting_transf`
> has the retained component computation and ordinary off-diagonal/higher
> transfor action. The whole transformation is present from the outset;
> pointwise naturality proofs are not additional caller inputs.

The native implementation retains a snake-based trace of the same public
homology operation. A useful comparison in that trace is the canonical
monomorphism

$$
j_A:H_{n-1}(A)\longrightarrow\operatorname{Coker}(d^A_n).
\tag{31.15}
$$

It is induced from the actual cycle embedding and boundary cokernel.
Its monicity follows generically from pushout stability.

<!-- evidence:HOMOLOGY-COKERNEL-INCLUSION -->

> **Formal status — checked.** Evidence `HOMOLOGY-COKERNEL-INCLUSION`.
> The homology-inclusion owner constructs $j_A$ at the supplied whole
> homology and proves it monic, retaining the original cycles and quotient.

If $s$ compares source cycles with the snake kernel and $v$ compares
the snake cokernel with the differential cokernel, the retained native
reconstruction is

$$
j_A\circ\partial_n\circ q_C=v\circ\partial\circ s.
\tag{31.16}
$$

This explains the implementation trace without making its intermediate
isomorphisms the public definition of the formal connecting interface.
The supplied-model interpretation in Section 31.10 records the connection
to the native selected arrow explicitly.

Finite formal assembly starts with an actual H-inclusion arrow. Each window
extension prepends its three arrows and the three existing zero/exactness
annotations to a retained continuation. A field-indexed Nat iterator repeats
this operation over coherent rows and transformations. Adjacent windows share
their boundary arrow; they are not independent windows joined by
object-equality fields. For two windows, the result has eight objects,
seven arrows and six interior exactness annotations.

<!-- evidence:HOMOLOGY-BOUNDED-ITERATOR -->

> **Formal status — checked.** Evidence `HOMOLOGY-BOUNDED-ITERATOR`.
> `homology_row_field_span_exact_tail` iterates any finite number of
> windows. Its data projections retain the actual arrows and original
> annotations. The conventional zero-ended symbolic theorem, including
> its final endpoint-proof attachment, is deferred; it is not implied
> merely by this checked iterator.

The native polynomial implementation already assembles the complete bounded
display. It constructs each degree's homologies and ordinary induced maps
once, then shares them between neighboring windows. Exactness at $H_n(B)$
and $H_n(C)$ comes from the window at $n$; exactness at $H_n(A)$
comes from the window at $n+1$. Its outside-support endpoints retain their
true neighboring differentials and explicit zero-identity witnesses, not
replacement zero presentations.

These are whole operations in the computational category interface. A
retained program declares its kernel, cokernel, normal-factor and other
prerequisites; compilation lowers the operation to the native algebra engine.
Observations return stored homologies and windows. Direct and compiled
execution are compared on complete serialized results.

This operation-and-prerequisite design takes inspiration from
[CAP](#ref-cap-project) and the separation of categorical algorithms from
ring computations in [homalg](#ref-homalg-meta). The native emdash
implementation owns its polynomial algorithms; those reference systems
are not required at runtime.

The examples exercise nonsplit polynomial rows, nonzero boundaries and
nonzero connecting maps. An independent field-linear calculation over
$\mathbb Q$ compares results in explicit quotient coordinates, including
both signs and endpoint cases. It uses constant polynomials, where the
coefficient ring is already $\mathbb Q$; it does not specialize a
polynomial variable and assume that exactness survives.

Executable reviewers:

- `tests/v3_2_algebra_polynomial_freyd_homology_connecting_tests.ts`
- `tests/v3_2_algebra_polynomial_freyd_long_exact_tests.ts`
- `tests/v3_2_algebra_polynomial_freyd_long_exact_category_tests.ts`
- `tests/v3_2_algebra_polynomial_freyd_long_exact_differential_tests.ts`

They check selected-object reuse, bounded output, compiled agreement and
coordinate comparisons. Native endpoint computation and the checked
generic window theorem must not be confused with the deferred final
symbolic endpoint attachment.
The [worked nonsplit example](#homology-nonsplit-worked-example) below
follows one such computation through to its whole-H interpretation.

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

The whole-H interface adds a further connection. A supplied coherent Freyd
homology model retains its kernel and cokernel operations and their
presentations. Its formal H points and induced maps can be interpreted at
the native results already stored by a replay. With the same model's
normality enhancement, this includes every retained connecting window and
the complete displayed arrow order. The interpretation does not run
homology or connecting again, or select another kernel to make the types fit.

Three kinds of information remain distinct. Matrix equations justify
particular raw morphisms and agreements. Selected-provider contracts supply
all-test universal operations. Whole-model interpretations identify the
formal H observations, model-side short-exact rows and connecting arrows
with the retained computational data. The latter two are explicitly recorded
trusted presentation semantics, not theorems inferred from a finite list of
equations. Model normality is a typed supplied input.

<!-- evidence:FREYD-WHOLE-HOMOLOGY-MODEL -->

> **Formal status — checked.** Evidence `FREYD-WHOLE-HOMOLOGY-MODEL`.
> `FreydHomologyModel` packages the supplied coherent data. Its object,
> complete-arrow and connecting observations use the original H; the
> normality enhancement retains its original kernel/cokernel selections.
> This is an interface for a supplied model, not a closed construction of
> a polynomial Freyd Abelian model from matrix equations alone.

Without normality, the workflow still exposes the useful point/induced-map
prefix and reports that connecting interpretation was not requested. With
normality, it checks that every displayed arrow is the original retained
arrow before returning the complete observation view. Repeating an adoption
reuses existing claims rather than silently adding duplicate assumptions.

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

The adopted equations construct a formal raw spine. Each displayed
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
endpoints, with every projected arrow preserved. Taken by itself, this
establishes a formal chain spine. Section 31.11 adds the separate
selected-homology and exactness evidence.

<!-- evidence:FREYD-FORMAL-RAW-SPINE -->

> **Formal status — checked.** Evidence `FREYD-FORMAL-RAW-SPINE`.
> `comm_ring_presentation_morphism_from_matrices` and
> `comm_ring_freyd_chain_pair_from_matrices` return the existing formal
> owners, which assemble raw morphisms and adjacent-zero agreements through
> the existing bounded constructors. No primitive matrix algorithm, quotient
> decoder, or new Core structure is introduced.

The executable bridge and its trust boundary have separate reviewers:

- `tests/v3_2_algebra_formal_freyd_long_exact_tests.ts`
- `tests/v3_2_algebra_formal_freyd_spine_tests.ts`

Their live consumers check
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

The explicit-equation bridge and its application to every retained interior
boundary are exercised by:

- `tests/v3_2_algebra_formal_freyd_epimorphism_tests.ts`
- `tests/v3_2_algebra_formal_freyd_long_exact_epimorphisms_tests.ts`

These reviewers separately check original-morphism preservation, adoption
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
without another kernel or homology selection. The executable reviewers are:

- `tests/v3_2_algebra_formal_freyd_actual_homology_tests.ts`
- `tests/v3_2_algebra_formal_freyd_long_exact_homology_tests.ts`

Their conclusion is relative to the recorded equation and provider
assumptions, not a generic theorem about arbitrary Abelian categories.
The same reviewers cover the retained whole-model point, induced-map and
connecting interpretations described in Section 31.10, including explicit
coverage, unchanged selections and rejection of mismatched model inputs.

<a id="homology-nonsplit-worked-example"></a>

### A Nonsplit Example From Computation To Whole H

Take $R=\mathbb Q[x]$ and $S=R/(x)$, always regarded as an $R$-module.
Consider the complexes supported in degrees one and zero:

$$
A_\bullet=(R\xrightarrow{x}R),\qquad
B_\bullet=(R\xrightarrow{x}R),\qquad
C_\bullet=(S\xrightarrow{0}S).
$$

Multiplication by $x$ defines the inclusion $i:A_\bullet\to B_\bullet$,
and quotient projection defines $p:B_\bullet\to C_\bullet$. In both
supported degrees the row is

$$
0\longrightarrow R\xrightarrow{x}R\longrightarrow S\longrightarrow0.
$$

This row is nonsplit. An $R$-linear map $s:S\to R$ would satisfy
$x s(\overline 1)=s(x\overline 1)=0$. Since multiplication by $x$ is
injective on $R$, every such map is zero; none is a section of the quotient
projection. The computation therefore cannot obtain its connecting map by
choosing a linear section.

The homology calculation gives

$$
\begin{aligned}
H_1(A)&=H_1(B)=0, & H_0(A)&\cong H_0(B)\cong S,\\
H_1(C)&\cong S, & H_0(C)&\cong S.
\end{aligned}
$$

After omitting the leading zero terms and identifying the displayed
homologies with $S$, the long exact sequence reads

$$
0\longrightarrow S\xrightarrow{\partial_1}S
\xrightarrow{0}S\xrightarrow{\operatorname{id}}S\longrightarrow0,
\qquad \partial_1=\operatorname{id}.
$$

To see the connecting map, represent a class of $H_1(C)$ by
$\overline r$, lift it to $r\in B_1$, and apply the differential.
The result $xr\in B_0$ is the image of $r\in A_0$, whose homology
class is again $\overline r$. Replacing the representative by $r+xu$
changes the resulting element of $A_0$ by the boundary $xu$, so the
class is independent of that choice. This is a calculation with a
representative, not a linear section $S\to R$. The native algorithm
implements the corresponding universal lifting and descent operations.

The actual matrices retain more information than this simplified display.
The differential of $C$ is stored as $[x]$ between presentations with
relation matrix $[x]$; it is zero as a quotient map, not as a raw matrix.
The returned connecting and induced maps are

$$
\partial_1=[1],\qquad H_0(i)=[x],\qquad H_0(p)=[1].
$$

The selected $H_0(C)$ has one generator and relation matrix $[x\ x]$.
Its cokernel construction retains both the original relation and the image
of the incoming differential. The two columns generate the same relation
submodule as $[x]$, but the result is not silently replaced by that smaller
presentation. Neighboring windows and formal observations refer to the
original selected object.

The same distinction explains a concrete adjacent-zero witness. The
composite $H_0(i)\circ\partial_1$ has raw matrix $[x][1]=[x]$, while
its target $H_0(B)$ has relation matrix $\rho=[x]$. The coefficient
matrix $[1]$ witnesses

$$
\rho[1]=[x]=[x][1]-[0].
$$

This is an instance of (31.18). Reifying the coefficient witness gives a
formal zero-composite agreement without falsely reducing the raw matrix
$[x]$ to zero. A relation-preservation witness for each individual arrow
still has its separate role in (31.17).

Now interpret the retained calculation in a supplied coherent model $M$.
Its whole functor $H_M$ is the construction of Section 31.4, obtained by
applying the whole cokernel functor to the boundary diagram. In particular,
the two inputs relevant to the nonzero connecting map are

$$
H_1(C):\quad 0\longrightarrow S\xrightarrow{[x]}S,
\qquad
H_0(A):\quad R\xrightarrow{[x]}R\longrightarrow0.
$$

The original raw arrows and chain agreement introduce each input into the
native zero-diagram category. Applying $H_M$ gives its formal homology
point. Applying the Hom action of $H_M$ to an introduced chain map gives
the formal induced map. The connecting component has those whole-H points
as its source and target; its family-level owner is the actual connecting
transformation of Section 31.9. No second H object is chosen merely to
state the component.

For this example the proof-CAS workflow first replays the whole categorical
program and checks agreement with the selected result. Explicit adoption
then makes the computed equations available in the proof environment.
The formal constructors build the bounded raw sequence and its six
interior homology/exactness pairs from the retained maps, boundary witnesses
and selected universal-provider contracts.

The model-observation stage adds a different kind of binding. Write $P_z$
for the reified selected homology presentation of an input $z$, and
$\operatorname{obs}(f)$ for a complete arrow observation in the existing
arrow-object carrier: source, target and arrow together. The bindings have
the form

$$
H_M[z]=P_z,\qquad
\operatorname{obs}(\partial_{1,M})
=\operatorname{obs}(\partial_{1,\mathrm{native}}).
$$

Here the native arrow is the reified $[1]$ between the two retained
homologies. These are explicitly adopted model interpretations, not new
runtime rewrites that make every occurrence of $H_M$ call the CAS. The
coherent model and its normality enhancement remain supplied inputs.

The complete consumer keeps eighteen H observations: twelve degreewise
points for the three complexes in degrees $-1,0,1,2$, and six homologies
of the adjacent pairs in the long exact sequence used to express interior
exactness. It also retains eight degreewise induced-map observations and
three connecting observations. Only the connecting map at degree one is
nonzero. All seven displayed arrows refer to these original observations.
During interpretation the test forbids calls that would rerun homology,
connecting or the kernel/weak-pullback algorithms; mismatched selections
are rejected and existing adopted claims are reused.

The runnable entry is `polynomialFreydHomologyFixture('two')`. Its fixture,
displayed-matrix regression and complete formal/model consumer are,
respectively:

- `tests/v3_2_algebra_polynomial_freyd_homology_fixtures.ts`
- `tests/v3_2_algebra_polynomial_freyd_long_exact_tests.ts`
- `tests/v3_2_algebra_formal_freyd_long_exact_homology_tests.ts`

> **Formal status — mathematical development.** This worked module
> calculation is exercised by the named native regression and formal/model
> consumer. It illustrates the checked conditional interfaces above; it
> is not a closed construction of the supplied model, a correctness proof
> for all native algorithms, or a proof of the deferred symbolic endpoint
> theorem. The native result retains its two actual outside-support zero
> homologies and their witnesses.

## 31.12 Boundaries Of The Integration

The generic and selected-result developments now meet at a useful
computational interface, but their conclusions must be kept separate.

- Whole formal H and connecting use coherent K/Q presentations, a derived
  H and a whole connecting transformation. They do not construct a coherent
  presentation for every older universal-operation family.
- Generic exactness supplies three exact window interiors and a finite
  iterator retaining their arrows and evidence, not the final conventional
  zero-ended symbolic theorem.
- Native bounded computation supplies the complete selected sequence,
  interior witnesses and outside-support zero data. Its tests do not prove
  a theorem for every category.
- Retained proof-CAS interpretation supplies formal raw terms, selected
  interior exactness and model H/map/connecting observations. It does not
  extract arbitrary quotient witnesses or construct a closed model.

The remaining endpoint issue is an interface problem, not an absent native
endpoint calculation. Separate formal zero-object lemmas are available, but
their final symbolic attachment to the conventional bounded display is
deferred. The checked iterator and practical model interpretation do not
require that deferred attachment as an input. This edition states the
boundary rather than replacing the actual H endpoints by convenient zero
objects.

> **Formal status — research boundary.** The deferred claim is the final
> zero-ended bounded theorem with its symbolic endpoint evidence, not the
> checked window and finite-iterator interfaces above. Coherent model
> existence, arbitrary quotient
> effectiveness and a general normalization calculus for homological
> algebra remain separate obligations.

The current formulation is a constructive reference implementation with
whole functors and transformations. Its algebraic reconstruction and
exactness laws still use explicit paths. A later, more economical record
and projection design may improve the dependent interfaces; a Došen-style
normalization theorem for this whole homological layer has not been proved.
Unbounded complexes, derived categories and spectral sequences are also
later developments, not implicit consequences of the bounded result.

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
