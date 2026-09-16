<a id="chapter-31"></a>

# 31. Additive, Abelian, And Homological Computation

How can homology be a computational construction without asking its users to
assemble naturality squares by hand? The answer begins with the universal
operations themselves. A kernel is supplied by a whole right adjoint; a
cokernel by a whole left adjoint. Their units, counits and mate operations
construct the maps that homological algebra needs. Homology and its connecting
transformation are then built from those operations at their actual native
inputs.

This order matters. Selecting an object called a kernel and later attaching
an externally indexed collection of factors does not by itself provide the
whole functor or its higher action. Here the functor and adjunction come
first. In the ordinary-category part of the development, their observations
also yield familiar factor, reconstruction and uniqueness records. Those
records are useful views of the same construction.

The chapter develops whole K, Q, H and δ, the three exactness positions of a
homology window, a general native snake sequence, and the comparison between
the two new connecting constructions. It then follows a nonsplit polynomial
example through the CAS and the formal layer to a certificate for the actual
displayed long exact sequence. The model and interpretation contracts are
explicit throughout. No output-exactness assumption is used to manufacture
that certificate.

The formal development is qualified at an ordinary additive target and its
stated structural profiles. Its foundations remain the internal Hom and
dependent-Hom calculus. This chapter does not claim a complete higher
Abelian-category theory, a general homology normalization theorem, or a closed
construction of every concrete model. The distinctions are part of the
mathematics, not merely limitations of the notation.

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

## 31.2 Universality As A Whole Adjunction

Let C be the ordinary additive target and let D(C) be its native category
of diagrams on the walking arrow. Evaluation at the two vertices gives
functors e₀,e₁:D(C)→C. The zero object determines two further whole functors:

J(A) = (A→0), I(A) = (0→A).

The primary universal data are actual functors K,Q:D(C)→C with adjunctions

J ⊣ K, Q ⊣ I.

A kernel structure consists of K together with its adjunction evidence. It
does not require an earlier dictionary of selected kernels. Dually, a
cokernel structure consists of Q and its adjunction evidence. These are
internal terms with the action supplied by their existing categorical
owners.

The counit J∘K⇒id, evaluated at the source vertex, gives the whole kernel
inclusion κ:K⇒e₀. The unit id⇒I∘Q, evaluated at the target vertex, gives the
whole cokernel projection π:e₁⇒Q. Their endpoint computations expose the
usual arrows κ(d):K(d)→dom(d) and π(d):cod(d)→Q(d).

Now take an entire diagram transformation u:J(A)⇒d. Transposition under
J ⊣ K produces an arrow u♯:A→K(d). The adjunction reconstruction is an
identity between whole diagram maps. Its source observation is the familiar
equation κ(d)∘u♯=u₀. The inverse mate returns u, including the diagram data
that made it a kernel test. The cokernel operation is dual: a whole map
v:d⇒I(B) transposes to v♭:Q(d)→B, and its target observation gives
v♭∘π(d)=v₁.

The same operations apply to families. Postcomposition lifts the original
adjunction to the relevant functor categories, so a whole transformation is
transposed at once. The formal caller supplies that transformation; it does
not separately prove a naturality square for every parameter arrow. Generic
functor and transfor action remain responsible for the coherence of the
result.

<!-- evidence:NATIVE-KERNEL-COKERNEL-UNIVERSALITY -->

> **Formal status — checked.** Evidence
> `NATIVE-KERNEL-COKERNEL-UNIVERSALITY`. `KernelAdjunctionStructure` and
> `CokernelAdjunctionStructure` retain the actual whole functors and their
> adjunctions. Units, counits and mate operations supply their structural
> arrows and whole-family universal operations. The ordinary target and
> declared adjunction-lifting profiles are explicit premises.

### The Diagram Presentation And Its Reconstruction

The walking-arrow diagram and the complete arrow-object presentation have
different jobs. The former is the domain of K and Q. The latter exposes a
source, a target and an arrow together, and is useful for observing a result.
Let E evaluate a diagram to its complete arrow, and let D introduce a diagram
from such an arrow.

In the ordinary-target presentation, the development supplies a natural
DefIso D∘E≅id. Both directions have identity components at the two walking-arrow
vertices. Applying K or Q to the actual reconstruction maps therefore retains
their categorical action and exposes the endpoint computation. The inverse
comes from the same DefIso package.

This reconstruction is a declared extension of the existing diagram
interface. It is not claimed to follow from the old introduction β rules
alone. Nor is it an unrestricted identification of strict functor diagrams
with higher lax-arrow categories. The ordinary-target guard and the stated
structural presentation are retained.

There are analogous whole comparisons for transformations to a terminal
constant family and from an initial constant family. They permit the
universal constructions to operate on the original family rather than on a
sequence of independently rebuilt pointwise cones.

<!-- evidence:ORDINARY-DIAGRAM-UNIVERSALITY -->

> **Formal status — checked.** Evidence `ORDINARY-DIAGRAM-UNIVERSALITY`.
> The reconstruction and zero-family DefIso instances have declared
> structural owners with checked computational consumers. They use the
> existing DefIso inverse and inverse cuts; no new equivalence notion is
> introduced. They are part of the explicitly stated ordinary presentation.

### Ordinary Factor Records As Derived Views

For an ordinary arrow d:B→D, the adjunction can also be observed in the usual
form. A test u:T→B with d∘u=0 has a factor through κ(d), together with
reconstruction and uniqueness. Cokernel observations give the corresponding
colifts. The native record view retains K(d) or Q(d); it does not choose
another universal object.

This is the appropriate place for the familiar factor spaces
Σ(v:T→K(d)), κ(d)∘v=u and their contractions. They express the ordinary
universal property and support existing ordinary consumers. They are not
prerequisites from which the primary whole K and Q are reconstructed.

The distinction becomes important in higher categories. Contractibility of
the object space of a Hom category does not control its noninvertible higher
arrows. A general categorical terminality interface should contract the whole
Hom category coherently. [Chapter 30](#chapter-30) now distinguishes the whole contraction interface
and the checked ordinary terminal/initial adjunction presentations. A general
higher replacement of terminality remains separate. Univalence does not
remove the need to specify the level at which contraction is asserted.

## 31.3 Coimage, Image, And Normality

The same whole adjunctions construct coimage and image. For a diagram d,
form the cokernel of its kernel inclusion and the kernel of its cokernel
projection:

Coim(d) = Q(κ(d)), Im(d) = K(π(d)).

These formulas abbreviate composites of whole functors. The structural
inclusion and projection are whole transformations, so their arrow diagrams
are whole inputs to Q and K.

Transposition and reconstruction produce the canonical comparison

c:Coim⇒Im.

It is the comparison for which d factors through its original coimage
projection and image inclusion. The construction of c precedes any
invertibility assumption. Normality then supplies fixed-forward ΩAlong
evidence on that actual transformation. Its inverse data are retained in
the existing equivalence package.

This order prevents a common ambiguity. An arbitrary isomorphism between
objects named Coim(d) and Im(d) does not establish that the canonical map is
invertible. The normality premise concerns c itself. The same discipline
will define exactness at a pair of arrows.

The ordinary algebraic consequences remain useful. In an additive category,
a difference kernel constructs a fibre product: the kernel of [f,−g] has
projections whose composites with f and g agree. The dual cokernel of the
column ⟨f,−g⟩ constructs a pushout. The existing ordinary universal records
support these familiar calculations. In the direct connecting construction
below, the needed pullback along a kernel has a particularly economical
native form, K(d∘p), using the same K.

<!-- evidence:NATIVE-COIMAGE-IMAGE-NORMALITY -->

> **Formal status — checked.** Evidence
> `NATIVE-COIMAGE-IMAGE-NORMALITY`. The canonical whole Coim⇒Im
> transformation is derived from the original adjunctions. The normality
> interface supplies equivalence of that fixed transformation. Ordinary
> product, biproduct and functor-category structural instances used by the
> construction remain declared premises of the presentation.

## 31.4 Whole Homology From A Native Zero Diagram

A one-degree homology input retains the incoming object A, an outgoing
walking-arrow diagram d:B→D, and a whole diagram map h:J(A)⇒d. Its incoming
face is e:A→B, and its diagram compatibility expresses d∘e=0. The native
input is the object on which the universal constructions act.

This formulation keeps the directed data. It is not merely three object
names accompanied by external naturality equations. The input lives in the
existing native zero-cone category, whose Hom structure comes from the
internal dependent-Hom foundations.

Apply the right adjoint K to obtain the cycle family Z. The mate of the
original input gives the whole boundary transformation

β:A⇒Z.

Apply the original Q to the arrow family of β. The resulting whole homology
functor is

H = Q∘Arr(β).

Its quotient transformation q:Z⇒H is the corresponding observation of the
unit. All three objects A, Z and H remain those selected by the original
whole data. No ordinary kernel or cokernel record is needed to define H.

For a native map of inputs, the Hom action of H gives the induced map on
homology. Its cycle and quotient reconstruction laws follow from the same
whole transformations. A matrix chain map can later be introduced into this
native Hom, but it does not define a separate homology algorithm in the
formal layer.

### Comparing Presentations By Actual Maps

A family-level homology and the observation of the global H functor may
present their boundary diagrams differently. The useful comparison is an
actual map between those diagrams, with its inverse data and endpoint
components. Applying Q to that map gives the homology comparison. Applying
Q to the inverse gives the retained inverse operation.

This exposes the action needed by consumers. An equality of diagram or
functor objects, followed by a generic path transport, may conceal that
action even when the endpoint objects are mathematically equivalent. In the
qualified point and column comparisons, categorical reconstruction is the
primary operation. Ordinary equations record the laws of the constructed
maps; they do not replace them.

If parameters vary in a directed category, a whole comparison must also
retain its action and coherence in those parameters. A successful point
observation alone is not evidence for that stronger interface.

<!-- evidence:NATIVE-WHOLE-HOMOLOGY -->

> **Formal status — checked.** Evidence `NATIVE-WHOLE-HOMOLOGY`.
> The whole boundary and H are defined from the native adjunction
> structures. The point comparison uses an actual boundary-diagram map
> under Q, with its inverse retained. Column comparisons and their quotient
> reconstruction laws refer to the same selected objects.

## 31.5 Exactness At The Canonical Comparison

Consider a whole composable pair f:A⇒B and g:B⇒D, together with its native
zero-composition input. Applying the existing image and kernel functors gives
an actual canonical transformation

χ:Im(f)⇒K(g).

Exactness means ΩAlong(χ), with χ fixed. In particular, the witness includes
the inverse data for this comparison. It does not merely assert that two
endpoint objects happen to be isomorphic.

There are two useful operations on this interface. First, a whole exactness
family can be evaluated at a parameter. Second, an equivalence between actual
native zero inputs transports exactness to the canonical comparison at the
new input. The generic naturality of the canonical Im⇒Ker transformation
supplies the required compatibility. The caller is not asked to provide an
additional naturality square.

For the LES, this matters when comparing a whole family presentation with
the H arrows used by the CAS-facing model. Actual input maps and their
selected inverses reconcile the presentations. Target zero composition is
derived from the source input and the comparison; it is not a new premise.
Only after this categorical step are the complete arrow observations related
to the displayed matrices.

The concrete observation certificate therefore retains two pieces together:
the canonical exactness witness at a fixed native input X, and a path from
its complete observed arrow pair to the chosen displayed pair. Extending
that observation path leaves the Ω witness unchanged, including its inverse
slots. It does not authorize replacing X by another input without the
categorical comparison required above.

<!-- evidence:NATIVE-CANONICAL-EXACTNESS -->

> **Formal status — checked.** Evidence `NATIVE-CANONICAL-EXACTNESS`.
> Whole, evaluated and actual-input exactness use the same canonical
> comparison. The public-pair constructions derive the target zero law and
> apply the original exactness proofs. Observation transport retains the
> canonical witness; a reviewer rejects substituting a different input.

## 31.6 Constructing The Whole Connecting Transformation

Consider a short exact sequence of chain complexes, written degreewise as

0→Aₙ ─iₙ→ Bₙ ─pₙ→ Dₙ→0.

The differentials lower degree, and i and p commute with them. The formal
construction works with whole row families and their maps. Four consecutive
rows retain the neighboring boundary and cycle data needed by a homology
window. The whole kernel and cokernel structures, row exactness and normality
are explicit inputs.

Write Zᴰₙ=K(dᴰₙ) for the source cycle object. The native pullback needed to lift
cycles through pₙ is constructed using the same kernel functor:

Eₙ = K(dᴰₙ∘pₙ).

Its inclusion into Bₙ and the kernel mate give r:Eₙ→Zᴰₙ. In the whole-family
construction these are transformations. The upper short-exact row makes r
an epimorphic cover, through the actual coimage comparison and its retained
inverse. There is no choice of a section of pₙ.

Apply dᴮₙ to the inclusion Eₙ→Bₙ. Row commutation and the definition of Eₙ
show that the result is killed by pₙ₋₁. Exactness of the lower row and the
original kernel operation therefore produce a whole lift into Aₙ₋₁.
The next differential vanishes on this lift. Transposition into the original
cycle object and the original homology quotient give

θ:Eₙ⇒Hₙ₋₁(A).

The construction now makes two universal descents. First, θ kills the kernel
of r, so it descends to γ:Zᴰₙ⇒Hₙ₋₁(A). Second, γ kills the original source
boundary βᴰₙ, so it descends through qᴰₙ:Zᴰₙ⇒Hₙ(D). The result is the whole
connecting transformation

δₙ:Hₙ(D)⇒Hₙ₋₁(A).

Let ρ=qᴰₙ∘r. Its reconstruction is

δₙ∘ρ = θ.

The same cover proves uniqueness. Any whole transformation with this
reconstruction agrees with δₙ. A single descent along ρ is also compared
with the two-stage construction as a whole transformation. This gives a
useful computational characterization while keeping the source quotient
and all inverse choices visible.

Naturality has not been added after an elementwise construction. The lifts,
cover maps and descents were whole operations throughout. Their generic
functorial and natural action supplies the action of δ. A component δₙ[x]
is an observation of that transformation.

<!-- evidence:NATIVE-HOMOLOGY-CONNECTING -->

> **Formal status — checked.** Evidence `NATIVE-HOMOLOGY-CONNECTING`.
> The native connecting owner constructs δ by the two descents above and
> proves whole reconstruction and uniqueness. Its direct descent is related
> to the same result. No new connecting-arrow primitive or output-exactness
> premise is introduced. The argument uses the recorded ordinary/additive,
> whole-adjunction, normality and row-exactness hypotheses.

## 31.7 Exact Homology Windows And Finite Assembly

The connecting transformation completes the five-term window

Hₙ(A) → Hₙ(B) → Hₙ(D) ─δₙ→ Hₙ₋₁(A) → Hₙ₋₁(B).

There are three interior exactness assertions: at Hₙ(B), at Hₙ(D), and at
Hₙ₋₁(A). Each concerns the canonical Im→Ker comparison for the actual
adjacent pair. The proofs construct the required kernel and cokernel zero
properties through whole lifts, quotient descents, additive differences and
cover cancellation. Normality then supplies invertibility of that fixed
comparison.

The proof strategy retains the actual maps. For example, an equality after
a quotient is established by the original quotient cancellation; an equality
after a cover is reflected through that same cover. An image or kernel is
not replaced by an unrelated isomorphic object merely because its endpoints
look appropriate. The resulting Ω evidence records the inverse data used
by consumers.

<!-- evidence:NATIVE-HOMOLOGY-WINDOW-EXACTNESS -->

> **Formal status — checked.** Evidence
> `NATIVE-HOMOLOGY-WINDOW-EXACTNESS`. All three original native window
> comparisons have derived fixed-forward equivalence witnesses. Their
> evaluated observations and actual-input transport use the same canonical
> comparisons. The displayed CAS certificate is a later consumer of these
> proofs, not a premise of them.

### Shared Boundaries And Indexing

Finite assembly should share a boundary arrow, rather than repeatedly prove
that two independently chosen endpoint objects are equal. The retained
field/window iterator, in its original ordinary record interface, is a
checked example of this principle. It starts with an actual H-inclusion arrow, and each window extension prepends three arrows with their
original zero and exactness annotations to a retained continuation.

That earlier iterator remains available in its own interface. The native
CAS certificate below is assembled directly from the new whole proofs and
does not require a comparison with that presentation. Constructor-local
indexing makes the next position and its continuation explicit. Adjacent windows use the same selected boundary arrow. Flattening
the sequence and trimming a display belong downstream, after this shared
structure has been constructed.

For two windows, the finite tail has eight objects, seven arrows and six
interior annotations. The external degree labels are a convenient way to
read it; they are not instructions to cast a functor along an equality of
shifted indices.

Indexing and observation cost are distinct. An index can compute while
recovering a large selected H expression remains expensive. The native
presentation comparisons address the latter with actual categorical maps.
The checked iterator is retained; an alternative simplicial or cubical
indexing experiment is not silently promoted on the strength of a point
calculation.

<!-- evidence:HOMOLOGY-BOUNDED-ITERATOR -->

> **Formal status — checked.** Evidence `HOMOLOGY-BOUNDED-ITERATOR`.
> The existing field-span iterator assembles any finite number of windows
> in its ordinary record interface, with shared boundary arrows and retained
> annotations. It is not presented as a migrated native whole-window iterator. This is separate
> from a conventional symbolic zero-endpoint theorem. The older final
> endpoint-proof attachment remains deferred. The concrete displayed CAS
> sequence below has its own checked observations and exactness certificate.

## 31.8 The General Native Snake

The general snake construction starts with whole transformations

A ─a⇒ B ─b⇒ X ─c⇒ D, c∘b∘a=0.

Neither a monic nor c epic is assumed. These omissions matter: replacing A
by Im(a), or D by Im(c), would change the outer terms and require further
comparisons. The native input retains the original whole data.

The two universal operations define α:A⇒K(c) and γ:Q(a)⇒D, with
κ(c)∘α=b∘a and γ∘π(a)=c∘b. Now form E=K(γ∘π(a)), using the original
whole K. The map π(a) on E lifts to a cover ρ:E⇒K(γ). The map b on E lands
in K(c); passing through the original quotient of α gives θ:E⇒Q(α).

The image factorization and whole kernel lifts show that θ kills K(ρ).
Descent gives the snake connecting transformation

∂:K(γ)⇒Q(α), ∂∘ρ=θ.

The cover ρ proves uniqueness. The construction is again internal and
categorical: it uses whole maps, their native universal transpositions and
the same selected quotient. No family of hand-written naturality squares is
supplied to assemble ∂.

The other four arrows are the original K and Q actions on the two induced
diagram maps. They give

K(α) → K(b) → K(γ) ─∂→ Q(α) → Q(b) → Q(γ).

The four interior canonical Im→Ker comparisons are invertible. Their proofs
use the same E, ∂ and cover data, with additive difference representatives
and cancellation where required. All six terms remain in scope; the result
is not reduced to a short exact pair with monic a and epic c.

<!-- evidence:NATIVE-SNAKE-CONNECTING -->
<!-- evidence:NATIVE-SNAKE-SIX-TERM -->

> **Formal status — checked.** Evidence `NATIVE-SNAKE-CONNECTING` and
> `NATIVE-SNAKE-SIX-TERM`. The native construction derives ∂, its
> reconstruction and uniqueness, all five whole maps, and the four original
> canonical exactness witnesses. The finite six-term result and its typed
> data observations are checked under the documented resource profiles.

One normalization boundary remains explicit. A large reviewer that directly
compares the extracted complete comparison/witness packages with their
standalone presentations still exhausts resources. The individual first-step
comparison and the typed observations of all four packages, including their
inverse maps, pass. A bounded review found no functor equality-cast in the
observer to replace; fresh parent compilation did not resolve the large
comparison. That direct normalization check is deferred. It is neither a
new exactness assumption nor a claimed proved comparison.

## 31.9 Relating The Two Native Connecting Constructions

The LES was defined directly from its own whole window. The general snake
was defined from its own native triple. Their agreement is a mathematical
result between these two new constructions, not a compatibility test against
a former record-based implementation.

For a four-row homology window, use the block maps

a = [dᴮₙ₊₁,iₙ], b = dᴮₙ, c = ⟨dᴮₙ₋₁,pₙ₋₁⟩.

Thus a has source Bₙ₊₁⊕Aₙ and target Bₙ; c has target Bₙ₋₂⊕Dₙ₋₁.
The middle chain-zero and row-commutation laws give c∘b∘a=0. This constructs
an actual input to the general native snake without choosing new kernels or
cokernels.

Whole universal comparisons then identify its connecting endpoints. Write

R:K(γ)≃Hₙ(D), L:Q(α)≃Hₙ₋₁(A)

for the retained forward maps with their inverse data. The connecting-map
comparison is

δₙ∘R = L∘∂.

The sign is positive for these conventions. Reconstruction through the
original covers proves this whole-transformation equation; the endpoint
comparisons are genuine categorical maps. The surrounding-map comparisons
are checked at the retained endpoints as well.

This arrangement leaves both constructions useful. The direct LES exposes
its cycle and boundary descents. The snake handles its full arbitrary-triple
scope. Their common categorical operations explain their agreement, without
making a legacy formulation an intermediate target of either definition.

<!-- evidence:NATIVE-SNAKE-LES-COMPARISON -->

> **Formal status — checked.** Evidence `NATIVE-SNAKE-LES-COMPARISON`.
> The native window is constructed as a general snake input. The endpoint
> equivalences, surrounding-map comparisons and connecting equation retain
> their original forward maps and inverse data. This establishes agreement
> of the new native ∂ and δ with the stated positive sign.

## 31.10 Native Models And Complete CAS Observations

Polynomial presentations make the universal constructions executable. A
presentation retains generators and a relation matrix. A raw morphism retains
its matrix and relation-preservation data. Equality of the induced quotient
maps has its own coefficient witness. A raw matrix can therefore be nonzero
while representing the zero arrow in the presented-module category.

The CAS layer computes kernels, quotients, homology and connecting data using
these representations. A retained categorical program records its algebraic
prerequisites and keeps the selected results. The formal layer has a different
role: it expresses the whole universal constructions and proves the
categorical statements about their actual maps.

The primary bridge supplies a native model M containing the whole kernel and
cokernel adjunction structures, together with the initial-zero capability
needed by the construction. Its normality N is a separate supplied input.
Write Hᴹ for the resulting whole homology functor.

Introducing a raw chain pair into the native zero-cone category and applying
Hᴹ gives the formal homology observation. Introducing a raw chain map into
the native Hom and applying the same Hᴹ gives its map observation. The
prefix `raw` in these adapters identifies matrix/presentation input; it does
not name an earlier homology algorithm.

<!-- evidence:NATIVE-FREYD-MODEL -->

> **Formal status — checked.** Evidence `NATIVE-FREYD-MODEL`.
> `FreydAdjunctionModel` supplies the actual whole adjunction structures.
> Native H and its Hom action consume introduced chain data directly.
> Model normality, model-side row short-exactness and realization on the
> selected presentations remain explicit contracts. No legacy homology
> model is a prerequisite of this route.

### What Is Computed, Supplied, And Proved

The distinctions can be read as three different obligations:

| Layer | Retained data | Meaning |
| --- | --- | --- |
| CAS computation | Matrices, presentations, coefficient witnesses and selected outputs | Executable algebra and its checked/adopted equations |
| Model interpretation | The whole model, normality, row semantics and complete-arrow agreements | Explicit semantic contracts connecting the formal operations to those selections |
| Native proof | Canonical comparison inverses and exactness certificates | Results derived from the preceding context, without an output-exactness assumption |

The frontend automates preparation, equation lookup and reuse, construction
of the raw input terms, complete-arrow observation, endpoint matching and
certificate assembly. A user does not manually assemble a new naturality
square at each position of the LES. This automation does not prove every
semantic model contract from a matrix computation. A closed construction of
the full model is separate work.

A complete arrow observation retains its source, target and arrow in the
existing arrow-object carrier. An interpretation relates this whole
observation to the reified selected CAS arrow. This is stronger bookkeeping
than comparing only the entries of its raw matrix: adjacent arrows must use
the same actual selected endpoints.

The finite displayed diagram retains all its complete arrows and their
endpoint matching. Its exactness certificate is indexed by that same diagram
and a retained native input for every adjacent pair. The constructor chooses
the appropriate native proof according to the pair:

- H(i),H(p): exactness at the middle homology;
- H(p),δ: exactness at the source of the connecting map;
- δ,H(i): exactness at its target.

The categorical input comparisons of Section 31.5 first put each original
proof at the actual public native pair. The existing interpretation paths
then attach its complete arrow observations to the displayed CAS pair.
The Ω witness is retained unchanged at this last step. The finite certificate
has one such entry for every interior position, so its length and coverage
are part of the checked result.

<!-- evidence:NATIVE-CAS-DISPLAYED-EXACTNESS -->

> **Formal status — checked.** Evidence
> `NATIVE-CAS-DISPLAYED-EXACTNESS`. The native public-pair proofs and finite
> certificate constructors derive exactness of the complete displayed
> diagram under the original model and interpretation contracts. The
> concrete frontend replay checks all its pair certificates and the whole
> result. The certificate constructor adds no assumption or trust decision.

The native snake has an analogous complete displayed certificate. It uses
the general whole snake, its original maps and exactness data, and the
existing complete-arrow interpretations. Its proof–CAS consumer does not
need an equivalence with the former snake implementation.

## 31.11 A Nonsplit Example With A Nonzero Connecting Map

<a id="homology-nonsplit-worked-example"></a>

Take R=ℚ[x] and S=R/(x), regarded as an R-module. Consider the complexes
supported in degrees one and zero:

A• = (R ─x→ R), B• = (R ─x→ R), D• = (S ─0→ S).

Multiplication by x gives i:A•→B•, and quotient projection gives p:B•→D•.
In each supported degree the row is

0→R ─x→ R→S→0.

The row is nonsplit. An R-linear map s:S→R must satisfy
x·s(1̄)=s(x·1̄)=0. Multiplication by x is injective on R, so s is zero.
It cannot be a section of the quotient projection. The connecting computation
therefore cannot rely on a chosen R-linear section.

The homology objects are

H₁(A)≃H₁(B)≃0, H₀(A)≃H₀(B)≃S,

H₁(D)≃S, H₀(D)≃S.

After simplifying the display, the nontrivial part is

0→S ─δ₁→ S ─0→ S ─id→ S→0, δ₁=id.

A representative explains the sign. Lift the class of r in H₁(D) to r in
B₁ and apply the differential, obtaining xr. This is i₀(r), so the
resulting class in H₀(A) is the class of r. Replacing r by r+xu changes
that result by the boundary xu. This calculation explains the universal
lift and descent; it does not choose a linear section S→R.

### Retaining The Actual Presentations

The raw matrices carry more information than the simplified display. The
differential of D is stored as [x] between presentations with relation [x].
It is zero as a quotient map. The returned connecting and induced matrices
are

δ₁=[1], H₀(i)=[x], H₀(p)=[1].

The selected H₀(D) has one generator and relation matrix [x x]. The cokernel
construction retains both the original relation and the incoming image.
Although those columns generate the same submodule as [x], the result is
not silently replaced by a smaller presentation. Neighboring windows and
formal observations continue to use that selected object.

For example, H₀(i)∘δ₁ has raw matrix [x], while the target H₀(B) has relation
matrix ρ=[x]. The coefficient matrix [1] witnesses

ρ[1]=[x]=[x][1]−[0].

Reifying this coefficient witness supplies the corresponding quotient-map
equation. A raw nonzero matrix and a zero arrow are compatible statements
because they refer to different levels of the representation.

### The Complete Native LES Certificate

The actual bounded result retains twelve degreewise H points: the three
complexes in degrees −1,0,1,2. It also retains eight induced maps and three
connecting windows. Its displayed sequence has eight objects and seven
arrows. Only the degree-one connecting arrow is nonzero.

The six adjacent pairs are certified in this order:

| Interior position | Native proof used |
| --- | --- |
| H₁(A) | Target exactness of the degree-two window |
| H₁(B) | Middle exactness of the degree-one window |
| H₁(D) | Source exactness of the degree-one window |
| H₀(A) | Target exactness of the degree-one window |
| H₀(B) | Middle exactness of the degree-zero window |
| H₀(D) | Source exactness of the degree-zero window |

These are the actual displayed endpoints, not a second list of freshly
selected homologies. A final proof packages their canonical exactness data
over the same coherent diagram. The original whole proofs are also retained.
In particular, the integration does not need to compute the homology of each
adjacent displayed pair by an older independent procedure and compare the
results with the new universal construction.

The complete replay distinguishes twenty computed equations from thirteen
interpretation claims. Those are the existing workflow's adopted context.
Constructing the six pair certificates and the complete diagram certificate
adds zero assumptions and zero trust decisions. A second run reuses the same
source, inputs and proof terms. During assembly the tests forbid rerunning
the homology, connecting, kernel and weak-pullback algorithms; missing map
coverage and changed endpoint data are rejected.

The runnable example is `polynomialFreydHomologyFixture('two')`. Its actual
native diagram consumer is
`tests/v3_2_algebra_formal_freyd_native_diagram_tests.ts`. Its emitted formal
checks cover the retained H/map/δ observations, the original whole proofs,
all six displayed-pair certificates and the complete diagram certificate.

**The corresponding basic snake computation.** The native snake also supports
the nonsplit triple with a=x, b=id and c=0, all between copies of R. Its retained six presentations are

0, 0, S, S, R/(1), R/(0).

The five raw matrices are [], [], [1], [1], [0], and ∂ is the identity of S.
The raw [1] into R/(1) represents zero. The result keeps R/(1) and R/(0)
as selected presentations rather than silently replacing them by preferred
zero and free objects.

The native snake workflow checks its complete displayed exactness certificate
under the supplied model and interpretations. Its three backend contracts,
nine computed equations and five complete-arrow interpretations remain
separate in the proof source. Reuse requires no additional decisions.

> **Formal status — checked conditional interfaces.** The native
> displayed LES and snake certificate owners apply to these supplied model
> contexts. The named executable consumers check the nonsplit calculations,
> retained presentations and emitted formal terms. This is not a closed
> construction of the supplied model or a general correctness theorem for
> every CAS operation.

### Retained Observations And Retired Implementations

The native proof–CAS path now imports its raw chain inputs independently of
the former selected-homology algorithms. Ordinary H records likewise have an
independent observation owner. An ordinary record describes the same selected
native data; using it does not reinstate the former algorithm as a prerequisite.

Superseded model facades, the old snake-derived connecting route, and unused
comparison wrappers have been retired from active source and check registries.
Git history preserves them. Shared matrix/provider algorithms and the explicitly
identified ordinary finite-window iterator remain useful separate references.
There is no obligation to compare new homology with every retired formulation.

A further distinction concerns observations at a chosen parameter. The primary
H and its induced maps are whole; the finite CAS interface also needs ordinary
equations relating particular selected presentations and maps. Those equations
remain appropriate observations. A proposed whole classification of coherent
family inputs, followed by a whole family-to-global H comparison, is a natural
further interface refinement. Its prototype is not evidence that the existing
native computation has regressed, and it is not claimed implemented here.

## 31.12 Computation, Qualifications, And Further Work

There are two computational contributions. The categorical layer provides
whole universal operations, adjunction cuts, canonical transformations,
cover cancellation and universal descents. The algebra engine computes with
presentations and matrices. The proof–CAS interface connects these layers
while retaining the selected inputs, maps and explicit trust boundary.

This is a concrete setting for Došen-style categorical computation: a
universal operation is represented by a whole categorical owner with its
introduction, elimination and reconstruction behavior. The kernel and
cokernel operations participate directly in the definitions of H, δ and ∂.
That does not establish a general homological cut-elimination, coherence or
normalization theorem. No such theorem is inferred from successful examples
or from the existence of a matrix algorithm.

The ordinary structural presentation includes declared instances for diagram
reconstruction, zero-family comparisons, postcomposition adjunction lifting,
and the needed functor/product/slice profiles. Their computational consumers
are checked. These assumptions must not be confused with axioms asserting
output homology exactness; the latter is derived from the original whole
operations and normality.

Several boundaries remain explicit:

- The large direct comparison of extracted six-term witness packages remains
  deferred after its bounded resource review. The original six-term result,
  typed data access and displayed CAS certificates have their separate
  positive evidence.
- The conventional generic symbolic endpoint attachment is distinct from
  the checked finite iterator and the concrete displayed CAS certificate.
- Full concrete model/provider construction is not replaced by a list of
  successful matrix tests. The supplied semantic contracts remain visible.
- General categorical terminality and higher coherence require their own
  refinement beyond the current ordinary-target presentation.
- The higher Op/duality and strictness-profile migration belongs to a
  separate development. No general higher-duality repair is claimed here.
- Categories of unbounded or derived complexes and further derived or stable
  constructions are outside the implemented boundary of this chapter.

Controlled unfolding, source sharing and garbage-collection settings can
change whether a checker completes without changing the mathematical term.
A resource failure is not a mathematical counterexample. Conversely, a
successful small projection does not qualify a larger computation that has
not completed. The formal-status notes distinguish the relevant consumers
instead of treating all these outcomes as one normalization claim.

The operation-and-prerequisite architecture has affinities with
[CAP](#ref-cap-project) and the separation of categorical algorithms from
ring computations in [homalg](#ref-homalg-meta). The relevant distinctions
between constructive computation, image completion and theorem proving also
appear in Posur's [constructive methods](#ref-posur-methods),
[image completion](#ref-posur-images), and
[free Abelian categories for theorem proving](#ref-posur-free-abelian).
These references provide context; the qualified native constructions and
the explicit model contracts described above determine the present interface.
