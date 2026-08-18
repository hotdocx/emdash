<a id="chapter-26"></a>

# 26. The Circle And The Integer Line

The walking endomorphism of Chapter 8 has one point and one directed
generator. Every based arrow is a finite forward composite, so its arithmetic
is the arithmetic of natural numbers. The Circle also has one point and one
generator, but its generator is an equality path. It can be followed in
either direction. Forward powers are joined by powers of the inverse, and the
corresponding arithmetic becomes the integer line.

This resemblance is exact enough to be useful and dangerous enough to demand
care. The Circle is not obtained by replacing the natural-number answer in
the WalkingEnd theorem with integers. Its loop is intrinsically groupoidal;
its eliminator must act on dependent paths; and the inverse generator is
derived from path reversal rather than postulated as another arrow. The
integer answer is then *calculated* by a universal-cover encode–decode
argument. Only in Chapter 27 will the relationship with the directed walking
endomorphism be promoted to a universal free-inversion theorem.

The calculation has four layers. First, successor on natural numbers is
localized to an invertible shift, producing an internal Integer classifier.
Second, the Circle is given its point, loop, and dependent computation.
Third, univalence turns integer successor into the monodromy of a family over
the Circle; transport in this family records winding number. Finally,
integer-indexed loop powers decode winding numbers back to paths. The two
directions are inverse not only at the base point but fibrewise over every
endpoint of the Circle.

## 26.1 Integers By Inverting Successor

The Integer classifier is not introduced as a new datatype with positive and
negative constructors. It is obtained from the sequential telescope

$$
\mathbb N\xrightarrow{\mathsf{succ}}
\mathbb N\xrightarrow{\mathsf{succ}}
\mathbb N\xrightarrow{\mathsf{succ}}\cdots
\tag{26.1}
$$

by the set-truncated telescope-localization construction of Chapter 7. Write

$$
\mathsf{Integer}=\operatorname{Tel}(\mathbb N,\mathsf{succ}).
\tag{26.2}
$$

A representative at stage $n$ with value $x$ will be denoted $[n,x]$ and has
the intended reading $x-n$. The telescope constructor identifies the
diagonal step

$$
[n+1,x+1]=[n,x].
\tag{26.3}
$$

Thus $[0,0]$ represents zero, $[0,x]$ represents the nonnegative integer
$x$, and $[1,0]$ represents negative one. No subtraction operation is needed
to define the carrier. The notation $x-n$ explains the invariant respected
by (26.3); the formal object is the localized telescope itself.

This presentation separates arithmetic content from notation. A signed
datatype would choose, at the outset, between a nonnegative and a negative
constructor and would then require normalization at their boundary. The
telescope instead records a history: $n$ applications of the inverse shift
and a current natural value $x$. The diagonal equality (26.3) performs the
cancellation that signed notation normally hides. A later theorem may choose
canonical representatives, but the Circle proof does not depend on that
choice.

The construction also isolates exactly what “integer” means at this stage.
The proof needs a set with a distinguished zero and an invertible successor,
together with an eliminator that respects the localization equation. It does
not need addition, multiplication, order, or the universal property of the
group completion of the natural-number monoid. Those structures may be built
later from the same carrier. Declining to presuppose them makes the eventual
loop calculation more informative: integer behaviour is forced by reversible
successor, not smuggled in through a ready-made ring.

The forward telescope action descends to integer successor. Shifting the
stage supplies its inverse, predecessor:

$$
\mathsf{succ},\mathsf{pred}:\mathsf{Integer}\longrightarrow
\mathsf{Integer},
\qquad
\mathsf{succ}\,\mathsf{pred}\simeq\operatorname{id},
\quad
\mathsf{pred}\,\mathsf{succ}\simeq\operatorname{id}.
\tag{26.4}
$$

Consequently successor is retained as a type equivalence. Univalence turns
that equivalence into a path

$$
\mathsf{ua}(\mathsf{succ}):
\mathsf{Integer}=\mathsf{Integer},
\tag{26.5}
$$

and transport along (26.5) agrees with the actual successor function. This is
the path that will drive the universal cover.

The telescope is set-truncated by construction. Its dependent eliminator is
therefore restricted to set-valued motives. To define a section over all
integers, it is enough to define it on every stage representative $[n,x]$,
give a dependent path over (26.3), and show that each target fibre is a set.
This restriction is not an inconvenience hidden by notation: it will match
exactly the one-dimensional boundary of the Circle loop space used by the
decoder.

<!-- evidence:INTEGER-LOCALIZATION-LINE -->

> **Formal status — checked.** Evidence `INTEGER-LOCALIZATION-LINE`. The
> Integer carrier is a transparent facade over the successor telescope;
> successor and predecessor have explicit inverse paths; successor is a
> retained equivalence and universe path; and set-targeted elimination
> computes on stage representatives. No addition, signed normal-form
> equivalence, ordered-ring structure, or universal additive-group-completion
> theorem is claimed here.

## 26.2 A Circle That Computes On Its Loop

The groupoidal Circle is generated by

$$
\mathsf{Circle}:\mathcal U,
\qquad
\mathsf{base}:\mathsf{Circle},
\qquad
\mathsf{loop}:\mathsf{base}=\mathsf{base}.
\tag{26.6}
$$

Its inverse loop is simply $\mathsf{loop}^{-1}$, obtained by equality
symmetry. It is not a second constructor. The signature also states its
selected one-dimensional boundary: every path type of the Circle is a set.
This evidence is later checked from another direction when the based loop
space is computed to be the set-valued Integer classifier.

The dependent eliminator has the usual geometric form. Given a family
$D:\mathsf{Circle}\to\mathcal U$, an element
$b:D(\mathsf{base})$, and a dependent path

$$
\ell:
\operatorname{PathOver}_D(\mathsf{loop};b,b),
\tag{26.7}
$$

it produces a section

$$
\mathsf{circle\_ind}(D,b,\ell):
\prod_{x:\mathsf{Circle}}D(x).
\tag{26.8}
$$

The section computes judgmentally at the point constructor. More
significantly, its canonical dependent action computes judgmentally at the
path constructor:

$$
\begin{aligned}
\mathsf{circle\_ind}(D,b,\ell)(\mathsf{base})
  &\equiv b,\\
\operatorname{apd}(\mathsf{circle\_ind}(D,b,\ell),\mathsf{loop})
  &\equiv \ell.
\end{aligned}
\tag{26.9}
$$

The second rule retains the full path-over type in (26.7); it does not erase
the transport of endpoints. It is also narrowly owned by the Circle
eliminator and generating loop. An arbitrary dependent function on the
Circle does not acquire this reduction merely because it is evaluated on
$\mathsf{loop}$.

Ordinary recursion is the constant-family case of (26.8). For a point $b:B$
and loop $\ell:b=b$, it gives a function

$$
\mathsf{circle\_rec}(B,b,\ell):\mathsf{Circle}\to B.
\tag{26.10}
$$

Its dependent action inherits the second reduction in (26.9), represented as
the constant-family path-over built from $\ell$. The familiar ordinary
equation

$$
\operatorname{ap}(\mathsf{circle\_rec}(B,b,\ell),\mathsf{loop})=\ell
\tag{26.11}
$$

is derived propositionally. It is not a second runtime rule. This distinction
is easy to miss on paper because (26.9) and (26.11) express the same
mathematical computation. In the formal calculus they are different
observers: `apd` sees the primitive dependent constructor action, while
ordinary `ap` is reconstructed through constant-family transport.

Dependent computation is the stronger statement. In (26.7), the endpoint
$b$ is transported around the nontrivial base loop before it is compared
with itself. The path-over remembers that movement even when the family is
not constant. Ordinary `ap` sees only the constant-family shadow after the
transport has been converted back into a path of $B$. If one installed only
(26.11), the universal-cover decoder would still need a separate principle
to control the function family in (26.20). Rule (26.9) supplies that control
at the actual higher-constructor owner.

This is the first HIT in the book whose higher constructor has a selected
judgmental dependent beta. The lesson is not that every appealing higher
equation should become a rewrite. The safe unit of computation is the action
of the eliminator on its own constructor, with its full dependent type
retained. Readable constant-family equations may remain propositional when a
second reduction would duplicate normal forms or disturb unrelated equality
proofs.

<!-- evidence:CIRCLE-HIT-COMPUTATION -->

> **Formal status — checked.** Evidence `CIRCLE-HIT-COMPUTATION`. Point beta
> and dependent loop beta are runtime computations at their stable owners;
> the named dependent beta is reflexivity after reduction. Constant-family
> recursion inherits the dependent computation. Its ordinary `ap` equation
> remains a checked propositional path, and unrelated sections do not
> collapse to the supplied loop datum.

> **Attribution and adaptation boundary.** The Circle signature and the
> universal-cover rhythm below structurally adapt the [HoTT Book](#ref-hott-book),
> Sections 6.2 and 8.1. The present account uses the active emdash dependent
> computation boundary, successor-localized Integer rather than the Book's
> signed/quotient presentation, and whole categorical realizations. It does
> not import the HoTT Book's flattening proof or silently claim all of its
> later homotopy-group consequences.

## 26.3 The Universal Cover As Monodromy

The classical universal cover of the circle may be pictured as a helix over a
circle. Following the positive loop raises the lift by one level; following
the negative loop lowers it. Type theory replaces the helix by a family whose
fibres are integers and whose monodromy is successor.

Equation (26.5) supplies exactly the loop in the universe needed by Circle
recursion. Define

$$
\mathsf{Code}:\mathsf{Circle}\longrightarrow\mathcal U
\tag{26.12}
$$

by

$$
\mathsf{Code}(\mathsf{base})\equiv\mathsf{Integer},
\qquad
\operatorname{ap}(\mathsf{Code},\mathsf{loop})
  =\mathsf{ua}(\mathsf{succ}).
\tag{26.13}
$$

The loop equation in (26.13) is the ordinary `ap` observation of Circle
recursion and is therefore propositional, consistently with (26.11).
Transport along it nevertheless has the intended computational content:

$$
\begin{aligned}
\operatorname{transport}^{\mathsf{Code}}(\mathsf{loop},z)
  &=\mathsf{succ}(z),\\
\operatorname{transport}^{\mathsf{Code}}(\mathsf{loop}^{-1},z)
  &=\mathsf{pred}(z).
\end{aligned}
\tag{26.14}
$$

Univalence is essential here. Successor is not the identity function on
integers, so an ordinary reflexive universe path could not encode the desired
monodromy. The equivalence-to-path direction of univalence turns the actual
self-equivalence into a loop of classifiers, and its transport comparison
returns the underlying successor map.

For any endpoint $x:\mathsf{Circle}$, a path
$p:\mathsf{base}=x$ can now be lifted into the code family. Start at integer
zero and transport it along $p$:

$$
\mathsf{encode}_x(p)
  :=\operatorname{transport}^{\mathsf{Code}}(p,0)
  :\mathsf{Code}(x).
\tag{26.15}
$$

Encoding reflexivity computes to zero. Encoding the generating loop is
propositionally successor of zero. More generally, concatenating a positive
loop applies successor and concatenating an inverse loop applies predecessor.
The encoder is therefore the winding-number observer: it converts abstract
groupoidal motion into a point of the localized integer line.

The calculation can be followed compositionally. If a based path first
follows $p$ and then follows $q$, transport in the code family first lifts
zero along $p$ and then acts along $q$. Each occurrence of
$\mathsf{loop}$ contributes successor, and each occurrence of
$\mathsf{loop}^{-1}$ contributes predecessor. Adjacent inverse pairs cancel
through (26.4). Thus a composite such as

$$
\mathsf{loop}\cdot\mathsf{loop}^{-1}\cdot
\mathsf{loop}\cdot\mathsf{loop}
$$

is observed as two. This example is intuition rather than a claim that every
path arrives as a parsed word. The encode map works on arbitrary equality
evidence; the word picture explains its behaviour on paths constructed from
the generator and its inverse.

The family point of view also explains the name *cover*. Over each Circle
point there is an Integer fibre, and travelling once around the base permutes
that fibre by successor. What is constructed here is the type-theoretic
family and its monodromy. No topological space of real numbers, local
triviality atlas, or external covering-space apparatus is assumed.

It is tempting to stop at the base fibre and define only

$$
(\mathsf{base}=\mathsf{base})\longrightarrow\mathsf{Integer}.
\tag{26.16}
$$

That specialization is the desired forward map, but it is too narrow for the
hard inverse proof. Path induction cannot directly simplify an arbitrary
loop whose two endpoints have both been fixed at the base. The crucial move,
as in the HoTT encode–decode method, is to retain the endpoint $x$ and work
fibrewise with (26.15).

## 26.4 Decoding Integer Powers

At the base point, decoding should send an integer to the corresponding power
of the generating loop. Natural powers are obtained by repeatedly appending
$\mathsf{loop}$; inverse powers repeatedly append
$\mathsf{loop}^{-1}$:

$$
\begin{aligned}
\mathsf{loop}^{0}
  &=\mathsf{refl}_{\mathsf{base}},\\
\mathsf{loop}^{n+1}
  &=\mathsf{loop}^{n}\cdot\mathsf{loop},\\
\mathsf{loop}^{-(n+1)}
  &=\mathsf{loop}^{-n}\cdot\mathsf{loop}^{-1}.
\end{aligned}
\tag{26.17}
$$

The telescope presentation asks for a slightly subtler definition. A stage
representative $[n,x]$ should decode to the loop power corresponding to
$x-n$. Rather than first choosing a signed normal form, the construction
recurses simultaneously on $n$ and $x$. Along the diagonal it cancels one
positive and one negative step, so that

$$
\mathsf{power}(n+1,x+1)\equiv\mathsf{power}(n,x).
\tag{26.18}
$$

The coherence required by the telescope relation (26.3) is therefore literal
reflexivity. Integer elimination then gives the based decoder

$$
\mathsf{decode}_{\mathsf{base}}:
\mathsf{Integer}\longrightarrow
(\mathsf{base}=\mathsf{base}),
\tag{26.19}
$$

with the expected computations at zero, nonnegative representatives, and
negative one. The required target is a set because the Circle signature says
that its path types are sets. This is the exact point where the truncation
level of the telescope eliminator and the dimension of the Circle meet.

The three boundary cases make the construction concrete. At stage zero,
$[0,x]$ decodes to the $x$th positive power. At value zero, $[n,0]$ decodes
to the $n$th inverse power. When both indices are successors, the definition
removes one loop and one inverse loop simultaneously and returns to the
preceding stage. These are computations of the representative-level decoder,
not a post hoc proof that two separately normalized signed expressions happen
to agree.

The decoder must now be generalized over the endpoint, just as the encoder
was. Consider the family

$$
M(x):=\mathsf{Code}(x)\longrightarrow(\mathsf{base}=x).
\tag{26.20}
$$

At the base, the desired inhabitant is (26.19). To apply Circle induction one
must show that this function returns to itself over
$\mathsf{loop}$. Transport in the domain of (26.20) uses predecessor,
transport in the codomain appends the loop, and the required comparison is
therefore the cancellation law

$$
\mathsf{loop}^{z-1}\cdot\mathsf{loop}=\mathsf{loop}^{z}.
\tag{26.21}
$$

Positive and negative cases are proved from path composition, reversal, and
inverse cancellation. The resulting dependent loop datum feeds the Circle
eliminator and produces

$$
\mathsf{decode}_x:
\mathsf{Code}(x)\longrightarrow(\mathsf{base}=x)
\tag{26.22}
$$

for every $x$. This is the step that turns the obvious based loop-power
function into a morphism of the entire path fibration and code family.

Endpoint generalization is therefore not merely a clever way around a weak
induction tactic. It states the invariant at its natural level. The encoder
and decoder are maps between two families over the Circle: the outgoing-path
family $x\mapsto(\mathsf{base}=x)$ and the code family
$x\mapsto\mathsf{Code}(x)$. The loop coherence for (26.22) says that decode
commutes with their monodromies. Once the whole family map exists, the based
loop function is obtained by ordinary specialization rather than by fixing
endpoints before the structure has been built.

## 26.5 The Two Round Trips

The composite from paths to codes and back is now the easy direction. For
$p:\mathsf{base}=x$, ordinary endpoint path induction reduces $p$ to
reflexivity. Encoding reflexivity is zero and decoding zero is reflexivity,
so

$$
\mathsf{decode}_x(\mathsf{encode}_x(p))=p.
\tag{26.23}
$$

The reverse composite begins at the base. One proves by natural and
telescope induction that positive loop powers encode to $[0,n]$, inverse
powers encode to $[n,0]$, and the general simultaneous power encodes to its
own representative $[n,x]$. Integer induction then gives

$$
\mathsf{encode}_{\mathsf{base}}
  (\mathsf{decode}_{\mathsf{base}}(z))=z.
\tag{26.24}
$$

To extend (26.24) from the base fibre to every $x$, observe that every
$\mathsf{Code}(x)$ is a set. At the base this is the sethood of Integer; the
statement that a fibre is a set is itself propositional, so Circle induction
propagates it around the generating loop without a new choice of coherence.
The desired equality is likewise proposition-valued. A second Circle
induction therefore yields

$$
\mathsf{encode}_x(\mathsf{decode}_x(c))=c
\tag{26.25}
$$

for all endpoints and all codes.

Equations (26.23) and (26.25) package an endpoint-dependent family of
equivalences. At the base point it gives the central calculation

$$
(\mathsf{base}=\mathsf{base})\simeq\mathsf{Integer}.
\tag{26.26}
$$

Now form the categorical realization
$\mathsf{Circle}_{\mathrm{cat}}:=\operatorname{Path}(\mathsf{Circle})$.
Its based hom carrier is definitionally the same loop space, so there is also

$$
\operatorname{Hom}_{\mathsf{Circle}_{\mathrm{cat}}}
  (\mathsf{base},\mathsf{base})
\simeq\mathsf{Integer}.
\tag{26.27}
$$

This is the precise meaning of the shorthand
“$\operatorname{Hom}(\mathsf{Circle})=\mathbb Z$.” It concerns the based
endomorphism carrier of the path category, not the type of all self-maps of
the Circle.

The result is retained at three levels. Equation (26.26) is an intrinsic
type equivalence. Equation (26.27) reads the same carrier as a categorical
hom. Applying the whole path-category action to the selected encoder gives a
categorical equivalence

$$
\operatorname{Hom}_{\mathrm{cat}}
  (\mathsf{base},\mathsf{base})
\simeq_{\omega}
\operatorname{Path}(\mathsf{Integer}),
\tag{26.28}
$$

whose forward functor acts by the encoder and retains higher equality action.
Neither category head is rewritten to the other. The selected
one-dimensional Circle evidence and the equivalence with the set
$\mathsf{Integer}$ also give two independent proofs that the based hom is a
set.

The distinction among these three packages prevents an easy overstatement.
A `TypeEquiv` is enough to transport properties of the carrier and to select
the encode/decode functions. The categorical hom reading says where that
carrier occurs in the directed language. The whole categorical equivalence
adds action on equalities between loops and on their iterated equalities.
None of them, by itself, is a judgmental identification of the two category
expressions, and none yet says that the equivalence preserves a separately
packaged group operation. Each level answers a different downstream question
without forcing the strongest possible interface on every reader.

<!-- evidence:CIRCLE-LOOP-INTEGER -->

> **Formal status — checked.** **Theorem 26.1 (the Circle loop space).**
> Evidence `CIRCLE-LOOP-INTEGER`. Endpoint-dependent encode and decode are
> inverse. Their based specializations form an explicit `TypeEquiv` between
> the intrinsic loop space and successor-localized Integer; the categorical
> hom has the same carrier; and a separate whole equality-valued categorical
> equivalence is retained. No category-head rewrite or group-structure
> preservation theorem is included in this result.

## 26.6 Monodromy Beyond Successor

The universal cover is one instance of a general construction. Let $A$ be a
groupoidal classifier and let $e:A\simeq A$ be a self-equivalence. Univalence
turns $e$ into a universe path, and Circle recursion constructs a family

$$
\begin{aligned}
\mathsf{Mon}_e &: \mathsf{Circle}\longrightarrow\mathcal U,
&\mathsf{Mon}_e(\mathsf{base})&=A,\\
\operatorname{ap}(\mathsf{Mon}_e,\mathsf{loop})
  &=\mathsf{ua}(e).&&
\end{aligned}
\tag{26.29}
$$

Transport around the actual loop agrees with the forward map of $e$. Taking
$A=\mathsf{Integer}$ and $e=\mathsf{succ}$ recovers the code family above.
Taking another automorphism produces another local system on the same Circle
without changing the HIT.

There is also a directed shadow. Restrict the family along the canonical map
from the walking endomorphism to the Circle. The resulting directed
representation remembers $A$ at its point and the univalence path of $e$ at
its forward generator. The checked restriction–extension comparison recovers
that whole representation, rather than only its two displayed components.
Chapter 27 will explain the universal mapping theorem that makes this
restriction canonical; here it serves as a geometric consumer of monodromy.

<!-- evidence:CIRCLE-MONODROMY -->

> **Formal status — checked.** Evidence `CIRCLE-MONODROMY`. A selected
> self-equivalence determines a Circle-indexed groupoid family; its base and
> loop observations have the expected values; transport around the loop
> agrees with the equivalence's forward map; and whole restriction recovers
> the corresponding WalkingEnd representation. The result is a consumer of
> the concrete WalkingEnd–Circle universality theorem, not a second primitive
> monodromy axiom.

## 26.7 Connected Without Choosing Paths

The Circle has one point constructor, so one expects every point to be
reachable from the base. A function choosing an actual path
$\mathsf{base}=x$ for every $x$ would say too much: it would contract the
Circle and destroy its nontrivial loop space. The correct statement is mere
connectedness:

$$
\prod_{x:\mathsf{Circle}}
\left\|\mathsf{base}=x\right\|_{-1}.
\tag{26.30}
$$

At the base, reflexivity supplies the truncated witness. Every fibre in
(26.30) is a proposition, so there is a unique dependent path over the
generating loop. Circle induction then constructs the section without ever
choosing an untruncated global path.

This statement has a concrete truncation consequence. Let
$\|\mathsf{Circle}\|_0$ be the classified set truncation and take the image of
$\mathsf{base}$ as centre. Mere connectedness can be eliminated into equality
inside this set, because its path types have the required truncation level.
First one obtains a path from the centre to the image of every Circle point;
set-truncation induction then extends it to every point of the truncation:

$$
\operatorname{isContr}\bigl(\|\mathsf{Circle}\|_0\bigr).
\tag{26.31}
$$

Contractibility is retained as evidence. The carrier of the set truncation is
not judgmentally replaced by Unit. This preserves the distinction between a
universal construction characterized by elimination and a convenient chosen
normal form.

Connectedness and the loop calculation complement rather than contradict one
another. Equation (26.30) says that the Circle has only one component after
paths are merely inhabited; equation (26.26) says that the ways of returning
to the base retain an entire Integer classifier. Set truncation forgets those
different return paths while preserving the component, which is why it is
contractible even though the Circle itself is not. The proof performs that
forgetting through the truncation eliminator instead of declaring the loops
irrelevant in the original type.

<!-- evidence:CIRCLE-CONNECTED-TRUNCATION -->

> **Formal status — checked.** Evidence `CIRCLE-CONNECTED-TRUNCATION`. The
> propositional truncation of each based path fibre gives mere connectedness,
> and restricted truncation elimination proves the set truncation
> contractible. The result selects no global untruncated path and adds no
> rewrite from the set-truncated Circle to Unit.

## 26.8 From Counting To Free Inversion

We can now place the two arithmetic calculations side by side:

$$
\begin{array}{c|c|c}
\text{shape}&\text{generator}&\text{based hom classifier}\\ \hline
\text{walking endomorphism}&\text{directed arrow}&\mathbb N\\
\text{Circle}&\text{invertible path}&\mathsf{Integer}.
\end{array}
\tag{26.32}
$$

The change from $\mathbb N$ to Integer is not an analogy imposed after the
proof. It is the effect of reversibility inside the proof. Positive composites
of the directed generator remain distinct natural powers because no inverse
exists. Positive and negative powers of the Circle loop cancel because path
symmetry supplies an inverse. The telescope relation makes the same
cancellation computational on integer representatives.

The canonical map from the walking endomorphism sees only the upper half of
this arithmetic. Its $n$th directed power maps to the nonnegative integer
$[0,n]$ and to the $n$th positive Circle loop. Nothing in the directed source
names $[n,0]$ or $\mathsf{loop}^{-n}$: those elements appear because the
target is groupoidal. Free inversion must therefore do more than preserve the
old powers. It must add the reverse motion and impose the cancellations that
make it inverse, while retaining how all of this acts on higher cells.

This observation also explains why the loop-space calculation is such a good
test for the universal property. If restriction from the Circle to the
walking endomorphism forgot too much, an extension could choose incompatible
actions on negative powers. If it imposed too much, ordinary directed
representations whose generator lands in a groupoidal target might fail to
extend. The correct theorem says that the image of the one directed generator
already determines the whole reversible action: its inverse and all integer
powers are forced by the target's path structure. Chapter 27 establishes that
claim at the level of whole mapping objects.

Several boundaries remain explicit. Integer has not yet been packaged as an
additive group, so Theorem 26.1 does not separately prove that path
composition corresponds to integer addition. The chapter does not provide a
generic HIT declaration language, a proof that every categorical former has
a groupoidal specialization, or a global normalization theorem for
computational homotopy type theory. And although the Circle is connected and
has a set-valued loop space, the selected results here are not advertised as
a complete formal calculation of every homotopy group.

What has been obtained is enough for the next question. The walking
endomorphism maps to the Circle by sending its directed generator to the
generating loop. Is every map from the walking endomorphism into a groupoidal
target extended uniquely, in the appropriate whole sense, across this free
inversion? And can the same principle be stated for an arbitrary directed
category? Chapter 27 turns the arithmetic evidence of this chapter into that
universal property.
