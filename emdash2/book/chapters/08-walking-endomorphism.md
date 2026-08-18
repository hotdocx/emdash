<a id="chapter-8"></a>

# 8. Synthetic Directed Homotopy Theory

Homotopy type theory studies spaces by calculating identity types and loop
spaces internally. A directed foundation admits another kind of calculation:
we may calculate a hom whose arrows are not assumed invertible. The first
example is the walking endomorphism.

Write `W` for `WalkingEnd`, `*` for its base, and
$\ell:*\to *$ for its generating arrow. Composition is in
categorical order, so $g\circ f$ means first `f` and then
`g`. For any object `x` of `W`, abbreviate the
based hom-category by

$$
H_x \;:=\; \operatorname{Hom}_W(*,x).
$$

An object of `H_x` is a directed arrow $*\to x$. An arrow
of `H_x` is a directed 2-cell between two such arrows. The signature
states that `W` is one-dimensional, which means precisely that every
`H_x` is discrete. We will exploit this discreteness only after a
directed 2-cell has been constructed.

The proof uses six interfaces:

- `Path(A)`, the equality-local path category of a type `A`;
- functor action `F[f]` on arrows and its higher action on cells;
- a directed Cat-valued family $E:K\to\mathsf{Cat}$ and its fibre
  `E[k]`;
- a displayed functor between two such families;
- natural-number induction;
- a carrier equivalence `TypeEquiv(A,B)`, consisting of maps and
  inverse laws.

Chapters 1–7 develop these notions. This chapter uses them as a compact
working language and returns to implementation names only in formal-status
notes.

The proof also follows the formal rule ledger of
[Appendix G.4](#appendix-formal-presentation-g4). The WalkingEnd constructors
and contextual eliminator supply formation, introduction, elimination, and
beta computation; the code family and spiral supply the missing action and
coherence; one-dimensionality is used only afterward. Full initiality is the
uniqueness clause and remains separate from the checked encode–decode
calculation.

## 8.1 The Based Endomorphisms Of The Walking Endomorphism

<!-- evidence:WE-HOM-NAT-CARRIER -->

The target statement is:

> **Theorem 8.1 (the walking-endomorphism calculation).** There is an
> equivalence of underlying carriers
>
> $$\operatorname{Obj}(H_*) = \operatorname{Hom}_W(*,*) \;\simeq\; \mathbb{N}.$$
>
> **Formal status — checked.** Evidence `WE-HOM-NAT-CARRIER`. The
> active package is `walking_hom_nat_type_equiv`, with an additional
> equality-valued omega-equivalence facade at the groupoid/type level.

The qualification “underlying carriers” matters. The theorem does not
definitionally replace `H_*` by a concrete Nat category. Nor does the
current package include a monoid isomorphism, a reverse functor from the
concrete model `BNat`, an equivalence of hom-categories, or the full
initiality of `W`. We will identify exactly which stronger statements
follow on paper and which still require formal infrastructure.

<a id="chapter-8-1-1"></a>

### 8.1.1 Getting Started

The obvious endomorphisms are the natural powers of the generator:

$$
\begin{aligned}
\ell^0 &:= \mathrm{id}_*,\\
\ell^{n+1} &:= \ell\circ\ell^n.
\end{aligned}
$$

The recursion prefixes one copy of `ell` at each successor. Thus
$\ell^2$ is $\ell\circ\ell$ and no inverse power is present.
The definition is an ordinary Nat eliminator whose motive is the object
carrier of `H_*`.

<!-- evidence:WE-POWER -->

> **Formal status — checked.** Evidence `WE-POWER`. The object map is
> `walking_power`, and
> `walking_power_func` $:\mathsf{Path}(\mathbb{N})\to H_*$ supplies its equality-local
> higher action.

To prove that these powers exhaust the endomorphisms, we seek a measurement

$$
\mathsf{encode}_*:\operatorname{Obj}(H_*)\longrightarrow\mathbb{N}
$$

such that

$$
\mathsf{encode}_*(\ell^n)=n
\quad\text{and}\quad
\ell^{\mathsf{encode}_*(p)}=p.
$$

The first equation is approachable by Nat induction. The second quantifies
over an arbitrary opaque arrow $p:*\to *$. We cannot inspect
`p` as a word because no word datatype is installed as the hom of
`W`.

There is a second, subtler obstruction. An induction principle for a based
path normally becomes useful only after the other endpoint has been
generalized. Fixing both endpoints too early hides the varying family on which
induction acts. The same phenomenon appears here in directed form: the
calculation must be stated not only for `H_*` but for every based
hom `H_x`.

We therefore look for a family of codes `Code[x]` and maps

$$
\begin{aligned}
\mathsf{encode}_x &: \operatorname{Obj}(H_x)
  \longrightarrow \operatorname{Obj}(\mathsf{Code}[x]),\\
\mathsf{decode}_x &: \operatorname{Obj}(\mathsf{Code}[x])
  \longrightarrow \operatorname{Obj}(H_x),
\end{aligned}
$$

natural in the directed endpoint `x`. The base instance will then be
the desired Nat comparison.

The encoder is the easy half once `Code` is known: start at zero and
let the arrow act,

$$
\mathsf{encode}_x(p):=\mathsf{Code}[p](0).
$$

<!-- evidence:WE-ENCODE -->

> **Formal status — checked.** Evidence `WE-ENCODE`.
> `walking_encode` is defined for every endpoint and every based
> arrow, not only for endomorphisms at the base.

At the base, the computations we want are

$$
\mathsf{encode}_*(\mathrm{id}_*)=0
$$

and

$$
\mathsf{encode}_*(\ell\circ p)
=
\mathsf{succ}(\mathsf{encode}_*(p)).
$$

The first is the identity action of a functor. The second will follow from the
generator computation of `Code` together with generic functoriality
on a composite. No WalkingEnd-specific composition rewrite is needed.

<!-- evidence:WE-ENCODE-PREFIX -->

> **Formal status — checked.** Evidence `WE-ENCODE-PREFIX`. The
> prefix equation is propositional; its owner specializes ordinary functor
> action on composition and the literal generator computation.

<a id="chapter-8-1-2"></a>

### 8.1.2 The Free-Monoid Model

Before constructing `Code`, it helps to exhibit the arithmetic object
we expect `W` to resemble. Define a category `BNat` by

$$
\operatorname{Obj}(BNat)=\mathbf{1},
\qquad
\operatorname{Hom}_{BNat}(\bullet,\bullet)=\mathsf{Path}(\mathbb{N}).
$$

Its identity is zero. With our composition convention,

$$
m\circ n := m+n,
$$

where addition recurses in its left input:

$$
0+n=n,
\qquad
(m+1)+n=(m+n)+1.
$$

The underlying objects of the sole hom-category are therefore the natural
numbers. Its higher arrows are equality paths between naturals. Since
`Nat` is a set, that hom-category is discrete, so `BNat`
satisfies the same one-dimensionality contract as `W`.

The generator in `BNat` is `1`. Applying the ordinary
recursor of `W` produces

$$
J:W\longrightarrow BNat,
\qquad
J(*)=\bullet,
\qquad
J[\ell]=1.
$$

Functoriality forces `J` to send a displayed composite of generators
to the corresponding sum. Thus `BNat` demonstrates that the walking
signature has the expected one-object Nat-monoid interpretation.

<!-- evidence:WE-BNAT-MODEL -->

> **Formal status — checked.** Evidence `WE-BNAT-MODEL`. The
> identity and recursive composition of `BNat`, their propositional
> agreement with Nat addition, its one-dimensionality, and
> `walking_bnat_model_func` are checked.

This model does **not** settle Theorem 8.1. A functor `J` gives a
number to every endomorphism, but it need not reflect equality: two unknown
arrows might map to the same number. Nor does a map *out of* an opaque
inductive object supply a map back. The model is valuable precisely because
it remains separate:

- it checks that the signature can be interpreted without collapsing zero and
  one;
- it fixes the intended orientation of identity, composition, and generator;
- it predicts the normal forms;
- it does not place those normal forms into the definition of `W`.

This is the categorical analogue of testing a presentation in a familiar
model before proving its universal consequences. The exhaustiveness proof
must come from the eliminator and dimension evidence of `W` itself.

<!-- evidence:WE-FULL-CATEGORICAL-COMPARISON -->

> **Formal status — research boundary.** Evidence
> `WE-FULL-CATEGORICAL-COMPARISON` records what is absent: a reverse
> $\mathsf{BNat}\to W$ functor, a packaged categorical equivalence, and full
> functor-category initiality require reusable monoid-action-to-functor and
> functor-extensionality infrastructure.

<a id="chapter-8-1-3"></a>

### 8.1.3 The Directed Cover In Functorial Type Theory

We now define the family that measures arrows. The ordinary recursor for
`W` says that a functor out of the walking object is determined by a
target object and one endomorphism of that object. Take the target category to
be `Cat`, choose `Path(Nat)` as the object, and choose the
successor functor as its endomorphism. The result is

$$
\mathsf{Code}:W\longrightarrow\mathsf{Cat}
$$

with constructor computations

$$
\mathsf{Code}[*]=\mathsf{Path}(\mathbb{N}),
\qquad
\mathsf{Code}[\ell]=\mathsf{Succ}.
$$

<!-- evidence:WE-CODE -->

> **Formal status — checked.** Evidence `WE-CODE`. Both the base
> fibre and literal generator action are checked recursor observations.

There is an important contrast with the circle. A universe-valued family over
the circle must send its loop to an equality of types. Univalence can produce
such an equality from successor on the integers because integer successor is
an equivalence. Natural-number successor is not an equivalence: it misses
zero. The directed recursor asks only for an endofunctor, so it accepts
successor directly. Univalence remains part of the surrounding foundation,
but it is neither needed nor appropriate to turn this action into a reversible
path.

At the base fibre, picture

$$
0\longrightarrow 1\longrightarrow 2\longrightarrow 3\longrightarrow\cdots
$$

as levels of a helix over the directed loop. One traversal moves upward by one
level. There is a boundary at zero and no downward motion. The picture is a
guide to the action of the family; it is not a claim that a topological
covering space or a contractible total category has been constructed.

For any based arrow $p:*\to x$, functor action gives

$$
\mathsf{Code}[p]:
\mathsf{Code}[*]\longrightarrow\mathsf{Code}[x].
$$

Evaluating at zero defines `encode_x(p)`. At `x=*` the
result is a natural number. For a generator-prefixed arrow, strict
functoriality factors the action:

$$
\begin{aligned}
\mathsf{encode}_*(\ell\circ p)
&=\mathsf{Code}[\ell\circ p](0)\\
&=\mathsf{Code}[\ell](\mathsf{Code}[p](0))\\
&=\mathsf{succ}(\mathsf{encode}_*(p)).
\end{aligned}
$$

The target of the decoder is the based representable family

$$
\mathsf{Rep}_*:W\longrightarrow\mathsf{Cat},
\qquad
\mathsf{Rep}_*[x]=H_x.
$$

For $f:x\to y$, its action is postcomposition:

$$
\mathsf{Rep}_*[f](q)=f\circ q.
$$

Thus a decoder varying over `x` should be a displayed functor

$$
\mathsf{decode}^{d}:
\mathsf{Code}\Longrightarrow\mathsf{Rep}_*.
$$

At the base, its object map ought to send `n` to `ell^n`.
But an object map alone is too little. It must act on equality paths between
naturals, and it must be coherent with the base generator.

The pointwise power function lifts to a functor

$$
\mathsf{power}:
\mathsf{Path}(\mathbb{N})\longrightarrow H_*.
$$

The lift uses equality action and inclusion into the directed hom-category.
This retains the higher action needed by the contextual eliminator rather
than truncating power to a bare function.

The generator coherence has the form

$$
\mathsf{Rep}_*[\ell]\circ\mathsf{power}
\Longrightarrow
\mathsf{power}\circ\mathsf{Code}[\ell].
$$

At a natural number `n`, its readable component is

$$
\sigma_n:
\ell\circ\ell^n\longrightarrow\ell^{n+1}
$$

inside `H_*`. The endpoints express the same recursive power
equation, but the contextual eliminator requires a coherent transformation,
not merely a family of object equalities. Emdash constructs it by lifting the
equality between the two step functions through the restricted equality-local
core and adding the endpoint adjustments demanded by the ambient directed
hom. This is the **spiral**.

<!-- evidence:WE-SPIRAL -->

> **Formal status — checked.** Evidence `WE-SPIRAL`. The selected
> spiral is the explicit-core-inclusion two-factor construction; its readable
> component has the direction shown above.

The contextual elimination principle for `W` may be read as follows.
Given directed families $R,D:W\to\mathsf{Cat}$, a base functor

$$
u:R[*]\longrightarrow D[*],
$$

and a transformation

$$
D[\ell]\circ u\Longrightarrow u\circ R[\ell],
$$

it produces a displayed functor $R\Rightarrow D$. Substituting
`R=Code`, `D=Rep_*`, `u=power`, and
`sigma` equal to the spiral yields the desired contextual decoder.

<!-- evidence:WE-CONTEXTUAL-ELIMINATOR -->
<!-- evidence:WE-CONTEXTUAL-DECODER -->

> **Formal status — checked.** Evidence
> `WE-CONTEXTUAL-ELIMINATOR` and
> `WE-CONTEXTUAL-DECODER`. The displayed decoder is
> `walking_directed_decode_funcd`, and its base fibre computes to the
> power functor.

This construction is why the generalization over all endpoints is not a
stylistic flourish. The decoder is coherent because it is one displayed
functor over the whole opaque object, not a collection of unrelated functions
defined only at the base.

<a id="chapter-8-1-4"></a>

### 8.1.4 The Encode-Decode Proof

We now follow the dependency order of the construction. The order matters:
compressing the argument into two carrier functions would hide its directed
content.

#### Step 1: powers with higher action

Nat induction defines `power(n)=ell^n` on objects. Equality action
lifts this function to

$$
\mathsf{power}:\mathsf{Path}(\mathbb{N})\longrightarrow H_*.
$$

At zero and successor,

$$
\mathsf{power}(0)=\mathrm{id}_*,
\qquad
\mathsf{power}(n+1)=\ell\circ\mathsf{power}(n).
$$

The functorial lift is essential: the next step needs to transport equality
of naturals to a 2-cell between powers.

#### Step 2: the spiral

Postcomposition by `ell` after power and power after successor are two
functors from `Path(Nat)` to `H_*`. The recursive power
equation gives equality of their underlying object functions. The
equality-local lift, restricted core inclusion, and directed endpoint
adjustments turn this into

$$
\sigma:
\mathsf{Rep}_*[\ell]\circ\mathsf{power}
\Longrightarrow
\mathsf{power}\circ\mathsf{Code}[\ell].
$$

Its component `sigma_n` points from generator-prefix composition
toward the successor power. This is the coherence algebra consumed by the
HIT eliminator.

#### Step 3: the contextual decoder

Contextual elimination now supplies

$$
\mathsf{decode}^{d}:
\mathsf{Code}\Longrightarrow\mathsf{Rep}_*.
$$

Projecting to a fibre gives, for every `x`,

$$
\mathsf{decode}^{d}[x]:
\mathsf{Code}[x]\longrightarrow H_x.
$$

Write `decode_x(c)` for its object action. At the base this functor is
judgmentally the power functor, so

$$
\mathsf{decode}_*(n)=\ell^n.
$$

#### Step 4: the directed normalization cell

Let $p:*\to x$ be arbitrary. A displayed functor does more than
provide fibrewise maps: it compares transport in its source and target
families along every base arrow. Apply this comparison to `p` and to
zero in `Code[*]`.

On the source side, the representable action gives

$$
\mathsf{Rep}_*[p](\mathsf{power}(0))
=p\circ\mathrm{id}_*
=p.
$$

On the target side, Code action gives `Code[p](0)=encode_x(p)`, then
the fibre decoder gives `decode_x(encode_x(p))`. The displayed
comparison is therefore a directed 2-cell

$$
\nu_p:
p\longrightarrow
\mathsf{decode}_x(\mathsf{encode}_x(p))
$$

in `H_x`.

<!-- evidence:WE-NORMALIZATION-CELL -->

> **Formal status — checked.** Evidence
> `WE-NORMALIZATION-CELL`. The term is the displayed hom-action of
> the contextual decoder at `p` and zero. Its source reduces through
> representable postcomposition, `power(0)`, and the right unit.

This is the conceptual climax of the proof. It says that an unknown arrow can
move, by a directed higher cell, toward the canonical power selected by its
code. We have not yet said that the two arrows are equal.

#### Step 5: equality from categorical height

The one-dimensionality witness for `W` makes `H_x`
discrete. In a discrete category, a hom between two objects can be converted
to equality of those objects. Applying this operation to `nu_p`
gives

$$
\bar{\nu}_p:
p=
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

<!-- evidence:WE-NORMALIZATION-PATH -->

> **Formal status — checked.** Evidence
> `WE-NORMALIZATION-PATH`. The implementation explicitly constructs
> `walking_directed_normalization_cell` before applying
> hom-discreteness in `walking_directed_normalization_path`.

This final conversion forgets the orientation of normalization, but it does
not make `p` or `ell` invertible. It uses the absence of
nontrivial 2-dimensional variation in a hom-category; it says nothing about
inverses for its objects as 1-arrows of `W`.

#### Step 6: the hard inverse

Specialize to `x=*`. Because the base decoder computes to power,
`bar(nu)_p` becomes

$$
p=\ell^{\mathsf{encode}_*(p)}.
$$

The inverse law for the desired equivalence is conventionally oriented the
other way, so we take symmetry:

$$
\ell^{\mathsf{encode}_*(p)}=p.
$$

<!-- evidence:WE-POWER-ENCODE -->

> **Formal status — checked.** Evidence `WE-POWER-ENCODE`. This is
> the difficult carrier inverse, and it is derived from directed
> normalization rather than from induction on an exposed word.

In the circle calculation, the analogous fixed-loop problem is repaired by
generalizing the endpoint and using path induction. Here the endpoint is also
generalized, but the eliminator supplies a directed displayed action. The
normalization cell is the directed replacement for the equality that path
induction would have produced immediately in a groupoidal setting.

#### Step 7: the easy inverse

For `n:Nat`, prove

$$
\mathsf{encode}_*(\ell^n)=n
$$

by Nat induction.

At zero, power is the identity and a functor sends identity to identity, so
acting on zero returns zero. At a successor,

$$
\begin{aligned}
\mathsf{encode}_*(\ell^{n+1})
&=\mathsf{encode}_*(\ell\circ\ell^n)\\
&=\mathsf{succ}(\mathsf{encode}_*(\ell^n))\\
&=\mathsf{succ}(n).
\end{aligned}
$$

The middle equality is the generator-prefix encoding formula; the last is the
induction hypothesis acted on by successor. No negative case is required.

<!-- evidence:WE-ENCODE-POWER -->

> **Formal status — checked.** Evidence `WE-ENCODE-POWER`. The
> theorem `walking_encode_power_roundtrip` is native Nat induction
> over the checked prefix equation.

#### Step 8: package the equivalence

The forward function is `encode_*` and the inverse is
`power`. The previous two steps provide both quasi-inverse laws, so
they determine

$$
\operatorname{Hom}_W(*,*)\simeq\mathbb{N}.
$$

The encoder is also packaged as a functor

$$
H_*\longrightarrow\mathsf{Path}(\mathbb{N}),
$$

obtained by taking the hom-action of `Code` and evaluating at zero.
This functor acts on 2-cells between endomorphisms. Its ordinary functor laws
should not be confused with preservation of the *horizontal* monoid
composition of the endomorphisms themselves.

<!-- evidence:WE-STRUCTURED-ENCODER -->
<!-- evidence:WE-HOM-NAT-CARRIER -->

> **Formal status — checked.** Evidence
> `WE-STRUCTURED-ENCODER` and
> `WE-HOM-NAT-CARRIER`. The structured encoder and carrier
> equivalence are active; a structured reverse functor and a monoid package
> are not.

The proof can now be summarized without erasing its architecture:

$$
\begin{array}{c}
p\\[2pt]
\downarrow\;\nu_p\\[2pt]
\mathsf{decode}(\mathsf{encode}(p))
\end{array}
\quad\Longrightarrow_{\text{discreteness}}\quad
p=\ell^{\mathsf{encode}(p)},
$$

followed by the independent Nat-inductive calculation
`encode(ell^n)=n`.

<a id="chapter-8-1-5"></a>

### 8.1.5 Consequences And The Missing Negative Integers

The equivalence has immediate structural consequences, but the most
illuminating ones concern what the walking generator cannot do.

#### The based hom is a set

There are two checked proofs that the underlying carrier
`Hom_W(*,*)` is a set.

1. **By dimension.** One-dimensionality makes `H_*` discrete, and
   discreteness includes sethood of its object carrier.
2. **By comparison.** Natural numbers form a set, and truncation is invariant
   under the carrier equivalence.

<!-- evidence:WE-HOM-SETHOOD -->

> **Formal status — checked.** Evidence `WE-HOM-SETHOOD`. The two
> proofs are separately named, so the dimensional and equivalence-based
> explanations remain visible.

#### The generator is not the identity

The prefix computation gives

$$
\mathsf{encode}_*(\ell)=1,
\qquad
\mathsf{encode}_*(\mathrm{id}_*)=0.
$$

If `ell=id_*`, functorial action of `encode` on that
equality would yield `1=0`, whose Nat equality classifier is empty.

<!-- evidence:WE-LOOP-NOT-IDENTITY -->

> **Formal status — checked.** Evidence
> `WE-LOOP-NOT-IDENTITY`.

#### The generator has no right inverse

Suppose $r:*\to *$ and

$$
\ell\circ r=\mathrm{id}_*.
$$

Encoding the left side and using the prefix formula gives
`succ(encode(r))`; encoding the right side gives zero. Again a
successor cannot equal zero. Therefore no such `r` exists.

<!-- evidence:WE-LOOP-NO-RIGHT-INVERSE -->

> **Formal status — checked.** Evidence
> `WE-LOOP-NO-RIGHT-INVERSE`. The statement is specifically the
> absence of a right inverse in the displayed composition orientation; no
> stronger cancellation theorem is being silently imported.

Native omega-equivalence evidence for an arrow contains, among its data, a
right inverse and its equality law. The preceding result therefore rules out
such evidence for `ell`.

<!-- evidence:WE-LOOP-NONINVERTIBLE -->

> **Formal status — checked.** Evidence
> `WE-LOOP-NONINVERTIBLE`.

#### Composition and addition

The carrier theorem strongly suggests the monoid formula

$$
\mathsf{encode}_*(q\circ p)
=
\mathsf{encode}_*(q)+\mathsf{encode}_*(p).
$$

Its orientation agrees with `BNat`: `q` is the outer arrow
and its code is the left input of addition. A paper proof follows from the
checked interfaces. First use Nat induction and associativity to show

$$
\ell^{m+n}=\ell^m\circ\ell^n.
$$

Then replace `q` and `p` by their normalized powers and use
`encode(power(k))=k`. What is absent is not the mathematical
argument but its selected library package and its interaction with a future
reverse functor.

<!-- evidence:WE-COMPOSITION-ADDITION -->

> **Formal status — formal consequence.** Evidence
> `WE-COMPOSITION-ADDITION`. The current kernel does not expose a
> named monoid-isomorphism object for this statement.

#### Why naturals replace integers

For the circle, every loop is an equality path and hence can be reversed.
Powers extend from naturals to integers, the code action has both successor
and predecessor, and the result is group-valued.

For `W`, the generator is a directed arrow with no supplied inverse.
The code action moves

$$
0\mapsto1\mapsto2\mapsto\cdots
$$

and cannot move below zero. Natural numbers record the free monoid generated
by forward motion. The negative integers are missing for the same reason the
right inverse is missing: direction has not been group-completed.

The comparison with the Circle now proceeds by exactly such an explicit
free-inversion construction. A whole functor

$$
W\longrightarrow\operatorname{Path}(S^1)
$$

sends the base and directed generator to the Circle base and loop. It sends
every natural power to the corresponding nonnegative Circle power, and the
Circle encoder reads that image as the canonical inclusion
$\mathbb N\to\mathbb Z$. More strongly, restriction along this functor is a
whole mapping equivalence against every groupoidal target. The theorem does
not make $\ell$ invertible inside $W$; it characterizes the separate
groupoidal object obtained by freely allowing inverse motion.

<!-- evidence:WE-GROUP-COMPLETION -->

> **Formal status — checked.** Evidence `WE-GROUP-COMPLETION`. The concrete
> WalkingEnd–Circle restriction/extension theorem is active and iterable.
> Chapter 27 places it beside category-indexed groupoidification. A reverse
> `BNat` functor and a packaged monoid isomorphism for the original carrier
> theorem remain separate questions.

The calculation has reached its intended boundary. It proves that an opaque
directed generator has exactly the expected natural powers, and it proves
noninvertibility rather than assuming it. The later universal mapping theorem
strengthens the surrounding comparison, but it is not a hidden premise of
the Nat encode–decode proof.

## 8.2 Higher Groupoidal Shadows

The surrounding calculus is directed, but equality-local and groupoidal
phenomena remain inside it. The first neighboring example is the
Eckmann–Hilton argument.

Let `B` be a category and `x` an object. The 2-endomorphisms
of the identity 1-arrow form the carrier

$$
\operatorname{2End}_B(x)
:=
\operatorname{Hom}_{\operatorname{Hom}_B(x,x)}
(\mathrm{id}_x,\mathrm{id}_x).
$$

There are apparently two ways to combine elements. Vertical composition is
ordinary composition in the hom-category `Hom_B(x,x)`. Horizontal
composition is obtained by whiskering/postcomposition at the identity
1-arrow. They share the identity 2-cell as a unit, and the ordinary
functoriality of whiskering supplies interchange. The classical
Eckmann–Hilton calculation then makes the operations agree and commute:

$$
\beta\cdot\alpha=\alpha\cdot\beta.
$$

<!-- evidence:EH-COMMUTATIVITY -->

> **Formal status — checked.** Evidence `EH-COMMUTATIVITY`. The
> active term `EH_comm` derives commutativity from the two
> compositions, shared units, and interchange in the iterated-hom
> representation.

This result does not undo the directed character of `W`. It lives
one dimension higher at the identity arrow, where the relevant comparison is
equality-local. The coexistence is the point: a directed theory can contain
groupoidal shadows at controlled boundaries without declaring all of its
arrows reversible.
