<a id="chapter-12"></a>

# 12. Adjunctions And Equivalences

An adjunction is the first universal construction in which the cut calculus
becomes a theorem about a chosen relationship between two functors. It can be
presented by a unit and counit, by a natural equivalence of homs, or by
representability. These presentations explain one another, but they should
not be collapsed before their hypotheses and equality modes have been stated.

Equivalence requires the same care. Carrier equivalence, isomorphism of two
objects, equivalence of ordinary categories, and native omega-equivalence
answer different questions. This chapter builds the adjunction interface
first, then uses it to organize those notions.

## 12.1 Indexed Adjunction Data

Let

$$
F:A\longrightarrow B,
\qquad
G:B\longrightarrow A.
$$

An adjunction $F\dashv G$ has a unit and counit

$$
\eta:\mathrm{id}_A\Rightarrow GF,
\qquad
\varepsilon:FG\Rightarrow\mathrm{id}_B,
$$

subject to the two triangle identities. In ordinary notation these say

$$
(\varepsilon F)\circ(F\eta)=\mathrm{id}_F,
\qquad
(G\varepsilon)\circ(\eta G)=\mathrm{id}_G.
$$

The active `Adjunction` classifier keeps $F$ and $G$ as indices. Its
`unit_adj_transf` and `counit_adj_transf` observations are stable
computational heads. This matters: triangle computation is attached to the
selected adjunction witness, not to every pair of transformations having the
same displayed types.

The direct-TypeScript authoring layer can package already declared
$F$, $G$, $\eta$, and $\varepsilon$—or a counit and whole natural hom
transpose—as an indexed witness with proof-time agreements. It expands into
ordinary logical-framework declarations: no new adjunction notion and no
runtime alias. [Appendix G.5](#appendix-formal-presentation-g5) places this
convenience at its precise trust boundary.

## 12.2 The Triangle Cuts

The checked equations are stronger than the diagonal component formulas.
Take

$$
g:X\to X',
\qquad
f:FX'\to Y.
$$

The left triangle cut is

$$
\varepsilon[f]\circ F[\eta[g]]
\rightsquigarrow
f\circ F[g].
$$

Both sides are arrows $FX\to Y$. The unit moves $g$ into the $GF$ boundary,
the functor $F$ acts on that off-diagonal component, and the counit removes the
resulting $FG$ detour.

Dually, for

$$
f:X\to GY',
\qquad
g:Y'\to Y,
$$

the right triangle cut is

$$
G[\varepsilon[g]]\circ\eta[f]
\rightsquigarrow
G[g]\circ f.
$$

Both sides are arrows $X\to GY$. Setting $f$ and $g$ to suitable identities
recovers the familiar pointwise triangle identities. Retaining arbitrary
$f$ and $g$ exhibits the naturality and higher action consumed by the cut.

<!-- evidence:ADJ-TRIANGLE-CUTS -->

> **Formal status — checked.** Evidence `ADJ-TRIANGLE-CUTS`. The indexed
> owner is `Adjunction`; `unit_adj_transf` and
> `counit_adj_transf` expose the rigid observations that trigger both
> runtime reductions.

These are the chapter's central checked computations. They illustrate the
general policy from Chapter 9: a universal detour reduces only at the
universal construction that owns it.

## 12.3 Transposing Arrows

The ordinary hom formulation of the same adjunction is a natural equivalence

$$
\Phi_{a,b}:
\operatorname{Hom}_B(Fa,b)
\simeq
\operatorname{Hom}_A(a,Gb).
$$

Starting from the unit and counit, its two directions are

$$
\begin{aligned}
\Phi_{a,b}(u)&=G[u]\circ\eta_a,\\
\Phi^{-1}_{a,b}(v)&=\varepsilon_b\circ F[v].
\end{aligned}
$$

The triangle identities cancel the introduced unit-counit pairs, while
naturality makes the construction contravariant in $a$ and covariant in $b$.
This is why transposition is more than a family of bijections: it is a
comparison of represented hom functors.

In the active interface, let $M:I\to A$ and $H:K\to B$ be arbitrary probes.
The reindexed comparison has the profunctor form

$$
\operatorname{Hom}_B(FM,H)
\simeq
\operatorname{Hom}_A(M,GH).
$$

The endpoints $I$ and $K$ remain variable, so naturality in both arguments is
part of the comparison. Maps into either side can be pushed across the
adjunction and pulled back, with beta and eta computation supplied by the
generic comparison owner.

<!-- evidence:ADJ-HOM-PROF-COMPARISON -->

> **Formal status — checked.** Evidence
> `ADJ-HOM-PROF-COMPARISON`.
> `Adjunction_hom_prof_comparison` is the binary representable
> comparison, and `Adjunction_hom_prof_comparison_along` reindexes it
> along arbitrary probes. Its push/pull beta and eta laws are inherited from
> `ProfComparison`; no second adjunction-specific cancellation calculus is
> added.

The component formulas above are the mathematical reading of this package.
The stable runtime owner is the profunctor comparison, not a global rewrite
that expands every mate into a unit/counit composite.

## 12.4 Adjoints As Representability

Fix $F:A\to B$ and an object $b:B$. The contravariant hom functor

$$
a\longmapsto\operatorname{Hom}_B(Fa,b)
$$

is represented by an object $Gb$ exactly when there is a natural equivalence

$$
\operatorname{Hom}_B(F{-},b)
\simeq
\operatorname{Hom}_A({-},Gb).
$$

If such representing objects are chosen coherently as $b$ varies, they form a
functor $G:B\to A$, and the representations assemble into $F\dashv G$.
Conversely, an adjunction supplies these representations by its hom
comparison.

This characterization explains the direction of the terminology. A *right
adjoint* assigns representing objects to the functors
$\operatorname{Hom}_B(F{-},b)$; a *left adjoint* is the functor whose
outgoing homs are being represented.

<!-- evidence:UCAT-ADJOINT-REPRESENTABILITY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-ADJOINT-REPRESENTABILITY`. The equivalence between ordinary
> adjunction data and coherent pointwise representability belongs to the
> univalent 1-category development. The active code checks the forward
> adjunction-to-profunctor comparison and has chosen representation packages,
> but it does not reconstruct a general adjunction from arbitrary local
> representations.

Chapter 13 will supply the Yoneda theorem that makes representing objects
unique in the correct sense. Chapter 16 will then define weighted limits by
the same pattern.

## 12.5 Uniqueness Of Adjoints

Suppose $F:A\to B$ has two right adjoints $G$ and $G'$. Their hom
representations give, for every $b$,

$$
\operatorname{Hom}_A(-,Gb)
\simeq
\operatorname{Hom}_B(F-,b)
\simeq
\operatorname{Hom}_A(-,G'b).
$$

Yoneda turns this into a canonical isomorphism $Gb\cong G'b$, natural in
$b$. If $A$ is an ordinary univalent category, those isomorphisms determine
identity of the right-adjoint functors. Hence the type asserting that $F$ has
a right adjoint is a mere proposition under the appropriate univalence
hypothesis.

<!-- evidence:UCAT-ADJOINT-UNIQUENESS -->

> **Formal status — mathematical development.** Evidence
> `UCAT-ADJOINT-UNIQUENESS`. This is the ordinary HoTT theorem. A native
> version must choose among identity, natural isomorphism, adjoint
> equivalence, and omega-equivalence while retaining higher coherence.

Uniqueness therefore does not mean that all chosen units and counits are
judgmentally the same. It means that the space of choices has the claimed
truncation once categorical identity has been aligned with the relevant
equivalence.

## 12.6 A Ladder Of Equivalence Notions

The word *equivalence* will be qualified according to the following table.

| Notion | Data or property | What it controls |
| --- | --- | --- |
| carrier equivalence | a `TypeEquiv` between decoded classifiers | elements and identity structure of two carriers |
| ordinary object isomorphism | inverse arrows $x\rightleftarrows y$ inside one category | categorical sameness of two objects at the 1-cell level |
| isomorphism of precategories | a functor that is fully faithful and whose object map is a carrier equivalence | strict invertibility of the whole ordinary presentation |
| categorical equivalence | a functor with a quasi-inverse promoted to coherent adjoint-equivalence data | sameness up to natural isomorphism |
| weak equivalence | fully faithful and merely essentially surjective | property-level ordinary categorical equivalence criterion |
| native omega-equivalence | a selected arrow with recursively usable inverse evidence | equivalence inside an arbitrary native iterated category |

These rows interact only through explicit theorems. A carrier equivalence
between object types need not preserve homs. An ordinary isomorphism compares
objects in one category, not two entire categories. A categorical equivalence
uses functors and natural isomorphisms. Native omega-equivalence can be
applied to objects of `Cat_cat`, but its recursive equality-valued
interface is not definitionally the HoTT package of fully faithful and
essentially surjective data.

## 12.7 Full Faithfulness And Essential Surjectivity

For an ordinary functor $F:\mathcal A\to\mathcal B$:

- $F$ is **fully faithful** if every hom map from
  $\operatorname{Hom}_{\mathcal A}(a,a')$ to
  $\operatorname{Hom}_{\mathcal B}(Fa,Fa')$ is an equivalence;
- $F$ is **split essentially surjective** if each $b:\mathcal B$ comes with a
  chosen $a:\mathcal A$ and a chosen isomorphism $Fa\cong b$;
- $F$ is **essentially surjective** if the existence of such $a$ and such an
  isomorphism is merely asserted.

For ordinary precategories, an adjoint equivalence yields full faithfulness
and split essential surjectivity, and those chosen data reconstruct an
adjoint equivalence. Replacing split existence by mere existence gives the
weaker property traditionally called a weak equivalence.

When both sides are univalent categories, full faithfulness makes the type of
possible preimages of an object a proposition. Essential surjectivity can
then be upgraded to a coherent choice, so weak equivalence and categorical
equivalence agree. The same univalence also turns an equivalence into an
isomorphism of the underlying precategory presentations.

<!-- evidence:UCAT-EQUIVALENCE-CRITERIA -->

> **Formal status — mathematical development.** Evidence
> `UCAT-EQUIVALENCE-CRITERIA`. These are the ordinary HoTT
> 1-categorical equivalence theorems. No native fully-faithful or
> essentially-surjective package with coherent higher action is claimed
> active.

The distinction between split and mere essential surjectivity is constructive,
not bureaucratic. An adjoint equivalence needs data that can be applied; a
mere existence statement deliberately hides its witness. Univalence supplies
the uniqueness needed to recover that data in the ordinary categorical case.

## 12.8 Adjointification

Sometimes one begins with a functor $F$, a proposed inverse $G$, and natural
isomorphisms

$$
GF\cong\mathrm{id}_A,
\qquad
FG\cong\mathrm{id}_B
$$

whose chosen unit and counit do not yet satisfy the triangle equations. In
ordinary category theory, one of the two isomorphisms can be adjusted so that
the triangles hold. This **adjointification** turns equivalence data into an
adjoint equivalence.

The triangles are therefore coherent normalization data, not an arbitrary
extra burden. They make mate transposition inverse in a controlled way and
permit universal cuts to reduce without choosing a fresh proof at every use.

> **Formal status — mathematical development.** Ordinary adjointification is
> part of the 1-categorical theory. The active `Adjunction` relation starts
> with a selected triangle-computing witness; it does not expose a generic
> constructor that adjusts arbitrary quasi-inverse transfors.

## 12.9 Identity Of Ordinary Categories

There is one further univalent step. For ordinary precategories, identity of
the complete precategory structures corresponds to isomorphism of
precategories: a fully faithful functor whose object map is a carrier
equivalence. When the precategories are univalent categories, categorical
equivalence and such isomorphism agree. Consequently identity of ordinary
categories corresponds to equivalence of categories.

Schematically,

$$
(\mathcal A=\mathcal B)
\simeq
(\mathcal A\cong\mathcal B)
\simeq
(\mathcal A\simeq_{\mathrm{cat}}\mathcal B),
$$

with the second comparison restricted to univalent categories. Since the type
of functors has the expected 1-categorical truncation, the type of ordinary
categories is a 2-type.

<!-- evidence:UCAT-CATEGORY-IDENTITY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-CATEGORY-IDENTITY`. This is the ordinary HoTT result, not a checked
> identity-to-equivalence theorem for the native universe `Cat_cat`. Chapter
> 15 places it in the broader structure-identity and saturation programme.

## 12.10 What The Active Equivalence Layer Proves

At the object level, the active code packages carrier equivalence and native
omega-equivalence separately. It also lifts ordinary isomorphism evidence to
native omega-equivalence evidence.

<!-- evidence:EQUIV-ORDINARY-ISO-LIFT -->

> **Formal status — checked.** Evidence
> `EQUIV-ORDINARY-ISO-LIFT`. The lift is one-way and retains the ordinary
> forward arrow. It does not prove the full-faithful/essentially-surjective
> characterization of functors.

At the functor level, an adjunction has checked triangle cuts and a checked
binary representable comparison. These facts are sufficient for the later
weighted-limit preservation theorem. They are not yet a complete native
theory of categorical equivalence.

## 12.11 The Native Higher Boundary

A higher fully-faithful functor should compare whole hom-categories, then the
homs between their arrows, and so on. A higher essential-surjectivity
condition should specify which equivalence witnesses inhabit its fibres and
whether their evidence is propositional. Turning those conditions into a
native adjoint equivalence would require:

- iterable hom-equivalence packages;
- a coherent object-level essential-surjectivity interface;
- natural unit and counit transfors with full off-diagonal action;
- triangle coherence at every retained level;
- a chosen relationship with object identity or saturation.

> **Formal status — research boundary.** The missing result is a native
> fully-faithful-plus-essentially-surjective characterization compatible with
> `OmegaEquiv`, `Functor_cat`, and higher transfors. Ordinary HoTT
> equivalence theorems are used only in their stated 1-categorical
> specialization.

The next chapter begins where the ordinary and native stories already meet:
representable homs. Yoneda explains why their maps are controlled by elements;
the checked co-Yoneda cut then gives that explanation a directed
profunctorial computation.
