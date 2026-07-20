<a id="chapter-15"></a>

# 15. Structure Identity And Saturation

Univalence is most useful when it propagates from bare carriers to the
structures mathematicians put on them. The *structure identity principle*
says that structure-preserving equivalence is the identity of structured
objects. *Saturation* asks the complementary question: if a categorical
presentation does not yet have the desired identity-to-equivalence property,
can it be completed universally into one that does?

The ordinary 1-categorical answers are the structure identity theorem and
Rezk completion. They also reveal the architecture a directed version would
need. Evidence must be a property when it is intended to be inessential;
transport of structure must act coherently; the selected equivalence notion
must be stated; and a completion is characterized by its mapping property,
not merely by a newly constructed carrier.

This chapter adapts Sections 9.8 and 9.9 of the
[HoTT Book](#ref-hott-book). The ordinary theorems are mathematical
development. Emdash already checks several local ingredients, but a general
native structure identity principle and Rezk completion remain research
boundaries.

## 15.1 Truncation And Saturation Answer Different Questions

The following distinctions are essential.

| Condition | What it controls | What it does not supply |
| --- | --- | --- |
| object truncation | the height of $x=y$ | a comparison with categorical equivalence |
| finite `IsNCat` evidence | recursive height of hom-categories | category univalence |
| ordinary category saturation | $(x=y)\simeq(x\cong y)$ | proposition-valued object identity |
| dagger saturation | $(x=y)\simeq(x\cong_\dagger y)$ | identity with every ordinary isomorphism |
| prospective native saturation | identity agrees with one specified higher equivalence classifier | a canonical choice of that classifier |

A strict category can therefore be unsaturated, while a saturated category
can have a non-set-valued object type. Likewise, the finite-height theorem
used for WalkingEnd bounds identity types but does not turn an arbitrary
ordinary isomorphism into object identity.

## 15.2 A Notion Of Structure Over A Carrier Category

Let $\mathcal X$ be an ordinary precategory. A notion of structure $(P,H)$
over $\mathcal X$ consists of:

1. a type $P(x)$ of structures on each object $x$;
2. for $f:x\to y$, $\alpha:P(x)$, and $\beta:P(y)$, a proposition
   $H_{\alpha,\beta}(f)$ saying that $f$ preserves the structures;
3. evidence that identity arrows preserve structure;
4. evidence that composites of structure-preserving arrows preserve
   structure.

For structures $\alpha,\beta:P(x)$ on the same carrier, define

$$
\alpha\leq_x\beta
:\!\!\equiv
H_{\alpha,\beta}(\mathrm{id}_x).
$$

Identity and composition make this a preorder. The notion of structure is
called *standard* when this preorder is antisymmetric in every fibre. In
particular, each $P(x)$ is then a set.

The associated precategory
$\mathsf{Str}_{P,H}(\mathcal X)$ has objects

$$
(x,\alpha):\sum_{x:\operatorname{Obj}(\mathcal X)}P(x)
$$

and arrows

$$
(x,\alpha)\longrightarrow(y,\beta)
\quad:=\quad
\sum_{f:x\to y}H_{\alpha,\beta}(f).
$$

Because $H$ is proposition-valued, it adds a preservation condition without
adding competing arrow data. Identities and composition come from
$\mathcal X$ and the two closure laws.

## 15.3 The Ordinary Structure Identity Theorem

> **Structure identity principle.** If $\mathcal X$ is an ordinary univalent
> category and $(P,H)$ is a standard notion of structure over it, then
> $\mathsf{Str}_{P,H}(\mathcal X)$ is an ordinary univalent category.

The proof isolates the two uses of uniqueness. An identity

$$
(x,\alpha)=(y,\beta)
$$

is a carrier identity $p:x=y$ together with

$$
\operatorname{transport}_{P}(p,\alpha)=\beta.
$$

Since the structure fibres are sets, the second clause is a proposition. An
isomorphism of structured objects is a carrier isomorphism $f:x\cong y$
together with preservation by $f$ and by $f^{-1}$; those clauses are also
propositions.

Univalence of $\mathcal X$ converts $f$ into a carrier identity $p$. By
identity induction, it remains to consider $p\equiv\mathrm{refl}_x$. The two
preservation clauses then say

$$
\alpha\leq_x\beta
\qquad\text{and}\qquad
\beta\leq_x\alpha.
$$

Antisymmetry gives $\alpha=\beta$. This constructs the inverse to
`idtoiso` for structured objects; proposition-valuedness supplies the
remaining coherence.

<!-- evidence:UCAT-STRUCTURE-IDENTITY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-STRUCTURE-IDENTITY`. The theorem is the ordinary HoTT structure
> identity principle. It depends on set-valued homs, proposition-valued
> preservation, base-category univalence, and fibrewise antisymmetry.

## 15.4 Examples And The Role Of Standardness

Functor structure is a representative example. Begin with object functions
$F_0:\operatorname{Obj}(\mathcal A)\to\operatorname{Obj}(\mathcal B)$.
The additional structure assigns arrow actions preserving identities and
composition. A pointwise family of arrows is a homomorphism exactly when it
is natural. If $\mathcal B$ is univalent, the structure identity theorem
recovers the functor-category result from Chapter 11: natural isomorphism
agrees with identity of functors.

Ordinary algebraic and relational structures fit the same scheme. A signature
specifies operations and relations on a carrier set, while $H$ says that a
function preserves them. Function extensionality and proposition
extensionality make the structure fibres sets; mutual preservation by the
identity function forces equality of structures. Thus isomorphic groups,
rings, ordered sets, and similar standard structures become identical in
their univalent categories.

Standardness is not cosmetic. If two distinct structures on the same carrier
admit identity-carrier homomorphisms in both directions, structured
isomorphism contains less discriminating information than structure
identity. The theorem correctly refuses to identify them until antisymmetry
or an appropriate higher replacement has been supplied.

## 15.5 Checked Native Footholds

The active theory contains four ingredients that a native structure identity
theorem should reuse.

First, truncation evidence is proposition-valued at every implemented level.
Adding an `IsTruncGrpd` field to a carrier package therefore does not add a
second independent notion of identity between witnesses.

Second, for a fixed arrow, native equality-valued omega-equivalence evidence
is proposition-valued. The chosen arrow remains data, but two proofs that the
same arrow is an omega-equivalence agree.

Third, the packaged universes of truncated classifiers have a local
structure-identity theorem: package identity is equivalent to
`TypeEquiv` of the retained carriers. This is the closest checked example
of univalence propagating through an evidence field.

Fourth, ordinary isomorphism evidence maps one way into native
omega-equivalence evidence, and finite `IsNCat` evidence yields the expected
object-truncation bound. These maps organize nearby notions without asserting
the missing reverse object-identity comparison.

<!-- evidence:LOGIC-TRUNCATION-EVIDENCE-PROP -->
<!-- evidence:EQUIV-EVIDENCE-PROP -->
<!-- evidence:UNIV-TRUNCATED -->
<!-- evidence:EQUIV-ORDINARY-ISO-LIFT -->
<!-- evidence:CAT-DIMENSION -->

> **Formal status — checked.** Evidence
> `LOGIC-TRUNCATION-EVIDENCE-PROP`, `EQUIV-EVIDENCE-PROP`,
> `UNIV-TRUNCATED`, `EQUIV-ORDINARY-ISO-LIFT`, and
> `CAT-DIMENSION`. These are local evidence-property, package-univalence,
> comparison, and truncation theorems. Their conjunction is not a generic
> structure identity principle.

## 15.6 A Plausible Native Structure-Identity Interface

The ordinary $(P,H)$ schema suppresses the higher cells of preservation
evidence. A directed native version should expose them. One plausible
architecture begins with:

- a native carrier category $K$;
- a directed family $S:K\to\mathsf{Cat}$ of structures;
- for each base arrow $f:x\to y$ and structures
  $\alpha:S(x)$, $\beta:S(y)$, a category
  $H_f(\alpha,\beta)$ of structure-preserving lifts;
- identity, composition, and higher action for those lifts;
- a selected classifier
  $\operatorname{StructuredEquiv}((x,\alpha),(y,\beta))$.

The total category of structures is Sigma-shaped, but a general
$H_f(\alpha,\beta)$ may carry more information than the canonical transport
arrow of a bare directed family. A *standardness* condition must say exactly
when that extra information is property-like and when it is genuinely higher
structure.

The prospective comparison is

$$
\operatorname{idtoStructuredEquiv}:
\bigl((x,\alpha)=(y,\beta)\bigr)
\longrightarrow
\operatorname{StructuredEquiv}
  \bigl((x,\alpha),(y,\beta)\bigr).
$$

A native SIP would prove this to be an equivalence under qualified base
univalence and standardness hypotheses, while retaining its off-diagonal and
next-hom action. The target might use ordinary isomorphism, adjoint
equivalence, or native omega-equivalence; the theorem cannot be stated
honestly until that choice is part of the signature.

<!-- evidence:NATIVE-STRUCTURE-IDENTITY -->

> **Formal status — research boundary.** Evidence
> `NATIVE-STRUCTURE-IDENTITY`. The active `Catd`, `Sigma_cat`,
> `Hom_catd`, evidence-property, and equivalence interfaces are plausible
> ingredients, but there is no generic structure signature,
> structured-equivalence classifier, or identity theorem. Side task
> `FTTX-S9` records this prospective owner.

## 15.7 Weak Equivalences And The Universal Property Of Completion

Return to ordinary precategories. A functor

$$
I:\mathcal A\longrightarrow\widehat{\mathcal A}
$$

is a *weak equivalence* when it is fully faithful and essentially surjective,
where essential surjectivity is merely inhabited rather than split by a
chosen inverse on objects. A Rezk completion of $\mathcal A$ consists of such
an $I$ with $\widehat{\mathcal A}$ an ordinary univalent category.

The construction is characterized by what saturated targets see. For every
ordinary univalent category $\mathcal C$, precomposition induces

$$
I^*:
\mathcal C^{\widehat{\mathcal A}}
\longrightarrow
\mathcal C^{\mathcal A},
\qquad
G\longmapsto G\circ I,
$$

and $I^*$ is an isomorphism of ordinary precategories. Equivalently, every
functor $\mathcal A\to\mathcal C$ extends essentially uniquely across $I$,
and every natural transformation between extensions is determined by its
restriction.

The word *universal* belongs here, not merely in the statement that
$\widehat{\mathcal A}$ is saturated. Any two completions with this mapping
property are uniquely equivalent in the appropriate functor category.

## 15.8 Why Saturated Targets See Weak Equivalences As Equivalences

The proof of the mapping property is a lesson in constructive uniqueness.
If $I$ is essentially surjective, a natural transformation out of
$\widehat{\mathcal A}$ is determined by its components on the image of $I$;
this makes precomposition faithful. Fullness of $I$, together with essential
surjectivity, reconstructs the missing components and proves naturality, so
precomposition is fully faithful.

To extend a functor on objects, one knows only that each object of
$\widehat{\mathcal A}$ is isomorphic to something in the image. Choosing an
arbitrary representative would require choice. Instead one describes the
candidate image and its comparison data as a contractible type. The crucial
step uses univalence of $\mathcal C$: uniqueness up to unique isomorphism
becomes uniqueness by identity, which is enough to define a function. This
proves essential surjectivity of $I^*$ and hence the mapping property.

In short, saturated targets turn weak equivalences into equivalences of
functor categories.

The converse detects saturation. An ordinary precategory $\mathcal C$ is
univalent exactly when every weak equivalence
$H:\mathcal A\to\mathcal B$ makes

$$
H^*:\mathcal C^{\mathcal B}\longrightarrow\mathcal C^{\mathcal A}
$$

an isomorphism. For the reverse implication, apply the assumption to a Rezk
completion $I:\mathcal C\to\widehat{\mathcal C}$. Precomposition then
constructs an inverse to $I$, making $\mathcal C$ isomorphic to the
univalent category $\widehat{\mathcal C}$ and hence univalent itself.

This characterization also explains why a weak equivalence need not be an
isomorphism between unsaturated presentations. It becomes invertible to every
target precisely when object isomorphism in that target can be absorbed as
identity.

## 15.9 The Yoneda-Image Completion

The first construction uses Chapter 13. Let

$$
\mathsf{PSh}(\mathcal A)
:=\mathsf{Set}^{\mathcal A^{\mathrm{op}}}.
$$

Define $\widehat{\mathcal A}$ to be the full subcategory whose objects are
presheaves $P$ for which there merely exists an $a:\mathcal A$ and an
isomorphism

$$
y(a)\cong P.
$$

The ambient presheaf category is univalent, and the condition of being merely
representable is a proposition, so the full subcategory is univalent. The
Yoneda embedding

$$
y:\mathcal A\longrightarrow\widehat{\mathcal A}
$$

is fully faithful by Yoneda and essentially surjective by the definition of
the image. It is therefore a Rezk completion.

This proof is short because representability has already packaged the
necessary universal coordinates. Its cost is universe size: the presheaf
category may live in a larger universe than $\mathcal A$.

## 15.10 The Higher-Inductive Completion

A second construction stays closer to the original universe by freely adding
the missing object identities. Its object type
$\operatorname{Obj}(\widehat{\mathcal A})$ is generated by:

- $i(a)$ for every object $a:\mathcal A$;
- a path $j(e):i(a)=i(b)$ for every isomorphism $e:a\cong b$;
- coherences $j(\mathrm{id}_a)=\mathrm{refl}_{i(a)}$ and
  $j(g\circ f)=j(f)\mathbin{\cdot}j(g)$;
- 1-truncation, so parallel 2-paths agree.

The hom family is then defined by double induction on the new object type,
starting with

$$
\operatorname{Hom}_{\widehat{\mathcal A}}(i(a),i(b))
:=\operatorname{Hom}_{\mathcal A}(a,b).
$$

Transport along $j(e)$ is postcomposition or precomposition by $e$ and its
inverse. The identity and composition laws of $\mathcal A$ discharge the HIT
coherences, after which identities and composition on the new hom family are
defined by induction.

To show saturation, use encode-decode:

$$
\begin{aligned}
\operatorname{encode}_{x,y}&:
(x=y)\longrightarrow(x\cong y),
&&\operatorname{encode}=\operatorname{idtoiso},\\
\operatorname{decode}_{x,y}&:
(x\cong y)\longrightarrow(x=y),
&&\operatorname{decode}(e)=j(e)
\text{ on generators}.
\end{aligned}
$$

Induction over the HIT and its paths proves both composites. The identity and
composition constructors are precisely the cases needed for the code family
of isomorphisms to respect reflexivity and path concatenation. Finally,
$I(a):=i(a)$ is fully faithful by construction and essentially surjective by
HIT induction.

<!-- evidence:UCAT-REZK-COMPLETION -->

> **Formal status — mathematical development.** Evidence
> `UCAT-REZK-COMPLETION`. The ordinary theorem states that every
> precategory has a univalent Rezk completion, constructed either as the
> Yoneda image or by the 1-truncated HIT above, and that weak equivalences
> into univalent targets have the stated functor-category mapping property.

## 15.11 The Encode-Decode Analogy With WalkingEnd

The HIT proof deliberately echoes Chapter 8, but the two constructions solve
different problems.

| Feature | WalkingEnd | Rezk-completion HIT |
| --- | --- | --- |
| generators | one object and one directed loop | old objects and paths for old isomorphisms |
| code | natural powers of the loop | isomorphisms between completed objects |
| decode | contextual directed normalization | a path constructor $j(e)$ |
| invertibility | the loop is checked noninvertible | every added generator is a path and hence invertible |
| purpose | compute the free directed endomorphism monoid | saturate object identity |

Both proofs define a code family, construct encode and decode, and calculate
two composites by the relevant eliminator. That is an analogy of proof
architecture. WalkingEnd is **not** a Rezk completion: its defining loop is
not an isomorphism, its hom corresponds to natural numbers, and its universal
problem is directed generation rather than saturation.

<!-- evidence:WE-LOOP-NONINVERTIBLE -->

> **Formal status — checked comparison.** Evidence
> `WE-LOOP-NONINVERTIBLE` verifies the decisive negative fact on the
> WalkingEnd side. The Rezk construction in the other column remains the
> ordinary mathematical development above.

## 15.12 Specification Of A Native Rezk Completion

A native completion cannot be obtained by replacing the word “isomorphism”
with “equivalence” and leaving the rest implicit. A prospective interface
must specify:

1. a classifier $\mathsf{Eqv}_C(x,y)$ of the selected categorical sameness;
2. a coherent map $(x=y)\to\mathsf{Eqv}_C(x,y)$;
3. the saturation predicate asserting that this map is an equivalence;
4. a category $\operatorname{Rezk}(C)$ and unit functor
   $\eta_C:C\to\operatorname{Rezk}(C)$;
5. local full faithfulness at every retained hom dimension and essential
   surjectivity relative to $\mathsf{Eqv}$;
6. for every saturated $D$, an equivalence between the iterable functor
   categories out of $\operatorname{Rezk}(C)$ and out of $C$;
7. naturality of that mapping equivalence in $D$, together with its
   transformation and higher-cell action.

Ordinary isomorphism, adjoint equivalence, and native omega-equivalence are
different candidates for $\mathsf{Eqv}$. Chapter 10 supplies maps among some
of them, but no general theorem chooses one as object identity in every
native category. The completion’s higher universal property must therefore
be designed together with its saturation predicate.

<!-- evidence:NATIVE-REZK-COMPLETION -->

> **Formal status — research boundary.** Evidence
> `NATIVE-REZK-COMPLETION`. No native saturation predicate, completion
> object, unit weak equivalence, or iterable mapping property is active.
> Constructing a carrier without these laws would not discharge
> `FTTX-S9`.

## 15.13 Identity Principles And Universal Constructions

The two halves of the chapter meet in a useful division of labor. A structure
identity theorem proves that a well-behaved construction *preserves*
saturation: structured objects over a saturated carrier form another
saturated category. Rezk completion *creates* saturation from a presentation
that lacks it. Yoneda supplies one completion because representables turn
objects into universal coordinates; the HIT supplies another because
encode-decode computes the freely generated identity structure.

Chapters 16 and 17 now return to universal constructions internal to a fixed
categorical world. Their limits, colimits, and joins do not require a native
Rezk completion to be stated, but the distinction between presentation and
saturated identity will remain visible whenever uniqueness is upgraded from
equivalence to equality.
