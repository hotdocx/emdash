# Posur And Homalg: Constructive Categories And Proof-CAS Design

Date: 2026-09-07

Status: substantive literature review; design guidance, not implementation authority

## Scope And Reading Record

This review answers the user's request to assess seven papers now, while
preserving the working bounded long-exact proof-CAS baseline. It supplements
the [reference inventory](TYPESCRIPT_EMDASH_HOMOLOGICAL_REDESIGN_REFERENCES.md)
and informs the [living implementation plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md).
It does not start spectral sequences, an omega-categorical stabilization,
a new universal theorem prover, or a replacement of the current kernel.

Primary arXiv records and local versions were checked. Four papers were
already supplied as PDF/text pairs; three additional open-access preprints
were downloaded with companion text extractions. Original PDFs were not
edited. Page numbers below are the printed pages of the pinned versions.
Examples and external implementations were read, not executed for this review.
Citation counts supplied by the user were not used as technical evidence.

| Inventory ID | Pinned source | Reading coverage |
|---|---|---|
| HRI-11 | Posur, *On free abelian categories for theorem proving*, [2103.08379v1](https://arxiv.org/abs/2103.08379v1), 15 March 2021 | Complete substantive text and references; key diagrams/formulas visually checked on pp.3-5, 9, 13-14, 17 |
| HRI-12 | Posur, *Closing the category of finitely presented functors under images made constructive*, [1911.11469v3](https://arxiv.org/abs/1911.11469v3), 31 August 2020 | Mathematical body, sections 1-5; visual checks on pp.5, 21, 24, 29, 31 |
| HRI-13 | Posur, *Methods of constructive category theory*, [1908.04132v1](https://arxiv.org/abs/1908.04132v1), 12 August 2019 | Complete substantive text and references; visual checks on pp.26, 42, 44-45 |
| HRI-14 | Posur, *A constructive approach to Freyd categories*, [1712.03492v1](https://arxiv.org/abs/1712.03492v1), 10 December 2017 | Sections 1-4, 5.3, 6 and Appendix A; statements of the undecidability examples inspected, not every proof in 5.1-5.2; section 7 applications not reviewed in detail; visual checks on pp.8, 11, 37 |
| HRI-15 | Barakat-Robertz, *homalg: A meta-package for homological algebra*, [math/0701146v2](https://arxiv.org/abs/math/0701146v2), 23 July 2007; journal 2008 | Main text 1-7, Appendices A-B and selected Appendix C examples; visual checks on pp.19-20 |
| HRI-16 | Barakat-Lange-Hegermann, *An axiomatic setup for algorithmic homological algebra and an alternative approach to localization*, [1003.1943v5](https://arxiv.org/abs/1003.1943v5), 26 October 2017; journal 2011 | Main text 1-7 and Appendix A; visual checks on pp.11-12; v5 corrects the proof of Lemma 4.3 |
| HRI-17 | Barakat-Lange-Hegermann-Posur, *Elimination via saturation*, [1707.00925v3](https://arxiv.org/abs/1707.00925v3), 8 July 2020 | Complete seven-page text, including Appendix A; page 6 visually checked for the module formula and localization arrows |

HRI-14's preprint-v1 Constructions 3.13/3.14 correspond to the published
3.14/3.15 numbering already identified in the
[Abelian implementation plan](TYPESCRIPT_EMDASH_FREYD_ABELIAN_COMPUTATION_PLAN.md).
This is a version distinction, not automatically an implementation defect.
HRI-11's reference `[Pos20]` is the foundational Freyd paper, not HRI-13.

## Main Conclusion

The papers reinforce a computation-first categorical architecture, but
distinguish three different constructions. They should not be conflated
into one datatype or one unqualified claim of computable Abelian structure.

| Construction | Intended object | Main role and algorithmic boundary |
|---|---|---|
| Freyd A(P) | One presentation arrow R → A | Concrete finitely presented objects/functors; cokernels are formal constructions; weak kernels in P give Abelianity, and decidable lifts supply effective equality |
| Image completion Q(P) | A cospan A → Ω ← R | Images/subquotients without immediately converting them to fresh presentations; effective syzygy inclusion supplies its decision interface; it need not have kernels |
| Adelman Adel(A) | A composable pair R → A → C, not necessarily a complex | Free Abelian completion for universal instances; effective two-sided homotopy solving makes it computably Abelian |

The current concrete polynomial/Freyd runtime remains useful. A subquotient
representation and a universal-diagram computation mode are plausible
additional layers, not reasons to rename today's objects or discard the
tested baseline. An eventual emdash implementation should expose these
distinctions through typed category constructors and explicit capability
interfaces.

“Witness” below usually means computational data needed to construct the
next map: relation coefficients, factors or homotopies. It does not impose
a new priority of certifying every CAS step in the kernel. Trusted native
providers remain compatible with the user's usability-first objective;
their operation contracts and mathematical interpretation must still be
stated accurately.

## Free Abelian Categories As A Universal Computation Mode

### The extra structure is essential

HRI-11 Construction 1.3 (p.4) retains a relation and a corelation map:

```text
R_a → A → C_a.
```

Their composite need not be zero. A morphism has a middle datum and both
relation/corelation compatibility witnesses. In emdash's composition
convention, equality of middle data takes the form

```text
α − α′ = ρ_b ∘ σ₁ + σ₂ ∘ γ_a.
```

The second summand is not optional. A one-sided Freyd presentation cannot
be relabelled as an Adelman object. Remark 1.2 (p.3) interprets an arbitrary
composable pair by

```text
im(ker γ → coker ρ)
  ≅ ker γ / (im ρ ∩ ker γ).
```

Our current chain-pair homology is the zero-composite special case. A full
Adelman interpreter therefore needs the general image/subquotient operation.

### What the computation theorem gives

Constructions 1.5, 1.7 and 1.8, and Corollary 1.9 (pp.5-9), provide explicit
cokernels, kernels and normality. Definition 1.10/Theorem 1.11 (p.9) isolate
the remaining algorithmic problem: solve the two-sided homotopy equations
in the additive base. The implementation contract must distinguish a
solution with its witness from a negative decision. Resource exhaustion or
unsupported inputs are not negative decisions.

Example 1.13 (p.10) gives a concrete decidable fragment: finite acyclic
quivers with effectively supplied Z-linear path relations, followed by
additive closure. Homotopy solving reduces to linear algebra over finitely
presented Abelian groups and Hermite normal forms over Z. Arbitrary cyclic
quivers do not inherit this finite-path argument. A Q-linear backend also
cannot replace the Z-linear one when claiming results for all Abelian
categories: rationalization loses torsion.

Remark 1.12 decides zero objects, whether a *given arrow* is mono/epi/iso,
and inclusion/equality of supplied subobjects. It does not give a complete
prover for every homological assertion or decide whether arbitrary objects
admit some isomorphism.

### Universal interpretation is distinct from testing an example

The strategy of section 2 has three obligations: encode the premise by an
additive functor, compute the universal instance in Adel(A), and interpret
it through the exact extension of Theorem 2.2 (pp.10-11). The extension is
unique up to natural isomorphism, not literal equality of every selected
kernel or homology object. The target need not possess a decision procedure
once the universal construction/witness is available.

The universal snake is a strong future benchmark. Lemmas 2.5-2.7 reduce
its premise to three arrows with zero triple composite, closely matching
`AbelianSnakeTriple`. Figure 1 and Computation 2.8 (pp.12-14) give explicit
data and homotopy witnesses; Corollary 2.9 performs the universal transfer.
This is materially stronger than our constant-field comparison, which is
only a test of selected instances.

Remark 2.10 (p.14) suggests a second focused experiment. Dowker's connecting
map is induced by β between the chain pairs

```text
(a →α b →γβ d)  →  (a →βα c →γ d),
```

with identity outer components. The existing generic homology-map owner is
therefore relevant. Comparing this route to the current selected snake
arrow still requires correctly oriented endpoint isomorphisms and the
selected reconstruction law.

Lemma 2.11/Remark 2.12 (pp.14-16) compute the universal Hom as Z and single
out the two signs of its generator for exactness. This is a universal
statement qualified by endpoint automorphisms, not uniqueness of a chosen
connecting arrow from exactness in an arbitrary single instance.

Finally, encoding hypotheses is not automatic. The five-lemma requires a
refinement in Lemmas 2.17-2.18. Section 3 (p.20) proposes Serre quotients
for more general premises but supplies no general algorithm for the resulting
Serre-subcategory membership problem. Zero-composition relations alone do
not encode exactness, monicity or epicity.

## Freyd Operations, Actual Choices, And Effective Capabilities

HRI-14 Definition 3.1/Remark 3.3 (p.5) separate a morphism datum, its
relation-preservation witness, and witnesses for quotient equality.
Definition 3.4 (p.6) makes a weak kernel an object/arrow/annihilation datum
*plus a factor operation on arbitrary annihilated tests*. A matrix whose
columns happen to annihilate an arrow supplies only part of that interface.

Construction 3.6 (pp.6-7) gives cokernels without weak kernels. Construction
3.10 (pp.8-9) uses two weak pullbacks for a Freyd kernel; the supplied
zero-composite witness affects the raw induced map. Retaining those data
through execution and serialization is therefore computationally relevant,
even though quotient equality can identify different resulting representatives.

Theorem 3.5/Corollary 3.16 distinguish Abelianity from computable Abelianity.
Decidable lifts (Definition 3.12, p.9) require producing a lift or disproving
existence. Remark 3.17 and Theorem 5.9/Remark 5.10 show that weak-kernel
factor operations and decidable base equality do not automatically solve
arbitrary lifting problems. Definition 4.3 and Remark 4.4 (pp.15-16) make constructive coherence
include both syzygy generation and effective factoring through those syzygies.

Constructions 3.13/3.14 (requested v1, pp.10-12) support our normality
operations. Equation (5) is the row-convention counterpart of the current
column identity Q·U + F·V = id. The new explicit boundary-epicity constructor
therefore has a direct mathematical precedent, but does not supply cycle
universality by itself.

The selection issue is explicit in the source. Construction 3.18/Remark
3.19 (p.14) compare chosen cokernel operations by natural isomorphism;
Remark A.6 (p.37) explains that equal arrows need not have equal kernel
terms. Particular comparison isomorphisms arise from the universal operations.
This supports local selected-universal packages or constructed comparisons,
not forcing an abstract W to produce the native presentation by equality fiat.

Section 6 is especially useful for a categorical compiler. Theorem 6.3
(pp.25-26) lowers linear systems in iterated Freyd categories to systems in
the additive base by introducing relation/equality-witness unknowns.
Theorem 6.9/Corollary 6.10 (pp.27-28) use a homomorphism structure and
decidable lifts in its target. Iterating the constructor does not erase
these hypotheses; the special conclusions of 6.16-6.17 retain them.

## Images And Subquotients As Another Representation

HRI-12 represents a cospan A →γ Ω ←ρ R as

```text
im γ / (im γ ∩ im ρ)  ≅  (im γ + im ρ) / im ρ.
```

It does not assume im ρ ⊆ im γ. Definitions 2.1/2.4 (pp.4-5) formulate
syzygy inclusion with an essential positive output: an operation converting
every source syzygy and its witness into a target witness. A Boolean test
alone is insufficient. Remarks 2.6-2.7 relate this to decidable lifts.

Definitions 2.9 and 2.14-2.15 and Constructions 2.22-2.29 give the
syzygy-preserving morphisms, quotient equality, cokernels, images, normal
mono lifts and a suitable epi-colift operation. The latter uses a universal
annihilation test rather than assuming a kernel object exists.

Theorem 3.8 and Corollaries 3.9-3.10 (pp.18-20), under the section's
smallness convention, identify Q(P) with the image/cokernel closure of
representables in the functor category. The embedding of a Freyd presentation
is the cospan `(A →id A ←ρ R)`. Thus Q(P) can be a useful representation
of images/subquotients without repeatedly rebuilding a finite presentation.

Theorem 4.1 (pp.20-21) is a crucial limit: Q(P) is Abelian exactly when P
has weak kernels, in which case it coincides up to equivalence with finitely
presented functors. The noncoherent example of Theorem 5.2 has decidable
syzygy inclusion but an infinitely generated annihilator. It does not turn
all noncoherent finitely presented module categories into Abelian categories.

Definition 4.2/Lemma 4.4 and Construction 4.7 (pp.21-24) use biased weak
pullbacks, retaining only a designated projection's reconstruction. Individual
choices can be smaller (Example 4.6). That optimization belongs to this
cospan construction; it cannot simply delete a reconstruction required by
our current two-pullback Freyd proof.

## Generalized Morphisms And Whole Functorial Computation

HRI-13's category-constructor sequence leads from rings and additive closure
through Freyd categories and homomorphism structures to computations of
natural transformations between finitely presented functors (sections 1.4-1.7).
This is a direct precedent for operation roles above matrix algorithms,
not a reason to choose between a categorical interface and concrete vectors.

Sections 2.2-2.3 (pp.35-42) introduce generalized morphisms as spans modulo
equality of image subobjects. Reversing such a relation is a pseudo-inverse
in G(A), not a section or inverse in A. The graph functor is faithful, not
full; an expression must be shown to be *honest* before it represents an
ordinary arrow.

Theorem 2.18 (pp.42-43) expresses induced homology maps using these generalized
inverses. Section 2.5 does likewise for the snake arrow, but Remark 2.19
(p.45) explicitly distinguishes this construction from proving the snake
lemma. Sections 2.6-2.7 extend the calculus to defects and spectral-sequence
differentials. A future relational intermediate language must retain its
honesty/recovery obligation rather than treating inverse notation as a
primitive ordinary lift.

These are ordinary additive/Abelian constructions. Internalizing their
diagrams through emdash's Hom families is a separate design task; the papers
do not justify primitive hand-written square records or collapsing higher
action in the omega-category kernel.

## Homalg's Operational Requirements

HRI-15 section 1.2 (pp.3-4) requires effective membership coefficients and
generating syzygies, but not canonical normal forms. Sections 3.1.1-3.1.4
limit when a raw preimage automatically defines a module morphism: a free
source on a supplied free basis or a monic target map are the key cases. Sections 5-6.1.3 derive map
actions through natural embeddings, including homology into the incoming
differential's cokernel. Sections 7.2-7.4 construct resolution comparisons,
simultaneous resolutions and long exact sequences. Additivity applies to
the degreewise split resolution rows used there, not arbitrary short exact
rows. Appendix B.7 records variance/composition/derivation metadata.

HRI-16 Definition 2.1 (pp.3-4) lists 13 operations for an already Abelian
category; it is not an independent proof of Abelianity. Projective lifts
and hulls are extra operations 14-15. Definition 3.2/Theorem 3.4 (pp.6-8)
construct the operations using matrix solving. Section 5 separates categorical,
presentation, and matrix-engine layers. Theorem 4.1/Lemma 4.3/Proposition 4.5
(pp.10-12) reduce local systems to global ones for a commutative computable
ring at a finitely generated **maximal** ideal; the result is not an
unrestricted prime-localization API.
Remark 4.8 retains tasks such as local standard bases/Hilbert series outside
that optimization.

Our inference: separate mathematical equality, selected computational data,
and canonical serialization. Keep operation contracts with producing solvers;
do not make arbitrary preimage selection or field splitting a generic
module capability.

## Elimination As A Consumer Of The Same Algebraic Engine

HRI-17 Proposition 2.4 gives Iʰ = ⟨gʰ : g ∈ G⟩ : x₀^∞.
Lemma 2.7 identifies I ∩ B with Iʰ ∩ B; Corollary 2.9 extracts generators
by evaluating x₀,…,xₙ at zero after saturation. Section 2.4 extends this to
submodules. The ring maps in Appendix A are R → S[x₀⁻¹] ← S, not the
reverse localization arrows.

The algebraic identities hold over a unital commutative B; algorithmic
termination/effectivity has additional requirements. Syzygy-based ideal
quotients and a stabilizing saturation chain suffice in the stated settings.
Homogenizing generators alone can leave components at infinity (2.5-2.6).
The authors report that their straightforward implementation was slower
than direct block-order elimination; no performance superiority is claimed.

Our inference: homogenization, ideal quotient and saturation can become
alternative composable strategies over the existing syzygy/membership
engine, with explicit supported-ring/termination conditions. This is a
later focused-CAS extension, not a dependency of the current long-exact goal.

## Consequences For The Living Design

1. Preserve the working concrete baseline and its actual selected objects.
   Universal comparisons or per-choice packages should handle different
   representations; neither textual equality nor a fresh opaque object path
   supplies the missing interpretation. A shared selected owner may still
   compute definitionally by design. This is not a justification for opaque
   equality bridges between aliases of the same operation.
2. Make effective capabilities explicit: equality, lift solving, universal
   factor operations, syzygy inclusion with witness transport, and homotopy
   solving are different contracts. A trusted native implementation is an
   acceptable usability choice; finite replay alone is not the all-input
   operation promised by a universal capability.
3. Keep category constructors above interchangeable matrix algorithms.
   A(P), Q(P), and Adel(A) have different data and hypotheses. Their shared
   operations can use the same backend-neutral graph/operation machinery
   without being identified as one representation.
4. Consider universal-diagram computation as a separate future mode. Begin
   with the finite Z-linear universal snake and its exact-functor
   interpretation, or compare Dowker's homology-map formula with today's
   selected construction. Do not declare Q-linear examples universal or
   start a new kernel free-syntax/decidability-proof project implicitly.
5. Consider generalized morphisms as an intermediate computational language,
   with explicit honesty and recovery into ordinary arrows. Keep the
   current nonsplitting discipline and internal Hom-based diagrams.
6. Treat proof reconstruction/certification as optional, separately scoped
   assurance. The immediate purpose of witness data is usable computation
   and typed interoperability, as requested by the user.

No code architecture was replaced during this review. The pending formal
boundary-epicity and generic covered-reconstruction implementations are
preserved for subsequent integration. The stronger selected-cycle
universality, generic long-exact theorem, and book deliverables remain open.
