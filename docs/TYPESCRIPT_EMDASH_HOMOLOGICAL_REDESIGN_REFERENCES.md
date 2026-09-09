# Homological And Categorical-Spectra Redesign References

Date: 2026-09-07

Status: reference inventory; HRI-11 to HRI-17 substantively reviewed; selected HRI-01/02/03 and HRI-18 material reviewed on 2026-09-08

## Purpose And Scope

The user supplied these references while prioritizing a working proof–CAS
baseline for bounded long exact homology. Keep them available for a later
literature-informed redesign of the logical, computational, and internal
formulation. Bibliographic metadata and the three supplied local PDF/text
pairs were checked on the date above; detailed mathematical assessment,
section-by-section reading, and reproduction of external formalizations were
initially deferred for HRI-01 to HRI-10. Proposed relevance there is a research
question, not an assertion that an emdash construction follows from a cited
theorem.

The user subsequently requested immediate review of seven constructive
category/homalg papers. HRI-11 to HRI-17 now have a
[dedicated substantive review](TYPESCRIPT_EMDASH_POSUR_HOMALG_REDESIGN_REVIEW.md)
with exact reading coverage, source locators, hypotheses, architecture
implications and limitations. This does not retroactively claim a full
review of the earlier spectral/coherence inventory.

The active implementation remains governed by
[the bounded long-exact plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md).
This inventory does not begin spectra, spectral sequences, unbounded
complexes, derived categories, or an orthogonal strictness/cubical migration.

The subsequent [homology internalization review](TYPESCRIPT_EMDASH_HOMOLOGY_INTERNALIZATION_REDESIGN_REVIEW.md)
records selected reading of HRI-01's introduction/matrix construction/coherence
statement, HRI-02's fiber-sequence, indexing and truncation strategy, and
HRI-03's actual module-complex/exact-couple/cohomology source. It also records
selected sections of the newly supplied Cisinski et al. draft (HRI-18).
These are targeted readings, not full reviews of those books or successful
builds of the historical Lean code.

## Coherence, Biproducts, And The Abelian Reference Layer

### HRI-01 — Zoran Petrić and Mladen Zekić

*Coherence for closed categories with biproducts*, arXiv:2001.09736v4,
26 March 2022. The abstract concerns symmetric monoidal closed categories
with biproducts and related compact/dagger variants.
[Versioned primary record](https://arxiv.org/abs/2001.09736v4).

Verified local copies:

- `/home/user1/dosen-book/dosen-petric-zekic-Coherence-for-closed-categories-with-biproducts-2001.09736v4.pdf`
- `/home/user1/dosen-book/dosen-petric-zekic-Coherence-for-closed-categories-with-biproducts-2001.09736v4.txt`

Future questions: can its Došen-related coherence techniques inform the
internal additive/biproduct syntax, choice of computational owners, or
normal forms? Do not infer a normalization theorem for arbitrary Abelian
categories, kernels/cokernels, or homological algebra from this coherence
result without examining its hypotheses and exact equality notion.

## Synthetic Homotopy Theory, Homology, And Spectral Sequences

### HRI-02 — Floris van Doorn

*On the Formalization of Higher Inductive Types and Synthetic Homotopy
Theory*, dissertation, 2018; arXiv:1808.10690v1, 31 August 2018. Its abstract
reports Lean formalizations of the Atiyah–Hirzebruch and Serre cohomological
spectral sequences. [Primary record](https://arxiv.org/abs/1808.10690v1).

Verified local copies:

- `/home/user1/algebraic-geometry/vandoorn-On-the-Formalization-of-Higher-Inductive-Types-and-Synthetic-Homotopy-Theory-1808.10690v1.pdf`
- `/home/user1/algebraic-geometry/vandoorn-On-the-Formalization-of-Higher-Inductive-Types-and-Synthetic-Homotopy-Theory-1808.10690v1.txt`

Future questions: compare synthetic connecting operations, exactness, exact
couples, and stabilization with the current constructive Abelian/CAS
reference. Investigate which constructions admit whole internal families
and natural transformations, rather than preserving today's component-path
packaging by default.

### HRI-03 — CMU HoTT spectral-sequence formalization

[cmu-phil/Spectral](https://github.com/cmu-phil/spectral) is a Lean 2
formalization. Its README points to `cohomology.serre` and
`algebra.exact_couple`, and describes the spectrum-sequence/exact-couple
route to the Serre and Atiyah–Hirzebruch constructions. Treat the old Lean 2
code as reference material, not as a current Lean 4 dependency.

Shallow local checkout, acquired 2026-09-07:

- directory: `/home/user1/algebraic-geometry/cmu-phil-spectral`
- revision: `3b078f5f1de251637decf04bd3fc8aa01930a6b3`
- verified entry points: `README.md`, `algebra/exact_couple.hlean`, and
  `cohomology/serre.hlean`

Initially only metadata, the README, and file locations were inspected. No historical
toolchain was installed or executed and no build success is claimed. First
locate the definitions and assumptions relevant to an actual redesign
question before attempting reproduction. The checkout is external reference
material, not vendored emdash source or an active runtime dependency.

On 2026-09-08 the user also identified `/home/user1/cmu-phil-spectral`.
It is clean at the same revision. The internalization review records the
additional inspected source sections and preserves the no-build boundary.

### HRI-04 — Ulrik Buchholtz, Floris van Doorn, and Egbert Rijke

*Higher Groups in Homotopy Type Theory*, arXiv:1802.04315v1,
12 February 2018. Relevant topics include higher groups, deloopings,
connective spectra, and stabilization.
[Primary record](https://arxiv.org/abs/1802.04315v1).

No local PDF is recorded by this inventory yet. Review the loop/pointed
assumptions explicitly before comparing this framework with directed,
varying-endpoint internal Homs.

### HRI-05 — Floris van Doorn, HoTTEST 2018 slides

[User-supplied official slide link](https://florisvandoorn.com/talks/HoTTEST2018.pdf).
Retain as a complementary explanatory source. The slide contents and local
download remain unreviewed here; do not assign particular results or a more
specific talk title without checking the PDF.

## Categorical Spectra And Bi-Infinite Categories

### HRI-06 — Hadrian Heine

*Stable homotopy theory of higher categories*, arXiv:2605.05195v1,
6 May 2026. The abstract describes stabilization by inverting endomorphism
categories, categorical Brown representability, and resulting long exact
sequences. [Primary record](https://arxiv.org/abs/2605.05195v1).

Verified local copies:

- `/home/user1/algebraic-geometry/Heine-Stable-homotopy-theory-of-higher-categories-2605.05195v1.pdf`
- `/home/user1/algebraic-geometry/Heine-Stable-homotopy-theory-of-higher-categories-2605.05195v1.txt`

Future questions: identify the precise suspension/endomorphism construction,
stable-range hypotheses, categorical Freudenthal/Brown results, and
homology-theory interfaces. Compare these with emdash's directed internal
Hom interpretation without assuming that endomorphism-based stabilization
is the only possible design.

### HRI-07 — David Kern

*Categorical spectra as pointed (∞, ℤ)-categories*, arXiv:2410.02578;
the checked record is v2, 4 November 2024.
[Versioned primary record](https://arxiv.org/abs/2410.02578v2).

The abstract compares categorical spectra with pointed weak ℤ-categories.
The user's suggested initial reading is Section 3, especially the spectrum
construction/comparison and Corollary 3.3.5 on ordinary spectra as groupoidal
objects. Verify those locators against the selected version before quoting
them; v2 records a newly added Section 3.2 on monoidal structures. No local
PDF is recorded here yet.

### HRI-08 — Germán Stefanich

*Higher Quasicoherent Sheaves*, PhD thesis, UC Berkeley, 2021.
[University bibliographic record](https://pantheon.math.berkeley.edu/publications/higher-quasicoherent-sheaves).

The user identifies Chapter 13, “Categorical Spectra,” for the general
construction, enriched variants, cells, and examples. The thesis metadata
was checked; the chapter locator and contents remain to be checked during
the full review. The university's second listed name is the advisor, not
an additional thesis author. No local thesis copy is recorded here yet.

### HRI-09 — Paul Lessard

*ℤ-Categories I*, arXiv:2206.00849v1, 2 June 2022. Relevant topics include
bi-infinite categorical dimension, homotopy-coherent ℤ-categories,
combinatorial spectra, and category-weighted spectrification.
[Primary record](https://arxiv.org/abs/2206.00849v1).

Future questions: compare its cellular/simplicial descriptions with the
existing internal dependent-Hom and simplex infrastructure; distinguish
strict models, weak models, and groupoidal specializations. No local PDF is
recorded here yet.

### HRI-10 — Naruki Masuda

*The Algebra of Categorical Spectra*, originally a July 2024 thesis;
arXiv:2605.03114v2, 7 August 2026. Relevant topics include the stabilized
lax Gray tensor product, categorical stability, and the cobordism hypothesis
with singularities. [Versioned primary record](https://arxiv.org/abs/2605.03114v2).

Version caution: the v2 metadata explicitly records removal of incorrect
claims about closure of strong Steiner complexes under partial duality
(Proposition 2.4.17 and Remark A.2.5). Pin the version and inspect that
correction before borrowing a duality argument. No local PDF is recorded
here yet.

## Constructive Categories And Proof-CAS: Reviewed Sources

The seven entries below were reviewed on 2026-09-07. See the dedicated
review for section/page locators and the distinction between source results
and proposed emdash applications. Companion `.txt` files exist beside every
listed PDF. The user-supplied PDFs were preserved; the final three entries
were downloaded from primary arXiv records without overwriting prior files.

### HRI-11 - Sebastian Posur

*On free abelian categories for theorem proving*,
[arXiv:2103.08379v1](https://arxiv.org/abs/2103.08379v1), 15 March 2021.

Local PDF:
`/home/user1/algebraic-geometry/posur-On-free-abelian-categories-for-theorem-proving-2103.08379v1.pdf`

Reviewed lead: Adelman categories, two-sided homotopy solving, finite
Z-linear universal diagrams, exact-functor interpretation, the universal
snake and Dowker's homology-map formula. Concrete rational examples do not
replace the universal interpretation or its integral coefficient boundary.

### HRI-12 - Sebastian Posur

*Closing the category of finitely presented functors under images made
constructive*, [arXiv:1911.11469v3](https://arxiv.org/abs/1911.11469v3),
31 August 2020; [Compositionality DOI](https://doi.org/10.32408/compositionality-2-4).

Local PDF:
`/home/user1/algebraic-geometry/posur-Closing-the-category-of-finitely-presented-functors-under-images-made-constructive-1911.11469v3.pdf`

Reviewed lead: Q(P)'s cospan/subquotient representation, syzygy inclusion
with witness transport, image/cokernel closure, and biased weak pullbacks.
The noncoherent example does not acquire general kernels or Abelianity.

### HRI-13 - Sebastian Posur

*Methods of constructive category theory*,
[arXiv:1908.04132v1](https://arxiv.org/abs/1908.04132v1), 12 August 2019.

Local PDF:
`/home/user1/algebraic-geometry/posur-Methods-of-constructive-category-theory-1908.04132v1.pdf`

Reviewed lead: category constructors, homomorphism structures, natural
transformations, generalized morphisms and diagrammatic computation. Its
generalized inverses are not ordinary sections. Remark 2.19 distinguishes
constructing the snake arrow from proving the snake lemma.

### HRI-14 - Sebastian Posur

*A constructive approach to Freyd categories*,
[arXiv:1712.03492v1](https://arxiv.org/abs/1712.03492v1), 10 December 2017;
[published DOI](https://doi.org/10.1007/s10485-020-09612-y).

Local PDF:
`/home/user1/algebraic-geometry/posur-A-constructive-approach-to-Freyd-categories-1712.03492v1.pdf`

Reviewed lead: selected weak kernels and their all-test factor operations,
decidable lifts, two-pullback kernels, normality, choice comparisons, and
lowering linear systems from iterated Freyd categories to the base. Keep
preprint-v1 versus published construction numbering explicit, as already
recorded in the Freyd Abelian implementation plan.

### HRI-15 - Mohamed Barakat And Daniel Robertz

*homalg: A meta-package for homological algebra*,
[arXiv:math/0701146v2](https://arxiv.org/abs/math/0701146v2), 23 July 2007;
*Journal of Algebra and Its Applications* 7 (2008), 299-317,
[DOI](https://doi.org/10.1142/S0219498808002813).

Downloaded PDF:
`/home/user1/algebraic-geometry/barakat-robertz-homalg-A-meta-package-for-homological-algebra-math-0701146v2.pdf`

Reviewed lead: effective membership/syzygy operations, functor and induced-map
interfaces, variance metadata, and long-exact construction through split
resolution rows. No canonical remainder form is required.

### HRI-16 - Mohamed Barakat And Markus Lange-Hegermann

*An axiomatic setup for algorithmic homological algebra and an alternative
approach to localization*, [arXiv:1003.1943v5](https://arxiv.org/abs/1003.1943v5),
26 October 2017; *Journal of Algebra and Its Applications* 10 (2011), 269-293,
[DOI](https://doi.org/10.1142/S0219498811004562).

Downloaded PDF:
`/home/user1/algebraic-geometry/barakat-lange-hegermann-An-axiomatic-setup-for-algorithmic-homological-algebra-1003.1943v5.pdf`

Version caution: v5 corrects a typo in Lemma 4.3's proof. The localization
result requires a commutative computable ring and a finitely generated
maximal ideal. The operational checklist
starts with an Abelian category; it does not prove Abelianity from unrelated
algorithms alone.

### HRI-17 - Mohamed Barakat, Markus Lange-Hegermann And Sebastian Posur

*Elimination via saturation*, [arXiv:1707.00925v3](https://arxiv.org/abs/1707.00925v3),
8 July 2020; original preprint submitted 4 July 2017.

Downloaded PDF:
`/home/user1/algebraic-geometry/barakat-lange-hegermann-posur-Elimination-via-saturation-1707.00925v3.pdf`

Reviewed lead: homogenization plus saturation computes elimination using
syzygies and membership without requiring block orders. Keep correctness,
termination hypotheses and performance claims separate; the reported
straightforward implementation was not faster than direct block elimination.

### HRI-18 — Cisinski, Cnossen, Nguyen And Walde

*Synthetic Category Theory*, book project, supplied draft dated September 7,
2026. The [author's publication page](https://cisinski.app.uni-regensburg.de/publikationen.html)
links the evolving project; use the local dated copy for the reviewed section
numbers rather than assuming every future online revision has the same text.

Local PDF/text pair:
`/home/user1/algebraic-geometry/cisinski-Book-project-Synthetic-Category-Theory-2026-sep-7.pdf`
and the corresponding `.txt` file.

Selected reading: introduction/contents; §5.9's functoriality of universals
and pointwise adjunction criterion; Corollaries 11.9.35–37 on complete Segal
animae/realization; Definition 15.1.1 and Definition 15.3.1, Lemma 15.3.2,
Theorem 15.3.4. The rest is not claimed as read.

The immediate design lead is assembling universal choices into whole
adjoint sections of genuine fibrations. The completion/realization boundary
also matters for `make_cat`-style constructors from ordinary data. The
stable-category chapters are longer-term guidance for fiber/cofiber methods,
not an implemented comparison with present module homology or authority to
import new stable/spectral foundations into the active goal.

### HRI-19 — Martin Markl And Dominik Trnka

*Kernels, lax algebras, décalage, and supercoherence*,
[arXiv:2601.20322v1](https://arxiv.org/abs/2601.20322v1), 28 January 2026.

Newly found during the 2026-09-09 adjunction-usability review. The abstract,
introduction and accessible arrow-(co)monad statements were checked; a
complete proof review or local PDF acquisition has not yet been performed.
It characterizes kernels in pointed categories through an arrow 2-monad and
relates them to a simplicial nerve/décalage formulation. This directly
intersects the pilot's adjunction and complementary simplicial/cubical ideas.

Do not identify the paper's lax-algebra comparisons with arbitrary emdash
extracted laxity cells or assume that all should be identities. Its
ordinary-category result is not automatically an arbitrary-omega emdash
construction. Retain it as focused design evidence, not a new prerequisite
to implement its entire theory before completing the homology/CAS goal.

## User's Independent Directed-Spectrum Hypothesis

Preserve this separately from the literature: the user proposes a notion of
categorical spectrum/suspension in which directed arrows need not be loops
or endomorphisms, based on emdash's simplicial interpretation of internalized
dependent Hom. This is an open design hypothesis, not an implemented
construction or an established identification with any cited framework.

A future review should ask:

1. What varies at the source and target of the directed Hom, and how is that
   variation internalized through existing whole families/actions?
2. What replaces, generalizes, or specializes pointed loop/endomorphism
   stabilization, without collapsing the directed endpoints prematurely?
3. How should homology/cohomology and their connecting morphisms become whole
   internal functors/transfors with useful computation?
4. What exactness, suspension, and stability hypotheses are required, and
   which ordinary/groupoidal cases must be recovered by checked comparisons?
5. Which computational laws should be runtime normal forms, proof-time
   usability comparisons, or derived paths? Coherence in a reference does
   not automatically supply a suitable emdash rewrite orientation.

The working proof–CAS baseline should supply algorithms, examples, selected
results, and regression laws for that redesign. It should not freeze its
present formal packaging or be delayed by this future literature review.
