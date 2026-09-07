# Homological And Categorical-Spectra Redesign References

Date: 2026-09-07

Status: retained future-research inventory; not an implementation plan or a completed literature review

## Purpose And Scope

The user supplied these references while prioritizing a working proof–CAS
baseline for bounded long exact homology. Keep them available for a later
literature-informed redesign of the logical, computational, and internal
formulation. Bibliographic metadata and the three supplied local PDF/text
pairs were checked on the date above; detailed mathematical assessment,
section-by-section reading, and reproduction of external formalizations are
deferred. Proposed relevance below is a research question, not an assertion
that an emdash construction follows from a cited theorem.

The active implementation remains governed by
[the bounded long-exact plan](TYPESCRIPT_EMDASH_BOUNDED_LONG_EXACT_HOMOLOGY_AND_BOOK_PLAN.md).
This inventory does not begin spectra, spectral sequences, unbounded
complexes, derived categories, or an orthogonal strictness/cubical migration.

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

Only metadata, the README, and file locations were inspected. No historical
toolchain was installed or executed and no build success is claimed. First
locate the definitions and assumptions relevant to an actual redesign
question before attempting reproduction. The checkout is external reference
material, not vendored emdash source or an active runtime dependency.

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
