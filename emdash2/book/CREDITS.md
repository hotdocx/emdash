<a id="book-credits"></a>

# Credits And Third-Party Attribution

This development edition is prepared by the emdash contributors.
Individual authorship and editorial credits will be made explicit before a
public edition is released.

## Homotopy Type Theory book

The organization and adapted passages of this book are inspired by:

> The Univalent Foundations Program, *Homotopy Type Theory: Univalent
> Foundations of Mathematics*, Institute for Advanced Study, 2013.

The reviewed source is the
[HoTT Book repository](https://github.com/HoTT/book) at revision
`578b85cc8d586b1677ec4335148adeb443057d24` (2026-05-12).
That work is licensed under the
[Creative Commons Attribution-ShareAlike 3.0 Unported
License](https://creativecommons.org/licenses/by-sa/3.0/).

Any adapted material in this book is modified for a directed,
category-theoretic setting. In particular, the circle/integer calculation is
not reproduced as the WalkingEnd/Nat calculation: invertible paths are
replaced by genuinely directed arrows, integer powers by natural powers, and
the hard inverse by a directed normalization cell followed by
one-dimensionality. Chapter 26 then returns to the Circle itself and adapts
the universal-cover encode–decode architecture to the checked emdash
Circle/Integer construction, including its distinct computational and
categorical boundaries.

The exact source map and adaptation ledger live in
`references/third-party-sources.json`. They were established before the
corresponding prose was drafted. The Chapter 8 vertical slice records
structural and conceptual adaptations from the pinned source, while Chapters
10–15 adapt all nine sections of `categories.tex`, Chapter 26 records the
Circle HIT and universal-cover source map, and Appendix G adapts all four
parts of `formal.tex`. The resulting prose is newly written for the directed
categorical setting; the ledger records the source labels, adaptation kind,
and target under this attribution and ShareAlike notice.

## Max Zeuner's constructive algebraic geometry

The local-to-global geometry spiral takes mathematical and expository
inspiration from:

> Max Zeuner, *Univalent Foundations of Constructive Algebraic Geometry*,
> arXiv:2407.17362v1, 2024.

The reviewed [arXiv version](https://arxiv.org/abs/2407.17362) is licensed
under the [Creative Commons Attribution 4.0 International
License](https://creativecommons.org/licenses/by/4.0/). Chapter 18 adapts the
locally ringed lattice's largest compact-open invertibility support into a
comparison with the sieve $D_U(s)$ of all invertibility probes. This is a
change of organizing viewpoint: the compact open remains the appropriate
representative in Zeuner's coherent or qcqs setting when it exists, while the
sieve is defined on a general site before representability is known. Chapter
22 structurally adapts the Zariski-lattice, coverage, compact-open, and
functor-of-points narrative to this sieve-first organization: a supplied
localization represents $D_R(f)$ pointwise, and the big-site topology is
generated from selected finite localization charts. Neither chapter imports
Zeuner's qcqs comparison theorem or general scheme theorem as an emdash
result. Chapter 23 comparatively adapts the finite affine-cover architecture,
but reverses the direction of construction: its global ringed object is
supplied first, two charts constructively generate one retained covering
sieve, and restrictions and a selected intersection are inherited from that
single object. It does not import Zeuner's gluing theorem, compact-open
classifier, or equivalence between functorial and locally ringed-lattice qcqs
schemes. Chapter 24 carries that finite-cover rhythm and comparison boundary
into a supplied projective-line presentation, but its Laurent calculation and
explicit `Proj` horizon are an emdash synthesis rather than a construction
drawn from Zeuner's thesis. The source sections, targets, adaptation kinds,
and mathematical changes are recorded in
`references/third-party-sources.json`.

## Pierre-Marie Pédrot's computational sheafification

The return/glue/silent presentation in Chapter 20 takes conceptual and
structural inspiration from:

> Pierre-Marie Pédrot, “Pursuing Shtuck,” preprint, 2023.

The reviewed [HAL version](https://inria.hal.science/hal-04251754v1) is
licensed under the [Creative Commons Attribution 4.0 International
License](https://creativecommons.org/licenses/by/4.0/). Pédrot presents free
sheaves by a return constructor, a branching glue constructor, and an equation
that erases a branch whose result is ignored, then explains the last as a
silent transition. Emdash adapts that computational picture to actual varying
cover questions in categorical semantics: the branches are matching objects
of Cat-valued presheaves, and the checked endpoint is a whole Hom-category
universal property and reflector. The book does not import the paper's
internal type theory, metatheory, universe claims, or dependent-elimination
results. Exact source sections and adaptation boundaries are recorded in
`references/third-party-sources.json`.

## Došen's cut-elimination perspective

The four-level cut calculus in Chapter 9 takes conceptual inspiration from
Kosta Došen's *Cut Elimination in Categories* (Kluwer, 1999). The cited work
is not licensed for textual adaptation here. It is used only as a
bibliographic and conceptual reference: the exposition, notation, examples,
and emdash correspondence in this book are newly written, and no passage from
Došen's text is copied or closely paraphrased.

## Hadzihasanovic's higher-categorical diagrams

Chapter 28 uses the Gray-product and oriented-cube discussion in Amar
Hadzihasanovic's *Combinatorics of Higher-Categorical Diagrams*,
arXiv:2404.07273v2, as comparative mathematical orientation. The source is
cited rather than textually adapted: no passage is copied or closely
paraphrased. In particular, the chapter distinguishes Hadzihasanovic's
combinatorially constructed higher-dimensional products from emdash's checked
and deliberately narrower experiment—one profiled right closure and its
walking-square interchanger. The exact sections and reference-only boundary
are recorded in `references/third-party-sources.json`.
