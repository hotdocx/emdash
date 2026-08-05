<a id="how-to-read"></a>

# How To Read This Book

The shortest route is the [prologue](#prologue), followed by the compact
prerequisite review and proof in [Chapter 8](#chapter-8). The foundational
route reads Chapters [1](#chapter-1)–[7](#chapter-7) first and then returns to
the same calculation with every interface available. The second spiral begins
with the cut calculus in [Chapter 9](#chapter-9), develops ordinary and native
category theory through [Chapter 15](#chapter-15), and culminates in weighted
universals, duality, and join in Chapters [16](#chapter-16)–[17](#chapter-17).
The local-to-global spiral begins with presheaves and sieves in
[Chapter 18](#chapter-18), then selects covers and formulates descent in
[Chapter 19](#chapter-19), and constructs Cat-valued sheafification by direct
cover completion in [Chapter 20](#chapter-20). [Chapter 21](#chapter-21) adds
the representation-free commutative algebra that turns invertibility into
computational affine charts, and [Chapter 22](#chapter-22) constructs the
functor-of-points bridge from $D(f)$ and localization to the generated big
Zariski site. [Chapter 23](#chapter-23) begins with a supplied global ringed
object, recognizes two constructively generating regions as affine, imposes
topology-local ring behaviour on the actual slice, and derives a selected
chart intersection from the global structure presheaf.
[Chapter 24](#chapter-24) constructs Laurent coordinate changes on that
literal overlap, packages the resulting supplied projective-line capability,
and separates it from the still-unconstructed graded `Proj` route. The
[contents](#contents) and
[glossary/index](#appendix-glossary) provide stable anchor-based navigation.

Five reading paths make the dependencies explicit:

| Reader | Main path | Consult when needed |
| --- | --- | --- |
| type theorist | Prologue; Chapters 1, 3–8, 10, and 15 | Chapters 2 and 9 for directed action; Appendix G for the formal presentation |
| category theorist | Prologue; Chapters 2, 5, and 8–24 | Chapters 1, 3, 4, and 7 for equality, propositions, univalence, and height |
| algebraic geometer | Chapters 13, 16, and 18–24 | Chapters 2, 3, 5, 6, and 12 for the directed, logical, inductive, universal, and adjoint foundations |
| implementer | Chapters 1, 2, 6, 8, and 9; Appendices A, B, E, F, and G | the theorem chapters whose evidence route is being inspected |
| external reviewer | Chapters 2.6, 8, and 9; then the integrated reviewer, live or local | Appendices A, B, F, and G for notation, evidence, status, and architecture |

These are paths through one dependency graph, not separate foundations. In
particular, the category-theory route still uses equality-local reasoning, and
the type-theory route still needs directed functor action.

For the executable-review path, open the
[integrated reviewer](https://hotdocx.github.io/emdash/) or run
`./scripts/pnpmw run reviewer:dev` from the repository root. The wholly
client-side workbench offers editable examples across the four binder modes.
It lets the reader inspect explicit Core, inferred and expected classifiers,
structural lowering, computation, and source-located failures; the same page
runs the three-part research report and opens this book. Its text notation is
a bounded executable subset. The mathematical notation used throughout the
book is intentionally broader and should not be read as a complete parser
grammar.

Composition is written in categorical order:

$$
g\circ f : x\longrightarrow z
$$

means “first $f$, then $g$.” Functor action is written $F[x]$ on objects and
$F[f]$ on arrows. The path category $\mathsf{Path}(A)$ retains equality-local,
hence groupoidal, structure inside the directed calculus. Symbols such as
$W$, $*$, $\ell$, $\mathsf{Code}$, $\mathsf{encode}$, and
$\mathsf{power}$ are mathematical abbreviations; the notation appendix maps
them to active Lambdapi names.

## Evidence Status

Every theorem-like assertion has one of four evidence statuses:

- **Checked.** An active declaration and a regression or reviewer example
  establish the stated interface.
- **Formal consequence.** The assertion follows from named checked interfaces,
  but the library does not yet package the result under the stated name.
- **Mathematical development.** The theory is developed in ordinary
  mathematics with explicit prerequisites and a plausible future emdash
  owner.
- **Research boundary.** A construction is conjectural, underspecified, or
  blocked on named infrastructure.

A typical note looks like this:

> **Formal status — checked.** Evidence `WE-HOM-NAT-CARRIER`.

The evidence identifier resolves through `book/evidence.json` to
declarations and executable checks. It is traceability metadata, not a
replacement for the proof in the prose.

The active Lambdapi sources outrank the book. The current implementation and
safe-development procedure are described in the repository’s current-status
report; the canonical-syntax report owns the mathematical notation, which is
broader than the reviewed executable text subset. Dated reports preserve
design history but do not silently revive retired interfaces.

Passages structurally or conceptually adapted from the *Homotopy Type Theory*
book, Zeuner's constructive algebraic geometry, and Pédrot's computational
sheafification work are versioned and section-mapped in
`book/references/third-party-sources.json`. The relevant licenses and kinds of
adaptation are recorded there, and emdash's mathematical changes are stated
rather than hidden behind a change of symbols.
