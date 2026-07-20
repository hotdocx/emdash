<a id="how-to-read"></a>

# How To Read This Book

The shortest route is the [prologue](#prologue), followed by the compact
prerequisite review and proof in [Chapter 8](#chapter-8). The foundational
route reads Chapters [1](#chapter-1)–[7](#chapter-7) first and then returns to
the same calculation with every interface available. The second spiral begins
with the cut calculus in [Chapter 9](#chapter-9), develops ordinary and native
category theory through [Chapter 15](#chapter-15), and culminates in weighted
universals, duality, and join in Chapters [16](#chapter-16)–[17](#chapter-17).
The [contents](#contents) and [glossary/index](#appendix-glossary) provide
stable anchor-based navigation.

Three reading paths make the dependencies explicit:

| Reader | Main path | Consult when needed |
| --- | --- | --- |
| type theorist | Prologue; Chapters 1, 3–8, 10, and 15 | Chapters 2 and 9 for directed action; Appendix G for the formal presentation |
| category theorist | Prologue; Chapters 2, 5, and 8–17 | Chapters 1, 3, 4, and 7 for equality, propositions, univalence, and height |
| implementer | Chapters 1, 2, 6, 8, and 9; Appendices A, B, E, F, and G | the theorem chapters whose evidence route is being inspected |

These are paths through one dependency graph, not separate foundations. In
particular, the category-theory route still uses equality-local reasoning, and
the type-theory route still needs directed functor action.

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
report; canonical comment and future parser notation live in the canonical
surface-syntax report. Dated reports preserve design history but do not
silently revive retired interfaces.

Passages structurally or conceptually adapted from the *Homotopy Type Theory*
book are revision-pinned in
`book/references/third-party-sources.json`. The book is licensed to
permit that adaptation, and the directed changes are stated rather than hidden
behind a change of symbols.
