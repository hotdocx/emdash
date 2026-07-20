<a id="how-to-read"></a>

# How To Read This Book

The shortest route is the [prologue](#prologue), followed by the prerequisite
glossary at the beginning of [Chapter 8](#chapter-8). The fuller route reads
Chapters 1–7 in order and then returns to the same proof with every interface
available. Chapters 9–10 then continue from the proof into transfors,
displayed laxity, representability, and profunctor cut elimination. The
[contents](#contents) and [glossary/index](#appendix-glossary) provide stable
anchor-based navigation.

Different readers may use the book differently:

- A type theorist can follow equality, induction, equivalence, and truncation,
  watching for the places where directed functor action replaces transport
  along an identity.
- A category theorist can begin with categories, functors, transfors, and
  Cat-valued families, treating the familiar type formers as dependent
  categorical constructions.
- An implementer can read the mathematical line first and consult the evidence
  notes, notation appendix, and source map only when a computational boundary
  matters.

Composition is written in categorical order:

$$
g\circ f : x\longrightarrow z
$$

means “first `f`, then `g`.” Functor action is written
`F[x]` on objects and `F[f]` on arrows. The path category
`Path(A)` retains equality-local, hence groupoidal, structure inside
the directed calculus. Symbols such as `W`, `*`,
`ell`, `Code`, `encode`, and `power` are
mathematical abbreviations; the notation appendix maps them to active
Lambdapi names.

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
