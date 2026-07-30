---
title: "Functorial Type Theory: Univalent Foundations for Mathematics"
authors: "The emdash contributors"
edition: "expanded development edition"
editionVersion: "0.3.0-dev"
publicationDate: "2026-07-30"
status: "draft"
license: "CC-BY-SA-3.0"
---
<!-- book-source:edition-notice book/frontmatter/00-title.md -->
<a id="edition-notice"></a>

## Expanded development edition

This is a working edition of *Functorial Type Theory: Univalent Foundations
for Mathematics*. The WalkingEnd/Nat encode-decode argument remains its
mathematical centre. Around it, the edition develops a second spiral through
cut elimination, category theory, weighted universal constructions, directed
duality, and a categorical-kernel-first formal presentation. Chapter details,
notation, and cross-references may still change. The active implementation
remains authoritative whenever prose and code disagree.

Copyright © 2026 the emdash contributors. Except where separately identified,
the book text is licensed under CC BY-SA 3.0. See
[Credits and Third-Party Attribution](#book-credits) and the source files
`book/CREDITS.md` and `book/LICENSE.md`.

> **Formal status — research boundary.** The title names the intended
> foundational programme. It does not assert that this edition already
> implements a finished proof assistant, every weak omega-categorical
> coherence, or a universal computational univalence principle.
<!-- /book-source:edition-notice -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:preface book/frontmatter/01-preface.md -->
<a id="preface"></a>

# Preface

Type theory is often introduced through terms and substitution. Category
theory is often introduced through objects and arrows. Functorial type theory
starts from the conviction that these are not two unrelated beginnings.
Substitution has action; action has coherence; and a useful formal language
should retain that structure rather than recover it after the fact.

The resulting theory has two kinds of motion. Equality supplies groupoidal
paths: they can be reversed, transported along, and compared through
equivalence and univalence. Categories supply directed arrows: an arrow may
have no inverse, and that failure is mathematical information. Functors act on
both objects and higher arrows. Cat-valued families turn dependent
substitution into directed reindexing. Transformations and their higher
components express the coherence of those actions.

This edition is organized around a single calculation because a foundation is
best learned while it is doing something. Consider an opaque category
generated, in the higher-inductive sense selected by emdash, by a base object
and one directed endomorphism. Its endomorphisms look like

$$
\mathrm{id},\quad \ell,\quad \ell^2,\quad \ell^3,\quad\ldots .
$$

The calculation proves that this list is exhaustive at the level of the
underlying carrier:

$$
\operatorname{Hom}_{W}(*,*) \simeq \mathbb{N}.
$$

The proof is not obtained by defining the hom to be a datatype of words.
Instead it constructs a Cat-valued code, transports zero forward along a
directed arrow, builds a contextual decoder, and produces a directed
normalization cell from every based arrow toward its coded power. Only then
does one-dimensionality turn that cell into equality. This order—directed
structure first, equality at the boundary—is the small example in which the
larger programme becomes visible.

The argument deliberately echoes the calculation
$\Omega(S^1)\simeq\mathbb{Z}$ in the *Homotopy Type Theory* book. The echo is
not an identification. A loop in an identity type is invertible, while the
walking endomorphism is not. The circle needs positive and negative powers;
the directed object has only natural powers. The circle’s code uses
univalence to turn successor on the integers into a path in a universe; the
directed code sends its generator directly to a successor functor, which need
not be an equivalence. What fails to transfer is as instructive as what does.

The title’s phrase “univalent foundations” therefore describes a layer, not a
device forced into every proof. Emdash contains checked equality,
equivalence, groupoid-univalence, restricted truncated-universe univalence,
and equality-valued omega-equivalence interfaces. The WalkingEnd calculation
also shows why a univalent foundation for directed mathematics must permit
actions that are not equivalences.

The exposition follows a spiral. The [prologue](#prologue) states the central
theorem with minimal prerequisites. Chapters 1–7 then develop the judgments,
categories, families, logic, equivalence, induction, directed higher
induction, and categorical height needed to understand the proof.
[Chapter 8](#chapter-8) returns to the calculation in full.

The later chapters move outward from that proof in a second spiral.
[Chapter 9](#chapter-9)
organizes functorial computation as a calculus of cuts. Chapters
[10](#chapter-10)–[15](#chapter-15) develop categories, functors, adjunctions,
Yoneda, duality, structure identity, and saturation. Chapters
[16](#chapter-16)–[17](#chapter-17) treat weighted limits and colimits before
returning to directed geometry through join. [Appendix G](#appendix-formal-presentation)
then states how the mathematical surface, checked categorical kernel, bounded
TypeScript elaborator through explicit Core, and external models fit together,
with the Lambdapi kernel remaining the mathematical authority.

The book is evidence-aware without being a source-code catalogue. Checked
claims name their evidence in compact notes. Free mathematical development is
welcome, but it is named as such and states what an emdash implementation
would require. This lets the prose reach beyond the current library without
blurring the line between a plausible design and a theorem already accepted
by the kernel.

> **Formal status — mathematical development.** This preface states the
> expository and research programme. Each theorem-like claim in the chapters
> carries its own status and, when checked, a machine-verified evidence link.
<!-- /book-source:preface -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:how-to-read book/frontmatter/02-how-to-read.md -->
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

Four reading paths make the dependencies explicit:

| Reader | Main path | Consult when needed |
| --- | --- | --- |
| type theorist | Prologue; Chapters 1, 3–8, 10, and 15 | Chapters 2 and 9 for directed action; Appendix G for the formal presentation |
| category theorist | Prologue; Chapters 2, 5, and 8–17 | Chapters 1, 3, 4, and 7 for equality, propositions, univalence, and height |
| implementer | Chapters 1, 2, 6, 8, and 9; Appendices A, B, E, F, and G | the theorem chapters whose evidence route is being inspected |
| external reviewer | Chapters 2.6, 8, and 9; then the integrated reviewer | Appendices A, B, F, and G for notation, evidence, status, and architecture |

These are paths through one dependency graph, not separate foundations. In
particular, the category-theory route still uses equality-local reasoning, and
the type-theory route still needs directed functor action.

For the executable-review path, run
`./scripts/pnpmw run reviewer:dev` from the repository root. The client lets
the reader edit a reviewed categorical expression, inspect its explicit Core
and checked classifier, run the three-part research report, and open this
book. Its text notation is a bounded executable subset. The mathematical
notation used throughout the book is intentionally broader and should not be
read as a complete parser grammar.

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
report; canonical comment and future parser notation live in the canonical
surface-syntax report. Dated reports preserve design history but do not
silently revive retired interfaces.

Passages structurally or conceptually adapted from the *Homotopy Type Theory*
book are revision-pinned in
`book/references/third-party-sources.json`. The book is licensed to
permit that adaptation, and the directed changes are stated rather than hidden
behind a change of symbols.
<!-- /book-source:how-to-read -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:contents book/frontmatter/03-contents.md -->
<a id="contents"></a>

# Contents

This contents list is generated from the ordered source manifest. Its links
use the explicit stable anchors owned by the chapter files.

## Front matter

- [Preface](#preface)
- [How To Read This Book](#how-to-read)

## Main text

- [Prologue: The Natural Number Hidden In A Directed Loop](#prologue)
- [1. Judgments, Universes, And Computation](#chapter-1)
- [2. Categories, Functors, And Directed Families](#chapter-2)
- [3. Logic, Propositions, And Sets](#chapter-3)
- [4. Equivalence And Univalence](#chapter-4)
- [5. Induction, Arrow Induction, And Universal Properties](#chapter-5)
- [6. Directed Higher Inductive Types](#chapter-6)
- [7. Truncation And Categorical Height](#chapter-7)
- [8. Synthetic Directed Homotopy Theory](#chapter-8)
- [9. Transfors And The Calculus Of Cuts](#chapter-9)
- [10. Categories, Precategories, And Categorical Identity](#chapter-10)
- [11. Functors, Transfors, And Functor Categories](#chapter-11)
- [12. Adjunctions And Equivalences](#chapter-12)
- [13. Yoneda, Representability, And Profunctors](#chapter-13)
- [14. Strictness, Dagger Structure, And Duality](#chapter-14)
- [15. Structure Identity And Saturation](#chapter-15)
- [16. Weighted Universal Constructions](#chapter-16)
- [17. Weighted Colimits, Duality, And Join](#chapter-17)

## Appendices

- [Appendix A. Notation](#appendix-notation)
- [Appendix B. Emdash Evidence](#appendix-evidence)
- [Appendix C. From The Circle To The Walking Endomorphism](#appendix-hott-correspondence)
- [Appendix D. Glossary And Concept Index](#appendix-glossary)
- [Appendix E. Computation And Normalization](#appendix-computation)
- [Appendix F. Implementation Status And Research Directions](#appendix-status)
- [Appendix G. Formal Presentation Of Functorial Type Theory](#appendix-formal-presentation)

## Back matter

- [Bibliography](#bibliography)
- [Credits And Third-Party Attribution](#book-credits)
- [License For The Book](#book-license)
<!-- /book-source:contents -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:prologue book/chapters/00-prologue.md -->
<a id="prologue"></a>

# Prologue: The Natural Number Hidden In A Directed Loop

Imagine a world with one distinguished place and one permitted step that
returns to it. Call the place `*` and the step `ell`. We may
stand still, take the step once, take it twice, and continue:

$$
\mathrm{id}_*,\qquad
\ell,\qquad
\ell\circ\ell,\qquad
\ell\circ\ell\circ\ell,\qquad\ldots .
$$

If this is the *free* directed situation, every journey from `*` back
to `*` should have a unique length. That sentence sounds obvious
only because it quietly identifies two descriptions:

1. the syntactic description of a journey as a finite word in one generator;
2. the universal object characterized by how maps out of it behave.

Functorial type theory keeps them apart. The walking endomorphism `W`
is presented opaquely by a category, a base, a directed loop, explicit
one-dimensionality, and a contextual elimination principle. Its object type,
hom-categories, identities, and composition do not reduce to a word datatype.

<!-- evidence:WE-SIGNATURE -->
<!-- evidence:WE-ONE-DIMENSIONAL -->

> **Formal status — checked.** Evidence `WE-SIGNATURE` and
> `WE-ONE-DIMENSIONAL`. One-dimensionality says that each
> hom-category is discrete; it neither makes `W` a discrete category
> nor makes `ell` invertible.

There is also a concrete category `BNat`. It has one object, natural
numbers as endomorphisms, zero as identity, and addition as composition. The
recursor for `W` gives a functor

$$
W\longrightarrow BNat
$$

sending `*` to the sole object and `ell` to one. This is the
expected arithmetic model. It is not a definition of `W`, and a
functor into a model cannot by itself prove that two arrows of `W`
with the same image are equal.

<!-- evidence:WE-BNAT-MODEL -->

> **Formal status — checked.** Evidence `WE-BNAT-MODEL`.
> `BNat` is separate model evidence. A reverse functor and a
> categorical equivalence have not been packaged.

The central theorem supplies the missing exhaustiveness statement by a
different route.

<!-- evidence:WE-HOM-NAT-CARRIER -->

> **Theorem preview.** There is an equivalence of underlying carriers
>
> $$
> \operatorname{Hom}_{W}(*,*)\simeq\mathbb{N}.
> $$
>
> **Formal status — checked.** Evidence `WE-HOM-NAT-CARRIER`. The
> current package is a `TypeEquiv`, together with a native
> equality-valued facade. A monoid or hom-category equivalence is not being
> asserted here.

## Measuring An Abstract Arrow

How can an opaque arrow be assigned a number? We construct a Cat-valued family

$$
\mathsf{Code}:W\longrightarrow\mathsf{Cat}
$$

whose fibre at `*` is the path category of natural numbers. The
generator acts by the successor functor. For any endpoint `x` and any
based arrow $p:* \to x$, define

$$
\mathsf{encode}_x(p)\;=\;\mathsf{Code}[p](0).
$$

This is directed transport in its plainest form: a functor acts on an object.
When `p` begins with the generator, its code begins with a successor.
There is no predecessor action because none was requested by the signature.

To go back, natural numbers produce powers:

$$
\ell^0=\mathrm{id}_*,
\qquad
\ell^{n+1}=\ell\circ\ell^n.
$$

At first this decoder exists only over the base. The decisive move is to
generalize it over every endpoint. The based representable family

$$
\mathsf{Rep}_*(x)=\operatorname{Hom}_W(*,x)
$$

acts on a base arrow by postcomposition. A displayed transformation

$$
\mathsf{decode}^{d}:\mathsf{Code}\Longrightarrow\mathsf{Rep}_*
$$

must therefore reconcile successor in `Code` with postcomposition by
`ell` in the representable. Its coherence winds forward through the
natural levels:

$$
\ell\circ\ell^n\longrightarrow\ell^{n+1}.
$$

This family of higher arrows is the **directed spiral**.

## Normalize Before Comparing

Applying the displayed decoder’s arrow action to
$p:* \to x$ at zero produces

$$
\nu_p:
p\longrightarrow
\mathsf{decode}_x(\mathsf{encode}_x(p))
$$

inside the hom-category `Hom_W(*,x)`. This is not initially an
equation. It is a directed 2-cell whose orientation records a normalization
process.

<!-- evidence:WE-NORMALIZATION-CELL -->

> **Formal status — checked.** Evidence `WE-NORMALIZATION-CELL`.
> The normalization cell is obtained from the contextual displayed
> eliminator; it is not postulated as a word-reduction axiom.

Only now is one-dimensionality used. The hom-category is discrete, so a cell
between parallel based arrows determines equality:

$$
p =
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

At the base, `decode` computes to `power`. Reversing the
displayed equality gives

$$
\ell^{\mathsf{encode}(p)}=p.
$$

The other composite is arithmetic. The generator-prefix equation and natural
number induction give

$$
\mathsf{encode}(\ell^n)=n.
$$

These two equations package the carrier equivalence.

<!-- evidence:WE-NORMALIZATION-PATH -->
<!-- evidence:WE-POWER-ENCODE -->
<!-- evidence:WE-ENCODE-POWER -->

> **Formal status — checked.** Evidence
> `WE-NORMALIZATION-PATH`, `WE-POWER-ENCODE`, and
> `WE-ENCODE-POWER`. Direction is retained until the first of these
> equalities is extracted.

## Why The Answer Is Not The Integers

For the circle, a loop is an equality path and therefore has an inverse. Its
powers are indexed by integers. Here `ell` is a directed arrow.
Nothing in the category laws manufactures a reverse arrow, and the calculation
detects that absence.

Encoding sends `ell` to one and the identity to zero. Consequently
the generator is not the identity. If an arrow `r` were a right
inverse, then encoding $\ell\circ r=\mathrm{id}$ would force a
successor to equal zero. Hence no right inverse exists, and in particular
`ell` carries no native omega-equivalence evidence.

<!-- evidence:WE-LOOP-NOT-IDENTITY -->
<!-- evidence:WE-LOOP-NO-RIGHT-INVERSE -->
<!-- evidence:WE-LOOP-NONINVERTIBLE -->

> **Formal status — checked.** Evidence
> `WE-LOOP-NOT-IDENTITY`,
> `WE-LOOP-NO-RIGHT-INVERSE`, and
> `WE-LOOP-NONINVERTIBLE`.

The missing negative integers are therefore not an incomplete case of the
proof. They are the numerical trace of directionality.

## The Road To The Proof

The next seven chapters unpack the interfaces used above.

- [Chapter 1](#chapter-1) separates definitional computation, proof-time
  comparison, and equality evidence.
- [Chapter 2](#chapter-2) introduces iterated hom-categories, functors,
  transfors, and directed Cat-valued families.
- [Chapter 3](#chapter-3) develops constructive logic, propositions, and sets.
- [Chapter 4](#chapter-4) distinguishes equality, ordinary equivalence,
  categorical isomorphism, and univalence.
- [Chapter 5](#chapter-5) moves from ordinary induction to arrow induction and
  contextual universal properties.
- [Chapter 6](#chapter-6) states the selected directed higher-inductive
  signature and its contextual eliminator.
- [Chapter 7](#chapter-7) explains categorical height and why a directed cell
  in a discrete hom-category yields equality.
- [Chapter 8](#chapter-8) returns to every step of the construction, including
  the spiral, the two inverse laws, and the noninvertibility consequences.

The second spiral asks what the same computational discipline contributes to
category theory. [Chapter 9](#chapter-9) isolates its cut calculus; Chapters
[10](#chapter-10)–[15](#chapter-15) develop categorical identity, functor
categories, adjunctions, Yoneda, duality, and saturation; and Chapters
[16](#chapter-16)–[17](#chapter-17) organize limits, colimits, and join by
representability and opposite duality. [Appendix G](#appendix-formal-presentation)
collects the formal rule schemas and states the metatheoretic boundary.

The larger aim is not merely to calculate one hom. It is to show how a type
theory can let groupoidal equality and noninvertible arrows coexist, interact,
and compute—without quietly turning one into the other.
<!-- /book-source:prologue -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-1 book/chapters/01-judgments-and-computation.md -->
<a id="chapter-1"></a>

# 1. Judgments, Universes, And Computation

A foundation does not begin by placing mathematical objects in a previously
given container. It begins by saying which expressions may be formed, which
expressions inhabit which classifiers, and which calculations count without
further proof. The elementary judgments have the familiar shape

$$
A\;\mathsf{classifier},\qquad a:A,\qquad a\equiv b:A.
$$

The last display uses $\equiv$ only as the glyph for *judgmental* or
definitional equality. It is not an inhabitant of an identity type. This
distinction will matter throughout the book: computation may make two
expressions the same input to every later rule, while a path is mathematical
data that can itself be transported, inverted, and compared.

Emdash represents its small type-like classifiers by a universe called
`Grpd`. A classifier `A:Grpd` decodes to the ambient type of its
elements, written mathematically simply as `a:A` and represented in the
kernel by `a:tau(A)`. This two-level presentation is an implementation
device. Unless a decoding boundary is at issue, we suppress `tau` and
reason in ordinary type-theoretic notation.

[Appendix G](#appendix-formal-presentation) gives the full formal reading of
this convention. It separates external contexts and typing judgments from
internal classifiers, then asks of each major construction for its formation,
introduction, elimination, computation, uniqueness, and functorial action.
The last two clauses will often be independent: a beta rule can be checked
even when a general uniqueness theorem remains open, and a pointwise
construction is incomplete until its arrow and higher-cell action is known.

<a id="chapter-1-1"></a>

## 1.1 Contexts And Families

A judgment rarely stands alone. It is made in a context:

$$
x:A,\quad y:B(x),\quad z:C(x,y)\;\vdash\;t:D(x,y,z).
$$

Each declaration may depend on those before it. Substitution replaces a
variable by a term of the right classifier and acts through every expression
that follows. In ordinary dependent type theory this action is often left
implicit in notation. Functorial type theory will progressively expose it:
first as path action, then as functor action on directed arrows, and finally
as coherent action on higher cells.

An ordinary function classifier is written

$$
A\longrightarrow B,
$$

and a dependent function classifier as

$$
\prod_{x:A}B(x).
$$

An element `f` of the second classifier assigns `f(x):B(x)`.
Lambda abstraction introduces such an element, and application to an
argument computes by beta reduction. The nondependent function classifier is
the constant-family case.

A dependent pair classifier is

$$
\sum_{x:A}B(x).
$$

An element is a pair `(x,u)` with `u:B(x)`. Equality of dependent
pairs is not merely a pair of unrelated equalities: it consists of a base
path together with a fibre path lying over that base path. Emdash exposes this
observation explicitly. For dependent functions it exposes pointwise path
observation and a converse function-extensionality constructor. Thus the
basic Sigma and Pi layers already carry the path structure later used in
equivalence and truncation arguments.

<!-- evidence:TT-SIGMA-PI-PATHS -->

> **Formal status — checked.** Evidence `TT-SIGMA-PI-PATHS` covers
> dependent-pair projections and path views together with the checked
> `happly`/`funext` equivalence for dependent functions. This is an
> implemented equality interface, not a claim that every future categorical
> section category is merely a pointwise Pi type.

<a id="chapter-1-2"></a>

## 1.2 Three Ways Expressions Agree

The word “equal” hides three operationally different relations in the current
development.

First, a **runtime rewrite** chooses a normal form. For example, applying the
Nat eliminator to zero returns its zero branch, while applying it to a
successor returns the successor branch with the recursive result. Such a rule
is part of computation: later expressions literally see the reduced term.

Second, a **proof-time comparison** helps elaboration recognize two typed
presentations without orienting either as the other's runtime normal form.
This is useful when a mathematical construction has two stable categorical
views—for example, a displayed-family facade and the corresponding ordinary
functor-category view. Proof-time comparison is intentionally narrower than
an equation available to the mathematician.

Third, an **identity term**

$$
p:x=_A y
$$

is internal evidence. It may be an argument to a function, the index of a
dependent family, or the object of a higher identity type. Its existence does
not by itself make `x` and `y` judgmentally interchangeable.

These layers cooperate, but they should not be conflated. A rewrite is chosen
because a form is intended to compute. A proof-time comparison is chosen
because two rigid presentations should elaborate together. A path is chosen
because equality is part of the mathematics. Much of emdash's engineering is
the discipline of putting a law at the right one of these layers.

As a small example, Nat addition is defined by recursion in its left input:

$$
0+n\equiv n,\qquad
\mathsf{succ}(m)+n\equiv\mathsf{succ}(m+n).
$$

Associativity is an identity term proved by Nat induction; it is not installed
as a global reassociation rewrite. The distinction keeps computation
predictable while leaving the algebra available propositionally.

> **Formal status — mathematical development.** The three-layer terminology
> is the book's explanation of the active kernel discipline. Exact rewrite
> and unification ownership remains an implementation matter governed by the
> current SOP; the mathematical chapters rely only on the checked interfaces
> cited in their evidence notes.

<a id="chapter-1-3"></a>

## 1.3 Elementary Inductive Classifiers

The initial object language contains classifiers for Empty, Unit, Bool, and
Nat. Their constructors have the expected readings:

$$
\begin{array}{c|c}
\mathsf{Empty} & \text{no constructor}\\
\mathsf{Unit} & \mathsf{tt}\\
\mathsf{Bool} & \mathsf{false},\mathsf{true}\\
\mathbb N & 0,\mathsf{succ}(n).
\end{array}
$$

An inductive classifier is characterized computationally by how dependent
data are defined from its constructors. For Nat, a motive
`P:Nat -> Grpd`, a base value `z:P(0)`, and a step

$$
s:\prod_{n:\mathbb N}P(n)\longrightarrow P(n+1)
$$

determine

$$
\mathsf{ind}_{\mathbb N}(P,z,s,n):P(n)
$$

with the zero and successor computations. Recursion is the constant-motive
special case; induction retains the dependence on the number being analyzed.
The power function in Chapter 8 is exactly such a Nat elimination, with a hom
carrier as its motive.

The equality classifiers of visible Unit, Bool, and Nat constructors also
have bounded observational computations. In particular, zero cannot equal a
visible successor, and equality of two visible successors reduces to equality
of their predecessors. These classifier computations do not erase a generic
reflexivity proof into the unique constructor of Unit, nor do they establish a
global normalization or canonicity theorem for every open Nat term.

<!-- evidence:TT-ELEMENTARY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-ELEMENTARY-INDUCTION` covers
> the decoded elementary classifiers and their dependent eliminators. The
> currently selected reusable Nat library additionally supplies addition,
> associativity, successor action, and sethood. A retired experimental binary
> coproduct is not part of this edition's active elementary API.

<a id="chapter-1-4"></a>

## 1.4 Identity And Path Induction

For `x,y:A`, the classifier `x=y` records identity paths.
Reflexivity gives

$$
\mathsf{refl}_x:x=x.
$$

The fundamental elimination rule says that a property of paths can be proved
by treating the reflexive path. In the right-based form used by emdash, fix
`y:A`, take a motive

$$
P:\prod_{x:A}(x=y)\longrightarrow\mathsf{Grpd},
$$

and provide `u:P(y,refl_y)`. Then every `p:x=y` receives an
element of `P(x,p)`, and the construction computes to `u` on
literal reflexivity.

Path symmetry, transitivity, and action follow from this eliminator:

$$
\begin{aligned}
p^{-1}&:y=x,\\
q\mathbin{\cdot}p&:x=z,\\
\mathsf{ap}_f(p)&:f(x)=f(y).
\end{aligned}
$$

For a dependent function `f:prod_(x:A) B(x)`, ordinary `ap` is
not well typed because its two outputs lie in different fibres. Dependent path
action instead gives a path over `p`, written

$$
\mathsf{apd}_f(p):f(x)=_{p}^{B}f(y).
$$

This is the first appearance of a recurring idea: motion in the base changes
the classifier in which the endpoint lives. In the equality-local fragment,
the motion is invertible and is handled by path induction. In a directed
family over a category, Chapter 2 will replace it with an explicit functor
between fibres.

<!-- evidence:TT-EQUALITY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-EQUALITY-INDUCTION` covers
> reflexivity, right-based dependent equality induction, `ap`, and
> `apd`. Emdash does not assume equality reflection: possessing a term
> `p:x=y` does not turn an arbitrary expression containing `x` into
> the same runtime term containing `y`.

<a id="chapter-1-5"></a>

## 1.5 Propositions As Classifiers

Under the broad propositions-as-types reading, to prove a statement is to
construct an inhabitant of its classifier. Conjunction is represented by a
pair, implication by a function, universal quantification by a dependent
function, and existential data by a dependent pair. Negation of `A` is
the function classifier

$$
\neg A:=A\longrightarrow\mathsf{Empty}.
$$

This reading is constructive: an inhabitant of an existential Sigma type
contains a witness, and an inhabitant of an implication is an operation on
evidence. It does not make every classifier proof-irrelevant. A Boolean, for
example, carries the information of which constructor was chosen. Chapter 3
will isolate the narrower classifiers whose inhabitants are all equal and
will call those *proposition-valued*.

No classical principle is needed for the WalkingEnd calculation. The negative
results there are constructive functions: an alleged equality or inverse is
sent to the empty classifier by inspecting its Nat code.

<a id="chapter-1-6"></a>

## 1.6 From Terms To Actions

The material so far is groupoidal. Identity paths are reversible, and an
ordinary function acts on them through `ap`. That is enough for
homotopy type theory's slogan that functions behave functorially on paths.
Functorial type theory retains this layer but adds a second one: a function
between object carriers is not automatically the whole meaning of a directed
functor. A directed functor must act on arrows, on arrows between arrows, and
so on.

The transition is therefore not from “types” to an unrelated category theory.
It is from implicit action generated by identity induction to explicit action
over possibly noninvertible arrows. The next chapter makes that action part of
the primary syntax.
<!-- /book-source:chapter-1 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-2 book/chapters/02-categories-functors-and-families.md -->
<a id="chapter-2"></a>

# 2. Categories, Functors, And Directed Families

An ordinary type family varies with a term and transports along equality. A
directed family varies with an object and acts along arrows that need not be
equalities. This small change reorganizes the entire dependent calculus. The
action is no longer reconstructed only from path induction: it is presented
as a functor and is therefore available at every cell dimension.

The central example already suggests the shape. `Code` is not merely an
assignment of a category to the base object of `W`. It must send the
generator to the successor functor. The based representable is not merely the
collection of hom carriers. It must act on an arrow by postcomposition. The
decoder is not merely a family of functions. It must compare these two
actions coherently.

For classical category-theoretic background, see
[Mac Lane](#ref-mac-lane). For broader context on directed type theory, see
[GPT 5.6 Codex](#ref-gpt-codex). The present calculus makes its own
computational and formal choices.

<a id="chapter-2-1"></a>

## 2.1 Categories With Iterated Homs

For a category `A`, write

$$
\operatorname{Obj}(A)
$$

for its classifier of objects. For `x,y:Obj(A)`, emdash does not take
`Hom_A(x,y)` to be only a set or a type of arrows. It is another
category. Its objects are 1-arrows `f:x -> y`; its arrows are 2-cells
between such arrows; iterating `Hom` reveals 3-cells and beyond.

Schematically,

$$
\begin{aligned}
f &: x\longrightarrow y,\\
\alpha &: f\Longrightarrow g,\\
\Gamma &: \alpha\Rrightarrow\beta,\\
&\ \vdots
\end{aligned}
$$

are read by repeatedly taking the object classifier of a hom-category. This
is the strict/lax omega-oriented *shape* of the implementation. It should not
be mistaken for a completed semantics of every weak omega-category: the
available composition, action, and coherence interfaces are explicit and
grow as consumers require them.

Every object has an identity arrow, and composable arrows have a composite

$$
x\xrightarrow{f}y\xrightarrow{g}z
\qquad\leadsto\qquad
g\circ f:x\longrightarrow z.
$$

We always read `g o f` as first `f`, then `g`. Identity,
composition, and their higher actions are global operations of the category
calculus. Some laws are selected as runtime reductions; others are exposed as
typed propositional or proof-time comparisons. The mathematical reading is
the familiar category law, while the implementation distinguishes which
direction is a useful normal form.

<!-- evidence:CAT-ITERATED-HOMS -->

> **Formal status — checked.** Evidence `CAT-ITERATED-HOMS` covers the
> category, object, and iterated-hom interface. The phrase “omega-oriented”
> describes this unbounded hom iteration; it does not claim a finished theory
> of arbitrary weak coherence.

<a id="chapter-2-2"></a>

## 2.2 The Equality-Local Category

Every groupoid classifier `A` determines a path category

$$
\mathsf{Path}(A).
$$

Its objects are elements of `A`, and its hom from `x` to `y` is
the path category of the identity classifier `x=y`. Its identity is
reflexivity and its composition is path concatenation. Since paths have
symmetry, this is the groupoidal fragment of the categorical universe.

An ordinary function `f:A -> B` lifts to an iterable functor

$$
\mathsf{Path}(f):\mathsf{Path}(A)\longrightarrow\mathsf{Path}(B).
$$

On objects it is `f`; on a path it is `ap_f`; on higher paths it
continues by the generic functor calculus. This is a precise bridge between
the type-theoretic material of Chapter 1 and the directed material here.

It is important that the bridge is an inclusion of a special case, not a
collapse. A directed category `C` may contain an arrow `x -> y`
without any path `x=y`. Conversely, an object path can be mapped to an
arrow through the equality-local core inclusion. Later equivalence interfaces
state when that inclusion captures all arrows.

<!-- evidence:CAT-PATH-CATEGORY -->

> **Formal status — checked.** Evidence `CAT-PATH-CATEGORY` covers the
> recursive path category and the functor induced by an ordinary function.
> No rule identifies a general directed hom-category with an equality type.

<a id="chapter-2-3"></a>

## 2.3 Functors Act At Every Dimension

A functor `F:A -> B` has an object action

$$
x\longmapsto F[x]
$$

and, for every pair `x,y`, a hom functor

$$
F_1[x,y]:\operatorname{Hom}_A(x,y)\longrightarrow
\operatorname{Hom}_B(F[x],F[y]).
$$

Evaluating the hom functor at an arrow `f` gives the familiar
`F[f]`. Because the result before evaluation is itself a functor, the
same construction already acts on 2-cells between `f` and `g`, then
on higher cells. The notation suppresses this projection ladder, but the
structure does not stop at the first arrow.

Functoriality has the expected equations

$$
F[\mathrm{id}_x]=\mathrm{id}_{F[x]},
\qquad
F[g\circ f]=F[g]\circ F[f].
$$

In the active calculus these are owned globally. A named construction that is
already a functor does not receive a private copy of the identity and
composition laws. This is more than code reuse: it expresses the foundational
thesis that substitution-like operations should be internalized until their
action and coherence come from the generic functor structure.

<!-- evidence:CAT-FUNCTOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-FUNCTOR-CALCULUS` covers
> object action, full hom action, capped arrow action, and the generic identity
> and composition surfaces.

<a id="chapter-2-4"></a>

## 2.4 Transfors And Naturality

Given functors `F,G:A -> B`, the next hom-category is written

$$
\mathsf{Transf}(F,G).
$$

An object `eta:F => G` has a component at every object,

$$
\eta[x]:F[x]\longrightarrow G[x].
$$

Its action over an arrow `f:x -> y` expresses naturality. In a
1-categorical shadow, this is the familiar square comparing

$$
G[f]\circ\eta[x]
\qquad\text{and}\qquad
\eta[y]\circ F[f].
$$

In the iterated-hom presentation, naturality is not an external proposition
attached after the components are chosen. It is part of the higher action of
the transfor object. Further homs between transfors provide higher transfors
and their components.

Vertical composition is computed componentwise, and identity transfors have
identity components. Whiskering and functor action provide horizontal
interaction. Chapter 8.2 uses precisely this infrastructure when the two
compositions on 2-endomorphisms meet in the Eckmann–Hilton calculation.

<!-- evidence:CAT-TRANSFOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-TRANSFOR-CALCULUS` covers
> transfors, their point components, and the next naturality projection. The
> book uses “transfor” for the dimension-uniform notion and “transformation”
> when discussing its ordinary categorical shadow.

<a id="chapter-2-5"></a>

## 2.5 The Directed Universe And Its Families

The category of categories has

$$
\operatorname{Obj}(\mathsf{Cat})=\mathsf{Cat},
\qquad
\operatorname{Hom}_{\mathsf{Cat}}(A,B)=\mathsf{Functor}(A,B).
$$

Thus an arrow in the categorical universe is a functor. A Cat-valued directed
family over `K` is consequently a functor

$$
E:K\longrightarrow\mathsf{Cat}.
$$

We write its fibre over `k` as `E[k]`. A base arrow
`p:k -> l` induces the reindexing functor

$$
E[p]:E[k]\longrightarrow E[l].
$$

This is covariant directed transport. It can carry an object `u:E[k]`
forward to `E[p](u)` even when `p` has no inverse. Ordinary path
transport is recovered when `K` is a path category, but directed
transport is strictly more general.

A morphism between families `E,D:K -> Cat` is a displayed or
fibrewise functor

$$
\Phi:E\Longrightarrow D.
$$

It has a functor `Phi[k]:E[k] -> D[k]` in each fibre. Over a base
arrow `p:k -> l`, its coherent comparison has the directed form

$$
D[p](\Phi[k](u))
\longrightarrow
\Phi[l](E[p](u)).
$$

The arrow points from “map, then transport in `D`” toward “transport in
`E`, then map.” It need not be an identity and need not be invertible.
This is the first elementary appearance of laxity in the dependent calculus.
Strict/cartesian constructions may make the comparison compute to an
identity, but that is additional structure or focused computation, not the
default meaning of a family morphism.

<!-- evidence:CAT-DIRECTED-FAMILIES -->

> **Formal status — checked.** Evidence `CAT-DIRECTED-FAMILIES` covers
> Cat-valued families, fibres, arrow reindexing, fibre functors, and the
> canonical displayed comparison cell. A general directed family is not
> required to send its base arrows to equivalences.

<a id="chapter-2-6"></a>

## 2.6 Totals And Sections

A family can be read in two complementary ways. Its **total category** gathers
all fibre objects together:

$$
\sum_{k:K}E[k].
$$

An object is a pair `(k,u)` with `u:E[k]`. An arrow

$$
(k,u)\longrightarrow(l,v)
$$

contains a base arrow `p:k -> l` and a fibre arrow

$$
\alpha:E[p](u)\longrightarrow v
$$

in `E[l]`. The canonical transport arrow is the special case

$$
(p,\mathrm{id}_{E[p](u)}):
(k,u)\longrightarrow(l,E[p](u)).
$$

This description makes directed dependence concrete. Transport is an actual
arrow in the total category, and its direction is inherited from the base.

The **section category** is the dependent product

$$
\prod_{k:K}E[k].
$$

A section `s` assigns an object `s[k]:E[k]` and, for every base
arrow, a coherent comparison

$$
s[p]:E[p](s[k])\longrightarrow s[l].
$$

An arrow between sections is not an arbitrary pointwise family of fibre
arrows. Its components must be natural over the base. This distinction
disappears over a trivial base but is essential over a directed one.

For a constant family with fibre `A`, the total is the product category
`K x A`, while the section category is the functor category
`Functor(K,A)`. These are useful checks on the definitions: a section of
a constant family is precisely a functorial choice varying over `K`.

<!-- evidence:CAT-SIGMA-PI -->

> **Formal status — checked.** Evidence `CAT-SIGMA-PI` covers the Sigma
> total, its canonical transport arrow, the Pi section facade, and section
> evaluation. Some broader Sigma/Pi adjunctions and generic section-total
> packaging remain future work; they are not prerequisites for Chapter 8.

### 2.6.1 Fibrewise Contexts

Totals make genuine dependence visible, but not every pair of declarations
over a base depends on one another. Let
$B,C:K\vdash\mathsf{Cat}$ be two families over the same category. Their
fibrewise product is the transparent family

$$
P(B,C)[k]:=B[k]\times C[k],
\qquad
P(B,C)[p]:=B[p]\times C[p].
$$

The second formula uses the same base arrow $p$ in both components. It is the
action required by a context of independent siblings

$$
k:K,\qquad b:B[k],\qquad c:C[k].
$$

This differs from a genuinely dependent context

$$
k:K,\qquad a:A[k],\qquad b:B[k,a].
$$

In the first context, $b$ and $c$ may be projected, paired, exchanged, or
contracted while the common prefix $k$ is fixed. In the second, exchanging
$a$ and $b$ without transporting the classifier of $b$ is generally
ill-typed.

The fixed-base structural maps are

$$
\begin{aligned}
\mathsf{projL}_d(B,C)&:P(B,C)\Longrightarrow B,\\
\mathsf{projR}_d(B,C)&:P(B,C)\Longrightarrow C,\\
\mathsf{pair}_d(\Phi,\Psi)&:E\Longrightarrow P(B,C),
\end{aligned}
$$

where $\Phi:E\Longrightarrow B$ and $\Psi:E\Longrightarrow C$. They satisfy
the displayed product cuts

$$
\mathsf{projL}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Phi,
\qquad
\mathsf{projR}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Psi.
$$

Their fibre functors, base-arrow actions, and selected internalized higher
cells compute componentwise. Exchange and contraction are consequently
derived maps:

$$
\begin{aligned}
\mathsf{swap}_d(B,C)
  &:=\mathsf{pair}_d(\mathsf{projR}_d,\mathsf{projL}_d),\\
\mathsf{diag}_d(B)
  &:=\mathsf{pair}_d(\mathsf{id}_d,\mathsf{id}_d).
\end{aligned}
$$

The family $P(B,C)$ is built from ordinary categorical product functoriality;
it is not a new primitive family former. Reindexing a grouped context is
presented canonically by reindexing its two families and rebuilding their
fibrewise product.

<!-- evidence:CAT-FIBREWISE-CONTEXT -->

> **Formal status — checked.** Evidence `CAT-FIBREWISE-CONTEXT` covers the
> transparent fibrewise family, its displayed projections and pairing,
> componentwise object, arrow, and selected higher action, the two product
> cuts, and the derived swap and diagonal. It does not license exchange
> across a genuine dependency edge.

### 2.6.2 Base Change And Evaluation

A functor $F:A\vdash K$ can change the base of a family
$D:K\vdash\mathsf{Cat}$. The pulled-back family $F^*D$ has fibre
$(F^*D)[a]=D[F[a]]$. Its total category carries a canonical functor

$$
\mathsf{Tot}(F,D):
\sum_{a:A}(F^*D)[a]\longrightarrow\sum_{k:K}D[k]
$$

with computations

$$
(a,u)\longmapsto(F[a],u),
\qquad
(p,\alpha)\longmapsto(F[p],\alpha).
$$

The base component is acted on by $F$, while the fibre component is retained.
This is the asymmetric Grothendieck totalization of family reindexing. It is
not a claim that arbitrary functors between total categories admit a
computational pullback.

The same fibrewise structure supports coherent evaluation. Fix an ordinary
category $A$ and a family $B:K\vdash\mathsf{Cat}$, and write

$$
S(A,B)[k]:=\operatorname{Functor}(A,B[k]).
$$

Then

$$
\mathsf{Eval}_d(B):
P\bigl(S(A,B),\mathsf{Const}_K(A)\bigr)\Longrightarrow B
$$

projects in each fibre to ordinary functor evaluation:

$$
\mathsf{Eval}_d(B)[k]=\mathsf{Eval}(A,B[k]).
$$

Weakening is supplied by the displayed terminal map

$$
\mathsf{Terminal}_d(E):
E\Longrightarrow\mathsf{Const}_K(1).
$$

Composing it with a constant section yields a fixed argument. Pairing that
argument with a varying functor and applying $\mathsf{Eval}_d$ therefore
interprets application without asking the user to supply a separate
naturality square. Base-arrow and higher action are inherited from the
internal functorial calculus.

<!-- evidence:CAT-BASE-CHANGE-TOTALIZATION -->
<!-- evidence:CAT-DISPLAYED-EVALUATION -->

> **Formal status — checked.** Evidence
> `CAT-BASE-CHANGE-TOTALIZATION` covers the object and arrow action of
> asymmetric pullback totalization. Evidence `CAT-DISPLAYED-EVALUATION`
> covers constant-domain displayed evaluation, terminal weakening, and their
> retained generic base and higher action. Arbitrary mixed-domain evaluation
> remains outside this result.

<a id="chapter-2-7"></a>

## 2.7 Representables And Variance

Fix `x:K`. The covariant fixed-source representable family is

$$
\mathsf{Rep}_x[k]:=\operatorname{Hom}_K(x,k).
$$

For `p:k -> l`, it acts by postcomposition:

$$
\mathsf{Rep}_x[p](q)=p\circ q.
$$

This is exactly the action used in the WalkingEnd decoder: a based arrow
`q:* -> k` is carried along `p` to `p o q:* -> l`.

The source variable is contravariant. Given `r:x -> y`,
precomposition defines a family morphism

$$
\mathsf{Rep}_y\Longrightarrow\mathsf{Rep}_x,
\qquad
q\longmapsto q\circ r.
$$

Keeping these two variances distinct is not pedantry. Postcomposition changes
the target of an arrow; precomposition changes its source. Emdash gives them
separate runtime owners and compares alternate presentations only where the
types justify it.

<!-- evidence:CAT-REPRESENTABLE -->

> **Formal status — checked.** Evidence `CAT-REPRESENTABLE` covers the
> fixed-source representable and its contravariant source action. Generic
> functoriality owns its action in the varying target.

<a id="chapter-2-8"></a>

## 2.8 The Interfaces Needed By The Main Proof

The Chapter 8 calculation uses only a compact part of this chapter:

1. `Code:W -> Cat` is a directed family, so every based arrow
   `p:* -> x` acts by a functor `Code[p]`.
2. The target family is the representable `Rep_*`, whose base-arrow
   action is postcomposition.
3. Natural powers form a functor from `Path(Nat)` to the based
   hom-category, not merely a function on objects.
4. A contextual decoder is a family morphism from `Code` to
   `Rep_*`; its base-arrow comparison produces the normalization cell.
5. The ordinary and higher functor laws supply identity, composite, and cell
   action without WalkingEnd-specific copies.

The proof therefore depends on category theory at exactly the point where a
carrier-only argument would lose direction. The next chapters add the logical,
equivalence, induction, and height interfaces needed to turn that directed
construction into a numerical classification.
<!-- /book-source:chapter-2 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-3 book/chapters/03-logic-propositions-and-sets.md -->
<a id="chapter-3"></a>

# 3. Logic, Propositions, And Sets

The propositions-as-types reading begins with a useful ambiguity. Any
classifier may be read as a proposition: to prove it is to construct an
inhabitant. But not every classifier behaves like a truth value. An inhabitant
of Bool tells us which Boolean was chosen; a natural number contains still
more data. Logic becomes precise only after we distinguish *having evidence*
from *having no relevant choice of evidence*.

This distinction is particularly important in a directed foundation. A
classifier may carry higher identity information even when the surrounding
category also carries noninvertible arrows. Proposition and set evidence
control the groupoidal identity layer; they do not erase directed structure.

<a id="chapter-3-1"></a>

## 3.1 Propositions As Types, Broadly Read

The basic logical readings are constructive:

$$
\begin{array}{c|c}
\text{statement} & \text{classifier}\\ \hline
P\text{ and }Q & P\times Q\\
P\text{ implies }Q & P\longrightarrow Q\\
\text{for every }x:A,\ P(x) & \prod_{x:A}P(x)\\
\text{there is }x:A\text{ with }P(x) & \sum_{x:A}P(x)\\
\text{falsehood} & \mathsf{Empty}.
\end{array}
$$

Under this reading, a proof of an existential statement contains a witness and
its evidence. A proof of an implication is an operation that transforms
evidence. Negation is

$$
\neg P:=P\longrightarrow\mathsf{Empty}.
$$

This is enough to state the negative theorems of Chapter 8. To prove that the
walking loop is not the identity, for instance, one assumes an equality and
constructs an inhabitant of Empty by mapping it to an impossible Nat equality.

What this reading does not supply is automatic proof irrelevance. If `P`
has two inhabitants, the bare fact that both prove a statement says nothing
yet about whether they are equal. That is a separate property of `P`.

<a id="chapter-3-2"></a>

## 3.2 Contractibility And Proposition-Valuedness

A classifier `A` is **contractible** when it has a chosen centre and a
path from that centre to every point:

$$
\mathsf{isContr}(A)
:=\sum_{a_0:A}\prod_{a:A}(a_0=a).
$$

Contractibility contains both existence and uniqueness, with uniqueness
understood homotopically. The centre is data, but the total classifier of
contractibility evidence is itself proposition-valued: any two such packages
are equal.

A classifier is **proposition-valued** when its identity classifiers are
contractible. In the familiar shorthand, any two of its inhabitants are
equal, and there is no further choice among the paths witnessing that fact.
It may be inhabited, like Unit, or uninhabited, like Empty. If it is inhabited,
it is contractible.

The adjective “proposition-valued” is deliberate. We still use every
classifier as a proposition in the broad Curry–Howard reading. The additional
property says that inhabitation carries no mathematical information beyond
truth.

<!-- evidence:LOGIC-TRUNCATION-PREDICATE -->

> **Formal status — checked.** Evidence `LOGIC-TRUNCATION-PREDICATE`
> covers `IsContr` and the recursive truncation predicate whose
> `-1` and `0` specializations are proposition- and set-valuedness.

<a id="chapter-3-3"></a>

## 3.3 Sets As A Homotopical Property

A classifier `A` is **set-valued** when every identity classifier
`x=y` is proposition-valued. Equivalently, any two parallel paths in
`A` are equal. This is the type-theoretic notion of a set: it concerns
the height of identity information, not membership in a global cumulative
set universe.

The hierarchy begins

$$
\begin{array}{ccl}
-2 &:& \text{contractible classifiers},\\
-1 &:& \text{proposition-valued classifiers},\\
0 &:& \text{set-valued classifiers},\\
1 &:& \text{groupoid-valued classifiers},\\
&\vdots&
\end{array}
$$

and each successor level asks that every identity classifier lie one level
lower. Chapter 7 develops this recursion uniformly. For now, sethood provides
the exact uniqueness principle needed for arithmetic codes.

Unit is proposition-valued because it is contractible. Empty is
proposition-valued by elimination: from an alleged first inhabitant one may
derive the required path data. Nat is set-valued by nested induction on its
visible constructors. Equality of zero with a successor reduces to Empty;
equality of two successors reduces to predecessor equality; the remaining
cases reduce to the proposition evidence for Unit or Empty.

<!-- evidence:LOGIC-NAT-SETHOOD -->

> **Formal status — checked.** Evidence `LOGIC-NAT-SETHOOD` supplies
> explicit terms witnessing that Unit and Empty are proposition-valued and
> Nat is set-valued. Nat sethood is not inferred merely from a rewrite table;
> it is an inhabitant of the internal `IsSetGrpd(Nat)` classifier.

<a id="chapter-3-4"></a>

## 3.4 Evidence Is Not Erasure

It is tempting to read “being a property” as permission for the kernel to
erase every proof to one constant. That is not the policy here. Emdash retains
evidence terms and proves that the classifier containing them is
proposition-valued.

For every level `n` and classifier `A`, the classifier

$$
\mathsf{isTrunc}_n(A)
$$

of evidence that `A` lies at level `n` is proposition-valued. Hence two
truncation witnesses are equal, but their constructors and projections remain
available to computation. This matters for packaged universes: a package can
retain both a carrier and its truncation evidence while still having equality
controlled by the carrier.

The same style recurs for equality-valued equivalence evidence. Rather than
declaring inverse-law proofs irrelevant by fiat, the theory proves that their
classifier is a proposition. Retained evidence supports computation and
transport; proposition-valuedness supports uniqueness and truncation.

<!-- evidence:LOGIC-TRUNCATION-EVIDENCE-PROP -->

> **Formal status — checked.** Evidence
> `LOGIC-TRUNCATION-EVIDENCE-PROP` establishes property-valuedness at
> every recursive truncation level. It introduces no proof-erasure rewrite.

<a id="chapter-3-5"></a>

## 3.5 Constructive Reasoning

The foundational rules used in this book are constructive. To prove
`P or Q` one must select a side in whatever sum-like interface is in
scope; to prove an existential one must provide a witness; to refute a claim
one must map its evidence to Empty. The law of excluded middle and double
negation elimination are not silently used as global inference rules.

This does not forbid classical mathematics. A classical principle can be
studied as additional structure, restricted to a suitable proposition-valued
universe, or derived in a context where decidability data are available. The
point is bookkeeping: a proof should reveal when such data enter.

The WalkingEnd theorem needs none. Its code is computed by functor action, its
inverse laws by contextual elimination and Nat induction, and its
noninvertibility by successor/zero discrimination. The argument is therefore
valid in the constructive core presented here.

> **Formal status — mathematical development.** This section states the
> logical discipline of the book. It does not claim a complete internal
> library of all connectives, propositional truncations, choice principles, or
> classical axioms.

<a id="chapter-3-6"></a>

## 3.6 Two Uses Of Sethood In The Main Calculation

Sethood enters Chapter 8 in two distinct ways.

First, Nat sethood controls equality in the code fibre `Path(Nat)`.
It ensures that higher coherence between arithmetic equalities is unique at
the needed level. This lets the power construction lift equality of naturals
without introducing uncontrolled higher data.

Second, the based hom carrier is proved set-valued after the calculation. One
proof comes directly from the one-dimensional signature of `W`; another
transports Nat sethood backward across the carrier equivalence. Agreement of
the conclusions does not collapse the proofs: each exposes a different reason
for sethood.

This is typical of univalent foundations. A property may be reached through
dimension, through equivalence, or through a direct induction. Since the
classifier of evidence is proposition-valued, the resulting witnesses agree,
yet their constructions remain mathematically informative.
<!-- /book-source:chapter-3 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-4 book/chapters/04-equivalence-and-univalence.md -->
<a id="chapter-4"></a>

# 4. Equivalence And Univalence

Univalence is often summarized by the phrase “equivalent things may be
identified.” In a directed setting, that sentence must be typed with care.
Equivalent *classifiers*, isomorphic objects of a 1-category, recursively
invertible arrows, and arbitrary functors are different notions. The theory
becomes clearer, not more cumbersome, when each receives its own interface.

The WalkingEnd example is the test. Its generator is a perfectly good arrow,
and `Code` sends it to a perfectly good functor, but neither is an
equivalence. At the same time, the final comparison between its endomorphism
carrier and Nat is a type equivalence. Univalent foundations must support both
statements without forcing one into the shape of the other.

<a id="chapter-4-1"></a>

## 4.1 Maps With Contractible Fibres

For a function `f:A -> B` and `b:B`, its homotopy fibre is

$$
\mathsf{fib}_f(b)
:=\sum_{a:A}(f(a)=b).
$$

The function is an equivalence when every such fibre is contractible. A
`TypeEquiv(A,B)` packages `f` with this evidence. The centre of the
fibre over `b` selects an inverse value `f^{-1}(b)`, and its path
component gives

$$
f(f^{-1}(b))=b.
$$

Contractibility of the fibre also yields the other law

$$
f^{-1}(f(a))=a.
$$

This definition has two advantages. It treats being an equivalence as a
property of a fixed map, and it supplies a canonical selected inverse from the
contractible-fibre evidence. Conversely, explicit inverse data with both
homotopies can be adjusted and converted into contractible-fibre evidence.
That is the route used by the WalkingEnd carrier comparison: `encode` and
`power` are built first, their two round trips are proved, and then the
equivalence package is formed.

<!-- evidence:EQUIV-TYPE -->

> **Formal status — checked.** Evidence `EQUIV-TYPE` covers homotopy
> fibres, the equivalence-map predicate, `TypeEquiv`, its selected
> inverse, and both inverse paths.

<a id="chapter-4-2"></a>

## 4.2 Algebra Of Type Equivalences

Equivalences have reflexivity, symmetry, and composition:

$$
\begin{aligned}
\mathsf{id}_A &: A\simeq A,\\
e^{-1} &: B\simeq A,\\
e_{BC}\circ e_{AB} &: A\simeq C.
\end{aligned}
$$

Composition is written in categorical order; the forward map of the last
line sends `a` first through `e_AB` and then through `e_BC`.
The inverse laws are constructed from explicit quasi-inverse data and the
path algebra of Chapter 1.

Not every mathematically true equation between equivalence packages is chosen
as a runtime eta rule. What computes is the public interface needed by
consumers: the selected forward map of reflexivity, symmetry, and composition,
together with designated projections of inverse data. Remaining coherence is
propositional. This is the same separation between computation and evidence
that we saw for Nat associativity.

<!-- evidence:EQUIV-TYPE-ALGEBRA -->

> **Formal status — checked.** Evidence `EQUIV-TYPE-ALGEBRA` covers
> reflexivity, symmetry, composition, and their selected forward-map
> computation.

<a id="chapter-4-3"></a>

## 4.3 Univalence In The Groupoid Universe

Every universe path `p:A=B` induces a type equivalence by transporting
elements:

$$
\mathsf{idtoequiv}(p):A\simeq B.
$$

Univalence supplies the converse in a coherent way. In the groupoid universe,
emdash has an operational decoder

$$
\mathsf{ua}(e):A=B
$$

and named round trips

$$
\mathsf{ua}(\mathsf{idtoequiv}(p))=p,
\qquad
\mathsf{idtoequiv}(\mathsf{ua}(e))=e.
$$

Transport along the decoded path agrees propositionally with the forward map
of `e`. The qualification “propositionally” is important. A single
operational decoder owns the comparison; the kernel does not turn every
universe transport expression into arbitrary equivalence application by a
broad rewrite.

This gives the groupoid/type layer its univalent reading: identity in the
universe and equivalence of decoded classifiers carry the same information
through the named interface. It does not say that a noninvertible arrow in an
arbitrary category is an identity.

<!-- evidence:UNIV-GROUPOID -->

> **Formal status — checked.** Evidence `UNIV-GROUPOID` covers the
> decoder-oriented groupoid-univalence equivalence, both round trips, and the
> selected transport agreement.

<a id="chapter-4-4"></a>

## 4.4 Universes With Retained Truncation Evidence

For each truncation level `n`, the theory also packages a classifier
together with evidence that it is `n`-truncated:

$$
\mathsf{TruncU}_n
:=\sum_{A:\mathsf{Grpd}}\mathsf{isTrunc}_n(A).
$$

The evidence is retained, not erased. Nevertheless, because truncation
evidence is proposition-valued, equality of packages is controlled by
equality of their carriers. Combining that fact with groupoid univalence gives
the restricted comparison

$$
(A,h_A)=(B,h_B)
\simeq
A\simeq B.
$$

The familiar universes of propositions, sets, and groupoids are the `-1`,
`0`, and `1` cases of this package. This is a concrete example of
structure identity: once a field is proposition-valued, identifying the
carrier supplies the dependent identification of that field.

<!-- evidence:UNIV-TRUNCATED -->

> **Formal status — checked.** Evidence `UNIV-TRUNCATED` covers the
> carrier-equivalence view of paths between packaged truncated classifiers and
> its named encode/decode laws. It is a restricted univalence theorem, not a
> truncation reflector.

<a id="chapter-4-5"></a>

## 4.5 Three Categorical Notions Of Invertibility

At the categorical layer we distinguish three interfaces.

An ordinary isomorphism between objects `x,y:C` consists of a forward
arrow, one inverse arrow, and equality-valued left and right inverse laws:

$$
f:x\to y,\qquad
g:y\to x,\qquad
g\circ f=\mathrm{id}_x,\qquad
f\circ g=\mathrm{id}_y.
$$

For a fixed arrow `f`, the native classifier
`OmegaEquivAlong(f)` carries recursively equality-valued inverse
evidence. Its selected left and right inverse arrows may be presented
separately, with their laws living in the next hom-categories. Finally,
`OmegaEquiv(C,x,y)` packages a chosen forward arrow together with such
evidence.

The distinction allows the interface to remain iterable. Inverse laws at one
dimension are equality data in a hom-category, where the same machinery can
act again. An ordinary isomorphism has a checked one-way lift into the native
omega-equivalence package, but the notions are not collapsed definitionally.

<!-- evidence:EQUIV-OMEGA -->
<!-- evidence:EQUIV-ORDINARY-ISO-LIFT -->

> **Formal status — checked.** Evidence `EQUIV-OMEGA` covers the
> fixed-arrow and packaged equality-valued interfaces and the transparent
> package built from an object path. Evidence
> `EQUIV-ORDINARY-ISO-LIFT` covers the one-way lift from ordinary
> isomorphism evidence.

For an object path `p:x=y`, path induction constructs a forward arrow,
an inverse, and both cancellation laws. Thus equality can be *reified* as a
computational equivalence package. A bare classifier-level cast may permit an
identity term to be used at the stable equivalence facade, but it does not
magically give that term the projections of a package; observable computation
uses the explicit construction.

The converse direction has a more delicate status. The current native surface
supports selected equality/equivalence casts and rigid universe boundaries,
but a full general equivalence between arbitrary object equality and ordinary
1-categorical isomorphism evidence is not a compatibility prerequisite and is
not claimed here.

<!-- evidence:UNIV-FULL-OBJECT-ISO -->

> **Formal status — research boundary.** Evidence
> `UNIV-FULL-OBJECT-ISO` records the intentionally absent two-sided
> ordinary-isomorphism/object-equality theorem. Its absence does not weaken the
> checked path-to-equivalence construction used elsewhere in the book.

<a id="chapter-4-6"></a>

## 4.6 Equivalence Evidence Is A Property

For a fixed arrow `f`, two complete choices of equality-valued inverse
evidence are equal. The proof does not erase the choices. It shows that the
left- and right-inverse fibres are contractible, using ordinary associativity,
unit laws, and the supplied inverse equations, and then transfers that
contractibility to the native record.

Consequently,

$$
\mathsf{OmegaEquivAlong}(f)
$$

is proposition-valued for every category and fixed arrow, without assuming
that the category has finite height or locally set-valued homs. This is the
categorical analogue of the fact that “is an equivalence” should be a property
of a map even though an explicit quasi-inverse package may contain choices.

<!-- evidence:EQUIV-EVIDENCE-PROP -->

> **Formal status — checked.** Evidence `EQUIV-EVIDENCE-PROP` is the
> dimension-independent property theorem for the native fixed-arrow evidence.

<a id="chapter-4-7"></a>

## 4.7 Hom Action And Groupoidal Sources

Equivalence evidence must itself act functorially if the foundation is to be
usable at higher dimension. The one-way derived hom-action layer sends
fixed-arrow omega-equivalence evidence through the next hom action of an
ordinary functor. In particular, if a category is coherently groupoidal, its
core inclusion is an omega-equivalence and each directed arrow can be related
to an object path through the selected homwise inverse.

For a directed family `D:C -> Cat`, coherent groupoidality of `C`
then implies that transport along a base arrow is an equivalence:

$$
D[f]:D[x]\simeq D[y].
$$

This recovers the familiar groupoidal behavior of path-indexed families as a
special case. It also states the boundary sharply: without groupoidality,
`D[f]` remains only a functor.

<!-- evidence:EQUIV-HOM-ACTION -->

> **Formal status — checked.** Evidence `EQUIV-HOM-ACTION` covers the
> one-way next-hom action and its specialization to equivalence of fibre
> transport over a coherently groupoidal source.

<a id="chapter-4-8"></a>

## 4.8 Why Successor Needs No Univalence In Chapter 8

The circle's universal cover sends an invertible loop to successor on the
integers. To define it as a universe-valued family, one first recognizes
successor as an equivalence and then uses univalence to obtain a universe
path.

The WalkingEnd code has a different type:

$$
\mathsf{Code}:W\longrightarrow\mathsf{Cat}.
$$

Its generator is a directed arrow in `W`, so its image need only be a
functor. Natural-number successor qualifies directly even though it misses
zero and has no inverse. Forcing univalence into this step would change the
mathematics by demanding reversibility where the signature deliberately has
none.

The carrier equivalence at the end of the proof is nevertheless genuinely a
type equivalence, and the surrounding universes retain their checked
univalence interfaces. The lesson is not that univalence disappears. It is
that univalence governs equivalence and identity, while directed functoriality
also governs noninvertible action.
<!-- /book-source:chapter-4 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-5 book/chapters/05-induction-and-universal-properties.md -->
<a id="chapter-5"></a>

# 5. Induction, Arrow Induction, And Universal Properties

Induction is often introduced as a collection of unrelated proof rules: one
for natural numbers, another for equality, and still others for higher
inductive types. A more durable view is that an inductively presented object
comes with a way to extend compatible data from its generators. Recursion
extends nondependent data; induction extends data in a family; contextual
elimination lets both the source and target vary. The increasing amount of
context is not bureaucratic overhead. It is what records naturality.

In a functorial setting, this extension principle should itself preserve
arrows and higher cells. That demand turns a familiar logical rule into a
categorical construction. This chapter begins with ordinary induction, then
develops the outgoing-arrow category and the arrow-induction interface used
throughout emdash. The result is a bridge between equality induction and the
contextual eliminator of the walking endomorphism.

## 5.1 Data On Generators

For the natural numbers, dependent induction has the familiar shape. Given a
family `P(n)`, a base element

$$
z:P(0),
$$

and a step operation

$$
s_n:P(n)\longrightarrow P(n+1),
$$

there is a section

$$
\mathsf{ind}_{\mathbb N}(z,s):\prod_{n:\mathbb N}P(n)
$$

whose observations at zero and successor compute to the supplied data. If
`P` is constant, the same interface is recursion. Thus recursion is not a
second principle: it is dependent elimination with no meaningful dependency.

The same pattern appears for a category presented by an object and an
endomorphism. To map it into a category `C`, one supplies an object of
`C` and an endomorphism of that object. To define a dependent section,
one supplies an object in the fibre over the generating object and a lift over
the generating arrow. To compare two varying families, one supplies a functor
between their base fibres and a coherent cell over the generator. Chapters 6
and 8 will instantiate precisely these three levels.

This perspective separates two questions:

1. what data an eliminator accepts; and
2. how its observations compute at the constructors.

Both matter. Existence without computation cannot drive a normalization
proof; computation without a coherent extension does not define an action on
the whole object.

In the rule schema of
[Appendix G.4](#appendix-formal-presentation-g4), generator data are the
introduction clauses, the induced section or functor is elimination, and the
constructor observations are computation. Uniqueness or initiality is a
separate universal clause, while coherent action on arrows and higher cells is
the specifically functorial clause. We will report all five independently
rather than treating the word “induction” as evidence for whichever clauses
have not yet been supplied.

## 5.2 Equality Induction As The Local Case

For a type `A`, right-based equality induction says that, with the right
endpoint `y` fixed, a family

$$
C(x,p)\qquad(x:A,\;p:x=y)
$$

is determined by its value at `(y,refl_y)`. In one conventional
orientation,

$$
\frac{d:C(y,\mathsf{refl}_y)}
     {\mathsf J(d,x,p):C(x,p)}.
$$

The reflexive observation computes to `d`. Ordinary action on paths and
dependent action on paths are specializations of this principle. They explain
why a function respects equality and how a section over a family produces a
dependent path.

<!-- evidence:TT-EQUALITY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-EQUALITY-INDUCTION`. The
> equality-local layer provides reflexivity, right-based dependent induction,
> ordinary path action, and dependent path action.

Equality induction is already functorial when it is read inside the path
category `Path(A)`: objects are elements of `A`, arrows are
equalities, and every arrow is invertible. But this is a special, groupoidal
base. A directed category contains arrows that need not have inverses, so we
want an induction interface whose statement does not presuppose that a given
arrow is an equality.

## 5.3 The Category Of Outgoing Arrows

Fix a category `Z` and an object `x`. The category of arrows leaving
`x` is the total category of the represented family

$$
\mathsf{PathOut}_Z(x)
  :=\sum_{y:\,Z}\operatorname{Hom}_Z(x,y).
$$

Its objects are pairs `(y,p)` with $p:x\to y$. It has a
distinguished reflexive object

$$
\mathsf{reflout}_x:=(x,\mathrm{id}_x).
$$

For every outgoing arrow $p:x\to y$, functorial action of the
representable family supplies a canonical total arrow

$$
\rho_{x,y,p}:
(x,\mathrm{id}_x)\longrightarrow(y,p)
\quad\text{in }\mathsf{PathOut}_Z(x).
$$

Its base component is `p`; its fibre endpoint reduces by the unit law
$p\circ\mathrm{id}_x=p$. The direction of `rho` is significant. It
starts at the reflexive arrow and reaches `p`. Nothing in the
construction produces a reverse arrow, and no invertibility premise is used.

<!-- evidence:IND-PATHOUT -->

> **Formal status — checked.** Evidence `IND-PATHOUT`.
> `PathOut_cat` is the Sigma total of the fixed-source
> representable, `pathout_refl_obj` is its distinguished object, and
> `pathout_refl_arrow` is the canonical Sigma transport arrow
> `rho`.

The name “PathOut” emphasizes an analogy, not an identification. When
`Z=Path(A)`, its objects really are equality paths out of `x`.
For a general `Z`, they are directed arrows. The same categorical shape
therefore hosts both ordinary path induction and a genuinely directed
extension principle.

The source object also varies contravariantly. An arrow $r:x\to y$
induces a functor

$$
\mathsf{PathOut}_Z(y)\longrightarrow\mathsf{PathOut}_Z(x),
\qquad
(z,q)\longmapsto(z,q\circ r).
$$

Precomposition changes which object the arrows leave, while postcomposition
changes where they arrive. Keeping these variances separate will prevent a
common mistake in Chapter 8: the based representable there varies
covariantly in its endpoint, not contravariantly in its source.

## 5.4 Fixed-Source Arrow Induction

Let

$$
E:\mathsf{PathOut}_Z(x)\longrightarrow\mathsf{Cat}
$$

be a directed family. An element

$$
u\in E[\mathsf{reflout}_x]
$$

can be transported along every canonical arrow `rho`. This produces a
section

$$
\mathsf{path\_ind}(x,E,u):
\prod_{q:\,\mathsf{PathOut}_Z(x)}E[q],
$$

whose readable value is

$$
\mathsf{path\_ind}(x,E,u)(y,p)
  = E[\rho_{x,y,p}](u).
$$

This formula is arrow induction: data at the identity arrow extends along
every outgoing arrow. Because `E` is Cat-valued, the result is a section
with coherent action, rather than merely a function that chooses one object
in each fibre.

<!-- evidence:IND-ARROW -->

> **Formal status — checked.** Evidence `IND-ARROW`. The fixed-source
> section is `path_ind_sec`; `PathInd_func` packages its action in the
> motive and base datum, and `PathInd_transfd` internalizes the theorem
> while the source object varies.

There are three layers here, and it helps not to conflate them:

- `path_ind_sec` is the readable theorem at a fixed source;
- `PathInd_func` says that this theorem acts functorially on motives and
  their data;
- `PathInd_transfd` records coherence as the source object moves.

The third layer uses the contravariant source action of `PathOut` and
the corresponding pullback of motives. Its naturality is internal to the
displayed transformation. One need not append an external family of
hand-written commuting squares.

## 5.5 Composition As A Diagnostic

An abstract eliminator earns its keep by recovering an operation we already
understand. Fix `x` and give `(y,p)` the represented motive

$$
E(y,p):=
\bigl(\operatorname{Rep}_Z(y)\longrightarrow
      \operatorname{Rep}_Z(x)\bigr).
$$

At the reflexive arrow, the identity transformation supplies the base datum.
Arrow induction then extends it to every $p:x\to y$. Evaluating the
result at $q:y\to z$ gives

$$
q\circ p:x\longrightarrow z.
$$

Thus ordinary categorical composition appears as transport from the identity
case. The resulting operation is still packaged functorially, so its action on
higher cells remains available to later constructions.

<!-- evidence:IND-COMPOSITION -->

> **Formal status — checked.** Evidence `IND-COMPOSITION`.
> `CompMotive_catd` is the represented motive,
> `path_comp_sec` is the induced section, and
> `path_comp_func` exposes composition as the object action of a
> functor.

This benchmark is more informative than a proof that some carrier-level
function exists. It checks the direction of `rho`, the variance of the
representable, and the agreement of the generic Sigma and Pi constructions.
If any of those are reversed, the result has the wrong endpoints before one
even asks for associativity.

## 5.6 Returning To Literal Equality

Set `Z=Path(A)` and let `D` be a directed family over that path
category. There are now two ways to move `u` along an equality
`p:x=y`:

1. use the functorial action of `D` on the arrow `p`; or
2. use primitive equality induction with a function-valued motive.

They need not be definitionally the same expression. The active calculus
proves that they are propositionally equal:

$$
\mathsf{transport}^{\mathrm{structured}}_D(p,u)
=
\mathsf{transport}^{\mathsf J}_D(p,u).
$$

<!-- evidence:IND-PATH-COMPARISON -->

> **Formal status — checked.** Evidence `IND-PATH-COMPARISON`.
> `path_cat_structured_transport_agrees_ind_eqr` compares the existing
> directed-family action with primitive right-based equality induction. It
> does not introduce a second equality eliminator or turn the comparison into
> a global rewrite.

This is the precise relation between the equality-local and directed views.
Functorial transport extends beyond equality paths; on a literal path
category, it agrees with `J` by a theorem. The groupoidal case is
therefore recovered without making all directed arrows groupoidal.

## 5.7 Contextual Elimination

Fixed-source arrow induction varies a motive over outgoing arrows. A
contextual eliminator goes one step further: it compares two families over an
inductively presented base. Schematically, suppose
$R,D:K\to\mathsf{Cat}$.
At each base object it should provide a functor

$$
T_k:R[k]\longrightarrow D[k],
$$

and for each base arrow $f:k\to k'$ a directed comparison

$$
D[f]\circ T_k
\Longrightarrow
T_{k'}\circ R[f].
$$

This is exactly the data of a displayed functor in the lax direction selected
by the calculus. If `R` is terminal, a displayed functor becomes a
section of `D`. If both `R` and `D` are constant, it becomes an
ordinary functor out of `K`. Section induction and recursion are therefore
special cases of contextual elimination.

For an inductively presented `K`, the desired eliminator should build the
whole displayed functor from compatible data at the constructors. The
WalkingEnd interface of Chapter 6 realizes this pattern for one point and one
directed loop. Chapter 8 then uses the genuinely contextual form: its source
is the code family and its target is a representable family, so neither side
can be discarded as mere bookkeeping.

## 5.8 Universal Properties: What Is And Is Not Packaged

Induction principles often admit a universal-property formulation. For an
ordinary inductive type, one expects the canonical algebra to be initial, or
homotopy-initial when maps carry higher equality. For a directed higher
inductive category, one similarly expects a category of algebras, structured
functors, and coherent transfors in which the presented object is suitably
initial.

That formulation is mathematically attractive because it gathers recursion,
induction, uniqueness, and higher coherence into one statement. It is also
more demanding than writing a selected eliminator. One must define the
algebra category at every relevant cell dimension, identify its notion of
equivalence, and prove contractibility or an equivalent universal mapping
property.

<!-- evidence:IND-GENERAL-INITIALITY -->

> **Formal status — research boundary.** Evidence
> `IND-GENERAL-INITIALITY`. The current calculus packages Nat and equality
> induction, generic `PathOut` arrow induction, and the selected
> WalkingEnd eliminator. It does not yet prove a general equivalence between
> such interfaces and homotopy-initial categorical algebras.

We will therefore use “walking” in its presentation-theoretic sense and use
the eliminator that is actually checked. Full functor-category initiality is
a strengthening target, not an implicit premise of the computation.

## 5.9 The Interface Needed For Encode–Decode

The next two chapters isolate the additional ingredients required by the
walking-endomorphism calculation:

- Chapter 6 supplies a contextual eliminator whose generator datum is a
  coherent directed transformation;
- Chapter 7 supplies one-dimensionality, allowing a directed 2-cell between
  parallel based arrows to be read as equality.

The roles are deliberately ordered. Elimination constructs directed data.
Truncation may later show that some of that data is unique or equality-like.
Reversing the order would erase the very directionality the example is meant
to expose.
<!-- /book-source:chapter-5 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-6 book/chapters/06-directed-hits.md -->
<a id="chapter-6"></a>

# 6. Directed Higher Inductive Types

An ordinary inductive type is specified by point constructors. A higher
inductive type may also be specified by path constructors and constructors
between paths. In a directed foundation, the corresponding presentation may
contain objects, directed arrows, and higher directed cells. The change is
small in notation and large in meaning: an arrow constructor does not carry
an inverse unless inverse data are separately supplied.

This chapter develops the one directed higher-inductive interface that the
current emdash calculus actually implements. It is enough to support the
central calculation of Chapter 8 and to reveal what a reusable directed-HIT
schema would have to provide. We will not promote this single example into a
general theorem about all cell presentations.

## 6.1 Constructors With Direction

At a schematic level, a directed higher-inductive category may have:

- **object constructors**, such as `b:Obj(W)`;
- **arrow constructors**, such as $\ell:b\to b$;
- **cell constructors**, identifying or comparing composites of arrows;
- **dimension conditions**, controlling which higher cells remain
  nontrivial.

The eliminator must mirror these constructors. A nondependent recursor into a
category `C` asks for an interpretation of every object, arrow, and cell
constructor in `C`. A dependent eliminator into a family `D` asks for
lifts in the appropriate fibres. A contextual eliminator between two families
asks for fibre functors together with comparison cells. In each case,
constructor computations say that the induced map observes the supplied data
at the constructors.

For a groupoidal path constructor, one may freely use inverse paths in later
reasoning. For a directed arrow constructor, that move is unavailable. If a
presentation contains only

$$
\ell:b\longrightarrow b,
$$

then it generates forward composites
$\mathrm{id}_b,\ell,\ell\circ\ell,\ldots$; no negative power has been
introduced. This is the fundamental distinction between the walking
endomorphism and the circle.

The formal ledger for such a signature is therefore longer than a constructor
list. It records formation, introductions and their boundaries, the chosen
eliminator, constructor beta rules, higher action and coherence, dimension
data, and the current uniqueness status. The general template and the exact
WalkingEnd instance are collected in
[Appendix G.6](#appendix-formal-presentation-g6); this chapter develops the
same clauses in mathematical order.

## 6.2 The Selected Walking Signature

Write `W` for the category `WalkingEnd`, with constructors

$$
*:\operatorname{Obj}(W),
\qquad
\ell:\operatorname{Hom}_W(*,*).
$$

The category is opaque. Its object classifier, hom-categories, identities,
and composition are not defined by reducing them to a Nat model. Alongside
the constructors, the signature retains evidence that `W` is
one-dimensional: every hom-category is discrete.

<!-- evidence:WE-SIGNATURE -->

> **Formal status — checked.** Evidence `WE-SIGNATURE`.
> `WalkingEnd_cat`, `walking_base`, and `walking_loop` are
> opaque declarations. `walking_end_is_one_cat` is explicit signature
> evidence; it does not unfold the category into a concrete presentation.

One-dimensionality is a height condition, not an invertibility condition. It
says that parallel 2-cells in each hom are equality-like and that there are no
nontrivial higher directed layers there. It does not say that every 1-cell of
`W` has a reverse. Chapter 7 will make the distinction precise.

Why keep `W` opaque? Because the theorem in Chapter 8 is then a
consequence of its constructors, eliminator, and dimension evidence. If its
based hom were defined to be Nat, the calculation would merely restate a
definition. Opacity turns the comparison with Nat into a normalization
theorem.

## 6.3 The Contextual Algebra

Let

$$
R,D:W\longrightarrow\mathsf{Cat}
$$

be directed Cat-valued families. At the base, suppose we are given a functor

$$
u:R[*]\longrightarrow D[*].
$$

There are two ways to move an element of `R[*]` once around the
generator and then apply `u`:

$$
D[\ell]\circ u,
\qquad
u\circ R[\ell].
$$

The selected lax orientation asks for a transformation

$$
\sigma:
D[\ell]\circ u
\Longrightarrow
u\circ R[\ell].
$$

These data form the contextual algebra of the walking endomorphism. Its
eliminator produces a displayed functor

$$
\mathsf{ind}^{d}(R,D,u,\sigma):R\Longrightarrow D
$$

over the whole of `W`.

<!-- evidence:WE-CONTEXTUAL-ELIMINATOR -->

> **Formal status — checked.** Evidence
> `WE-CONTEXTUAL-ELIMINATOR`. The owner is
> `walking_end_ind_funcd`. Its base component computes to `u`, and
> its displayed action on the literal generator computes to the component of
> `sigma` at the selected source object.

The direction of `sigma` deserves attention. It is not an equality
asserting strict commutation, nor is it automatically reversible. It is a
directed cell comparing the two composites. This is the right amount of
coherence for the displayed-functor interface used by emdash: composition
with base action commutes laxly in the selected direction, and higher
naturality continues through the generic transfor calculus.

The word “contextual” means that the eliminator retains `R`, the context
from which inputs are drawn. Removing `R` too early would reduce `u`
to a single object and `sigma` to a single lift. That specialization is
useful, but it cannot construct Chapter 8's decoder from one nonconstant
family to another.

## 6.4 Sections And Recursors Are Special Cases

Take `R` to be the constant terminal family. A functor
$R[*]\to D[*]$ is determined by an object `d` of the base
fibre. The generator coherence reduces to an arrow

$$
\bar\ell:D[\ell](d)\longrightarrow d.
$$

Contextual elimination then yields a dependent section

$$
\mathsf{ind}(D,d,\bar\ell):
\prod_{x:\,W}D[x].
$$

Take `D` constant as well, at a category `C`. Its transport is the
identity, so the data become an object `c:Obj(C)` and an endomorphism
$f:c\to c$. The resulting section is an ordinary functor

$$
\mathsf{rec}(C,c,f):W\longrightarrow C
$$

with the expected observations

$$
\mathsf{rec}(*)=c,
\qquad
\mathsf{rec}[\ell]=f.
$$

<!-- evidence:DHIT-DERIVED-ELIMINATORS -->

> **Formal status — checked.** Evidence `DHIT-DERIVED-ELIMINATORS`.
> `walking_end_ind_sec` and `walking_end_rec_func` are transparent
> specializations of the contextual eliminator, with checked base and loop
> observations.

This dependency is architecturally important. There is one semantic
elimination principle, not three unrelated black boxes. The derived views
retain the generic functor and transfor action, which is why a recursor-built
object such as `Code` can later be acted on at higher cells.

## 6.5 What “Computes” Means

A constructor computation can be visible in several ways:

1. a runtime reduction may expose the supplied constructor datum;
2. a typed equality may state that two stable observations agree;
3. a proof-time comparison may join expressions without selecting either as
   the runtime normal form.

For the walking eliminator, the contextual base projection and the displayed
generator cell are the constructor-specific runtime owners. Narrow
projections expose the same data through the derived section and recursor
views. Transparent equality theorems record those observations at their
readable types.

This distinction prevents a tempting but dangerous simplification. One
should not add a new constructor-specific rewrite merely because a theorem is
mathematically true. Generic functoriality already owns preservation of
identities, composition, and ordinary naturality. The HIT-specific rules own
only what observing the literal constructors must reveal.

The book will normally write a constructor equation with `=`. A formal
status note determines whether that equation is runtime computation,
propositional equality, or a mathematical development. This keeps the main
line readable without blurring the operational contract.

## 6.6 From A Pointwise Step To A Coherent Spiral

Chapter 8 requires more than the ordinary recursor. Its code family and based
representable family are both nonconstant:

$$
\mathsf{Code},\mathsf{Rep}_*:W\longrightarrow\mathsf{Cat}.
$$

At the base, natural-number powers give a carrier function

$$
n\longmapsto\ell^n.
$$

Because the source is the path category of Nat, equality action lifts this
function to a functor

$$
\mathsf{power}:\mathsf{Path}(\mathbb N)
  \longrightarrow\operatorname{Hom}_W(*,*).
$$

The contextual algebra still needs a transformation

$$
\mathsf{Rep}_*[\ell]\circ\mathsf{power}
\Longrightarrow
\mathsf{power}\circ\mathsf{Code}[\ell].
$$

Pointwise, the endpoints are $\ell\circ\ell^n$ and
$\ell^{n+1}$. Nat recursion makes them propositionally equal, but a
family of equalities is not by itself the required transformation into a
directed hom-category. The higher action and endpoint comparisons must be
assembled coherently.

Emdash does this through a restricted equality-local core inclusion and a
`PathLift` construction. Informally, `PathLift` turns a function
whose source carries equality paths into a functor with directed target. The
non-strict spiral inserts the necessary comparison before the lifted step;
ordinary path functoriality discharges the other side. Its readable component
has the forward direction

$$
\ell\circ\ell^n\longrightarrow\ell^{n+1}.
$$

<!-- evidence:WE-SPIRAL -->

> **Formal status — checked.** Evidence `WE-SPIRAL`. The selected
> `walking_power_spiral` is the explicit restricted-core-inclusion
> construction, and `walking_power_spiral_cell` exposes the directed
> component shown above.

The spiral is a small but representative lesson in functorial type theory.
Carrier equality supplies useful input, yet the consumer asks for a coherent
cell with functorial higher action. The bridge between the two must be an
explicit construction; it cannot be hidden by treating every directed hom as
an identity type.

## 6.7 The Derived Decoder Interface

Substituting

$$
R=\mathsf{Code},\qquad
D=\mathsf{Rep}_*,\qquad
u=\mathsf{power},\qquad
\sigma=\mathsf{spiral}
$$

into contextual elimination yields

$$
\mathsf{decode}^{d}:\mathsf{Code}\Longrightarrow\mathsf{Rep}_*.
$$

Its fibre component at `x` is a functor from codes over `x` to
based arrows ending at `x`; at the base it computes to the power
functor. Naturality of this single displayed functor is what later produces a
directed normalization cell for every opaque based arrow.

This is stronger than defining only a function
`Nat -> Hom_W(*,*)`. The latter supplies candidate normal forms but
contains no explanation of why an arbitrary arrow reaches its candidate. The
contextual eliminator supplies exactly that missing action.

## 6.8 Toward A General Directed-HIT Schema

The walking interface suggests a reusable architecture. A general schema
would need at least:

- a language of object, arrow, and higher-cell boundaries;
- generated recursion, dependent elimination, and contextual elimination;
- functorial action at every exposed cell level;
- a policy distinguishing computational constructor rules from
  propositional coherences;
- subject-reduction and overlap checks for the generated rules;
- algebra and morphism categories suitable for universal-property theorems;
- optional dimension or truncation constructors whose consequences are
  separately controlled.

Pushouts, quotients, directed intervals, and cell complexes would test
different parts of such a design. None follows merely by changing the name of
the walking generator.

<!-- evidence:DHIT-GENERAL-SCHEMA -->

> **Formal status — research boundary.** Evidence `DHIT-GENERAL-SCHEMA`.
> The active code implements the selected opaque WalkingEnd signature and its
> eliminator interfaces. It does not yet implement a generic signature
> compiler or arbitrary directed higher-inductive categories.

The selected example is nevertheless substantial enough to guide that future
work. It forces object action, arrow action, a genuine lax coherence cell,
higher functorial lifting, constructor computation, and an interaction with
finite categorical height. The next chapter develops the last item before we
use all of them together.
<!-- /book-source:chapter-6 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-7 book/chapters/07-truncation-and-categorical-height.md -->
<a id="chapter-7"></a>

# 7. Truncation And Categorical Height

An induction principle tells us how to construct data. A truncation principle
tells us how much distinction that data can retain. These ideas meet in the
walking-endomorphism proof: contextual elimination first constructs a
directed 2-cell, and one-dimensionality then shows that the parallel
1-arrows it connects are equal.

There are two related height measures in emdash. Recursive groupoidal
truncation measures the identity types of a classifier. Recursive categorical
dimension measures the hom-categories of a directed category. They agree in
important boundary cases, but they are not the same definition. Keeping them
separate lets us use equality locally without declaring all directed arrows
invertible.

## 7.1 Recursive Truncation

The truncation levels begin at `-2` and continue by successor. For a
classifier `A`, define

$$
\begin{aligned}
\mathsf{isTrunc}_{-2}(A)
  &:=\mathsf{isContr}(A),\\
\mathsf{isTrunc}_{n+1}(A)
  &:=\prod_{x,y:A}\mathsf{isTrunc}_{n}(x=y).
\end{aligned}
$$

Thus:

- a `(-2)`-truncated classifier is contractible;
- a `(-1)`-truncated classifier is a proposition;
- a `0`-truncated classifier is a set;
- a `1`-truncated classifier has set-valued identity types;
- each further level permits one more layer of identity structure.

The recursive equation is the important part. To prove that `A` is
`(n+1)`-truncated, one proves that every identity classifier `x=y`
is `n`-truncated. Truncation arguments can therefore descend through
identity types until they reach contractibility.

<!-- evidence:LOGIC-TRUNCATION-PREDICATE -->

> **Formal status — checked.** Evidence
> `LOGIC-TRUNCATION-PREDICATE`. `IsTruncGrpd` implements this
> recursion, with `IsPropGrpd` and `IsSetGrpd` as the proposition
> and set abbreviations.

This is a property of an existing classifier. Supplying
`h:isTrunc_n(A)` does not replace `A` by a quotient, erase its
points, or create a new type. It certifies that higher identity distinctions
already collapse at the stated level.

## 7.2 Truncation Evidence Is Itself A Property

There may be many expressions witnessing that `A` is `n`-truncated.
Mathematically, the choice should not matter. The evidence classifier itself
is proposition-valued:

$$
\mathsf{isProp}\bigl(\mathsf{isTrunc}_n(A)\bigr).
$$

Consequently any two truncation witnesses are equal. Packages may retain the
witness for later use without turning it into observable structure.

<!-- evidence:LOGIC-TRUNCATION-EVIDENCE-PROP -->

> **Formal status — checked.** Evidence
> `LOGIC-TRUNCATION-EVIDENCE-PROP`. The theorem is uniform in the
> truncation level and the classifier.

There is a useful distinction between **retaining** evidence and
**erasing** it. Emdash generally retains evidence in Sigma-like packages so a
consumer can project it. Proposition-valuedness then proves that two choices
are equal when equality is needed. This is constructive proof irrelevance,
not an instruction to remove the field from the data representation.

## 7.3 Closure Principles

The recursive definition supports the standard structural operations.

First, truncation is monotone:

$$
\mathsf{isTrunc}_n(A)
\longrightarrow
\mathsf{isTrunc}_{n+1}(A).
$$

A type with no distinctions above level `n` also has none above the
weaker level `n+1`.

Second, dependent functions preserve a pointwise truncation bound. If every
`B(x)` is `n`-truncated, then

$$
\prod_{x:A}B(x)
$$

is `n`-truncated. At successor levels the proof uses the equivalence
between equality of functions and pointwise equality.

Third, dependent sums preserve a common bound. If `A` and every
`B(x)` are `n`-truncated, then

$$
\sum_{x:A}B(x)
$$

is `n`-truncated. The successor proof analyzes equality of dependent
pairs as a base path together with a path over it.

<!-- evidence:TRUNC-CLOSURE -->

> **Formal status — checked.** Evidence `TRUNC-CLOSURE`. The active
> operations are `is_trunc_grpd_succ`, `is_trunc_pi`, and
> `is_trunc_sigma`, each with recursive base and successor behavior.

Truncation is also invariant under equivalence and closed under retracts. For
the latter, suppose `Y` is a retract of `X`: there are maps

$$
Y\xrightarrow{s}X\xrightarrow{r}Y
$$

with $r\circ s$ equal to the identity on `Y`. Any truncation
bound on `X` descends to `Y`.

<!-- evidence:TRUNC-RETRACT -->

> **Formal status — checked.** Evidence `TRUNC-RETRACT`.
> `is_trunc_retract` works uniformly at every recursive truncation
> level from explicit retraction data.

These closure results are not merely a catalogue. Pi closure makes
proposition evidence stable under universal quantification; Sigma closure
controls total spaces and evidence-retaining universes; retract closure lets a
normalization or equivalence argument transfer height to a less explicit
carrier.

## 7.4 Universes Of Truncated Classifiers

For each level `n`, the package

$$
\mathsf{TruncGrpdU}(n)
  :=\sum_{A:\mathsf{Grpd}}\mathsf{isTrunc}_n(A)
$$

retains a classifier and its truncation evidence. Since the evidence is a
proposition, equality of packages is governed by the carriers rather than by
an arbitrary choice of proof.

The selected truncated-universe univalence theorem identifies package
equality with carrier equivalence:

$$
(X=Y)
\simeq
\mathsf{TypeEquiv}
  (\mathsf{carrier}(X),\mathsf{carrier}(Y)).
$$

Both directions and their round trips are named. This is a useful, precise
univalent universe: it ranges over classifiers already equipped with one
fixed truncation bound.

<!-- evidence:UNIV-TRUNCATED -->

> **Formal status — checked.** Evidence `UNIV-TRUNCATED`. The package
> is `TruncGrpdU`; `trunc_grpd_univalence_type_equiv` supplies the
> carrier equivalence between package identity and `TypeEquiv`.

The adjective “restricted” matters. This theorem does not by itself identify
objects in an arbitrary directed category with ordinary categorical
isomorphisms. Nor does it construct a truncation of an arbitrary input. It is
a univalence theorem for an evidence-retaining subuniverse of the groupoidal
classifier universe.

## 7.5 Finite Directed Dimension

Truncation follows identity types. Directed dimension follows hom-categories.
The nonnegative dimension codes are generated by

$$
0_{\mathsf{cat}}
\qquad\text{and}\qquad
\mathsf{succ}_{\mathsf{cat}}(n).
$$

Their classifier is recursive:

$$
\begin{aligned}
\mathsf{isNCat}(0,C)
  &:=\mathsf{isDiscreteCat}(C),\\
\mathsf{isNCat}(n+1,C)
  &:=\prod_{x,y:\operatorname{Obj}(C)}
       \mathsf{isNCat}
       \bigl(n,\operatorname{Hom}_C(x,y)\bigr).
\end{aligned}
$$

A zero-dimensional category is discrete. A one-dimensional category may have
nonidentity directed 1-arrows, but each of its hom-categories is discrete. A
two-dimensional category may have nontrivial 2-cells, while the next homs are
discrete, and so on.

There is a corresponding object-truncation level:

$$
\begin{aligned}
\mathsf{catLevel}(0)&=0,\\
\mathsf{catLevel}(n+1)&=\mathsf{catLevel}(n)+1.
\end{aligned}
$$

If `C` has categorical dimension `n`, then its object classifier is
truncated at `catLevel(n)`. In particular, objects of a discrete category
form a set, and objects of a one-dimensional category form a 1-truncated
classifier.

<!-- evidence:CAT-DIMENSION -->

> **Formal status — checked.** Evidence `CAT-DIMENSION`. `IsNCat`
> owns the homwise recursion, `cat_dim_trunc_level` computes the
> corresponding groupoidal level, and `ncat_obj_trunc` proves the
> object-truncation consequence.

This bridge does not collapse the two notions. `IsNCat` constrains all
iterated directed homs; object truncation records only equality structure on
the object classifier. Two categories can have equally truncated object
classifiers while differing radically in their directed arrows.

## 7.6 One-Dimensionality Of The Walking Endomorphism

The WalkingEnd signature contains

$$
\mathsf{isNCat}(1,W).
$$

Unfolding the successor clause gives, for every `x,y:Obj(W)`,

$$
\mathsf{isDiscreteCat}
  \bigl(\operatorname{Hom}_W(x,y)\bigr).
$$

In particular the based hom

$$
H_x:=\operatorname{Hom}_W(*,x)
$$

is discrete. Given two based arrows $p,q:*\to x$, a directed
2-cell

$$
\alpha:p\longrightarrow q
\quad\text{in }H_x
$$

can therefore be converted to an equality `p=q` of objects of the
hom-category.

<!-- evidence:WE-ONE-DIMENSIONAL -->

> **Formal status — checked.** Evidence `WE-ONE-DIMENSIONAL`.
> `walking_end_hom_discrete` specializes the dimension witness, and
> `walking_end_based_cell_to_path` converts a based 2-cell to equality.

This operation is local to the next hom. It does **not** produce an arrow
$q\to p$, an inverse for `p`, or an inverse for `ell` in
`W`. Equality between the *objects of a discrete hom-category* and
invertibility of those objects as *arrows of the ambient category* are
different statements.

## 7.7 The Exact Height Step In Encode–Decode

Chapter 8 constructs, for every based arrow $p:*\to x$, a directed
normalization cell

$$
\nu_p:
p\longrightarrow
\mathsf{decode}_x(\mathsf{encode}_x(p))
$$

inside `H_x`. Only then does hom-discreteness give

$$
p=
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

This is the sole step in the hard inverse where one-dimensionality is used.
It converts already-constructed directed information into equality; it does
not help construct the information.

The other inverse,

$$
\mathsf{encode}_*(\ell^n)=n,
$$

is proved independently by Nat induction using the zero and successor
computations. It does not require hom-discreteness. Nat sethood plays two
nearby but distinct roles: it makes the concrete `BNat` hom-category
discrete, and it can be transported backward along the final carrier
equivalence to give a second proof that the based-endomorphism carrier is a
set. Neither role should be substituted for the directed normalization step.

This separation is a model for later proofs:

1. build a cell using functorial or contextual action;
2. invoke a dimension hypothesis at the exact hom level where the cell lives;
3. extract equality only if the target theorem needs it.

The intermediate cell can carry an orientation or support further
composition even when its equality shadow cannot.

## 7.8 Properties Are Not Reflectors

A general truncation operation would assign to every classifier `A` a
new classifier `||A||_n`, together with a universal map and an
elimination principle into `n`-truncated targets. In a directed setting
one may also ask for categorical truncations that collapse cells above a
chosen dimension while preserving lower directed structure.

The active layer does not provide either general reflector. It provides
predicates on existing classifiers, closure theorems, evidence-retaining
universes, and consequences of finite categorical dimension. Those tools are
enough for the WalkingEnd calculation because its one-dimensionality is
signature data rather than something that must be freely imposed afterward.

<!-- evidence:TRUNC-REFLECTOR -->

> **Formal status — research boundary.** Evidence `TRUNC-REFLECTOR`.
> A general truncation HIT or directed categorical reflector remains future
> work and must come with its own universal and computational properties.

We now have every prerequisite for the main proof: equality-local action,
functors and directed families, contextual elimination, equivalence packages,
recursive truncation, and homwise categorical height. The next chapter puts
them together without identifying direction with invertibility.
<!-- /book-source:chapter-7 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-8 book/chapters/08-walking-endomorphism.md -->
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

A future comparison with the circle should therefore proceed by an explicit
group-completion construction, not by renaming `Nat` to
`Int` or declaring `ell` invertible.

<!-- evidence:WE-GROUP-COMPLETION -->

> **Formal status — research boundary.** Evidence
> `WE-GROUP-COMPLETION`. No `BInt`/circle group completion
> or comparison functor is active.

The calculation has reached its intended boundary. It proves that an opaque
directed generator has exactly the expected natural powers, and it proves
noninvertibility rather than assuming it. Stronger categorical universal
properties are the next layer, not hidden premises of this one.

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
<!-- /book-source:chapter-8 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-9 book/chapters/09-transfors-and-the-calculus-of-cuts.md -->
<a id="chapter-9"></a>

# 9. Transfors And The Calculus Of Cuts

Composition is indispensable, but a syntax made only of nested composites
quickly forgets why a particular reassociation matters. Functorial type theory
therefore gives important cuts a name and a computational owner. A functor
acts on an arrow; postcomposition and precomposition act on represented homs;
a transfor acts off the diagonal; and a universal construction eliminates a
map through the object it represents. Each operation controls its own
reassociation.

This point of view is inspired by the categorical proof theory of
[Došen's *Cut Elimination in Categories*](#ref-dosen-cut-elimination).
We use that work only as a conceptual reference. The presentation below is
newly written for emdash, whose iterated homs and directed families require a
different formal architecture.

The gain is not merely prettier notation. A selected cut can compute while
retaining the functor or transfor that acts on the next hom. An unrestricted
associativity rewrite would erase that information, create competing normal
forms, or loop by repeatedly changing brackets. Controlled cut elimination
instead answers three questions at once: what is being eliminated, where its
normal form lives, and which higher action survives.

## 9.1 Four Levels Of Cuts

We shall use four levels throughout the rest of the book.

1. An **arrow cut** composes one chosen arrow on the left or right. Its
   owners are the lower-star postcomposition and upper-star precomposition
   actions.
2. A **family cut** composes next to an arrow that varies naturally. Its
   owner is the off-diagonal action of a transfor.
3. A **structural cut** eliminates data introduced by a product, dependent
   total, curry, or related type former. Its owner is the corresponding
   projection or eliminator.
4. A **universal cut** factors through a chosen representing object. Its
   owner is an adjunction, representability comparison, or another explicit
   universal-property interface.

These levels are not four unrelated collections of rewrite rules. They form a
progression. Arrow cuts explain local composition; family cuts explain
naturality; structural cuts explain computation for categorical type formers;
and universal cuts explain why constructions such as adjoints, Yoneda maps,
and weighted limits compute.

We also keep four equality modes distinct. A runtime reduction selects a
normal form. A proof-time comparison helps Lambdapi elaborate two intended
presentations without making either one compute to the other. A propositional
equality is an internal witness. A mathematical equality in free-form theory
states the intended theorem while naming the interface still needed to check
it. The symbol $\rightsquigarrow$ below is reserved for an actual selected
runtime reduction; an ordinary equality sign does not silently make that
claim.

In the terminology of
[Appendix G.4](#appendix-formal-presentation-g4), each named cut is an
elimination followed by a computation rule. Its formation and introduction
data determine which composite is well typed; its full functor or transfor
owner supplies higher action; and any eta or uniqueness principle is stated
separately. This is why a pointwise naturality equation cannot replace
`tapp1_func`, and why a universal comparison needs both beta and eta rather
than one attractive factorization formula.

## 9.2 Arrow Cuts

Composition is written $g\circ f$: first $f$, then $g$. The two star actions
record which side of a represented hom is moving.

If $g:w\to x$ and $u:x\to y$, then

$$
u_*(g):=u\circ g:w\to y
$$

is **postcomposition** by $u$. If $u:x\to y$ and $h:y\to z$, then

$$
u^*(h):=h\circ u:x\to z
$$

is **precomposition** by $u$. Lower star is covariant in the moving target;
upper star is contravariant in the moving source. They are different
operations, not typographic variants.

The implemented forms are slightly more general. For $K:A\to B$ and
$p:x\to y$ in $A$, postcomposition uses $K[p]$ on a hom ending at $Kx$,
while precomposition uses $K[p]$ on a hom beginning at $Ky$. Retaining $K$
is what lets the action iterate on higher cells.

### 9.2.1 Example 1: Postcomposition Accumulates

Let

$$
g:w\to x,\qquad u:x\to y,\qquad v:y\to z.
$$

Two consecutive lower-star cuts reduce to one:

$$
v_*(u_*(g))\rightsquigarrow(v\circ u)_*(g).
$$

Both sides are arrows $w\to z$. The selected normal form retains a single
postcomposition action whose moving arrow is $v\circ u$; it does not expand
to a raw threefold composite. The generic owner is
`hom_postcomp_fapp0`, and the displayed equality mode is runtime reduction.
Before capping at $g$, `hom_postcomp_func` remains a functor between
hom-categories, so its action on 2-cells between possible values of $g$ is
still available.

The functor-indexed version says the same thing. If $p:x\to y$ and
$q:y\to z$ in $A$, then consecutive action by $K[p]$ and $K[q]$ accumulates
under the single arrow $q\circ p$. Ordinary functoriality belongs to the
generic `fapp*` calculus; no constructor receives a private composition law.

### 9.2.2 Example 2: Precomposition Reverses The Action Order

Let

$$
u:w\to x,\qquad v:x\to y,\qquad h:y\to z.
$$

The corresponding upper-star reduction is

$$
u^*(v^*(h))\rightsquigarrow(v\circ u)^*(h).
$$

Both sides are arrows $w\to z$. The selected normal form is one
precomposition action along $v\circ u$. The generic owner is
`hom_precomp_along_fapp0`, and this is again runtime reduction. Its uncapped
form `hom_precomp_along_func` remains a functor on the represented hom, with
the next hom-action intact.

The order is worth reading twice. Starting with $h$, we first precompose by
$v$ and then by $u$, but the accumulated base arrow is $v\circ u$. Thus

$$
u^*\circ v^*=(v\circ u)^*.
$$

That reversal is contravariance, not a special exception to associativity.

<!-- evidence:CAT-HOM-CUTS -->

> **Formal status — checked.** Evidence `CAT-HOM-CUTS`. The full and capped
> lower-star and upper-star actions have identity, consecutive-action, and
> adjacent raw-cut computations. Their ordinary-composition readings remain
> proof-time comparisons where selecting a second runtime normal form would
> be harmful.

### 9.2.3 Why There Is No Global Associativity Rewrite

The ordinary associator is available as a proof-time comparison and as
propositional evidence. It is not installed as a pair of unrestricted runtime
rules. Such rules would either orient every composite toward a normal form
that ignores semantic owners or permit both bracketings and loop.

Star accumulation is narrower. It reassociates exactly when one side is a
represented-hom action, and its result retains that action as a stable head.
The same policy will govern the next three levels: eliminate the cut at the
construction that understands it.

## 9.3 Family Cuts

Let $F,G:A\to B$ and let $\eta:F\Rightarrow G$. A point component
$\eta_x:Fx\to Gx$ is only the diagonal of a more useful operation. For every
$x,y:A$ there is an off-diagonal functor

$$
\eta_{x,y}:\operatorname{Hom}_A(x,y)\longrightarrow
           \operatorname{Hom}_B(Fx,Gy).
$$

For $f:x\to y$, write its value as $\eta[f]:Fx\to Gy$. Setting
$f=\mathrm{id}_x$ recovers $\eta_x$; retaining the whole functor retains its
action on 2-cells between arrows $f$.

<!-- evidence:TRANSF-POINT-OFFDIAGONAL -->

> **Formal status — checked.** Evidence `TRANSF-POINT-OFFDIAGONAL`.
> `tapp0_fapp0` observes the point component, while `tapp1_func` and
> `tapp1_fapp0` expose the iterable and capped off-diagonal actions.

### 9.3.1 Example 3: The Two Naturality Cuts

Take arrows

$$
h:w\to x,\qquad f:x\to y,\qquad g:y\to z.
$$

There are two neighboring cuts, one on each side of the varying arrow:

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

The first source and target are $Fx\to Gz$; the second are $Fw\to Gy$.
In each case the selected normal form is one off-diagonal action on the
composite source arrow. The generic owner is `tapp1_fapp0`, and both
displayed equalities are runtime reductions. At the uncapped level
`tapp1_func` remains a functor between hom-categories, so a 2-cell between
$f$ and $f'$ is carried to a 2-cell between $\eta[f]$ and $\eta[f']$ after
the cut has normalized.

<!-- evidence:TRANSF-STRICT-NATURALITY -->

> **Formal status — checked.** Evidence `TRANSF-STRICT-NATURALITY`. Both
> full-functor and capped-arrow forms are owned by the generic `tapp*`
> calculus. Constructor-specific copies of ordinary naturality are neither
> needed nor desired.

The familiar naturality square is the identity-boundary instance. For
$f:x\to y$, the expressions $G[f]\circ\eta_x$ and
$\eta_y\circ F[f]$ both normalize through the common interior $\eta[f]$.
Naturality is therefore not an equality proof added after defining a family
of point components. It is computation exposed by the family action itself.

Identity and vertical composition follow the same architecture. The identity
transfor and a vertical composite live in the transformation category, so
their component projections use the generic identity and composition
calculus. Higher transfors arise by iterating the next hom rather than by
inventing a separate coherence language at every dimension.

## 9.4 Structural Cuts

A structural cut applies an eliminator to data whose introduction form is
known. Product projections are the simplest case, but they already reveal an
important distinction between the general categorical theory and the
currently checked category-of-categories instance.

### 9.4.1 Example 4: The Product/Projection Benchmark In A General Category

Let $K$ be a category equipped with chosen binary products. Take objects

$$
A_0,A_1,B_0,B_1,C:\operatorname{Obj}(K)
$$

and arrows

$$
h:A_0\to A_1,\qquad
k:B_0\to B_1,\qquad
g:A_1\to C.
$$

Write $h\times k:A_0\times B_0\to A_1\times B_1$ for the induced product
arrow, and distinguish the two projections by

$$
\pi_1^1:A_1\times B_1\to A_1,
\qquad
\pi_1^0:A_0\times B_0\to A_0.
$$

Upper-star precomposition in $K$ gives

$$
(\pi_1^1)^*(g):A_1\times B_1\to C.
$$

The Došen-style product cut is the equation

$$
(\pi_1^1)^*(g)\circ(h\times k)
=
(\pi_1^0)^*(g\circ h),
$$

with both sides in $\operatorname{Hom}_K(A_0\times B_0,C)$. Its intended
computational orientation is left to right. The calculation combines two
controlled steps:

$$
\pi_1^1\circ(h\times k)=h\circ\pi_1^0
$$

by product projection, followed by upper-star accumulation. The arrow $k$
disappears because the first projection observes only the first component.

The source is a composite out of $A_0\times B_0$ and the target is a single
upper-star cut with the same source and codomain. The proposed normal form is
$(\pi_1^0)^*(g\circ h)$. Its future generic owners should be the upper-star
action together with chosen product projections and the bifunctorial action
of the product structure in $K$. The equality mode here is mathematical
development: emdash does not yet package binary products of objects in an
arbitrary ambient category with this universal computation. Such an owner
should retain the next-hom actions of the projection and product-arrow
operations, rather than stop at a 1-categorical equation.

> **Formal status — mathematical development.** The general theorem assumes a
> chosen binary-product interface internal to an arbitrary category $K$,
> including product arrows, projection beta, and iterable higher action. The
> active product package instead supplies binary products of categories, which
> gives the specialization $K=\mathsf{Cat}$ described next.

### 9.4.2 The Checked Cat-Specialized Legs

Set $K=\mathsf{Cat}$. Then $A_i,B_i,C$ are categories and $h,k,g$ are
functors. The active product-valued-functor representation exposes projection
by a Sigma observation. Its checked structural reduction is

$$
\mathsf{fst}(h\times k)\rightsquigarrow h\circ\pi_1^0.
$$

The checked, owner-aligned upper-star cut is

$$
(\pi_1^0)^*(h^*(g))
\rightsquigarrow
(h\circ\pi_1^0)^*(g),
$$

and $h^*(g)$ is proof-time comparable with the readable composite
$g\circ h$. Both owner-aligned sides retain the upper-star precomposition
head and therefore its higher action on transfors between possible functors
$g$.

The literal $\mathsf{Cat}$ instance of the general equation is not currently
one runtime reduction. A focused typed audit found both sides well formed,
checked the two owner-aligned legs, and found that neither runtime conversion
nor typed reflexivity joins the raw composite
$\pi_1^1\circ(h\times k)$ directly to the selected observation
$\mathsf{fst}(h\times k)$. Packaging that narrow projection/composition
comparison would suffice. Installing a broad product eta rewrite would be a
much stronger and unsafe response.

<!-- evidence:CUT-PRODUCT-PROJECTION -->

> **Formal status — formal consequence.** Evidence
> `CUT-PRODUCT-PROJECTION`. The $\mathsf{Cat}$-specialized equation follows
> from controlled associativity, upper-star composition, and the checked
> product projection. The diagnostic suite checks the owner-aligned
> reduction. The literal raw-composite bridge is not packaged, so the
> textbook display is not labeled a checked kernel reduction.

### 9.4.3 Example 5: Product Beta Is Elimination After Introduction

In a category $K$ with chosen products, arrows $p:X\to A$ and $q:X\to B$
have a pairing $\langle p,q\rangle:X\to A\times B$. The characteristic
structural cuts are

$$
\pi_1\circ\langle p,q\rangle=p,
\qquad
\pi_2\circ\langle p,q\rangle=q.
$$

The source and target of the first equation lie in
$\operatorname{Hom}_K(X,A)$, and those of the second lie in
$\operatorname{Hom}_K(X,B)$. Their proposed normal forms are $p$ and $q$.
For arbitrary $K$, the owners and higher action belong to the same future
chosen-product interface as Example 4, so these equations are mathematical
development rather than claims about the present kernel.

The active category-of-categories specialization is nevertheless concrete.
For arrows $p:a\to a'$ in $A$ and $q:b\to b'$ in $B$, the pair $(p,q)$ is an
arrow $(a,b)\to(a',b')$ in the product category. The projection functors
compute:

$$
\pi_1[p,q]\rightsquigarrow p,
\qquad
\pi_2[p,q]\rightsquigarrow q.
$$

Here the selected normal forms are the component arrows themselves. The
specialized owners are the capped hom-actions of
`Product_projL_func` and `Product_projR_func`, and the equality mode is
runtime reduction. Before capping, each full hom-action remains a projection
functor from a product of hom-categories, so higher component cells remain
available.

<!-- evidence:CAT-PRODUCT-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-PRODUCT-CALCULUS`. Product
> categories, product maps, projection functors, and their object and hom
> projections have focused componentwise computations. This is evidence for
> the desired general architecture, not an assertion that arbitrary
> object-level products in every $K$ are already implemented.

### 9.4.4 Fibred Structural Cuts

The same introduction/elimination pattern appears in a dependent categorical
context. Let $B,C:K\vdash\mathsf{Cat}$ be independent families over one base,
and let $P(B,C)$ be their fibrewise product. For displayed functors

$$
\Phi:E\Longrightarrow B,
\qquad
\Psi:E\Longrightarrow C,
$$

pairing introduces a map
$\mathsf{pair}_d(\Phi,\Psi):E\Longrightarrow P(B,C)$, while the two displayed
projections eliminate it. Their structural cuts are whole displayed-functor
reductions:

$$
\mathsf{projL}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Phi,
\qquad
\mathsf{projR}_d\circ\mathsf{pair}_d(\Phi,\Psi)
\rightsquigarrow\Psi.
$$

These equations say more than pointwise product beta. At an object $k:K$,
pairing is the ordinary product pairing in the fibre. Over a base arrow
$p:k\to l$, its action is the pair of the two displayed actions over the
same $p$. Its canonical internalized cell at a fibre object $u$ is likewise
componentwise:

$$
\mathsf{cell}\bigl(\mathsf{pair}_d(\Phi,\Psi),p,u\bigr)
=
\bigl(
  \mathsf{cell}(\Phi,p,u),
  \mathsf{cell}(\Psi,p,u)
\bigr).
$$

Thus the elimination cuts remain valid while object action, base-arrow
action, and the selected next-cell observation stay internally functorial.
This is the structural calculus of independent siblings
$k:K,b:B[k],c:C[k]$; it does not exchange a variable with another whose
classifier depends on it.

<!-- evidence:CAT-FIBREWISE-CONTEXT -->

> **Formal status — checked.** Evidence `CAT-FIBREWISE-CONTEXT` covers the
> fixed-base displayed projections and pairing, both whole
> projection-after-pairing reductions, and their componentwise fibre,
> base-arrow, internalized-cell, and selected higher observations. The
> arbitrary-$K$ chosen-object-product interface of Examples 4 and 5 remains a
> separate mathematical development.

## 9.5 Universal Cuts

A universal property turns a family of maps into a chosen object together
with inverse ways of introducing and eliminating a factorization. Its
computation laws are higher-level cut elimination. Adjunction triangles are
the first example; representability, co-Yoneda, and weighted limits continue
the same line.

### 9.5.1 Example 6: The Two Adjunction Triangles

Let $F:R\to L$ be left adjoint to $G:L\to R$, with unit
$\eta:\mathrm{id}_R\Rightarrow GF$ and counit
$\varepsilon:FG\Rightarrow\mathrm{id}_L$.

For $g:X\to X'$ in $R$ and $f:FX'\to Y$ in $L$, the left triangle cut is

$$
\varepsilon[f]\circ F[\eta[g]]
\rightsquigarrow
f\circ F[g].
$$

Both sides have source $FX$ and target $Y$. The selected normal form removes
the adjacent unit-counit detour while preserving the ordinary functor action
$F[g]$.

Dually, for $f:X\to GY'$ in $R$ and $g:Y'\to Y$ in $L$, the right triangle
cut is

$$
G[\varepsilon[g]]\circ\eta[f]
\rightsquigarrow
G[g]\circ f.
$$

Both sides have source $X$ and target $GY$. The selected normal form again
removes the universal detour and retains the functorial image of the boundary
arrow.

The owners are not arbitrary transformations with the same types. They are
the stable unit and counit observations of the indexed `Adjunction` witness,
and both equations are runtime reductions. Their components use the
off-diagonal `tapp1` action, so action on higher cells in $f$ and $g$ remains
part of the surrounding functorial calculus.

<!-- evidence:ADJ-TRIANGLE-CUTS -->

> **Formal status — checked.** Evidence `ADJ-TRIANGLE-CUTS`.
> `unit_adj_transf` and `counit_adj_transf` are the selected observations
> that trigger the two reductions. Independently named unit-shaped and
> counit-shaped transfors do not acquire these computations by type alone.

### 9.5.2 Example 7: The Shaped Co-Yoneda Beta Cut

For a profunctor $P:A\rightsquigarrow B$, the right and left unit maps have
the forms

$$
P\otimes_B U_B\Longrightarrow P,
\qquad
U_A\otimes_A P\Longrightarrow P.
$$

If $p$ is a shaped element and $\mathrm{id}$ is the matching identity-shaped
hom element, their component cuts reduce as

$$
\varepsilon^R_P(p\otimes\mathrm{id})\rightsquigarrow p,
\qquad
\varepsilon^L_P(\mathrm{id}\otimes p)\rightsquigarrow p.
$$

The source is a shaped element of the corresponding tensor and the target is
the original shaped element of $P$. The normal form is $p$; the owners are the
two `Prof_coyoneda_*` transformations; and the equality mode is runtime
reduction on the selected shaped cells. Naturality-fusion remains available
for a profunctor map $P\to P'$, so this beta law is not merely a capped
set-level equation.

<!-- evidence:PROF-COYONEDA -->

> **Formal status — checked.** Evidence `PROF-COYONEDA`. Chapter 13 develops
> the representable and profunctor context required to read this calculation
> as the computational core of Yoneda.

### 9.5.3 Example 8: Weighted-Limit Beta And Eta

A computational weighted-limit witness is a comparison between the weighted
cone profunctor and the representable hom profunctor at the proposed limit.
After reindexing along a probe $M:I\to B$, it supplies operations

$$
\mathsf{push}(r):R\Longrightarrow\operatorname{Hom}(M,L),
\qquad
\mathsf{pull}(s):R\Longrightarrow\operatorname{Cone}_W(M,F).
$$

Their universal cuts reduce in both directions:

$$
\mathsf{pull}(\mathsf{push}(r))\rightsquigarrow r,
\qquad
\mathsf{push}(\mathsf{pull}(s))\rightsquigarrow s.
$$

The source and target are profunctor maps of the displayed kinds, and the
normal forms are the original maps $r$ and $s$. The generic owners are
`prof_comparison_push` and `prof_comparison_pull`; the weighted names
merely specialize their types. The equality mode is runtime beta/eta
reduction. The comparison can still be reindexed, symmetrized, and composed,
so the higher universal structure is retained instead of being collapsed to
a chosen set-level bijection.

<!-- evidence:PROF-COMPARISON-BETA-ETA -->

> **Formal status — checked.** Evidence
> `PROF-COMPARISON-BETA-ETA`. Chapter 16 turns this general comparison
> calculus into the weighted-limit interface.

### 9.5.4 Example 9: A Right Adjoint Preserves The Weighted Limit

Suppose $L_{\!a}:A\to B$ is left adjoint to $R_{\!a}:B\to A$, and a
comparison certifies $L:J'\to B$ as the $W$-weighted limit of $F:J\to B$.
Three universal cuts compose: move a cone across the adjunction, use the
given representation, and move the representing hom back. The output is a
comparison certifying $R_{\!a}L$ as the weighted limit of $R_{\!a}F$.

The source is the supplied weighted-limit comparison together with the
adjunction; the target is the transported comparison in $A$. The selected
normal form is the composite of the two adjunction-mate comparisons and the
reindexed limit comparison. Its owner is
`right_adjoint_preserves_weighted_limit_cov_comp`. This is a checked
construction, not a rewrite asserting that arbitrary limit syntax commutes
with every right adjoint. The resulting comparison retains its push/pull
beta-eta action on every probe and profunctor map.

<!-- evidence:WEIGHTED-LIMIT-PRESERVATION -->

> **Formal status — checked.** Evidence
> `WEIGHTED-LIMIT-PRESERVATION`. The theorem is developed in Chapter 16
> after weights, cones, and mate comparison have been introduced.

### 9.5.5 Example 10: The Weighted-Colimit Dual

A $W$-weighted colimit in $B$ is represented by the corresponding weighted
limit in $B^{\mathrm{op}}$. Applying the preceding theorem to the opposite
adjunction gives the dual statement: a left adjoint preserves the selected
weighted colimit.

The source is a weighted-colimit comparison and an adjunction; the target is
the transported comparison after the left adjoint. The selected normal form
is the opposite of the right-adjoint preservation composite, with double
opposites and reversed composition reduced by the generic duality owners. The
construction is checked under
`left_adjoint_preserves_weighted_colimit_con`. Its output is still a full
comparison with push/pull behavior after passing to opposites, not merely an
equality of chosen objects.

<!-- evidence:WEIGHTED-COLIMIT-PRESERVATION -->

> **Formal status — checked.** Evidence
> `WEIGHTED-COLIMIT-PRESERVATION`. Chapter 17 develops the variance and
> opposite-category calculation in full.

## 9.6 What Cut Elimination Preserves

The ten examples have a common shape:

$$
\text{introduction or action}
\quad+\quad
\text{matching elimination}
\quad\longrightarrow\quad
\text{one semantic owner}.
$$

Their normal forms are deliberately not all raw composites. Lower star keeps
postcomposition visible; upper star keeps precomposition visible; `tapp1`
keeps the varying arrow family visible; product projection keeps a structural
component visible; and a universal comparison keeps its inverse operations
visible. This is what makes the calculus iterable.

In particular, a capped equation is not the whole meaning of a construction.
The full `hom_postcomp_func`, `hom_precomp_along_func`, and
`tapp1_func` operations act on the next hom. Product projection has a full
hom-functor. Profunctor comparison can be reindexed and composed. A good
reduction removes the cut without discarding the object that
higher-dimensional consumers need.

## 9.7 Directed Family Transfors And Lax Comparison

Strict cut elimination should not be confused with strictness of every
directed comparison. Let $E,D:K\to\mathsf{Cat}$ be directed families and let

$$
\Phi:E\Longrightarrow D
$$

be a natural family morphism. At each $k:K$ it has a fibre functor
$\Phi_k:E[k]\to D[k]$. A transfor $\epsilon:\Phi\Rightarrow\Psi$ has a
fibrewise transfor and point components at objects of each fibre.

<!-- evidence:TRANSFD-FIBRE-COMPONENTS -->

> **Formal status — checked.** Evidence `TRANSFD-FIBRE-COMPONENTS`. The
> stable displayed presentations are `Transfd_cat` and `Transfd`;
> `Fibre_transf` and `Fibre_transf_app` expose their fibre and object
> projections.

When the base moves along $p:x\to y$, the two relevant transports do not have
to be equal. Starting with $u:E[x]$, the internal displayed hom action gives
a directed cell

$$
\chi^\Phi_{p,u}:
D[p](\Phi_xu)\longrightarrow\Phi_y(E[p]u)
$$

in $D[y]$. This is the displayed laxity cell. It has a direction and need not
be invertible. The generic functor and transfor cuts around it compute
strictly, but the comparison itself remains mathematical data.

<!-- evidence:FUNCTORD-DISPLAYED-LAXITY -->

> **Formal status — checked.** Evidence
> `FUNCTORD-DISPLAYED-LAXITY`. The endpoint functors are
> `functord_transport_lhs_func` and `functord_transport_rhs_func`; the
> active component is `fdapp1_int_cell`.

For a fibre arrow $\alpha:E[p](u)\to v$, the capped displayed action has the
readable form

$$
\Phi_y[\alpha]\circ\chi^\Phi_{p,u}:
D[p](\Phi_xu)\longrightarrow\Phi_yv.
$$

The direct internal-hom projection is the runtime owner. Expanding it into
this composite on every use would discard the stable higher action and give
the comparison a second owner.

## 9.8 Total Categories And The WalkingEnd Decoder

The family morphism induces a functor on total categories,

$$
\Sigma\Phi:\sum_{k:K}E[k]\longrightarrow\sum_{k:K}D[k].
$$

An arrow in the source has the form $(p,\alpha):(x,u)\to(y,v)$, where
$\alpha:E[p](u)\to v$. Its image is

$$
(p,\Phi^d[p,u,v,\alpha]).
$$

Thus the base arrow is retained and the fibre arrow is exactly the capped
displayed hom action. The laxity cell is the special case in which
$v=E[p](u)$ and $\alpha$ is the identity.

<!-- evidence:FUNCTORD-SIGMA-ACTION -->

> **Formal status — checked.** Evidence `FUNCTORD-SIGMA-ACTION`.
> `sigma_map_func` owns the total functor, whose arrow projection uses the
> capped internal displayed action rather than reconstructing a comparison
> composite.

For the contextual WalkingEnd decoder

$$
\mathsf{decode}^d:\mathsf{Code}\Longrightarrow\mathsf{Rep}_*,
$$

the generator comparison is the spiral. Evaluated at a base arrow $p:*\to x$
and zero, its endpoints reduce to

$$
p
\qquad\text{and}\qquad
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

The generic laxity component is therefore the directed normalization cell of
Chapter 8. Replacing it by a commuting equality at the outset would erase the
content of normalization. Equality is extracted only later, using
discreteness of the target hom-category.

## 9.9 The Packaging Boundary

The calculus now has a continuous line from local arrow composition to
weighted universal properties. Its discipline is equally important in the
negative direction.

- The arbitrary-$K$ product benchmark needs a general chosen-product
  interface. Its $\mathsf{Cat}$ instance still awaits one narrow packaged
  projection/composition comparison; neither gap justifies broad product eta.
- A displayed family morphism has the component-level laxity cell and its
  full internal projection ladder, but no duplicate whole-square facade.
- General ends, coends, and arbitrary Kan extensions require universal
  interfaces stronger than the selected profunctor operations.
- Runtime conversion, proof-time comparison, internal equality, and
  equivalence remain different judgments.

<!-- evidence:FUNCTORD-WHOLE-LAXITY -->

> **Formal status — research boundary.** Evidence
> `FUNCTORD-WHOLE-LAXITY`. A future whole-transfor comparison between
> $D[p]\circ\Phi_x$ and $\Phi_y\circ E[p]$ should be derived from the internal
> displayed action, project coherently through higher homs, and serve a
> concrete consumer. It must not duplicate the component semantics.

Cut elimination is therefore not a feature catalogue. It is the organizing
principle by which functorial type theory decides what should compute, what
should merely compare, and what higher structure must remain visible after a
calculation is complete.
<!-- /book-source:chapter-9 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-10 book/chapters/10-categories-precategories-and-categorical-identity.md -->
<a id="chapter-10"></a>

# 10. Categories, Precategories, And Categorical Identity

Chapter 2 introduced the categorical language needed for the WalkingEnd
calculation. We now return to the word *category* with a different question:
when should equality of objects agree with categorical sameness? The answer
depends on which categorical layer is under discussion. This second pass is a
spiral over Chapters 2, 4, and 7, not a replacement for their definitions.

The distinction is foundational. Ordinary univalent category theory begins
with set-valued homs and asks for an identity-to-isomorphism map to be an
equivalence. Emdash begins with iterated hom-categories, where arrows may have
directed higher arrows between them. The ordinary theory is therefore an
important specialization of functorial type theory, but it cannot serve as the
definition of the ambient native category.

## 10.1 A Translation Table, Not A Collapse

The following table fixes the translation used throughout the remainder of
the book.

| Layer | Characteristic data | Equality or height condition | Role here |
| --- | --- | --- | --- |
| Native `Cat` | objects and iterated `Hom_cat` classifiers | no set-valued-hom premise in the definition | ambient directed higher language |
| Equality-local `Path(A)` | elements of $A$ and identity evidence between them | every arrow is induced by equality | groupoidal specialization used for ordinary type theory |
| Finite `IsNCat` evidence, including `OneCat` | a native category plus a recursive hom-height witness | one-dimensionality makes each next hom discrete | bridge to ordinary category-shaped examples |
| HoTT precategory | a type of objects and set-valued homs | equality between parallel arrows is proposition-valued | ordinary 1-categorical specialization |
| HoTT category | a HoTT precategory for which object identity agrees with isomorphism | `idtoiso` is an equivalence | univalent 1-category notion, not the definition of native `Cat` |
| HoTT strict category | a HoTT precategory whose object type is a set | object identity is proposition-valued, without assuming `idtoiso` is an equivalence | a qualified truncation notion, unrelated to runtime strictness |

Three warnings belong beside the table.

First, *set-valued hom* means a truncation condition, not that a hom must be
presented by a classical set outside type theory. Second, *strict category* in
the HoTT sense refers to the truncation level of the object type; it says
nothing about which emdash expressions reduce at runtime. Third, a HoTT
strict category need not be a univalent category: object identity may be
proposition-valued while nontrivial isomorphisms remain. Finally, a `OneCat`
witness controls the height of a native category but does not by itself
identify object equality with isomorphism.

> **Formal status — mathematical development.** The table is a translation
> discipline, not an implemented equivalence of packages. A generic
> construction identifying native finite-height categories with HoTT
> precategories would have to choose the ordinary hom-set presentation and
> prove compatibility with native composition and object equality.

## 10.2 The Ordinary Precategory Specialization

An ordinary HoTT precategory $\mathcal A$ consists of:

- a type $\operatorname{Obj}(\mathcal A)$ of objects;
- for each $a,b$, a set $\operatorname{Hom}_{\mathcal A}(a,b)$;
- identity arrows $\mathrm{id}_a$;
- composition $g\circ f$, typed so that $f:a\to b$ and $g:b\to c$;
- left-unit, right-unit, and associativity equalities.

Because each hom is a set, equality between parallel arrows is a proposition.
The category laws therefore do not require an additional tower of coherence
data. This is precisely the simplifying hypothesis that ceases to be
available in a genuinely higher native category: there, the equality or cell
between two composites may itself have nontrivial higher structure.

The emdash specialization replaces an external record of hom sets by a native
category $C$ equipped with one-dimensional evidence. For every pair $x,y$,
the witness

$$
\operatorname{IsNCat}(1,C)
$$

makes the next hom-category
$\operatorname{Hom}_{C}(x,y)$ discrete. Its objects are the ordinary arrows;
the discreteness evidence controls their higher equality. The same witness
also implies the corresponding truncation bound on
$\operatorname{Obj}(C)$, but it still says nothing about whether every
ordinary isomorphism comes from object identity.

<!-- evidence:CAT-ITERATED-HOMS -->
<!-- evidence:CAT-DIMENSION -->

> **Formal status — checked.** Evidence `CAT-ITERATED-HOMS` and
> `CAT-DIMENSION`. Native `Cat` has category-valued homs, `IsNCat`
> recurses through those homs, and finite-dimensional evidence yields the
> predicted truncation evidence for the object classifier.

This gives a reliable rule of reading: use ordinary precategory reasoning
when the hom-height assumptions make it valid, but keep the native iterated
owner visible whenever a construction must act on the next cell.

## 10.3 Isomorphism And Identity-To-Isomorphism

For objects $a,b$ of an ordinary precategory, an isomorphism
$a\cong b$ consists of arrows

$$
f:a\longrightarrow b,
\qquad
g:b\longrightarrow a
$$

with $g\circ f=\mathrm{id}_a$ and
$f\circ g=\mathrm{id}_b$. Since the homs are sets, an inverse to a fixed
$f$ is unique when it exists. Consequently the type of isomorphism evidence
between two fixed objects is itself a set.

Object identity always produces an isomorphism. Given
$p:a=b$, identity induction defines

$$
\operatorname{idtoiso}_{\mathcal A}(p):a\cong b
$$

by sending reflexivity to the identity isomorphism. This map exists before
assuming univalence. The additional assertion that $\mathcal A$ is a
*category* in the HoTT sense is that

$$
\operatorname{idtoiso}_{\mathcal A}:
 (a=b)\longrightarrow(a\cong b)
$$

is an equivalence for every $a,b$.

<!-- evidence:UCAT-IDENTITY-ISOMORPHISM -->

> **Formal status — mathematical development.** Evidence
> `UCAT-IDENTITY-ISOMORPHISM`. This is the ordinary univalent
> 1-categorical theorem adapted from the HoTT category spine. It is not a
> theorem about every native `Cat`.

Univalence changes how one reasons about structure. A property or
construction invariant under isomorphism can be transported along object
identity because isomorphism and identity carry the same information. It
also implies that the object type of an ordinary category is a 1-type:
its identity types are equivalent to isomorphism types, and those are sets.

The effect on arrows is concrete. If $p:a=a'$, $q:b=b'$, and $f:a\to b$,
then transporting $f$ across both endpoint identities agrees with

$$
\operatorname{idtoiso}(q)
\circ f\circ
\operatorname{idtoiso}(p)^{-1}
:a'\longrightarrow b'.
$$

Thus endpoint transport is a lower-star cut at the target and an upper-star
cut at the source. This ordinary formula anticipates the represented-hom
actions used throughout the native calculus.

The implication should not be reversed carelessly. Having a 1-type of
objects does not make a precategory univalent, just as having discrete homs
does not force isomorphic objects to be equal.

## 10.4 Five Nearby Notions Of Sameness

The native theory places several useful notions next to one another. Their
proximity is a feature, but it is not an identification.

| Notion | Typical expression | What it compares |
| --- | --- | --- |
| object identity | $p:x=y$ in $\operatorname{Obj}(C)$ | two objects in the underlying equality layer |
| path-generated arrow | $\operatorname{path\_to\_hom}(p):x\to y$ | the directed arrow induced by object identity |
| ordinary isomorphism | $\operatorname{IsoEvidence}_C(x,y)$ | inverse arrows with equality-valued cancellation |
| carrier equivalence | $A\simeq B$ via `TypeEquiv` | two decoded groupoidal carriers |
| native omega-equivalence | $\operatorname{OmegaEquiv}_C(x,y)$ | a selected arrow with recursively usable inverse evidence |

There are checked maps between some adjacent entries. Object identity yields a
path-generated arrow and a transparent native omega-equivalence package.
Ordinary isomorphism evidence also yields native omega-equivalence evidence.
A `TypeEquiv`, however, compares carriers rather than two objects of an
arbitrary category, and it must not be substituted for categorical
equivalence without an explicit construction.

<!-- evidence:EQUIV-OMEGA -->
<!-- evidence:EQUIV-TYPE -->

> **Formal status — checked.** Evidence `EQUIV-OMEGA` and `EQUIV-TYPE`.
> The active interfaces expose object-path and carrier-equivalence
> constructions separately; neither declaration asserts a blanket
> identification of all five rows.

This ladder explains why the book qualifies the word *equivalence*. A theorem
about carrier equivalence, ordinary categorical equivalence, or recursive
omega-equivalence has different inputs and different higher consequences.

## 10.5 Equality-Local Categories

For a groupoidal classifier $A$, the native category

$$
\operatorname{Path}(A)
$$

has the elements of $A$ as objects and identity evidence $x=y$ as the hom
from $x$ to $y$. Reflexivity supplies identities, and ordinary functions act
functorially on paths. This is the native home of the familiar principle that
equality behaves like a groupoid.

<!-- evidence:CAT-PATH-CATEGORY -->

> **Formal status — checked.** Evidence `CAT-PATH-CATEGORY`.
> `Path_cat`, `Path_cat_func`, and `path_map_func` retain the
> equality-local category and its iterable functor action.

The ordinary and native readings coincide only under the appropriate height
condition. If $A$ is a 1-type, each identity type $x=y$ is a set, so
$\operatorname{Path}(A)$ can be read as an ordinary HoTT precategory. For a
general $A$, its identity types may have higher identity types, and the native
iterated-hom presentation retains them rather than truncating them away.

This example also separates groupoidality from directed categorical
univalence. Every arrow in $\operatorname{Path}(A)$ comes from identity by
construction. An arbitrary native category may contain noninvertible arrows,
and its identity layer cannot be recovered merely by declaring those arrows
to be paths.

## 10.6 Preorders, Posets, And Skeletal Reasoning

An ordinary preorder can be regarded as a precategory whose homs are mere
propositions: there is at most one arrow from $a$ to $b$. Isomorphism then
means $a\leq b$ and $b\leq a$. The preorder is a univalent category exactly
when this mutual reachability agrees with identity—the type-theoretic form of
antisymmetry. Thus posets are the proposition-valued-hom examples of the
general identity-to-isomorphism principle.

This example is useful because it exposes a frequent confusion. A skeletal
presentation says that isomorphic objects are literally or propositionally
the same in a chosen presentation. Univalence says that the canonical map
from identity to isomorphism is an equivalence, so the identification is
stable under dependent reasoning. The latter is an internal principle, not
merely a convention for selecting representatives.

The category of small sets is the other basic example. Its arrows are
functions, and its identity-to-isomorphism map is the restriction of the
identity-to-equivalence map for types. Universe univalence therefore makes it
a univalent category. Categories of groups, rings, and similar structures
follow when equivalence of carriers preserving the structure is shown to
agree with identity of the structured object. Chapter 15 develops that
structure-identity pattern.

> **Formal status — mathematical development.** The preorder/poset example is
> ordinary univalent 1-category theory, as are the category-of-sets and
> structured-object examples. The active code has proposition and set
> truncation evidence plus selected universe-univalence results, but no generic
> packaged preorder or structured-category construction is claimed here.

## 10.7 The Checked Ordinary-Isomorphism Lift

The active calculus supports one direction of the native comparison with no
finite-height premise. Given ordinary isomorphism evidence $i:x\cong y$, its
forward arrow and inverse laws define

$$
\operatorname{iso\_evidence\_omega\_equiv}(i):
\operatorname{OmegaEquiv}_C(x,y).
$$

The construction keeps the forward arrow selected by $i$ and packages its
inverse evidence in the recursive native facade. It is a structural lift, not
a decoder identifying isomorphism evidence with object identity.

<!-- evidence:EQUIV-ORDINARY-ISO-LIFT -->

> **Formal status — checked.** Evidence
> `EQUIV-ORDINARY-ISO-LIFT`. The owners are
> `iso_evidence_omega_along` and
> `iso_evidence_omega_equiv`; diagnostics check their projections and
> reflexive behavior.

This is the chapter's central checked theorem. It says that ordinary inverse
data is strong enough to enter the native equivalence calculus. It does not
say that native equivalence, ordinary isomorphism, and object identity are
interchangeable in every category.

## 10.8 The Native Univalence Boundary

A full categorical identity theorem for the ambient directed theory would
need to answer at least four questions.

1. Which equivalence classifier is compared with object identity?
2. Does the comparison retain a selected directed arrow?
3. How does it act on every next hom-category?
4. Under what height, saturation, or groupoidality hypotheses are the two
   directions inverse?

The active code has selected univalence theorems for groupoidal and truncated
universes, object-path-to-equivalence constructions, finite-height truncation,
and the one-way ordinary-isomorphism lift. It does not package a general
equivalence

$$
(x=y)\simeq\operatorname{IsoEvidence}_C(x,y)
$$

for arbitrary native $C$, nor a general saturation theorem that freely adds
such identities.

<!-- evidence:UNIV-FULL-OBJECT-ISO -->

> **Formal status — research boundary.** Evidence
> `UNIV-FULL-OBJECT-ISO`. A future owner must compare object identity and
> the selected categorical equivalence notion while remaining coherent with
> iterated hom action. Chapter 15 returns to this problem through the
> structure identity principle and Rezk-style saturation.

The title *univalent foundations* should therefore be read layer by layer.
Univalence is the disciplined alignment of identity with the appropriate
equivalence, not a license to erase the distinctions that make the directed
higher theory computational.
<!-- /book-source:chapter-10 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-11 book/chapters/11-functors-transfors-and-functor-categories.md -->
<a id="chapter-11"></a>

# 11. Functors, Transfors, And Functor Categories

Chapter 9 studied transfors as a calculus of cuts. We now make their
categorical organization explicit. Functors are objects of a functor
category, transfors are arrows between those objects, and higher transfors
are obtained by iterating the same hom construction.

This is another spiral rather than a repetition. Ordinary 1-category theory
starts from object functions, hom functions, and pointwise naturality
squares. The native calculus packages all of these as iterable categorical
action. A point component is the identity-boundary case of an off-diagonal
action, and a naturality square is the visible boundary of a computation.

## 11.1 Functors Act At Every Retained Dimension

For ordinary precategories $\mathcal A$ and $\mathcal B$, a functor
$F:\mathcal A\to\mathcal B$ consists of an object function and functions

$$
F_{a,b}:
\operatorname{Hom}_{\mathcal A}(a,b)
\longrightarrow
\operatorname{Hom}_{\mathcal B}(Fa,Fb)
$$

that preserve identities and composition. In the set-valued-hom
specialization, these are ordinary functions between hom sets.

A native emdash functor retains more structure. Its action on a pair of
objects is itself a functor

$$
F_{x,y}:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(Fx,Fy).
$$

Evaluating that functor at an arrow $f:x\to y$ gives $F[f]$. Keeping the full
hom functor visible also keeps its action on 2-cells between arrows, and then
on higher cells by iteration.

<!-- evidence:CAT-FUNCTOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-FUNCTOR-CALCULUS`.
> `fapp0` is object action, `fapp1_func` is the full next-hom action,
> and `fapp1_fapp0` is its value at one arrow. Identity and composition
> reductions belong to these generic owners.

The preservation law is oriented as cut elimination:

$$
F[g]\circ F[f]\rightsquigarrow F[g\circ f].
$$

This is not a theorem copied onto each constructor. It is computation of the
global functor-action interface. A specialized construction should expose its
own semantic projections, while ordinary functoriality remains owned here.

## 11.2 From Natural Transformations To Transfors

For ordinary functors $F,G:\mathcal A\to\mathcal B$, a natural transformation
$\eta:F\Rightarrow G$ is usually presented by arrows

$$
\eta_x:Fx\longrightarrow Gx
$$

such that every $f:x\to y$ satisfies

$$
G[f]\circ\eta_x=\eta_y\circ F[f].
$$

The native transfor retains the common interior of this square. For every
pair $x,y$ it supplies an off-diagonal functor

$$
\eta_{x,y}:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(Fx,Gy).
$$

We write $\eta[f]:Fx\to Gy$ for its value at $f$. The point component is
recovered at the identity:

$$
\eta[\mathrm{id}_x]\rightsquigarrow\eta_x.
$$

<!-- evidence:TRANSF-POINT-OFFDIAGONAL -->

> **Formal status — checked.** Evidence
> `TRANSF-POINT-OFFDIAGONAL`. The point projection is
> `tapp0_fapp0`; `tapp1_func` and `tapp1_fapp0` expose the full and
> capped off-diagonal actions.

This presentation does not add exotic data to an ordinary natural
transformation. In the one-dimensional specialization, naturality determines
the off-diagonal value in either familiar way:

$$
\eta[f]
=G[f]\circ\eta_x
=\eta_y\circ F[f].
$$

In the native higher setting, however, retaining $\eta_{x,y}$ as a functor
also retains its action on cells between possible $f$'s. Point components
alone would hide that action and force it to be reconstructed later.

## 11.3 Naturality Is A Pair Of Family Cuts

Take composable arrows

$$
h:w\to x,\qquad f:x\to y,\qquad g:y\to z.
$$

The two strict naturality computations are

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

Setting $f$ to an identity makes the usual naturality square reappear. Both
boundary composites normalize through the same off-diagonal interior
$\eta[f]$. Thus naturality is not merely a proposition verified after a
family of components has been assembled; it is the way the family action
absorbs neighboring cuts.

<!-- evidence:TRANSF-STRICT-NATURALITY -->

> **Formal status — checked.** Evidence
> `TRANSF-STRICT-NATURALITY`. Both capped equations and their uncapped
> hom-functor forms are runtime reductions of the global `tapp1*`
> calculus. The full forms retain action on the next cells.

This is the chapter's central checked theorem. It explains why the calculus
uses a transfor rather than a bare dependent function of point components:
the transfor is the computational natural family.

## 11.4 The Functor Category

For native categories $A$ and $B$, the category

$$
[A,B]:=\operatorname{Functor\_cat}(A,B)
$$

has functors $A\to B$ as objects. Its hom-category between $F$ and $G$ is

$$
\operatorname{Transf\_cat}(F,G).
$$

An identity arrow in $[A,B]$ is the identity transfor. Composition in
$[A,B]$ is vertical composition of transfors. Iterating the hom of
$\operatorname{Transf\_cat}(F,G)$ yields modifications and higher transfors
without changing the ambient notion of category.

<!-- evidence:CAT-TRANSFOR-CALCULUS -->

> **Formal status — checked.** Evidence `CAT-TRANSFOR-CALCULUS`.
> `Functor_cat` and `Transf_cat` are active native categories, and
> `Hom_cat(Functor_cat(A,B),F,G)` reduces to the corresponding transfor
> category.

In the ordinary set-valued-hom specialization, the same construction gives a
precategory of functors and natural transformations. Equality between natural
transformations is pointwise because the codomain homs are sets. A natural
transformation is a natural isomorphism exactly when each component is an
isomorphism.

The native formulation is intentionally stronger at the interface. It does
not force all higher transfor structure to be proposition-valued merely
because the first components resemble ordinary natural transformations.

## 11.5 Whiskering And Horizontal Composition

Functor composition acts on transfors in two one-sided ways. If
$\eta:F\Rightarrow G$ and $K:B\to C$, post-whiskering gives

$$
K\eta:KF\Rightarrow KG.
$$

If $H:X\to A$, pre-whiskering gives

$$
\eta H:FH\Rightarrow GH.
$$

These are the transfor-level actions of the same postcomposition and
precomposition functors studied in Chapter 9. They are not independent
definitions of naturality.

Now take

$$
\alpha:F\Rightarrow G:A\to B,
\qquad
\beta:H\Rightarrow K:B\to C.
$$

Their horizontal composite can be read at an object $a$ in either of the
ordinary forms

$$
\beta_{Ga}\circ H[\alpha_a],
\qquad
K[\alpha_a]\circ\beta_{Fa}.
$$

Naturality of $\beta$ identifies the two. The native calculus packages the
pair $(\alpha,\beta)$ under the product-composition action, so its
off-diagonal value first transports the $A$-arrow through $\alpha$ and then
through $\beta$. This gives a single iterable owner rather than two competing
component formulas.

<!-- evidence:TRANSF-HORIZONTAL-CALCULUS -->

> **Formal status — checked.** Evidence
> `TRANSF-HORIZONTAL-CALCULUS`. The generic owner is
> `comp_prod_fapp1_fapp0`; diagnostics check its point, full
> off-diagonal, and capped off-diagonal projections. The ordinary two-formula
> equality is its 1-categorical reading.

## 11.6 Interchange And Controlled Coherence

Vertical and horizontal composition satisfy interchange. Schematically, for
a composable four-cell grid,

$$
(\beta_2\circ\beta_1)\ast(\alpha_2\circ\alpha_1)
=
(\beta_2\ast\alpha_2)\circ(\beta_1\ast\alpha_1).
$$

In an ordinary functor precategory this is an equality of natural
transformations, proved componentwise using associativity and naturality. In
the native calculus, the corresponding computation is organized by the
generic product-composition action and the off-diagonal vertical-composite
folds. A representable four-cell instance is exposed as propositional
interchange evidence.

The equality mode matters. Functor composition has associativity and unit
comparisons, and ordinary category theory packages their familiar pentagon
and triangle coherences. Emdash does not install unrestricted reassociation
in both directions as runtime computation. Instead:

- a semantic owner absorbs a neighboring cut when it has a selected normal
  form;
- proof-time comparison is used when two presentations should elaborate
  together but neither should replace the other globally;
- propositional equality records a theorem without changing runtime normal
  forms;
- higher transfors retain coherence data that is not truncated away.

This is the categorical version of controlling associativity. Parentheses may
be suppressed in mathematical prose when the intended composite is
unambiguous, but the formal presentation must still select an owner and an
equality mode.

## 11.7 The Ordinary Functor-Category Theorem

Let $\mathcal A$ be an ordinary precategory and $\mathcal B$ an ordinary
univalent category. Then the functor precategory
$[\mathcal A,\mathcal B]$ is a univalent category. The reason is
pointwise but not merely syntactic:

1. an identity $F=G$ gives a natural isomorphism by identity induction;
2. a natural isomorphism gives pointwise isomorphisms $Fx\cong Gx$;
3. univalence of $\mathcal B$ turns those into pointwise identities;
4. function extensionality assembles equality of object functions;
5. the functor laws and naturality data are propositions at this height, so
   the assembled equality determines the whole functor.

The same analysis shows that identity between ordinary functors agrees with
natural isomorphism.

<!-- evidence:UCAT-FUNCTOR-CATEGORY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-FUNCTOR-CATEGORY`. This is the HoTT 1-categorical theorem under
> set-valued-hom and univalent-codomain hypotheses. The active native
> `Functor_cat` supplies the categorical object, but this general
> identity-to-natural-isomorphism equivalence is not a checked emdash theorem.

## 11.8 The Native Functor-Category Boundary

A native analogue cannot be obtained by deleting the word *set* from the
ordinary proof. One must choose the relevant sameness of functors—object
identity, ordinary isomorphism in `Functor_cat`, pointwise native
omega-equivalence, or a higher adjoint equivalence—and then prove that the
comparison respects:

- point components;
- off-diagonal arrow action;
- cells between source arrows;
- vertical and horizontal composition;
- every further retained hom level.

Pointwise object formulas are therefore necessary but insufficient. The
active code has the functor category, the full transfor calculus, and selected
object-path and ordinary-isomorphism lifts. It does not yet combine them into
a general univalence theorem for native functor categories.

> **Formal status — research boundary.** The missing owner is a native
> category-univalence package stable under `Functor_cat` and coherent with
> `tapp1_func` at every retained dimension. Chapter 15 discusses the
> saturation problem that such a theorem would have to solve.

The computational lesson survives independently of that boundary. Functors
and transfors already form a native higher category, and their naturality is
already internal computation. Univalence would identify the right notion of
sameness in this existing structure.
<!-- /book-source:chapter-11 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-12 book/chapters/12-adjunctions-and-equivalences.md -->
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
<!-- /book-source:chapter-12 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-13 book/chapters/13-yoneda-representability-and-profunctors.md -->
<a id="chapter-13"></a>

# 13. Yoneda, Representability, And Profunctors

Representability turns the arrows out of, or into, one object into a universal
coordinate system. Yoneda says that a natural map out of such a coordinate
system is determined by its value at an identity. Adjunction says that one
hom coordinate system is represented by another object. Weighted limits will
repeat the same argument for a more elaborate functor.

The ordinary Yoneda lemma is therefore the conceptual center of this part of
the book. We first develop its univalent 1-categorical form, then identify the
native representable families already used by arrow induction, and finally
pass to Cat-valued profunctors. The chapter's central *checked* computation is
a shaped co-Yoneda cut: tensor an element with the appropriate identity-shaped
hom, apply the co-Yoneda map, and recover the original element.

The full ordinary Yoneda lemma below is mathematical development adapted from
the [HoTT Book](#ref-hott-book). The active artifact checks native
representables and the shaped Cat-valued co-Yoneda beta/fusion equations. It
does not yet package a general Cat-valued Yoneda equivalence or a semantic
coend. [Kelly](#ref-kelly) supplies enriched background for these patterns,
while [Bénabou](#ref-benabou) is a classical reference for their bicategorical
organization.

## 13.1 Representables And Variance

Let $\mathcal A$ be an ordinary precategory. A presheaf is a functor

$$
P:\mathcal A^{\mathrm{op}}\longrightarrow\mathsf{Set}.
$$

For $a:\mathcal A$, the contravariant representable presheaf is

$$
y(a):=\operatorname{Hom}_{\mathcal A}(-,a).
$$

An arrow $u:a\to b$ induces a natural transformation
$y(u):y(a)\Rightarrow y(b)$ by postcomposition:

$$
y(u)_x(f)=u\circ f=u_*(f).
$$

This defines the Yoneda embedding

$$
y:\mathcal A\longrightarrow
[\mathcal A^{\mathrm{op}},\mathsf{Set}].
$$

There is a covariant mirror

$$
y^{a}:=\operatorname{Hom}_{\mathcal A}(a,-):
\mathcal A\longrightarrow\mathsf{Set}.
$$

It is contravariant in the represented object $a$: an arrow $u:a\to b$
induces precomposition

$$
u^*:\operatorname{Hom}_{\mathcal A}(b,-)
\Longrightarrow
\operatorname{Hom}_{\mathcal A}(a,-).
$$

The lower-star and upper-star actions from Chapter 9 are therefore the two
variance legs of representability.

## 13.2 The Ordinary Yoneda Equivalence

For a presheaf $P:\mathcal A^{\mathrm{op}}\to\mathsf{Set}$, the Yoneda
equivalence is

$$
\operatorname{Nat}(y(a),P)\simeq P(a).
$$

Its forward map evaluates a natural transformation at the identity:

$$
\operatorname{encode}(\alpha)
:=\alpha_a(\mathrm{id}_a).
$$

For $p:P(a)$, the reverse map defines a natural transformation by

$$
\operatorname{decode}(p)_x(f)
:=P[f](p),
\qquad
f:x\to a.
$$

The first composite is immediate from preservation of identity:

$$
\operatorname{encode}(\operatorname{decode}(p))
=P[\mathrm{id}_a](p)
=p.
$$

For the other composite, naturality of $\alpha$ at $f:x\to a$ gives

$$
P[f]\bigl(\alpha_a(\mathrm{id}_a)\bigr)
=\alpha_x(f).
$$

Thus
$\operatorname{decode}(\operatorname{encode}(\alpha))=\alpha$ by
extensionality. The proof has the same shape as Chapter 8: choose a code by
evaluation, decode it by functorial transport, and calculate both composites.
Here the distinguished constructor is the identity arrow of a representable.

The covariant form is equally important. For
$Q:\mathcal A\to\mathsf{Set}$,

$$
\operatorname{Nat}
  \bigl(\operatorname{Hom}_{\mathcal A}(a,-),Q\bigr)
\simeq Q(a),
$$

and the inverse sends $q:Q(a)$ to the family
$f:a\to x\mapsto Q[f](q)$.

<!-- evidence:UCAT-YONEDA -->

> **Formal status — mathematical development.** Evidence
> `UCAT-YONEDA`. These are the ordinary set-valued Yoneda equivalences.
> They are stated under the HoTT precategory assumptions and are not labeled
> as the active full Cat-valued theorem.

## 13.3 Full Faithfulness And Uniqueness Of Representation

Apply Yoneda with $P=y(b)$. One obtains

$$
\operatorname{Nat}(y(a),y(b))
\simeq
\operatorname{Hom}_{\mathcal A}(a,b).
$$

Under this equivalence, an arrow $u:a\to b$ corresponds to
postcomposition by $u$. Hence the Yoneda embedding is fully faithful: it
recovers every hom from the natural maps between representables.

More generally, a representation of $P$ consists of an object $a$ and a
natural isomorphism $y(a)\cong P$. If $a$ and $b$ both represent $P$, full
faithfulness produces a canonical isomorphism $a\cong b$. When
$\mathcal A$ is a univalent category, this isomorphism corresponds to object
identity, and representability becomes a property rather than an uncontrolled
choice of presentation.

> **Formal status — mathematical development.** This full-faithfulness and
> uniqueness result is part of evidence `UCAT-YONEDA`. The conclusion uses
> ordinary category univalence exactly where an isomorphism of representing
> objects is turned into identity.

## 13.4 Native Representable Families

For a native category $Z$ and an object $x$, emdash has the Cat-valued
fixed-source representable

$$
\operatorname{Rep}_Z(x)[y]
:=\operatorname{Hom}_Z(x,y).
$$

Its target action is postcomposition. Its dependence on the represented
source is contravariant: for $p:x\to y$, the transport

$$
\operatorname{Rep}_Z(y)\longrightarrow\operatorname{Rep}_Z(x)
$$

acts by

$$
q\longmapsto q\circ p=p^*(q).
$$

The full operation is a functor between directed families, so it retains
action on cells between possible $q$'s.

<!-- evidence:CAT-REPRESENTABLE -->

> **Formal status — checked.** Evidence `CAT-REPRESENTABLE`.
> `Rep_catd` owns the fixed-source family and
> `Rep_transport_func` owns its upper-star source action.

The outgoing-arrow category from Chapter 5 is the total category

$$
\operatorname{PathOut}_Z(x)
=\sum_{y:Z}\operatorname{Hom}_Z(x,y).
$$

Its distinguished object $(x,\mathrm{id}_x)$ and its canonical arrow to every
$(y,p)$ are built from the representable family. Arrow induction extends data
from that reflexive outgoing arrow.

This is Yoneda-shaped, but it is not literally the ordinary Yoneda lemma.
Yoneda classifies natural transformations from a representable; the selected
arrow-induction theorem eliminates a dependent motive over the total category
of outgoing arrows. Both begin at an identity arrow because identities are
the universal points of representables.

## 13.5 From One Endpoint To Two

Opposites and products make the two variances explicit. In the ordinary
1-categorical setting, currying and uncurrying compare functors

$$
\mathcal A\times\mathcal B\longrightarrow\mathcal C
$$

with functors

$$
\mathcal A\longrightarrow[\mathcal B,\mathcal C].
$$

Applying this organization to composition shows that hom is functorial in
both endpoints, contravariantly in its source and covariantly in its target.

The two representable variances combine in the hom bifunctor

$$
\operatorname{Hom}_{X}(-,-):
X^{\mathrm{op}}\times X\longrightarrow\mathsf{Cat}.
$$

Reindexing its two endpoints along functors $F:A\to X$ and $G:B\to X$
gives

$$
\operatorname{Hom}_{X}(F{-},G{-}):
A^{\mathrm{op}}\times B\longrightarrow\mathsf{Cat}.
$$

This two-variable view is the bridge from Yoneda to profunctors. It makes
contravariance and covariance simultaneous, lets endpoint functors vary, and
turns hom transposition for an adjunction into a comparison of profunctors.

The price of the richer codomain is that ordinary elementwise proofs no longer
automatically supply all higher naturality. The active development therefore
selects shaped elements and explicit comparison maps before claiming a
general coend-based composition.

## 13.6 Cat-Valued Profunctors

For categories `A` and `B`, a Cat-valued profunctor from `A`
to `B` is a functorial family

$$
P:A^{\mathrm{op}}\times B\longrightarrow\mathsf{Cat}.
$$

We write `P:A prof B` informally and write its fibre at `(a,b)`
as `P(a,b)`. The opposite on `A` records the variance:

- an arrow $p:a'\to a$ acts contravariantly in the first endpoint;
- an arrow $q:b\to b'$ acts covariantly in the second endpoint.

Profunctors with fixed endpoints form a category. A vertical map

$$
r:P\Longrightarrow Q
$$

is a natural family morphism over `A^op times B`. Its identity,
vertical composition, components, and higher action are inherited from the
directed-family and transfor calculus of Chapters 2 and 9.

<!-- evidence:PROF-CATEGORY -->

> **Formal status — checked.** Evidence `PROF-CATEGORY`.
> `Prof_base(A,B)=A^op times B`; `Prof_cat` is the fixed-endpoint
> category and `ProfMap` its vertical-map classifier.

This definition introduces no new primitive notion of naturality. A
profunctor is a familiar Cat-valued functor on a product base, viewed through
notation that makes its two variances visible.

## 13.7 The Unit Hom Profunctor

Every category `X` has a canonical profunctor

$$
U_X:X^{\mathrm{op}}\times X\longrightarrow\mathsf{Cat},
\qquad
U_X(x,y):=\operatorname{Hom}_X(x,y).
$$

On an arrow pair

$$
p:x'\to x,
\qquad
q:y\to y',
$$

it acts by cutting on both sides:

$$
h\longmapsto q\circ h\circ p.
$$

The opposite variance is not decorative: it is exactly what makes the first
composition type-correct. Identity and composite action follow from the
generic hom bifunctor.

More generally, given functors

$$
F:A\longrightarrow X,
\qquad
G:B\longrightarrow X,
$$

reindex the unit to obtain the binary representable

$$
\operatorname{Hom}_X(F{-},G{-}):A\rightsquigarrow B
$$

with fibres

$$
\operatorname{Hom}_X(Fa,Gb)
$$

and action

$$
h\longmapsto G(q)\circ h\circ F(p).
$$

<!-- evidence:PROF-REPRESENTABLE -->

> **Formal status — checked.** Evidence `PROF-REPRESENTABLE`.
> `Unit_prof` owns the hom profunctor, and `Hom_prof_along(F,G)` is
> its endpoint-reindexed presentation with the two-sided `Hom_fapp0`
> action.

Two specializations are useful. The **companion** of
$F:A\to B$ is represented covariantly by `F`; the **conjoint** is
represented contravariantly by `F`. These are not assumed to be inverse
profunctors. They are the two variance choices obtained from the same ambient
hom.

## 13.8 Reindexing Endpoints

Let `P:A prof B`, $F:A'\to A$, and $G:B'\to B$.
Endpoint reindexing is

$$
(F,G)^*P:A'\rightsquigarrow B',
\qquad
((F,G)^*P)(a',b'):=P(Fa',Gb').
$$

Semantically this is pullback along

$$
F^{\mathrm{op}}\times G:
(A')^{\mathrm{op}}\times B'
\longrightarrow
A^{\mathrm{op}}\times B.
$$

The operation acts on vertical maps, is neutral at identity endpoint
functors, and accumulates nested reindexings by composing both endpoints. For
representables, it gives the expected equation

$$
(F',G')^*\operatorname{Hom}_X(F{-},G{-})
=
\operatorname{Hom}_X((F\circ F'){-},(G\circ G'){-}).
$$

<!-- evidence:PROF-REINDEXING -->

> **Formal status — checked.** Evidence `PROF-REINDEXING`.
> `Prof_reindex` is the stable object owner and
> `Prof_reindex_func` provides its vertical functorial action.

The separation between a profunctor and its reindexed view is analogous to the
separation between WalkingEnd and `BNat`. A readable model or pullback
presentation does not become a definitional replacement for the object it
explains.

## 13.9 Representability As A Chosen Comparison

A profunctor `P:B prof J` is right-represented by a functor
$L:J\to B$ when it is isomorphic, in the fixed-endpoint profunctor
category, to the conjoint of `L`:

$$
P\cong\operatorname{Hom}_B(-,L{-}).
$$

A representation package retains both the chosen functor and its
isomorphism evidence:

$$
\sum_{L:J\to B}
\mathsf{IsoEvidence}
  \bigl(P,\operatorname{Hom}_B(-,L{-})\bigr).
$$

<!-- evidence:PROF-REPRESENTATION-PACKAGE -->

> **Formal status — checked.** Evidence
> `PROF-REPRESENTATION-PACKAGE`. The classifiers are
> `IsRepresentedBy_iso` and `Representation_iso`; the current
> comparison is ordinary isomorphism evidence in `Prof_cat`.

This is a useful universal-property interface even before uniqueness of the
representing object is packaged. A weighted limit, for example, can be
presented as a chosen representation of a cone profunctor. The computational
strength of that use depends on how much of the comparison is exposed by the
consumer.

## 13.10 Cells With Moving Endpoints

Vertical maps keep endpoints fixed. Equipment-style cells allow endpoint
functors to move as well. Given

$$
R':A'\rightsquigarrow B',
\quad
R:A\rightsquigarrow B,
\quad
F:A'\to A,
\quad
G:B'\to B,
$$

a cell over `F,G` is a natural family morphism

$$
c:R'\Longrightarrow(F,G)^*R.
$$

If the source profunctor is the unit `U_I`, such a cell is a shaped
element of `R` with endpoint functors $I\to A$ and $I\to B$.
The narrow application operation sends a shaped element of `R'` through
`c` to the corresponding shaped element of `R`.

<!-- evidence:PROF-SHAPED-CELLS -->

> **Formal status — checked.** Evidence `PROF-SHAPED-CELLS`.
> `Prof_transf_cat` is the endpoint-changing cell category,
> `Prof_hom` is its unit-source specialization, and
> `Prof_cell_apply` is the selected application operation.

The operation is intentionally narrower than arbitrary horizontal
composition of equipment cells. It supplies the consumer needed by the
co-Yoneda calculation without pretending that all bicategorical coherence is
already present.

## 13.11 Tensor As A Selected Composite

For

$$
P:A\rightsquigarrow B,
\qquad
Q:B\rightsquigarrow X,
$$

write

$$
P\otimes_B Q:A\rightsquigarrow X
$$

for their selected profunctor tensor. In ordinary enriched category theory
one expects a coend-like formula

$$
(P\otimes_B Q)(a,x)
\simeq
\int^{b:B}P(a,b)\times Q(b,x).
$$

This formula is the intended mathematical reading, not a definition unfolded
by the active kernel. `Prof_tensor` is opaque. What is exposed is the
behavior required by current consumers:

- reindexing in the outer endpoints distributes through the tensor;
- the middle category stays fixed;
- vertical maps in both factors induce a vertical map of tensors;
- compatible shaped elements compose to a shaped tensor element.

<!-- evidence:PROF-TENSOR -->

> **Formal status — checked.** Evidence `PROF-TENSOR`. The fixed-middle
> object is `Prof_tensor`; `Prof_tensor_func` owns fixed-endpoint
> bifunctoriality and `Prof_tensor_hom_hom` composes shaped elements.

Opacity is mathematically honest here. A genuine coend construction would
need a quotient or universal colimit with its own eliminator and computation
rules. The selected tensor can support tested cut-elimination interfaces
without serving as evidence that this general construction has already been
built.

## 13.12 The Shaped Co-Yoneda Cut

The unit profunctor should behave as a unit for tensor. The active interface
supplies natural maps in both orientations:

$$
\begin{aligned}
\varepsilon^R_P &: P\otimes_B U_B\Longrightarrow P,\\
\varepsilon^L_P &: U_A\otimes_A P\Longrightarrow P.
\end{aligned}
$$

They are components of transformations natural in `P`, rather than a
collection of unrelated vertical maps.

Now let `p` be a shaped element of `P` with middle shape
$M:I\to B$. The unit profunctor has a canonical shaped element given by
the identity transformation on `M`. Tensor the two elements and apply the
right co-Yoneda map. The cut eliminates:

$$
\varepsilon^R_P
  \bigl(p\otimes\mathrm{id}_M\bigr)
=p.
$$

Dually, for an `A`-shaped endpoint `F`,

$$
\varepsilon^L_P
  \bigl(\mathrm{id}_F\otimes p\bigr)
=p.
$$

<!-- evidence:PROF-COYONEDA -->

> **Formal status — checked.** Evidence `PROF-COYONEDA`.
> `Prof_coyoneda_cov_transf` and
> `Prof_coyoneda_con_transf` are the two natural transformations;
> their component maps have the shaped-element beta equations above.

These equations are the chapter's central theorem. They express Yoneda-style
evaluation as computation: insert an identity-shaped hom, form the composite,
and the co-Yoneda counit removes the cut.

The transformations also fuse with an arbitrary vertical map
$r:P\to P'$. Applying the naturality component of co-Yoneda to
$p\otimes\mathrm{id}$ reduces to applying `r` directly to `p`:

$$
\varepsilon_{P'}
  \bigl((r\otimes\mathrm{id})(p\otimes\mathrm{id})\bigr)
=r(p),
$$

with the analogous left-unit equation. This is not a separate law attached to
every `r`; it is the off-diagonal action of the co-Yoneda transfor from
Chapter 9.

## 13.13 Adjunctions As Representable Hom Comparisons

Chapter 12 characterized a right adjoint $G:B\to A$ to $F:A\to B$ by
representations

$$
\operatorname{Hom}_B(F{-},b)
\simeq
\operatorname{Hom}_A({-},Gb).
$$

Yoneda explains both the representing object and its uniqueness. The
profunctor formulation adds simultaneous naturality in the source probe and
in $b$. For arbitrary $M:I\to A$ and $H:K\to B$, the active comparison is

$$
\operatorname{Hom}_B(FM,H)
\simeq
\operatorname{Hom}_A(M,GH).
$$

<!-- evidence:ADJ-HOM-PROF-COMPARISON -->

> **Formal status — checked.** Evidence
> `ADJ-HOM-PROF-COMPARISON`. The adjunction supplies this reindexable
> `ProfComparison`; its push and pull operations have the generic
> comparison beta/eta laws.

Conversely, an ordinary pointwise family of such representations reconstructs
a right adjoint only after the representing objects and comparisons have been
made coherent in $b$. The active representation package records a chosen
representing functor and ordinary isomorphism evidence in the profunctor
category, but no general reverse constructor from that package to
`Adjunction` is asserted.

<!-- evidence:UCAT-ADJOINT-REPRESENTABILITY -->

> **Formal status — mathematical development.** The ordinary reverse
> representability theorem is part of
> `UCAT-ADJOINT-REPRESENTABILITY`. Evidence
> `PROF-REPRESENTATION-PACKAGE`, checked in Section 13.9, supplies the
> native chosen representation interface on which a future reverse
> construction could be based.

This is the bridge to weighted universals. A weighted cone construction will
produce another profunctor; a weighted limit is the functor that represents
it. The same comparison beta/eta laws will eliminate the corresponding
universal cuts.

## 13.14 The Full Cat-Valued Yoneda Boundary

The computations capture an essential Yoneda idea: represented hom data can
be inserted as an identity-shaped cut and then eliminated. The existing
right-representable embedding, endpoint reindexing, shaped cells, and
co-Yoneda maps give a credible computational core for a broader theorem.

A full Cat-valued Yoneda theorem would package more. One expects a functor
from `A` into an appropriate presheaf or profunctor category, a precise
mapping-category equivalence, naturality in the represented object and the
presheaf, and a proof that the embedding is fully faithful at every retained
cell level. Those data have not been gathered into one active theorem.

<!-- evidence:YONEDA-FULLY-FAITHFUL -->

> **Formal status — research boundary.** Evidence
> `YONEDA-FULLY-FAITHFUL`. The intended future owner should be built
> from the existing representable functor, shaped-cell, and co-Yoneda
> interfaces and should expose a reusable equivalence rather than add isolated
> projection rules.

The checked beta equations remain valuable without that package. They are
local computational theorems, not merely motivational analogies.

## 13.15 The Coend And Bicategorical Boundary

To promote the tensor to a general profunctor composition, one would need:

- a coend or coinserter construction for Cat-valued data;
- its dinatural elimination and computation principles;
- associativity and left/right unit comparisons;
- coherent higher cells for those comparisons;
- horizontal composition of arbitrary endpoint-changing cells;
- compatibility with opposites, reindexing, and internal homs.

Only selected parts of this list are active. Fixed-endpoint tensor action,
outer reindexing, shaped composition, and both co-Yoneda counits have checked
owners. They do not automatically assemble into a bicategory.

<!-- evidence:PROF-GENERAL-COEND -->

> **Formal status — research boundary.** Evidence
> `PROF-GENERAL-COEND`. A future implementation should give the opaque
> tensor a universal semantics or relate it to a separately constructed
> coend; it should not infer general coherence from the current endpoint beta
> rules alone.

This staged boundary mirrors the rest of the book. We expose enough
functorial structure to compute a central example, retain the higher action
that example consumes, and state the missing universal package explicitly.
<!-- /book-source:chapter-13 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-14 book/chapters/14-strictness-dagger-and-duality.md -->
<a id="chapter-14"></a>

# 14. Strictness, Dagger Structure, And Duality

The word *strict* enters category theory by several doors. A HoTT strict
category has a set of objects. An emdash naturality cut is strict when it
selects a runtime normal form. A rewrite is strict in yet another sense when
it is judgmental computation rather than internal equality. None of these
conditions implies either of the others.

The neighboring notion of a dagger illustrates why this vocabulary matters.
A dagger is a *chosen* reversal internal to one category, whereas the
opposite construction reverses any category from the outside. The distinction
is the same one that has guided the book throughout: a generic operation, a
selected structure, and a computational presentation have different owners.

This chapter adapts the strict- and dagger-category discussions of the
[HoTT Book](#ref-hott-book) to the ordinary 1-categorical specialization,
then states the additional coherence a native directed version would need.
Its central checked theorem is opposite duality. The dagger theory is
mathematical development with an explicit implementation boundary.

## 14.1 A Qualified Strictness Vocabulary

The following terms remain separate throughout the book.

| Qualified notion | Meaning | Does not imply |
| --- | --- | --- |
| HoTT strict category | an ordinary precategory whose object type is a set | category univalence |
| HoTT category | an ordinary precategory for which `idtoiso` is an equivalence | that the object type is a set |
| gaunt category | a HoTT category that is also strict | runtime strictness |
| native `IsNCat(n,C)` | recursive finite height of the hom-categories | object identity agrees with isomorphism |
| strict naturality cut | a selected `tapp1` composite reduces to one off-diagonal action | all coherence is judgmental |
| runtime strictness | an oriented kernel reduction chooses a normal form | object truncation or invertibility |
| dagger category | identity agrees with *unitary* isomorphism | identity agrees with every isomorphism |

In particular, the HoTT phrase *strict category* begins with a
**precategory**, not with a univalent category. Chapter 10’s translation table
uses this definition. A strict precategory may still have nontrivial
automorphisms that cannot come from its proposition-valued object identity.

## 14.2 Strict Categories In Ordinary Univalent Foundations

Let $\mathcal A$ be an ordinary precategory. It is *strict* when
$\operatorname{Obj}(\mathcal A)$ is a set:

$$
\prod_{x,y:\operatorname{Obj}(\mathcal A)}
\operatorname{isProp}(x=y).
$$

This condition says that two proofs of equality between objects agree. It
does not say that every isomorphism comes from equality. For example, the
one-object category associated to a nontrivial group is strict: its object
type is the unit type. It is not a HoTT category, since its nonidentity group
elements are automorphisms while the unique object has only the reflexive
identity path.

A poset on a set-valued carrier gives the contrasting example. Its homs are
propositions and antisymmetry identifies mutual reachability with object
identity, so it is both strict and univalent. More generally, a HoTT category
is strict exactly when it is *gaunt*: its isomorphisms contain no additional
object sameness beyond proposition-valued identity.

Strict categories therefore support a stricter package-level notion of
sameness than categorical equivalence. Equality of their presentations agrees
with isomorphism of the corresponding precategory structures, whereas an
equivalence can still change a presentation by choosing merely equivalent
objects. This can be useful, but it is not the default notion of sameness in
univalent category theory.

<!-- evidence:UCAT-STRICT-CATEGORY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-STRICT-CATEGORY`. The definition and the gauntness comparison belong
> to ordinary univalent 1-category theory. They are not a definition of
> native `Cat` or a theorem about arbitrary finite-dimensional native
> categories.

## 14.3 Three Native Notions That Strict Categories Do Not Control

Finite directed height is the first separate notion. A witness

$$
\operatorname{IsNCat}(n,C)
$$

recurses through native hom-categories. At dimension one it says that every
hom-category is discrete and entails that the object classifier is a
1-type. HoTT strictness instead asks directly that the object classifier be a
set. Neither condition supplies a native identity-to-isomorphism theorem.

The second notion is strict naturality. For an ordinary transfor
$\eta:F\Rightarrow G$, the generic off-diagonal action has the two reductions

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

The phrase *strict transfor* in this book describes this selected two-sided
cut behavior; it is not a new classifier of categories. A displayed lax
comparison can instead retain a directed naturality cell without forcing it
to equality.

The third notion is runtime strictness itself. The arrow
$t\rightsquigarrow u$ records a chosen normal form in the Lambdapi theory.
An internal equality $t=u$, a proof-time comparison, and a free-form
mathematical equation have different force. A category can have
proposition-valued object identity while none of its interesting operations
compute, or support rich directed higher cells while selected naturality cuts
do compute.

<!-- evidence:CAT-DIMENSION -->
<!-- evidence:TRANSF-STRICT-NATURALITY -->

> **Formal status — checked.** Evidence `CAT-DIMENSION` and
> `TRANSF-STRICT-NATURALITY`. The active theory separately checks recursive
> dimension/object truncation and the two ordinary `tapp1` naturality
> reductions. No checked theorem identifies these interfaces.

## 14.4 Opposite Duality Computes

For every native category $C$, the opposite category has the same objects and
reversed homs:

$$
\operatorname{Hom}_{C^{\mathrm{op}}}(x,y)
=\operatorname{Hom}_{C}(y,x).
$$

Identity arrows are unchanged, while the factors of composition reverse.
The active operation is involutive not only on categories but through the
iterable functor and transfor layers:

$$
\begin{aligned}
(C^{\mathrm{op}})^{\mathrm{op}}&\rightsquigarrow C,\\
(F^{\mathrm{op}})^{\mathrm{op}}&\rightsquigarrow F,\\
(\alpha^{\mathrm{op}})^{\mathrm{op}}&\rightsquigarrow\alpha.
\end{aligned}
$$

Opposite reverses vertical composition of transfors. It also turns an
adjunction

$$
F\dashv G
$$

into

$$
G^{\mathrm{op}}\dashv F^{\mathrm{op}}.
$$

The new unit is the opposite of the old counit, and the new counit is the
opposite of the old unit. Applying opposite twice reduces to the original
adjunction package. This is a computational duality, not a silent convention
that suppresses variance.

<!-- evidence:OP-DUALITY -->

> **Formal status — checked.** Evidence `OP-DUALITY`. The principal owners
> are `Op_cat`, `Op_func`, `Op_transf`, and `Op_adjunction`. Their
> involution and variance-reversal rules are the checked basis for the
> weighted-colimit duality in Chapter 17.

## 14.5 Dagger Structure Is Chosen Self-Duality

An ordinary †-precategory is a precategory $\mathcal A$ equipped with an
operation

$$
(-)^\dagger:
\operatorname{Hom}_{\mathcal A}(x,y)
\longrightarrow
\operatorname{Hom}_{\mathcal A}(y,x)
$$

satisfying

$$
\begin{aligned}
(\mathrm{id}_x)^\dagger&=\mathrm{id}_x,\\
(g\circ f)^\dagger&=f^\dagger\circ g^\dagger,\\
(f^\dagger)^\dagger&=f.
\end{aligned}
$$

Equivalently, it is an identity-on-objects functor-like map

$$
D:\mathcal A^{\mathrm{op}}\longrightarrow\mathcal A
$$

with a chosen involution law. The word *chosen* is essential. The opposite
construction gives $\mathcal A^{\mathrm{op}}$ for every $\mathcal A$; it
does not give a functor from that opposite back to $\mathcal A$, much less
one that fixes objects and squares to the identity.

## 14.6 Unitary Arrows And Dagger Univalence

An arrow $f:x\to y$ is *unitary* when its dagger is its two-sided inverse:

$$
f^\dagger\circ f=\mathrm{id}_x,
\qquad
f\circ f^\dagger=\mathrm{id}_y.
$$

Every unitary arrow is an isomorphism, but an isomorphism need not be unitary.
Object identity always produces a unitary isomorphism by identity induction,
so there is a canonical map

$$
\operatorname{idtoUnitary}_{\mathcal A}:
(x=y)\longrightarrow(x\cong_\dagger y).
$$

A †-category is a †-precategory for which this map is an equivalence. Its
selected notion of object sameness is unitary isomorphism, not arbitrary
isomorphism.

Two examples separate the notions. In a groupoid, define
$f^\dagger=f^{-1}$; then every arrow is unitary. For finite-dimensional inner
product spaces with arbitrary linear maps, the dagger is the adjoint linear
map. The unitary isomorphisms are the isometries, while many invertible linear
maps are not unitary. Thus this †-category need not be a HoTT category under
ordinary isomorphism.

<!-- evidence:UCAT-DAGGER-CATEGORY -->

> **Formal status — mathematical development.** Evidence
> `UCAT-DAGGER-CATEGORY`. This is the ordinary set-valued-hom theory:
> dagger laws are equalities, unitarity is a property, and dagger univalence
> compares object identity with unitary isomorphism.

## 14.7 Opposite, Duality, And Dagger Compared

The three reversal notions have different input data.

| Construction | Data supplied | Result |
| --- | --- | --- |
| opposite | any category $C$ | a category $C^{\mathrm{op}}$ with arrows reversed |
| categorical duality | a chosen equivalence $C^{\mathrm{op}}\simeq D$ | a comparison between two categories |
| dagger | a chosen identity-on-objects involutive map $C^{\mathrm{op}}\to C$ | a unitary notion internal to $C$ |

A native dagger would have to act at every retained hom dimension. At minimum
it would require:

1. a functor $D:C^{\mathrm{op}}\to C$;
2. identity-on-objects data, with an explicit decision about whether it
   computes or is witnessed coherently;
3. an involution comparison between $D\circ D^{\mathrm{op}}$ and
   $\mathrm{id}_C$;
4. compatibility of that comparison with off-diagonal and higher action;
5. a unitary-arrow classifier whose evidence is stable under identity,
   composition, and the next hom action;
6. a qualified identity-to-unitary-equivalence interface.

The ordinary equations above are a plausible strict specialization of this
design, not a license to erase the higher coherence. In particular,
`Op_cat` supplies only the first half of the ambient reversal and cannot
serve as a native dagger by itself.

<!-- evidence:NATIVE-DAGGER-INTERFACE -->

> **Formal status — research boundary.** Evidence
> `NATIVE-DAGGER-INTERFACE`. No dagger/unitary owner is active. Side task
> `FTTX-S12` remains a specification target, and this chapter does not add
> a prose-only kernel name or infer dagger structure from opposite duality.

## 14.8 Duality As A Proof Method

Opposite duality becomes useful when a theorem has already exposed its
variance. A right adjoint preserves weighted limits because a representable
comparison can be transported through its hom adjunction. Passing to
opposites exchanges:

$$
\begin{aligned}
\text{right adjoint}&\longleftrightarrow\text{left adjoint},\\
\text{weighted limit}&\longleftrightarrow\text{weighted colimit},\\
\text{unit}&\longleftrightarrow\text{counit},\\
\text{upper-star source action}&\longleftrightarrow
  \text{lower-star target action}.
\end{aligned}
$$

Chapter 17 will use these checked opposite owners to derive the colimit
preservation theorem rather than repeat the limit proof with reversed arrows.
A dagger could internalize a particular self-dual instance of such an
argument, but the general theorem needs only opposite duality. This is why the
book includes dagger structure for conceptual completeness without making it
the foundation of categorical duality.
<!-- /book-source:chapter-14 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-15 book/chapters/15-structure-identity-and-saturation.md -->
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
<!-- /book-source:chapter-15 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-16 book/chapters/16-weighted-universal-constructions.md -->
<a id="chapter-16"></a>

# 16. Weighted Universal Constructions

A limit is often introduced by drawing a cone and asking for a universal
vertex. That picture is indispensable, but it hides the operation that makes
the vertex universal: for every probe object, the category of cones must be
represented by a hom. Weighted limits expose this operation directly.

The resulting account is not a catalogue of products, equalizers, ends, and
Kan extensions. It is one theorem with several specializations:

$$
\text{weight and diagram}
\longrightarrow
\text{cone classifier}
\longrightarrow
\text{representing comparison}.
$$

The same comparison calculus that eliminated cuts in Chapter 9 then supplies
the universal beta and eta laws. Adjunction mates transport the comparison,
and therefore every right adjoint preserves every selected weighted limit for
which the comparison has been supplied.

Our mathematical conventions follow the Cat-enriched viewpoint of
[Kelly](#ref-kelly). The active artifact deliberately implements a narrower
computational interface: tensor and its two residuals are symbolic objects
with checked vertical beta/eta operations, not constructions from general
ends and coends. This distinction lets the theorem compute without claiming
semantic infrastructure that has not yet been built.

## 16.1 Weights Are Parameterized Shapes

Let

$$
F:J\longrightarrow B
$$

be a diagram. A parameterized covariant weight has the form

$$
W:J'\rightsquigarrow J,
\qquad
W:(J')^{\mathrm{op}}\times J\longrightarrow\mathsf{Cat}.
$$

For each $j':J'$, the partial functor $W(j',-)$ is a Cat-valued weight on
$J$. The first endpoint is contravariant, so an arrow $j'_0\to j'_1$ acts
from the weight at $j'_1$ to the weight at $j'_0$. This is exactly the
variance needed for the resulting representing objects to assemble into a
functor

$$
L:J'\longrightarrow B.
$$

The familiar unparameterized definition is the special case
$J'=\mathbf 1$. Retaining $J'$ is important: choosing one limit object for
each parameter is not enough. The comparison below must also make those
choices functorial in the parameter and iterable at the next hom level.

In the ordinary set-enriched case, a weight is a functor
$W:J\to\mathsf{Set}$. The set $W(j)$ describes how many copies, positions,
or generalized inputs the object $Fj$ contributes. In the Cat-valued case
those positions themselves have arrows, so a weighted cone carries coherence
along both $J$ and the internal categories $W(j',j)$.

## 16.2 The Profunctor Of Weighted Cones

For a probe object $b:B$ and a parameter $j':J'$, the expected category of
weighted cones is

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
[J,\mathsf{Cat}]
\bigl(W(j',-),\operatorname{Hom}_{B}(b,F-)\bigr).
$$

An object of this category is a natural family of arrows from $b$ into the
diagram, indexed by the weight. Its arrows are the corresponding higher
transformations. Varying $b$ acts by precomposition, while varying $j'$ acts
through the contravariant endpoint of $W$. Thus the cone construction has the
profunctorial type

$$
\operatorname{Cone}_{W}(F):B\rightsquigarrow J'.
$$

The active definition does not unfold the functor-category expression above.
It uses the covariant profunctor implication:

$$
\operatorname{Cone}_{W}(F)
:=
\operatorname{ProfImply}_{\mathrm{cov}}
\bigl(\operatorname{Hom}_{B}(-,F-),W\bigr).
$$

The literal owner is `WeightedCone_prof`, defined through
`Prof_imply_cov`. This is a useful separation. The mathematical formula says
what weighted cones mean in a semantic model with the necessary ends; the
implication is the stable computational owner used by the present theory.

## 16.3 Tensor And The Two Residuals

Suppose

$$
P:A\rightsquigarrow B,
\qquad
Q:B\rightsquigarrow X,
\qquad
O:A\rightsquigarrow X.
$$

Tensor makes the middle endpoint into a cut:

$$
P\otimes_B Q:A\rightsquigarrow X.
$$

There are two ways to solve a mapping problem against this composite. Holding
$Q$ fixed gives a right residual with type $A\rightsquigarrow B$; holding
$P$ fixed gives a left residual with type $B\rightsquigarrow X$. The active
interfaces are characterized by inverse operations

$$
\begin{aligned}
\operatorname{ProfMap}
 \bigl(P,\operatorname{ProfImply}_{\mathrm{cov}}(O,Q)\bigr)
&\simeq
\operatorname{ProfMap}(P\otimes_B Q,O),\\
\operatorname{ProfMap}
 \bigl(Q,\operatorname{ProfImply}_{\mathrm{con}}(P,O)\bigr)
&\simeq
\operatorname{ProfMap}(P\otimes_B Q,O).
\end{aligned}
$$

Evaluation introduces the tensor cut; lambda abstraction removes it. In both
orientations the selected composites reduce:

$$
\begin{aligned}
\lambda(\operatorname{eval}(t))&\rightsquigarrow t,\\
\operatorname{eval}(\lambda(u))&\rightsquigarrow u.
\end{aligned}
$$

These are universal-property beta and eta laws in the same sense as the
upper-star and `tapp1` reductions of Chapter 9. They choose a stable owner for
associativity rather than globally reassociating arbitrary composites.

<!-- evidence:PROF-CLOSED-CALCULUS -->

> **Formal status — checked.** Evidence `PROF-CLOSED-CALCULUS`.
> `Prof_imply_cov` and `Prof_imply_con` are the two opaque residual
> objects. `Prof_eval_cov_map`, `Prof_lambda_cov_map`,
> `Prof_eval_con_map`, and `Prof_lambda_con_map` expose the checked
> fixed-endpoint beta/eta calculus. This status does not assert an end formula
> for either residual.

The weighted cone is now forced rather than guessed. For every
$P:B\rightsquigarrow J'$,

$$
\operatorname{ProfMap}
 \bigl(P,\operatorname{Cone}_{W}(F)\bigr)
\simeq
\operatorname{ProfMap}
 \bigl(P\otimes_{J'}W,\operatorname{Hom}_{B}(-,F-)\bigr).
$$

A map on the right is precisely a $P$-shaped family of $W$-weighted cone
data. The residual packages all such maps into one profunctor. In this form,
a weight is not an annotation on a limit symbol: it is the profunctor cut
that the cone classifier abstracts.

The tensor itself remains an opaque fixed-middle composite. Its current
functorial action and shaped-element constructor are checked, but a semantic
coend, associator, unitors as equivalences, and the coherence of a full
profunctor bicategory are not consequences of those interfaces.

<!-- evidence:PROF-TENSOR -->
<!-- evidence:PROF-GENERAL-COEND -->

> **Formal status — checked interface and research boundary.** Evidence
> `PROF-TENSOR` covers the selected tensor object, outer-endpoint
> reindexing, vertical bifunctoriality, and shaped tensor elements. Evidence
> `PROF-GENERAL-COEND` records what is missing. The displayed residual
> mapping laws are checked only through the fixed-endpoint eval/lambda
> operations above.

## 16.4 A Weighted Limit Is A Representation

A $W$-weighted limit of $F$ is a functor

$$
L:J'\longrightarrow B
$$

together with a representation of the cone profunctor:

$$
\Phi:
\operatorname{Cone}_{W}(F)
\simeq
\operatorname{Hom}_{B}(-,L-).
$$

At a pair $(b,j')$, this says

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
\operatorname{Hom}_{B}(b,Lj').
$$

The direction of the hom is worth checking. A limit receives a cone *from*
the probe $b$, so maps from $b$ to the limit classify cones from $b$. A
colimit will reverse this direction in Chapter 17.

There are two active representation classifiers. The ordinary classifier
`IsWeightedLimit_cov_iso` asks for isomorphism evidence in the profunctor
category. The computational classifier `IsWeightedLimit_cov_comp` asks for a
`ProfComparison`. The latter retains selected forward and inverse maps whose
beta and eta laws compute on every incoming profunctor map.

<!-- evidence:WEIGHTED-LIMIT-REPRESENTABILITY -->

> **Formal status — checked.** Evidence
> `WEIGHTED-LIMIT-REPRESENTABILITY`. `WeightedCone_prof` constructs the
> cone profunctor, while `IsWeightedLimit_cov_iso` and
> `IsWeightedLimit_cov_comp` give the ordinary and computational
> representation interfaces. The checked claim is the interface and its
> reductions, not existence of a weighted limit for every diagram.

This is the universal-property row of the rule schema in
[Appendix G.4](#appendix-formal-presentation-g4). Formation fixes
$F$, $W$, and the proposed representing functor $L$; introduction supplies a
comparison certificate; push and pull are eliminations; their inverse
reductions are beta and eta; and reindexing in the probe is the action clause.
Existence and univalent uniqueness are additional principles, not hidden
fields of the checked classifier.

This formulation also separates *being* a limit from *choosing* one. A
theorem may accept a comparison for a particular $F$, $W$, and $L$ without
postulating a global limit operator. In a univalent specialization,
representability can later make the choice unique in the appropriate sense;
the preservation theorem below does not need that stronger uniqueness
package.

## 16.5 Universal Introduction And Elimination

Let

$$
M:I\longrightarrow B
$$

be a shaped family of probe objects, and let

$$
R:I\rightsquigarrow J'
$$

index a family of test data. Reindexing $\Phi$ along $M$ gives inverse
operations

$$
\begin{aligned}
\mathsf{push}:&
\operatorname{ProfMap}
 \bigl(R,\operatorname{Cone}_{W}(M,F)\bigr)
\longrightarrow
\operatorname{ProfMap}
 \bigl(R,\operatorname{Hom}_{B}(M,L)\bigr),\\
\mathsf{pull}:&
\operatorname{ProfMap}
 \bigl(R,\operatorname{Hom}_{B}(M,L)\bigr)
\longrightarrow
\operatorname{ProfMap}
 \bigl(R,\operatorname{Cone}_{W}(M,F)\bigr).
\end{aligned}
$$

Here

$$
\operatorname{Cone}_{W}(M,F)
:=
\operatorname{ProfImply}_{\mathrm{cov}}
 \bigl(\operatorname{Hom}_{B}(M-,F-),W\bigr).
$$

The operation `push` eliminates a supplied cone through the universal
comparison and obtains its mediating map into $L$. The operation `pull`
introduces a cone by composing a map into $L$ with the universal cone. Their
cuts reduce in both directions:

$$
\begin{aligned}
\mathsf{pull}(\mathsf{push}(r))&\rightsquigarrow r,\\
\mathsf{push}(\mathsf{pull}(s))&\rightsquigarrow s.
\end{aligned}
$$

<!-- evidence:PROF-COMPARISON-BETA-ETA -->

> **Formal status — checked.** Evidence
> `PROF-COMPARISON-BETA-ETA`. The weighted operations
> `weighted_limit_cov_push` and `weighted_limit_cov_pull` are typed
> specializations of the generic `prof_comparison_push` and
> `prof_comparison_pull` owners. The beta/eta rules belong to the generic
> comparison, so no new cancellation rule is attached to each kind of limit.

The role of $R$ is easy to underestimate. Taking a single element would test
only one cone. Allowing an arbitrary incoming profunctor map says that the
universal operation is stable under families, endpoint action, and the next
categorical layer retained by the fixed-endpoint profunctor category. This is
the functorial type-theoretic replacement for an unstructured bijection of
sets of cones.

## 16.6 Conical Limits As The Terminal-Weight Specialization

Set $J'=\mathbf 1$ and take the terminal weight

$$
\mathbf 1_{J}:\mathbf 1\rightsquigarrow J.
$$

Its only fibre is the terminal category. In the usual semantic
interpretation,

$$
\begin{aligned}
\operatorname{Cone}_{\mathbf 1_J}(b,F;*)
&\simeq
[J,\mathsf{Cat}]
 \bigl(\mathbf 1,\operatorname{Hom}_{B}(b,F-)\bigr)\\
&\simeq
\operatorname{Cone}(b,F).
\end{aligned}
$$

A functor $\ell:\mathbf 1\to B$ selects a vertex. The weighted
representation becomes the familiar conical universal property

$$
\operatorname{Cone}(b,F)
\simeq
\operatorname{Hom}_{B}(b,\ell).
$$

Products, terminal objects, pullbacks, and equalizers arise by choosing their
usual indexing categories $J$. The weighted formulation does not require a
new universal-property mechanism for each of them.

At the active-interface level, the substitution is exact:

$$
\operatorname{IsWeightedLimit}
 \bigl(F,\operatorname{TerminalProf}(\mathbf 1,J),\ell\bigr)
$$

is a well-formed instance of `IsWeightedLimit_cov_comp`. This variance fact
is permanent regression evidence. What is not checked is the semantic
identification of the opaque profunctor implication with the displayed
functor category of ordinary cones.

<!-- evidence:WEIGHTED-LIMIT-SPECIALIZATIONS -->

> **Formal status — formal consequence.** Evidence
> `WEIGHTED-LIMIT-SPECIALIZATIONS`. `Terminal_prof`,
> `IsWeightedLimit_cov_comp`, and the focused classifier diagnostics
> establish the terminal-weight instance and its preservation corollary.
> Calling its fibres the usual cone categories is mathematical development
> contingent on the end semantics described below.

## 16.7 Right Kan Extensions As Conjoint-Weighted Limits

Let

$$
K:J\longrightarrow J'
$$

and retain the diagram $F:J\to B$. The conjoint of $K$ is the profunctor

$$
K^{\ast}:J'\rightsquigarrow J,
\qquad
K^{\ast}(j',j)
=\operatorname{Hom}_{J'}(j',Kj).
$$

It has exactly the variance of a limit weight. Define a selected right
Kan-extension comparison along $K$ to be the weighted-limit comparison

$$
\operatorname{IsWeightedLimit}
 \bigl(F,K^{\ast},\operatorname{Ran}_{K}F\bigr).
$$

When the residual has its expected end semantics, the fibrewise formula is

$$
\operatorname{Hom}_{B}
 \bigl(b,(\operatorname{Ran}_{K}F)(j')\bigr)
\simeq
\operatorname{Nat}
\left(
  \operatorname{Hom}_{J'}(j',K-),
  \operatorname{Hom}_{B}(b,F-)
\right).
$$

This is the standard pointwise right Kan-extension formula. It says that
maps into the value at $j'$ are cones whose shape is the representable
weight out of $j'$.

The use of a conjoint is not a mnemonic guess. `Conjoint_prof K` has type
$J'\rightsquigarrow J$, so the expression

$$
\operatorname{IsWeightedLimit}
 \bigl(F,\operatorname{Conjoint}(K),R\bigr)
$$

is a well-formed active classifier for every $R:J'\to B$. The focused
variance audit checks precisely this substitution.

The following two claims must nevertheless remain separate:

1. **Interface specialization:** conjoint weight yields an instance of the
   selected weighted comparison. This is a formal consequence of the active
   types.
2. **Semantic identification:** that instance agrees with the ordinary
   natural-transformation or end definition of pointwise right Kan extension.
   This requires a semantic end owner and coherence for the relevant
   Cat-valued transformation category.

<!-- evidence:WEIGHTED-END-KAN-SEMANTICS -->

> **Formal status — mathematical development.** Evidence
> `WEIGHTED-END-KAN-SEMANTICS`. The standard conical and pointwise
> Kan-extension formulas are mathematically part of the weighted theory.
> `Prof_imply_cov` currently packages their computational residual but does
> not unfold to a general end.

## 16.8 Adjunction Mates Transport Representables

Let

$$
S:A\longrightarrow B,
\qquad
R:B\longrightarrow A,
\qquad
S\dashv R.
$$

For arbitrary shaped functors $M:I\to A$ and $D:J\to B$, the adjunction
supplies the representable comparison

$$
\operatorname{Hom}_{B}(SM,D)
\simeq
\operatorname{Hom}_{A}(M,RD).
$$

It is natural in both endpoints and therefore lives as a
`ProfComparison`, not merely as a family of unrelated pointwise
equivalences. Passing this comparison through the fixed-weight implication
transports whole cone profunctors.

<!-- evidence:ADJ-HOM-PROF-COMPARISON -->

> **Formal status — checked.** Evidence
> `ADJ-HOM-PROF-COMPARISON`.
> `Adjunction_hom_prof_comparison_along` is the reindexed mate
> comparison. Its inverse directions and their cancellation are inherited
> from the generic profunctor-comparison calculus.

In classical category theory, a mate is often introduced by a formula using
the unit and counit. Computationally, the mate is better understood as a
change of representable coordinates. The triangle reductions of Chapter 12
are exactly the beta/eta laws ensuring that moving across the adjunction and
back removes the cut.

## 16.9 The Preservation Theorem

Assume that

$$
\ell:J'\longrightarrow B
$$

is supplied with a computational comparison certifying it as the
$W$-weighted limit of $D:J\to B$. We prove that

$$
R\ell:J'\longrightarrow A
$$

is the $W$-weighted limit of $RD:J\to A$.

Test the proposed representation at an arbitrary $M:I\to A$. There are three
comparisons:

$$
\begin{aligned}
\operatorname{Cone}_{W}(M,RD)
&\simeq
\operatorname{Cone}_{W}(SM,D)
&&\text{by the inverse mate under the residual},\\
&\simeq
\operatorname{Hom}_{B}(SM,\ell)
&&\text{by the supplied limit comparison},\\
&\simeq
\operatorname{Hom}_{A}(M,R\ell)
&&\text{by the mate at the candidate limit}.
\end{aligned}
$$

The middle comparison is the original representation reindexed along $S$.
The first and third are the same hom adjunction used in opposite directions
and at different diagrams. Composing them yields

$$
\operatorname{Cone}_{W}(RD)
\simeq
\operatorname{Hom}_{A}(-,R\ell-),
$$

which is the required weighted-limit comparison.

The implementation mirrors this proof without inserting a special rewrite
that says “right adjoints preserve limits.” Its three factors are:

1. `right_adjoint_weighted_limit_comp_step1`, the inverse mate mapped
   through the fixed-weight implication;
2. `right_adjoint_weighted_limit_comp_step2`, the supplied comparison
   reindexed along the left adjoint;
3. `right_adjoint_weighted_limit_comp_step3`, the mate at $\ell$.

`right_adjoint_preserves_weighted_limit_cov_comp` composes these
certificates. Since the result is again a `ProfComparison`, all universal
push/pull beta and eta behavior survives.

<!-- evidence:WEIGHTED-LIMIT-PRESERVATION -->

> **Theorem 16.1 — Right adjoints preserve selected weighted limits.**
> Given a computational $W$-weighted-limit comparison for $D$ and an
> adjunction $S\dashv R$, the active construction returns a computational
> $W$-weighted-limit comparison for $RD$ represented by $R\ell$.
>
> **Formal status — checked.** Evidence
> `WEIGHTED-LIMIT-PRESERVATION`. The theorem is conditional on a supplied
> comparison. It neither asserts that every weighted limit exists nor that a
> right adjoint creates one.

This proof is the promised continuation of cut elimination. The first mate
changes coordinates, the given universal comparison eliminates the central
cone cut, and the final mate changes coordinates back. Associativity is
controlled by composition of comparison certificates; it is not delegated to
a global reassociation rule.

## 16.10 Ordinary-Limit And Kan-Extension Corollaries

The theorem is uniform in $W$, so the two audited specializations immediately
give interface-level corollaries.

For the terminal weight:

> If $\ell$ carries the selected conical-limit comparison for $D$, then
> $R\ell$ carries the corresponding comparison for $RD$.

For the conjoint of $K:J\to J'$:

> If $\operatorname{Ran}_{K}D$ carries the selected right-Kan comparison,
> then $R\operatorname{Ran}_{K}D$ carries the corresponding comparison for
> $\operatorname{Ran}_{K}(RD)$.

These are not new preservation algorithms. They are the same
`right_adjoint_preserves_weighted_limit_cov_comp` term with
$W=\operatorname{TerminalProf}(\mathbf 1,J)$ or
$W=\operatorname{Conjoint}(K)$. The formal consequence is therefore stronger
than a slogan and weaker than the unimplemented semantic end theorem: the
classifier, transported comparison, and beta/eta interface are active; the
identification with every conventional presentation of limits or Kan
extensions is not.

## 16.11 Ends, Coends, And Dependent Universal Constructions

A semantic completion of this chapter would construct the residual by an end,
for example

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
\int_{j:J}
\left[
  W(j',j),
  \operatorname{Hom}_{B}(b,Fj)
\right],
$$

and tensor by a coend

$$
(P\otimes_B Q)(a,x)
\simeq
\int^{b:B}P(a,b)\times Q(b,x).
$$

Such constructions must provide more than object formulas. They need
introduction and elimination principles, action on base arrows and transfors,
beta/eta or comparison laws, associativity and unit coherence, and a
validation route through the shaped co-Yoneda theorem. Until those owners
exist, the formulas are semantic specifications for the opaque interfaces.

Dependent category theory asks for a further chain. For a base functor
$f:X\to Y$, one expects suitable change-of-base functors and adjunctions

$$
\Sigma_f\dashv f^{*}\dashv\Pi_f,
$$

with Beck--Chevalley and higher naturality conditions. The current Sigma and
Pi categories of directed families are important footholds, but no general
dependent adjunction package connects them to arbitrary base change. A
pointwise object formula would be insufficient: the construction must retain
base-arrow action, off-diagonal transfor action, and iteration into the next
hom.

<!-- evidence:DEPENDENT-ADJUNCTIONS -->

> **Formal status — research boundary.** Evidence
> `DEPENDENT-ADJUNCTIONS`. General end/coend owners, pointwise Kan
> packages, and the dependent adjunction chain remain separate formal
> projects. The active weighted comparison is the design constraint those
> projects should refine, not a claim that they are already present.

Chapter 17 now applies the safest of all extensions: opposite duality. It
turns the checked limit theorem into a colimit theorem, after which the join
shows how terminal-weight cross-arrow data can itself be internalized as a
directed categorical shape.
<!-- /book-source:chapter-16 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:chapter-17 book/chapters/17-weighted-colimits-duality-and-join.md -->
<a id="chapter-17"></a>

# 17. Weighted Colimits, Duality, And Join

The preceding chapter classified cones by homs *into* a representing object.
Colimits classify cocones by homs *out of* one. Every variance reverses:
companions replace conjoints, left adjoints replace right adjoints, and the
universal arrows point away from the colimit.

Opposite duality makes this reversal a proof method rather than an invitation
to duplicate the theory. The active weighted-colimit classifier is defined
through the weighted-limit classifier in opposite categories. Its
preservation theorem is therefore the right-adjoint theorem of Chapter 16
applied once to the opposite adjunction.

The second half of the chapter gives this duality a directed geometry. The
join $A\star B$ contains a left part, a right part, and an internally natural
family of arrows directed from left to right. Its recursor has the same input
shape as the collage of a terminal profunctor. That observation connects
joins to weighted cone data while leaving the stronger collage semantics
explicitly open.

## 17.1 Weighted Cocones

Let

$$
F:J\longrightarrow B
$$

be a diagram and let

$$
W:J\rightsquigarrow J'
$$

be a contravariant weight, meaning a Cat-valued profunctor

$$
W:J^{\mathrm{op}}\times J'\longrightarrow\mathsf{Cat}.
$$

For fixed $j':J'$, the weight $W(-,j')$ is contravariant in $J$. At a
candidate target $b:B$, its expected cocone category is

$$
\operatorname{Cocone}_{W}(F;j',b)
\simeq
[J^{\mathrm{op}},\mathsf{Cat}]
\bigl(W(-,j'),\operatorname{Hom}_{B}(F-,b)\bigr).
$$

A $W$-weighted colimit is a functor

$$
C:J'\longrightarrow B
$$

with a representation

$$
\operatorname{Cocone}_{W}(F;j',b)
\simeq
\operatorname{Hom}_{B}(Cj',b)
$$

natural in $j'$ and $b$. Compare this with the limit equation

$$
\operatorname{Cone}_{W}(b,F;j')
\simeq
\operatorname{Hom}_{B}(b,Lj').
$$

The same words “represented by” occur in both formulas, but the representable
hom has changed side.

## 17.2 One Universal Owner Through Opposite Categories

For

$$
F:J\to B,
\qquad
W:J\rightsquigarrow J',
\qquad
C:J'\to B,
$$

the active definition is

$$
\operatorname{IsWeightedColimit}_{B}(F,W,C)
:=
\operatorname{IsWeightedLimit}_{B^{\mathrm{op}}}
\bigl(F^{\mathrm{op}},W^{\mathrm{op}},C^{\mathrm{op}}\bigr).
$$

Reversing the profunctor endpoints gives

$$
W^{\mathrm{op}}:(J')^{\mathrm{op}}\rightsquigarrow J^{\mathrm{op}},
$$

which is exactly the variance expected by the limit classifier in the
opposite categories. The representing equation there is

$$
\operatorname{Hom}_{B^{\mathrm{op}}}(b,Cj')
=
\operatorname{Hom}_{B}(Cj',b),
$$

so it recovers the desired cocone orientation.

The owner `WeightedColimit_con` is transparent to
`IsWeightedLimit_cov_comp` after applying `Op_func` and
`Op_prof`. The conversion operations between a limit witness and the
corresponding opposite colimit witness are identity-like wrappers after
double-opposite and product-swap computation. Colimit beta/eta therefore
comes from the same profunctor comparison used for limits.

<!-- evidence:OP-DUALITY -->

> **Formal status — checked.** Evidence `OP-DUALITY`. The involutive
> category, functor, transfor, profunctor, and adjunction operations justify
> the variance reversal. No independent colimit cancellation calculus is
> introduced.

## 17.3 Conical Colimits And Left Kan Extensions

The terminal-weight specialization now uses the opposite orientation:

$$
\mathbf 1^{J}:J\rightsquigarrow\mathbf 1.
$$

For a vertex $c:\mathbf 1\to B$, the active classifier

$$
\operatorname{IsWeightedColimit}
\bigl(F,\operatorname{TerminalProf}(J,\mathbf 1),c\bigr)
$$

is well formed. Under the standard semantic interpretation its fibres become
ordinary cocone categories, and the representation reads

$$
\operatorname{Cocone}(F,b)
\simeq
\operatorname{Hom}_{B}(c,b).
$$

Thus initial objects, coproducts, pushouts, and coequalizers are terminal
weight specializations on their usual indexing categories.

For a functor

$$
K:J\longrightarrow J',
$$

the companion has the required colimit variance:

$$
K_{\ast}:J\rightsquigarrow J',
\qquad
K_{\ast}(j,j')
=\operatorname{Hom}_{J'}(Kj,j').
$$

A selected left Kan-extension comparison is therefore

$$
\operatorname{IsWeightedColimit}
\bigl(F,K_{\ast},\operatorname{Lan}_{K}F\bigr).
$$

With the expected coend or cocone semantics, it gives the pointwise formula

$$
\operatorname{Hom}_{B}
\bigl((\operatorname{Lan}_{K}F)(j'),b\bigr)
\simeq
\operatorname{Nat}
\left(
  \operatorname{Hom}_{J'}(K-,j'),
  \operatorname{Hom}_{B}(F-,b)
\right).
$$

The focused variance audit checks both active substitutions:
`Terminal_prof J Terminal_cat` and `Companion_prof K` inhabit the
weight slot of `WeightedColimit_con`. As in Chapter 16, this does not by
itself identify the opaque opposite residual with a semantic category of
cocones.

<!-- evidence:WEIGHTED-COLIMIT-SPECIALIZATIONS -->

> **Formal status — formal consequence.** Evidence
> `WEIGHTED-COLIMIT-SPECIALIZATIONS`. The terminal-weight and companion
> classifiers, together with their preservation instances, follow from the
> active types and the opposite definition. Their standard conical and
> pointwise-left-Kan interpretations remain mathematical development under
> `WEIGHTED-END-KAN-SEMANTICS`.

The companion/conjoint distinction is now visible in one table:

| Construction along $K:J\to J'$ | Weight | Fibre |
| --- | --- | --- |
| right Kan extension | conjoint $K^{\ast}:J'\rightsquigarrow J$ | $\operatorname{Hom}_{J'}(j',Kj)$ |
| left Kan extension | companion $K_{\ast}:J\rightsquigarrow J'$ | $\operatorname{Hom}_{J'}(Kj,j')$ |

Suppressing the profunctor endpoints would make these formulas look
deceptively interchangeable. The endpoints are the type-level variance audit.

## 17.4 Left Adjoints Preserve Weighted Colimits

Let

$$
S:A\longrightarrow B,
\qquad
R:B\longrightarrow A,
\qquad
S\dashv R,
$$

and suppose

$$
C:J'\longrightarrow A
$$

carries a comparison certifying it as the $W$-weighted colimit of
$F:J\to A$. Passing to opposites turns the data into:

1. a weighted-limit comparison for $C^{\mathrm{op}}$ and
   $F^{\mathrm{op}}$ in $A^{\mathrm{op}}$;
2. the opposite adjunction
   $R^{\mathrm{op}}\dashv S^{\mathrm{op}}$;
3. a right adjoint $S^{\mathrm{op}}:A^{\mathrm{op}}\to B^{\mathrm{op}}$.

Theorem 16.1 therefore supplies a weighted-limit comparison represented by

$$
S^{\mathrm{op}}C^{\mathrm{op}}
=(SC)^{\mathrm{op}}.
$$

Turning the result back around gives a $W$-weighted-colimit comparison for
$SF$ represented by $SC$.

At the level of cocones, the three-comparison proof is the familiar chain

$$
\begin{aligned}
\operatorname{Cocone}_{W}(SF;b)
&\simeq
\operatorname{Cocone}_{W}(F;Rb),\\
&\simeq
\operatorname{Hom}_{A}(C,Rb),\\
&\simeq
\operatorname{Hom}_{B}(SC,b).
\end{aligned}
$$

The first and last steps are adjunction mates, and the middle step is the
given colimit representation. The implementation obtains this chain by
calling the right-adjoint theorem on `Op_adjunction`; it does not repeat the
three steps under new primitive names.

<!-- evidence:WEIGHTED-COLIMIT-PRESERVATION -->

> **Theorem 17.1 — Left adjoints preserve selected weighted colimits.**
> Given a computational $W$-weighted-colimit comparison for $F$ and an
> adjunction $S\dashv R$, the active construction returns a computational
> comparison for $SF$ represented by $SC$.
>
> **Formal status — checked.** Evidence
> `WEIGHTED-COLIMIT-PRESERVATION`. The owner
> `left_adjoint_preserves_weighted_colimit_con` applies
> `right_adjoint_preserves_weighted_limit_cov_comp` to the opposite
> adjunction. The theorem is conditional on the supplied colimit comparison.

Consequently, the terminal and companion specializations yield the familiar
interface-level corollaries: left adjoints preserve selected conical colimits
and selected left Kan extensions. No new proof is hidden behind either
phrase.

## 17.5 A Variance Ledger

The dual theorem can be remembered without reversing formulas in one’s head:

| Feature | Weighted limit | Weighted colimit |
| --- | --- | --- |
| weight | $J'\rightsquigarrow J$ | $J\rightsquigarrow J'$ |
| universal data | arrows $b\to Fj$ | arrows $Fj\to b$ |
| represented hom | $\operatorname{Hom}_{B}(b,Lj')$ | $\operatorname{Hom}_{B}(Cj',b)$ |
| Kan weight | conjoint | companion |
| preserving adjoint | right | left |
| proof | direct three-comparison chain | the same chain in opposites |

This ledger is more than notation. It identifies which endpoint acts by
upper-star precomposition and which acts by lower-star postcomposition. The
opposite construction exchanges those actions while preserving their
computational owners.

## 17.6 The Directed Join Signature

For native categories $A$ and $B$, the primitive join is a category

$$
A\star B
$$

with inclusion functors

$$
\iota_A:A\longrightarrow A\star B,
\qquad
\iota_B:B\longrightarrow A\star B.
$$

Its characteristic constructor is not an equality between the two parts. It
is an internally natural family of arrows from the left part to the right
part:

$$
\chi:
\mathbf 1_{A,B}
\Longrightarrow
\operatorname{Hom}_{A\star B}(\iota_A- ,\iota_B-),
$$

where

$$
\mathbf 1_{A,B}:A\rightsquigarrow B
$$

is the terminal profunctor. At objects, $\chi$ supplies

$$
\chi_{a,b}:\iota_A(a)\longrightarrow\iota_B(b).
$$

Because $\chi$ is a profunctor cell, naturality in both $a$ and $b$ is part
of one internal datum. It is not an externally quantified family followed by
a separately asserted equation. For shaped functors $a:I\to A$ and
$b:I\to B$, `join_cross_hom` evaluates the same cell to the corresponding
shaped cross arrow and retains its higher action.

There is no reverse constructor
$\iota_B(b)\to\iota_A(a)$. The join is directed even when $A$ and $B$
individually happen to be groupoidal.

## 17.7 Recursion And Its Three Beta Observations

To define a functor

$$
H:A\star B\longrightarrow E,
$$

the active nondependent recursor accepts:

1. a functor $F:A\to E$;
2. a functor $G:B\to E$;
3. an internally natural cross cell

   $$
   \gamma:
   \mathbf 1_{A,B}
   \Longrightarrow
   \operatorname{Hom}_{E}(F-,G-).
   $$

It returns `join_elim_func F G gamma`. The two restrictions compute:

$$
\begin{aligned}
H\circ\iota_A&\rightsquigarrow F,\\
H\circ\iota_B&\rightsquigarrow G.
\end{aligned}
$$

The selected observation of the image of the universal cross cell also
computes:

$$
H(\chi)\rightsquigarrow\gamma.
$$

The literal third owner is `join_elim_cross_transf`. It records the
cross-cell beta rule without adding a broad equation for arbitrary functor
application to primitive join syntax.

<!-- evidence:JOIN-RECURSOR -->

> **Formal status — checked.** Evidence `JOIN-RECURSOR`. The active
> owners are `Join_cat`, `join_fst_func`, `join_snd_func`,
> `join_cross_transf`, `join_cross_hom`, `join_elim_func`, and
> `join_elim_cross_transf`. The checked interface is a nondependent
> recursor with its three observations; it is not yet a uniqueness theorem
> for all functors out of the join.

The recursor repeats the book’s computational pattern. The inclusions and
cross cell introduce the join; restriction and the selected cross
observation eliminate it; matching introduction/elimination cuts reduce to
the supplied data.

## 17.8 Ordinary Cones And Cocones As Join Diagrams

The join makes the orientation of conical universal data concrete. A functor

$$
\mathbf 1\star J\longrightarrow B
$$

can be constructed from:

- an object $b:B$;
- a diagram $F:J\to B$;
- a natural family of cross arrows $b\to Fj$.

That is precisely the data of a cone from $b$ to $F$. Reversing the two
parts, a functor

$$
J\star\mathbf 1\longrightarrow B
$$

can be constructed from $F$, an object $c$, and arrows
$Fj\to c$: the data of a cocone.

This is an interface-level construction supplied by the recursor. It does not
yet assert an equivalence between a full mapping category out of the join and
a category of cones. Such an equivalence would require an eta or uniqueness
principle for join maps and coherent action on transformations between them.

The connection to weights is now visible. A conical cone uses the terminal
weight, and the join internalizes a terminal profunctor as its family of
left-to-right cross arrows. Replacing that terminal profunctor by an arbitrary
$P:A\rightsquigarrow B$ leads to the notion of a collage.

## 17.9 Join As A Directed Higher-Inductive Pattern

The join has the shape of a directed higher-inductive specification:

- two strata of objects, introduced through $A$ and $B$;
- a family of directed arrow constructors from every left object to every
  right object;
- a recursor into an arbitrary target;
- beta observations on the two strata and the cross family.

This comparison is architectural, not a claim that `Join_cat` was generated
by a general directed-HIT compiler. The primitive join is one selected
signature. Its cross constructor is already internally natural, which is the
category-level analogue of giving all boundary coherence with the
constructor.

WalkingEnd and join illustrate two different levels of the same programme.
WalkingEnd has an opaque point and endomorphism together with a contextual
dependent eliminator strong enough for encode-decode. Join has two
category-shaped introductions and a nondependent recursor, but no dependent
eliminator or computation of all its hom-categories. Thus join supplies a
promising stress test for a future directed-HIT schema without borrowing
properties proved only for WalkingEnd.

## 17.10 The Collage Comparison

For a profunctor

$$
P:A\rightsquigarrow B,
$$

its expected collage $\operatorname{Coll}(P)$ contains $A$ and $B$ as two
parts and uses $P(a,b)$ as the category of arrows from the left object $a$ to
the right object $b$. Its universal mapping property has the schematic form

$$
\operatorname{Fun}\bigl(\operatorname{Coll}(P),E\bigr)
\simeq
\sum_{F:A\to E}
\sum_{G:B\to E}
\operatorname{ProfCell}
\bigl(P,\operatorname{Hom}_{E}(F-,G-)\bigr).
$$

Taking $P=\mathbf 1_{A,B}$ gives exactly the *input shape* of the active join
recursor. This is strong design evidence for reading $A\star B$ as the
prospective collage of the terminal profunctor.

It is not yet a proof of that reading. A checked collage theorem would need:

1. an object decomposition into the left and right strata;
2. left-left and right-right hom comparisons recovering $A$ and $B$;
3. a left-right hom comparison recovering $P$;
4. a right-left hom description, normally initial in the free collage;
5. composition and higher action compatible with those four regions;
6. full faithfulness of the inclusions;
7. an equivalence of mapping categories, including uniqueness and higher
   transformations;
8. a dependent eliminator with beta behavior on the cross cells.

The active primitive supplies the inclusions, one terminal cross cell, and
the forward recursor only. It exposes none of the required hom
decompositions. Likewise, one expects an opposite comparison

$$
(A\star B)^{\mathrm{op}}
\simeq
B^{\mathrm{op}}\star A^{\mathrm{op}},
$$

but no such comparison is currently selected.

<!-- evidence:JOIN-COLLAGE-BOUNDARY -->

> **Formal status — research boundary.** Evidence
> `JOIN-COLLAGE-BOUNDARY`. Side task `FTTX-S13` owns the proposed
> collage semantics and dependent elimination. The current chapter claims
> only that the checked recursor has the terminal-collage input shape.

## 17.11 From Universal Cuts To Directed Geometry

Weighted limits and colimits began with a mapping problem: a profunctor of
cones or cocones is represented by a hom. Join begins with the same data from
the other side. Instead of representing a terminal family of cross arrows
inside a target, it freely presents a domain from which such data can be
interpreted by recursion.

The two constructions therefore complement one another:

$$
\begin{array}{c|c}
\text{weighted representation}
&
\text{directed join recursion}\\
\hline
\text{classifies maps into or out of a vertex}
&
\text{internalizes a family of cross arrows}\\
\text{beta/eta from a profunctor comparison}
&
\text{beta from introduction/recursion}\\
\text{arbitrary weight}
&
\text{currently the terminal profunctor}\\
\text{right/left adjoint preservation}
&
\text{prospective collage and dependent elimination}
\end{array}
$$

This is the globally coherent role of the active universal-construction
interfaces. Tensor, residuals, weighted representation, duality, and join are
not isolated features. Each controls a different kind of cut, and each leaves
enough categorical action visible for a future elaboration layer to compile
surface mathematics into the same computational core.
<!-- /book-source:chapter-17 -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:appendix-notation book/appendices/a-notation.md -->
<a id="appendix-notation"></a>

# Appendix A. Notation

The book follows
`reports/REPORT_EMDASH_V3_2_CANONICAL_SURFACE_SYNTAX_2026-06-05.md`.
This appendix records the compact notation used in the mathematical line of
the book. It is a reading guide, not a proposal to make every glyph parser
syntax.

| Book notation | Reading | Current implementation witness |
| --- | --- | --- |
| $a\to_C b$ | an arrow of $C$ from $a$ to $b$ | `Hom C a b` |
| $F:A\vdash B$ | a functor from $A$ to $B$ | `Functor A B` |
| $E:K\vdash\mathsf{Cat}$ | a Cat-valued directed family | `Catd K` |
| $E[f]$ | functorial action of a family on a base arrow | `catd_transport_func` |
| $H_x$ | the based hom-category $\operatorname{Hom}_W(*,x)$ | `Hom_cat WalkingEnd_cat walking_base x` |
| $W$, $*$, $\ell$ | WalkingEnd, its base, and its directed generator | `WalkingEnd_cat`, `walking_base`, `walking_loop` |
| $\mathsf{Code}$ | the Nat-valued directed family over $W$ | `walking_Code_catd` |
| $\mathsf{encode}_x(p)$ | apply $\mathsf{Code}[p]$ to zero | `walking_encode` |
| $\ell^n$ or $\mathsf{power}(n)$ | the $n$th generator-prefix power | `walking_power` |
| $\mathsf{decode}_x(c)$ | the object action of the contextual decoder | `walking_directed_decode_funcd` |
| $\nu_p$ | the directed normalization cell $p\to\mathsf{decode}_x(\mathsf{encode}_x(p))$ | `walking_directed_normalization_cell` |
| $\simeq$ | an explicitly stated equivalence interface | in Theorem 8.1, `walking_hom_nat_type_equiv` |
| $F[f]$ | functor action on an arrow | `fapp1_fapp0` and its iterable `fapp1_func` owner |
| $u_*(g)$ | postcomposition by $u$, namely $u\circ g$ | `hom_postcomp_fapp0` |
| $u^*(h)$ | precomposition by $u$, namely $h\circ u$ | `hom_precomp_along_fapp0` |
| $\eta[f]$ | off-diagonal action of a transfor on $f:x\to y$ | `tapp1_fapp0` |
| $\chi^\Phi_{(p,u)}$ | displayed transport-comparison component | `fdapp1_int_cell` |
| $P:A\rightsquigarrow B$ | a Cat-valued profunctor on $A^{\mathrm{op}}\times B$ | `Prof A B` |
| $U_A$ | the unit hom profunctor | `Unit_prof A` |
| $P\otimes_B Q$ | selected fixed-middle profunctor tensor | `Prof_tensor P Q` |
| $F\dashv G$ | adjunction data with selected triangle cuts | `Adjunction F G` |
| $\operatorname{Cone}_W(F)$ | the weighted-cone profunctor | `WeightedCone_prof F W` |
| $\operatorname{IsWeightedLimit}(F,W,L)$ | a chosen representation of weighted cones | `IsWeightedLimit_cov_comp F W L` |
| $\operatorname{Cocone}_W(F)$ | the opposite-dual weighted-cocone profunctor | `WeightedCocone_prof F W` |
| $A\star B$ | directed join with left-to-right cross arrows | `Join_cat A B` |

The bounded executable text bridge uses four intrinsic categorical lambda
modes:

```text
λ^f  x : A. ...
λ^n  k : K. ...
λ^fd a : E. ...
λ^nd k : K. ...
```

The superscript belongs to the lambda: it specifies ordinary functorial,
natural/indexed, displayed-functorial, or displayed-natural variation. The
classifier annotation after the variable may be omitted when an expected
classifier supplies it bidirectionally, but the binder mode itself is not
inferred from that annotation. Thus the book's mathematical telescope
declaration $k:^{n}K$ corresponds to binding with `λ^n k : K. ...`; the two
notations have the same mode reading without being character-for-character
surface syntax. Ordinary object binding in the outer logical framework uses
its ordinary dependent lambda rather than a categorical `^o` mode.

Composition is written in diagrammatic reading order as $g\circ f$: first
$f$, then $g$. For the concrete model $\mathsf{BNat}$, this agrees with the
implemented convention $g\circ f=g+f$, where Nat addition recurses in its
left argument.

The two star actions are deliberately variance-separated. If $g:w\to x$ and
$u:x\to y$, then $u_*(g):w\to y$. If $u:x\to y$ and $h:y\to z$, then
$u^*(h):x\to z$. Thus the formula $f^*(g)=g\circ f$ names
**precomposition** and belongs to `hom_precomp_along_*`; it is not the
postcomposition owner with a typographic variation.

These formulas are categorical, not specifically functor-categorical. Their
general reading takes $w,x,y,z$ to be objects and the displayed arrows to be
arrows of an arbitrary ambient category $K$. The specialization
$K=\mathsf{Cat}$ makes those objects categories and those arrows functors;
that is the currently checked product/projection instance used in Chapter 9.

$\mathsf{Path}(A)$ denotes the equality-path category on a carrier $A$. It
must not be confused with a directed hom-category. In particular, the objects
of $H_x$ are arrows of $W$, whereas arrows of $H_x$ are directed
2-cells between those arrows.

> **Formal status — mathematical development with a checked executable
> subset.** The four categorical binder spellings, neutral application, and
> selected structural forms are implemented only for the reviewed profiles.
> The rest of the appendix remains mathematical notation, not an assertion
> that the complete book grammar is parsed.
<!-- /book-source:appendix-notation -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:appendix-evidence book/appendices/b-emdash-evidence.md -->
<a id="appendix-evidence"></a>

# Appendix B. Emdash Evidence

The prose cites stable evidence IDs rather than brittle line numbers. The
register behind this appendix names a claim's status, its active owner, and
the diagnostic or reviewer surface that exercises it. During assembly, the
table below is generated directly from `book/evidence.json`; editing the
table here is therefore neither necessary nor possible.

An **owner** is the declaration that supplies the interface used by the book.
A **reviewer/check** is a separate executable occurrence or deliberately
searched check phrase. “Formal consequence” rows name checked premises but
also say that the displayed theorem has not yet been packaged. “Research
boundary” rows deliberately have no purported proof owner.

> **Formal status — checked.** This appendix describes traceability; the
> [accompanying emdash artifact](#ref-emdash-artifact) remains the proof
> authority. The evidence checker validates every row before this generated
> view is assembled.

| Evidence | Status | Claim | Owners | Reviewer/check evidence |
| --- | --- | --- | --- | --- |
| `TT-EQUALITY-INDUCTION` | checked | The equality-local foundation has reflexivity, right-based dependent equality induction, nondependent path action, and dependent path action. | `eq_refl`<br><small>`emdash3_2.lp`</small><br>`ind_eqr`<br><small>`emdash3_2.lp`</small><br>`eq_ap`<br><small>`emdash3_2.lp`</small><br>`eq_apd`<br><small>`emdash3_2.lp`</small> | `eq_apd`<br><small>`examples/path_category.lp`</small> |
| `TT-ELEMENTARY-INDUCTION` | checked | Empty, Unit, Bool, and Nat have decoded classifiers, and the nontrivial elementary inductive carriers have dependent eliminators with constructor computation. | `Empty_grpd`<br><small>`emdash3_2.lp`</small><br>`Unit_grpd`<br><small>`emdash3_2.lp`</small><br>`Bool_grpd`<br><small>`emdash3_2.lp`</small><br>`Nat_grpd`<br><small>`emdash3_2.lp`</small><br>`empty_elim`<br><small>`emdash3_2.lp`</small><br>`bool_elim`<br><small>`emdash3_2.lp`</small><br>`nat_elim`<br><small>`emdash3_2.lp`</small> | `nat_elim`<br><small>`emdash3_2_checks.lp`</small> |
| `TT-SIGMA-PI-PATHS` | checked | The groupoid layer has dependent-pair and dependent-function classifiers, observational Sigma paths, and a checked happly/funext equivalence for Pi paths. | `sigma_Fst`<br><small>`emdash3_2.lp`</small><br>`sigma_Snd`<br><small>`emdash3_2.lp`</small><br>`PiHapply`<br><small>`emdash3_2.lp`</small><br>`PiFunext`<br><small>`emdash3_2.lp`</small><br>`pi_happly_type_equiv`<br><small>`emdash3_2.lp`</small> | `PiFunext`<br><small>`examples/pi_funext.lp`</small> |
| `CAT-ITERATED-HOMS` | checked | A category has an object classifier and category-valued homs, so higher cells are represented by iterating Hom. | `Cat`<br><small>`emdash3_2.lp`</small><br>`Obj`<br><small>`emdash3_2.lp`</small><br>`Hom`<br><small>`emdash3_2.lp`</small> | `Hom`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-PATH-CATEGORY` | checked | Path(A) internalizes equality as a groupoidal category, and an ordinary function induces an iterable functor between path categories. | `Path_cat`<br><small>`emdash3_2.lp`</small><br>`Path_cat_func`<br><small>`emdash3_2.lp`</small><br>`path_map_func`<br><small>`emdash3_2.lp`</small> | `path_map_func`<br><small>`examples/path_category.lp`</small> |
| `CAT-FUNCTOR-CALCULUS` | checked | Ordinary functors expose object and iterated-hom action, with generic identity and composition computation rather than constructor-specific functor laws. | `Functor`<br><small>`emdash3_2.lp`</small><br>`fapp0`<br><small>`emdash3_2.lp`</small><br>`fapp1_func`<br><small>`emdash3_2.lp`</small><br>`fapp1_fapp0`<br><small>`emdash3_2.lp`</small><br>`id_func`<br><small>`emdash3_2.lp`</small><br>`comp_cat_fapp0`<br><small>`emdash3_2.lp`</small> | `fapp1_fapp0`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-PRODUCT-CALCULUS` | checked | Binary product categories have projection functors and a stable two-sided product-map constructor whose object, arrow, and projection observations compute componentwise. | `Product_cat`<br><small>`emdash3_2.lp`</small><br>`Product_projL_func`<br><small>`emdash3_2.lp`</small><br>`Product_map_func`<br><small>`emdash3_2.lp`</small> | text `product/projection cut used by the book`<br><small>`emdash3_2_checks.lp`</small><br>text `General two-sided product maps used by profunctor reindexing`<br><small>`emdash3_2_checks.lp`</small> |
| `CUT-PRODUCT-PROJECTION` | formal-consequence | In the Cat-specialized case, for h:A0→A1, k:B0→B1, and g:A1→C, the readable equation pi1^*(g) composed with h×k equals pi1'^*(g composed with h); its owner-aligned projection and nested-precomposition forms are checked, while the literal raw projection-composite equality is not packaged. | `hom_precomp_along_fapp0`<br><small>`emdash3_2.lp`</small><br>`Product_projL_func`<br><small>`emdash3_2.lp`</small><br>`Product_map_func`<br><small>`emdash3_2.lp`</small><br>`comp_assoc`<br><small>`emdash3_2.lp`</small> | text `product/projection cut used by the book`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-HOM-CUTS` | checked | Represented-hom postcomposition and precomposition have distinct stable full and capped owners with identity, consecutive-action, adjacent-cut, and proof-time ordinary-composition comparisons. | `hom_postcomp_func`<br><small>`emdash3_2.lp`</small><br>`hom_postcomp_fapp0`<br><small>`emdash3_2.lp`</small><br>`hom_precomp_along_func`<br><small>`emdash3_2.lp`</small><br>`hom_precomp_along_fapp0`<br><small>`emdash3_2.lp`</small> | text `Hom-action functoriality joins for postcomposition`<br><small>`emdash3_2_checks.lp`</small><br>text `Hom-action functoriality joins for precomposition`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-TRANSFOR-CALCULUS` | checked | Transformations form the next hom between functors and expose point components together with higher naturality action. | `Transf`<br><small>`emdash3_2.lp`</small><br>`tapp0_fapp0`<br><small>`emdash3_2.lp`</small><br>`tapp1_fapp0`<br><small>`emdash3_2.lp`</small> | `tapp1_fapp0`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-DIRECTED-FAMILIES` | checked | A Cat-valued directed family has fibres and functorial reindexing, while a family morphism has fibre functors and directed comparison cells. | `Catd`<br><small>`emdash3_2.lp`</small><br>`Fibre_cat`<br><small>`emdash3_2.lp`</small><br>`catd_transport_func`<br><small>`emdash3_2.lp`</small><br>`Functord`<br><small>`emdash3_2.lp`</small><br>`fdapp1_int_cell`<br><small>`emdash3_2.lp`</small> | `fdapp1_int_cell`<br><small>`examples/dependent_hom_laxity.lp`</small> |
| `CAT-SIGMA-PI` | checked | Directed families have a Sigma total category, canonical transport arrows, and a Pi section category with coherent evaluation. | `Sigma_cat`<br><small>`emdash3_2.lp`</small><br>`sigma_transport_arrow`<br><small>`emdash3_2.lp`</small><br>`Pi_cat`<br><small>`emdash3_2.lp`</small><br>`piapp0`<br><small>`emdash3_2.lp`</small> | `sigma_transport_arrow`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-FIBREWISE-CONTEXT` | checked | Fixed-base fibrewise products of displayed families have displayed projections and pairing whose fibre, base-arrow, internalized-cell, higher, and projection-after-pairing observations compute componentwise; swap and diagonal are derived from those owners. | `Product_projL_funcd`<br><small>`emdash3_2.lp`</small><br>`Product_projR_funcd`<br><small>`emdash3_2.lp`</small><br>`Product_pair_funcd`<br><small>`emdash3_2.lp`</small> | `Product_projL_funcd_higher_check`<br><small>`emdash3_2_checks.lp`</small><br>`Product_projR_funcd_higher_check`<br><small>`emdash3_2_checks.lp`</small><br>`Product_pair_funcd_higher_check`<br><small>`emdash3_2_checks.lp`</small><br>text `The canonical internalized cell of displayed pairing is componentwise.`<br><small>`emdash3_2_checks.lp`</small><br>text `Whole displayed universal-property betas.`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-BASE-CHANGE-TOTALIZATION` | checked | Pullback totalization sends a base-changed dependent pair `(a,u)` to `(F[a],u)` and sends its total arrow by the functorial base action while retaining the fibre component. | `sigma_pullback_total_func`<br><small>`emdash3_2.lp`</small> | text `Pullback totalization exposes exactly its base-changed dependent pair.`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-DISPLAYED-EVALUATION` | checked | Constant-domain displayed evaluation projects fibrewise to ordinary functor evaluation and retains generic base/higher action, while displayed terminal weakening projects to the ordinary terminal functor. | `Eval_funcd`<br><small>`emdash3_2.lp`</small><br>`Terminal_funcd`<br><small>`emdash3_2.lp`</small> | text `The stable displayed evaluator projects to ordinary product evaluation.`<br><small>`emdash3_2_checks.lp`</small><br>`Displayed_eval_higher_check`<br><small>`emdash3_2_checks.lp`</small><br>text `Displayed terminal weakening projects to the ordinary unique functor.`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-REPRESENTABLE` | checked | The fixed-source representable family has fibre Hom(x,y), and its source action is precomposition. | `Rep_catd`<br><small>`emdash3_2.lp`</small><br>`Rep_transport_func`<br><small>`emdash3_2.lp`</small> | `Rep_catd`<br><small>`examples/path_induction_transitivity.lp`</small> |
| `LOGIC-TRUNCATION-PREDICATE` | checked | Contractibility and recursive truncation evidence define the proposition, set, and groupoid levels as properties of existing classifiers. | `IsContr`<br><small>`emdash3_2.lp`</small><br>`IsTruncGrpd`<br><small>`emdash3_2.lp`</small><br>`IsPropGrpd`<br><small>`emdash3_2.lp`</small><br>`IsSetGrpd`<br><small>`emdash3_2.lp`</small> | `IsTruncGrpd`<br><small>`examples/truncation_monotonicity.lp`</small> |
| `LOGIC-NAT-SETHOOD` | checked | Unit and Empty are proposition-valued and Nat is set-valued by explicit internal evidence. | `unit_is_prop`<br><small>`emdash3_2_nat_arithmetic.lp`</small><br>`empty_is_prop`<br><small>`emdash3_2_nat_arithmetic.lp`</small><br>`nat_is_set`<br><small>`emdash3_2_nat_arithmetic.lp`</small> | `nat_is_set`<br><small>`examples/walking_endomorphism_nat_prerequisites.lp`</small> |
| `LOGIC-TRUNCATION-EVIDENCE-PROP` | checked | For every truncation level and classifier, the classifier of truncation evidence is proposition-valued. | `is_trunc_grpd_evidence_is_prop`<br><small>`emdash3_2.lp`</small> | `is_trunc_grpd_evidence_is_prop`<br><small>`examples/truncation_evidence_property.lp`</small> |
| `EQUIV-TYPE` | checked | TypeEquiv packages a forward map with contractible homotopy fibres and exposes a selected inverse with both inverse paths. | `HFiber`<br><small>`emdash3_2.lp`</small><br>`IsEquivMap`<br><small>`emdash3_2.lp`</small><br>`TypeEquiv`<br><small>`emdash3_2.lp`</small><br>`type_equiv_from`<br><small>`emdash3_2.lp`</small><br>`type_equiv_left`<br><small>`emdash3_2.lp`</small><br>`type_equiv_right`<br><small>`emdash3_2.lp`</small> | `TypeEquiv`<br><small>`examples/type_equiv_algebra.lp`</small> |
| `EQUIV-TYPE-ALGEBRA` | checked | Type equivalences have reflexivity, symmetry, and categorical-order composition with checked forward-map computation. | `type_equiv_refl`<br><small>`emdash3_2.lp`</small><br>`type_equiv_sym`<br><small>`emdash3_2.lp`</small><br>`type_equiv_comp`<br><small>`emdash3_2.lp`</small> | `type_equiv_comp`<br><small>`examples/type_equiv_algebra.lp`</small> |
| `UNIV-GROUPOID` | checked | The groupoid universe has a decoder-oriented univalence equivalence between universe paths and TypeEquiv, with named round trips and transport agreement. | `grpd_univalence_type_equiv`<br><small>`emdash3_2.lp`</small><br>`grpd_equiv_path`<br><small>`emdash3_2.lp`</small><br>`grpd_equiv_path_idtoequiv`<br><small>`emdash3_2.lp`</small><br>`idtoequiv_grpd_equiv_path`<br><small>`emdash3_2.lp`</small> | `grpd_univalence_from_decoder`<br><small>`examples/grpd_univalence_decoder.lp`</small> |
| `UNIV-TRUNCATED` | checked | For packaged n-truncated classifiers, package equality is equivalent to TypeEquiv of the retained carriers, with named encode/decode round trips. | `trunc_grpd_univalence_type_equiv`<br><small>`emdash3_2.lp`</small><br>`trunc_grpd_idtoequiv`<br><small>`emdash3_2.lp`</small><br>`trunc_grpd_equiv_path`<br><small>`emdash3_2.lp`</small> | `trunc_grpd_univalence_type_equiv`<br><small>`examples/truncation_universe_univalence.lp`</small> |
| `EQUIV-OMEGA` | checked | OmegaEquivAlong carries equality-valued inverse-arrow data, OmegaEquiv packages a selected arrow, and an object path has a transparent computational equivalence package. | `OmegaEquivAlong`<br><small>`emdash3_2.lp`</small><br>`OmegaEquiv`<br><small>`emdash3_2.lp`</small><br>`object_path_equiv`<br><small>`emdash3_2.lp`</small> | `object_path_equiv`<br><small>`examples/equality_valued_omega_equivalence.lp`</small> |
| `EQUIV-EVIDENCE-PROP` | checked | For every fixed arrow, its equality-valued OmegaEquivAlong evidence is proposition-valued without a finite-dimensional hypothesis. | `omega_equiv_along_evidence_is_prop`<br><small>`emdash3_2_eq1_evidence_property.lp`</small> | `omega_equiv_along_evidence_is_prop`<br><small>`examples/equality_valued_omega_equivalence_evidence_property.lp`</small> |
| `EQUIV-HOM-ACTION` | checked | Equality-valued equivalence evidence has a one-way next-hom action, and coherent groupoidality makes directed fibre transport an equivalence. | `omega_equiv_along_fapp1`<br><small>`emdash3_2_eq1_hom_action.lp`</small><br>`groupoidal_fibre_transport_equiv`<br><small>`emdash3_2_eq1_hom_action.lp`</small> | `omega_equiv_along_fapp1`<br><small>`examples/equality_valued_omega_equivalence_hom_action.lp`</small> |
| `EQUIV-ORDINARY-ISO-LIFT` | checked | Ordinary categorical isomorphism evidence has a one-way lift to the native equality-valued OmegaEquiv package. | `IsoEvidence`<br><small>`emdash3_2.lp`</small><br>`iso_evidence_omega_equiv`<br><small>`emdash3_2.lp`</small> | `iso_evidence_omega_equiv`<br><small>`emdash3_2_checks.lp`</small> |
| `UNIV-FULL-OBJECT-ISO` | research-boundary | A full native equivalence between arbitrary categorical object equality and ordinary isomorphism evidence is not part of the selected API. | — | — |
| `IND-PATHOUT` | checked | PathOut_Z(x) is the Sigma total of the fixed-source representable, with a reflexive object and a canonical rho arrow to every outgoing arrow. | `PathOut_cat`<br><small>`emdash3_2.lp`</small><br>`pathout_refl_obj`<br><small>`emdash3_2.lp`</small><br>`pathout_refl_arrow`<br><small>`emdash3_2.lp`</small> | `pathout_refl_arrow`<br><small>`emdash3_2_checks.lp`</small> |
| `IND-ARROW` | checked | Fixed-source arrow induction extends data at the reflexive outgoing arrow to a section, and the theorem is internalized functorially as fixed-source and varying-source interfaces. | `path_ind_sec`<br><small>`emdash3_2.lp`</small><br>`PathInd_func`<br><small>`emdash3_2.lp`</small><br>`PathInd_transfd`<br><small>`emdash3_2.lp`</small> | `path_ind_sec`<br><small>`examples/path_induction_transitivity.lp`</small> |
| `IND-COMPOSITION` | checked | Applying arrow induction to the represented composition motive yields a functor whose object action computes to categorical composition. | `CompMotive_catd`<br><small>`emdash3_2.lp`</small><br>`path_comp_sec`<br><small>`emdash3_2.lp`</small><br>`path_comp_func`<br><small>`emdash3_2.lp`</small> | `path_comp_func`<br><small>`examples/path_induction_transitivity.lp`</small> |
| `IND-PATH-COMPARISON` | checked | For a literal path-category base, structured directed transport agrees propositionally with primitive right-based equality induction. | `path_cat_structured_transport_agrees_ind_eqr`<br><small>`emdash3_2.lp`</small> | `path_cat_structured_transport_agrees_ind_eqr`<br><small>`examples/groupoidal_structured_j_eq1.lp`</small> |
| `IND-GENERAL-INITIALITY` | research-boundary | A general theorem identifying all selected categorical induction interfaces with homotopy-initial algebras has not been packaged. | — | — |
| `DHIT-DERIVED-ELIMINATORS` | checked | The contextual WalkingEnd eliminator specializes to a dependent section and an ordinary recursor with base and generator observations. | `walking_end_ind_sec`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_end_rec_func`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_end_rec_beta_base`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_end_rec_beta_loop_ordinary`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_end_rec_func`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `DHIT-GENERAL-SCHEMA` | research-boundary | The selected WalkingEnd interface does not yet constitute a reusable schema for arbitrary directed higher-inductive categories, pushouts, or cell complexes. | — | — |
| `TRUNC-CLOSURE` | checked | Recursive truncation evidence is monotone and has checked dependent Pi and same-level dependent Sigma closure operations. | `is_trunc_grpd_succ`<br><small>`emdash3_2.lp`</small><br>`is_trunc_pi`<br><small>`emdash3_2.lp`</small><br>`is_trunc_sigma`<br><small>`emdash3_2.lp`</small> | `is_trunc_pi`<br><small>`examples/truncation_pi_closure.lp`</small><br>`is_trunc_sigma`<br><small>`examples/truncation_sigma_closure.lp`</small> |
| `TRUNC-RETRACT` | checked | Every recursive truncation level is closed under explicit retractions. | `is_trunc_retract`<br><small>`emdash3_2_eq1_evidence_property.lp`</small> | `is_trunc_retract`<br><small>`emdash3_2_checks.lp`</small> |
| `CAT-DIMENSION` | checked | IsNCat defines finite directed height by hom recursion, and every such category has the recursively predicted object-truncation evidence. | `IsNCat`<br><small>`emdash3_2.lp`</small><br>`cat_dim_trunc_level`<br><small>`emdash3_2.lp`</small><br>`ncat_obj_trunc`<br><small>`emdash3_2_eq1_evidence_property.lp`</small> | `IsNCat`<br><small>`examples/directed_dimension.lp`</small><br>`ncat_obj_trunc`<br><small>`examples/equality_valued_omega_equivalence_evidence_property.lp`</small> |
| `TRUNC-REFLECTOR` | research-boundary | The active truncation layer supplies properties and packaged truncated universes, not a general truncation reflector or arbitrary truncation HIT. | — | — |
| `WE-SIGNATURE` | checked | WalkingEnd has an opaque category, base, directed loop, and explicit one-dimensional evidence. | `WalkingEnd_cat`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_base`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_loop`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_end_is_one_cat`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_end_is_one_cat`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-ONE-DIMENSIONAL` | checked | Every WalkingEnd hom-category is discrete, without WalkingEnd itself becoming discrete. | `walking_end_hom_discrete`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_end_hom_discrete`<br><small>`emdash3_2_checks.lp`</small> |
| `WE-CONTEXTUAL-ELIMINATOR` | checked | The contextual WalkingEnd eliminator has base and loop computation at the selected displayed observers. | `walking_end_ind_funcd`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_end_ind_funcd_beta_base`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_end_ind_funcd_beta_loop`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_end_ind_funcd`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-BNAT-MODEL` | checked | BNat is a separate one-object Nat-monoid model and receives a functor from WalkingEnd. | `BNat_cat`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`bnat_comp_nat_add`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_bnat_model_func`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_bnat_model_func`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-CODE` | checked | Code sends the walking base to Path(Nat) and the walking loop to the Nat successor functor. | `walking_Code_catd`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_Code_beta_base`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_Code_beta_loop`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_Code_catd`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-ENCODE` | checked | Encode acts with Code on a based arrow and evaluates at zero. | `walking_encode`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_encode`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-POWER` | checked | Natural powers map zero to identity and successor to generator-prefix composition. | `walking_power`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_power_func`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_power`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-SPIRAL` | checked | The selected explicit-kappa directed spiral supplies the loop coherence for powers. | `walking_power_spiral`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_power_spiral_cell`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_power_spiral_cell`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-CONTEXTUAL-DECODER` | checked | The contextual decoder maps Code to the based representable and computes to powers at the base. | `walking_directed_decode_funcd`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_directed_decode_beta_base`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_directed_decode_funcd`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-NORMALIZATION-CELL` | checked | Every based arrow has a directed normalization cell toward decode(encode(p)). | `walking_directed_normalization_cell`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_directed_normalization_cell`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-NORMALIZATION-PATH` | checked | Hom-discreteness converts the directed normalization cell into equality. | `walking_directed_normalization_path`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_directed_normalization_path`<br><small>`emdash3_2_checks.lp`</small> |
| `WE-POWER-ENCODE` | checked | For a based endomorphism p, power(encode(p)) equals p. | `walking_power_encode_roundtrip`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_power_encode_roundtrip`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-ENCODE-POWER` | checked | For every natural n, encode(power(n)) equals n. | `walking_encode_power_roundtrip`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_encode_power_roundtrip`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-HOM-NAT-CARRIER` | checked | The underlying based-endomorphism carrier is equivalent to Nat. | `walking_hom_nat_type_equiv`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_hom_nat_omega_equiv`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_hom_nat_type_equiv`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-HOM-SETHOOD` | checked | The based-endomorphism carrier is a set both from dimension and from the Nat equivalence. | `walking_end_hom_is_set_from_dimension`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_end_hom_is_set_from_equiv`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_end_hom_is_set_from_dimension`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-LOOP-NOT-IDENTITY` | checked | The walking generator is not equal to the identity. | `walking_loop_not_identity`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_loop_not_identity`<br><small>`emdash3_2_checks.lp`</small> |
| `WE-LOOP-NO-RIGHT-INVERSE` | checked | The walking generator has no right inverse. | `walking_loop_no_right_inverse`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_loop_no_right_inverse`<br><small>`emdash3_2_checks.lp`</small> |
| `WE-LOOP-NONINVERTIBLE` | checked | The walking generator carries no native omega-equivalence evidence. | `walking_loop_not_omega_equiv`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_loop_not_omega_equiv`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-ENCODE-PREFIX` | checked | Encoding a generator-prefixed based endomorphism produces the successor of its code. | `walking_encode_loop_prefix_path`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_encode_loop_prefix_path`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-STRUCTURED-ENCODER` | checked | The based encoder is also packaged as a functor from the based hom-category to Path(Nat). | `walking_encode_func`<br><small>`emdash3_2_walking_end_hit.lp`</small> | `walking_encode_func`<br><small>`examples/walking_endomorphism_hit.lp`</small> |
| `WE-COMPOSITION-ADDITION` | formal-consequence | Compatibility of based composition with Nat addition follows from the checked power recursion, inverse laws, and ordinary category/Nat induction, but is not packaged as a monoid equivalence. | `walking_encode_loop_prefix_path`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_power_encode_roundtrip`<br><small>`emdash3_2_walking_end_hit.lp`</small><br>`walking_encode_power_roundtrip`<br><small>`emdash3_2_walking_end_hit.lp`</small> | — |
| `WE-FULL-CATEGORICAL-COMPARISON` | research-boundary | A reverse BNat functor, full hom-category equivalence, and functor-category initiality require additional reusable infrastructure. | — | — |
| `WE-GROUP-COMPLETION` | research-boundary | Group completion toward BInt or the circle comparison has not been implemented. | — | — |
| `TRANSF-POINT-OFFDIAGONAL` | checked | An ordinary transfor has point components and an iterable off-diagonal hom action from F(x) to G(y) along every source arrow x to y. | `Transf_cat`<br><small>`emdash3_2.lp`</small><br>`tapp0_fapp0`<br><small>`emdash3_2.lp`</small><br>`tapp1_func`<br><small>`emdash3_2.lp`</small><br>`tapp1_fapp0`<br><small>`emdash3_2.lp`</small> | `tapp1_at_transf`<br><small>`emdash3_2_checks.lp`</small> |
| `TRANSF-STRICT-NATURALITY` | checked | Postcomposition and precomposition adjacent to an ordinary transfor's off-diagonal action reduce to the action on the corresponding composite source arrow. | text `Full strict naturality for ordinary transfors`<br><small>`emdash3_2.lp`</small> | text `Full strict naturality: post/left accumulation before capping`<br><small>`emdash3_2_checks.lp`</small> |
| `TRANSF-HORIZONTAL-CALCULUS` | checked | The product-composition action supplies an iterable horizontal composite of a pair of ordinary transfors, with checked point, full off-diagonal, and capped off-diagonal projections. | `comp_prod_fapp1_fapp0`<br><small>`emdash3_2.lp`</small> | `comp_prod_fapp1_fapp0`<br><small>`emdash3_2_checks.lp`</small> |
| `TRANSFD-FIBRE-COMPONENTS` | checked | A natural family transformation between displayed functors has a transformation in every fibre and a point component at every fibre object, with identity and vertical composition inherited from the generic transfor calculus. | `Transfd_cat`<br><small>`emdash3_2.lp`</small><br>`Fibre_transf`<br><small>`emdash3_2.lp`</small><br>`Fibre_transf_app`<br><small>`emdash3_2.lp`</small> | `Fibre_transf_app`<br><small>`emdash3_2_checks.lp`</small> |
| `FUNCTORD-DISPLAYED-LAXITY` | checked | For a natural family morphism and a base arrow, the internal displayed hom action supplies a directed component from target transport after the source fibre functor to the target fibre functor after source transport. | `functord_transport_lhs_func`<br><small>`emdash3_2.lp`</small><br>`functord_transport_rhs_func`<br><small>`emdash3_2.lp`</small><br>`fdapp1_int_cell`<br><small>`emdash3_2.lp`</small> | `fdapp1_int_cell`<br><small>`examples/dependent_hom_laxity.lp`</small> |
| `FUNCTORD-SIGMA-ACTION` | checked | The Sigma-total map induced by a natural family morphism sends a total arrow to the same base arrow paired with the capped internal displayed hom action in the fibre. | `sigma_map_func`<br><small>`emdash3_2.lp`</small><br>`fdapp1_int_hom_fapp0`<br><small>`emdash3_2.lp`</small> | `sigma_map_transf`<br><small>`examples/sigma_total.lp`</small> |
| `FUNCTORD-WHOLE-LAXITY` | research-boundary | A standalone whole-transfor laxity facade between the two transport composites is intentionally deferred; the active owner is the internal displayed hom action and its component projections. | — | — |
| `PROF-CATEGORY` | checked | A Cat-valued profunctor from A to B is a directed family on A opposite times B, and vertical profunctor maps are natural family morphisms with the existing identity and composition calculus. | `Prof_base`<br><small>`emdash3_2.lp`</small><br>`Prof_cat`<br><small>`emdash3_2.lp`</small><br>`ProfMap`<br><small>`emdash3_2.lp`</small> | text `Cat-valued profunctor facade and representable hom action`<br><small>`emdash3_2_checks.lp`</small> |
| `PROF-REPRESENTABLE` | checked | The unit profunctor evaluates to the ambient hom, and reindexing it along endpoint functors gives the binary representable with action by precomposition and postcomposition. | `Unit_prof`<br><small>`emdash3_2.lp`</small><br>`Hom_prof_along`<br><small>`emdash3_2.lp`</small><br>`Hom_fapp0`<br><small>`emdash3_2.lp`</small> | `Hom_prof_along`<br><small>`emdash3_2_checks.lp`</small> |
| `PROF-REINDEXING` | checked | Profunctors reindex functorially in both endpoints by pullback along an opposite-times-covariant product map, including identity, nesting, and representable accumulation laws. | `Prof_reindex`<br><small>`emdash3_2.lp`</small><br>`Prof_reindex_func`<br><small>`emdash3_2.lp`</small> | text `Stable profunctor reindexing and its representable fold`<br><small>`emdash3_2_checks.lp`</small> |
| `PROF-REPRESENTATION-PACKAGE` | checked | Representability of a profunctor is expressible as ordinary isomorphism to a conjoint, and a representation package retains a chosen representing functor with that evidence. | `Conjoint_prof`<br><small>`emdash3_2.lp`</small><br>`IsRepresentedBy_iso`<br><small>`emdash3_2.lp`</small><br>`Representation_iso`<br><small>`emdash3_2.lp`</small> | `Representation_iso`<br><small>`emdash3_2_checks.lp`</small> |
| `PROF-COMPARISON-BETA-ETA` | checked | A computational profunctor comparison exposes mutually inverse push and pull operations on every incoming profunctor map, with runtime beta and eta reductions and functorial reindexing and composition. | `ProfComparison`<br><small>`emdash3_2.lp`</small><br>`prof_comparison_push`<br><small>`emdash3_2.lp`</small><br>`prof_comparison_pull`<br><small>`emdash3_2.lp`</small> | text `Computational profunctor comparisons and weighted representability`<br><small>`emdash3_2_checks.lp`</small><br>`prof_comparison_pull`<br><small>`emdash3_2_checks.lp`</small> |
| `PROF-SHAPED-CELLS` | checked | A profunctor cell over endpoint functors is a natural family morphism into a reindexed target; unit-source specialization and narrow cell application provide shaped elements and their action. | `Prof_transf_cat`<br><small>`emdash3_2.lp`</small><br>`Prof_hom`<br><small>`emdash3_2.lp`</small><br>`Prof_cell_apply`<br><small>`emdash3_2.lp`</small> | text `Shaped profunctor cells and elements`<br><small>`emdash3_2_checks.lp`</small> |
| `PROF-TENSOR` | checked | The selected profunctor tensor is an opaque fixed-middle composite with exposed-endpoint reindexing and a fixed-endpoint bifunctorial map action. | `Prof_tensor`<br><small>`emdash3_2.lp`</small><br>`Prof_tensor_func`<br><small>`emdash3_2.lp`</small><br>`Prof_tensor_hom_hom`<br><small>`emdash3_2.lp`</small> | text `Primitive profunctor tensor and exposed-endpoint reindexing`<br><small>`emdash3_2_checks.lp`</small><br>`Prof_tensor`<br><small>`examples/profunctor_weighted_limits.lp`</small> |
| `PROF-CLOSED-CALCULUS` | checked | The two selected profunctor residuals expose fixed-endpoint evaluation and lambda operations inverse by runtime beta and eta, without asserting semantic end formulas for their opaque objects. | `Prof_imply_cov`<br><small>`emdash3_2.lp`</small><br>`Prof_eval_cov_map`<br><small>`emdash3_2.lp`</small><br>`Prof_lambda_cov_map`<br><small>`emdash3_2.lp`</small><br>`Prof_imply_con`<br><small>`emdash3_2.lp`</small><br>`Prof_eval_con_map`<br><small>`emdash3_2.lp`</small><br>`Prof_lambda_con_map`<br><small>`emdash3_2.lp`</small> | `Prof_lambda_cov_map`<br><small>`emdash3_2_checks.lp`</small><br>`Prof_lambda_con_map`<br><small>`emdash3_2_checks.lp`</small><br>`Prof_lambda_cov_map`<br><small>`examples/profunctor_weighted_limits.lp`</small> |
| `PROF-COYONEDA` | checked | Tensoring on either side with the unit profunctor has a natural co-Yoneda map to the original profunctor, with fixed shaped-element beta and naturality-fusion computations. | `Prof_coyoneda_cov_transf`<br><small>`emdash3_2.lp`</small><br>`Prof_coyoneda_con_transf`<br><small>`emdash3_2.lp`</small><br>`Prof_coyoneda_cov_map`<br><small>`emdash3_2.lp`</small><br>`Prof_coyoneda_con_map`<br><small>`emdash3_2.lp`</small> | `Prof_coyoneda_cov_transf`<br><small>`emdash3_2_checks.lp`</small><br>`Prof_coyoneda_con_transf`<br><small>`emdash3_2_checks.lp`</small> |
| `PROF-GENERAL-COEND` | research-boundary | The selected opaque tensor and co-Yoneda computations do not yet provide a general coend or coinserter construction, tensor associativity package, or a bicategory of profunctors. | — | — |
| `YONEDA-FULLY-FAITHFUL` | research-boundary | The active representable and co-Yoneda interfaces do not yet package a general fully faithful Yoneda embedding or the full Yoneda equivalence for arbitrary Cat-valued presheaves. | — | — |
| `UCAT-IDENTITY-ISOMORPHISM` | mathematical-development | In the ordinary set-valued-hom specialization, a category is a precategory whose identity-to-isomorphism map is an equivalence; its object type is consequently a 1-type. | — | — |
| `UCAT-FUNCTOR-CATEGORY` | mathematical-development | An ordinary natural transformation is invertible exactly when its components are, and for a precategory A and univalent category B the functor precategory from A to B is univalent, with functor identity corresponding to natural isomorphism. | — | — |
| `UCAT-ADJOINT-REPRESENTABILITY` | mathematical-development | In ordinary univalent 1-category theory, right adjoints are equivalently coherent representations of the contravariant hom functors obtained by fixing the target of the left adjoint. | — | — |
| `UCAT-ADJOINT-UNIQUENESS` | mathematical-development | For an ordinary functor whose source is a univalent category, right-adjoint structures are unique in the appropriate identity sense and existence of a right adjoint is a mere proposition. | — | — |
| `UCAT-EQUIVALENCE-CRITERIA` | mathematical-development | Ordinary adjoint equivalences correspond to fully faithful and split essentially surjective functors, and between univalent categories mere essential surjectivity suffices. | — | — |
| `UCAT-CATEGORY-IDENTITY` | mathematical-development | Identity of ordinary precategories corresponds to isomorphism of precategories, and for univalent categories this agrees with categorical equivalence; the resulting type of categories is a 2-type. | — | — |
| `UCAT-YONEDA` | mathematical-development | The ordinary set-valued Yoneda evaluation map is an equivalence, making the Yoneda embedding fully faithful and representing objects unique up to isomorphism, hence up to identity in a univalent category. | — | — |
| `UCAT-STRICT-CATEGORY` | mathematical-development | An ordinary HoTT strict category is a precategory whose object type is a set; it need not be univalent, and an ordinary univalent category is strict exactly when it is gaunt. | — | — |
| `UCAT-DAGGER-CATEGORY` | mathematical-development | An ordinary dagger precategory has a chosen identity-on-objects contravariant involution; unitary arrows use the dagger as inverse, and dagger univalence identifies object identity with unitary isomorphism. | — | — |
| `UCAT-STRUCTURE-IDENTITY` | mathematical-development | For a standard proposition-valued notion of structure over an ordinary univalent category, the precategory of structured objects and structure-preserving arrows is itself univalent. | — | — |
| `UCAT-REZK-COMPLETION` | mathematical-development | Every ordinary precategory admits a fully faithful and essentially surjective map into a univalent category, constructible by a Yoneda image or a 1-truncated HIT; univalent categories are exactly the targets that invert all such weak equivalences by precomposition. | — | — |
| `NATIVE-DAGGER-INTERFACE` | research-boundary | The active opposite operation does not provide a chosen identity-on-objects involutive self-duality, coherent higher dagger action, a unitary classifier, or native dagger univalence. | — | — |
| `NATIVE-STRUCTURE-IDENTITY` | research-boundary | A generic native structure identity theorem requires a directed structure signature, a higher structure-preserving equivalence classifier, qualified base univalence, and coherent off-diagonal and next-hom action. | — | — |
| `NATIVE-REZK-COMPLETION` | research-boundary | No selected native saturation predicate, Rezk completion object, unit weak equivalence, or iterable higher mapping property is currently implemented. | — | — |
| `ADJ-TRIANGLE-CUTS` | checked | An indexed adjunction exposes stable unit and counit observations whose two component-level triangle cuts reduce to the corresponding functorial composites. | `Adjunction`<br><small>`emdash3_2.lp`</small><br>`unit_adj_transf`<br><small>`emdash3_2.lp`</small><br>`counit_adj_transf`<br><small>`emdash3_2.lp`</small> | `unit_adj_transf`<br><small>`examples/adjunction_triangles.lp`</small><br>text `Indexed adjunction triangles, opposite, and operation-trust boundary`<br><small>`emdash3_2_checks.lp`</small> |
| `ADJ-HOM-PROF-COMPARISON` | checked | An indexed adjunction supplies a reindexable profunctor comparison between Hom_B(LM,F) and Hom_A(M,RF), whose push and pull inherit the generic comparison beta and eta laws. | `Adjunction_hom_prof_comparison`<br><small>`emdash3_2.lp`</small><br>`Adjunction_hom_prof_comparison_along`<br><small>`emdash3_2.lp`</small> | `Adjunction_hom_prof_comparison_along`<br><small>`emdash3_2_checks.lp`</small> |
| `WEIGHTED-LIMIT-REPRESENTABILITY` | checked | A parameterized weighted-cone profunctor is formed by the selected covariant residual, and its computational representation by a functor exposes inverse push and pull operations on every reindexed incoming profunctor map. | `WeightedCone_prof`<br><small>`emdash3_2.lp`</small><br>`IsWeightedLimit_cov_iso`<br><small>`emdash3_2.lp`</small><br>`IsWeightedLimit_cov_comp`<br><small>`emdash3_2.lp`</small><br>`weighted_limit_cov_push`<br><small>`emdash3_2.lp`</small><br>`weighted_limit_cov_pull`<br><small>`emdash3_2.lp`</small> | text `Computational profunctor comparisons and weighted representability`<br><small>`emdash3_2_checks.lp`</small><br>`weighted_limit_cov_pull`<br><small>`emdash3_2_checks.lp`</small><br>`weighted_limit_cov_pull`<br><small>`examples/profunctor_weighted_limits.lp`</small> |
| `WEIGHTED-LIMIT-SPECIALIZATIONS` | formal-consequence | Terminal weights and conjoint weights inhabit the selected weighted-limit classifier, so the general right-adjoint preservation construction specializes to the corresponding conical-limit and right-Kan interfaces; this does not assert their missing semantic end identifications. | `Terminal_prof`<br><small>`emdash3_2.lp`</small><br>`Conjoint_prof`<br><small>`emdash3_2.lp`</small><br>`IsWeightedLimit_cov_comp`<br><small>`emdash3_2.lp`</small><br>`right_adjoint_preserves_weighted_limit_cov_comp`<br><small>`emdash3_2.lp`</small> | text `Weighted limit and colimit specialization typing`<br><small>`emdash3_2_checks.lp`</small> |
| `WEIGHTED-END-KAN-SEMANTICS` | mathematical-development | With semantic ends and coends, terminal weights recover ordinary cone and cocone categories while conjoint and companion weights recover the standard pointwise right and left Kan extension formulas. | — | — |
| `DEPENDENT-ADJUNCTIONS` | research-boundary | A general dependent Sigma-change-of-base-Pi adjunction chain requires base-arrow action, off-diagonal and next-hom coherence, and Beck-Chevalley comparisons beyond the current Sigma and Pi family interfaces. | — | — |
| `OP-DUALITY` | checked | Opposite category, functor, transfor, and adjunction operations expose the selected involutive and variance-reversing computations used by the duality arguments. | `Op_cat`<br><small>`emdash3_2.lp`</small><br>`Op_func`<br><small>`emdash3_2.lp`</small><br>`Op_transf`<br><small>`emdash3_2.lp`</small><br>`Op_adjunction`<br><small>`emdash3_2.lp`</small> | `Op_adjunction`<br><small>`emdash3_2_checks.lp`</small> |
| `WEIGHTED-LIMIT-PRESERVATION` | checked | The selected profunctor comparison certifying a weighted limit is transported by an indexed right adjoint to a weighted-limit comparison for the composed diagram and cone point. | `IsWeightedLimit_cov_comp`<br><small>`emdash3_2.lp`</small><br>`right_adjoint_preserves_weighted_limit_cov_comp`<br><small>`emdash3_2.lp`</small> | `right_adjoint_preserves_weighted_limit_cov_comp`<br><small>`emdash3_2_checks.lp`</small><br>`right_adjoint_preserves_weighted_limit_cov_comp`<br><small>`examples/profunctor_weighted_limits.lp`</small> |
| `WEIGHTED-COLIMIT-PRESERVATION` | checked | Weighted colimits are presented through opposite weighted limits, and the selected left-adjoint preservation certificate is derived by applying right-adjoint preservation to the opposite adjunction. | `WeightedColimit_con`<br><small>`emdash3_2.lp`</small><br>`left_adjoint_preserves_weighted_colimit_con`<br><small>`emdash3_2.lp`</small> | `left_adjoint_preserves_weighted_colimit_con`<br><small>`emdash3_2_checks.lp`</small> |
| `WEIGHTED-COLIMIT-SPECIALIZATIONS` | formal-consequence | Terminal weights and companion weights inhabit the selected opposite-defined weighted-colimit classifier, so left-adjoint preservation specializes to the corresponding conical-colimit and left-Kan interfaces without supplying semantic coend identifications. | `Terminal_prof`<br><small>`emdash3_2.lp`</small><br>`Companion_prof`<br><small>`emdash3_2.lp`</small><br>`WeightedColimit_con`<br><small>`emdash3_2.lp`</small><br>`left_adjoint_preserves_weighted_colimit_con`<br><small>`emdash3_2.lp`</small> | text `Weighted limit and colimit specialization typing`<br><small>`emdash3_2_checks.lp`</small> |
| `JOIN-RECURSOR` | checked | The primitive directed join has two inclusion functors, an internally natural cross cell, and a nondependent recursor with beta computation on both inclusions and the cross-cell datum. | `Join_cat`<br><small>`emdash3_2.lp`</small><br>`join_cross_transf`<br><small>`emdash3_2.lp`</small><br>`join_elim_func`<br><small>`emdash3_2.lp`</small><br>`join_elim_cross_transf`<br><small>`emdash3_2.lp`</small> | `join_elim_cross_transf`<br><small>`emdash3_2_checks.lp`</small><br>`join_elim_cross_transf`<br><small>`examples/directed_join.lp`</small> |
| `JOIN-COLLAGE-BOUNDARY` | research-boundary | The join recursor has the input shape of the collage of the terminal profunctor, but no object or hom decomposition, mapping-category equivalence, opposite comparison, or dependent collage eliminator is active. | — | — |
| `FORMAL-KERNEL-PRESENTATION` | checked | The active v3.2 modules expose categories, iterated homs, functors, transfors, and directed families through explicit classifiers and full or capped application owners, with executable assertions checking representative typing and computation. | `Cat`<br><small>`emdash3_2.lp`</small><br>`Hom_cat`<br><small>`emdash3_2.lp`</small><br>`fapp1_func`<br><small>`emdash3_2.lp`</small><br>`tapp1_func`<br><small>`emdash3_2.lp`</small><br>`Catd`<br><small>`emdash3_2.lp`</small> | `fapp1_fapp0`<br><small>`emdash3_2_checks.lp`</small><br>`tapp1_fapp0`<br><small>`emdash3_2_checks.lp`</small> |
| `FORMAL-ELABORATION-BOUNDARY` | research-boundary | The renewed TypeScript product implements a bounded direct-TypeScript and categorical-text path through scoped contextual elaboration, backend-neutral explicit Core, and a generic checker/evaluator, with optional Lambdapi conformance. A complete compiler for the book's canonical surface, arbitrary displayed coherence, and whole-library transfer are not claimed. | — | — |
| `FORMAL-METATHEORY-BOUNDARY` | research-boundary | Local source acceptance, diagnostics, warning inventories, and model examples do not establish global confluence, strong normalization, canonicity, decidability, consistency, or semantic soundness for the whole emdash rewrite and unification theory. | — | — |
| `EH-COMMUTATIVITY` | checked | Two 2-endomorphisms of an identity 1-cell commute in the selected Eckmann-Hilton slice. | `EH_comm`<br><small>`emdash3_2.lp`</small> | text `Eckmann-Hilton specialization`<br><small>`emdash3_2_checks.lp`</small> |
<!-- /book-source:appendix-evidence -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:appendix-hott book/appendices/c-hott-correspondence.md -->
<a id="appendix-hott-correspondence"></a>

# Appendix C. From The Circle To The Walking Endomorphism

The proof of Theorem 8.1 is inspired by the encode-decode calculation of the
loop space of the circle in the [*Homotopy Type Theory* book](#ref-hott-book).
This appendix
records the correspondence so that the analogy can guide the reader without
smuggling groupoidal assumptions into the directed theorem.

The source reference is revision
`578b85cc8d586b1677ec4335148adeb443057d24` of the HoTT Book
repository. The detailed, machine-readable adaptation ledger is
`book/references/third-party-sources.json`.

## C.1 The Rhetorical Spine

The HoTT calculation proceeds through four questions:

1. What are the evident powers of the loop, and how might a loop be assigned a
   winding number?
2. What does the classical free/universal-cover picture predict?
3. How can the cover be represented internally as a family?
4. How do encode and decode become inverse after the endpoint is generalized?

Chapter 8 retains that sequence. It changes the mathematical answer at every
point where the circle proof uses reversibility.

| Circle calculation | Walking-endomorphism calculation |
| --- | --- |
| A base point and an identity loop in `S¹` | A base object and a directed arrow `ell` in `W` |
| Loop carrier `base = base` | Based hom carrier `Hom_W(*,*)` |
| Integer-indexed positive and negative powers | Natural-number-indexed forward powers |
| A cover with integer fibre | A Cat-valued code with `Path(Nat)` base fibre |
| Successor equivalence on integers | Successor functor on naturals |
| A universe path obtained through univalence | A directed endofunctor accepted directly by recursion into `Cat` |
| Transport zero along an identity path | Apply the Code functor to zero along a directed arrow |
| Decode by dependent circle induction | Decode by the contextual displayed eliminator |
| Hard inverse by generalized path induction | Directed normalization cell, then hom-discreteness |
| Easy inverse by integer/circle induction | Easy inverse by Nat induction |
| `Omega(S¹) ≃ Int` | `Hom_W(*,*) ≃ Nat` as carriers |
| Group structure and inverse loops | Free-monoid direction and a noninvertible generator |

The table is a dependency map, not a dictionary identifying the objects.

## C.2 Where Univalence Moves

In the circle proof, a family $\mathsf{Code}:S^1\to\mathsf{Type}$ must map the loop of
`S¹` to a loop in the universe. Successor on the integers is an
equivalence, and univalence converts that equivalence into the needed universe
identity. Its inverse supplies predecessor action.

In the directed proof,

$$
\mathsf{Code}:W\longrightarrow\mathsf{Cat}
$$

is specified by a category and an endofunctor. Natural-number successor is
therefore accepted without being an equivalence. No universe identity and no
predecessor are needed.

This does not make univalence irrelevant to functorial type theory. It
clarifies its jurisdiction. Equality, transport, equivalence, and univalent
universes govern groupoidal identification. A directed family may additionally
act along arrows that are not identities and whose action is not invertible.
The title of this book refers to a foundation containing both layers.

> **Formal status — mathematical development.** The comparison of the roles
> of univalence is explanatory. The individual emdash interfaces cited by
> Chapter 8 are checked; a general metatheorem comparing all directed families
> with HoTT fibrations is not claimed.

## C.3 The Generalized Endpoint

Both proofs teach the same strategic lesson in different formal languages:
when a statement about a fixed loop cannot be inducted on, vary its endpoint.

For the circle, one considers all `x:S¹` and paths
`base=x`. For `W`, one considers all objects `x`
and based arrows $*\to x$. The target family is the representable

$$
x\longmapsto\operatorname{Hom}_W(*,x).
$$

The crucial difference is what generalized elimination produces. Groupoidal
path induction produces equality. The contextual directed eliminator first
produces coherent arrow action, and at an arbitrary based arrow it yields a
directed 2-cell

$$
p\longrightarrow
\mathsf{decode}_x(\mathsf{encode}_x(p)).
$$

Only the separate one-dimensionality premise converts that cell into
equality. Thus the directed proof factors the groupoidal conclusion into two
conceptually independent steps: normalization and dimension.

## C.4 What Was Not Transferred

The adaptation removes, rather than renames, the following ingredients:

- inverse paths and negative powers;
- predecessor action on the code;
- the claim that successor is an equivalence;
- a universe path produced from successor;
- cancellation in a group;
- equality as the first output of the hard inverse;
- the conclusion that the result is already a group isomorphism.

It also adds ingredients absent from the circle proof in this form:

- a separate `BNat` model whose definitional structure is not imposed
  on the HIT;
- a displayed contextual algebra comparing postcomposition with successor;
- a coherent directed spiral;
- a dimension witness used explicitly at the equality boundary;
- negative results proving the generator has no right inverse or
  omega-equivalence evidence.

These changes explain why a textual search-and-replace from
`S¹/Int` to `W/Nat` would be mathematically misleading.

## C.5 Stronger Comparisons

The carrier equivalence suggests two future constructions.

First, composition/addition compatibility should package the comparison as a
monoid isomorphism. Chapter 8 records this as a formal consequence of the
checked recursion and inverse laws, but the library does not yet expose the
package.

Second, group completion should freely invert the generator. Only after that
construction is available should one compare the result with an integer
one-object category or the circle’s loop object. Such a comparison must state
whether it concerns carriers, monoids, categories, or a universal property.

> **Formal status — research boundary.** A reverse `BNat` functor,
> full categorical initiality, group completion, and the precise
> `BInt`/circle bridge remain future work.

## C.6 Attribution Method

The subsection order and proof strategy are structural adaptations from the
pinned HoTT sources. The prose in this edition is newly written. Each target,
source file, source label, and adaptation type is recorded before the
adaptation is committed. The book’s CC BY-SA 3.0 license and
[credits](#book-credits) preserve the upstream attribution and ShareAlike
requirements.
<!-- /book-source:appendix-hott -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:appendix-glossary book/appendices/d-glossary-and-index.md -->
<a id="appendix-glossary"></a>

# Appendix D. Glossary And Concept Index

This appendix fixes the vocabulary used by the expanded development edition.
Each entry points to the place where the idea is constructed or used, rather
than to a page number that would change with paper size and typography.

## D.1 Glossary

<a id="glossary-adjunction"></a>

**Adjunction.** Functors $F:A\to B$ and $G:B\to A$ equipped either with a
unit and counit satisfying the two triangle laws or with an equivalent
natural hom comparison. In the active calculus, the triangles are universal
cuts with selected computational owners. See [Chapter 12](#chapter-12).

<a id="glossary-arrow-induction"></a>

**Arrow induction.** Extension of data at the reflexive outgoing arrow to a
section over $\mathsf{PathOut}$. Unlike equality induction, its base category may
contain noninvertible arrows. See [Chapter 5](#chapter-5).

<a id="glossary-based-hom"></a>

**Based hom-category.** For a selected base object $*$ and endpoint
$x$, the category $H_x=\operatorname{Hom}_W(*,x)$. Its objects are based
1-arrows and its arrows are based 2-cells. See [Chapter 8](#chapter-8).

<a id="glossary-bnat"></a>

**BNat.** The separate one-object category with $\mathbb N$-valued hom, zero
identity, and addition composition. It is a concrete model of the walking
signature, not the definition of WalkingEnd. See
[§8.1.2](#chapter-8-1-2).

<a id="glossary-canonical-surface"></a>

**Canonical mathematical surface.** The readable notation in which the book
states categorical judgments and rule schemas. It maps to stable kernel
owners but is not itself a currently implemented parser language. See
[Appendix G.5](#appendix-formal-presentation-g5).

<a id="glossary-carrier-equivalence"></a>

**Carrier equivalence.** An equivalence between underlying classifiers, here
$\operatorname{Hom}_W(*,*)\simeq\mathbb N$. It does not by itself package
preservation of composition or an equivalence of ambient categories. See
[Theorem 8.1](#chapter-8).

<a id="glossary-cat-family"></a>

**Cat-valued directed family.** A functor $E:K\to\mathsf{Cat}$. It assigns a
category $E[k]$ to each base object and a transport functor $E[p]$
to each directed base arrow. See [Chapter 2](#chapter-2).

<a id="glossary-categorical-height"></a>

**Categorical height.** The recursive `IsNCat` condition: dimension zero
is discreteness, and successor dimension asks every hom-category to have the
preceding dimension. See [Chapter 7](#chapter-7).

<a id="glossary-native-category"></a>

**Category, native.** An object of `Cat`, with iterable category-valued homs.
It is not definitionally an ordinary HoTT precategory. See
[Chapters 2](#chapter-2) and [10](#chapter-10).

<a id="glossary-code"></a>

**Code.** The Cat-valued family over WalkingEnd whose base fibre is
$\mathsf{Path}(\mathbb N)$ and whose generator action is successor. See
[§8.1.3](#chapter-8-1-3).

<a id="glossary-coyoneda"></a>

**Co-Yoneda cut.** Elimination of a representable leg from a profunctor
composite. The checked theorem is a shaped, fixed-middle beta/fusion law; a
general coend theorem remains separate. See [Chapter 13](#chapter-13).

<a id="glossary-contextual-eliminator"></a>

**Contextual eliminator.** An eliminator that constructs a displayed functor
between two varying families from base-fibre data and coherent constructor
cells. Sections and ordinary recursors are special cases. See
[Chapter 6](#chapter-6).

<a id="glossary-cut-elimination"></a>

**Cut elimination.** Controlled normalization at the semantic owner of an
arrow, family, structural, or universal cut. It does not mean installing
unrestricted associativity as a global rewrite. See [Chapter 9](#chapter-9).

<a id="glossary-dagger"></a>

**Dagger structure.** A chosen contravariant involution on one category,
identity on objects in the ordinary presentation and coherent with retained
higher action in a prospective native presentation. It is not merely the
operation of taking an arbitrary opposite category. See
[Chapter 14](#chapter-14).

<a id="glossary-directed-hit"></a>

**Directed higher-inductive type/category.** A presentation with object,
directed-arrow, and possibly higher-cell constructors whose arrow generators
are not silently inverted. The current book has one selected implementation,
WalkingEnd, not a general schema. See [Chapter 6](#chapter-6).

<a id="glossary-directed-normalization"></a>

**Directed normalization cell.** The cell
$p\to\mathsf{decode}(\mathsf{encode}(p))$ constructed by the contextual decoder before
hom-discreteness extracts equality. See
[§8.1.4](#chapter-8-1-4).

<a id="glossary-discrete-category"></a>

**Discrete category.** A category whose hom structure agrees with equality of
objects at the selected interface. In a one-dimensional category every
hom-category is discrete; this does not make every ambient 1-arrow invertible.
See [§7.6](#chapter-7).

<a id="glossary-duality"></a>

**Duality.** Either a proof method that transports a theorem through the
opposite construction or additional structure comparing a category with an
opposite. It never licenses an unannounced variance reversal. See
[Chapters 14](#chapter-14) and [17](#chapter-17).

<a id="glossary-elaborator"></a>

**Elaborator.** A future, optional compilation layer that would parse surface
notation, infer omitted categorical data, select stable owners, and emit
explicit Lambdapi terms. The historical parent TypeScript prototype is
feasibility evidence, not that compiler. See
[Appendix G.5](#appendix-formal-presentation-g5).

<a id="glossary-evidence-status"></a>

**Evidence status.** One of checked, formal consequence, mathematical
development, or research boundary. The status describes the relation between
prose and the active artifact. See [How to Read](#how-to-read) and
[Appendix B](#appendix-evidence).

<a id="glossary-formal-presentation"></a>

**Formal presentation.** The four-layer account consisting of the
computational categorical kernel, the canonical mathematical surface, an
optional future elaborator, and external semantic models. The kernel comes
first; it is not post-hoc semantics for an unspecified traditional syntax.
See [Appendix G](#appendix-formal-presentation).

<a id="glossary-functor"></a>

**Functor.** A map with object and iterated-hom action. Generic functoriality,
not constructor-specific laws, owns identity and composition preservation.
See [Chapter 2](#chapter-2).

<a id="glossary-group-completion"></a>

**Group completion.** A future construction freely adjoining inverse motion
to the walking directed generator. It is the proper route from Nat powers
toward integers or a circle comparison. See [§8.1.5](#chapter-8-1-5).

<a id="glossary-hom-action"></a>

**Hom action.** The functorial action induced on a hom-category. Emdash keeps
covariant postcomposition, contravariant precomposition, and simultaneous
two-endpoint action as distinct computational owners. See
[Chapters 2](#chapter-2), [9](#chapter-9), and [13](#chapter-13).

<a id="glossary-join"></a>

**Join.** The selected directed category generated by left and right
embeddings together with cross arrows from the left side to the right side.
Its recursor and three beta observations are checked; a general collage
mapping property and dependent eliminator are not. See
[Chapter 17](#chapter-17).

<a id="glossary-kan-extension"></a>

**Kan extension.** A universal extension along a functor. This edition
expresses right and left Kan interfaces as conjoint- and companion-weighted
limits and colimits; identifying those interfaces with the full standard
pointwise semantics remains mathematical development. See Chapters
[16](#chapter-16) and [17](#chapter-17).

<a id="glossary-lower-star"></a>

**Lower-star action.** Postcomposition: if $g:w\to x$ and $u:x\to y$, then
$u_*(g)=u\circ g:w\to y$. Its active owners are `hom_postcomp_func` and
`hom_postcomp_fapp0`. See [§9.2](#chapter-9).

<a id="glossary-natural-transformation"></a>

**Natural transformation.** In the ordinary specialization, a pointwise
family $\alpha_x:F(x)\to G(x)$ satisfying a naturality equation. A native
transfor retains an off-diagonal action and iterates to higher hom levels, so
the two notions are related but not definitionally identical. See
[Chapter 11](#chapter-11).

<a id="glossary-off-diagonal-action"></a>

**Off-diagonal transfor action.** If $\eta:F\Rightarrow G$ and $f:x\to y$,
then $\eta[f]:F(x)\to G(y)$. Adjacent functor actions accumulate into this
term by strict naturality. See
[Chapter 9](#chapter-9).

<a id="glossary-omega-equivalence"></a>

**Omega-equivalence.** The native recursive equality-valued equivalence
interface for categorical cells. It is distinct from a bare carrier
`TypeEquiv` and from ordinary isomorphism evidence. See
[Chapter 4](#chapter-4).

<a id="glossary-opposite"></a>

**Opposite category.** The active arrow-reversing construction
$C\mapsto C^{\mathrm{op}}$. Opposite duality exchanges selected limit and
colimit interfaces while preserving a visible variance ledger. See
[Chapter 14](#chapter-14).

<a id="glossary-path-category"></a>

**Path category.** $\mathsf{Path}(A)$, the equality-local groupoidal category
on a classifier $A$. It embeds ordinary identity reasoning into the directed
calculus without identifying every directed hom with equality. See
[Chapter 2](#chapter-2).

<a id="glossary-pathout"></a>

**PathOut.** The outgoing-arrow category
$\sum_{y:Z}\operatorname{Hom}_Z(x,y)$ at a fixed source $x$. Its canonical
arrow from $(x,\mathrm{id}_x)$ to $(y,p)$ drives arrow induction. See
[Chapter 5](#chapter-5).

<a id="glossary-precategory"></a>

**Precategory, ordinary.** A classifier of objects with set-valued homs,
identities, composition, and category laws. It is used as a readable
one-categorical specialization of the native iterated-hom architecture. See
[Chapter 10](#chapter-10).

<a id="glossary-profunctor"></a>

**Profunctor.** A Cat-valued functor
$A^{\mathrm{op}}\times B\to\mathsf{Cat}$, contravariant in its first endpoint
and covariant in its second. See
[Chapter 13](#chapter-13).

<a id="glossary-representable"></a>

**Representable.** A family or profunctor obtained from an ambient hom. Its
action is composition, which makes it the computational bridge between
universal properties and cut elimination. See
[Chapters 5](#chapter-5) and [13](#chapter-13).

<a id="glossary-rezk-completion"></a>

**Rezk completion.** A completion intended to turn the selected weak
equivalences into equivalences as seen by saturated targets. The book gives
ordinary Yoneda-image and higher-inductive constructions and a prospective
native specification; no native implementation is claimed. See
[Chapter 15](#chapter-15).

<a id="glossary-rewrite"></a>

**Runtime rewrite.** A directed reduction selecting an intended normal form.
It is distinct from proof-time unification and internal propositional
equality. See [Appendix E](#appendix-computation).

<a id="glossary-saturation"></a>

**Saturation.** The property that the chosen identity-to-equivalence map is
itself an equivalence, or the result of freely enforcing that property by a
completion. Saturation is not finite categorical height. See
[Chapter 15](#chapter-15).

<a id="glossary-strict-category"></a>

**Strict category, ordinary HoTT sense.** A precategory whose object
classifier is a set. This is object-level truncation and must not be confused
with strict transfor computation or strict higher associativity. See
[Chapter 14](#chapter-14).

<a id="glossary-strict-transfor"></a>

**Strict transfor.** A native transfor for which the selected two-sided
naturality cuts compute through the global `tapp*` calculus. The adjective
does not say that every coherence law in its ambient category is
judgmental. See [Chapters 9](#chapter-9) and [14](#chapter-14).

<a id="glossary-structure-identity"></a>

**Structure identity principle.** A theorem identifying equality of
structured objects with an appropriate structure-preserving equivalence when
the displayed notion of structure is univalent or standard. The ordinary
theorem is developed mathematically; a generic native package is a research
boundary. See [Chapter 15](#chapter-15).

<a id="glossary-transfor"></a>

**Transfor.** An arrow in a functor category, generalizing a natural
transformation through off-diagonal and higher hom action. See
[Chapters 9](#chapter-9) and [11](#chapter-11).

<a id="glossary-truncation"></a>

**Truncation evidence.** A recursive property of an existing classifier: at
the base level it is contractibility, and at successor levels it truncates
all identity classifiers one step lower. It is not a truncation reflector.
See [Chapter 7](#chapter-7).

<a id="glossary-univalence"></a>

**Univalence.** An interface relating identity of classifiers or packages to
an appropriate equivalence. This edition has checked groupoid and restricted
truncated-universe interfaces but does not claim one universal directed
univalence axiom. See [Chapter 4](#chapter-4).

<a id="glossary-unitary"></a>

**Unitary arrow.** In a dagger category, an arrow whose dagger is an inverse.
The ordinary theory is developed in Chapter 14; a native unitary classifier
awaits the selected dagger interface and coherent higher action. See
[Chapter 14](#chapter-14).

<a id="glossary-upper-star"></a>

**Upper-star action.** Precomposition: if $u:x\to y$ and $h:y\to z$, then
$u^*(h)=h\circ u:x\to z$. Its active owners are
`hom_precomp_along_func` and `hom_precomp_along_fapp0`. The action is
contravariant in $u$. See [§9.2](#chapter-9).

<a id="glossary-weighted-colimit"></a>

**Weighted colimit.** A representation of a weighted-cocone profunctor. The
selected interface and left-adjoint preservation theorem are checked through
opposite duality; full coend semantics is not assumed. See
[Chapter 17](#chapter-17).

<a id="glossary-weighted-limit"></a>

**Weighted limit.** A representation of a weighted-cone profunctor, with beta
and eta supplied by a chosen profunctor comparison. The selected interface
and right-adjoint preservation theorem are checked. See
[Chapter 16](#chapter-16).

<a id="glossary-walkingend"></a>

**WalkingEnd.** The opaque one-dimensional directed HIT/category with a base
object and a directed generating endomorphism. See
[Chapters 6](#chapter-6) and [8](#chapter-8).

<a id="glossary-yoneda"></a>

**Yoneda principle.** Natural maps out of a representable are determined by
their value at the identity. The ordinary equivalence is developed by
encode-decode, while the active native theorem is the shaped co-Yoneda cut;
full Cat-valued Yoneda remains a named boundary. See
[Chapter 13](#chapter-13).

## D.2 Index strategy

This edition uses the linked concept index as its stable index. Terms
are curated rather than extracted from raw identifier frequency; synonyms
point to one canonical entry, and every destination is an explicit HTML
anchor checked by the source gate.

Page numbers are deliberately absent from the source because they depend on
the renderer, paper size, and font metrics. A later release tool may resolve
these anchors to PDF page labels, but the anchor remains the authority. New
index entries should be added when a concept is defined or changes status,
not for every occurrence of its implementation name.
<!-- /book-source:appendix-glossary -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:appendix-computation book/appendices/e-computation-and-normalization.md -->
<a id="appendix-computation"></a>

# Appendix E. Computation And Normalization

The prose uses equations freely, but the implementation distinguishes three
ways expressions can agree. That distinction is essential whenever a theorem
depends on a particular normal form.

## E.1 Three Forms Of Agreement

**Runtime reduction** selects a computational direction. A rewrite

```text
left  ↪  right
```

makes `right` the intended normal form when the left pattern is
observed. Constructor beta rules, functor projection rules, and selected
cut-elimination rules live here.

**Proof-time comparison** helps elaboration recognize two typed expressions
without making either one compute to the other. Emdash uses narrow
`unif_rule` declarations for this purpose. A typed reflexivity proof is
the relevant diagnostic; mere conversion testing does not exercise the same
interface.

**Internal equality** is mathematical data in a classifier
`x=y`. It can be transported, acted on, inverted, or used in an
equivalence proof. A propositional theorem may compare two stable runtime
presentations without changing either presentation's reduction behavior.

The book's symbol `=` normally denotes internal equality or an ordinary
mathematical equality justified by a formal-status note. It never implies that
the source expressions are definitionally identical.

## E.2 Semantic Owners

A computational operation should have one owner. Generic functoriality is
owned by the `fapp*` calculus; generic naturality by `tapp*`;
displayed hom action by `fdapp*` and `tdapp*`; Sigma and Pi expose
their own structural projections. Readable aliases route through these owners
instead of copying their semantic bodies.

This prevents two kinds of drift:

- competing rewrites can no longer silently choose incompatible normal forms;
- a theorem at the next hom level retains the functor or transfor object it
  needs for further iteration.

The WalkingEnd development illustrates the policy. The contextual eliminator
owns the constructor-specific base and generator observations. It does not
restate generic preservation of identity or composition. The decoder's
normalization cell is the displayed hom-action of one constructed functor; it
is not a custom recursion rule for every arbitrary based arrow.

## E.3 Direction And Variance In Normal Forms

Covariant postcomposition and contravariant precomposition have different
runtime owners. Their mathematical comparison through opposites is available
at proof time, but forcing both into one rewrite direction would erase the
variance used by `PathOut` and profunctor action.

Similarly, an identity may appear as an ambient categorical identity, a
functor identity, a displayed identity, or a specialized projection. These
forms are joined only where a typed consumer requires it. Broad eta-style
rewrites are avoided because unification is experimental and because a
functor-level normal form may be needed to act on the next cell.

## E.4 How A Checked Prose Claim Is Reviewed

For a code-facing claim, the review path is:

1. identify the mathematical interface and its direction;
2. locate the active owner declaration with lexical or type-aware search;
3. identify an independent regression or reviewer example;
4. decide whether the observation is runtime, proof-time, or propositional;
5. add or update the evidence-register entry;
6. cite the evidence identifier beside the prose claim;
7. run the evidence, assembly, source, and browser-render checks.

Changes to rewrite or unification behavior require the stronger repository
workflow: an owner-position probe, bounded typecheck, warning comparison when
relevant, focused assertions, and full CI before handoff. Book prose does not
authorize changing kernel normal forms merely to make an explanation shorter.

## E.5 What Has Not Been Proved Metatheoretically

The passing executable checks establish the selected interfaces and
regression observations. They do not by themselves prove global confluence,
strong normalization, canonicity, consistency of every future extension, or
soundness with respect to a complete weak omega-categorical model.

Those are research-level metatheorems. A future semantics chapter should state
its fragment, model, and computation theorem explicitly. Until then, the book
uses “computes” locally for named checked reductions and uses a formal-status
note for every stronger reading.

The current development SOP remains the operational authority for rule design
and validation. This appendix explains the mathematical reading needed by a
book reader; it is not a replacement for that SOP.
<!-- /book-source:appendix-computation -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:appendix-status book/appendices/f-status-and-research.md -->
<a id="appendix-status"></a>

# Appendix F. Implementation Status And Research Directions

This appendix summarizes the boundary of the expanded development edition.
The generated [evidence register](#appendix-evidence) remains the detailed
claim-by-claim authority.

## F.1 Status Matrix

| Area | Checked nucleus used by the book | Explicit boundary |
| --- | --- | --- |
| Equality-local type theory | Equality induction, path action, Sigma/Pi path interfaces, elementary inductives | No claim of a complete standalone HoTT implementation |
| Directed categories | Iterated homs, identities, composition, functors, transfors, opposites, products | No complete weak omega-category metatheory or model theorem |
| Directed families | Fibres, transport, family morphisms, Sigma totals, Pi sections, displayed hom action, fixed-base fibrewise products, asymmetric pullback totalization, and constant-domain displayed evaluation | Arbitrary displayed telescope depth, mixed-domain evaluation, and exchange across genuine dependency remain open |
| Cut and transfor calculus | Lower-star postcomposition, upper-star precomposition, off-diagonal `tapp1`, horizontal composition, selected universal beta/eta cuts | No unrestricted runtime associativity rewrite or claim that all higher coherence is judgmental |
| Equivalence and univalence | `TypeEquiv`, groupoid univalence, truncated-universe univalence, native recursive omega-equivalence facade and one-way hom action | No full general object-equality/ordinary-isomorphism equivalence for arbitrary categories |
| Induction | Nat and equality induction, fixed/varying-source `PathOut` induction, composition benchmark | No general equivalence with homotopy-initial categorical algebras |
| Directed HITs | One opaque WalkingEnd signature, contextual eliminator, section and recursor specializations | No general directed-HIT signature compiler or arbitrary cell-complex schema |
| Truncation and height | Recursive truncation properties and closure, evidence-property, finite `IsNCat` object truncation | No general truncation reflector or arbitrary truncation HIT |
| WalkingEnd calculation | Code, encode, power, spiral, contextual decoder, normalization cell/path, two inverse laws, carrier equivalence and noninvertibility results | No packaged monoid isomorphism, reverse `BNat` functor, full hom-category equivalence, or initiality theorem |
| Higher groupoidal shadow | Selected Eckmann–Hilton commutativity slice | No claim that all directed structure is groupoidal |
| Ordinary categorical specialization | Precategories, univalent categories, strict categories, functors, natural transformations, and ordinary Yoneda developed over the native vocabulary | These readable one-categorical theorems are mathematical development, not definitions of native `Cat` |
| Adjunctions and equivalences | Triangle cuts and hom-profunctor comparison; one-way lift from ordinary isomorphism to native evidence | No checked native fully-faithful/essentially-surjective characterization or general adjointification package |
| Yoneda and profunctors | Cat-valued profunctors, endpoint reindexing, representables, shaped cells, fixed-middle tensor, co-Yoneda beta/fusion | No general coend semantics, tensor associativity package, full Cat-valued Yoneda equivalence, or profunctor bicategory |
| Opposite, duality, and dagger | Opposite category action and selected opposite-duality comparisons | Dagger, unitary structure, and dagger univalence are mathematical development pending a native involutive interface |
| Structure identity and saturation | Truncation/evidence-property footholds and ordinary-isomorphism lift | Generic native structure identity and Rezk completion, including their higher universal properties, are research boundaries |
| Weighted limits and Kan interfaces | Weighted representability, beta/eta comparison, right-adjoint preservation, terminal/conjoint specializations | Standard end formulas, pointwise Kan semantics, existence, and general dependent adjunctions are not globally packaged |
| Weighted colimits and join | Opposite-dual colimit preservation, terminal/companion specializations, primitive join recursor and three beta observations | General coend semantics and join-as-collage mapping, hom-decomposition, opposite, and dependent-elimination theorems remain open |
| Formal presentation | Checked categorical owners; a bounded TypeScript outer LF, explicit Core, contextual elaborator, checker/runtime, and reviewed text subset | No compiler for the complete book surface, arbitrary displayed coherence, or whole-library transfer; readable notation is not a second kernel |
| Metatheory and models | Bounded typechecking, subject-reduction checks performed by Lambdapi, focused diagnostics, and the concrete BNat model | No global confluence, normalization, canonicity, decidability, consistency, or semantic-soundness theorem for the full combined calculus |
| Production artifact | Manifest assembly, provenance/evidence checks, local assets, bounded browser validation, and deterministic PDF export | External mathematical peer review and a non-draft public edition remain future release work |

## F.2 Near-Term Formal Strengthening

The most direct strengthening of Theorem 8.1 is to package composition and
addition compatibility. Its proof can use the checked power recursion, Nat
addition associativity, and both carrier inverse laws. The desired result is a
monoid-level comparison with an explicit orientation matching `BNat`.

Next comes a reverse functor from `BNat` to WalkingEnd and a comparison
with the existing model functor. This requires reusable action-to-functor and
functor-extensionality infrastructure; it should not be simulated by making
the opaque hom definitionally Nat-valued.

Full initiality is a further layer. It asks for a category of endomorphism
algebras, structured maps, and coherent higher transfors, followed by an
appropriate contractibility or equivalence theorem.

## F.3 Foundational Extensions

A reusable directed-HIT schema should generate contextual elimination and
constructor computation from typed object, arrow, and higher-cell boundaries.
Its validation must include rewrite overlap and subject-reduction behavior,
not only a semantic signature.

A truncation reflector should construct a universal truncated target rather
than merely certify an existing classifier. Directed categorical truncation
would additionally need to specify which lower arrows and compositions are
preserved.

The univalence programme should continue to separate carrier equivalence,
ordinary categorical isomorphism, and native equality-valued recursive
equivalence. A full theorem relating object equality and ordinary isomorphism
must be proved at the intended categorical level rather than recovered through
retired compatibility aliases.

## F.4 Categorical Extensions

The representable/profunctor and identity layers suggest four staged projects:

1. package a fully faithful Yoneda embedding with mapping-category
   equivalences and higher naturality;
2. construct or model Cat-valued coends/coinserters and relate the opaque
   tensor to their universal property;
3. assemble associators, unitors, and horizontal cell composition into a
   coherent profunctor bicategory or suitable omega-categorical analogue.
4. design generic structure identity and Rezk completion interfaces only after
   the intended native equivalence and higher mapping properties are fixed.

Weighted limits, colimits, adjunctions, duality, and joins now enter the
expanded chapter sequence through the triangle reductions, right-adjoint
weighted-limit preservation, its opposite-dual colimit theorem, and the join
recursor. The checked interfaces are the theorem spine; neighboring Kan,
end/coend, dagger, collage, and dependent-elimination theory remains
explicitly status-labeled rather than presented as a feature catalogue.

## F.5 Semantics And Proof-Assistant Engineering

The largest research objective is a semantics and metatheory for a precisely
stated fragment: typing, substitution, subject reduction, normalization or a
weaker operational theorem, and interpretation in a suitable strict/lax
omega-categorical model. The current executable artifact is evidence for
specific interfaces, not a substitute for that theorem.

The renewed TypeScript product now elaborates a bounded direct-TypeScript and
categorical-text surface into backend-neutral explicit Core, then checks and
reduces that Core with a small dependent logical framework. Its contextual
categorical layer covers reviewed ordinary, natural, displayed-functorial,
and displayed-natural binders, including one mixed dependent telescope. An
optional deterministic Lambdapi path remains a conformance oracle; it is not
a production dependency, and the active Lambdapi development remains the
mathematical authority.

This is a real executable bridge, but not completion of the canonical
mathematical surface. Arbitrary displayed coherence, unrestricted telescope
depth and variance, a compiler for the whole book notation, and systematic
transfer of the remaining library are still engineering boundaries. The
older TypeScript prototype remains historical feasibility evidence; its
stale category-specific layer is neither an authority nor the architecture
of the renewed product.

On the engineering side, a physical split of `emdash3_2.lp` remains
optional. It should begin only when a measured dependency or evidence-ownership
problem justifies the migration, and it must preserve declaration/rule order
and all current checks one boundary at a time.

## F.6 Reading Claims Across Editions

The edition version in `book/book.json` identifies the source snapshot
policy for generated artifacts. A later edition may promote a research
boundary only when the evidence register names active owners and independent
checks, or when the claim is explicitly reclassified as mathematical
development with stated prerequisites. Dated reports preserve why a boundary
was chosen; they do not override the current code.
<!-- /book-source:appendix-status -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:appendix-formal-presentation book/appendices/g-formal-presentation.md -->
<a id="appendix-formal-presentation"></a>

# Appendix G. Formal Presentation Of Functorial Type Theory

The mathematical chapters have used rules from the beginning: an identity
path eliminates by reflexivity, a functor acts on an arrow, a transfor
absorbs a naturality cut, and a representing comparison eliminates a
universal map. This appendix puts those rules in one formal architecture.
It follows the discipline of Appendix A of the
[HoTT Book](#ref-hott-book)—contexts and judgments first, then rule families,
extensions, and metatheory—but changes the order of explanation at one
decisive point.

In functorial type theory, category theory is not added later as a model of a
previously specified, traditional term calculus. The explicit categorical
calculus is already the computational core. Its objects include categories,
iterated homs, functors, transfors, and directed families; its reductions
express functoriality, naturality, induction, and universal properties. The
active Lambdapi v3.2 development authors and checks that calculus and remains
the mathematical authority.

The canonical mathematical surface used by this book is deliberately more
spacious than any one executable grammar. A renewed TypeScript product now
implements a bounded route from readable categorical binders to explicit
emdash Core and a small dependent logical framework. That route makes a
reviewed fragment directly usable; it does not become a second categorical
kernel or define the mathematics retroactively.

The architecture therefore distinguishes these roles:

| Layer or role | Responsibility | Present status |
| --- | --- | --- |
| canonical mathematical surface | the notation and rule presentation used by this book | active for prose, comments, and examples; not a parser grammar |
| scoped contextual elaboration | recursively interprets reviewed categorical variables, binders, neutral applications, and structural forms against typed expectations | active for the bounded direct-TypeScript and text profiles |
| backend-neutral explicit emdash Core | records the selected logical and categorical owners without committing to one runtime backend | active TypeScript intermediate representation |
| generic TypeScript dependent LF | checks Core terms, performs conversion and bounded reduction, and runs the reviewed proof-time rules | active for the recorded product boundary |
| active Lambdapi v3.2 kernel | authors the categorical declarations, computation, and proof-time comparisons used as mathematical authority | active and checked in the cited modules; also the conformance oracle |
| external semantic models | interpret a stated kernel fragment in mathematical categories or other structures | separate mathematical work; available only in selected examples |

The operational direction is

```text
canonical mathematical surface (broader than implemented text)
               |
               | reviewed direct TypeScript / text subset
               v
scoped contextual elaboration
               |
               v
backend-neutral explicit emdash Core
               |
               v
generic TypeScript LF checker / conversion / bounded runtime
               |
               +---- optional deterministic Lambdapi emission/conformance

active authored Lambdapi v3.2 kernel = mathematical authority
external models                    = separate mathematical work
```

The text adapter is not the checker, the TypeScript checker is not the active
mathematical authority, and the implemented text subset is not the whole
canonical surface. External interpretation is separate again. Keeping these
roles distinct lets us say exactly which claims are checked computation,
which are executable presentation, which are mathematical exposition, and
which remain research.

<a id="appendix-formal-presentation-g1"></a>

## G.1 Judgments, Contexts, And Classifiers

A formal presentation begins with judgments made in contexts. We use
$\Gamma$ for a finite ordered list of declarations. The basic external
judgments have the schematic forms

$$
\Gamma\;\mathsf{ctx},
\qquad
\Gamma\vdash T:\mathsf{TYPE},
\qquad
\Gamma\vdash t:T,
\qquad
\Gamma\vdash t\equiv u:T.
$$

These are metatheoretic assertions about expressions. In particular,
`t:T` is not itself an internal proposition whose inhabitant is a proof that
`t` has type `T`. Lambdapi checks the judgment while reading a declaration,
definition, rule, or assertion.

Contexts are ordered because later entries may depend on earlier ones:

$$
x:A,\quad y:B(x),\quad z:C(x,y).
$$

Substitution replaces a declared variable by a term of the required type and
acts in every later entry and conclusion. Renaming, weakening, exchange when
dependencies permit it, and substitution are structural operations of the
ambient dependent framework. They are not constructors of an internal
`Context` classifier in the active emdash kernel.

### External Types And Decoded Classifiers

The kernel uses two related universes. `TYPE` is Lambdapi's ambient type
level. `Grpd : TYPE` is the small groupoidal or type-like classifier
universe used by emdash, and

$$
\tau:\mathsf{Grpd}\longrightarrow\mathsf{TYPE}
$$

decodes a classifier to the ambient type of its elements. Thus the book's
readable judgment $a:A$ normally abbreviates the literal judgment
`a : τ A` for `A : Grpd`.

Categories live at the ambient level:

$$
\mathsf{Cat}:\mathsf{TYPE}.
$$

Their object and arrow collections are internal classifiers:

$$
\begin{aligned}
\operatorname{Obj}(C)&:\mathsf{Grpd},\\
\operatorname{Hom}_{C}(x,y)&:\mathsf{Cat},\\
\operatorname{Hom}(C,x,y)
  :=\operatorname{Obj}(\operatorname{Hom}_{C}(x,y))
  &:\mathsf{Grpd}.
\end{aligned}
$$

The second line is the source of higher structure. If $f,g:x\to y$, then a
2-cell $\alpha:f\to g$ is an object of
$\operatorname{Hom}_{\operatorname{Hom}_{C}(x,y)}(f,g)$; repeating the same
construction exposes higher cells without changing the grammar at each
dimension.

The main internal classifiers used in the book are:

| Mathematical classifier | Literal owner | Decoded inhabitants |
| --- | --- | --- |
| objects of $C$ | `Obj C` | `τ (Obj C)` |
| arrows $x\to_C y$ | `Hom C x y` | `τ (Hom C x y)` |
| functors $A\to B$ | `Functor A B` | `τ (Functor A B)` |
| transfors $F\Rightarrow G$ | `Transf F G` | `τ (Transf F G)` |
| Cat-valued families over $K$ | `Catd K` | `τ (Catd K)` |
| displayed functors $E\to D$ | `Functord E D` | `τ (Functord E D)` |
| displayed transfors $FF\Rightarrow GG$ | `Transfd FF GG` | `τ (Transfd FF GG)` |

This distinction prevents two common category mistakes. First,
`C : Cat` is not an object of some silently assumed set of all categories;
it is an ambient kernel judgment. Second, an arrow classifier is not merely a
set of morphisms: it is the object classifier of another category and can
therefore be iterated.

### Six Ways To Compare Expressions

Several notations that resemble equality have different force.

| Notation | Layer | Meaning |
| --- | --- | --- |
| $t\rightsquigarrow u$ in this book; `t ↪ u` in source | runtime | a selected oriented rewrite makes $u$ the computational form |
| $t\equiv u$ | external conversion | the checker regards the terms as definitionally convertible using active computation |
| `unif_rule t ≡ u ↪ [...]` | proof-time elaboration | a unification problem is replaced by narrower subproblems; neither side is selected as a runtime normal form |
| $p:x=_A y$ | internal mathematics | `p` inhabits an equality classifier and can be eliminated by `ind_eqr` |
| $A\simeq B$ | internal mathematical structure | specified maps and inverse/coherence evidence, such as `TypeEquiv` or a categorical comparison |
| $t=u$ in status-labeled free-form prose | mathematical development | a theorem to be proved in the named future interface, not an undisclosed kernel conversion |

A runtime rule does not by itself assert equality reflection. An internal
path does not make its endpoints definitionally identical. A proof-time
unification rule is not a path constructor, and an equivalence is not an
unlabeled use of conversion. Chapters 1 and 9 rely on precisely these
distinctions.

<!-- evidence:FORMAL-KERNEL-PRESENTATION -->

> **Formal status — checked.** Evidence
> `FORMAL-KERNEL-PRESENTATION` covers the active categorical classifiers,
> their application operations, and representative executable checks. The
> displayed turnstile notation is the book's metanotation; it is not a new
> internal judgment former.

<a id="appendix-formal-presentation-g2"></a>

## G.2 The Mathematical Categorical Presentation

We now give a compact signature in the notation of the book. It is the
human-readable presentation of the kernel, not an untyped concrete grammar.
Implicit arguments are suppressed only when their recovery is forced by the
displayed source and target.

### Categories And Iterated Homs

The core categorical judgments are

$$
\frac{}{C:\mathsf{Cat}},
\qquad
\frac{C:\mathsf{Cat}}{x:\operatorname{Obj}(C)},
\qquad
\frac{x,y:\operatorname{Obj}(C)}
     {f:\operatorname{Hom}_{C}(x,y)}.
$$

Every object has an identity, and composable arrows have a composite:

$$
\operatorname{id}_x:x\to_Cx,
\qquad
\frac{f:x\to_Cy\quad g:y\to_Cz}{g\circ f:x\to_Cz}.
$$

The convention is always “first $f$, then $g$.” Identity and associativity
are available at the intended comparison layers. The implementation does not
install unrestricted reassociation as a general runtime rewrite.

Opposite categories reverse the hom endpoints:

$$
\operatorname{Hom}_{C^{\mathrm{op}}}(x,y)
\rightsquigarrow
\operatorname{Hom}_{C}(y,x).
$$

The path category embeds the equality-local fragment:

$$
\operatorname{Obj}(\mathsf{Path}(A))\rightsquigarrow A,
\qquad
\operatorname{Hom}_{\mathsf{Path}(A)}(x,y)
\rightsquigarrow\mathsf{Path}(x=_Ay).
$$

This is a groupoidal specialization. It does not identify arbitrary directed
arrows with equality paths.

### Functors And Their Iterable Action

For categories $A,B$, the category $A\vdash B$ has functors as objects:

$$
\frac{A,B:\mathsf{Cat}}{A\vdash B:\mathsf{Cat}},
\qquad
\frac{}{F:\operatorname{Obj}(A\vdash B)}.
$$

We write the second judgment as $F:A\to B$. A functor has object action and,
for every pair $x,y:A$, a functor on the whole hom-category:

$$
\begin{aligned}
F[x]&:\operatorname{Obj}(B),\\
F_{x,y}&:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(F[x],F[y]),\\
F[f]&:=F_{x,y}[f].
\end{aligned}
$$

The hom action, not only its value at one arrow, is primary. It can act again
on a 2-cell between arrows, and its own hom action continues the same pattern.
At the first capped level, the selected functoriality cuts are

$$
F[\operatorname{id}_x]\rightsquigarrow\operatorname{id}_{F[x]},
\qquad
F[g]\circ F[f]\rightsquigarrow F[g\circ f].
$$

### Transfors And Family Action

For parallel functors $F,G:A\to B$, the category $F\Rightarrow G$ is their
first hom in the functor category. A transfor
$\eta:F\Rightarrow G$ has a point component

$$
\eta_x:F[x]\longrightarrow G[x]
$$

and, more fundamentally, an off-diagonal hom functor

$$
\eta_{x,y}:
\operatorname{Hom}_{A}(x,y)
\longrightarrow
\operatorname{Hom}_{B}(F[x],G[y]).
$$

We write $\eta[f]$ for its value at $f:x\to y$. Its two adjacent naturality
cuts compute:

$$
\begin{aligned}
G[g]\circ\eta[f]&\rightsquigarrow\eta[g\circ f],\\
\eta[f]\circ F[h]&\rightsquigarrow\eta[f\circ h].
\end{aligned}
$$

The diagonal component is the identity-arrow instance of this family action.
Thus naturality is not a proposition pasted onto a bare family of arrows. It
is part of an operation whose higher action remains available.

### Directed Families, Totals, And Sections

A directed Cat-valued family over $K$ is written

$$
E:K\longrightarrow\mathsf{Cat}.
$$

For $k:K$ it has a fibre $E[k]$, and for $p:k\to_Kk'$ it has transport

$$
E[p]:E[k]\longrightarrow E[k'].
$$

A displayed functor $FF:E\to D$ contains fibre functors and off-diagonal
comparison cells over base arrows. In book notation its classifier is

$$
k:^{n}K\ ;\ E[k]\vdash D[k].
$$

Displayed transfors arise by taking the next hom in this category. The
`Catd`, `Functord`, and `Transfd` facades keep these levels visible
instead of flattening them into pointwise functions.

Two categorical dependent formers organize families:

$$
\sum_{k:^{n}K}E[k]
\qquad\text{and}\qquad
\prod_{k:^{n}K}E[k].
$$

The Sigma total has objects $(k,u)$ with $u:E[k]$. An arrow consists of a base
arrow $p:k\to k'$ and a fibre arrow

$$
E[p](u)\longrightarrow u'
\quad\text{in }E[k'].
$$

The Pi category has coherent sections as objects. Its evaluation at $k$ is a
functor to $E[k]$, not merely a carrier-level application function.

### Chosen Arrows And Natural Families

The two represented-hom actions expose the first Došen-style cut discipline.
For $u:x\to_Ay$,

$$
u_*(g)=u\circ g
\quad\text{and}\quad
u^*(h)=h\circ u.
$$

Lower star is covariant postcomposition; upper star is contravariant
precomposition. With a functor $H$, the acting arrow is $H[u]$, so
$(H[u])^*(h)=h\circ H[u]$. By contrast, $\eta[f]$ uses the whole natural
family $\eta$, not one selected arrow. Structural and universal eliminators
continue this progression.

The product/projection benchmark of Chapter 9 is a theorem in an arbitrary
category $K$ equipped with products. Its Cat-specialized executable probe is
evidence about the current owner calculus, not a restriction of the
mathematical statement to the category of categories.

### Signature-To-Owner Map

The following table records the correspondence without treating readable
notation as a second implementation.

| Readable operation | Active owner |
| --- | --- |
| $x\to_Cy$ | `Hom_cat C x y` and `Hom C x y` |
| $A\vdash B$ | `Functor_cat A B` |
| $F[x]$, $F[f]$ | `fapp0`, `fapp1_func`, `fapp1_fapp0` |
| $F\Rightarrow G$ | `Transf_cat F G` |
| $\eta_x$, $\eta[f]$ | `tapp0_fapp0`, `tapp1_func`, `tapp1_fapp0` |
| $E:K\to\mathsf{Cat}$ and $E[k]$ | `Catd K` and `Fibre_cat E k` |
| displayed functors and transfors | `Functord` and `Transfd` |
| $\sum_kE[k]$, $\prod_kE[k]$ | `Sigma_cat E` and `Pi_cat E` |
| $u_*$, $u^*$ | `hom_postcomp_*` and `hom_precomp_along_*` |

<!-- evidence:CAT-ITERATED-HOMS -->
<!-- evidence:CAT-FUNCTOR-CALCULUS -->
<!-- evidence:TRANSF-POINT-OFFDIAGONAL -->
<!-- evidence:TRANSF-STRICT-NATURALITY -->
<!-- evidence:CAT-DIRECTED-FAMILIES -->

> **Formal status — checked.** Evidence `CAT-ITERATED-HOMS`,
> `CAT-FUNCTOR-CALCULUS`, `TRANSF-POINT-OFFDIAGONAL`,
> `TRANSF-STRICT-NATURALITY`, and `CAT-DIRECTED-FAMILIES` support the
> displayed nucleus. The typography in this section is canonical
> mathematical surface notation; the next section shows literal source.

<a id="appendix-formal-presentation-g3"></a>

## G.3 The Checked Lambdapi Presentation

The active source is a Lambdapi signature. This section gives representative
literal excerpts, enough to explain how the mathematical presentation is
checked without reproducing the kernel.

### Declarations And Definitions

At the universe boundary the source says:

```lambdapi
constant symbol Grpd : TYPE;
injective symbol τ : Grpd → TYPE;

constant symbol Cat : TYPE;
symbol Obj : Cat → Grpd;
injective symbol Hom_cat :
  Π (A : Cat) (X_A Y_A : τ (Obj A)), Cat;
injective symbol Hom (A : Cat) (X_A Y_A : τ (Obj A)) : Grpd
≔ Obj (Hom_cat A X_A Y_A);
```

These lines exhibit three declaration policies.

- A `constant symbol` cannot receive a definition or rewrite rules.
  `Cat`, `Grpd`, and the WalkingEnd constructors use this literal policy.
- A plain `symbol` may be an undefined operation that later receives rules,
  or it may have a transparent body after `≔`.
- An `injective symbol` gives the unifier a rigid constructor-like head.
  The modifier is a trusted declaration choice and is used only at selected
  classifier and stable-owner boundaries.

Lambdapi also supports an `opaque` modifier for a defined symbol whose body
must not reduce. In the book, “opaque WalkingEnd” describes the mathematical
effect of its constant declarations; it does not claim that those lines use
the literal `opaque symbol` spelling.

Implicit parameters appear in square brackets and explicit parameters in
parentheses. Prefix `@` exposes normally implicit parameters at a use site.
In rule patterns, a dollar-prefixed name such as `$A` is a pattern
variable, while `_` asks typing and unification to recover a slot that is
not a genuine discriminator.

### Rewrite Owners

Functor application is declared at a full hom level and a capped arrow level:

```lambdapi
symbol fapp1_func : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  τ (Functor
    (Hom_cat A X_A Y_A)
    (Hom_cat B (fapp0 F_AB X_A) (fapp0 F_AB Y_A)));

symbol fapp1_fapp0 : Π [A B : Cat], Π (F_AB : τ (Functor A B)),
  Π [X_A Y_A : τ (Obj A)],
  Π (f : τ (Hom A X_A Y_A)),
  τ (Hom B (fapp0 F_AB X_A) (fapp0 F_AB Y_A));

rule fapp0 (fapp1_func $F_AB) $f
  ↪ fapp1_fapp0 $F_AB $f;
```

The last line is runtime computation: observing the full hom-action at one
arrow exposes the capped action. The generic identity and composition rules
then contract $F[\operatorname{id}]$ and
$F[g]\circ F[f]$. Concrete functor constructors inherit those rules; they do
not each receive private copies of ordinary functoriality.

The same ownership policy governs transfors. `tapp0_fapp0` observes a point
component, while `tapp1_func` and `tapp1_fapp0` own off-diagonal action.
The two strict naturality rewrites are attached to that generic action. A
constructor-specific rule is justified only when it expresses extra
constructor computation, not the fact that something already typed as a
transfor is natural.

### Proof-Time Unification

Some stable category presentations should elaborate together without one
being erased at runtime. For rigid hom-category heads the source includes:

```lambdapi
unif_rule Obj (Hom_cat $A $X $Y) ≡ Obj (Hom_cat $A' $X' $Y')
  ↪ [ $A ≡ $A'; $X ≡ $X'; $Y ≡ $Y' ];
```

This rule decomposes one proof-time unification problem into three. It does
not rewrite an object classifier during execution, prove an internal path,
or assert that `Obj` is globally injective for every category construction.

Similar narrow comparisons relate the ordinary functor-category presentation
to `Catd_cat`, and the ordinary transfor presentation to
`Functord_cat`.

Associativity illustrates the boundary particularly well. The two bracketings
of ordinary composition are compared at proof time, and `comp_assoc`
packages a propositional witness. There is no global runtime rule that
continually reassociates every composite. Represented hom actions,
`tapp1`, and universal comparisons instead own the specific cuts they can
normalize without losing higher action.

### Assertions And Negative Assertions

Executable diagnostics are source commands, not theorem prose. A small
example is:

```lambdapi
assert ⊢ Nat_grpd : Grpd;
assert ⊢ zero : τ Nat_grpd;
assertnot ⊢ @eq_refl Nat_grpd zero ≡ tt;
```

The first two ask Lambdapi to accept a type and an inhabitant. The last checks
that two terms are not definitionally convertible. A typed reflexivity term is
used when a proof-time unification rule must be exercised; a bare conversion
assertion does not test that same mechanism.

The diagnostic suite is intentionally separate from implementation owners.
Permanent examples and assertions provide regression evidence, while the
evidence register connects book claims to both declarations and reviewers.

### Modules And Ownership

The current organization is:

| Module | Formal role |
| --- | --- |
| `emdash3_2.lp` | active categorical kernel and universal-construction owners |
| `emdash3_2_eq1_hom_action.lp` | derived native equality-valued next-hom and groupoidality layer |
| `emdash3_2_eq1_evidence_property.lp` | evidence-property and finite-height consequences |
| `emdash3_2_nat_arithmetic.lp` | reusable Nat operations and sethood |
| `emdash3_2_walking_end_hit.lp` | selected WalkingEnd signature, eliminator, computation, and comparison |
| `emdash3_2_checks.lp` | executable diagnostics |

Imports use `require`; `open` brings imported public names into scope.
The file split expresses dependency and evidence ownership. It is not a claim
that every conceptual chapter already has its own kernel module.

Three source policies are essential for reading rules correctly.

1. Match a computation at its semantic owner and retain stable heads needed
   by later higher action.
2. Keep inferred rule slots anonymous unless a slot is a measured type,
   subject-reduction, or decision-tree guard.
3. Use runtime rewrites only for intended normal forms; use narrowly typed
   proof-time comparisons when neither side should compute to the other.

<!-- evidence:FORMAL-KERNEL-PRESENTATION -->

> **Formal status — checked.** Evidence
> `FORMAL-KERNEL-PRESENTATION` records the representative declaration,
> action, rule, module, and diagnostic surface described here. Successful
> source checking warrants these interfaces; it does not establish the global
> metatheorems listed in G.7.

<a id="appendix-formal-presentation-g4"></a>

## G.4 Formation, Introduction, Elimination, And Computation

The familiar rule schema remains useful, provided we add a sixth question
suited to directed mathematics.

| Rule aspect | Question |
| --- | --- |
| formation | when is the classifier or categorical object well formed? |
| introduction | what data construct an inhabitant or structured object? |
| elimination | how may an inhabitant be observed or used? |
| computation | what does elimination do to introduced data? |
| uniqueness or universality | is an arbitrary inhabitant recovered, propositionally compared, or characterized by a mapping property? |
| action and coherence | how does the construction act on arrows and higher cells as its parameters vary? |

The last row is not optional decoration. A pointwise formula may answer the
first five questions at objects while failing to define a functor, transfor,
or displayed family.

### Equality Induction

For $A:\mathsf{Grpd}$ and $x,y:A$, equality formation gives $x=_Ay$.
Reflexivity introduces an inhabitant
$\mathsf{refl}_x:x=x$. Right-based elimination fixes $y$, takes

$$
P:\prod_{x:A}(x=y)\longrightarrow\mathsf{Grpd},
\qquad
u:P(y,\mathsf{refl}_y),
$$

and returns

$$
\mathsf{ind\_eqr}(P,u,p):P(x,p)
\quad\text{for }p:x=y.
$$

Its literal-reflexivity beta computes:

$$
\mathsf{ind\_eqr}(P,u,\mathsf{refl}_y)
\rightsquigarrow u.
$$

Path action, dependent path action, symmetry, and transitivity are derived
uses. No equality reflection, uniqueness of identity proofs, or global
path-eta rule is added. At the categorical layer, `Path_cat` and
`path_map_func` package equality and function action so that higher path
action can be iterated.

<!-- evidence:TT-EQUALITY-INDUCTION -->

> **Formal status — checked.** Evidence `TT-EQUALITY-INDUCTION`.
> Formation, reflexivity, right-based elimination, beta, `ap`, and
> `apd` are active. A stronger global uniqueness principle is not silently
> inferred from the beta rule.

### Categories, Functors, And Transfors

`Cat`, `Obj`, and `Hom_cat` give formation for the categorical tower.
Identity and composition are introduction operations for arrows, while
iteration of `Hom_cat` eliminates an arrow into its next-cell context.
The selected unit and associativity comparisons say how these introductions
compose; there is no eliminator claiming that every category is freely
generated by its displayed arrows.

For a functor, formation is `Functor A B`. Its elimination operations are
`fapp0` and `fapp1_func`. The projection beta from full hom action to
`fapp1_fapp0` and the identity/composition cuts are its generic
computations. The active theory obtains inhabitants from named functor
constructors and categorical operations; the book does not posit one
record-style constructor whose fields may be supplied incoherently.

For a transfor, formation is `Transf F G`. Point and off-diagonal
application are eliminations. Identity-boundary, composition, and the two
naturality cuts are computations. The full off-diagonal functor is the action
clause: it says what happens not just to an arrow $f$ but to a higher cell
between possible values of $f$.

This gives a useful criterion:

> A point-component formula does not define a transfor until the
> off-diagonal arrow action and its next-hom behavior are supplied or
> explicitly deferred.

### Sigma Totals And Pi Sections

For $E:K\to\mathsf{Cat}$, categorical Sigma formation gives
$\Sigma_KE:\mathsf{Cat}$. An object is introduced as $(k,u)$ with $u:E[k]$.
The first projection and the fibre component eliminate it. A total arrow is
introduced by a pair

$$
\bigl(p:k\to k',
  \alpha:E[p](u)\to_{E[k']}u'\bigr).
$$

Projection and composition rules compute on this structure. The
`sigma_intro_transf` packages the inclusions $E[k]\to\Sigma_KE$ naturally
in $k$, so introduction also has a directed action rather than only a pair
constructor.

Pi formation gives the section category $\Pi_KE$. Evaluation is packaged by
`pi_eval_transf`, whose component at $k$ is the functor

$$
\operatorname{ev}_k:\Pi_KE\longrightarrow E[k].
$$

The evaluation projection computes through `piapp0_func`. Constant
sections and pullback of sections supply important introductions, but the
current interface does not assert a general categorical Pi-eta or a fully
packaged dependent adjunction. Those stronger universal laws require the
base-arrow, off-diagonal, and Beck–Chevalley data described in Chapter 16.

At the groupoid layer, encoded Sigma and Pi classifiers separately provide
dependent pairs, projections, pointwise path observation, and the selected
`happly`/`funext` equivalence. The categorical Sigma/Pi operations above
must not be flattened into those carrier-level formers: their objects vary in
categories and their arrow action is part of the interface.

<!-- evidence:CAT-SIGMA-PI -->
<!-- evidence:TT-SIGMA-PI-PATHS -->

> **Formal status — checked nucleus.** Evidence `CAT-SIGMA-PI` and
> `TT-SIGMA-PI-PATHS`. The active rules cover the cited constructors,
> projections, evaluation, and action. General dependent adjunctions remain
> the research boundary recorded in Chapter 16.

### The WalkingEnd Rule Package

The walking endomorphism makes every row of the schema visible:

| Aspect | Selected WalkingEnd datum |
| --- | --- |
| formation | `WalkingEnd_cat : Cat` |
| object introduction | `walking_base : Obj(WalkingEnd)` |
| arrow introduction | `walking_loop : Hom(WalkingEnd,base,base)` |
| height datum | `walking_end_is_one_cat : IsNCat(1,WalkingEnd)` |
| contextual algebra | $R,D:W\to\mathsf{Cat}$, $u:R[*]\to D[*]$, and $\sigma:D[\ell]\circ u\Rightarrow u\circ R[\ell]$ |
| elimination | `walking_end_ind_funcd R D u sigma : Functord R D` |
| base computation | the fibre component at $*$ reduces to $u$ |
| loop computation | the displayed action at $\ell$ reduces to the supplied component of $\sigma$ |
| uniqueness | no general initiality or contractibility theorem is currently packaged |
| action | the result is a displayed functor, so base-arrow and higher action are retained |

The section eliminator specializes $R$ to the terminal family. The ordinary
recursor specializes both families to constants. They are derived views of
the contextual eliminator, not three independent postulates. The literal
constructor betas are attached to stable generic observers, with two narrow
projection joins for the concrete ordinary-recursion consumers.

<!-- evidence:WE-SIGNATURE -->
<!-- evidence:WE-CONTEXTUAL-ELIMINATOR -->
<!-- evidence:DHIT-DERIVED-ELIMINATORS -->

> **Formal status — checked.** Evidence `WE-SIGNATURE`,
> `WE-CONTEXTUAL-ELIMINATOR`, and
> `DHIT-DERIVED-ELIMINATORS`. The absence of a uniqueness theorem is part
> of the formal statement, not a prose omission.

### Adjunction And Weighted Representability

An adjunction illustrates a rule package whose principal eliminations are
observations rather than a public record constructor. For named functors
$F:R\to L$ and $G:L\to R$, the classifier

$$
\mathsf{Adjunction}(F,G)
$$

forms the proposition-like structure accepted by the kernel. From
$J:\mathsf{Adjunction}(F,G)$ one eliminates the selected unit and counit:

$$
\eta:\operatorname{id}_R\Rightarrow GF,
\qquad
\varepsilon:FG\Rightarrow\operatorname{id}_L.
$$

The two triangle cuts compute at off-diagonal components. Their role is
exactly beta reduction: an introduction by a unit followed by elimination by
a counit contracts to the underlying map, and dually.

A weighted limit is presented one level more abstractly. Given
$F:J\to B$, $W:J'\rightsquigarrow J$, and $L:J'\to B$, formation gives the
classifier

$$
\mathsf{IsWeightedLimit}_{\mathrm{cov}}(F,W,L).
$$

An inhabitant is a computational comparison between the weighted-cone
profunctor and the representable hom profunctor. Reindexing and applying that
certificate eliminates it into inverse operations

$$
\mathsf{push}
\quad\text{and}\quad
\mathsf{pull}.
$$

Their composites reduce by the generic profunctor-comparison beta and eta
rules. The action clause is reindexing along every probe functor
$M:I\to B$; the universal property is not restricted to one set of global
elements. Adjunction mates then transport the whole comparison, which is why
right-adjoint preservation is a computation on certificates rather than a
fresh pointwise proof.

Existence for every diagram and uniqueness of representing objects are
separate theorems. The active classifier says what data certify a chosen
$L$; it does not postulate a global limit operator or a native univalent
uniqueness package.

<!-- evidence:ADJ-TRIANGLE-CUTS -->
<!-- evidence:WEIGHTED-LIMIT-REPRESENTABILITY -->

> **Formal status — checked.**
> Evidence `ADJ-TRIANGLE-CUTS` and
> `WEIGHTED-LIMIT-REPRESENTABILITY`.
>
> The formation/elimination/computation interface is active. Semantic end
> formulas, general existence, and univalent uniqueness remain separately
> status-labeled mathematics.

<a id="appendix-formal-presentation-g5"></a>

## G.5 Elaboration And Canonical Surface Syntax

Readable notation is indispensable, but it need not be the foundational
layer. The renewed TypeScript path compiles a reviewed subset into the
explicit owners described above:

| Stage | Implemented bounded profile | Retained boundary |
| --- | --- | --- |
| parse | located `^f`, `^n`, `^fd`, and `^nd` binders, neutral application, and reviewed constructors and contexts | not the complete book or Lambdapi grammar |
| elaborate | typed expected classifiers route recursively through the existing contextual categorical program | no arbitrary pointwise-to-coherent synthesis |
| select owner | reviewed operation families lower to internal categorical and structural owners | no whole-library owner-acquisition claim |
| check and reduce | the generic TypeScript LF checks explicit Core, compares terms, and executes the bounded runtime | no global metatheory |
| conform | optional deterministic Lambdapi emission and a bounded oracle compare selected results with the active kernel | no production Lambdapi dependency |

Elaboration may recover information; it may not invent mathematics. If a
pointwise family lacks arrow action, the elaborator must report missing
coherence rather than synthesize an arbitrary transfor. If lower-star and
upper-star action are both type-correct, the written variance or expected
type must disambiguate them.

### Surface Forms And Explicit Targets

The current canonical notation includes:

| Surface | Explicit target |
| --- | --- |
| `a ->^C b` | `Hom_cat C a b` |
| `A ⊢ B` | `Functor_cat A B` |
| `F => G` | `Transf_cat F G` |
| `E[k]` | `Fibre_cat E k` |
| `A[k^-] ⊢_[k] B[k]` | `Functor_catd A B` |
| `Π (k :^n K), E[k]` | `Pi_cat E` |
| `u_*(g)` | a `hom_postcomp_*` application |
| `u^*(h)` | a `hom_precomp_along_*` application |

For example, if $\eta:F\Rightarrow G$ and $f:x\to_Ay$, the readable term
$\eta[f]:F[x]\to_BG[y]$ elaborates toward the fully explicit owner

```lambdapi
@tapp1_fapp0 A B F G x y eta f
```

The source notation does not have to expose all seven parameters, but the
result must typecheck as that operation or an explicitly documented
equivalent owner.

### Executable Binders And Structural Lowering

Binder modes express how variables may vary. The reviewed executable forms
are

```text
λ^f  x : A. ...
λ^n  k : K. ...
λ^fd a : E. ...
λ^nd k : K. ...
```

The mode belongs to the lambda. The classifier annotation after the variable
may be omitted when the bidirectional expected classifier supplies it, but
the mode is not inferred from that annotation. The mathematical telescope
notation $k:^{n}K$ therefore records the same natural/indexed role as
`λ^n k : K. ...` without pretending that mathematical declarations and
executable binders are literally the same grammar. Ordinary object binding
in the outer LF uses its ordinary dependent lambda.

For example, assume

```text
A, B, C : Cat
E : Functor B (Functor_cat A C)
```

The reviewed expression

```text
λ^f x : A. λ^f y : B. E y x
```

has classifier `Functor A (Functor_cat B C)`. Neutral application first
selects the action of `E` on `y` and then its action on `x`. Recursive
abstraction lowers the result through the existing exchange/currying
construction; a compact rendering of the selected structural term is

```text
fapp0
  (Functor_cat B (Functor_cat A C))
  (Functor_cat A (Functor_cat B C))
  exchange-functor-abstraction
  E
```

No external functoriality equation accompanies the source expression. The
selected owner already carries object and arrow action, and the resulting
explicit Core is checked by the same generic LF as other terms.

Displayed contexts make the distinction between dependency and independence
visible. The bounded mixed telescope

```text
λ^fd (a : A; b : B, c : C; d : D). fibrePair b c
```

has dependency levels `A; B,C; D`. A semicolon advances to a family over the
preceding total context, while a comma groups independent siblings over the
same prefix. The middle pair lowers through the transparent fibrewise product,
displayed pairing, Sigma projections, and reindexing owners. Thus `b` and `c`
may be paired, weakened, contracted, or exchanged fibrewise; no exchange of
`a` across a classifier depending on `a` is implied. Object and base-arrow
behavior remain internal to those owners rather than being supplied as
external coherence evidence.

### Historical Prototype And Retained Boundary

The repository history contains an older TypeScript feasibility prototype
with generic bidirectional checking, holes, unification, rewriting, and
proof-state machinery. Those mechanisms informed the renewed work, but its
stale category-specific layer is not an authority for v3.2. The renewed
product instead targets backend-neutral explicit Core aligned with active
owners and uses Lambdapi only as an optional conformance oracle.

The current path is deliberately bounded. It does not parse every notation
used in this book, lower arbitrary displayed telescope depth or variance,
synthesize coherence from a pointwise function, or establish mechanical
transfer of the whole Lambdapi library. These are explicit continuation
boundaries, not hidden assumptions of the implemented examples.

<!-- evidence:FORMAL-ELABORATION-BOUNDARY -->

> **Formal status — research boundary.** Evidence
> `FORMAL-ELABORATION-BOUNDARY`. The direct-TypeScript and categorical-text
> paths, explicit Core, generic checker/evaluator, and optional conformance
> route are executable for the reviewed profile. A complete compiler for the
> canonical surface, arbitrary displayed coherence, and whole-library
> transfer are not claimed. The active Lambdapi sources remain the
> mathematical authority.

<a id="appendix-formal-presentation-g6"></a>

## G.6 Directed Higher-Inductive Signatures

A directed higher-inductive signature must specify more than a list of
generators. At minimum it needs:

1. object, arrow, and higher-cell constructors with typed boundaries;
2. the categories and families into which they may be interpreted;
3. recursion, dependent elimination, and any contextual elimination
   principles;
4. coherence data demanded by varying source and target families;
5. constructor computation at named observers;
6. action on arrows and higher cells of every varying parameter;
7. optional dimension or truncation evidence;
8. a statement of uniqueness or initiality when one has actually been proved.

The WalkingEnd signature is the selected worked instance. With
$W=\mathsf{WalkingEnd}$, $*:\operatorname{Obj}(W)$, and
$\ell:*\to_W*$, its contextual algebra is

$$
\begin{aligned}
R,D&:W\longrightarrow\mathsf{Cat},\\
u&:R[*]\longrightarrow D[*],\\
\sigma&:D[\ell]\circ u\Longrightarrow u\circ R[\ell].
\end{aligned}
$$

The eliminator returns

$$
\mathsf{ind}^{d}(R,D,u,\sigma):R\longrightarrow^{d}D.
$$

At the base, its fibre functor reduces to $u$. At the literal generator, its
displayed laxity component reduces to the supplied component of $\sigma$.
These are constructor beta rules. Generic functoriality and transfor
naturality own the remaining identity, composition, and ordinary naturality
cuts.

The coherence cell is directed:

$$
D[\ell]\circ u
\Longrightarrow
u\circ R[\ell].
$$

It is neither an equality nor an automatically invertible path. Reversing it
would define a different eliminator orientation. Supplying only its pointwise
components would also be incomplete, because the transfor must act on arrows
of $R[*]$ and on their higher cells.

The one-dimensional witness is separate signature data. It lets a later
directed 2-cell between parallel based arrows be converted to equality; it
does not make the generating 1-cell invertible. This separation is essential
to the normalization proof of Chapter 8.

The ordinary section eliminator and recursor are specializations:

$$
\begin{array}{c|c|c}
\text{view} & R & D\\
\hline
\text{contextual} & \text{arbitrary} & \text{arbitrary}\\
\text{section} & \text{terminal family} & \text{arbitrary}\\
\text{recursor} & \text{terminal family} & \text{constant family}.
\end{array}
$$

This relationship is an architectural requirement for a future signature
compiler: it should generate one coherent principle and derive weaker views,
not postulate unrelated recursors whose computations may disagree.

What is not yet active is equally specific. There is no general language of
directed cell boundaries, no compiler that generates contextual eliminators
and projection-stable beta rules, no general algebra category, and no theorem
that every such presentation is initial. A plausible implementation must
also generate focused diagnostics for typing, subject reduction, critical
pairs, and both possible projection orders.

<!-- evidence:DHIT-GENERAL-SCHEMA -->

> **Formal status — checked instance and research boundary.** Evidence
> `WE-SIGNATURE` and `WE-CONTEXTUAL-ELIMINATOR` support the complete
> selected instance. Evidence `DHIT-GENERAL-SCHEMA` records the missing
> general signature and compiler rather than extrapolating them from one HIT.

<a id="appendix-formal-presentation-g7"></a>

## G.7 Basic Metatheory And Its Boundary

A successful checker run is strong evidence that the submitted declarations
and rules satisfy the tool's current acceptance conditions. It is not, by
itself, a proof of every global property one might want from the combined
rewrite and unification theory. The current warranted statements are:

| Property | What this edition may say |
| --- | --- |
| typing of active sources | checked by bounded Lambdapi runs over the active module graph |
| local subject-reduction obligations of promoted rewrite rules | checked by Lambdapi's ordinary rule acceptance; not separately formalized as one global project theorem |
| selected computation | witnessed by promoted rules and focused positive and negative assertions |
| selected proof-time comparison | exercised by typed uses or typed reflexivity checks, not inferred merely from a conversion assertion |
| evidence traceability | checked syntactically from book markers to active owners and reviewers |
| build and render reproducibility | tested by the release tooling for the recorded source snapshot |
| global confluence | not established for the whole emdash rewrite and unification theory |
| strong normalization | not established for the whole theory |
| global canonicity | not established; only selected constructor and normalization computations are tested |
| decidable conversion or type checking as an emdash metatheorem | not claimed beyond observed behavior of the current Lambdapi toolchain on the active sources |
| consistency and semantic soundness | require model and metatheory proofs for a precisely stated fragment; they do not follow silently from compilation |

### Engineering Evidence Is Not A Metatheorem

The repository records warning inventories, focused owner-position probes,
critical-pair investigations, strict inferred-slot audits, and bounded full
checks. These practices are indispensable. They locate overlap risks, reject
ill-typed rules, compare reduction orders, and protect intended normal forms.
They still sample or delegate parts of a global theorem rather than proving
one in the object theory.

Warning counts are therefore diagnostics, not a numeric confluence proof.
A zero count would not establish normalization, and a nonzero count does not
by itself refute a deliberately joined computation. Likewise, deterministic
PDF output establishes release reproducibility, not mathematical consistency.

### The Role Of Models

`BNat` is a separate concrete one-object category whose endomorphisms are
natural numbers under addition. The checked functor from WalkingEnd to
`BNat` is meaningful model evidence for the selected generators and
recursor. The encode–decode theorem then proves much more about the based hom
inside the opaque source.

That model is not a soundness interpretation for all of `emdash3_2.lp`.
It does not interpret every higher category, displayed family, equality
principle, profunctor, or rewrite rule. A global consistency claim would
require a stated syntax fragment, an interpretation of every formation and
computation rule in that fragment, and a proof that conversion is preserved.

<!-- evidence:WE-BNAT-MODEL -->

> **Formal status — checked local model evidence.** Evidence
> `WE-BNAT-MODEL` supports the separate WalkingEnd-to-BNat interpretation.
> No global soundness theorem is inferred from it.

### Adaptation Of The HoTT Formal Appendix

The four source units of the HoTT formal appendix enter this presentation as
follows:

| HoTT source unit | Functorial adaptation |
| --- | --- |
| A.1, first presentation | G.2 gives the readable categorical signature; G.5 keeps it distinct from a parser |
| A.2, second presentation | G.1 and G.3 state judgments and literal source; G.4 organizes representative rule families |
| A.3, homotopy type theory | equality and univalence remain qualified layers, while G.6 presents the selected directed WalkingEnd extension |
| A.4, basic metatheory | this section retains the taxonomy of properties but replaces inherited conclusions by the conservative status matrix above |

The adaptation deliberately does not import the HoTT appendix's normalization
or metatheoretic conclusions as results about emdash. Different rewrite
owners, proof-time unification rules, opaque categorical structure, and
directed higher cells require their own theorem.

<!-- evidence:FORMAL-METATHEORY-BOUNDARY -->

> **Formal status — research boundary.** Evidence
> `FORMAL-METATHEORY-BOUNDARY`. The matrix states what current checks
> establish and gives a concrete specification for future metatheory. Global
> confluence, strong normalization, canonicity, decidability, consistency,
> and semantic soundness remain unclaimed until separately proved.

The resulting architecture is intentionally asymmetric. The categorical
kernel computes without depending on a traditional front end. The bounded
elaborator improves usability without changing the foundation, and future
semantic models may justify larger fragments without becoming a second
source language. That is the formal sense in which functorial type theory
begins from categorical computation.
<!-- /book-source:appendix-formal-presentation -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:bibliography book/references/bibliography.md -->
<a id="bibliography"></a>

# Bibliography

1. <a id="ref-hott-book"></a>The Univalent Foundations Program.
   *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for
   Advanced Study, 2013. [Source repository](https://github.com/HoTT/book),
   reviewed at revision
   `578b85cc8d586b1677ec4335148adeb443057d24`.

2. <a id="ref-mac-lane"></a>Saunders Mac Lane. *Categories for the Working
   Mathematician*, second edition. Graduate Texts in Mathematics 5. Springer,
   1998; [DOI 10.1007/978-1-4757-4721-8](https://doi.org/10.1007/978-1-4757-4721-8).

3. <a id="ref-kelly"></a>G. M. Kelly. *Basic Concepts of Enriched Category
   Theory*. London Mathematical Society Lecture Note Series 64. Cambridge
   University Press, 1982; reprinted in *Theory and Applications of
   Categories*, Reprints 10, 2005.
   [TAC reprint](https://www.tac.mta.ca/tac/reprints/articles/10/tr10.pdf).

4. <a id="ref-benabou"></a>Jean Bénabou. “Introduction to Bicategories.” In
   *Reports of the Midwest Category Seminar*, Lecture Notes in Mathematics 47,
   pages 1–77. Springer, 1967.
   [DOI 10.1007/BFb0074299](https://doi.org/10.1007/BFb0074299).

5. <a id="ref-gpt-codex"></a>GPT 5.6 Codex.

6. <a id="ref-lambdapi"></a>The Lambdapi contributors. *Lambdapi User
   Manual*. [Current online manual](https://lambdapi.readthedocs.io/). The
   repository copies under `docs/` are the operational references used while
   maintaining the accompanying formal development.

7. <a id="ref-emdash-artifact"></a>The emdash contributors. *emdash v3.2
   Lambdapi Sources*. Accompanying computational artifact for this development
   edition: `emdash3_2.lp` and its one-way extension modules.

8. <a id="ref-dosen-cut-elimination"></a>Kosta Došen. *Cut Elimination in
   Categories*. Trends in Logic 6. Kluwer Academic Publishers, Dordrecht,
   1999; [DOI 10.1007/978-94-017-1207-1](https://doi.org/10.1007/978-94-017-1207-1).

Items 1–5 and 8 situate the mathematical development; items 6–7 identify the
proof infrastructure and checked artifact. Citation does not by itself confer
the book's formal-status label. The exact HoTT source revision, section
labels, adaptation targets, and license metadata, together with the
reference-only policy for Došen's book, are recorded in
`book/references/third-party-sources.json`.
<!-- /book-source:bibliography -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:book-credits book/CREDITS.md -->
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
one-dimensionality.

The exact source map and adaptation ledger live in
`references/third-party-sources.json`. They were established before the
corresponding prose was drafted. The Chapter 8 vertical slice records
structural and conceptual adaptations from the pinned source, while Chapters
10–15 adapt all nine sections of `categories.tex` and Appendix G adapts all
four parts of `formal.tex`. The resulting prose is newly written for the
directed categorical setting; the ledger records the source labels,
adaptation kind, and target under this attribution and ShareAlike notice.

## Došen's cut-elimination perspective

The four-level cut calculus in Chapter 9 takes conceptual inspiration from
Kosta Došen's *Cut Elimination in Categories* (Kluwer, 1999). The cited work
is not licensed for textual adaptation here. It is used only as a
bibliographic and conceptual reference: the exposition, notation, examples,
and emdash correspondence in this book are newly written, and no passage from
Došen's text is copied or closely paraphrased.
<!-- /book-source:book-credits -->
<div class="book-source-end" aria-hidden="true"></div>

<!-- book-source:book-license book/LICENSE.md -->
<a id="book-license"></a>

# License For The Book

Except where a source or quotation is identified separately, the textual
contents of the `book/` directory and the generated
`print/public/emdash-book.md` artifact are licensed under the
[Creative Commons Attribution-ShareAlike 3.0 Unported
License](https://creativecommons.org/licenses/by-sa/3.0/), abbreviated
`CC BY-SA 3.0`.

You may share and adapt this material under the terms of that license,
including attribution and ShareAlike. Third-party material remains subject to
its identified license and attribution requirements.

This notice applies only to the book text and its generated Markdown form. It
does not assign or change a license for Lambdapi sources, renderer code,
reports, or other repository content outside that book artifact.
<!-- /book-source:book-license -->
<div class="book-source-end" aria-hidden="true"></div>
