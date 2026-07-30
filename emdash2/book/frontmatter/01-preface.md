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
