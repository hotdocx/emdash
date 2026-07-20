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
