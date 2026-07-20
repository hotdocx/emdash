<a id="chapter-12"></a>

# 12. Adjunctions And Equivalences

An adjunction is the first universal construction in which the book's cut
calculus becomes a theorem rather than a notation convention. The active
relation keeps the already named functors as indices and exposes a selected
unit and counit. Their triangle laws are oriented as computation.

## 12.1 Triangle cuts

For $F\dashv G$, the two component-level reductions have the schematic forms

$$
\varepsilon[f]\circ F(\eta[g])\longmapsto f\circ F(g),
\qquad
G(\varepsilon[g])\circ\eta[f]\longmapsto G(g)\circ f.
$$

These are controlled cuts at the stable unit and counit observations. An
arbitrary independently named transformation does not acquire the same
runtime behavior merely because it has a propositionally similar type.

> **Formal status — checked.** Evidence `ADJ-TRIANGLE-CUTS`. The indexed owner
> is `Adjunction`; `unit_adj_transf` and `counit_adj_transf` expose the stable
> observations that trigger both triangle reductions.

<!-- evidence:ADJ-TRIANGLE-CUTS -->

## 12.2 Several notions of equivalence

The chapter will keep the following notions separate: carrier equivalence,
ordinary isomorphism of objects, equivalence of ordinary categories, fully
faithful and essentially surjective functors, strict isomorphism of
categories, and native recursive omega-equivalence evidence. Relations among
them are stated only under hypotheses that make the relevant level and
equality notion explicit.

> **Formal status — mathematical development.** The HoTT equivalence between
> categorical equivalence and fully-faithful-plus-essentially-surjective data
> belongs to the ordinary univalent 1-category specialization. A native higher
> analogue needs packages for essential surjectivity, functor equivalence, and
> their coherent higher action.
