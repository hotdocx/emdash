<a id="chapter-25"></a>

# 25. Paths And The Groupoidal Shadow

A directed arrow remembers which way it points. An equality path may also be
followed, but it can be reversed. The two forms of motion coexist in
functorial type theory, and the first question of this fourth spiral is how
they meet without being identified.

For a classifier $A$, the category $\operatorname{Path}(A)$ has the elements
of $A$ as objects and equality evidence as arrows. An ordinary function
$f:A\to B$ acts on paths, hence determines an iterable functor

$$
\operatorname{Path}(f):\operatorname{Path}(A)
  \longrightarrow \operatorname{Path}(B).
$$

This construction is the **groupoidal shadow** of ordinary function action.
It does not say that every directed category is already a path category. It
says that equality-local motion can be presented inside the same categorical
language of objects, homs, functors, and higher action.

The decisive example is transport over a product. Let
$P:A\times B\to\mathcal U$, let $p:a=a'$, let $q:b=b'$, and let
$u:P(a,b)$. The pair path assembled from $p$ and $q$ supports one direct
transport. It also supports two sequential readings: first in the $A$
coordinate and then in the $B$ coordinate, or in the reverse order. The
active construction compares the direct transport with both readings and
shows that the resulting diamond is coherent.

<!-- evidence:GROUPOIDAL-PRODUCT-TRANSPORT -->

> **Formal status — checked.** Evidence
> `GROUPOIDAL-PRODUCT-TRANSPORT`. The comparison uses the one primitive
> right-based equality eliminator. The structured categorical transport and
> `PathOut` induction presentations agree with that same primitive operation;
> no second form of $J$ or product-specific transport axiom is introduced.

<a id="chapter-25-route"></a>

## 25.1 The Route Through The Chapter

The chapter will proceed in three movements. First it will reconstruct the
path category and its retained higher action from the equality layer already
used in Chapters 1–5. Second it will develop product paths and transport as a
representative closure theorem, making the order of dependent transport
visible without mistaking a comparison theorem for a new runtime reduction.
Third it will return to the ordinary functor compositor. When its codomain is
a path category, the directed comparison cell becomes an equality between
paths and therefore has an inverse. Laxity becomes pseudo-laxity because of
the target, not because the original directed witness has been erased.

This also separates three constructions that will matter later. Groupoidal
closure asks whether a former built from groupoidal data remains groupoidal.
Truncation reflects an already groupoidal classifier into a lower homotopy
level. Groupoidification starts with directed categorical data and freely
realizes its arrows as paths. The first two belong to this chapter and the
next; the third is the subject of Chapter 27.

> **Formal status — mathematical development.** The complete expository
> derivation and its diagrams are being expanded under the current fourth-
> spiral plan. The central product-transport theorem above and the active
> path-category action are already checked; no claim of closure for every
> categorical former is made.
