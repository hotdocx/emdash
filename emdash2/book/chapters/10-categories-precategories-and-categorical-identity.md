<a id="chapter-10"></a>

# 10. Categories, Precategories, And Categorical Identity

Chapter 2 introduced the categorical language needed for the WalkingEnd
calculation. We now return to the word *category* with a different question:
when should equality of objects agree with categorical sameness? The answer
depends on which categorical layer is under discussion. This second pass is a
spiral over Chapters 2, 4, and 7, not a replacement for their definitions.

## 10.1 A translation table, not a collapse

The HoTT Book's category chapter begins with ordinary precategories whose homs
are sets. Native emdash categories instead expose category-valued homs that
may be iterated. The following table fixes the translation used in the rest of
the book.

| Layer | Characteristic data | Equality or height condition | Role here |
| --- | --- | --- | --- |
| Native `Cat` | objects and iterated `Hom_cat` classifiers | no set-valued-hom premise in the definition | ambient directed higher language |
| Equality-local `Path(A)` | elements of `A` and identity evidence between them | every arrow is induced by equality | groupoidal specialization used for ordinary type theory |
| Finite `IsNCat` evidence, including `OneCat` | a native category plus a recursive hom-height witness | one-dimensionality makes each next hom discrete | bridge to ordinary category-shaped examples |
| HoTT precategory | a type of objects and set-valued homs | hom equality is proposition-valued | mathematical 1-categorical specialization |
| HoTT category | a HoTT precategory for which object identity agrees with isomorphism | `idtoiso` is an equivalence | univalent 1-category notion, not the definition of native `Cat` |
| HoTT strict category | a HoTT category whose object type is a set | object identity is proposition-valued | a qualified truncation notion, unrelated to runtime strictness |

Thus a HoTT precategory can be discussed inside the broader programme, but it
must not silently replace the iterated-hom architecture. Conversely, an
`IsNCat` witness controls categorical height; by itself it does not supply the
full object-identity-to-isomorphism equivalence of a univalent category.

> **Formal status — mathematical development.** The comparison table states
> the translation discipline for this book. A generic package identifying
> native finite-height categories with HoTT precategories has not been
> implemented.

## 10.2 The checked direction

The active calculus does support one important direction. Ordinary
isomorphism evidence between two objects can be lifted to the native recursive
omega-equivalence facade. The construction remains iterable at the next hom;
it is not a proof that every native equivalence arises from object equality.

> **Formal status — checked.** Evidence `EQUIV-ORDINARY-ISO-LIFT`. The owner is
> `iso_evidence_omega_equiv`, with its fixed-arrow refinement supplied by
> `iso_evidence_omega_along`.

<!-- evidence:EQUIV-ORDINARY-ISO-LIFT -->

## 10.3 The missing reverse direction

The categorical identity theorem sought by the larger programme would compare
object identity, ordinary isomorphism, and the appropriate higher equivalence
without erasing direction or higher action. The active evidence establishes
selected groupoid and truncated-universe univalence results and the one-way
ordinary-isomorphism lift above. It does not yet establish a general native
object-equality/ordinary-isomorphism equivalence.

> **Formal status — research boundary.** The missing owner is a native
> category-univalence interface whose forward and reverse maps are coherent
> with iterated hom action. A focused validation must test both object-level
> round trips and the induced next-hom comparison.
