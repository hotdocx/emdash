<a id="chapter-14"></a>

# 14. Strictness, Dagger Structure, And Duality

The word *strict* has several legitimate meanings here, and none may be left
unqualified.

| Qualified term | Reserved meaning |
| --- | --- |
| strict category | the HoTT notion whose object type is a set |
| strict transfor | a transfor whose selected naturality cuts compute in both directions |
| strict or runtime computation | an oriented kernel reduction selecting a normal form |
| dagger category | a category with a chosen contravariant involution and unitary comparison |
| opposite category | reversal of arrow direction through the active `Op_*` owners |
| duality | a proof method or structured equivalence relating a construction to its opposite |

The table prevents object truncation, computational strictness, and strict
naturality from being inferred from one another.

## 14.1 Opposite duality computes

The active opposite operation is involutive on categories and functors,
reverses composition, transports transfors, and swaps the sides of an
adjunction. This is the checked duality used later to derive weighted
colimits from weighted limits.

> **Formal status — checked.** Evidence `OP-DUALITY`. The principal owners are
> `Op_cat`, `Op_func`, `Op_transf`, and `Op_adjunction`.

<!-- evidence:OP-DUALITY -->

## 14.2 Dagger structure is additional data

A dagger is not merely the operation of passing to an opposite category. It
is a selected contravariant involution on one category, commonly
identity-on-objects, together with laws and a unitary notion. That neighboring
theory is needed to adapt the HoTT dagger-category discussion coherently, but
it has no active native owner yet.

> **Formal status — mathematical development.** A future implementation needs
> a dagger functor, involutivity and identity-on-objects evidence, coherent
> higher action, and a unitary equality package. `Op_cat` alone supplies none
> of that chosen structure.
