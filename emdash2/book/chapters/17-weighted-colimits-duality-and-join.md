<a id="chapter-17"></a>

# 17. Weighted Colimits, Duality, And Join

Opposite duality turns the preceding limit theorem around. A weighted colimit
witness is represented by the corresponding weighted-limit witness in
opposite categories, so left-adjoint preservation is obtained from the
right-adjoint theorem rather than developed as an unrelated feature.

## 17.1 Left adjoints preserve weighted colimits

The checked construction applies right-adjoint preservation to the opposite
adjunction and then reduces double opposites and reversed composition to the
colimit-oriented statement.

> **Formal status — checked.** Evidence
> `WEIGHTED-COLIMIT-PRESERVATION`. The owner is
> `left_adjoint_preserves_weighted_colimit_con`, with
> `WeightedColimit_con` defined through opposite duality.

<!-- evidence:WEIGHTED-COLIMIT-PRESERVATION -->

## 17.2 Join as a directed universal construction

The primitive join has left and right inclusions and one internally natural
cross cell directed from the left part to the right part. Its nondependent
recursor computes on both inclusions and on the cross-cell datum. This makes
join a directed-inductive construction rather than a groupoidal sum.

> **Formal status — checked.** Evidence `JOIN-RECURSOR`. The active owners are
> `Join_cat`, `join_cross_transf`, `join_elim_func`, and
> `join_elim_cross_transf`.

<!-- evidence:JOIN-RECURSOR -->

The expected interpretation of join as a collage is deliberately stronger.
It would require a semantic hom decomposition, its universal property, and a
dependent eliminator coherent with the cross-cell action.

> **Formal status — research boundary.** No general collage owner or
> dependent join eliminator is active. A future validation should recover the
> two inclusions and cross homs from the proposed universal property and test
> dependent beta behavior.
