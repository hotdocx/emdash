<a id="chapter-16"></a>

# 16. Weighted Universal Constructions

A weighted limit is not introduced here as one more primitive. It is a
representability statement for a profunctor of weighted cones. This makes the
route from Chapter 13 conceptual and computational:

$$
\text{weight and diagram}
\longrightarrow
\text{cone profunctor}
\longrightarrow
\text{chosen representable comparison}.
$$

Tensor, the two fixed-endpoint profunctor implications, and adjunction mates
provide the surrounding calculus.

## 16.1 Right adjoints preserve weighted limits

Given a selected weighted-limit comparison for a diagram and an adjunction
$F\dashv G$, mate comparison transports the representation across the right
adjoint. The result is again a weighted-limit comparison for the composed
diagram and cone point.

> **Formal status — checked.** Evidence `WEIGHTED-LIMIT-PRESERVATION`. The
> composite certificate is
> `right_adjoint_preserves_weighted_limit_cov_comp`; its input and output use
> `IsWeightedLimit_cov_comp`.

<!-- evidence:WEIGHTED-LIMIT-PRESERVATION -->

## 16.2 Neighboring theory required by the proof

The full chapter will explain weights, cone profunctors, representability,
mate correspondence, and the relation to ordinary limits before presenting
the checked composite. General semantic ends and coends, pointwise Kan
extensions, and dependent adjunctions are not inferred from the selected
fixed-endpoint interfaces.

> **Formal status — mathematical development.** General Kan-extension and
> end/coend owners, including their variance and higher coherence, remain
> missing. The validation target is a universal mapping comparison that
> reduces to the active weighted-limit interface on the selected slice.
