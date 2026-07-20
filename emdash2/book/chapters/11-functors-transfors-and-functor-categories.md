<a id="chapter-11"></a>

# 11. Functors, Transfors, And Functor Categories

Chapter 9 studies transfors as a calculus of cuts. This chapter makes the
categorical packaging explicit: functors are objects of a functor category,
transfors are its arrows, and higher transfors are obtained by iterating the
same hom construction. The spiral relationship is deliberate. Chapter 9 owns
the normalization argument; this chapter owns the categorical organization.

## 11.1 Off-diagonal action is the naturality datum

For a transfor $\eta:F\Rightarrow G$ and an arrow $f:x\to y$, the basic
component is not only a point component. It is the off-diagonal arrow

$$
\eta[f]:F(x)\longrightarrow G(y).
$$

Functor action may be cut on either side, and the strict naturality owners
absorb those cuts into the source arrow of `eta[f]`. Identity, vertical
composition, whiskering, and interchange must continue to use the generic
`fapp*` and `tapp*` calculus rather than constructor-specific copies of the
same laws.

> **Formal status — checked.** Evidence `TRANSF-STRICT-NATURALITY`. The two
> naturality directions compute through the global `tapp1*` owners and retain
> higher action.

<!-- evidence:TRANSF-STRICT-NATURALITY -->

## 11.2 What remains to be packaged

In ordinary univalent 1-category theory, functor categories inherit
categorical univalence under suitable hypotheses. The native directed
analogue must state which equality, equivalence, height, and transfor
structures are being compared. Pointwise object formulas alone are not
enough: the proof must account for off-diagonal action and higher transfors.

> **Formal status — mathematical development.** A general theorem saying that
> the relevant native functor category is univalent is not active. Its missing
> infrastructure is a category-univalence package compatible with functor and
> transfor hom action.
