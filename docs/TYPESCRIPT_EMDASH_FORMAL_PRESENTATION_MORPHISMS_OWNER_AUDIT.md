# Formal Presentation Morphisms Owner And Orientation Audit

Date: 2026-08-31

Plan-ID: `TS-EMDASH-FORMAL-PRESENTATION-MORPHISMS`

Status: completed prerequisite audit for the active implementation plan

## Audited Authorities

- `emdash2/emdash3_2_commutative_algebra_finite_modules.lp`
- `emdash2/emdash3_2_finite_families.lp`
- `emdash2/emdash3_2_commutative_algebra.lp`
- `src/v3_2/algebra_polynomial_module.ts`
- `src/v3_2/algebra_polynomial_presentation.ts`
- `src/v3_2/algebra_presented_module.ts`
- `src/v3_2/algebra_presented_module_map.ts`
- `src/v3_2/algebra_module.ts`
- `src/v3_2/algebra_homological.ts`

## Formal Owner Result

The finite-module owner already supplies the required column convention,
matrix action, zero, composition, vector subtraction, and equation
classifiers. The smallest coherent continuation is a new downstream one-way
module. It should add:

- componentwise matrix addition, negation, and subtraction;
- a transparent nested-Sigma presentation package and projections;
- relation-preserving morphism data;
- representative-agreement data; and
- one exact chain-map-square classifier.

No rewrite or unification rule is needed. The new operations are transparent
Nat/finite-family definitions, while all nontrivial algebraic laws remain
ordinary equality paths. Matrix identity is not required by the first
relation-witness or congruence consumer and remains gated by an actual
identity/composition packaging need.

The present kernel has no generic record constructor that turns arbitrary
object, hom, identity, composition, and law data into a value of `Cat`.
Introducing a formal presentation category would therefore require a separate
category-head and projection design. It is not part of this first morphism
bridge.

## Computational Owner Result

`AlgebraPolynomialModuleMap` already provides the correct fixed-ring map
orientation:

```text
rows-by-columns map : source rank -> target rank
composition(after,before) : source(before) -> target(after).
```

`AlgebraPresentedPolynomialModule` retains both the original ordered relation
submodule and a Gröbner basis. Crucially, module-basis transformations are
retained back to the original relation generators. Consequently,
`algebraPolynomialModuleMembership` returns coefficients in the original
relation order, even though reduction runs through the computed basis. These
coefficients can be assembled directly as the columns of `W` or `H`.

The existing public presented-algebra semilinear map validates that relation
images reduce to zero but stores only canonical target elements. It does not
retain the memberships, coefficients, remainders, or a matrix `W`. The new
bridge should therefore introduce a whole realization result rather than
mutating the public map representation merely to satisfy formal delegation.

The field-linear `AlgebraModuleMorphism.relationWitness` is useful comparison
evidence but is not the primary owner: it is restricted to operational fields
and quotient coordinates, whereas the new formal API is commutative-ring
generic and the first computational realization is polynomial.

## Selected Orientations

For source and target relation matrices

```text
R_P : g_P x r_P
R_Q : g_Q x r_Q
```

and a candidate generator map

```text
F : g_Q x g_P,
```

each source-relation image is tested by target membership:

```text
R_Q * w_j = F * (R_P)_j.
```

Assembling the coefficient columns gives the whole equation

```text
R_Q o W = F o R_P,
```

where `W : r_Q x r_P`.

For representative agreement, membership is applied to every difference
column:

```text
R_Q * h_j = F_j - G_j.
```

The whole equation is therefore

```text
R_Q o H = F - G,
```

where `H : r_Q x g_P`.

These orientations match the existing formal membership target
`matrix_apply(A,c) = v` and avoid a systematic equality-symmetry layer.

## Chain-Square Boundary

For

```text
d_i      : C_i -> C_(i-1)
e_i      : D_i -> D_(i-1)
F_i      : C_i -> D_i
F_(i-1)  : C_(i-1) -> D_(i-1),
```

the selected exact square is

```text
e_i o F_i = F_(i-1) o d_i.
```

The square is derived from the four matrices and checked by computation; it
is not an independent input proof field. A whole arbitrary-length formal
complex remains later work.

## Negative And Noncollapse Boundaries

- A failed source-relation membership retains its nonzero target remainder.
- A failed representative agreement retains at least one nonzero difference
  remainder.
- Foreign rings, term orders, module parents, ranks, relation orders, and map
  endpoints are rejected before reification.
- Distinct candidate matrices remain distinct runtime data even when an
  agreement witness exists.
- Different `W` or `H` choices are not identified.
- No quotient equality, exactness, homology, varying-ring semilinearity, or
  formal presentation category is inferred.

## Validation Consequence

The formal implementation can be rule-free. Required evidence is therefore:

- focused owner and reviewer checks;
- visible matrix add/sub and package projection computation;
- positive morphism/agreement/chain-square construction and relevant
  noncollapse assertions;
- zero strict LHS findings for the new module;
- TypeScript positive/negative whole-result tests;
- exact Core target checking and live bounded Lambdapi emission; and
- proportional registration, catalog/health, and standing-document updates.
