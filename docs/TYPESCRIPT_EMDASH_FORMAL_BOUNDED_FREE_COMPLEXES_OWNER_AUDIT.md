# Formal Bounded Free Complexes Owner Audit

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FORMAL-BOUNDED-FREE-COMPLEXES`

Status: completed complex-tail prerequisite audit; chain-map-tail audit remains
in the active implementation plan

## Audited Authorities

- `emdash2/emdash3_2_commutative_algebra_finite_modules.lp`
- `emdash2/emdash3_2_commutative_algebra_presentations.lp`
- `emdash2/emdash3_2_finite_families.lp`
- `emdash2/emdash3_2_nat_arithmetic.lp`
- `src/v3_2/algebra_polynomial_presentation.ts`
- `src/v3_2/algebra_polynomial_presentation_morphism.ts`
- `src/v3_2/algebra_homological.ts`

## Selected Recursive Owner

The smallest whole internal representation is a boundary-indexed continuation:

```text
ChainTail_R(0; below,current,d) = Unit

ChainTail_R(n+1; below,current,d)
  = Sigma next,
      Sigma e : Matrix_R(current,next),
        (d o e = 0)
        x ChainTail_R(n;current,next,e).
```

The Nat eliminator returns a dependent function of both ranks and the boundary
matrix. Consequently, the next differential and recursive rest are typed
without `Fin`, lookup, a heterogeneous list, or an external endpoint check.

The quiet owner-position probe validates the classifier; nil and cons
constructors; next-rank, differential, law, and rest projections; a visible
two-differential constructor with a supplied exact law; and definitional
reduction of the visible next rank and differential. No stable head, rewrite,
or unification rule is needed for this layer.

## Rejected Dummy Zero Boundary

The initial sketch defined every complex from a canonical boundary
`0_(0,rank0) : R^rank0 -> R^0` and asked the first differential to store
`0 o d1 = 0`. A direct conversion assertion failed. The equation is valid by
ring laws, but the matrix evaluator does not make scalar multiplication and
addition by zero judgmental for arbitrary ring elements.

Adding a rewrite, opaque law, or general matrix theorem solely to store this
redundant condition would obscure the actual recursive boundary. The whole
complex is therefore selected as

```text
BoundedFreeComplex_R(0) = Nat

BoundedFreeComplex_R(n+1)
  = Sigma rank0,
      Sigma rank1,
        Sigma d1 : Matrix_R(rank0,rank1),
          ChainTail_R(n;rank0,rank1,d1).
```

The first stored law is now the genuine adjacent condition `d1 o d2 = 0`.
The revised classifier and positive-length constructor/projections pass in the
same probe.

## Chain-Map Audit Boundary

The next formal probe must recurse simultaneously over two already-selected
tails. At each successor it extracts both next ranks and differentials, binds
the next component, stores the existing `CommRingChainMapSquare`, and recurses
over both rest projections.

Transparent tail projections are the selected starting point. If their
dependent use inside the Nat-eliminator motive is conversion-heavy, a narrow
stable schema/projection owner may be introduced. A jointly aligned chain-map
spine is a second fallback only if it retains recoverable whole source and
target complex data. Flat arrays and manually authored square fields are not
acceptable fallbacks.

## Computational Alignment

`AlgebraPolynomialSchreyerResolution` already stores free modules and
differentials in the required low-to-high order. The new computational owner
can therefore retain the same order and recompute every adjacent composite.
The formal length is the differential count; a free quotient with no
differential becomes the zero-length rank package.

The existing single-square operation supplies the local chain-map law, while
the next whole chain-map owner must retain every component and every computed
square. Field-linear homological structures remain comparison evidence rather
than the primary polynomial/free representation.
