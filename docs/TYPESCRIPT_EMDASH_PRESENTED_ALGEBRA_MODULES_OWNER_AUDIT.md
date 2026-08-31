# Presented-Algebra Modules Owner And Representation Audit

Date: 2026-08-31

Plan: `TYPESCRIPT_EMDASH_PRESENTED_ALGEBRA_MODULES_PLAN.md`

Status: `PAM-AUDIT-1A` complete; the quotient-module representation is
accepted with one required reduced-module-Gröbner prerequisite.

## Authorities Reviewed

The audit read the repository TypeScript handoff and persistent-goal workflow,
the completed focused-CAS, affine-geometry, and affine-formal plans, and the
active TypeScript owners and focused consumers listed below. Active source
wins over prose.

The unchanged focused baseline passed 27 tests across:

```text
v3_2_algebra_polynomial_module_tests.ts
v3_2_algebra_polynomial_presentation_tests.ts
v3_2_algebra_presented_algebra_tests.ts
v3_2_algebra_localization_tests.ts
v3_2_algebra_cech_tests.ts
```

Workspace bootstrap/check also passed in the dedicated worktree. No
Lambdapi source or unrelated TypeScript owner changed.

## Exact Owner Map

| Required datum or computation | Current owner | Use or gap |
| --- | --- | --- |
| sparse coefficient polynomial ring | `AlgebraPolynomialRing` in `algebra_polynomial.ts` | exact ambient scalar owner |
| polynomial ideal and reduced scalar basis | `AlgebraPolynomialIdeal`, `algebraReducedGroebnerBasis` in `algebra_ideal.ts` | canonical owner of the quotient algebra relations |
| canonical quotient algebra and elements | `AlgebraPolynomialQuotientRing`, `AlgebraQuotientElement` in `algebra_quotient.ts` | exact coefficient algebra and canonical component representatives |
| presented algebra role | `AlgebraPresentedAlgebra` in `algebra_presented_algebra.ts` | module scalar parent |
| presented algebra map | `AlgebraPresentedAlgebraMap` | exact base map for future semilinear maps and base change |
| polynomial free module and vector | `AlgebraPolynomialFreeModule`, `AlgebraPolynomialModuleVector` in `algebra_polynomial_module.ts` | implementation substrate over the polynomial presentation |
| relation submodule and module Buchberger | `AlgebraPolynomialSubmodule`, `algebraPolynomialModuleGroebnerBasis` | position-aware module algorithm and retained transformations |
| presented polynomial quotient and normal form | `AlgebraPresentedPolynomialModule`, `algebraPresentedPolynomialModuleNormalForm` in `algebra_polynomial_presentation.ts` | reusable quotient machinery, but not itself parent-aware over a presented algebra |
| reduced module Gröbner basis | none | required prerequisite; current module basis is complete/monic but not reduced or presentation-canonical |
| principal localization and canonical map | `AlgebraPrincipalLocalization` | target algebra and base map for module localization |
| affine cover simplices and face maps | `AlgebraCechSimplex`, `AlgebraCechFace` | later direct product localizations and semilinear restrictions |
| native operation/graph layer | `AlgebraOperation`, `AlgebraComputationGraph`, reference engine | later whole-computation exposure |

## Accepted Quotient-Module Representation

For `A = R/I`, free rank `r`, and selected module relations `N`, use:

```text
A^r / N  :=  R^r / (I R^r + N_lift).
```

The implementation uses the quotient's canonical reduced scalar basis—not
the original ordered ideal presentation—to generate `I R^r`. For every
canonical scalar basis polynomial `g` and free position `j`, it inserts the
module vector `g e_j`.

Public user relations are `A`-valued component arrays. Every component is
already one canonical `AlgebraQuotientElement`; its representative lifts into
the polynomial free module. The combined relation submodule retains the
separate algebra-action and user-relation families before computing one module
Gröbner owner.

This is a genuine module computation. Componentwise scalar ideal membership
cannot replace it because leading-term divisibility, S-pairs, reduction, and
syzygies also depend on basis position and the selected module order.

## Prototype Evidence

An isolated direct-TypeScript prototype used only existing owners.

For the rank-one free module over `Q[x]/(x²)` with no extra module relation:

```text
x²e normalizes to zero
xe does not normalize to zero.
```

For `A = Q[x]` and `M = A/(x)`, the same construction was transported through
the existing principal-localization maps:

```text
M[1/x]       is the zero module
M[1/(1−x)]   is not the zero module.
```

Both results follow from ordinary module Gröbner normal forms; neither uses a
special support or localization shortcut.

## Canonicality Gap And Selected Prerequisite

The current module Buchberger result is deterministic for one ordered input
but is not a reduced basis. The audit measured:

```text
generators (x,y)       -> basis (x,y)
generators (x,x+y)     -> basis (x,x+y,y)
generators (x+y,x)     -> basis (x+y,x,y).
```

These presentations generate the same rank-one submodule but retain different
bases and divisor orders. Consequently:

- the current `AlgebraPolynomialModuleGroebnerBasis` is valid for membership;
- it is not a stable semantic fingerprint for a new presented-module parent;
- normal-form representatives should not be called presentation-independent
  until a reduced postpass exists.

The first `PAM-MODULE-2A` subtranche will add a transformation-preserving
`algebraReducedPolynomialModuleGroebnerBasis` analogous to the existing
scalar reduced-basis owner. It will:

1. remove leading terms divisible at the same module position;
2. reduce every retained vector by the others;
3. update transformation rows against the original relation family;
4. normalize leading coefficients to one;
5. sort by the selected module term order; and
6. retain pair/reduction work and an explicit reduced marker.

Equivalent relation presentations must then produce byte-identical reduced
basis vectors in focused examples while every transformation still
reconstructs its output.

## Parent, Equality, And Element Decisions

- The module term order is explicit parent data. The default is the existing
  `term-over-position`; callers may select `position-over-term`.
- A free module over `A` records `A`, rank, term order, and the underlying
  polynomial free module.
- A presented-module parent additionally fingerprints the reduced combined
  relation basis. Equivalent original relation lists may share identity only
  when that canonical basis agrees.
- A public element stores the canonical remainder against that reduced basis.
  Whole normalization separately retains the input quotient components,
  polynomial lift, division quotients, original-relation coefficients, and
  remainder.
- Equality is same presented-module parent plus polynomial-module remainder
  equality.
- A module is computationally zero exactly when every ordered free basis
  vector reduces to zero; rank zero is the empty instance of that criterion.

## Semilinear And Descent Consequences

The later map owner should be semilinear over an explicit
`AlgebraPresentedAlgebraMap`. Applying a map transports scalar components and
combines selected target generator images. Construction validates the source
combined relations in the target module. Same-ring linear maps use the
identity algebra map.

This representation allows:

- base change to transport presentation relations;
- localization to specialize base change along the retained canonical map;
- affine chart values to use direct ambient localizations; and
- Čech face restrictions to be relation-checked semilinear maps into the
  direct product-localization module.

No manually supplied gluing square is required. A later ordinary chain
complex remains deferred because the diagram's scalar rings vary.

## Selected Next Row

`PAM-MODULE-2A` begins with the reduced module-Gröbner prerequisite, then
constructs the parent-aware presented-algebra module and element layer. The
first durable tests retain the three audit prototypes, equivalent relation
presentations, transformation reconstruction, POT/TOP identity separation,
foreign-parent failures, and zero-module detection.
