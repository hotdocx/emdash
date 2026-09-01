# TypeScript/emdash Freyd Pre-Abelian Owner Audit

Date: 2026-09-01

Plan-ID: `TS-EMDASH-FREYD-PREABELIAN-COMPUTATION`

Status: completed prerequisite audit for the active implementation plan

Baseline: `c781a42972a3e91f60a79bfd95989ca4dca4aaac`

## Audit Question

Determine the smallest existing formal and operational owners needed to turn
the completed additive Freyd category plus finite-free computational weak
kernels into genuine Freyd kernels and cokernels, and fix the matrix
orientation from source rather than memory.

## Bounded Baseline

The fresh successor worktree was bootstrapped with the pinned pnpm graph.
The following baseline passes:

- workspace contract;
- root TypeScript typecheck;
- `31/31` focused tests covering the field-module reference, doctrines,
  polynomial Freyd category, polynomial weak kernels, and their category
  provider;
- bounded checks of `emdash3_2_weak_kernels.lp`;
- bounded checks of
  `emdash3_2_commutative_algebra_finite_free_direct_sums.lp`; and
- bounded checks of `emdash3_2_commutative_algebra_freyd_additive.lp`.

The Lambdapi checks retain the baseline warning inventory. No candidate rule
was added during this audit.

## Formal Owner Inventory

### Generic universal-property substrate

`emdash3_2.lp` already owns:

- `IsContr`, `is_contr_center`, and `is_contr_path`;
- `HFiber`, `hfiber_point`, and `hfiber_path`;
- `IsEquivMap` as contractible homotopy fibres;
- ordinary equality, Sigma, Pi, products, and truncation levels; and
- generic Hom, composition, functor, opposite, and Path action.

This is sufficient to express genuine kernel/cokernel uniqueness internally.
No new foundational equality or cone classifier is needed.

### Additive substrate

`emdash3_2_preadditive_categories.lp` owns:

- `PreadditiveCategory`;
- selected abelian-group structures on every Hom;
- zero, addition, and negation observations; and
- left/right composition bilinearity.

`emdash3_2_additive_categories.lp` owns:

- `AdditiveCategory = PreadditiveCategory + CartesianCategory`;
- zero-composition consequences;
- selected injections and copairing from product data; and
- biproduct identities and beta/eta laws.

These generic owners should construct `[alpha,-gamma]` and all weak-pullback
paths. No weak-pullback-specific additive grammar is required.

### Weak-kernel substrate

`emdash3_2_weak_kernels.lp` owns annihilated test arrows as:

```text
WeakKernelAnnihilator(alpha,T)
  = HFiber(alpha o -, 0),
```

together with retained test-object reindexing, selected nonunique factors,
reconstruction, proposition-valued existence, and the whole
`HasComputationalWeakKernels` capability.

The new genuine-kernel layer must extend this interface with contractible
factor spaces. It must not modify weak-kernel nonuniqueness.

### Finite-free category substrate

`emdash3_2_commutative_algebra_finite_free_category.lp` owns ranks as objects
and column-oriented matrices as Homs. Generic `id` and `comp_fapp0` remain
runtime owners; proof-time unifiers connect them to rigid recursive identity
and composition matrices. Transparent comparison paths reach the direct
matrix evaluator.

`emdash3_2_commutative_algebra_finite_free_direct_sums.lp` owns the whole
direct-sum functor with rank addition and block-diagonal first-arrow action.
Matrix zero/add/negate laws and composition distributivity already exist in
the matrix additive/subtractive modules.

Missing: no selected `PreadditiveCategory`, binary-products/terminal-zero
package, or `AdditiveCategory` currently targets
`CommRingFiniteFree_cat(R)`. This is a structural packaging prerequisite,
not a missing matrix computation.

### Formal Freyd substrate

The current concrete formal carrier is
`CommRingFreydPresentation_cat(R)`. It already owns:

- presentation objects;
- relation-preserving raw morphisms;
- agreement witnesses;
- groupoidified raw classes and set-truncated quotient Homs;
- selected raw/class identity, composition, zero, addition, and negation;
- direct sums, products, terminal zero, Cartesian structure; and
- `comm_ring_freyd_additive(R)`.

The construction should reuse this category. Adding a parallel generic Freyd
quotient merely to state the theorem would duplicate active semantics. Generic
kernel/cokernel structures and the TypeScript provider interface remain
category-parametric; the first concrete Lambdapi theorem targets the existing
formal presentation category and accepts an explicit finite-free weak-kernel
capability.

## TypeScript Owner Inventory

### Polynomial finite-free provider

`algebra_polynomial_weak_kernel.ts` computes:

- the complete original-column syzygy module;
- `K -> source(F)`;
- checked `F o K = 0`;
- selected factors of arbitrary annihilated multi-column tests; and
- checked reconstruction.

`algebra_polynomial_weak_kernel_category.ts` packages this as a genuine
additive category provider with whole weak-kernel and derived
object/morphism/lift roles, compiler lowerings, reference execution, and a
qualified doctrine.

### Polynomial Freyd carrier

`algebra_polynomial_presentation_morphism.ts` owns relation-preserving maps
and agreement witnesses. `algebra_polynomial_freyd_category.ts` owns the
direct quotient category, additive operations, zero/direct sums/biproducts,
compiler lowerings, and qualified additive doctrine.

It currently has no kernel/cokernel result type or operation family. Its
historical `AlgebraPolynomialWeakKernelCapability` is now a compatibility
facade over the real finite-free provider and remains the correct capability
input.

### Generic operation and doctrine layer

`algebra_tower.ts` describes `freydConstructor()` as introducing `cokernel`,
but the polynomial Freyd category does not register an executable cokernel
operation. `algebra_doctrine.ts` asks `PREABELIAN_DOCTRINE` only for whole
`kernel` and `cokernel` roles. Both surfaces are metadata ahead of usability.

The implementation must expose and require complete role families:

```text
kernel, kernel-object, kernel-embedding, kernel-lift
cokernel, cokernel-object, cokernel-projection, cokernel-colift.
```

### Field-module differential reference

`algebra_module.ts` already contains whole field-linear kernels/cokernels,
`algebraModuleKernelLift`, and `algebraModuleCokernelColift`. The current
category registry exposes only the whole constructions and object
observations. This code can be upgraded for role-family conformance, but its
splitting/inverse algorithms are not valid polynomial-ring Freyd algorithms.

## Exact Constructive Freyd Orientation

The primary mathematical source is Posur, *A constructive approach to Freyd
categories*, Constructions 3.6 and 3.10. The formulas were also checked
against `FreydCategoriesForCAP` commit
`a49e94ffef5c63b754b7662201528cb8961c8d45`, specifically
`gap/FreydCategory.gi`.

For a Freyd morphism:

```text
{alpha,rho_alpha} : (R_A --rho_A--> A) -> (R_B --rho_B--> B),
```

the cokernel relation arrow is the universal map from the direct sum:

```text
[rho_B,alpha] : R_B + A -> B.
```

Its projection datum is `id_B`. The induced colift datum is exactly the test
morphism datum; the zero-composite witness supplies its relation witness.

For the kernel, using a biased weak fibre product whose selected projection
lands in the first source:

```text
projection_1 := WeakFiberProductProjection(alpha,rho_B)
projection_2 := WeakFiberProductProjection(projection_1,rho_A)

kernel presentation := projection_2
kernel embedding datum := projection_1.
```

The induced kernel-lift datum is the universal map into the first weak fibre
product for `(alpha,rho_B,test datum)`. In emdash the zero-composite agreement
witness must remain explicit input to constructing and validating that map,
even where CAP retrieves it indirectly from its operation precondition.

This orientation agrees with the repository's column-map convention:
`algebraPolynomialModuleMapCompose(after,before)` represents
`after o before`; a presentation relation map goes from its relation free
module into its ambient free module.

## Selected Generic Universal Form

For a candidate kernel arrow `kappa : K -> A` and
`cone : WeakKernelAnnihilator(alpha,T)`, define:

```text
KernelFactorSpace(kappa,cone)
  := HFiber(kappa o -, arrow(cone)).
```

`ComputationalKernel(alpha)` stores `K`, `kappa`, annihilation, and
`IsContr(KernelFactorSpace(kappa,cone))` for every test object and cone. The
contractible centre is the selected lift; its fibre path is reconstruction;
applying `sigma_Fst` to the contraction path proves uniqueness.

The dual coannihilator and cokernel factor spaces use precomposition. A direct
transparent dual definition is acceptable; it introduces no parallel runtime
rewrite theory. Stable readable projections may be added only when a real
consumer needs a surviving discriminator.

This generic rule-free module is independent of the missing finite-free
additive package and is therefore the first semantic implementation tranche.

## Rejected Immediate Alternatives

- **Declare pre-Abelian from doctrine metadata:** no object, arrow, factor, or
  universal law would be computed.
- **Use field-module inverses for polynomial presentations:** polynomial rings
  are not fields even when their coefficient domain is.
- **Construct a new generic formal Freyd quotient first:** this duplicates the
  active presentation/agreement/groupoidification carrier without a current
  consumer requiring a second carrier.
- **Turn named proof-CAS equations into a universal weak-kernel function:** a
  finite declaration set cannot inhabit a dependent product over every map.
- **Manual commuting-square records or Boolean zero tests:** these erase the
  typed witness needed by the kernel-lift construction.
- **Broad rewrites on generic identity or composition:** the active rigid-head
  usability design already records why those hot heads remain generic owners.

## First Dependency-Ready Rows

1. Implement the generic internal computational kernel/cokernel module and
   focused reviewer (`FPA-UNIVERSAL-3`).
2. In parallel dependency order, package the formal finite-free
   preadditive/additive structure (`FPA-BASE-ADD-2`).
3. Derive computational weak pullbacks from additive structure and weak
   kernels (`FPA-WEAK-PB-4`).
4. Promote the unconditional TypeScript Freyd cokernel before the weak-
   kernel-dependent Freyd kernel.

The active living plan remains the decision and completion ledger.
