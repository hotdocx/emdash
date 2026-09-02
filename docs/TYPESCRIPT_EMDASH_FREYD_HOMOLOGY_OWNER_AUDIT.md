# TypeScript/emdash Freyd Homology Owner Audit

Date: 2026-09-02

Plan-ID: `TS-EMDASH-FREYD-HOMOLOGY-COMPUTATION`

Status: active implementation audit

Baseline: `4acef747d4b80e92c5c653e0b6635e6817a9c909`

## Audit Question

Can the integrated bounded-complex, polynomial Freyd Abelian, categorical
compiler, formal witnessed, and proof–CAS owners construct one-degree
homology, exactness, and an induced homology map without introducing a second
quotient theory, a closed formal Abelian claim, or hand-written diagram data?

## Conclusion

Yes, with one categorical-IR qualification.

The mathematical and concrete owners are dependency-ready:

```text
d ∘ dNext ~ 0
  → selected kernel of d
  → selected lift of dNext into that kernel
  → selected cokernel of the lift
  → homology.
```

The generic Lambdapi construction can be completely rule-free. The native
polynomial Freyd construction can retain every agreement. The formal
construction can consume the same explicit agreements without decoding a
truncated-Hom path.

The current retained `CategoricalProgram` IR cannot yet express this as three
dependent nodes: it supports one input per node, exact schema equality, and no
generic record/product assembly; `derivedCallbackInlining` is explicitly
false. The initial categorical consumer should therefore retain one whole
`homology-at` operation, select a derived category method with kernel/cokernel
prerequisites, and lower that whole operation to the native engine. A generic
dependent record-builder or with-given universal operation remains
consumer-gated after this whole result exists.

No new runtime rewrite or unification rule is indicated by the audit.

## Baseline Evidence

The dedicated worktree was created from clean integrated main at `4acef747`
and bootstrapped with the pinned pnpm workspace. Baseline ancestry is `0 1`
after the initial plan checkpoint.

Proportional checks pass:

- workspace contract from bootstrap;
- root TypeScript typecheck;
- 24 focused tests across bounded polynomial complexes, their category and
  graph operations, field-linear homology, polynomial Freyd Abelian methods,
  and the Freyd Abelian proof–CAS bridge: 23 pass and one opt-in live probe is
  skipped;
- quiet bounded Lambdapi checks of the bounded-free complex/chain-map,
  generic Abelian, witnessed Freyd Abelian, and formal Freyd image owners;
- both bounded-free reviewer examples;
- warning-enabled formal Freyd image checking; and
- strict LHS audit with zero unreviewed reconstructible clauses.

The source-health snapshot is current at 425 files. The inherited formal
warning inventory is the completed Freyd–Abelian boundary
`1,392 = 1,223 critical pairs + 169 replaceable variables`; no candidate rule
exists yet to alter it.

## Exact Owner Matrix

| Concern | Generic/formal owner | Native/CAS owner | Status for this goal |
|---|---|---|---|
| zero composite | `WeakKernelAnnihilator`, ordinary composition and zero | presentation composite, zero morphism, `PresentationMorphismAgreement` | ready |
| selected cycles | `ComputationalKernel`, `preabelian_kernels` | `algebraPolynomialFreydKernel` | ready |
| boundary lift | `computational_kernel_lift` and `_path` | `algebraPolynomialFreydKernelLift` | ready |
| selected homology | `ComputationalCokernel`, `preabelian_cokernels` | `algebraPolynomialFreydCokernel` | ready |
| exactness property | `IsEpic` from `emdash3_2_abelian_categories.lp` | cokernel-projection-zero agreement / Freyd epimorphism witness | ready as witness boundary |
| epic ⇒ zero homology projection | `epic_cokernel_morphism_zero_path` | retained computed agreement | ready |
| bounded free complex | `CommRingBoundedFreeComplex` | `AlgebraPolynomialBoundedFreeComplex` | ready as adapter source only |
| bounded free chain map | `CommRingBoundedFreeChainMap` | `AlgebraPolynomialBoundedChainMap` | ready as adapter source only |
| Freyd complex | no current owner | no current whole owner | required |
| induced homology map | universal operations available, no current owner | field-only reference in `algebra_homological.ts` | required |
| proof–CAS | presentation-morphism/agreement realizations | formal delegation adapters | ready infrastructure |

## Generic Lambdapi Construction

### Chain pair

The selected carrier is the existing annihilator fibre, not a new square:

```text
ChainPair(dNext,d)
  := WeakKernelAnnihilator(d, source(dNext)).
```

For readable whole data, a thin package may retain the two arrows and this
fibre point. Its chain law is exactly the fibre path
`d ∘ dNext = 0`.

### Cycles and boundary

For selected kernel `K(d)`, the boundary is:

```text
b := computational_kernel_lift(K(d), chainPair).
```

The existing lift path gives `kernel_embedding(d) ∘ b = dNext`. No extra
factorization record or square field is needed.

### Homology

The selected homology construction is:

```text
Q(b) : ComputationalCokernel(b).
```

A thin `ComputationalHomologyAt` package should retain the selected cycle
kernel, the chain cone, the boundary lift, and the selected cokernel. Readable
projections expose cycle object/embedding, boundary, homology object/projection,
and both reconstruction/annihilation laws.

This requires only one selected `PreAbelianCategory`; normality is not needed
to construct homology.

### Exactness

Exactness at the middle object is:

```text
IsEpic(boundary).
```

Given that evidence, `epic_cokernel_morphism_zero_path` proves the selected
homology projection zero. The converse and an `Im ≅ Ker` view are useful later
theorems but are not prerequisites for the computation owner.

## Formal Polynomial Freyd Construction

For raw presentation morphisms `dNext` and `d`, an explicit agreement

```text
d ∘ dNext ~ 0
```

is already exactly the input type expected by
`comm_ring_freyd_kernel_lift_raw`. The formal construction is therefore:

1. `comm_ring_freyd_kernel_presentation(d)` and its embedding;
2. `comm_ring_freyd_kernel_lift_raw(d,dNext,agreement)` as the boundary;
3. `comm_ring_freyd_cokernel_presentation(boundary)` as homology; and
4. the existing kernel reconstruction and cokernel annihilation agreements as
   the computational laws.

The existing `W` parameter remains explicit. Exactness is an explicit
`CommRingFreydEpimorphismWitness` for the boundary, or equivalently its
cokernel-projection-zero agreement. No arbitrary path is decoded.

## Native Polynomial Freyd Construction

The native whole result should retain:

- `dNext`, `d`, their composite and zero morphism;
- the computed chain agreement, including a negative `agrees=false` result;
- the selected cycle kernel;
- for a valid pair, the selected boundary lift and reconstruction agreement;
- the selected homology cokernel and its projection/annihilation agreement;
  and
- exactness classification data when requested.

The chain-pair constructor may retain invalid pairs. The homology constructor
requires a positive chain agreement and reports a typed
`CHAIN_CONDITION_FAILED` error otherwise. This mirrors the completed
bounded-free negative-result policy while preventing invalid universal
operations.

The older field-linear `AlgebraModuleHomology` result is a differential
oracle. It does not replace this presentation-witnessed whole result.

The selected native implementation now follows this boundary exactly in
`algebra_polynomial_freyd_homology.ts`. The multiplication-by-`x` map followed
by its selected quotient projection is the first nontrivial exact consumer;
the zero-to-zero pair is retained as a valid but nonexact comparison.

## Categorical Program Feasibility

The operational polynomial Freyd Abelian category exposes inherited whole
kernel, kernel-lift, cokernel, and cokernel-colift roles. Its method registry
can add a derived `homology-at` role.

However, current `CategoricalProgram` nodes are unary and connect only when
the previous output schema is exactly the next input schema. There is no node
for combining a selected kernel with the original pair into a kernel-lift
input, and derived callbacks are not inlined during compilation.

Selected first implementation:

```text
one whole homology-at CategoryOperation
  → derived CategoryMethod with universal-operation prerequisites
  → one explicit lowering to one native homology AlgebraOperation
  → one retained categorical-program node
  → direct/graph whole-result comparison.
```

The pure native homology function remains the single algorithmic
implementation used by the method and native operation. The method's
prerequisite list records capability/planning dependence. Multi-node
dependent inlining is a separately gated generic-IR improvement, not a reason
to special-case homology syntax.

The implemented category model confirms this selection. Its retained program
chains whole homology into whole exactness, while its planner records the
universal-operation prerequisites and its compiler selects two ordinary
lowerings. Direct and graph results agree under canonical serialization.

## Whole Freyd Complex Boundary

The existing free-complex recursive shape is reusable, but its object and law
types are not. A Freyd complex must retain presentation terms, raw
presentation morphisms, and `PresentationMorphismAgreement`s for adjacent zero
composites. The direct matrix/free complex converts into this owner through
relation-free presentations.

The one-degree chain pair and homology result should be implemented before the
recursive whole complex. This keeps the mathematical owner independent of
indexing and lets the bounded adapter consume rather than duplicate homology.

The implemented bounded owner follows that split. It retains presentation
agreements at every adjacent pair, uses selected zero-presentation endpoint
maps, and delegates every degree query to the one-degree homology function.
The existing free complex embeds through relation-free presentations.

## Functorial Homology Boundary

The field reference confirms the correct two-factor algorithm. At a chain-map
degree:

- the lower square constructs the cycles map by kernel lifting;
- the upper square proves the cycles map coannihilates the source boundary;
- cokernel colifting constructs the induced homology map.

The polynomial/formal version must retain both presentation agreements. The
first goal requires identity and one nontrivial induced map. Composition
compatibility is implementation-ready mathematically but should be promoted
only after the concrete owner and equation orientation are measured.

## Proof–CAS Boundary

The completed presentation realization can reify every required structural or
agreement equation. A new adapter should replay the one whole native homology
operation and later the induced-map operation, comparing complete canonical
outputs before exposing chain, boundary reconstruction, homology annihilation,
exactness, cycles-map, and induced-map equations.

No new Core expression, proof-plan tag, or trust mode is needed.

## Revised Sequencing

1. Implement the generic rule-free one-degree owner.
2. Implement the native polynomial Freyd chain-pair and homology whole result.
3. Add witness-rich exactness classification.
4. Add the whole categorical operation/method/lowering and graph consumer.
5. Add the bounded Freyd-complex owner and free-complex adapter.
6. Promote the formal witnessed one-degree construction.
7. Implement the induced homology-map owner.
8. Add the proof–CAS consumer and differential.

This revises only the internal ordering of the living plan. It preserves the
selected mathematical formula and completion boundary.

## Rejection Signals

- a new quotient Hom or equality decoder;
- a Boolean-only chain or exactness result;
- a manually supplied cone or chain-map square outside existing agreements;
- a homology object without its cycle/boundary/cokernel whole data;
- a special-purpose categorical IR node or arbitrary callback decompilation;
- treating the field reference as polynomial authority;
- broad runtime rules on generic category operations; or
- a recursive bounded-complex design before the one-degree owner checks.
